use std::collections::HashMap;
use std::io::prelude::Write;
use std::path::Path;

use anyhow::Result;

use starlark_syntax::codemap;
use starlark_syntax::codemap::CodeMap;
use starlark_syntax::lexer;
use starlark_syntax::syntax;
use starlark_syntax::syntax::module::AstModuleFields;

use compile_core::{
    ast, Argument, AssignTarget, Ast, AstNode, AstType, BinOpNode, CodeLocation, Diagnostic, Label,
    LinkOptions, SpanId, StringKey,
};

use flat::{Blockify, Flatten, FlattenEnvironment, NodeBuilder, NodeBuilder as NB, ValueId};

use lower_mlir::Module;

#[derive(Debug, Clone)]
pub enum ExtraAst {
    LoopStart(Option<StringKey>),
    LoopBreak(Option<StringKey>),
    LoopContinue(Option<StringKey>),
    Label(StringKey),
    Goto(StringKey),
    BlockEnd,
}

fn get_string_arg(args: &[Argument], b: &mut NodeBuilder) -> Option<StringKey> {
    if args.len() == 0 {
        None
    } else if args.len() == 1 {
        let Argument::Positional(arg) = args.get(0).unwrap();
        let s = arg.try_string().unwrap();
        let key = b.labels.s(&s);
        Some(key)
    } else {
        unreachable!()
    }
}

impl ExtraAst {
    pub fn is_extra(name: &str) -> bool {
        name == "loop" || name == "loop_break" || name == "loop_continue" || name == "end"
        //|| name == "goto" || name == "label"
    }

    pub fn from_name(name: &str, args: &[Argument], b: &mut NodeBuilder) -> Option<ExtraAst> {
        match name {
            "loop" => Some(Self::LoopStart(get_string_arg(args, b))),
            "loop_break" => Some(Self::LoopBreak(get_string_arg(args, b))),
            "loop_continue" => Some(Self::LoopContinue(get_string_arg(args, b))),
            "end" => {
                assert_eq!(args.len(), 0);
                Some(ExtraAst::BlockEnd)
            }
            "goto" => Some(Self::Goto(get_string_arg(args, b).unwrap())),
            "label" => Some(Self::Label(get_string_arg(args, b).unwrap())),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub enum DataType {
    Global,
    Local,
}

#[derive(Debug, Clone)]
pub struct Data {
    ty: DataType,
}
impl Data {
    pub fn new_global() -> Self {
        Data {
            ty: DataType::Global,
        }
    }
    pub fn new_local() -> Self {
        Data {
            ty: DataType::Local,
        }
    }
}

#[derive(Debug)]
pub struct Layer {
    names: HashMap<StringKey, Data>,
    loops: Vec<StringKey>,
}
impl Default for Layer {
    fn default() -> Self {
        Self {
            names: HashMap::new(),
            loops: vec![],
        }
    }
}

#[derive(Debug)]
pub struct Environment<'a> {
    codemap: &'a CodeMap,
    in_func: Vec<bool>,
    layers: Vec<Layer>,
    file_id: usize,
    unique: usize,
}

impl<'a> Environment<'a> {
    pub fn new(codemap: &'a CodeMap, file_id: usize) -> Self {
        let start = Layer::default();
        Self {
            codemap,
            in_func: vec![],
            layers: vec![start],
            file_id,
            unique: 0,
        }
    }

    pub fn span_id(&self, span: codemap::Span, b: &mut NodeBuilder) -> SpanId {
        let begin = CodeLocation {
            pos: span.begin().get(),
        };
        let end = CodeLocation {
            pos: span.end().get(),
        };
        b.spans.get_span(self.file_id, begin.clone(), end.clone())
    }

    pub fn push_loop(&mut self, name: StringKey) {
        self.layers.last_mut().unwrap().loops.push(name);
    }

    pub fn pop_loop(&mut self) -> StringKey {
        for layer in self.layers.iter_mut().rev() {
            return layer.loops.pop().unwrap();
        }
        unreachable!()
    }

    pub fn enter_func(&mut self) {
        self.in_func.push(true);
    }

    pub fn exit_func(&mut self) {
        self.in_func.pop().unwrap();
    }

    pub fn is_in_func(&self) -> bool {
        self.in_func.len() > 0
    }

    pub fn define(&mut self, name: StringKey) {
        let data = if self.is_in_func() {
            Data::new_local()
        } else {
            Data::new_global()
        };
        self.layers.last_mut().unwrap().names.insert(name, data);
    }

    pub fn resolve(&self, name: StringKey) -> Option<Data> {
        for layer in self.layers.iter().rev() {
            return layer.names.get(&name).cloned();
        }
        None
    }

    pub fn dump(&self) {
        println!("{:?}", self);
    }

    pub fn error(&self, span: codemap::Span, msg: &str) -> Diagnostic<usize> {
        let r = span.begin().get() as usize..span.end().get() as usize;
        Diagnostic::error()
            .with_labels(vec![Label::primary(self.file_id, r).with_message(msg)])
            .with_message("error")
    }

    pub fn unimplemented(&self, span: codemap::Span) -> Diagnostic<usize> {
        let r = span.begin().get() as usize..span.end().get() as usize;
        Diagnostic::error()
            .with_labels(vec![
                Label::primary(self.file_id, r).with_message("Unimplemented")
            ])
            .with_message("error")
    }
}

fn from_literal(
    item: syntax::ast::AstLiteral,
    span: codemap::Span,
    env: &Environment,
    b: &mut NodeBuilder,
) -> compile_core::AstNode {
    use syntax::ast::AstLiteral;
    let lit = match &item {
        AstLiteral::Int(x) => {
            use lexer::TokenInt;
            match x.node {
                TokenInt::I32(y) => ast::Literal::Int(y as i64),
                _ => unimplemented!("{:?}", item),
            }
        }
        AstLiteral::Float(x) => ast::Literal::Float(x.node),
        AstLiteral::String(x) => ast::Literal::String(x.node.clone()),
        _ => unimplemented!("{:?}", item),
    };

    let span_id = env.span_id(span, b);
    Ast::Literal(lit).node(span_id)
}

fn from_binop(item: syntax::ast::BinOp) -> ast::BinaryOperation {
    use syntax::ast::BinOp;
    match item {
        BinOp::Add => ast::BinaryOperation::Add,
        BinOp::Subtract => ast::BinaryOperation::Subtract,
        BinOp::Multiply => ast::BinaryOperation::Multiply,
        BinOp::Divide => ast::BinaryOperation::Divide,
        BinOp::Equal => ast::BinaryOperation::EQ,
        BinOp::NotEqual => ast::BinaryOperation::NE,
        BinOp::Greater => ast::BinaryOperation::GT,
        BinOp::GreaterOrEqual => ast::BinaryOperation::GTE,
        _ => unimplemented!("{:?}", item),
    }
}

fn from_type<P: syntax::ast::AstPayload>(item: &syntax::ast::TypeExprP<P>) -> Option<AstType> {
    match &item.expr.node {
        syntax::ast::ExprP::Identifier(name) => match name.ident.as_str() {
            "float" => Some(AstType::Float),
            "int" => Some(AstType::Int),
            _ => None,
        },
        _ => None,
    }
}

fn from_assign_target<P: syntax::ast::AstPayload>(
    item: syntax::ast::AssignTargetP<P>,
    b: &mut NodeBuilder,
) -> ast::AssignTarget {
    use syntax::ast::AssignTargetP;
    match item {
        AssignTargetP::Identifier(ident) => {
            ast::AssignTarget::Identifier(b.labels.s(&ident.node.ident).into())
        }
        _ => unimplemented!(),
    }
}

pub struct Parser {
    //u: TypeUnify,
}

impl Parser {
    pub fn new() -> Self {
        Self {
            //u: TypeUnify::new(),
        }
    }

    pub fn parse<'a>(
        &mut self,
        path: &Path,
        content: Option<&str>,
        module_key: StringKey,
        file_id: usize,
        b: &mut NodeBuilder,
    ) -> Result<compile_core::AstNode> {
        let dialect = syntax::Dialect::Extended;
        let m = match content {
            Some(content) => {
                syntax::AstModule::parse(path.to_str().unwrap(), content.to_string(), &dialect)?
            }
            None => syntax::AstModule::parse_file(&path, &dialect)?,
        };
        let (codemap, stmt, _dialect, _typecheck) = m.into_parts();
        let mut env = Environment::new(&codemap, file_id);
        let mut seq = b.prelude();
        let ast: compile_core::AstNode = self.from_stmt(stmt, &mut env, b)?;
        let span_id = ast.span_id.clone();
        seq.push(ast);
        Ok(Ast::Module(module_key, NB::seq(seq, span_id).into()).node(span_id))
    }

    fn from_parameter<'a, P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstParameterP<P>,
        env: &mut Environment<'a>,
        b: &mut NodeBuilder,
    ) -> ast::ParameterNode {
        use syntax::ast::ParameterP;
        let span_id = env.span_id(item.span, b);

        match item.node {
            ParameterP::Normal(ident, maybe_type) => {
                let ty = if let Some(ty) = maybe_type.map(|ty| from_type(&ty)) {
                    ty
                } else {
                    Some(b.types.fresh_unknown())
                    //Some(self.u.fresh_unknown())
                    //d.push_diagnostic(env.error(item.span, "Missing Type"));
                    //Some(AstType::Unit)
                };
                ast::ParameterNode {
                    name: b.labels.s(&ident.node.ident),
                    ty: b.types.s(&ty.unwrap()),
                    node: ast::Parameter::Normal,
                    span_id,
                }
            }
            /*

            ParameterP::WithDefaultValue(ident, maybe_type, expr) => {
                let ty = if let Some(ty) = maybe_type.map(|ty| from_type(&ty)) {
                    ty
                } else {
                    Some(self.u.fresh_unknown())
                    //d.push_diagnostic(env.error(item.span, "Missing Type"));
                    //Some(AstType::Unit)
                };
                let expr = self.from_expr(*expr, env, d, b).unwrap();
                ast::ParameterNode {
                    name: b.s(&ident.node.ident),
                    ty: ty.unwrap(),
                    node: ast::Parameter::WithDefault(expr.into()),
                    extra,
                }
            }
            */
            _ => unimplemented!(),
        }
    }

    pub fn from_stmt<'a, P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstStmtP<P>,
        env: &mut Environment<'a>,
        b: &mut NodeBuilder,
    ) -> Result<compile_core::AstNode> {
        use syntax::ast::StmtP;
        let span_id = env.span_id(item.span, b);

        match item.node {
            StmtP::Statements(stmts) => {
                let span_id = env.span_id(item.span, b);
                StatementReader::build(self, stmts, span_id, env, b)
            }

            StmtP::Def(def) => {
                let name = b.labels.s(&def.name.ident);
                let span_id = env.span_id(item.span, b);

                env.enter_func();

                // push function name into scope
                env.define(name);

                let params = def
                    .params
                    .into_iter()
                    .map(|p| self.from_parameter(p, env, b))
                    .collect::<Vec<_>>();

                // push name to environment
                for p in params.iter() {
                    env.define(p.name);
                }

                let mut body = vec![];
                body.extend(self.from_stmt(*def.body, env, b)?.to_vec());

                env.exit_func();
                let return_type = def
                    .return_type
                    .map(|ty| from_type(&ty).unwrap_or(AstType::Unit))
                    .unwrap_or(AstType::Unit);

                let def_ast = Ast::Lambda(ast::Lambda {
                    body: Some(NB::seq(body, span_id).into()),
                    return_type: b.types.s(&return_type),
                    params,
                });

                env.define(name);
                Ok(NB::global(name, def_ast.node(span_id)))
            }

            StmtP::If(expr, truestmt) => {
                let condition = self.from_expr(expr, env, b)?;
                let truestmt = self.from_stmt(*truestmt, env, b)?;
                let span_id = env.span_id(item.span, b);
                Ok(Ast::Conditional(condition.into(), truestmt.into(), None).node(span_id))
            }

            StmtP::IfElse(expr, options) => {
                let condition = self.from_expr(expr, env, b)?;
                let truestmt = self.from_stmt(options.0, env, b)?;
                let elsestmt = self.from_stmt(options.1, env, b)?;
                let span_id = env.span_id(item.span, b);
                Ok(
                    Ast::Conditional(condition.into(), truestmt.into(), Some(elsestmt.into()))
                        .node(span_id),
                )
            }

            StmtP::Return(maybe_expr) => Ok(match maybe_expr {
                Some(expr) => {
                    let node = self.from_expr(expr, env, b)?;
                    Ast::Return(Some(node.into())).node(span_id)
                }
                None => NB::ret(None),
            }),

            StmtP::Assign(assign) => {
                use syntax::ast::AssignTargetP;
                let rhs = self.from_expr(assign.rhs, env, b)?;
                match assign.lhs.node {
                    AssignTargetP::Identifier(ident) => {
                        let name = &ident.node.ident;
                        if let Some(node) = b.build_literal_from_identifier(name) {
                            return Ok(node);
                        }

                        let name = b.labels.s(&ident.node.ident);

                        // lookup
                        if let Some(_data) = env.resolve(name) {
                            Ok(Ast::Assign(AssignTarget::Identifier(name), rhs.into())
                                .node(span_id))
                        } else {
                            // name does not exist in scope
                            // Either create a global or do local, depending on context
                            env.define(name);
                            if env.is_in_func() {
                                Ok(Ast::Assign(AssignTarget::Identifier(name), rhs.into())
                                    .node(span_id))
                            } else {
                                Ok(Ast::Global(name, rhs.into()).node(span_id))
                            }
                        }
                    }
                    _ => unimplemented!(),
                }
            }

            StmtP::Expression(expr) => self.from_expr(expr, env, b),

            _ => unimplemented!("{:?}", item),
        }
    }

    fn is_extra<P: syntax::ast::AstPayload>(&mut self, item: &syntax::ast::AstStmtP<P>) -> bool {
        use syntax::ast::ExprP;
        use syntax::ast::StmtP;

        if let StmtP::Expression(expr) = &item.node {
            match &expr.node {
                ExprP::Dot(expr, name) => {
                    if let ExprP::Identifier(ident) = &expr.node {
                        if &ident.node.ident == "q" && ExtraAst::is_extra(&name) {
                            return true;
                        }
                    } else {
                        unimplemented!("{:?}", (expr, name))
                    }
                }
                ExprP::Call(expr, _) => match &expr.node {
                    ExprP::Dot(expr, name) => {
                        if let ExprP::Identifier(ident) = &expr.node {
                            if &ident.node.ident == "q" && ExtraAst::is_extra(&name) {
                                return true;
                            }
                        }
                    }
                    _ => (),
                },
                _ => (),
            };
        }
        false
    }

    fn read_extra<P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstStmtP<P>,
        env: &mut Environment,
        b: &mut NodeBuilder,
    ) -> Result<ExtraAst> {
        use syntax::ast::ExprP;
        use syntax::ast::StmtP;

        if let StmtP::Expression(expr) = item.node {
            match expr.node {
                ExprP::Dot(expr, name) => {
                    if let ExprP::Identifier(ident) = &expr.node {
                        if &ident.node.ident == "q" && ExtraAst::is_extra(&name) {
                            if let Some(extra) = ExtraAst::from_name(&name, &[], b) {
                                return Ok(extra);
                            }
                        }
                    } else {
                        unimplemented!("{:?}", (expr, name))
                    }
                }
                ExprP::Call(expr, expr_args) => match expr.node {
                    ExprP::Dot(expr, name) => {
                        if let ExprP::Identifier(ident) = &expr.node {
                            if &ident.node.ident == "q" && ExtraAst::is_extra(&name) {
                                let mut args = vec![];
                                for arg in expr_args {
                                    args.push(self.from_argument(arg, env, b)?.into());
                                }
                                if let Some(extra) = ExtraAst::from_name(&name, &args, b) {
                                    return Ok(extra);
                                }
                            }
                        }
                    }
                    _ => (),
                },
                _ => (),
            }
        }
        unreachable!()
    }

    fn from_expr<P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstExprP<P>,
        env: &mut Environment,
        b: &mut NodeBuilder,
    ) -> Result<AstNode> {
        use syntax::ast::ExprP;
        let span_id = env.span_id(item.span, b);

        match item.node {
            ExprP::Dot(expr, name) => {
                if let ExprP::Identifier(ident) = &expr.node {
                    if &ident.node.ident == "q" {
                        // builtin namespace
                        if let Some(ast) = b.build_builtin_from_name(&name, vec![], span_id) {
                            Ok(ast)
                        } else if let Some(extra) = ExtraAst::from_name(&name, &[], b) {
                            match extra {
                                ExtraAst::LoopBreak(maybe_key) => Ok(NB::loop_break(maybe_key)),
                                ExtraAst::LoopContinue(maybe_key) => {
                                    Ok(NB::loop_continue(maybe_key))
                                }
                                _ => unimplemented!(),
                            }
                        } else {
                            assert!(false);
                            b.spans
                                .push_diagnostic(env.error(name.span, "Builtin not found"));
                            let span_id = env.span_id(item.span, b);
                            Ok(Ast::Error.node(span_id))
                        }
                    } else {
                        b.spans.push_diagnostic(env.error(
                            name.span,
                            &format!("Variable not in scope: {}", ident.node.ident),
                        ));
                        let span_id = env.span_id(item.span, b);
                        Ok(Ast::Error.node(span_id))
                    }
                } else {
                    unimplemented!("{:?}", (expr, name))
                }
            }

            ExprP::Op(lhs, op, rhs) => {
                let node_a = self.from_expr(*lhs, env, b)?;
                let node_b = self.from_expr(*rhs, env, b)?;

                let op_node = BinOpNode::new(from_binop(op), node_a.span_id.clone());
                let ast = Ast::BinaryOp(op_node, node_a.into(), node_b.into());
                Ok(ast.node(span_id))
            }

            ExprP::If(args) => {
                let (condition, then_expr, else_expr) = *args;
                let condition = self.from_expr(condition, env, b)?;
                let then_expr = self.from_expr(then_expr, env, b)?;
                let else_expr = self.from_expr(else_expr, env, b)?;
                let span_id = env.span_id(item.span, b);
                Ok(
                    Ast::Ternary(condition.into(), then_expr.into(), else_expr.into())
                        .node(span_id),
                )
            }

            ExprP::Call(expr, expr_args) => {
                let mut args = vec![];
                for arg in expr_args {
                    args.push(self.from_argument(arg, env, b)?.into());
                }
                let t_int = b.types.s(&AstType::Int);

                match expr.node {
                    ExprP::Identifier(ident) => {
                        let name = b.labels.s(&ident.node.ident);
                        if let Some(_data) = env.resolve(name) {
                            let ident_span_id = env.span_id(ident.span, b);
                            let ident = Ast::Identifier(name).node(ident_span_id);
                            let ast = Ast::Call(ident.into(), args, t_int).node(span_id.clone());
                            Ok(ast)
                        } else {
                            b.spans.push_diagnostic(env.error(ident.span, "Not found"));
                            let span_id = env.span_id(item.span, b);
                            Ok(Ast::Error.node(span_id))
                        }
                    }

                    ExprP::Dot(expr, name) => {
                        if let ExprP::Identifier(ident) = &expr.node {
                            let key = b.labels.s(&ident.node.ident);
                            if let Some(_data) = env.resolve(key) {
                                let ident_span_id = env.span_id(ident.span, b);
                                let ident = Ast::Identifier(key).node(ident_span_id);
                                let ast =
                                    Ast::Call(ident.into(), args, t_int).node(span_id.clone());
                                Ok(ast)
                            } else if &ident.node.ident == "q" {
                                // builtin namespace
                                if ExtraAst::is_extra(&name) {
                                    let extra = ExtraAst::from_name(&name, &args, b).unwrap();
                                    return match extra {
                                        ExtraAst::LoopBreak(maybe_key) => {
                                            Ok(NB::loop_break(maybe_key))
                                        }
                                        ExtraAst::LoopContinue(maybe_key) => {
                                            Ok(NB::loop_continue(maybe_key))
                                        }
                                        _ => unimplemented!(),
                                    };
                                }

                                if let Some(ast) = b.build_builtin_from_name(&name, args, span_id) {
                                    // define things appropriately
                                    match ast.node {
                                        Ast::Global(name, _) => {
                                            env.define(name);
                                        }
                                        _ => (),
                                    }
                                    Ok(ast)
                                } else {
                                    b.spans
                                        .push_diagnostic(env.error(name.span, "Builtin not found"));
                                    let span_id = env.span_id(item.span, b);
                                    Ok(Ast::Error.node(span_id))
                                }
                            } else {
                                b.spans.push_diagnostic(env.error(
                                    name.span,
                                    &format!("Variable not in scope: {}", ident.node.ident),
                                ));
                                let span_id = env.span_id(item.span, b);
                                Ok(Ast::Error.node(span_id))
                            }
                        } else {
                            unimplemented!("{:?}", (expr, name))
                        }
                    }
                    _ => unimplemented!("{:?}", expr.node),
                }
            }

            ExprP::Identifier(ident) => {
                if let Some(node) = b.build_literal_from_identifier(&ident.node.ident) {
                    return Ok(node);
                }

                let name = b.labels.s(&ident.node.ident);
                let span_id = env.span_id(item.span, b);
                if let Some(_data) = env.resolve(name) {
                    let ast = Ast::Identifier(name).node(span_id);
                    Ok(ast)
                } else {
                    b.spans.push_diagnostic(env.error(
                        ident.span,
                        &format!("Variable not in scope: {}", ident.node.ident),
                    ));
                    Ok(Ast::Error.node(span_id))
                }
            }

            ExprP::Literal(lit) => Ok(from_literal(lit, item.span, env, b)),

            ExprP::Minus(expr) => {
                let ast = Ast::UnaryOp(
                    ast::UnaryOperation::Minus,
                    self.from_expr(*expr, env, b)?.into(),
                );
                Ok(ast.node(span_id))
            }

            _ => unimplemented!("{:?}", item.node),
        }
    }

    fn from_argument<P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstArgumentP<P>,
        env: &mut Environment,
        b: &mut NodeBuilder,
    ) -> Result<ast::Argument> {
        use syntax::ast::ArgumentP;
        match item.node {
            ArgumentP::Positional(expr) => Ok(self.from_expr(expr, env, b)?.into()),
            _ => unimplemented!(),
        }
    }
}

struct StatementReader<P: syntax::ast::AstPayload> {
    loop_names: Vec<StringKey>,
    block_names: Vec<StringKey>,
    stack: Vec<(StackType, Vec<AstNode>)>,
    spans: Vec<SpanId>,
    seq: Vec<AstNode>,
    _p: std::marker::PhantomData<P>,
}

#[derive(Debug, PartialEq, Eq)]
enum StackType {
    Loop,
    Block,
}

impl<P: syntax::ast::AstPayload> StatementReader<P> {
    fn new() -> Self {
        Self {
            loop_names: vec![],
            block_names: vec![],
            stack: vec![],
            spans: vec![],
            seq: vec![],
            _p: std::marker::PhantomData::default(),
        }
    }

    fn start_loop(&mut self, key: StringKey, span_id: SpanId) {
        self.loop_names.push(key);
        self.stack.push((StackType::Loop, vec![]));
        self.spans.push(span_id)
    }

    fn end_loop(&mut self) -> AstNode {
        let (stack_type, seq) = self.stack.pop().unwrap();
        assert_eq!(stack_type, StackType::Loop);
        let span_id = self.spans.pop().unwrap();
        let key = self.loop_names.pop().unwrap();
        Ast::Loop(key, NB::seq(seq, span_id).into()).into()
    }

    fn start_block(&mut self, key: StringKey, span_id: SpanId) {
        self.block_names.push(key);
        self.stack.push((StackType::Block, vec![]));
        self.spans.push(span_id)
    }

    fn end_block(&mut self) -> AstNode {
        let (stack_type, seq) = self.stack.pop().unwrap();
        assert_eq!(stack_type, StackType::Block);
        let span_id = self.spans.pop().unwrap();
        let key = self.block_names.pop().unwrap();
        Ast::Block(key, vec![], NB::seq(seq, span_id).into()).into()
    }

    fn is_type(&self, t: StackType) -> bool {
        self.stack
            .last()
            .as_ref()
            .map(|v| v.0 == t)
            .unwrap_or(false)
    }

    fn is_block(&self) -> bool {
        self.is_type(StackType::Block)
    }

    fn is_loop(&self) -> bool {
        self.is_type(StackType::Loop)
    }

    fn push_ast(&mut self, ast: AstNode) {
        if self.stack.len() == 0 {
            self.seq.push(ast);
        } else {
            self.stack.last_mut().unwrap().1.push(ast);
        }
    }

    fn push_stmt(
        &mut self,
        stmt: syntax::ast::AstStmtP<P>,
        parse: &mut Parser,
        env: &mut Environment,
        b: &mut NodeBuilder,
    ) -> Result<()> {
        if parse.is_extra(&stmt) {
            let span_id = env.span_id(stmt.span.clone(), b);

            let extra = parse.read_extra(stmt, env, b)?;
            match extra {
                ExtraAst::LoopStart(maybe_key) => {
                    let key = if let Some(key) = maybe_key {
                        key
                    } else {
                        b.fresh_loop_name()
                    };
                    self.start_loop(key, span_id);
                }
                ExtraAst::LoopBreak(maybe_key) => {
                    self.push_ast(NB::loop_break(maybe_key));
                }
                ExtraAst::LoopContinue(maybe_key) => {
                    self.push_ast(NB::loop_continue(maybe_key));
                }
                ExtraAst::BlockEnd => {
                    let ast = self.end_loop();
                    self.push_ast(ast);
                }
                ExtraAst::Label(key) => {
                    self.start_block(key, span_id);
                    //self.push_ast(NB::block_start(key, vec![]))
                }
                ExtraAst::Goto(key) => {
                    if self.is_block() {
                        let ast = self.end_block();
                        self.push_ast(ast);
                    } else {
                        self.push_ast(NB::goto(key));
                    }
                } //_ => unimplemented!()
            }
        } else {
            let ast = parse.from_stmt(stmt, env, b)?;
            self.push_ast(ast);
        }

        Ok(())
    }

    fn build(
        parse: &mut Parser,
        stmts: Vec<syntax::ast::AstStmtP<P>>,
        span_id: SpanId,
        env: &mut Environment,
        b: &mut NodeBuilder,
    ) -> Result<AstNode> {
        let mut reader = Self::new();
        for stmt in stmts {
            reader.push_stmt(stmt, parse, env, b)?;
        }

        if reader.stack.len() > 0 {
            let span = b.spans.lookup(span_id);
            b.spans
                .push_diagnostic(b.spans.error("Mismatched end loop", &span));
        }

        Ok(NB::seq(reader.seq.drain(..).collect(), span_id))
    }
}

#[derive(Default)]
pub struct StarlarkParser {
    link: LinkOptions,
}

impl StarlarkParser {
    pub fn new() -> Self {
        Self {
            link: LinkOptions::new(),
        }
    }

    pub fn flatten(
        &mut self,
        filename: &str,
        b: &mut NodeBuilder,
        _verbose: bool,
    ) -> Result<AstNode> {
        log::debug!("flatten: {}", filename);
        let file_id = b
            .spans
            .add_source(filename.to_string(), std::fs::read_to_string(filename)?);
        let mut parser = Parser::new();
        let module_key = b.labels.s("module");
        let ast: AstNode = parser.parse(Path::new(filename), None, module_key, file_id, b)?;
        b.dump_ast(&ast);

        let mut fenv = FlattenEnvironment::new();
        let mut f = Flatten::flatten_module(ast, &mut fenv)?;
        f.run_loop(&mut fenv, b)?;
        f.dump_ast(b);
        let m = f.module(b);
        m.dump(b);

        let ast: AstNode = parser.parse(Path::new(filename), None, module_key, file_id, b)?;
        Ok(ast)
    }

    pub fn parse(
        &mut self,
        filename: &str,
        b: &mut NodeBuilder,
        _verbose: bool,
    ) -> Result<AstNode> {
        log::debug!("parsing: {}", filename);
        let file_id = b
            .spans
            .add_source(filename.to_string(), std::fs::read_to_string(filename)?);

        let mut parser = Parser::new();
        let module_key = b.labels.s("module");
        let ast: AstNode = parser.parse(Path::new(filename), None, module_key, file_id, b)?;
        b.dump_ast(&ast);
        let ast: AstNode = parser.parse(Path::new(filename), None, module_key, file_id, b)?;
        Ok(ast)
    }

    pub fn blockify(
        &mut self,
        ast: AstNode,
        b: &mut NodeBuilder,
        _verbose: bool,
    ) -> Result<(Blockify, ValueId)> {
        let mut blockify = Blockify::new();
        let r = blockify.build_module(ast, b);
        blockify.dump(b);
        dump::code::save_graph(&blockify, "out.dot", b);

        let j = dump::code::get_json(&blockify, b);
        let mut file = std::fs::File::create("blocks.json").unwrap();
        file.write_all(j.as_bytes()).unwrap();

        let module_block_id = r?;
        Ok((blockify, module_block_id))
    }

    pub fn lower<'c>(
        &mut self,
        blockify: Blockify,
        module_block_id: ValueId,
        context: &'c lower_mlir::Context,
        module: &mut Module<'c>,
        b: &mut NodeBuilder,
    ) -> Result<()> {
        let mut lower = lower_mlir::Lower::new(context, module_block_id);
        let mut blocks = lower_mlir::LowerBlocks::new();
        lower.lower_module(&blockify, &mut blocks, module, b)?;
        for lib in blockify.shared_libraries() {
            self.link.add_library(&lib);
        }
        Ok(())
    }

    pub fn exec_main<'c>(
        &self,
        context: &lower_mlir::Context,
        module: &mut Module,
        libpath: &str,
        verbose: bool,
    ) -> i32 {
        // lower mlir to llvmir
        if verbose {
            println!(
                "lowered {}",
                module
                    .as_operation()
                    .to_string_with_flags(lower_mlir::OperationPrintingFlags::new())
                    .unwrap()
            );
        }

        let pass_manager = lower_mlir::default_pass_manager(context);
        pass_manager.run(module).unwrap();
        assert!(module.as_operation().verify());

        if verbose {
            println!(
                "after pass {}",
                module
                    .as_operation()
                    .to_string_with_flags(lower_mlir::OperationPrintingFlags::new())
                    .unwrap()
            );
        }

        lower_mlir::compile::exec_main(&self.link.shared_libraries(), module, libpath)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::StarlarkParser;
    use lower_mlir::Location;
    use test_log::test;

    fn run_test_ir(filename: &str, expected: i32) {
        let mut p: StarlarkParser = StarlarkParser::new();
        let mut b = flat::NodeBuilder::new();
        let result = p.parse(filename, &mut b, true);
        b.spans.diagnostics_dump();
        let ast = result.unwrap();
        //return;

        let result = p.blockify(ast, &mut b, true);
        let (blockify, module_block_id) = result.unwrap();

        let context = lower_mlir::default_context();
        let mut module = lower_mlir::Module::new(Location::unknown(&context));
        let r = p.lower(blockify, module_block_id, &context, &mut module, &mut b);
        b.spans.diagnostics_dump();
        r.unwrap();
        let verify = module.as_operation().verify();
        module.as_operation().dump();
        assert!(verify);
        let r = p.exec_main(&context, &mut module, "../target/debug/", true);
        assert_eq!(expected, r);
    }

    #[test]
    fn test_recursive() {
        run_test_ir("../tests/test_recursive.star", 0);
    }

    #[test]
    fn test_goto() {
        run_test_ir("../tests/goto.star", 0);
    }

    #[test]
    fn test_bare() {
        run_test_ir("../tests/bare.star", 0);
    }

    #[test]
    fn test_fix() {
        run_test_ir("../tests/fix.star", 0);
    }

    #[test]
    fn test_nothing() {
        run_test_ir("../tests/test.star", 0);
    }

    #[test]
    fn test_global() {
        run_test_ir("../tests/test_global.star", 0);
    }

    #[test]
    fn test_static() {
        run_test_ir("../tests/test_static.star", 0);
    }

    #[test]
    fn test_float() {
        run_test_ir("../tests/test_float.star", 0);
    }

    #[test]
    fn test_cond() {
        run_test_ir("../tests/test_cond.star", 0);
    }

    #[test]
    fn test_loop() {
        run_test_ir("../tests/loop.star", 0);
    }

    #[test]
    fn test_nested_func() {
        run_test_ir("../tests/nested_func.star", 0);
    }

    #[test]
    fn test_static_var() {
        run_test_ir("../tests/static_var.star", 0);
    }
}
