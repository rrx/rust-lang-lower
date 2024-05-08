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
    SpanId, StringKey, TypeUnify,
};

use flat::{Blockify, NodeBuilder, ValueId};

use lower::LinkOptions;
use lower::Module;

#[derive(Debug, Clone)]
pub enum ExtraAst {
    LoopStart(Option<StringKey>),
    LoopBreak(Option<StringKey>),
    LoopContinue(Option<StringKey>),
    BlockEnd,
}

impl ExtraAst {
    pub fn is_extra(name: &str) -> bool {
        name == "loop" || name == "loop_break" || name == "loop_continue" || name == "end"
    }

    pub fn from_name(name: &str, mut args: Vec<Argument>, b: &mut NodeBuilder) -> Option<ExtraAst> {
        if name == "loop" {
            if args.len() == 0 {
                Some(Self::LoopStart(None))
            } else if args.len() == 1 {
                let Argument::Positional(arg) = args.pop().unwrap();
                let s = arg.try_string().unwrap();
                let key = b.s(&s);
                Some(Self::LoopStart(Some(key)))
            } else {
                unreachable!()
            }
        } else if name == "loop_break" {
            if args.len() == 0 {
                Some(Self::LoopBreak(None))
            } else if args.len() == 1 {
                let Argument::Positional(arg) = args.pop().unwrap();
                let s = arg.try_string().unwrap();
                let key = b.s(&s);
                Some(Self::LoopBreak(Some(key)))
            } else {
                unreachable!()
            }
        } else if name == "loop_continue" {
            if args.len() == 0 {
                Some(Self::LoopContinue(None))
            } else if args.len() == 1 {
                let Argument::Positional(arg) = args.pop().unwrap();
                let s = arg.try_string().unwrap();
                let key = b.s(&s);
                Some(Self::LoopContinue(Some(key)))
            } else {
                unreachable!()
            }
        } else if name == "end" {
            assert_eq!(args.len(), 0);
            Some(ExtraAst::BlockEnd)
        } else {
            None
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

pub fn get_span_id(file_id: usize, span: codemap::Span, b: &mut NodeBuilder) -> SpanId {
    let begin = CodeLocation {
        pos: span.begin().get(),
    };
    let end = CodeLocation {
        pos: span.end().get(),
    };
    b.spans.get_span(file_id, begin.clone(), end.clone())
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
                //_ => env.unimplemented(span),
                _ => unimplemented!("{:?}", item),
            }
        }
        AstLiteral::Float(x) => ast::Literal::Float(x.node),
        AstLiteral::String(x) => ast::Literal::String(x.node.clone()),
        //_ => env.unimplemented(span),
        _ => unimplemented!("{:?}", item),
    };
    //let extra = env.extra(span, d);
    //get_span_id(

    let span_id = env.span_id(span, b);
    b.build(Ast::Literal(lit), span_id)
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
            ast::AssignTarget::Identifier(b.s(&ident.node.ident).into())
        }
        _ => unimplemented!(),
    }
}

pub struct Parser {
    u: TypeUnify,
}

impl Parser {
    pub fn new() -> Self {
        Self {
            u: TypeUnify::new(),
        }
    }

    pub fn parse<'a>(
        &mut self,
        path: &Path,
        content: Option<&str>,
        module_key: StringKey,
        file_id: usize,
        //d: &mut Diagnostics,
        b: &mut NodeBuilder,
    ) -> Result<compile_core::AstNode> {
        //b.enter(file_id, path.to_str().unwrap());
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
        Ok(b.build(Ast::Module(module_key, b.seq(seq).into()), span_id))
    }

    fn from_parameter<'a, P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstParameterP<P>,
        env: &mut Environment<'a>,
        b: &mut NodeBuilder,
    ) -> ast::ParameterNode {
        use syntax::ast::ParameterP;
        let span_id = get_span_id(env.file_id, item.span, b);

        match item.node {
            ParameterP::Normal(ident, maybe_type) => {
                let ty = if let Some(ty) = maybe_type.map(|ty| from_type(&ty)) {
                    ty
                } else {
                    Some(self.u.fresh_unknown())
                    //d.push_diagnostic(env.error(item.span, "Missing Type"));
                    //Some(AstType::Unit)
                };
                ast::ParameterNode {
                    name: b.s(&ident.node.ident),
                    ty: b.t(&ty.unwrap()),
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
            StmtP::Statements(stmts) => StatementReader::build(self, stmts, env, b),

            StmtP::Def(def) => {
                let name = b.s(&def.name.ident);

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

                let def_ast = Ast::Definition(ast::Definition {
                    body: Some(b.seq(body).into()),
                    return_type: b.t(&return_type),
                    params,
                });

                env.define(name);
                Ok(b.global(name, b.build(def_ast, span_id)))
            }

            StmtP::If(expr, truestmt) => {
                let condition = self.from_expr(expr, env, b)?;
                let truestmt = self.from_stmt(*truestmt, env, b)?;
                let span_id = env.span_id(item.span, b);
                Ok(b.build(
                    Ast::Conditional(condition.into(), truestmt.into(), None),
                    span_id,
                ))
            }

            StmtP::IfElse(expr, options) => {
                let condition = self.from_expr(expr, env, b)?;
                let truestmt = self.from_stmt(options.0, env, b)?;
                let elsestmt = self.from_stmt(options.1, env, b)?;
                let span_id = env.span_id(item.span, b);
                Ok(b.build(
                    Ast::Conditional(condition.into(), truestmt.into(), Some(elsestmt.into())),
                    span_id,
                ))
            }

            StmtP::Return(maybe_expr) => Ok(match maybe_expr {
                Some(expr) => {
                    let node = self.from_expr(expr, env, b)?;
                    b.build(Ast::Return(Some(node.into())), span_id)
                }
                None => b.ret(None),
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

                        let name = b.s(&ident.node.ident);

                        // lookup
                        if let Some(_data) = env.resolve(name) {
                            Ok(b.build(
                                Ast::Assign(AssignTarget::Identifier(name), rhs.into()),
                                span_id,
                            ))
                        } else {
                            // name does not exist in scope
                            // Either create a global or do local, depending on context
                            env.define(name);
                            if env.is_in_func() {
                                Ok(b.build(
                                    Ast::Assign(AssignTarget::Identifier(name), rhs.into()),
                                    span_id,
                                ))
                            } else {
                                Ok(b.build(Ast::Global(name, rhs.into()), span_id))
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
                            if let Some(extra) = ExtraAst::from_name(&name, vec![], b) {
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
                                if let Some(extra) = ExtraAst::from_name(&name, args, b) {
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
                        } else if let Some(extra) = ExtraAst::from_name(&name, vec![], b) {
                            match extra {
                                ExtraAst::LoopBreak(maybe_key) => Ok(b.loop_break(maybe_key)),
                                ExtraAst::LoopContinue(maybe_key) => Ok(b.loop_continue(maybe_key)),
                                _ => unimplemented!(),
                            }
                        } else {
                            assert!(false);
                            b.spans
                                .push_diagnostic(env.error(name.span, "Builtin not found"));
                            let span_id = env.span_id(item.span, b);
                            Ok(b.error(span_id))
                        }
                    } else {
                        b.spans.push_diagnostic(env.error(
                            name.span,
                            &format!("Variable not in scope: {}", ident.node.ident),
                        ));
                        let span_id = env.span_id(item.span, b);
                        Ok(b.error(span_id))
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
                Ok(b.build(ast, span_id))
            }

            ExprP::If(args) => {
                let (condition, then_expr, else_expr) = *args;
                let condition = self.from_expr(condition, env, b)?;
                let then_expr = self.from_expr(then_expr, env, b)?;
                let else_expr = self.from_expr(else_expr, env, b)?;
                let span_id = env.span_id(item.span, b);
                Ok(b.build(
                    Ast::Ternary(condition.into(), then_expr.into(), else_expr.into()),
                    span_id,
                ))
            }

            ExprP::Call(expr, expr_args) => {
                let mut args = vec![];
                for arg in expr_args {
                    args.push(self.from_argument(arg, env, b)?.into());
                }
                let t_int = b.t(&AstType::Int);

                match expr.node {
                    ExprP::Identifier(ident) => {
                        let name = b.s(&ident.node.ident);
                        if let Some(_data) = env.resolve(name) {
                            let ident_span_id = env.span_id(ident.span, b);
                            let ident = b.build(Ast::Identifier(name), ident_span_id);
                            let ast =
                                b.build(Ast::Call(ident.into(), args, t_int), span_id.clone());
                            Ok(ast)
                        } else {
                            b.spans.push_diagnostic(env.error(ident.span, "Not found"));
                            let span_id = env.span_id(item.span, b);
                            Ok(b.error(span_id))
                        }
                    }

                    ExprP::Dot(expr, name) => {
                        if let ExprP::Identifier(ident) = &expr.node {
                            let key = b.s(&ident.node.ident);
                            if let Some(_data) = env.resolve(key) {
                                let ident_span_id = env.span_id(ident.span, b);
                                let ident = b.build(Ast::Identifier(key), ident_span_id);
                                let ast =
                                    b.build(Ast::Call(ident.into(), args, t_int), span_id.clone());
                                Ok(ast)
                            } else if &ident.node.ident == "q" {
                                // builtin namespace
                                if ExtraAst::is_extra(&name) {
                                    let extra = ExtraAst::from_name(&name, args, b).unwrap();
                                    return match extra {
                                        ExtraAst::LoopBreak(maybe_key) => {
                                            Ok(b.loop_break(maybe_key))
                                        }
                                        ExtraAst::LoopContinue(maybe_key) => {
                                            Ok(b.loop_continue(maybe_key))
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
                                    Ok(b.error(span_id))
                                }
                            } else {
                                b.spans.push_diagnostic(env.error(
                                    name.span,
                                    &format!("Variable not in scope: {}", ident.node.ident),
                                ));
                                let span_id = env.span_id(item.span, b);
                                Ok(b.error(span_id))
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

                let name = b.s(&ident.node.ident);
                let span_id = env.span_id(item.span, b);
                if let Some(_data) = env.resolve(name) {
                    let ast = b.build(Ast::Identifier(name), span_id);
                    Ok(ast)
                } else {
                    b.spans.push_diagnostic(env.error(
                        ident.span,
                        &format!("Variable not in scope: {}", ident.node.ident),
                    ));
                    Ok(b.error(span_id))
                }
            }

            ExprP::Literal(lit) => Ok(from_literal(lit, item.span, env, b)),

            ExprP::Minus(expr) => {
                let ast = Ast::UnaryOp(
                    ast::UnaryOperation::Minus,
                    self.from_expr(*expr, env, b)?.into(),
                );
                Ok(b.build(ast, span_id))
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
    names: Vec<StringKey>,
    loops: Vec<Vec<AstNode>>,
    seq: Vec<AstNode>,
    _p: std::marker::PhantomData<P>,
}

impl<P: syntax::ast::AstPayload> StatementReader<P> {
    fn new() -> Self {
        Self {
            names: vec![],
            loops: vec![],
            seq: vec![],
            _p: std::marker::PhantomData::default(),
        }
    }

    fn start_loop(&mut self, key: StringKey) {
        self.names.push(key);
        self.loops.push(vec![]);
    }

    fn end_loop(&mut self, b: &mut NodeBuilder) -> AstNode {
        let seq = self.loops.pop().unwrap();
        let key = self.names.pop().unwrap();
        b.node(Ast::Loop(key, b.seq(seq).into()))
    }

    fn push_ast(&mut self, ast: AstNode) {
        if self.loops.len() == 0 {
            self.seq.push(ast);
        } else {
            self.loops.last_mut().unwrap().push(ast);
        }
    }

    fn push_stmt(
        &mut self,
        stmt: syntax::ast::AstStmtP<P>,
        parse: &mut Parser,
        env: &mut Environment,
        b: &mut NodeBuilder,
    ) -> Result<()> {
        let ast = parse.from_stmt(stmt, env, b)?;
        self.push_ast(ast);
        Ok(())
    }

    fn build(
        parse: &mut Parser,
        stmts: Vec<syntax::ast::AstStmtP<P>>,
        env: &mut Environment,
        b: &mut NodeBuilder,
    ) -> Result<AstNode> {
        let mut reader = Self::new();
        for stmt in stmts {
            if parse.is_extra(&stmt) {
                let extra = parse.read_extra(stmt, env, b)?;
                match extra {
                    ExtraAst::LoopStart(maybe_key) => {
                        let key = if let Some(key) = maybe_key {
                            key
                        } else {
                            b.fresh_loop_name()
                        };
                        reader.start_loop(key);
                    }
                    ExtraAst::LoopBreak(maybe_key) => {
                        reader.push_ast(b.loop_break(maybe_key));
                    }
                    ExtraAst::LoopContinue(maybe_key) => {
                        reader.push_ast(b.loop_continue(maybe_key));
                    }
                    ExtraAst::BlockEnd => {
                        let ast = reader.end_loop(b);
                        reader.push_ast(ast);
                    }
                }
            } else {
                reader.push_stmt(stmt, parse, env, b)?;
            }
        }
        Ok(b.seq(reader.seq.drain(..).collect()))
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

    pub fn parse(
        &mut self,
        filename: &str,
        b: &mut NodeBuilder,
        _verbose: bool,
    ) -> Result<(Blockify, ValueId)> {
        log::debug!("parsing: {}", filename);
        //let file_id = d.add_source(filename.to_string(), std::fs::read_to_string(filename)?);
        let file_id = b
            .spans
            .add_source(filename.to_string(), std::fs::read_to_string(filename)?);

        let mut parser = Parser::new();
        let module_key = b.s("module");
        let ast: AstNode = parser.parse(Path::new(filename), None, module_key, file_id, b)?;
        dump::ast::dump(&ast, b);

        let mut blockify = Blockify::new();
        let r = blockify.build_module(ast, b);
        dump::env::blockify_dump(&blockify, b);
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
        context: &'c lower::Context,
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
        context: &lower::Context,
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
                    .to_string_with_flags(lower::OperationPrintingFlags::new())
                    .unwrap()
            );
        }

        let pass_manager = lower::default_pass_manager(context);
        pass_manager.run(module).unwrap();
        assert!(module.as_operation().verify());

        if verbose {
            println!(
                "after pass {}",
                module
                    .as_operation()
                    .to_string_with_flags(lower::OperationPrintingFlags::new())
                    .unwrap()
            );
        }

        lower::compile::exec_main(&self.link.shared_libraries(), module, libpath)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::StarlarkParser;
    use lower::Location;
    use test_log::test;

    fn run_test_ir(filename: &str, expected: i32) {
        let mut p: StarlarkParser = StarlarkParser::new();
        let mut b = flat::NodeBuilder::new();
        let context = lower::default_context();
        let mut module = lower::Module::new(Location::unknown(&context));
        let result = p.parse(filename, &mut b, true);
        b.spans.diagnostics_dump();
        let (blockify, module_block_id) = result.unwrap();

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
