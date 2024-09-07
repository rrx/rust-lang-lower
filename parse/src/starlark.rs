use std::collections::HashMap;
use std::path::Path;

use anyhow::Result;

use starlark_syntax::codemap;
use starlark_syntax::codemap::CodeMap;
use starlark_syntax::lexer;
use starlark_syntax::syntax;
use starlark_syntax::syntax::module::AstModuleFields;

use compile_core::{
    ast, AssignTarget, Ast, AstNode, AstType, BinOpNode, CodeLocation, Diagnostic, Label,
    LinkOptions, SpanId, StringKey,
};

use flat::{ICodeModule, NodeBuilder, NodeBuilder as NB, ValueId};

use lower_mlir::Module;

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
    item: &syntax::ast::AstLiteral,
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

pub struct Parser {}

impl Parser {
    pub fn new() -> Self {
        Self {}
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
        println!("m: {:?}", m);
        let (codemap, stmt, _dialect, _typecheck) = m.into_parts();
        let mut env = Environment::new(&codemap, file_id);
        let mut seq = b.prelude();
        let span_id = env.span_id(codemap.full_span(), b);
        let ast: compile_core::AstNode = self.from_stmt(&stmt, &mut env, b)?;
        seq.push(ast);
        Ok(Ast::Module(module_key, NB::seq(seq, span_id).into()).node(span_id))
    }

    fn from_parameter<'a, P: syntax::ast::AstPayload>(
        &mut self,
        item: &syntax::ast::AstParameterP<P>,
        env: &mut Environment<'a>,
        b: &mut NodeBuilder,
    ) -> ast::ParameterNode {
        use syntax::ast::ParameterP;
        let span_id = env.span_id(item.span, b);

        match &item.node {
            ParameterP::Normal(ident, maybe_type) => {
                let ty = if let Some(ty) = maybe_type.as_ref().map(|ty| from_type(&ty)) {
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
        item: &syntax::ast::AstStmtP<P>,
        env: &mut Environment<'a>,
        b: &mut NodeBuilder,
    ) -> Result<compile_core::AstNode> {
        use syntax::ast::StmtP;
        let span_id = env.span_id(item.span, b);

        match &item.node {
            StmtP::Statements(stmts) => {
                let span_id = env.span_id(item.span, b);
                let mut seq = vec![];
                for s in stmts {
                    let ast = self.from_stmt(s, env, b)?;
                    seq.push(ast);
                }
                Ok(NodeBuilder::seq(seq, span_id))
            }

            StmtP::Def(def) => {
                let name = b.labels.s(&def.name.ident);
                let span_id = env.span_id(item.span, b);
                let is_nested = env.is_in_func();

                env.enter_func();

                // push function name into scope
                env.define(name);

                let params = def
                    .params
                    .iter()
                    .map(|p| self.from_parameter(p, env, b))
                    .collect::<Vec<_>>();

                // push name to environment
                for p in params.iter() {
                    env.define(p.name);
                }

                let mut body = vec![];
                body.extend(self.from_stmt(&def.body, env, b)?.to_vec());

                env.exit_func();

                let return_type = def
                    .return_type
                    .as_ref()
                    .map(|ty| from_type(&ty).unwrap_or(AstType::Unit))
                    .unwrap_or(AstType::Unit);

                let body = NB::seq(body, span_id).into();

                let arg_type = AstType::Struct(
                    params
                        .iter()
                        .map(|p| {
                            let ty = b.types.r(p.ty);
                            (Some(p.name), ty.clone())
                        })
                        .collect::<Vec<_>>(),
                );

                let arg_type_id = b.types.s(&arg_type);

                let def_ast = Ast::Lambda(ast::Lambda {
                    arg_type: arg_type_id,
                    body: Some(body),
                    return_type: b.types.s(&return_type),
                    //params,
                });

                env.define(name);
                if is_nested {
                    Ok(NB::assign(name, def_ast.node(span_id)))
                } else {
                    Ok(NB::global(name, def_ast.node(span_id)))
                }
            }

            StmtP::If(expr, truestmt) => {
                let condition = self.from_expr(expr, env, b)?;
                let truestmt = self.from_stmt(&truestmt, env, b)?;
                let span_id = env.span_id(item.span, b);
                Ok(Ast::Conditional(condition.into(), truestmt.into(), None).node(span_id))
            }

            StmtP::IfElse(expr, options) => {
                let condition = self.from_expr(expr, env, b)?;
                let truestmt = self.from_stmt(&options.0, env, b)?;
                let elsestmt = self.from_stmt(&options.1, env, b)?;
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
                let rhs = self.from_expr(&assign.rhs, env, b)?;
                match &assign.lhs.node {
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

    fn read_extra<P: syntax::ast::AstPayload>(
        &mut self,
        item: &syntax::ast::AstStmtP<P>,
        env: &mut Environment,
        b: &mut NodeBuilder,
    ) -> Result<Option<AstNode>> {
        use syntax::ast::ExprP;
        use syntax::ast::StmtP;

        if let StmtP::Expression(expr) = &item.node {
            match &expr.node {
                ExprP::Dot(expr, name) => {
                    if let ExprP::Identifier(ident) = &expr.node {
                        if &ident.node.ident == "q" {
                            let span_id = env.span_id(item.span, b);
                            if let Some(extra) = b.build_builtin_from_name(&name, vec![], span_id) {
                                return Ok(Some(extra));
                            }
                        }
                    } else {
                        unimplemented!("{:?}", (expr, name))
                    }
                }
                ExprP::Call(expr, expr_args) => match &expr.node {
                    ExprP::Dot(expr, name) => {
                        if let ExprP::Identifier(ident) = &expr.node {
                            if &ident.node.ident == "q" {
                                let mut args = vec![];
                                for arg in expr_args {
                                    args.push(self.from_argument(arg, env, b)?.into());
                                }
                                let span_id = env.span_id(item.span, b);
                                if let Some(extra) = b.build_builtin_from_name(&name, args, span_id)
                                {
                                    return Ok(Some(extra));
                                }
                            }
                        }
                    }
                    _ => (),
                },
                _ => (),
            }
        }
        Ok(None)
    }

    fn from_expr<P: syntax::ast::AstPayload>(
        &mut self,
        item: &syntax::ast::AstExprP<P>,
        env: &mut Environment,
        b: &mut NodeBuilder,
    ) -> Result<AstNode> {
        use syntax::ast::ExprP;
        let span_id = env.span_id(item.span, b);

        match &item.node {
            ExprP::Dot(expr, name) => {
                if let ExprP::Identifier(ident) = &expr.node {
                    if &ident.node.ident == "q" {
                        // check builtin namespace
                        if let Some(ast) = b.build_builtin_from_name(&name, vec![], span_id) {
                            return Ok(ast);
                        }

                        // didn't find anything matching
                        b.spans
                            .push_diagnostic(env.error(name.span, "Builtin not found"));
                        Ok(Ast::Error.node(span_id))
                    } else {
                        b.spans.push_diagnostic(env.error(
                            name.span,
                            &format!("Variable not in scope: {}", ident.node.ident),
                        ));
                        Ok(Ast::Error.node(span_id))
                    }
                } else {
                    unimplemented!("{:?}", (expr, name))
                }
            }

            ExprP::Op(lhs, op, rhs) => {
                let node_a = self.from_expr(&lhs, env, b)?;
                let node_b = self.from_expr(&rhs, env, b)?;

                let op_node = BinOpNode::new(from_binop(*op), node_a.span_id.clone());
                let ast = Ast::BinaryOp(op_node, node_a.into(), node_b.into());
                Ok(ast.node(span_id))
            }

            ExprP::If(args) => {
                let condition = &args.0;
                let then_expr = &args.1;
                let else_expr = &args.2;
                let condition = self.from_expr(&condition, env, b)?;
                let then_expr = self.from_expr(&then_expr, env, b)?;
                let else_expr = self.from_expr(&else_expr, env, b)?;
                Ok(
                    Ast::Ternary(condition.into(), then_expr.into(), else_expr.into())
                        .node(span_id),
                )
            }

            ExprP::Call(expr, expr_args) => {
                let mut args = vec![];
                for arg in expr_args {
                    args.push(self.from_argument(&arg, env, b)?.into());
                }
                let t_int = b.types.s(&AstType::Int);

                match &expr.node {
                    ExprP::Identifier(ident) => {
                        let name = b.labels.s(&ident.node.ident);
                        if let Some(_data) = env.resolve(name) {
                            let ident_span_id = env.span_id(ident.span, b);
                            let ident = Ast::Identifier(name).node(ident_span_id);
                            let ast = Ast::Call(ident.into(), args, t_int).node(span_id.clone());
                            Ok(ast)
                        } else {
                            b.spans.push_diagnostic(env.error(ident.span, "Not found"));
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
                                    Ok(Ast::Error.node(span_id))
                                }
                            } else {
                                b.spans.push_diagnostic(env.error(
                                    name.span,
                                    &format!("Variable not in scope: {}", ident.node.ident),
                                ));
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

                // no need to check if it's in scope, we just pass along
                // We check scope in the target AST
                Ok(Ast::Identifier(name).node(span_id))
            }

            ExprP::Literal(lit) => Ok(from_literal(lit, item.span, env, b)),

            ExprP::Minus(expr) => {
                let ast = Ast::UnaryOp(
                    ast::UnaryOperation::Minus,
                    self.from_expr(&expr, env, b)?.into(),
                );
                Ok(ast.node(span_id))
            }

            _ => unimplemented!("{:?}", item.node),
        }
    }

    fn from_argument<P: syntax::ast::AstPayload>(
        &mut self,
        item: &syntax::ast::AstArgumentP<P>,
        env: &mut Environment,
        b: &mut NodeBuilder,
    ) -> Result<ast::Argument> {
        use syntax::ast::ArgumentP;
        match &item.node {
            ArgumentP::Positional(expr) => Ok(self.from_expr(expr, env, b)?.into()),
            _ => unimplemented!(),
        }
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

    pub fn lower<'c>(
        &mut self,
        blockify: &dyn ICodeModule,
        module_block_id: ValueId,
        context: &'c lower_mlir::Context,
        module: &mut Module<'c>,
        b: &mut NodeBuilder,
    ) -> Result<()> {
        let mut lower = lower_mlir::Lower::new(context, module_block_id);
        let mut blocks = lower_mlir::LowerBlocks::new();
        lower.lower_module(blockify, &mut blocks, module, b)?;
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
    use flat::{Flatten, FlattenEnvironment, ICodeModule, ValueId};
    use lower_mlir::Location;
    use test_log::test;

    fn run_test_flatten(filename: &str, expected: i32) {
        let mut p: StarlarkParser = StarlarkParser::new();
        let mut b = flat::NodeBuilder::new();
        let result = p.parse(filename, &mut b, true);
        b.spans.diagnostics_dump();
        let ast = result.unwrap();

        let context = lower_mlir::default_context();
        let mut module = lower_mlir::Module::new(Location::unknown(&context));

        let mut fenv = FlattenEnvironment::new();
        let r = Flatten::flatten_module(ast, &mut fenv, &mut b);
        b.spans.diagnostics_dump();
        let f = r.unwrap();
        b.spans.diagnostics_dump();
        let m = f.module(&mut fenv, &mut b);
        m.dump(&b);

        let r = p.lower(&m, ValueId::new(0), &context, &mut module, &mut b);
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
        run_test_flatten("../tests/test_recursive.star", 0);
    }

    #[test]
    fn test_recursive2() {
        run_test_flatten("../tests/test_recursive2.star", 0);
    }

    #[test]
    fn test_local() {
        run_test_flatten("../tests/test_local.star", 0);
    }

    #[test]
    fn test_goto() {
        run_test_flatten("../tests/goto.star", 0);
    }

    #[test]
    fn test_bare() {
        run_test_flatten("../tests/bare.star", 0);
    }

    #[test]
    fn test_fix() {
        run_test_flatten("../tests/fix.star", 0);
    }

    #[test]
    fn test_nothing() {
        run_test_flatten("../tests/test.star", 0);
    }

    #[test]
    fn test_global() {
        run_test_flatten("../tests/test_global.star", 0);
    }

    #[test]
    fn test_static() {
        run_test_flatten("../tests/test_static.star", 0);
    }

    #[test]
    fn test_float() {
        run_test_flatten("../tests/test_float.star", 0);
    }

    #[test]
    fn test_cond() {
        run_test_flatten("../tests/test_cond.star", 0);
    }

    #[test]
    fn test_ternary() {
        run_test_flatten("../tests/test_ternary.star", 0);
    }

    #[test]
    fn test_loop() {
        run_test_flatten("../tests/loop.star", 0);
    }

    #[test]
    fn test_nested_loops() {
        run_test_flatten("../tests/nested_loops.star", 0);
    }

    #[test]
    fn test_nested_func() {
        run_test_flatten("../tests/nested_func.star", 0);
    }

    #[test]
    fn test_static_var() {
        run_test_flatten("../tests/static_var.star", 0);
    }
}
