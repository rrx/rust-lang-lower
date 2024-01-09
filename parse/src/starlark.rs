use std::collections::HashMap;
use std::path::Path;

use anyhow::Error;
use anyhow::Result;
use codespan_reporting::diagnostic::{Diagnostic, Label};

use starlark_syntax::codemap;
use starlark_syntax::codemap::CodeMap;
use starlark_syntax::lexer;
use starlark_syntax::syntax;
use starlark_syntax::syntax::module::AstModuleFields;

use flat::Blockify;
use lower::ast;
use lower::ast::{Ast, AstNode, CodeLocation, Extra};
use lower::{
    AstType, CFGBlocks, Diagnostics, IRPlaceTable, LinkOptions, Module, NodeBuilder, ParseError,
    StringKey, TypeBuilder, TypeUnify,
};

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
}
impl Default for Layer {
    fn default() -> Self {
        Self {
            names: HashMap::new(),
        }
    }
}

#[derive(Debug)]
pub struct Environment<'a> {
    codemap: &'a CodeMap,
    in_func: bool,
    layers: Vec<Layer>,
    file_id: usize,
}

impl<'a> Environment<'a> {
    pub fn new(codemap: &'a CodeMap, file_id: usize) -> Self {
        let start = Layer::default();
        Self {
            codemap,
            in_func: false,
            layers: vec![start],
            file_id,
        }
    }

    pub fn extra<E: Extra>(&self, span: codemap::Span) -> E {
        let begin = CodeLocation {
            pos: span.begin().get(),
        };
        let end = CodeLocation {
            pos: span.end().get(),
        };
        E::new(self.file_id, begin, end)
    }

    pub fn enter_func(&mut self) {
        self.in_func = true;
    }

    pub fn exit_func(&mut self) {
        assert_eq!(self.in_func, true);
        self.in_func = false;
    }

    pub fn define(&mut self, name: StringKey) {
        let data = if self.in_func {
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

fn from_literal<E: Extra>(
    item: syntax::ast::AstLiteral,
    span: codemap::Span,
    env: &Environment,
    b: &mut NodeBuilder<E>,
) -> ast::AstNode<E> {
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
    let extra = env.extra(span);
    b.build(Ast::Literal(lit), extra)
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
    //log::debug!("type: {:?}", item);
    match &item.expr.node {
        syntax::ast::ExprP::Identifier(name) => match name.ident.as_str() {
            "float" => Some(AstType::Float),
            "int" => Some(AstType::Int),
            _ => None,
        },
        _ => None,
    }
}

fn from_assign_target<E: Extra, P: syntax::ast::AstPayload>(
    item: syntax::ast::AssignTargetP<P>,
    b: &mut NodeBuilder<E>,
) -> ast::AssignTarget {
    use syntax::ast::AssignTargetP;
    match item {
        AssignTargetP::Identifier(ident) => {
            ast::AssignTarget::Identifier(b.s(&ident.node.ident).into())
        }
        _ => unimplemented!(),
    }
}

pub struct Parser<E> {
    u: TypeUnify,
    _e: std::marker::PhantomData<E>,
}

impl<E: Extra> Parser<E> {
    pub fn new() -> Self {
        Self {
            u: TypeUnify::new(),
            _e: std::marker::PhantomData::default(),
        }
    }

    pub fn parse<'a>(
        &mut self,
        path: &Path,
        content: Option<&str>,
        module_key: StringKey,
        file_id: usize,
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) -> Result<ast::AstNode<E>> {
        b.enter(file_id, path.to_str().unwrap());
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
        let ast: ast::AstNode<E> = self.from_stmt(stmt, &mut env, d, b)?;
        let extra = ast.extra.clone();
        seq.push(ast);
        Ok(b.module(module_key.into(), b.seq(seq).set_extra(extra)))
    }

    fn from_parameter<'a, P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstParameterP<P>,
        env: &mut Environment<'a>,
        _d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) -> ast::ParameterNode<E> {
        use syntax::ast::ParameterP;

        //log::debug!("p: {:?}", item);
        match item.node {
            ParameterP::Normal(ident, maybe_type) => {
                let extra = env.extra(item.span);
                let ty = if let Some(ty) = maybe_type.map(|ty| from_type(&ty)) {
                    ty
                } else {
                    Some(self.u.fresh_unknown())
                    //d.push_diagnostic(env.error(item.span, "Missing Type"));
                    //Some(AstType::Unit)
                };
                ast::ParameterNode {
                    name: b.s(&ident.node.ident),
                    ty: ty.unwrap(),
                    node: ast::Parameter::Normal,
                    extra,
                }
            }
            /*

            ParameterP::WithDefaultValue(ident, maybe_type, expr) => {
                let extra = env.extra(item.span);
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
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) -> Result<ast::AstNode<E>> {
        use syntax::ast::StmtP;

        match item.node {
            StmtP::Statements(stmts) => {
                let mut exprs = vec![];
                for stmt in stmts {
                    exprs.push(self.from_stmt(stmt, env, d, b)?);
                }

                let extra = env.extra(item.span);
                Ok(b.seq(exprs).set_extra(extra))
            }

            StmtP::Def(def) => {
                let name = b.s(&def.name.ident);
                env.enter_func();

                // push function name into scope
                env.define(name);

                let params = def
                    .params
                    .into_iter()
                    .map(|p| self.from_parameter(p, env, d, b))
                    .collect::<Vec<_>>();

                // push name to environment
                for p in params.iter() {
                    env.define(p.name);
                }

                //let mut body = vec![b.label(name, params.clone())];
                let mut body = vec![];
                body.extend(self.from_stmt(*def.body, env, d, b)?.to_vec());

                env.exit_func();
                let return_type = def
                    .return_type
                    .map(|ty| from_type(&ty).unwrap_or(AstType::Unit))
                    .unwrap_or(AstType::Unit)
                    .into();

                let def_ast = Ast::Definition(ast::Definition {
                    name,
                    body: Some(b.seq(body).into()),
                    return_type,
                    params,
                });

                env.define(name);
                let extra = env.extra(item.span);
                Ok(b.build(def_ast, extra))
            }

            StmtP::If(expr, truestmt) => {
                let condition = self.from_expr(expr, env, d, b)?;
                let truestmt = self.from_stmt(*truestmt, env, d, b)?;
                let extra = env.extra(item.span);
                Ok(b.build(
                    Ast::Conditional(condition.into(), truestmt.into(), None),
                    extra,
                ))
            }

            StmtP::IfElse(expr, options) => {
                let condition = self.from_expr(expr, env, d, b)?;
                let truestmt = self.from_stmt(options.0, env, d, b)?;
                let elsestmt = self.from_stmt(options.1, env, d, b)?;
                let extra = env.extra(item.span);
                Ok(b.build(
                    Ast::Conditional(condition.into(), truestmt.into(), Some(elsestmt.into())),
                    extra,
                ))
            }

            StmtP::Return(maybe_expr) => {
                let extra = env.extra(item.span);
                Ok(match maybe_expr {
                    Some(expr) => {
                        let node = self.from_expr(expr, env, d, b)?;
                        b.ret(Some(node)).set_extra(extra)
                    }
                    None => b.ret(None),
                })
            }

            StmtP::Assign(assign) => {
                use syntax::ast::AssignTargetP;
                let rhs = self.from_expr(assign.rhs, env, d, b)?;
                match assign.lhs.node {
                    AssignTargetP::Identifier(ident) => {
                        //log::debug!("parse ident: {}", ident.node.ident);
                        let name = &ident.node.ident;
                        if let Some(node) = b.build_literal_from_identifier(name) {
                            return Ok(node);
                        }

                        let name = b.s(&ident.node.ident);

                        // lookup
                        if let Some(_data) = env.resolve(name) {
                            Ok(b.assign(name.into(), rhs))
                        } else {
                            // name does not exist in scope
                            // Either create a global or do local, depending on context
                            env.define(name);
                            if env.in_func {
                                Ok(b.assign(name.into(), rhs))
                            } else {
                                Ok(b.global(name, rhs))
                            }
                        }
                    }
                    _ => unimplemented!(),
                }
            }

            StmtP::Expression(expr) => self.from_expr(expr, env, d, b),

            _ => unimplemented!("{:?}", item),
        }
    }

    fn from_expr<P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstExprP<P>,
        env: &mut Environment,
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) -> Result<AstNode<E>> {
        use syntax::ast::ExprP;

        match item.node {
            ExprP::Op(lhs, op, rhs) => {
                let node_a = self.from_expr(*lhs, env, d, b)?.into();
                let node_b = self.from_expr(*rhs, env, d, b)?.into();
                Ok(b.binop(from_binop(op), node_a, node_b))
            }

            ExprP::If(args) => {
                let (condition, then_expr, else_expr) = *args;
                let condition = self.from_expr(condition, env, d, b)?;
                let then_expr = self.from_expr(then_expr, env, d, b)?;
                let else_expr = self.from_expr(else_expr, env, d, b)?;
                let extra = env.extra(item.span);
                Ok(b.build(
                    Ast::Ternary(condition.into(), then_expr.into(), else_expr.into()),
                    extra,
                ))
            }

            ExprP::Call(expr, expr_args) => {
                let mut args = vec![];
                for arg in expr_args {
                    args.push(self.from_argument(arg, env, d, b)?.into());
                }

                match expr.node {
                    ExprP::Identifier(ident) => {
                        let name = b.s(&ident.node.ident);
                        if let Some(_data) = env.resolve(name) {
                            let extra: E = env.extra(item.span);
                            Ok(b.apply(name.into(), args, AstType::Int).set_extra(extra))
                        } else if let Some(bi) = ast::Builtin::from_name(&ident.node.ident) {
                            let extra = env.extra(item.span);
                            assert_eq!(args.len(), bi.arity());
                            Ok(b.build(Ast::Builtin(bi, args), extra))
                        } else {
                            d.push_diagnostic(env.error(ident.span, "Not found"));
                            Ok(b.error())
                        }
                    }

                    ExprP::Dot(expr, name) => {
                        if let ExprP::Identifier(ident) = &expr.node {
                            let key = b.s(&ident.node.ident);
                            if let Some(_data) = env.resolve(key) {
                                let extra: E = env.extra(item.span);
                                Ok(b.apply(key.into(), args, AstType::Int).set_extra(extra))
                            } else if &ident.node.ident == "b" {
                                // builtin namespace
                                if let Some(mut ast) = b.build_builtin_from_name(&name, args) {
                                    let extra = env.extra(item.span);
                                    ast.extra = extra;
                                    Ok(ast)
                                } else {
                                    d.push_diagnostic(env.error(name.span, "Builtin not found"));
                                    Ok(b.error())
                                }
                            } else {
                                d.push_diagnostic(env.error(
                                    name.span,
                                    &format!("Variable not in scope: {}", ident.node.ident),
                                ));
                                Ok(b.error())
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
                if let Some(_data) = env.resolve(name) {
                    let extra = env.extra(item.span);
                    let ast = b.ident(name.into()).set_extra(extra);
                    Ok(ast)
                } else {
                    d.push_diagnostic(env.error(
                        ident.span,
                        &format!("Variable not in scope: {}", ident.node.ident),
                    ));
                    Ok(b.error())
                }
            }

            ExprP::Literal(lit) => Ok(from_literal(lit, item.span, env, b)),

            ExprP::Minus(expr) => {
                let extra = env.extra(item.span);
                let ast = Ast::UnaryOp(
                    ast::UnaryOperation::Minus,
                    self.from_expr(*expr, env, d, b)?.into(),
                );
                Ok(b.build(ast, extra))
            }

            _ => unimplemented!("{:?}", item.node),
        }
    }

    fn from_argument<P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstArgumentP<P>,
        env: &mut Environment,
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) -> Result<ast::Argument<E>> {
        use syntax::ast::ArgumentP;
        match item.node {
            ArgumentP::Positional(expr) => Ok(self.from_expr(expr, env, d, b)?.into()),
            _ => unimplemented!(),
        }
    }
}

#[derive(Default)]
pub struct StarlarkParser<E> {
    _e: std::marker::PhantomData<E>,
    link: LinkOptions,
    place: IRPlaceTable,
}

impl<E: Extra> StarlarkParser<E> {
    pub fn new() -> Self {
        Self {
            _e: std::marker::PhantomData::default(),
            link: LinkOptions::new(),
            place: IRPlaceTable::new(),
        }
    }

    pub fn parse_module2<'c>(
        &mut self,
        filename: &str,
        context: &'c lower::Context,
        module: &mut Module<'c>,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
        verbose: bool,
    ) -> Result<()> {
        log::debug!("parsing: {}", filename);
        use lower::IREnvironment;

        let file_id = d.add_source(filename.to_string(), std::fs::read_to_string(filename)?);

        b.enter(file_id, &filename);

        let mut parser = Parser::new();
        let module_key = b.s("module");
        let ast: AstNode<E> = parser
            .parse(Path::new(filename), None, module_key, file_id, d, b)?
            .normalize(d, b);

        let mut env = IREnvironment::new();
        let mut blockify = Blockify::new();
        blockify.add(ast, &mut env, b, d)?;
        blockify.build(&mut env, b, d)?;
        //ast.blockify(&mut self.place, &mut env, b, d)?;
        blockify.dump(&self.place, b);
        Ok(())
    }

    pub fn parse_module<'c>(
        &mut self,
        filename: &str,
        context: &'c lower::Context,
        module: &mut Module<'c>,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
        verbose: bool,
    ) -> Result<()> {
        log::debug!("parsing: {}", filename);
        use lower::IREnvironment;

        let file_id = d.add_source(filename.to_string(), std::fs::read_to_string(filename)?);

        b.enter(file_id, &filename);

        let mut parser = Parser::new();
        let module_key = b.s("module");
        let ast: AstNode<E> = parser
            .parse(Path::new(filename), None, module_key, file_id, d, b)?
            .normalize(d, b);

        ast.dump(b, 0);
        let ast = ast.first_pass(b, d)?;
        ast.dump(b, 0);

        let mut env = IREnvironment::new();

        // lower ast to ir
        let r = ast.lower_ir_module(&mut env, &mut self.place, d, b);
        d.dump();

        if d.has_errors {
            return Err(Error::new(ParseError::Invalid));
        }

        let (ir, _ty, root) = r?;

        // Analyze
        if verbose {
            ir.dump(&self.place, &b, 0);
            env.blocks.save_graph("lower.dot", b);
        }

        assert_eq!(0, env.stack_size());

        let r = ir.build_graph(&mut self.place, &mut env, d, b);
        d.dump();
        let ir = r?;

        if verbose {
            env.blocks.save_graph("build.dot", b);
        }

        // lower to mlir
        let mut types = TypeBuilder::new();
        let mut blocks = CFGBlocks::new(root, env.blocks.g);
        blocks.update_block_ir(context, root, b.s("module").into(), &[], &mut types, d);

        let mut stack = vec![blocks.root()];
        let r = ir.lower_mlir(
            context,
            &mut self.place,
            d,
            &mut types,
            &mut blocks,
            &mut stack,
            b,
            &mut self.link,
        );
        d.dump();
        r?;

        let data = blocks.get_mut(&blocks.root()).unwrap();
        for op in data.take_ops() {
            module.body().append_operation(op);
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

        use lower::compile::exec_main;
        exec_main(&self.link.shared_libraries(), module, libpath)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use lower::ast::SimpleExtra;
    use lower::Location;
    use test_log::test;

    fn run_test_ir2(filename: &str, expected: i32) {
        let mut p: StarlarkParser<SimpleExtra> = StarlarkParser::new();
        let mut b = NodeBuilder::new();
        let context = lower::default_context();
        let mut d = Diagnostics::new();
        let mut module = Module::new(Location::unknown(&context));
        let r = p.parse_module2(filename, &context, &mut module, &mut b, &mut d, true);
        r.unwrap();
    }

    fn run_test_ir(filename: &str, expected: i32) {
        let mut p: StarlarkParser<SimpleExtra> = StarlarkParser::new();
        let mut b = NodeBuilder::new();
        let context = lower::default_context();
        let mut d = Diagnostics::new();
        let mut module = Module::new(Location::unknown(&context));
        let r = p.parse_module(filename, &context, &mut module, &mut b, &mut d, true);
        r.unwrap();
        module.as_operation().dump();
        assert!(module.as_operation().verify());
        let r = p.exec_main(&context, &mut module, "../target/debug/", true);
        assert_eq!(expected, r);
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
    fn test_cond() {
        run_test_ir("../tests/test_cond.star", 0);
    }

    #[test]
    fn test_float() {
        run_test_ir("../tests/test_float.star", 0);
    }

    #[test]
    fn test_recursive() {
        run_test_ir("../tests/test_recursive.star", 0);
    }

    #[test]
    fn test_nothing() {
        run_test_ir("../tests/test.star", 0);
    }

    #[test]
    fn test_goto() {
        //run_test_ir2("../tests/goto.star", 0);
        run_test_ir("../tests/goto.star", 0);
    }
}
