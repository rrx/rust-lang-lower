use anyhow::Result;
use std::path::Path;
use thiserror::Error;

use starlark_syntax::codemap;
use starlark_syntax::codemap::CodeMap;

use starlark_syntax::lexer;
use starlark_syntax::syntax;
use starlark_syntax::syntax::module::AstModuleFields;

use codespan_reporting::diagnostic::{Diagnostic, Label};

use lower::ast;
use lower::ast::{Ast, AstNode, AstType, CodeLocation, DerefTarget, Extra};
use lower::{Diagnostics, NodeBuilder};
use std::collections::HashMap;

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("Invalid")]
    Invalid,
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
    names: HashMap<String, Data>,
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
        let r = self.codemap.resolve_span(span);
        let begin = CodeLocation {
            pos: span.begin().get(),
            line: r.begin.line,
            col: r.begin.column,
        };
        let end = CodeLocation {
            pos: span.end().get(),
            line: r.end.line,
            col: r.end.column,
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

    pub fn define(&mut self, name: &str) {
        let data = if self.in_func {
            Data::new_local()
        } else {
            Data::new_global()
        };
        self.layers
            .last_mut()
            .unwrap()
            .names
            .insert(name.to_string(), data);
    }

    pub fn resolve(&self, name: &str) -> Option<Data> {
        for layer in self.layers.iter().rev() {
            return layer.names.get(name).cloned();
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
    AstNode {
        node: Ast::Literal(lit),
        extra,
    }
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
    log::debug!("type: {:?}", item);
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
) -> ast::AssignTarget {
    use syntax::ast::AssignTargetP;
    match item {
        AssignTargetP::Identifier(ident) => ast::AssignTarget::Identifier(ident.node.ident),
        _ => unimplemented!(),
    }
}

pub struct Parser<E> {
    _e: std::marker::PhantomData<E>,
}

impl<E: Extra> Parser<E> {
    pub fn new() -> Self {
        Self {
            _e: std::marker::PhantomData::default(),
        }
    }

    pub fn parse<'a>(
        &mut self,
        path: &Path,
        content: Option<&str>,
        file_id: usize,
        d: &mut Diagnostics,
    ) -> Result<ast::AstNode<E>> {
        let b = lower::NodeBuilder::new(file_id, path.to_str().unwrap());
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
        let ast: ast::AstNode<E> = self.from_stmt(stmt, &mut env, d, &b)?;
        let extra = ast.extra.clone();
        seq.push(ast);
        Ok(b.seq(seq).set_extra(extra))
    }

    fn from_parameter<'a, P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstParameterP<P>,
        env: &mut Environment<'a>,
        d: &mut Diagnostics,
        b: &NodeBuilder<E>,
    ) -> ast::ParameterNode<E> {
        use syntax::ast::ParameterP;

        log::debug!("p: {:?}", item);
        match item.node {
            ParameterP::Normal(ident, maybe_type) => {
                let extra = env.extra(item.span);
                let ty = if let Some(ty) = maybe_type.map(|ty| from_type(&ty)) {
                    ty
                } else {
                    d.push_diagnostic(env.error(item.span, "Missing Type"));
                    Some(ast::AstType::Unit)
                };
                ast::ParameterNode {
                    name: ident.node.ident.to_string(),
                    ty: ty.unwrap(),
                    node: ast::Parameter::Normal,
                    extra,
                }
            }
            ParameterP::WithDefaultValue(ident, maybe_type, expr) => {
                let extra = env.extra(item.span);
                let ty = if let Some(ty) = maybe_type.map(|ty| from_type(&ty)) {
                    ty
                } else {
                    d.push_diagnostic(env.error(item.span, "Missing Type"));
                    Some(ast::AstType::Unit)
                };
                let expr = self.from_expr(*expr, env, d, b).unwrap();
                ast::ParameterNode {
                    name: ident.node.ident.to_string(),
                    ty: ty.unwrap(),
                    node: ast::Parameter::WithDefault(expr.into()),
                    extra,
                }
            }
            _ => unimplemented!(),
        }
    }

    pub fn from_stmt<'a, P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstStmtP<P>,
        env: &mut Environment<'a>,
        d: &mut Diagnostics,
        b: &NodeBuilder<E>,
    ) -> Result<ast::AstNode<E>> {
        use syntax::ast::StmtP;

        match item.node {
            StmtP::Statements(stmts) => {
                let mut exprs = vec![];
                for stmt in stmts {
                    exprs.push(self.from_stmt(stmt, env, d, b)?);
                }

                let extra = env.extra(item.span);
                let ast = Ast::Sequence(exprs);
                Ok(AstNode { node: ast, extra })
            }

            StmtP::Def(def) => {
                let name = &def.name.ident;
                env.enter_func();

                // push function name into scope
                env.define(&name);

                let params = def
                    .params
                    .into_iter()
                    .map(|p| self.from_parameter(p, env, d, b))
                    .collect::<Vec<_>>();

                // push name to environment
                for p in params.iter() {
                    env.define(&p.name);
                }

                let body = self.from_stmt(*def.body, env, d, b)?;
                env.exit_func();
                let return_type = def
                    .return_type
                    .map(|ty| from_type(&ty).unwrap_or(AstType::Unit))
                    .unwrap_or(AstType::Unit)
                    .into();
                let d = ast::Definition {
                    name: name.clone(),
                    body: Some(body.into()),
                    return_type,
                    params,
                };
                let ast = Ast::Definition(d);
                env.define(&name);
                let extra = env.extra(item.span);
                Ok(AstNode::new(ast, extra))
            }

            StmtP::If(expr, truestmt) => {
                let condition = self.from_expr(expr, env, d, b)?;
                let truestmt = self.from_stmt(*truestmt, env, d, b)?;
                let extra = env.extra(item.span);
                Ok(AstNode::new(
                    Ast::Conditional(condition.into(), truestmt.into(), None),
                    extra,
                ))
            }

            StmtP::IfElse(expr, options) => {
                let condition = self.from_expr(expr, env, d, b)?;
                let truestmt = self.from_stmt(options.0, env, d, b)?;
                let elsestmt = self.from_stmt(options.1, env, d, b)?;
                let extra = env.extra(item.span);
                Ok(AstNode::new(
                    Ast::Conditional(condition.into(), truestmt.into(), Some(elsestmt.into())),
                    extra,
                ))
            }

            StmtP::Return(maybe_expr) => {
                let extra = env.extra(item.span);
                Ok(match maybe_expr {
                    Some(expr) => b
                        .ret(Some(self.from_expr(expr, env, d, b)?))
                        .set_extra(extra),
                    None => b.ret(None),
                })
            }

            StmtP::Assign(assign) => {
                use syntax::ast::AssignTargetP;
                let rhs = self.from_expr(assign.rhs, env, d, b)?;
                match assign.lhs.node {
                    AssignTargetP::Identifier(ident) => {
                        let name = ident.node.ident;
                        env.define(&name);
                        if env.in_func {
                            Ok(b.assign(&name, rhs))
                        } else {
                            Ok(b.global(&name, rhs))
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
        b: &NodeBuilder<E>,
    ) -> Result<AstNode<E>> {
        use syntax::ast::ExprP;

        match item.node {
            ExprP::Op(lhs, op, rhs) => {
                let extra = env.extra(item.span);
                let ast = Ast::BinaryOp(
                    from_binop(op),
                    Box::new(self.from_expr(*lhs, env, d, b)?),
                    Box::new(self.from_expr(*rhs, env, d, b)?),
                );
                Ok(AstNode { node: ast, extra })
            }

            ExprP::Call(expr, expr_args) => {
                let mut args = vec![];
                for arg in expr_args {
                    args.push(self.from_argument(arg, env, d, b)?.into());
                }

                match expr.node {
                    ExprP::Identifier(ident) => {
                        if let Some(_data) = env.resolve(&ident.node.ident) {
                            let extra: E = env.extra(item.span);
                            Ok(b.apply(&ident.node.ident, args, AstType::Int)
                                .set_extra(extra))
                        } else if let Some(b) = ast::Builtin::from_name(&ident.node.ident) {
                            let extra = env.extra(item.span);
                            assert_eq!(args.len(), b.arity());
                            Ok(AstNode::new(Ast::Builtin(b, args), extra))
                        } else {
                            d.push_diagnostic(env.error(ident.span, "Not found"));
                            Ok(b.error())
                        }
                    }

                    ExprP::Dot(expr, name) => {
                        if let ExprP::Identifier(ident) = &expr.node {
                            if let Some(_data) = env.resolve(&ident.node.ident) {
                                let extra: E = env.extra(item.span);
                                Ok(b.apply(&ident.node.ident, args, AstType::Int)
                                    .set_extra(extra))
                            } else if &ident.node.ident == "b" {
                                // builtin namespace
                                if let Some(b) = ast::Builtin::from_name(&name.node) {
                                    assert_eq!(args.len(), b.arity());
                                    let extra = env.extra(item.span);
                                    Ok(AstNode::new(Ast::Builtin(b, args), extra))
                                } else {
                                    d.push_diagnostic(env.error(name.span, "Builtin not found"));
                                    Ok(b.error())
                                }
                            } else {
                                d.push_diagnostic(env.error(name.span, "Variable not in scope"));
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
                if let Some(data) = env.resolve(&ident.node.ident) {
                    let name = ident.node.ident;
                    let extra = env.extra(item.span);
                    let ast = AstNode {
                        node: Ast::Identifier(name),
                        extra,
                    };

                    // Global identifiers are dereferenced when accessed
                    if let DataType::Global = data.ty {
                        let extra = env.extra(item.span);
                        Ok(AstNode {
                            node: Ast::Deref(ast.into(), DerefTarget::Offset(0)),
                            extra,
                        })
                    } else {
                        Ok(ast)
                    }
                } else {
                    d.push_diagnostic(env.error(ident.span, "Variable not in scope"));
                    Ok(b.error())
                }
            }

            ExprP::Literal(lit) => Ok(from_literal(lit, item.span, env)),

            ExprP::Minus(expr) => {
                let extra = env.extra(item.span);
                let ast = Ast::UnaryOp(
                    ast::UnaryOperation::Minus,
                    self.from_expr(*expr, env, d, b)?.into(),
                );
                Ok(AstNode { node: ast, extra })
            }

            _ => unimplemented!("{:?}", item.node),
        }
    }

    fn from_argument<P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstArgumentP<P>,
        env: &mut Environment,
        d: &mut Diagnostics,
        b: &NodeBuilder<E>,
    ) -> Result<ast::Argument<E>> {
        use syntax::ast::ArgumentP;
        match item.node {
            ArgumentP::Positional(expr) => Ok(self.from_expr(expr, env, d, b)?.into()),
            _ => unimplemented!(),
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use test_log::test;

    fn run_test(filename: &str, expected: i32) {
        let context = lower::default_context();
        let mut lower = lower::lower::Lower::new(&context);
        let mut d = Diagnostics::new();
        let file_id = d.add_source(
            filename.to_string(),
            std::fs::read_to_string(filename).unwrap(),
        );
        let b = NodeBuilder::new(file_id, filename);
        // parse
        let mut parser = Parser::new();
        let ast: AstNode<ast::SimpleExtra> = parser
            .parse(Path::new(filename), None, file_id, &mut d)
            .unwrap();

        // lower
        let mut env = lower::lower::Environment::default();
        env.enter_static();

        // run
        assert_eq!(
            expected,
            lower.run_ast(ast, "../target/debug", env, &mut d, &b)
        );
        //env.exit();
    }

    #[test]
    fn test_global() {
        run_test("../tests/test_global.star", 0);
    }

    #[test]
    fn test_assign1() {
        run_test("../tests/test_assign1.star", 0);
    }
}
