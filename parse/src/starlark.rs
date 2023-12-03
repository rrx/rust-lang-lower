use anyhow::Result;
use std::path::Path;
use thiserror::Error;

use starlark_syntax::codemap::CodeMap;
use starlark_syntax::lexer;
use starlark_syntax::syntax;
use starlark_syntax::syntax::module::AstModuleFields;

use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};

use lower::ast::Extra;
use lower::ast::*;
use lower::lower::FileDB;
use std::collections::HashMap;

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("Invalid")]
    Invalid,
}

#[derive(Debug)]
pub struct Layer {
    names: HashMap<String, usize>,
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

    pub fn extra<E: Extra>(&self, span: starlark_syntax::codemap::Span) -> E {
        let r = self.codemap.resolve_span(span);
        let begin = CodeLocation {
            line: r.begin.line,
            col: r.begin.column,
        };
        let end = CodeLocation {
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
    pub fn define(&mut self, name: &str, v: usize) {
        self.layers
            .last_mut()
            .unwrap()
            .names
            .insert(name.to_string(), v);
    }
    pub fn resolve(&self, name: &str) -> Option<usize> {
        for layer in self.layers.iter().rev() {
            return layer.names.get(name).cloned();
        }
        None
    }
    pub fn dump(&self) {
        println!("{:?}", self);
    }
}

fn from_literal(item: syntax::ast::AstLiteral) -> Literal {
    use syntax::ast::AstLiteral;
    match item {
        AstLiteral::Int(x) => {
            use lexer::TokenInt;
            match x.node {
                TokenInt::I32(y) => Literal::Int(y as i64),
                _ => unimplemented!(),
            }
        }
        AstLiteral::Float(x) => Literal::Float(x.node),
        _ => unimplemented!(),
    }
}

fn from_binop(item: syntax::ast::BinOp) -> BinaryOperation {
    use syntax::ast::BinOp;
    match item {
        BinOp::Add => BinaryOperation::Add,
        BinOp::Subtract => BinaryOperation::Subtract,
        BinOp::Equal => BinaryOperation::Equal,
        _ => unimplemented!(),
    }
}

fn from_parameter<'a, E: Extra, P: syntax::ast::AstPayload>(
    item: syntax::ast::AstParameterP<P>,
    env: &Environment<'a>,
) -> ParameterNode<E> {
    use syntax::ast::ParameterP;
    let extra = env.extra(item.span);

    match item.node {
        ParameterP::Normal(ident, maybe_type) => {
            let ty = if let Some(_ty) = maybe_type {
                AstType::Int
            } else {
                AstType::Int
            };
            ParameterNode {
                node: Parameter::Normal(ident.node.ident, ty),
                extra,
            }
        }
        _ => unimplemented!(),
    }
}

fn from_assign_target<P: syntax::ast::AstPayload>(
    item: syntax::ast::AssignTargetP<P>,
) -> AssignTarget {
    use syntax::ast::AssignTargetP;
    match item {
        AssignTargetP::Identifier(ident) => AssignTarget::Identifier(ident.node.ident),
        _ => unimplemented!(),
    }
}

pub struct Parser {
    diagnostics: Vec<Diagnostic<usize>>,
}

impl Parser {
    pub fn new() -> Self {
        Self {
            diagnostics: vec![],
        }
    }

    pub fn dump(&self, files: &FileDB) {
        let writer = StandardStream::stderr(ColorChoice::Always);
        let config = codespan_reporting::term::Config::default();
        for d in self.diagnostics.iter() {
            term::emit(&mut writer.lock(), &config, files, &d).unwrap();
        }
    }

    pub fn parse<'a, E: Extra>(&mut self, path: &Path, files: &mut FileDB) -> Result<AstNode<E>> {
        let file_id = files.add(
            path.to_str().unwrap().to_string(),
            std::fs::read_to_string(path)?,
        );

        let dialect = syntax::Dialect::Extended;
        let m = syntax::AstModule::parse_file(&path, &dialect)?;
        let (codemap, stmt, _dialect, _typecheck) = m.into_parts();
        let mut env = Environment::new(&codemap, file_id);
        println!("m: {:?}", &stmt);
        let mut seq = lower::lower::prelude(file_id);
        let ast: AstNode<E> = self.from_stmt(stmt, &mut env)?;
        seq.push(ast);
        Ok(lower::lower::node(file_id, Ast::Sequence(seq)))
    }

    pub fn from_stmt<'a, E: Extra, P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstStmtP<P>,
        env: &mut Environment<'a>,
    ) -> Result<AstNode<E>> {
        use syntax::ast::StmtP;
        let extra = env.extra(item.span);

        match item.node {
            StmtP::Statements(stmts) => {
                let mut exprs = vec![];
                for stmt in stmts {
                    exprs.push(self.from_stmt(stmt, env)?);
                }

                let ast = Ast::Sequence(exprs);
                Ok(AstNode { node: ast, extra })
            }

            StmtP::Def(def) => {
                let params = def
                    .params
                    .into_iter()
                    .map(|p| from_parameter(p, env))
                    .collect();
                env.enter_func();
                let ast = self.from_stmt(*def.body, env)?;
                env.exit_func();
                let name = &def.name.ident;
                let d = Definition {
                    name: name.clone(),
                    body: Some(Box::new(ast)),
                    return_type: AstType::Int.into(),
                    params,
                };
                let ast = Ast::Definition(d);
                env.define(&name, 0);
                Ok(AstNode { node: ast, extra })
            }

            StmtP::If(expr, truestmt) => {
                let condition = self.from_expr(expr, env)?;
                let truestmt = self.from_stmt(*truestmt, env)?;
                Ok(AstNode {
                    node: Ast::Conditional(condition.into(), truestmt.into(), None),
                    extra,
                })
            }

            StmtP::IfElse(expr, options) => {
                let condition = self.from_expr(expr, env)?;
                let truestmt = self.from_stmt(options.0, env)?;
                let elsestmt = Some(Box::new(self.from_stmt(options.1, env)?));
                Ok(AstNode {
                    node: Ast::Conditional(condition.into(), truestmt.into(), elsestmt),
                    extra,
                })
            }

            StmtP::Return(maybe_expr) => {
                let node = match maybe_expr {
                    Some(expr) => Ast::Return(Some(Box::new(self.from_expr(expr, env)?))),
                    None => Ast::Return(None),
                };
                Ok(AstNode { node, extra })
            }

            StmtP::Assign(assign) => {
                use syntax::ast::AssignTargetP;
                let rhs = self.from_expr(assign.rhs, env)?;
                match assign.lhs.node {
                    AssignTargetP::Identifier(ident) => {
                        let name = ident.node.ident;
                        env.define(&name, 0);
                        if env.in_func {
                            let target = AssignTarget::Identifier(name);
                            Ok(AstNode {
                                node: Ast::Assign(target, Box::new(rhs)),
                                extra,
                            })
                        } else {
                            Ok(AstNode {
                                node: Ast::Global(name, Box::new(rhs)),
                                extra,
                            })
                        }
                    }
                    _ => unimplemented!(),
                }
            }

            StmtP::Expression(expr) => self.from_expr(expr, env),

            _ => unimplemented!("{:?}", item),
        }
    }

    fn from_expr<E: Extra, P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstExprP<P>,
        env: &mut Environment,
    ) -> Result<AstNode<E>> {
        use syntax::ast::ExprP;
        let extra = env.extra(item.span);

        match item.node {
            ExprP::Op(lhs, op, rhs) => {
                let ast = Ast::BinaryOp(
                    from_binop(op),
                    Box::new(self.from_expr(*lhs, env)?),
                    Box::new(self.from_expr(*rhs, env)?),
                );
                Ok(AstNode { node: ast, extra })
            }
            ExprP::Call(expr, expr_args) => {
                let mut args = vec![];
                for arg in expr_args {
                    args.push(self.from_argument(arg, env)?);
                }
                let f = self.from_expr(*expr, env)?;
                println!("args: {:?}", args);
                let ast = match &f.node {
                    Ast::Identifier(name) => match name.as_str() {
                        "check" => {
                            assert!(args.len() == 1);
                            let arg = args.pop().unwrap();
                            Ast::Builtin(Builtin::Assert(Box::new(arg)))
                        }
                        "print" => {
                            assert!(args.len() == 1);
                            let arg = args.pop().unwrap();
                            Ast::Builtin(Builtin::Print(Box::new(arg)))
                        }
                        _ => Ast::Call(Box::new(f), args),
                    },
                    _ => Ast::Call(Box::new(f), args),
                };
                Ok(AstNode { node: ast, extra })
            }
            ExprP::Identifier(ident) => {
                if let Some(_index) = env.resolve(&ident.node.ident) {
                    let name = ident.node.ident;
                    Ok(AstNode {
                        node: Ast::Identifier(name),
                        extra,
                    })
                } else {
                    let r = item.span.begin().get() as usize..item.span.end().get() as usize;

                    let diagnostic: Diagnostic<usize> = Diagnostic::error()
                        .with_labels(vec![
                            Label::primary(env.file_id, r).with_message("Variable not in scope")
                        ])
                        .with_message("error");
                    self.diagnostics.push(diagnostic);
                    Err(anyhow::Error::new(ParseError::Invalid))
                }
            }

            ExprP::Literal(lit) => {
                let x: Literal = from_literal(lit);
                Ok(AstNode {
                    node: Ast::Literal(x),
                    extra,
                })
            }

            _ => unimplemented!(),
        }
    }

    fn from_argument<E: Extra, P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstArgumentP<P>,
        env: &mut Environment,
    ) -> Result<Argument<E>> {
        use syntax::ast::ArgumentP;
        match item.node {
            ArgumentP::Positional(expr) => {
                Ok(Argument::Positional(Box::new(self.from_expr(expr, env)?)))
            }
            _ => unimplemented!(),
        }
    }
}
