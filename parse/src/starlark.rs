use anyhow::Result;
use std::path::Path;

use melior::Context;

use starlark_syntax::codemap;
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

pub type Environment = lower::env::EnvLayers<String, usize>;

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

fn from_parameter<E: Extra, P: syntax::ast::AstPayload>(
    item: syntax::ast::AstParameterP<P>,
    codemap: &CodeMap,
    file_id: usize,
) -> ParameterNode<E> {
    use syntax::ast::ParameterP;
    let r = codemap.resolve_span(item.span);
    let begin = CodeLocation {
        line: r.begin.line,
        col: r.begin.column,
    };
    let end = CodeLocation {
        line: r.end.line,
        col: r.end.column,
    };

    //println!("param: {:?}", &item);
    match item.node {
        ParameterP::Normal(ident, maybe_type) => {
            let ty = if let Some(_ty) = maybe_type {
                //let node = &ty.node.expr.node;
                //println!("tyx: {:?}", &ty);
                //println!("tyx: {:?}", &ty);
                AstType::Int
            } else {
                AstType::Int
            };
            ParameterNode {
                node: Parameter::Normal(ident.node.ident, ty),
                extra: E::new(file_id, begin, end),
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

pub fn extra<E: Extra>(file_id: usize, codemap: &codemap::CodeMap, span: codemap::Span) -> E {
    let r = codemap.resolve_span(span);
    let begin = CodeLocation {
        line: r.begin.line,
        col: r.begin.column,
    };
    let end = CodeLocation {
        line: r.end.line,
        col: r.end.column,
    };

    E::new(file_id, begin, end)
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

    pub fn parse<'a, E: Extra>(
        &mut self,
        context: &'a Context,
        path: &Path,
        files: &mut FileDB,
    ) -> Result<AstNode<E>> {
        let file_id = files.add(
            path.to_str().unwrap().to_string(),
            std::fs::read_to_string(path)?,
        );

        let env = Environment::default();
        let dialect = syntax::Dialect::Extended;
        let m = syntax::AstModule::parse_file(&path, &dialect)?;
        let (codemap, stmt, _dialect, _typecheck) = m.into_parts();
        println!("m: {:?}", &stmt);
        let mut seq = lower::lower::prelude(file_id);
        let ast: AstNode<E> = self.from_stmt(stmt, context, &codemap, file_id, env)?;
        seq.push(ast);
        Ok(lower::lower::node(file_id, Ast::Sequence(seq)))
    }

    pub fn from_stmt<E: Extra, P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstStmtP<P>,
        context: &Context,
        codemap: &CodeMap,
        file_id: usize,
        mut env: Environment,
    ) -> Result<AstNode<E>> {
        use syntax::ast::StmtP;
        let extra = extra(file_id, codemap, item.span);

        match item.node {
            StmtP::Statements(stmts) => {
                let mut exprs = vec![];
                for stmt in stmts {
                    exprs.push(self.from_stmt(stmt, context, codemap, file_id, env.clone())?);
                }

                let ast = Ast::Sequence(exprs);
                Ok(AstNode { node: ast, extra })
            }

            StmtP::Def(def) => {
                let params = def
                    .params
                    .into_iter()
                    .map(|p| from_parameter(p, codemap, file_id))
                    .collect();
                let d = Definition {
                    name: def.name.ident.clone(),
                    body: Some(Box::new(
                        self.from_stmt(*def.body, context, codemap, file_id, env)?,
                    )),
                    params,
                };
                let ast = Ast::Definition(d);
                Ok(AstNode { node: ast, extra })
            }

            StmtP::If(expr, truestmt) => {
                let condition = self.from_expr(expr, context, codemap, file_id, env.clone())?;
                let truestmt = self.from_stmt(*truestmt, context, codemap, file_id, env)?;
                Ok(AstNode {
                    node: Ast::Conditional(condition.into(), truestmt.into(), None),
                    extra,
                })
            }

            StmtP::IfElse(expr, options) => {
                let condition = self.from_expr(expr, context, codemap, file_id, env.clone())?;
                let truestmt = self.from_stmt(options.0, context, codemap, file_id, env.clone())?;
                let elsestmt = Some(Box::new(
                    self.from_stmt(options.1, context, codemap, file_id, env)?,
                ));
                Ok(AstNode {
                    node: Ast::Conditional(condition.into(), truestmt.into(), elsestmt),
                    extra,
                })
            }

            StmtP::Return(maybe_expr) => {
                let node = match maybe_expr {
                    Some(expr) => Ast::Return(Some(Box::new(
                        self.from_expr(expr, context, codemap, file_id, env)?,
                    ))),
                    None => Ast::Return(None),
                };
                Ok(AstNode { node, extra })
            }

            StmtP::Assign(assign) => {
                use syntax::ast::AssignTargetP;
                let rhs = self.from_expr(assign.rhs, context, codemap, file_id, env.clone())?;
                match assign.lhs.node {
                    AssignTargetP::Identifier(ident) => {
                        let name = ident.node.ident;
                        let exists = env.resolve(&name).is_some();
                        if exists {
                            env.define(name.clone(), 0);
                            let target = AssignTarget::Identifier(name);
                            Ok(AstNode {
                                node: Ast::Assign(target, Box::new(rhs)),
                                extra,
                            })
                        } else {
                            Ok(AstNode {
                                node: Ast::Variable(Definition {
                                    name,
                                    params: vec![],
                                    body: Some(Box::new(rhs)),
                                }),
                                extra,
                            })
                        }
                    }
                    _ => unimplemented!(),
                }
                //let target: AssignTarget = from_assign_target(assign.lhs.node);
                //Ok(AstNode {
                //node: Ast::Assign(target, Box::new(rhs)),
                //extra,
                //})
            }

            StmtP::Expression(expr) => self.from_expr(expr, context, codemap, file_id, env),

            _ => unimplemented!("{:?}", item),
        }
    }

    fn from_expr<E: Extra, P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstExprP<P>,
        context: &Context,
        codemap: &CodeMap,
        file_id: usize,
        env: Environment,
    ) -> Result<AstNode<E>> {
        use syntax::ast::ExprP;
        let extra = extra(file_id, codemap, item.span);

        match item.node {
            ExprP::Op(lhs, op, rhs) => {
                let ast = Ast::BinaryOp(
                    from_binop(op),
                    Box::new(self.from_expr(*lhs, context, codemap, file_id, env.clone())?),
                    Box::new(self.from_expr(*rhs, context, codemap, file_id, env)?),
                );
                Ok(AstNode { node: ast, extra })
            }
            ExprP::Call(expr, expr_args) => {
                let mut args = vec![];
                for arg in expr_args {
                    args.push(self.from_argument(arg, context, codemap, file_id, env.clone())?);
                }
                let f = self.from_expr(*expr, context, codemap, file_id, env)?;
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
                let name = ident.node.ident;
                Ok(AstNode {
                    node: Ast::Identifier(name),
                    extra,
                })
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
        context: &Context,
        codemap: &CodeMap,
        file_id: usize,
        env: Environment,
    ) -> Result<Argument<E>> {
        use syntax::ast::ArgumentP;
        match item.node {
            ArgumentP::Positional(expr) => Ok(Argument::Positional(Box::new(
                self.from_expr(expr, context, codemap, file_id, env)?,
            ))),
            _ => unimplemented!(),
        }
    }
}
