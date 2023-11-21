use anyhow::Result;
use std::error::Error;
use std::path::Path;

use melior::{ir::*, Context};

use starlark_syntax::codemap::CodeMap;
use starlark_syntax::lexer;
use starlark_syntax::syntax;
use starlark_syntax::syntax::module::AstModuleFields;

use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};

use crate::ast::Extra;
use crate::ast::*;
use crate::lower::*;

impl From<syntax::ast::AstLiteral> for Literal {
    fn from(item: syntax::ast::AstLiteral) -> Self {
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
}

impl From<syntax::ast::BinOp> for BinaryOperation {
    fn from(item: syntax::ast::BinOp) -> Self {
        use syntax::ast::BinOp;
        match item {
            BinOp::Add => BinaryOperation::Add,
            BinOp::Subtract => BinaryOperation::Subtract,
            BinOp::Equal => BinaryOperation::Equal,
            _ => unimplemented!(),
        }
    }
}

impl<E: Extra> ParameterNode<E> {
    fn from<P: syntax::ast::AstPayload>(
        item: syntax::ast::AstParameterP<P>,
        codemap: &CodeMap,
    ) -> Self {
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

        match item.node {
            ParameterP::Normal(ident, maybe_type) => Self {
                node: Parameter::Normal(ident.node.ident),
                extra: E::new(begin, end),
            },
            _ => unimplemented!(),
        }
    }
}

impl<P: syntax::ast::AstPayload> From<syntax::ast::AssignTargetP<P>> for AssignTarget {
    fn from(item: syntax::ast::AssignTargetP<P>) -> Self {
        use syntax::ast::AssignTargetP;
        match item {
            AssignTargetP::Identifier(ident) => AssignTarget::Identifier(ident.node.ident),
            _ => unimplemented!(),
        }
    }
}

pub struct Parser {
    diagnostics: Vec<Diagnostic<usize>>,
    files: SimpleFiles<String, String>,
}

impl Parser {
    pub fn new() -> Self {
        Self {
            diagnostics: vec![],
            files: SimpleFiles::new(),
        }
    }

    pub fn dump(&self) {
        let writer = StandardStream::stderr(ColorChoice::Always);
        let config = codespan_reporting::term::Config::default();
        for d in self.diagnostics.iter() {
            term::emit(&mut writer.lock(), &config, &self.files, &d).unwrap();
        }
    }

    pub fn parse<'a>(&mut self, context: &'a Context, path: &Path) -> Result<Vec<Operation<'a>>> {
        let path = Path::new("examples/test_simple.py");
        let file_id = self.files.add(
            path.to_str().unwrap().to_string(),
            std::fs::read_to_string(path)?,
        );

        let dialect = syntax::Dialect::Extended;
        let m = syntax::AstModule::parse_file(&path, &dialect)?;
        let (codemap, stmt, _dialect, _typecheck) = m.into_parts();
        println!("m: {:?}", &stmt);
        let mut parser = Parser::new();
        let ast: AstNode<SimpleExtra> = parser.from_stmt(stmt, context, &codemap)?;
        parser.dump();
        Ok(lower_expr(context, &codemap, ast))
    }

    pub fn from_stmt<E: Extra, P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstStmtP<P>,
        context: &Context,
        codemap: &CodeMap,
    ) -> Result<AstNode<E>> {
        use syntax::ast::StmtP;

        let r = codemap.resolve_span(item.span);
        let begin = CodeLocation {
            line: r.begin.line,
            col: r.begin.column,
        };
        let end = CodeLocation {
            line: r.end.line,
            col: r.end.column,
        };

        match item.node {
            StmtP::Statements(stmts) => {
                let mut exprs = vec![];
                for stmt in stmts {
                    exprs.push(self.from_stmt(stmt, context, codemap)?);
                }

                let ast = Ast::Sequence(exprs);
                Ok(AstNode {
                    node: ast,
                    extra: E::new(begin, end),
                })
            }

            StmtP::Def(def) => {
                let params = def
                    .params
                    .into_iter()
                    .map(|p| ParameterNode::from(p, codemap))
                    .collect();
                let d = Definition {
                    name: def.name.ident.clone(),
                    body: Box::new(self.from_stmt(*def.body, context, codemap)?),
                    params,
                };
                let ast = Ast::Definition(d);
                Ok(AstNode {
                    node: ast,
                    extra: E::new(begin, end),
                })
            }

            StmtP::If(expr, truestmt) => {
                let condition = self.from_expr(expr, context, codemap)?;
                let truestmt = self.from_stmt(*truestmt, context, codemap)?;
                Ok(AstNode {
                    node: Ast::Conditional(condition.into(), truestmt.into(), None),
                    extra: E::new(begin, end),
                })
            }

            StmtP::IfElse(expr, options) => {
                let condition = self.from_expr(expr, context, codemap)?;
                let truestmt = self.from_stmt(options.0, context, codemap)?;
                let elsestmt = Some(Box::new(self.from_stmt(options.1, context, codemap)?));
                Ok(AstNode {
                    node: Ast::Conditional(condition.into(), truestmt.into(), elsestmt),
                    extra: E::new(begin, end),
                })
            }

            StmtP::Return(maybe_expr) => {
                let node = match maybe_expr {
                    Some(expr) => {
                        Ast::Return(Some(Box::new(self.from_expr(expr, context, codemap)?)))
                    }
                    None => Ast::Return(None),
                };
                Ok(AstNode {
                    node,
                    extra: E::new(begin, end),
                })
            }

            StmtP::Assign(assign) => {
                let rhs = self.from_expr(assign.rhs, context, codemap)?;
                let target: AssignTarget = assign.lhs.node.into();
                Ok(AstNode {
                    node: Ast::Assign(target, Box::new(rhs)),
                    extra: E::new(begin, end),
                })
            }

            StmtP::Expression(expr) => self.from_expr(expr, context, codemap),

            _ => unimplemented!("{:?}", item),
        }
    }

    fn from_expr<E: Extra, P: syntax::ast::AstPayload>(
        &mut self,
        item: syntax::ast::AstExprP<P>,
        context: &Context,
        codemap: &CodeMap,
    ) -> Result<AstNode<E>> {
        use syntax::ast::ExprP;
        let r = codemap.resolve_span(item.span);
        let begin = CodeLocation {
            line: r.begin.line,
            col: r.begin.column,
        };
        let end = CodeLocation {
            line: r.end.line,
            col: r.end.column,
        };

        match item.node {
            ExprP::Op(lhs, op, rhs) => {
                let ast = Ast::BinaryOp(
                    op.into(),
                    Box::new(self.from_expr(*lhs, context, codemap)?),
                    Box::new(self.from_expr(*rhs, context, codemap)?),
                );
                Ok(AstNode {
                    node: ast,
                    extra: E::new(begin, end),
                })
            }
            ExprP::Call(expr, expr_args) => {
                let mut args = vec![];
                for arg in expr_args {
                    args.push(self.from_argument(arg, context, codemap)?);
                }
                let ast = Ast::Call(Box::new(self.from_expr(*expr, context, codemap)?), args);
                Ok(AstNode {
                    node: ast,
                    extra: E::new(begin, end),
                })
            }
            ExprP::Identifier(ident) => {
                let name = ident.node.ident;
                Ok(AstNode {
                    node: Ast::Identifier(name),
                    extra: E::new(begin, end),
                })
            }

            ExprP::Literal(lit) => {
                let x: Literal = lit.into();
                Ok(AstNode {
                    node: Ast::Literal(x),
                    extra: E::new(begin, end),
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
    ) -> Result<Argument<E>> {
        use syntax::ast::ArgumentP;
        match item.node {
            ArgumentP::Positional(expr) => Ok(Argument::Positional(Box::new(
                self.from_expr(expr, context, codemap)?,
            ))),
            _ => unimplemented!(),
        }
    }
}
