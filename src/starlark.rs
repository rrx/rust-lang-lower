use std::error::Error;
use std::fmt::Debug;
use std::fs::File;
use std::io::Write;
use std::ops::Deref;
use std::path::Path;

use melior::{
    dialect::{arith, func, DialectRegistry},
    ir::{
        attribute::{StringAttribute, TypeAttribute},
        r#type::FunctionType,
        *,
    },
    utility::{register_all_dialects, register_all_llvm_translations},
    Context,
};

use starlark_syntax::codemap;
use starlark_syntax::codemap::CodeMap;
use starlark_syntax::lexer;
use starlark_syntax::syntax;
use starlark_syntax::syntax::module::AstModuleFields;
use starlark_syntax::syntax::Dialect;

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

impl<E: Extra> AstNode<E> {
    fn from_expr<P: syntax::ast::AstPayload>(
        item: syntax::ast::AstExprP<P>,
        context: &Context,
        codemap: &CodeMap,
    ) -> Self {
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
                    Box::new(AstNode::from_expr(*lhs, context, codemap)),
                    Box::new(AstNode::from_expr(*rhs, context, codemap)),
                );
                //.node(begin, end)
                AstNode {
                    node: ast,
                    extra: E::new(begin, end),
                }
            }
            ExprP::Call(expr, args) => {
                let args = args
                    .into_iter()
                    .map(|arg| Argument::from(arg, context, codemap))
                    .collect::<Vec<Argument<E>>>();
                let ast = Ast::Call(Box::new(AstNode::from_expr(*expr, context, codemap)), args);
                //.node(begin, end)
                //kkkkk
                AstNode {
                    node: ast,
                    extra: E::new(begin, end),
                }
            }
            ExprP::Identifier(ident) => {
                let name = ident.node.ident;
                AstNode {
                    node: Ast::Identifier(name),
                    extra: E::new(begin, end),
                }
            }

            ExprP::Literal(lit) => {
                let x: Literal = lit.into();
                AstNode {
                    node: Ast::Literal(x),
                    extra: E::new(begin, end),
                }
            }

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

impl<E: Extra> Argument<E> {
    fn from<P: syntax::ast::AstPayload>(
        item: syntax::ast::AstArgumentP<P>,
        context: &Context,
        codemap: &CodeMap,
    ) -> Self {
        use syntax::ast::ArgumentP;
        match item.node {
            ArgumentP::Positional(expr) => {
                Argument::Positional(Box::new(AstNode::from_expr(expr, context, codemap)))
            }
            _ => unimplemented!(),
        }
    }
}

impl<E: Extra> Parameter<E> {
    fn from<P: syntax::ast::AstPayload>(
        item: syntax::ast::AstParameterP<P>,
        context: &Context,
        codemap: &CodeMap,
    ) -> Self {
        use syntax::ast::ParameterP;
        match item.node {
            ParameterP::Normal(ident, maybe_type) => Parameter::Normal(ident.node.ident),
            _ => unimplemented!(),
        }
    }
}

impl<E: Extra> ParameterNode<E> {
    fn from<P: syntax::ast::AstPayload>(
        item: syntax::ast::AstParameterP<P>,
        context: &Context,
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

impl<E: Extra> AstNode<E> {
    fn from_stmt<P: syntax::ast::AstPayload>(
        item: syntax::ast::AstStmtP<P>,
        context: &Context,
        codemap: &CodeMap,
    ) -> Self {
        use syntax::ast::StmtP;
        //use syntax::ast::ParameterP;

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
                let exprs = stmts
                    .into_iter()
                    .map(|stmt| AstNode::from_stmt(stmt, context, codemap))
                    .collect::<Vec<AstNode<E>>>();
                let ast = Ast::Sequence(exprs);
                AstNode {
                    node: ast,
                    extra: E::new(begin, end),
                }
            }

            StmtP::Def(def) => {
                let params = def
                    .params
                    .into_iter()
                    .map(|p| ParameterNode::from(p, context, codemap))
                    .collect();
                let d = Definition {
                    name: def.name.ident.clone(),
                    body: Box::new(AstNode::from_stmt(*def.body, context, codemap)),
                    params,
                };
                let ast = Ast::Definition(d);
                AstNode {
                    node: ast,
                    extra: E::new(begin, end),
                }
            }

            StmtP::IfElse(expr, options) => {
                let condition = AstNode::from_expr(expr, context, codemap);
                let truestmt = AstNode::from_stmt(options.0, context, codemap);
                let elsestmt = Some(Box::new(AstNode::from_stmt(options.1, context, codemap)));
                AstNode {
                    node: Ast::Conditional(condition.into(), truestmt.into(), elsestmt),
                    extra: E::new(begin, end),
                }
            }

            StmtP::Return(maybe_expr) => {
                let expr = maybe_expr.map(|x| Box::new(AstNode::from_expr(x, context, codemap)));
                AstNode {
                    node: Ast::Return(expr.into()),
                    extra: E::new(begin, end),
                }
            }

            StmtP::Assign(assign) => {
                let rhs = AstNode::from_expr(assign.rhs, context, codemap);
                let target: AssignTarget = assign.lhs.node.into();
                AstNode {
                    node: Ast::Assign(target, Box::new(rhs)),
                    extra: E::new(begin, end),
                }
            }

            StmtP::Expression(expr) => AstNode::from_expr(expr, context, codemap),

            _ => unimplemented!(),
        }
    }
}

pub fn parse<'a>(context: &'a Context, path: &Path) -> Result<Vec<Operation<'a>>, Box<dyn Error>> {
    let dialect = syntax::Dialect::Extended;
    let m = syntax::AstModule::parse_file(&path, &dialect)?;
    let (codemap, stmt, _dialect, _typecheck) = m.into_parts();

    //let stmt = m.statement();
    //let codemap = m.codemap();
    println!("m: {:?}", &stmt);
    let ast: AstNode<SimpleExtra> = AstNode::from_stmt(stmt, context, &codemap);
    Ok(lower_expr2(context, &codemap, ast))

    //Ok(lower_stmt(context, codemap, &stmt))
}
