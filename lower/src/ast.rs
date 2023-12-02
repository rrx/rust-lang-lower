use melior::ir;
use melior::Context;
use std::fmt::Debug;

use codespan_reporting::files::{Files, SimpleFiles};

#[derive(Debug)]
pub enum AstType {
    Int,
    Float,
    Bool,
    Unknown,
}

#[derive(Debug)]
pub enum Literal {
    Int(i64),
    Float(f64),
    Bool(bool),
}

#[derive(Debug)]
pub enum BinaryOperation {
    Add,
    Subtract,
    Equal,
}

#[derive(Debug)]
pub enum Argument<E> {
    Positional(Box<AstNode<E>>),
}

#[derive(Debug)]
pub enum Parameter<E> {
    Normal(String, AstType),
    Dummy(AstNode<E>),
}

#[derive(Debug)]
pub struct ParameterNode<E> {
    pub node: Parameter<E>,
    pub extra: E,
}

#[derive(Debug)]
pub struct Definition<E> {
    pub name: String,
    pub params: Vec<ParameterNode<E>>,
    //pub return_type: Option<Box<AstTypeExprP<P>>>,
    pub body: Option<Box<AstNode<E>>>,
    //pub payload: P::DefPayload,
}

#[derive(Debug)]
pub enum Builtin<E> {
    Assert(Box<Argument<E>>),
    Print(Box<Argument<E>>),
}

#[derive(Debug)]
pub enum Ast<E> {
    BinaryOp(BinaryOperation, Box<AstNode<E>>, Box<AstNode<E>>),
    Call(Box<AstNode<E>>, Vec<Argument<E>>),
    Identifier(String),
    Literal(Literal),
    Sequence(Vec<AstNode<E>>),
    Definition(Definition<E>),
    Variable(Definition<E>),
    Assign(AssignTarget, Box<AstNode<E>>),
    Conditional(Box<AstNode<E>>, Box<AstNode<E>>, Option<Box<AstNode<E>>>),
    Return(Option<Box<AstNode<E>>>),
    Test(Box<AstNode<E>>, Box<AstNode<E>>),
    While(Box<AstNode<E>>, Box<AstNode<E>>),
    Builtin(Builtin<E>),
}

impl<E: Extra> Ast<E> {
    pub fn node(self, file_id: usize, begin: CodeLocation, end: CodeLocation) -> AstNode<E> {
        AstNode {
            node: self,
            extra: E::new(file_id, begin, end),
        }
    }

    pub fn assign(target: AssignTarget, node: AstNode<E>) -> Self {
        Ast::Assign(target, Box::new(node))
    }

    pub fn bool(x: bool) -> Self {
        Ast::Literal(Literal::Bool(x))
    }
}

#[derive(Debug, Clone)]
pub struct CodeLocation {
    pub line: usize,
    pub col: usize,
}

#[derive(Debug)]
pub struct SimpleExtra {
    span: Span,
}

impl Extra for SimpleExtra {
    fn new(file_id: usize, begin: CodeLocation, end: CodeLocation) -> Self {
        Self {
            span: Span {
                file_id,
                begin,
                end,
            },
        }
    }
    fn location<'c>(
        &self,
        context: &'c Context,
        files: &SimpleFiles<String, String>,
    ) -> ir::Location<'c> {
        if let Ok(name) = files.name(self.span.file_id) {
            ir::Location::new(
                context,
                &name,
                self.span.begin.line + 1,
                self.span.begin.col + 1,
            )
        } else {
            ir::Location::unknown(context)
        }
    }
}

pub trait Extra: Debug {
    fn new(file_id: usize, begin: CodeLocation, end: CodeLocation) -> Self;
    fn location<'c>(
        &self,
        context: &'c Context,
        files: &SimpleFiles<String, String>,
    ) -> ir::Location<'c>;
}

#[derive(Debug)]
pub struct Span {
    pub file_id: usize,
    pub begin: CodeLocation,
    pub end: CodeLocation,
}

#[derive(Debug)]
pub struct AstNode<E> {
    pub node: Ast<E>,
    pub extra: E,
}

#[derive(Debug)]
pub enum AssignTarget {
    Identifier(String),
}
