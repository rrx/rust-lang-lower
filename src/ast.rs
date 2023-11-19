use melior::ir;
use melior::Context;
use std::fmt::Debug;

use starlark_syntax::codemap::CodeMap;

#[derive(Debug)]
pub enum Literal {
    Int(i64),
    Float(f64),
}

#[derive(Debug)]
pub enum BinaryOperation {
    Add,
    Subtract,
    Equal,
}

#[derive(Debug)]
pub enum Argument<P> {
    Positional(Box<AstNode<P>>),
}

#[derive(Debug)]
pub enum Parameter<E> {
    Normal(String),
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
    pub body: Box<AstNode<E>>,
    //pub payload: P::DefPayload,
}

#[derive(Debug)]
pub enum Ast<E> {
    BinaryOp(BinaryOperation, Box<AstNode<E>>, Box<AstNode<E>>),
    Call(Box<AstNode<E>>, Vec<Argument<E>>),
    Identifier(String),
    Literal(Literal),
    Sequence(Vec<AstNode<E>>),
    Definition(Definition<E>),
    Assign(AssignTarget, Box<AstNode<E>>),
    Conditional(Box<AstNode<E>>, Box<AstNode<E>>, Option<Box<AstNode<E>>>),
    Return(Option<Box<AstNode<E>>>),
}

#[derive(Debug)]
pub struct CodeLocation {
    pub line: usize,
    pub col: usize,
}

#[derive(Debug)]
pub struct SimpleExtra {
    span: Span,
}

impl Extra for SimpleExtra {
    fn new(begin: CodeLocation, end: CodeLocation) -> Self {
        Self {
            span: Span { begin, end },
        }
    }
    fn location<'c>(&self, context: &'c Context, codemap: &CodeMap) -> ir::Location<'c> {
        ir::Location::new(
            context,
            codemap.filename(),
            self.span.begin.line,
            self.span.begin.col,
        )
    }
}

pub trait Extra: Debug {
    fn new(begin: CodeLocation, end: CodeLocation) -> Self;
    fn location<'c>(&self, context: &'c Context, codemap: &CodeMap) -> ir::Location<'c>;
}

#[derive(Debug)]
pub struct Span {
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
