use melior::ir;
use melior::Context;
use std::fmt::Debug;

use codespan_reporting::files::{Files, SimpleFiles};

#[derive(Debug, PartialEq, Clone)]
pub enum AstType {
    Int,
    Index,
    Float,
    Bool,
    Unit,
    Ptr,
    Tuple(Vec<AstType>),
    // Func(parameters, return type)
    Func(Vec<AstType>, Box<AstType>),
    //Unknown,
}

#[derive(Debug)]
pub enum Literal {
    Int(i64),
    Index(usize),
    Float(f64),
    Bool(bool),
}

#[derive(Debug)]
pub enum BinaryOperation {
    Add,
    Subtract,
    Multiply,
    Divide,
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
    pub return_type: Box<AstType>,
    pub body: Option<Box<AstNode<E>>>,
    //pub payload: P::DefPayload,
}

#[derive(Debug)]
pub enum Builtin {
    Assert,
    Print,
}

impl Builtin {
    pub fn from_name(name: &str) -> Option<Builtin> {
        if name == "check" {
            Some(Builtin::Assert)
        } else if name == "print" {
            Some(Builtin::Print)
        } else {
            None
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            Self::Assert => 1,
            Self::Print => 1,
        }
    }
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
    Global(String, Box<AstNode<E>>),
    Assign(AssignTarget, Box<AstNode<E>>),
    Conditional(Box<AstNode<E>>, Box<AstNode<E>>, Option<Box<AstNode<E>>>),
    Return(Option<Box<AstNode<E>>>),
    Test(Box<AstNode<E>>, Box<AstNode<E>>),
    While(Box<AstNode<E>>, Box<AstNode<E>>),
    Builtin(Builtin, Vec<Argument<E>>),
}

impl<E: Extra> Ast<E> {
    pub fn node(self, file_id: usize, begin: CodeLocation, end: CodeLocation) -> AstNode<E> {
        AstNode {
            node: self,
            extra: E::new(file_id, begin, end),
        }
    }

    pub fn global(name: &str, node: AstNode<E>) -> Self {
        Ast::Global(name.to_string(), Box::new(node))
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
