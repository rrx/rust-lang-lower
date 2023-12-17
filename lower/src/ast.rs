use crate::Diagnostics;
//use anyhow::Error;
//use anyhow::Result;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use melior::ir;
use melior::Context;
use std::fmt::Debug;

#[derive(Debug, PartialEq, Clone)]
pub enum AstType {
    Int,
    Index,
    String,
    Float,
    Bool,
    Unit,
    Ptr(Box<AstType>),
    Tuple(Vec<AstType>),
    // Func(parameters, return type)
    Func(Vec<AstType>, Box<AstType>),
    //Unknown,
}

impl From<Literal> for AstType {
    fn from(item: Literal) -> Self {
        match item {
            Literal::Int(_) => AstType::Int,
            Literal::Float(_) => AstType::Float,
            Literal::Bool(_) => AstType::Bool,
            Literal::Index(_) => AstType::Index,
            Literal::String(_) => AstType::String,
        }
    }
}

impl From<&Literal> for AstType {
    fn from(item: &Literal) -> Self {
        match item {
            Literal::Int(_) => AstType::Int,
            Literal::Float(_) => AstType::Float,
            Literal::Bool(_) => AstType::Bool,
            Literal::Index(_) => AstType::Index,
            Literal::String(_) => AstType::String,
        }
    }
}

#[derive(Debug)]
pub enum Literal {
    Int(i64),
    Index(usize),
    Float(f64),
    String(String),
    Bool(bool),
}

#[derive(Debug)]
pub enum UnaryOperation {
    Minus,
}

#[derive(Debug)]
pub enum BinaryOperation {
    Add,
    Subtract,
    Multiply,
    Divide,
    NE,
    EQ,
    GT,
    GTE,
}

#[derive(Debug)]
pub enum Argument<E> {
    Positional(Box<AstNode<E>>),
}

impl<E> From<AstNode<E>> for Argument<E> {
    fn from(item: AstNode<E>) -> Self {
        Argument::Positional(item.into())
    }
}

#[derive(Debug)]
pub enum Parameter<E> {
    Normal,
    WithDefault(AstNode<E>),
    Dummy(AstNode<E>),
}

#[derive(Debug)]
pub struct ParameterNode<E> {
    pub name: String,
    pub ty: AstType,
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
    Import,
}

impl Builtin {
    pub fn from_name(name: &str) -> Option<Builtin> {
        if name == "check" {
            Some(Builtin::Assert)
        } else if name == "print" {
            Some(Builtin::Print)
        } else if name == "use" {
            Some(Builtin::Import)
        } else {
            None
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            Self::Assert => 1,
            Self::Print => 1,
            Self::Import => 1,
        }
    }
}

#[derive(Debug)]
pub enum DerefTarget {
    Offset(usize),
    Field(String),
}

#[derive(Debug)]
pub enum Terminator {
    Jump(String),
    Branch(String, String),
    Return,
}

#[derive(Debug)]
pub struct NodeBlock<E> {
    pub(crate) name: String,
    pub(crate) params: Vec<ParameterNode<E>>,
    pub(crate) body: Box<AstNode<E>>,
}

#[derive(Debug)]
pub enum Ast<E> {
    BinaryOp(BinaryOperation, Box<AstNode<E>>, Box<AstNode<E>>),
    UnaryOp(UnaryOperation, Box<AstNode<E>>),
    Call(Box<AstNode<E>>, Vec<Argument<E>>, AstType),
    Identifier(String),
    Literal(Literal),
    Sequence(Vec<AstNode<E>>),
    Definition(Definition<E>),
    Variable(Definition<E>),
    Global(String, Box<AstNode<E>>),
    Assign(AssignTarget, Box<AstNode<E>>),
    Replace(AssignTarget, Box<AstNode<E>>),
    Mutate(Box<AstNode<E>>, Box<AstNode<E>>),
    Conditional(Box<AstNode<E>>, Box<AstNode<E>>, Option<Box<AstNode<E>>>),
    Return(Option<Box<AstNode<E>>>),
    Test(Box<AstNode<E>>, Box<AstNode<E>>),
    While(Box<AstNode<E>>, Box<AstNode<E>>),
    Builtin(Builtin, Vec<Argument<E>>),
    Deref(Box<AstNode<E>>, DerefTarget),
    Block(NodeBlock<E>), //String, Vec<ParameterNode<E>>, Box<AstNode<E>>),
    Loop(String, Box<AstNode<E>>),
    Break(String),
    Continue(String),
    Goto(String),
    Error,
}

impl<E: Extra> Ast<E> {
    pub fn global(name: &str, node: AstNode<E>) -> Self {
        Ast::Global(name.to_string(), Box::new(node))
    }

    pub fn assign(target: AssignTarget, node: AstNode<E>) -> Self {
        Ast::Assign(target, Box::new(node))
    }

    pub fn bool(x: bool) -> Self {
        Ast::Literal(Literal::Bool(x))
    }

    pub fn terminator(&self) -> Option<Terminator> {
        match self {
            Self::Sequence(exprs) => exprs.last().unwrap().node.terminator(),
            Self::Block(nb) => nb.body.node.terminator(),
            Self::Goto(label) => Some(Terminator::Jump(label.clone())),
            Self::Return(_) => Some(Terminator::Return),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct CodeLocation {
    pub pos: u32,
    pub line: usize,
    pub col: usize,
}

#[derive(Clone)]
pub struct SimpleExtra {
    span: Span,
}

impl std::fmt::Debug for SimpleExtra {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.span.begin.pos == 0 && self.span.end.pos == 0 {
            f.write_str("extra")
        } else {
            f.debug_struct("span")
                .field("begin", &self.span.begin.pos)
                .field("end", &self.span.end.pos)
                .finish()
        }
    }
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
    fn span(span: Span) -> Self {
        Self { span }
    }
    fn location<'c>(&self, context: &'c Context, d: &Diagnostics) -> ir::Location<'c> {
        d.location(context, &self.span)
    }

    fn error(&self, msg: &str) -> Diagnostic<usize> {
        let r = self.span.begin.pos as usize..self.span.end.pos as usize;
        Diagnostic::error()
            .with_labels(vec![Label::primary(self.span.file_id, r).with_message(msg)])
            .with_message("error")
    }
}

pub trait Extra: Debug + Clone {
    fn new(file_id: usize, begin: CodeLocation, end: CodeLocation) -> Self;
    fn span(span: Span) -> Self;
    fn location<'c>(&self, context: &'c Context, d: &Diagnostics) -> ir::Location<'c>;
    fn error(&self, msg: &str) -> Diagnostic<usize>;
}

#[derive(Debug, Clone)]
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
impl<E> AstNode<E> {
    pub fn set_extra(mut self, extra: E) -> Self {
        self.extra = extra;
        self
    }

    pub fn new(node: Ast<E>, extra: E) -> Self {
        Self { node, extra }
    }

    pub fn try_string(&self) -> Option<String> {
        if let Ast::Literal(Literal::String(s)) = &self.node {
            Some(s.clone())
        } else {
            None
        }
    }

    pub fn is_block(&self) -> bool {
        if let Ast::Block(_nb) = &self.node {
            true
        } else {
            false
        }
    }

    pub fn try_block(self) -> Option<AstNode<E>> {
        if let Ast::Block(nb) = self.node {
            Some(*nb.body)
        } else {
            None
        }
    }

    pub fn is_seq(&self) -> bool {
        if let Ast::Sequence(_) = self.node {
            true
        } else {
            false
        }
    }

    pub fn try_seq(self) -> Option<Vec<AstNode<E>>> {
        if let Ast::Sequence(seq) = self.node {
            Some(seq)
        } else {
            None
        }
    }
}

impl<E> From<Argument<E>> for AstNode<E> {
    fn from(item: Argument<E>) -> Self {
        match item {
            Argument::Positional(x) => *x,
        }
    }
}

#[derive(Debug)]
pub enum AssignTarget {
    Identifier(String),
    Alloca(String),
}
