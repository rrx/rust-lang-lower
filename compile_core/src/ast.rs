use crate::{AstNode, AstType, BuiltinId, SpanId, StringKey, TypeId};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum VarDefinitionSpace {
    Arg,
    Reg,
    Static,
    Stack,
    Heap,
    Default,
}

impl Default for VarDefinitionSpace {
    fn default() -> Self {
        Self::Default
    }
}

impl VarDefinitionSpace {
    pub fn requires_deref(&self) -> bool {
        match self {
            Self::Static | Self::Stack | Self::Heap => true,
            _ => false,
        }
    }
}

/*
#[derive(Debug, Clone)]
pub struct VarDefinition {
    ty: TypeId,
    space: VarDefinitionSpace,
}
*/

#[derive(Debug, Clone)]
pub enum Literal {
    Int(i64),
    Index(usize),
    Float(f64),
    String(String),
    Bool(bool),
    //Type(TypeId),
}

impl From<Literal> for AstType {
    fn from(item: Literal) -> Self {
        From::from(&item)
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
            //Literal::Type(_) => AstType::Type,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum UnaryOperation {
    Minus,
}

#[derive(Debug, Clone, Copy)]
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

impl BinaryOperation {
    pub fn get_type(&self, x_ty: &AstType, _y_ty: &AstType) -> AstType {
        match self {
            Self::Add => x_ty.clone(),
            Self::Subtract => x_ty.clone(),
            Self::Multiply => x_ty.clone(),
            Self::Divide => x_ty.clone(),
            Self::NE | Self::EQ | Self::GT | Self::GTE => AstType::Bool,
        }
    }
}

#[derive(Debug, Clone)]
pub struct BinOpNode {
    pub node: BinaryOperation,
    pub span_id: SpanId,
}

impl BinOpNode {
    pub fn new(node: BinaryOperation, span_id: SpanId) -> Self {
        Self { node, span_id }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum NaryOperation {
    Struct,
}

impl NaryOperation {
    pub fn get_type(&self, types: &Vec<AstType>) -> AstType {
        match self {
            Self::Struct => AstType::Struct(types.iter().map(|ty| (None, ty.clone())).collect()),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Argument {
    Positional(Box<AstNode>),
    Named(StringKey, Box<AstNode>),
    Args(StringKey, Vec<AstNode>),
    KwArgs(StringKey, HashMap<StringKey, AstNode>),
}

impl From<AstNode> for Argument {
    fn from(item: AstNode) -> Self {
        Argument::Positional(item.into())
    }
}

impl Argument {
    pub fn try_string(self) -> Option<String> {
        let node = self.expr();
        node.try_string()
    }

    pub fn get_expr(&self) -> &AstNode {
        match &self {
            Argument::Positional(expr) => expr,
            Argument::Named(_, expr) => expr,
            //Argument::Args(seq) => &Ast::Sequence(seq.clone()).into(),
            _ => unimplemented!(),
        }
    }

    pub fn get_name(&self) -> Option<StringKey> {
        match &self {
            Argument::Positional(_) => None,
            Argument::Named(key, _) => Some(*key),
            Argument::Args(key, _) => Some(*key),
            Argument::KwArgs(key, _) => Some(*key),
        }
    }

    pub fn expr(self) -> AstNode {
        match self {
            Argument::Positional(expr) => *expr,
            Argument::Named(_, expr) => *expr,
            _ => unimplemented!(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Parameter {
    Normal,
    WithDefault(AstNode),
    Args,
    KwArgs,
    //Dummy<std::marker::PhantomData//(AstNode),
}

#[derive(Debug, Clone)]
pub struct ParameterNode {
    pub name: StringKey,
    pub ty: TypeId,
    pub node: Parameter,
    pub span_id: SpanId,
    //pub default: Option<AstNode>,
}

#[derive(Debug, Clone)]
pub struct Lambda {
    pub fun_type: TypeId,
    pub arg_type: TypeId,
    //pub params: Vec<ParameterNode>,
    pub return_type: TypeId,
    pub body: Option<Box<AstNode>>,
    pub defaults: HashMap<StringKey, AstNode>,
    //pub open_kwargs: Option<StringKey>,
    //pub open_args: Option<StringKey>,
}

#[derive(Debug, Clone)]
pub enum DerefTarget {
    Offset(usize),
    Field(String),
}

#[derive(Debug, Clone)]
pub enum AssignTarget {
    Identifier(StringKey),
    Alloca(StringKey),
}

#[derive(Debug, Clone)]
pub enum ControlFlowMarker {
    LoopStart(Option<StringKey>),
    LoopBreak(Option<StringKey>),
    LoopContinue(Option<StringKey>),
    BlockStart(Option<StringKey>, Vec<ParameterNode>),
    BlockEnd,
    Goto(StringKey),
}

impl From<ControlFlowMarker> for AstNode {
    fn from(c: ControlFlowMarker) -> Self {
        Ast::ControlFlowMarker(c).into()
    }
}

impl From<ControlFlowMarker> for Ast {
    fn from(c: ControlFlowMarker) -> Self {
        Ast::ControlFlowMarker(c)
    }
}

impl ControlFlowMarker {
    pub fn node(self, span_id: SpanId) -> AstNode {
        let ast: Ast = self.into();
        ast.node(span_id)
    }
}

#[derive(Debug, Clone)]
pub enum Ast {
    BinaryOp(BinOpNode, Box<AstNode>, Box<AstNode>),
    UnaryOp(UnaryOperation, Box<AstNode>),
    NaryOp(NaryOperation, Vec<AstNode>),
    // func, args, return type
    Call(Box<AstNode>, Vec<Argument>),
    // array(element type, dimensions), empty dim is the same as scalar
    Array(TypeId, Vec<AstNode>),
    Identifier(StringKey),
    Literal(Literal),
    Sequence(Vec<AstNode>),
    Lambda(Lambda),
    Global(StringKey, Box<AstNode>),
    Assign(AssignTarget, Box<AstNode>),
    Branch(Box<AstNode>, StringKey, StringKey),
    Conditional(Box<AstNode>, Box<AstNode>, Option<Box<AstNode>>),
    Ternary(Box<AstNode>, Box<AstNode>, Box<AstNode>),
    Return(Option<Box<AstNode>>),
    CloseBlock, // implicit close has different meaning depending on the context
    Yield(Option<Box<AstNode>>),
    While(Box<AstNode>, Box<AstNode>),
    Builtin(BuiltinId, Vec<Argument>),
    Module(StringKey, Box<AstNode>),
    ControlFlowMarker(ControlFlowMarker),
    Loop(StringKey, Box<AstNode>),

    // break and continue, yielding a value
    Break(Option<StringKey>, Vec<AstNode>),
    Continue(Option<StringKey>, Vec<AstNode>),

    Block(StringKey, Vec<ParameterNode>, Box<AstNode>),
    Type(TypeId),
    Noop,
    Error,
}

impl Ast {
    pub fn global(name: StringKey, node: AstNode) -> Self {
        Ast::Global(name, Box::new(node))
    }

    pub fn node(self, span_id: SpanId) -> AstNode {
        AstNode {
            node: self,
            span_id,
        }
    }

    pub fn assign(target: AssignTarget, node: AstNode) -> Self {
        Ast::Assign(target, Box::new(node))
    }

    pub fn bool(x: bool) -> Self {
        Ast::Literal(Literal::Bool(x))
    }

    pub fn is_label(&self) -> bool {
        match self {
            Ast::ControlFlowMarker(ControlFlowMarker::BlockStart(_, _)) => true,
            Ast::Block(_, _, _) => true,
            _ => false,
        }
    }

    pub fn get_label(&self) -> Option<StringKey> {
        match self {
            Ast::ControlFlowMarker(ControlFlowMarker::BlockStart(key, _)) => *key,
            Ast::Block(key, _, _) => Some(*key),
            _ => None,
        }
    }

    pub fn is_term(&self) -> bool {
        match self {
            Ast::Branch(_, _, _) => true,
            Ast::Conditional(_, _, _) => true,
            Ast::While(_, _) => true,
            Ast::Return(_) => true,
            Ast::Loop(_, _) => true,
            Ast::Module(_, _) => true,
            Ast::Break(_, _) => true,
            Ast::Continue(_, _) => true,
            Ast::CloseBlock => true,
            Ast::ControlFlowMarker(ControlFlowMarker::Goto(_)) => true,
            _ => false,
        }
    }
}
