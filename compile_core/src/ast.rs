use crate::{AstNode, AstType, BuiltinId, SpanId, StringKey, TypeId};

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

#[derive(Debug, Clone)]
pub struct VarDefinition {
    ty: TypeId,
    space: VarDefinitionSpace,
}

#[derive(Debug, Clone)]
pub enum Literal {
    Int(i64),
    Index(usize),
    Float(f64),
    String(String),
    Bool(bool),
    Type(TypeId),
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
            Literal::Type(_) => AstType::Type,
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

#[derive(Debug, Clone)]
pub struct BinOpNode {
    pub node: BinaryOperation,
    span_id: SpanId,
}

impl BinOpNode {
    pub fn new(node: BinaryOperation, span_id: SpanId) -> Self {
        Self { node, span_id }
    }
}

#[derive(Debug, Clone)]
pub enum Argument {
    Positional(Box<AstNode>),
}

impl From<AstNode> for Argument {
    fn from(item: AstNode) -> Self {
        Argument::Positional(item.into())
    }
}

impl Argument {
    pub fn try_string(self) -> Option<String> {
        let Self::Positional(node) = self;
        (*node).try_string()
    }
}

#[derive(Debug, Clone)]
pub enum Parameter {
    Normal,
    //WithDefault(AstNode),
    //Dummy<std::marker::PhantomData//(AstNode),
}

#[derive(Debug, Clone)]
pub struct ParameterNode {
    pub name: StringKey,
    pub ty: TypeId,
    pub node: Parameter,
    pub span_id: SpanId,
}

#[derive(Debug, Clone)]
pub struct Lambda {
    pub params: Vec<ParameterNode>,
    pub return_type: TypeId,
    pub body: Option<Box<AstNode>>,
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
pub enum Ast {
    BinaryOp(BinOpNode, Box<AstNode>, Box<AstNode>),
    UnaryOp(UnaryOperation, Box<AstNode>),
    // func, args, return type
    Call(Box<AstNode>, Vec<Argument>, TypeId),
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
    Yield(Option<Box<AstNode>>),
    While(Box<AstNode>, Box<AstNode>),
    Builtin(BuiltinId, Vec<Argument>),
    Module(StringKey, Box<AstNode>),
    Loop(StringKey, Box<AstNode>),
    Break(Option<StringKey>, Vec<AstNode>),
    Continue(Option<StringKey>, Vec<AstNode>),
    Goto(StringKey),
    BlockStart(StringKey, Vec<ParameterNode>),
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
        if let Ast::BlockStart(_, _) = self {
            true
        } else {
            false
        }
    }

    pub fn get_label(&self) -> Option<StringKey> {
        if let Ast::BlockStart(key, _) = self {
            Some(*key)
        } else {
            None
        }
    }

    pub fn is_expr(&self) -> bool {
        match self {
            Self::BinaryOp(_, _, _) => true,
            Self::UnaryOp(_, _) => true,
            Self::Call(_, _, _) => true,
            Self::Identifier(_) => true,
            Self::Literal(_) => true,
            //Self::Conditional(_, _, _) => true,
            Self::While(_, _) => true,
            _ => false,
        }
    }
}
