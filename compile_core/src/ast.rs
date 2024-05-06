use crate::{AstNode, AstType, NodeBuilder, SpanId, StringKey, TypeId};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum DefinitionId {
    Var(u32),
    Arg(u32),
}

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
pub struct Definition {
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

    pub fn get_return_type(&self) -> AstType {
        AstType::Unit
    }
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
    Call(Box<AstNode>, Vec<Argument>, AstType),
    Identifier(StringKey),
    Literal(Literal),
    Sequence(Vec<AstNode>),
    Definition(Definition),
    Global(StringKey, Box<AstNode>),
    Assign(AssignTarget, Box<AstNode>),
    Branch(Box<AstNode>, StringKey, StringKey),
    Conditional(Box<AstNode>, Box<AstNode>, Option<Box<AstNode>>),
    Ternary(Box<AstNode>, Box<AstNode>, Box<AstNode>),
    Return(Option<Box<AstNode>>),
    While(Box<AstNode>, Box<AstNode>),
    Builtin(Builtin, Vec<Argument>),
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

    pub fn from_name(name: &str, mut args: Vec<Argument>, b: &mut NodeBuilder) -> Option<Self> {
        if name == "goto" {
            let rest = args
                .split_off(1)
                .into_iter()
                .map(|a| {
                    let Argument::Positional(expr) = a;
                    *expr
                })
                .collect::<Vec<_>>();
            assert_eq!(rest.len(), 0);
            let s = args.pop().unwrap().try_string().unwrap();
            let key = b.s(&s);
            Some(Self::Goto(key.into()))
        } else if name == "static" {
            println!("args: {:?}", args);
            let Argument::Positional(value) = args.pop().unwrap();
            let Argument::Positional(name_node) = args.pop().unwrap();
            let name = b.s(&name_node.try_string().unwrap());
            Some(Self::global(name, *value))
        } else if name == "label" {
            let rest = args.split_off(1);
            let s = args.pop().unwrap().try_string().unwrap();
            let key = b.s(&s);

            let mut params = vec![];
            for arg in rest {
                let Argument::Positional(node) = arg;
                let name = node.try_string().unwrap();
                let key = b.s(&name);
                let ty = b.t(&AstType::Unit);
                params.push(ParameterNode {
                    name: key,
                    ty,
                    node: Parameter::Normal,
                    span_id: b.span_id.clone(),
                });
            }
            Some(Self::BlockStart(key.into(), vec![]))
        } else if name == "ternary" {
            let Argument::Positional(else_expr) = args.pop().unwrap();
            let Argument::Positional(then_expr) = args.pop().unwrap();
            let Argument::Positional(condition) = args.pop().unwrap();
            Some(Self::Ternary(
                condition.into(),
                then_expr.into(),
                else_expr.into(),
            ))
        } else {
            None
        }
    }
}
