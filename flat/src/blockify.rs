use std::collections::VecDeque;
use thiserror::Error;

use compile_core::{
    AstType, BinaryOperation, BuiltinId, Literal, NaryOperation, SpanId, StringKey, UnaryOperation,
};

use crate::{
    BlockId, CodeEntry, CodeOffset, LinkId, Node, NodeBuilder, StringLabel, Successor, ValueId,
    VarDefinitionSpace, CFG,
};

use std::collections::HashMap;

#[derive(Error, Debug)]
pub enum BlockifyError {
    #[error("BlockifyError: Unimplemented")]
    Unimplemented,
    #[error("BlockifyError: Invalid")]
    Invalid,
    #[error("BlockifyError: Incomplete")]
    Incomplete,
    #[error("BlockifyError: NotFound")]
    NotFound(String),
    #[error("BlockifyError: Template Not Found")]
    TemplateNotFound(String),
    #[error("BlockifyError: Unwind scopes: path not found")]
    UnwindNotFound(String),
}

#[derive(Debug, Clone)]
pub enum UseIndex {
    Attr(StringKey),
    Pos(usize),
    Use(CodeOffset),
}

impl UseIndex {
    pub fn offset(self) -> CodeOffset {
        match self {
            Self::Use(offset) => offset,
            _ => unimplemented!(),
        }
    }
}

impl From<LinkId> for UseIndex {
    fn from(item: LinkId) -> Self {
        Self::Use(item.into())
    }
}

impl From<&LinkId> for UseIndex {
    fn from(item: &LinkId) -> Self {
        Self::Use(item.into())
    }
}

#[derive(Debug, Clone)]
pub struct UseIndexList(Vec<UseIndex>);
impl UseIndexList {
    pub fn new(elements: Vec<UseIndex>) -> Self {
        Self(elements)
    }
    pub fn offset(self) -> CodeOffset {
        self.0.get(0).unwrap().clone().offset()
    }
}

impl From<LinkId> for UseIndexList {
    fn from(item: LinkId) -> Self {
        Self(vec![item.into()])
    }
}

impl From<&LinkId> for UseIndexList {
    fn from(item: &LinkId) -> Self {
        Self(vec![item.into()])
    }
}

#[derive(Debug, Clone)]
pub enum LCode {
    EndModule,
    Label, // number of positional arguments, number of named arguments
    Noop,
    Declare,
    DeclareFunction(Option<BlockId>), // optional entry block
    Extern,                           // optional entry block
    //Value(LinkId),
    //ValueIndex(LinkId, u8), // index into a struct
    //
    CallValue(CodeOffset),
    Call(CodeOffset),

    Arg(u8), // get the value of a positional arg
    Val(Literal),
    Use(CodeOffset, Vec<UseIndex>),
    Tuple(Vec<LinkId>),
    Op1(UnaryOperation),
    Op2(BinaryOperation),
    NaryOp(NaryOperation),
    Load(LinkId),          // memref
    Store(LinkId, LinkId), // memref, value to store
    Return,                // return values
    Yield,                 // yield values

    // jump to block, with num args
    Jump(BlockId),
    Switch(LinkId, HashMap<usize, BlockId>),
    PlaceholderTerminal,
    PlaceholderCodeReference,

    Branch(CodeOffset, BlockId, BlockId),
    Ternary(CodeOffset, BlockId, BlockId), // condition, then_entry, else_entry
    Builtin(BuiltinId),
}

impl LCode {
    pub fn is_start(&self) -> bool {
        match self {
            Self::Label => true,
            _ => false,
        }
    }

    pub fn is_term(&self) -> bool {
        match self {
            Self::Jump(_) => true,
            Self::Switch(_, _) => true,
            Self::PlaceholderTerminal => true,
            Self::Branch(_, _, _) => true,
            Self::Return => true,
            Self::Yield => true,
            Self::EndModule => true,
            _ => false,
        }
    }
}

pub trait ICodeModule {}
