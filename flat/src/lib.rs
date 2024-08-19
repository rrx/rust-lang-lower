pub mod block_format;
pub mod blockify;
pub mod builder;
pub mod builtin;
mod dump;
pub mod graph;
pub mod scope;
pub mod seq;
pub mod flatten;

pub use block_format::*;
pub use blockify::{Blockify, LCode, BlockifyError};
pub use builder::*;
pub use builtin::*;
pub use scope::{Environment, ScopeId, ScopeLayer, ScopeType, Successor, TemplateId};
pub use flatten::*;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct ValueId(pub(crate) u32);

impl ValueId {
    pub fn new(index: u32) -> Self {
        Self(index)
    }
    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

impl std::fmt::Display for ValueId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "v{}", self.index())
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct BlockId(pub(crate) u32);

impl BlockId {
    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

impl std::fmt::Display for BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "b{}", self.index())
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum CodeOffset {
    Value(ValueId),
    Block(BlockId),
}

impl std::fmt::Display for CodeOffset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Value(x) => write!(f, "{}", x),
            Self::Block(x) => write!(f, "{}", x),
        }
    }
}

impl From<ValueId> for CodeOffset {
    fn from(item: ValueId) -> Self {
        Self::Value(item)
    }
}

impl From<BlockId> for CodeOffset {
    fn from(item: BlockId) -> Self {
        Self::Block(item)
    }
}
