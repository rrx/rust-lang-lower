pub mod block_format;
pub mod blockify;
pub mod builder;
pub mod graph;
pub mod mlir;
pub mod scope;

pub use blockify::{Blockify, LCode};
pub use builder::*;
pub use mlir::{Lower, LowerBlocks};
pub use scope::{Environment, ScopeId, ScopeLayer, ScopeType, Successor, TemplateId};

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

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct BlockId(pub(crate) u32);

impl BlockId {
    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum CodeOffset {
    Value(ValueId),
    Block(BlockId),
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
