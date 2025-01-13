use crate::{
    ArgVec, BlockGraph, BlockGraphState, BlockGraphStateOpen, BlockGraphStateStart, BlockId,
    IRBlock, NodeBuilder, ScopeId, ScopeLayer,
};

use compile_core::SpanId;

pub trait SafeBlockState {}

pub struct Empty {}
impl SafeBlockState for Empty {}
pub struct Open {}
impl SafeBlockState for Open {}
pub struct Closed {}

impl SafeBlock<Closed> {}

impl SafeBlockState for Closed {}

pub struct Unknown {}
impl SafeBlockState for Unknown {}
impl SafeBlock<Unknown> {}

pub struct SafeBlock<S: SafeBlockState> {
    pub block_id: BlockId,
    pub extra: S,
}

impl SafeBlock<Open> {}

impl<S: SafeBlockState> SafeBlock<S> {
    pub fn unknown(self) -> SafeBlock<Unknown> {
        SafeBlock {
            block_id: self.block_id,
            extra: Unknown {},
        }
    }
}

pub type SafeBlockOpen = SafeBlock<Open>;
pub type SafeBlockClosed = SafeBlock<Closed>;
pub type SafeBlockEmpty = SafeBlock<Empty>;
pub type SafeBlockUnknown = SafeBlock<Unknown>;

impl BlockGraph<BlockGraphStateStart> {}

impl BlockGraph<BlockGraphStateOpen> {
    fn root_block(&mut self) -> SafeBlock<Closed> {
        SafeBlock {
            block_id: self.static_block_id(),
            extra: Closed {},
        }
    }

    pub fn block<B: SafeBlockState>(&self, block: &SafeBlock<B>) -> &IRBlock {
        self.get_block(block.block_id)
    }

    pub fn scope_id<B: SafeBlockState>(&self, block: &SafeBlock<B>) -> ScopeId {
        let block = self.get_block(block.block_id);
        block.scope()
    }

    pub fn scope<B: SafeBlockState>(&self, block: &SafeBlock<B>) -> &ScopeLayer {
        let block = self.get_block(block.block_id);
        self.get_scope(block.scope())
    }

    pub fn safe_unknown(&self) -> SafeBlock<Unknown> {
        SafeBlock {
            block_id: self.current_block_id(),
            extra: Unknown {},
        }
    }

    pub fn safe_block_try_open(&mut self, block: &SafeBlock<Unknown>) -> Option<SafeBlock<Open>> {
        let block_id = block.block_id;
        let block = self.get_block(block_id);
        if block.is_term() {
            return None;
        }
        Some(SafeBlock {
            block_id,
            extra: Open {},
        })
    }

    pub fn safe_block_try_closed(
        &mut self,
        block: SafeBlock<Unknown>,
    ) -> Option<SafeBlock<Closed>> {
        let block_id = block.block_id;
        let block = self.get_block(block_id);
        if !block.is_term() {
            return None;
        }
        Some(SafeBlock {
            block_id,
            extra: Closed {},
        })
    }
}

impl<S: BlockGraphState> BlockGraph<S> {
    fn new_safe_block<B: SafeBlockState>(&mut self, block: SafeBlock<B>) -> SafeBlock<Empty> {
        //let block_id = self.new_block(block.block_id);
        SafeBlock {
            block_id: block.block_id,
            extra: Empty {},
        }
    }

    fn start_block(&mut self, block: SafeBlock<Empty>) -> SafeBlock<Open> {
        SafeBlock {
            block_id: block.block_id,
            extra: Open {},
        }
    }

    pub fn safe_switch_block(&mut self, block_id: BlockId) -> SafeBlock<Open> {
        let block = self.get_block(block_id);
        assert!(!block.is_term());
        SafeBlock {
            block_id,
            extra: Open {},
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stuff1() {
        let mut b = NodeBuilder::new();
        let key = b.labels.s("module");
        let mut g = BlockGraph::new(key);
        let b = g.root_block();
        let empty = g.new_safe_block(b);
        let open = g.start_block(empty);
        //let closed = g.jump(open, g.static_block_id());
    }
}
