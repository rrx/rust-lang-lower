use crate::{
    ArgVec, BlockGraph, BlockGraphState, BlockGraphStateOpen, BlockGraphStateStart, BlockId,
    NodeBuilder,
};

use compile_core::SpanId;

pub trait SafeBlockState {}

pub struct Empty {}
impl SafeBlockState for Empty {}

pub struct Open {}
impl SafeBlockState for Open {}

pub struct Closed {}
impl SafeBlockState for Closed {}

pub struct SafeBlock<S: SafeBlockState> {
    pub block_id: BlockId,
    pub extra: S,
}

impl BlockGraph<BlockGraphStateStart> {}

impl BlockGraph<BlockGraphStateOpen> {
    fn root_block(&mut self) -> SafeBlock<Closed> {
        SafeBlock {
            block_id: self.static_block_id(),
            extra: Closed {},
        }
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
