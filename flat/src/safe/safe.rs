use crate::{BlockGraph, BlockGraphState, BlockId};

pub trait SafeBlockState {}

pub struct Empty {}
impl SafeBlockState for Empty {}

pub struct Open {}
impl SafeBlockState for Open {}

pub struct Closed {}
impl SafeBlockState for Closed {}

pub struct SafeBlock<S: SafeBlockState> {
    block_id: BlockId,
    extra: S,
}

impl<S: BlockGraphState> BlockGraph<S> {
    fn root_block(&mut self) -> SafeBlock<Empty> {
        let (block_id, scope_id) = self.root();

        SafeBlock {
            block_id,
            extra: Empty {},
        }
    }

    fn new_safe_block(&mut self, block_id: BlockId) -> SafeBlock<Empty> {
        SafeBlock {
            block_id,
            extra: Empty {},
        }
    }

    fn start_block(&mut self, block: SafeBlock<Empty>) -> SafeBlock<Open> {
        SafeBlock {
            block_id: block.block_id,
            extra: Open {},
        }
    }

    fn switch_block(&mut self, block: SafeBlock<Open>) -> SafeBlock<Open> {
        SafeBlock {
            block_id: block.block_id,
            extra: Open {},
        }
    }

    fn jump(&mut self, block: SafeBlock<Open>, target: BlockId) -> SafeBlock<Closed> {
        SafeBlock {
            block_id: block.block_id,
            extra: Closed {},
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stuff1() {
        let mut g = BlockGraph::new();
        let b = g.root_block();
        g.new_safe_block();
    }
}
