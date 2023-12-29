use crate::ast::Span;
use crate::{
    //AstNode, AstType,
    Diagnostics,
    Extra,
    IRPlaceTable,
    NodeBuilder,
    //ParseError,
    //PlaceId,
    //PlaceNode, StringKey, SymIndex
};

use crate::ir::{BlockTable, IRBlock, IRKind, IRNode};
use petgraph::graph::NodeIndex;

pub struct IRBlockSorter {
    pub stack: Vec<IRNode>,
    pub blocks: Vec<IRBlock>,
}

impl IRBlockSorter {
    pub fn new() -> Self {
        Self {
            stack: vec![],
            blocks: vec![],
        }
    }

    pub fn blocks<E: Extra>(self, b: &mut NodeBuilder<E>) -> Vec<IRNode> {
        self.blocks
            .into_iter()
            .map(|block| IRNode::new(IRKind::Block(block), b.extra().get_span()))
            .collect()
    }

    pub fn run<E: Extra>(
        ir: IRNode,
        places: &mut IRPlaceTable,
        blocks: &mut BlockTable,
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) -> IRNode {
        let mut s = Self::new();
        let ir = match ir.kind {
            IRKind::Seq(exprs) => {
                let label = blocks.fresh_block_label("module", b);
                //let module = b.s("module");
                let mut block = IRBlock::new(label, vec![], exprs);
                //let block_index = blocks.add_block(places, label, vec![], d);
                let block_index = NodeIndex::new(0);
                block
                    .children
                    .insert(0, b.ir_label(label, block_index, vec![]));
                IRNode::new(IRKind::Block(block), b.extra().get_span())
            }
            IRKind::Block(ref _block) => ir,
            _ => unreachable!(),
        };

        s.sort(ir, places, blocks, d, b);
        s.close_block(places, blocks, d, b);
        let blocks = s.blocks(b);
        b.ir_seq(blocks)
    }

    pub fn sort_block<E: Extra>(
        &mut self,
        block: IRBlock,
        places: &mut IRPlaceTable,
        blocks: &mut BlockTable,
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) {
        let mut s = Self::new();
        for c in block.children {
            s.sort(c, places, blocks, d, b);
        }
        s.close_block(places, blocks, d, b);
        for block in s.blocks {
            self.blocks.push(block);
        }
    }

    pub fn sort<E: Extra>(
        &mut self,
        ir: IRNode,
        places: &mut IRPlaceTable,
        blocks: &mut BlockTable,
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) {
        match ir.kind {
            IRKind::Seq(exprs) => {
                for e in exprs {
                    self.sort(e, places, blocks, d, b);
                }
            }
            //IRKind::Set(_, v, _) => {
            //self.sort(*v, b);
            //}
            IRKind::Block(nb) => {
                self.sort_block(nb, places, blocks, d, b);
            }
            IRKind::Jump(_, _) => {
                self.stack.push(ir);
                self.close_block(places, blocks, d, b);
            }
            IRKind::Label(_, _, _) => {
                self.close_block(places, blocks, d, b);
                self.stack.push(ir);
            }
            _ => {
                self.stack.push(ir);
            }
        }
    }

    pub fn close_block<E: Extra>(
        &mut self,
        places: &mut IRPlaceTable,
        blocks: &mut BlockTable,
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) {
        if self.stack.len() == 0 {
            return;
        }

        let first = self.stack.first();

        let span_first = first.as_ref().unwrap().span.clone();
        let span_last = self.stack.last().unwrap().span.clone();
        let _span = Span {
            file_id: span_first.file_id,
            begin: span_last.begin,
            end: span_last.end,
        };

        let nb = if let IRKind::Label(label, block_index, args) = &first.as_ref().unwrap().kind {
            IRBlock {
                index: *block_index,
                label: *label,
                params: args.clone(),
                // skip the first child which is a label, it's redundant now that we have a block
                children: self.stack.drain(..).skip(1).collect(),
            }
        } else {
            //assert!(false);
            let offset = self.blocks.len();
            //let label = blocks.fresh_block_label("block", b);
            let label = b.strings.intern(format!("_block{}", offset));
            //let block_index = blocks.add_block(places, label, vec![], d);
            let block_index = NodeIndex::new(0);
            IRBlock {
                index: block_index,
                label,
                params: vec![],
                children: self.stack.drain(..).collect(),
            }
        };
        // end of block

        self.blocks.push(nb);
    }
}
