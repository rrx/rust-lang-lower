use crate::ast::{Ast, AstNode, Span};
use crate::ir::IRArg;
use crate::{
    //AstNode, AstType,
    Diagnostics,
    Extra,
    IREnvironment,
    IRPlaceTable,
    NodeBuilder,
    StringKey,
    //ParseError,
    //PlaceId,
    //PlaceNode, StringKey, SymIndex
};

use anyhow::Error;
use anyhow::Result;
use std::collections::HashMap;

use crate::ir::{BlockTable, IRBlock, IRKind, IRNode};
use petgraph::graph::NodeIndex;

pub struct BlockScope {
    // names must be unique in the scope
    names: HashMap<StringKey, NodeIndex>,
}

pub struct AstBlockSorter<E> {
    pub exprs: Vec<AstNode<E>>,
    pub stack: Vec<AstNode<E>>,
    pub blocks: Vec<IRBlock>,
    pub names: HashMap<StringKey, NodeIndex>,
}

impl<E: Extra> AstBlockSorter<E> {
    pub fn new() -> Self {
        Self {
            exprs: vec![],
            blocks: vec![],
            stack: vec![],
            names: HashMap::new(),
        }
    }

    pub fn add(
        &mut self,
        expr: AstNode<E>,
        env: &mut IREnvironment,
        place: &mut IRPlaceTable,
        scope: &mut BlockScope,
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) -> Result<()> {
        // create blocks as we go
        match &expr.node {
            Ast::Label(name, params) => {
                let mut args = vec![];
                for p in params {
                    args.push(IRArg {
                        name: p.name,
                        ty: p.ty.clone(),
                    });
                }
                let block_index = env.blocks.add_block(place, *name, args, d);
                // name should be unique in scope
                assert!(!scope.names.contains_key(&name));
                scope.names.insert(*name, block_index);
            }
            _ => {
                // not a label
                if self.exprs.len() == 0 {
                    // empty expressions, create a block
                    let label = b.s("block");
                    let block_index = env.blocks.add_block(place, label, vec![], d);
                    // name should be unique in scope
                    assert!(!scope.names.contains_key(&label));
                    scope.names.insert(label, block_index);
                    self.exprs.push(b.label(label, vec![]));
                }
            }
        }
        self.exprs.push(expr);
        Ok(())
    }

    pub fn close(
        &mut self,
        place: &mut IRPlaceTable,
        env: &mut IREnvironment,
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) -> Result<()> {
        if self.stack.len() == 0 {
            return Ok(());
        }

        let exprs = self.stack.drain(1..).collect::<Vec<_>>();

        let first = self.stack.pop().unwrap();
        assert_eq!(self.stack.len(), 0);
        let span_first = exprs.first().unwrap().extra.get_span().clone();
        let span_last = exprs.last().unwrap().extra.get_span().clone();
        let _span = Span {
            file_id: span_first.file_id,
            begin: span_last.begin,
            end: span_last.end,
        };

        let label = if let Ast::Label(ref label, ref _args) = first.node {
            label
        } else {
            unreachable!()
        };

        let block_index = self.names.get(label).unwrap();
        let block = env.blocks.g.node_weight(*block_index).unwrap();
        let mut children = vec![];
        // skip the first child which is a label, it's redundant now that we have a block
        let params = block.params.clone();
        for expr in exprs.into_iter() {
            let (ir, ty) = expr.lower_ir_expr(env, place, d, b)?;
            children.push(ir);
        }

        let nb = IRBlock {
            index: *block_index,
            label: *label,
            params,
            children,
        };

        self.blocks.push(nb);
        Ok(())
    }

    pub fn visit(
        &mut self,
        expr: AstNode<E>,
        place: &mut IRPlaceTable,
        env: &mut IREnvironment,
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) {
        match expr.node {
            Ast::Label(ref name, ref params) => {
                self.close(place, env, d, b);
                self.stack.push(expr);
            }
            Ast::Goto(ref name, ref params) => {
                self.stack.push(expr);
                self.close(place, env, d, b);
            }
            /*
            Ast::Break(name) => {
                self.stack.push(expr);
                self.close(place, env, d, b);
            }
            Ast::Continue(name) => {
                self.stack.push(expr);
                self.close(env, b);
            }
            */
            Ast::Sequence(exprs) => {
                for e in exprs {
                    self.visit(e, place, env, d, b);
                }
            }
            Ast::Conditional(cond, then_expr, maybe_else) => {}
            Ast::Return(maybe_ret) => {}
            _ => (),
        }
    }

    pub fn run(
        exprs: Vec<AstNode<E>>,
        env: &mut IREnvironment,
        place: &mut IRPlaceTable,
        scope: &mut BlockScope,
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) -> Vec<IRBlock> {
        let mut s = Self::new();
        for expr in exprs {
            s.add(expr, env, place, scope, d, b);
        }
        s.blocks
    }
}

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
