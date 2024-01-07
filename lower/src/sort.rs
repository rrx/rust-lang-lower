use crate::ast::{Ast, AstNode, AstNodeBlock, ParameterNode, Span};
use crate::ir::IRArg;
use crate::{
    //AstNode, AstType,
    BlockId,
    Diagnostics,
    Extra,
    IREnvironment,
    IRPlaceTable,
    NodeBuilder,
    //StringKey,
    //ParseError,
    //PlaceId,
    //PlaceNode, StringKey, SymIndex
    StringLabel,
};

use anyhow::Result;
use std::collections::HashMap;

use crate::ir::{BlockTable, IRBlock, IRKind, IRNode};
use petgraph::graph::NodeIndex;

#[derive(Default)]
pub struct BlockScope {
    // names must be unique in the scope
    names: HashMap<BlockId, NodeIndex>,
}

pub struct AstBlockSorter<E> {
    pub stack: Vec<AstNode<E>>,
    pub blocks: Vec<AstNode<E>>,
}

impl<E: Extra> AstBlockSorter<E> {
    pub fn new() -> Self {
        Self {
            stack: vec![],
            blocks: vec![],
        }
    }
    pub fn sort_children(
        &mut self,
        ast: AstNode<E>,
        entry_params: &[ParameterNode<E>],
        b: &mut NodeBuilder<E>,
    ) {
        match ast.node {
            Ast::Sequence(exprs) => {
                for e in exprs {
                    if self.blocks.len() == 0 {
                        self.sort_children(e, entry_params, b);
                    } else {
                        self.sort_children(e, &[], b);
                    }
                }
            }
            Ast::Block(ref nb) => {
                // check params match
                if self.blocks.len() == 0 {
                    assert_eq!(nb.params.len(), entry_params.len());
                }
                self.blocks.push(ast);
            }
            Ast::Goto(_, _) => {
                self.stack.push(ast);
                self.close_block(b);
            }
            Ast::Label(_, _) => {
                self.close_block(b);
                self.stack.push(ast);
            }
            _ => {
                self.stack.push(ast);
            }
        }
    }

    fn close_block(&mut self, b: &mut NodeBuilder<E>) {
        unreachable!();
        if self.stack.len() == 0 {
            return;
        }

        // create a new block
        assert!(self.stack.first().unwrap().node.is_label());
        let extra = self.stack.first().unwrap().extra.clone();
        // end of block
        //let offset = self.blocks.len();

        let name = b.labels.fresh_block_id(); //(format!("_block{}", offset));
        let children = self.stack.drain(..).collect();
        //let seq = b
        //.seq(self.stack.drain(..).collect())
        //.set_extra(extra.clone());
        let nb = AstNodeBlock {
            name,
            params: vec![],
            children, //: seq.into(),
        };
        let ast = b.build(Ast::Block(nb), extra.clone());
        self.blocks.push(ast);
    }
}

pub struct AstBlockTransform<E> {
    pub exprs: Vec<AstNode<E>>,
    pub stack: Vec<AstNode<E>>,
    pub blocks: Vec<IRBlock>,
    pub names: HashMap<BlockId, NodeIndex>,
}

impl<E: Extra> AstBlockTransform<E> {
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
                        name: StringLabel::Intern(p.name),
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
                    let label = b.s("block").into();
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
        let span_first = first.extra.get_span().clone();
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

        println!("names: {:?}", self.names);
        let block_index = self.names.get(label).unwrap();
        let block = env.blocks.g.node_weight(*block_index).unwrap();
        let mut children = vec![];
        // skip the first child which is a label, it's redundant now that we have a block
        let params = block.params.clone();
        for expr in exprs.into_iter() {
            let (ir, _ty) = expr.lower_ir_expr(env, place, d, b)?;
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
            Ast::Label(ref _name, ref params) => {
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
    ) -> Result<Vec<IRBlock>> {
        let mut s = Self::new();
        for expr in exprs {
            s.add(expr, env, place, scope, d, b)?;
        }
        let exprs = s.exprs.drain(..).collect::<Vec<_>>();
        for expr in exprs {
            s.visit(expr, place, env, d, b);
        }
        Ok(s.blocks)
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

    /*
    pub fn run<E: Extra>(
        index: NodeIndex,
        name: StringKey,
        ir: IRNode,
        places: &mut IRPlaceTable,
        //env: &mut IREnvironment,
        blocks: &mut BlockTable,
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) -> IRNode {
        let mut s = Self::new();
        let ir = match ir.kind {
            IRKind::Seq(exprs) => {
                unreachable!();
                let label = blocks.fresh_block_label("module", b);
                //let index = blocks.add_block(places, label, vec![], d);
                let index = NodeIndex::new(0);
                //let module = b.s("module");
                let mut block = IRBlock::new(index, label, vec![], exprs);
                //let block_index = blocks.add_block(places, label, vec![], d);
                let block_index = NodeIndex::new(0);
                block
                    .children
                    .insert(0, b.ir_label(label, block_index, vec![]));
                IRNode::new(IRKind::Block(block), b.extra().get_span())
            }
            IRKind::Block(ref _block) => ir,
            IRKind::Module(ref _block) => ir,
            _ => unreachable!("{:?}", ir),
        };

        s.sort(ir, places, blocks, d, b);
        s.close_block(places, blocks, d, b);
        if s.blocks.len() == 1 {
            let block = s.blocks.pop().unwrap();
            //if let IRKind::Block(block) = block {
            //b.ir_block(block.label, block.index, vec![], block.children)
            b.ir_module(block.label, block.index, block.children)
            //} else {
            //unreachable!()
            //}
            //b.ir_module(index, name, blocks)//b.ir_seq(blocks)
        } else {
            let blocks = s.blocks(b);

            //b.ir_module(name, index, blocks)//b.ir_seq(blocks)
            b.ir_block(name, index, vec![], blocks) //b.ir_seq(blocks)
        }
    }
    */

    pub fn sort_block<E: Extra>(
        //&mut self,
        block: IRBlock,
        places: &mut IRPlaceTable,
        blocks: &mut BlockTable,
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) -> Vec<IRBlock> {
        let mut s = Self::new();
        for c in block.children {
            s.sort(c, places, blocks, d, b);
        }
        s.close_block(places, blocks, d, b);
        s.blocks
        //for block in s.blocks {
        //self.blocks.push(block);
        //}
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
            IRKind::Block(nb) | IRKind::Module(nb) => {
                self.blocks
                    .extend(Self::sort_block(nb, places, blocks, d, b));
            }
            IRKind::Branch(_, x, y) => {
                self.stack.push(ir);
                self.close_block(places, blocks, d, b);
            }
            IRKind::Jump(_, _) => {
                self.stack.push(ir);
                self.close_block(places, blocks, d, b);
            }
            IRKind::Label(_, _, _) => {
                self.close_block(places, blocks, d, b);
                self.stack.push(ir);
            }
            IRKind::Noop => (),
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
            for s in &self.stack {
                s.dump(places, b, 0);
            }
            unreachable!("{:?}", first);
            //assert!(false);
            //let offset = self.blocks.len();
            let label = b.labels.fresh_block_id();
            //let label = b.strings.intern(format!("_block{}", offset));
            println!("A: addblock");
            let block_index = blocks.add_block(places, label, vec![], d);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::SimpleExtra;
    use crate::tests::gen_block;
    use crate::{Diagnostics, NodeBuilder};
    use test_log::test;

    //#[test]
    fn test_ir_sort_1() {
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let mut b: NodeBuilder<SimpleExtra> = NodeBuilder::new();
        b.enter(file_id, "type.py");
        let module_key = b.s("module");
        let mut env = IREnvironment::new(); //module_key);
        let mut place = IRPlaceTable::new();
        let ast = gen_block(&mut b).normalize(&mut d, &mut b);
        let label = env.blocks.fresh_block_label("module", &mut b);
        let index = env.blocks.add_block(&mut place, label, vec![], &d);
        env.enter_block(index, ast.extra.get_span());
        let mut scope = BlockScope::default();
        let test1 = b.s("test1").into();
        let test2 = b.s("test2").into();
        let seq = vec![
            b.label(test1, vec![]),
            b.goto(test2, vec![]),
            b.label(test2, vec![]),
            b.ret(None),
        ];

        let blocks = AstBlockTransform::run(seq, &mut env, &mut place, &mut scope, &mut d, &mut b);
        println!("blocks: {:?}", blocks);
    }
}
