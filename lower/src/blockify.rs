use anyhow::Result;

use crate::{
    Ast, AstNode, BinaryOperation, Definition, Extra, NodeBuilder, ParameterNode, PlaceId,
    StringKey, StringLabel, UnaryOperation,
};

#[derive(Debug)]
pub enum BlockId {
    Name(StringKey),
    // unique
    U(usize),
}

#[derive(Debug)]
pub struct AstBlock {
    name: BlockId,
}

#[derive(Debug)]
pub struct LoopLayer {
    next: BlockId,
    restart: BlockId,
}

#[derive(Debug)]
pub struct ValueId(u32);

#[derive(Debug)]
pub enum LCode {
    Label(BlockId, u8, u8), // BlockId, number of positional arguments, number of named arguments
    NamedArg(StringKey),
    Op1(UnaryOperation, ValueId),
    Op2(BinaryOperation, ValueId, ValueId),
    Load(PlaceId),
    Store(PlaceId, ValueId),
    Jump(BlockId),
    Branch(ValueId, BlockId, BlockId),
}

#[derive(Debug)]
pub struct Blockify {
    code: Vec<LCode>,
    pending_blocks: Vec<AstBlock>,
    loop_stack: Vec<LoopLayer>,
}

impl Blockify {
    pub fn new() -> Self {
        Self {
            code: vec![],
            pending_blocks: vec![],
            loop_stack: vec![],
        }
    }

    pub fn build_block<E: Extra>(
        &mut self,
        node: AstNode<E>,
        name: StringLabel,
        params: Vec<ParameterNode<E>>,
        b: &mut NodeBuilder<E>,
    ) -> Result<()> {
        let seq = node.to_vec();
        if !seq.first().unwrap().node.is_label() {
            //self.add(b.label(name, params))?;
        }
        for n in seq {
            //self.add(n)?;
        }
        Ok(())
    }
}

impl<E: Extra> Definition<E> {
    fn flatten(self, b: &mut NodeBuilder<E>) -> Result<()> {
        //let code = LCode::Label();
        Ok(())
    }
}

impl<E: Extra> Definition<E> {
    fn blockify(mut self, b: &mut NodeBuilder<E>) -> Result<Self> {
        if let Some(ref _body) = self.body {
            let mut blockify = Blockify::new();
            blockify.build_block(
                *self.body.take().unwrap(),
                self.name.into(),
                self.params.clone(),
                b,
            )?;
            Ok(self)
        } else {
            Ok(self)
        }
    }
}

impl<E: Extra> AstNode<E> {
    pub fn is_term_recursive(&self) -> bool {
        false
    }

    pub fn blockify(self, b: &mut NodeBuilder<E>) -> Result<Self> {
        match self.node {
            Ast::Module(mut block) => {
                let mut seq = vec![];
                for c in block.children.into_iter() {
                    seq.push(c.blockify(b)?);
                }
                block.children = seq;
                Ok(b.module(block.name, b.node(Ast::Module(block))))
            }

            Ast::Definition(def) => {
                let def = def.blockify(b)?;
                Ok(b.node(Ast::Definition(def)))
            }

            _ => Ok(self),
        }
    }
}
