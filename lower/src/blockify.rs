use anyhow::Result;

use crate::{Ast, AstNode, Definition, Extra, StringKey};

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
pub struct Blockify<E> {
    nodes: Vec<AstNode<E>>,
    pending_blocks: Vec<AstBlock>,
    loop_stack: Vec<LoopLayer>,
}

impl<E: Extra> Blockify<E> {
    pub fn new() -> Self {
        Self {
            nodes: vec![],
            pending_blocks: vec![],
            loop_stack: vec![],
        }
    }

    fn add(&mut self, node: AstNode<E>) -> Result<()> {
        Ok(())
    }

    pub fn build(&mut self, node: AstNode<E>) -> Result<()> {
        for n in node.to_vec() {
            self.add(n)?;
        }
        Ok(())
    }
}

impl<E: Extra> Definition<E> {
    fn blockify(mut self) -> Result<()> {
        if let Some(ref _body) = self.body {
            let mut blockify = Blockify::new();
            blockify.build(*self.body.take().unwrap())
        } else {
            Ok(())
        }
    }
}

impl<E: Extra> AstNode<E> {
    pub fn is_term_recursive(&self) -> bool {
        false
    }

    pub fn blockify(self) -> Result<()> {
        match self.node {
            Ast::Module(block) => {
                for c in block.children.into_iter() {
                    c.blockify()?
                }
                Ok(())
            }

            Ast::Definition(def) => def.blockify(),

            _ => Ok(()),
        }
    }
}
