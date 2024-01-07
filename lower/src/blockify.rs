use anyhow::Result;

use crate::{
    Ast,
    AstNode,
    BinaryOperation,
    Definition,
    Extra,
    Literal,
    NodeBuilder,
    ParameterNode,
    PlaceId,
    StringKey,
    //StringLabel,
    UnaryOperation,
};

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum BlockId {
    Name(StringKey),
    // unique
    U(usize),
}

impl From<StringKey> for BlockId {
    fn from(item: StringKey) -> BlockId {
        BlockId::Name(item)
    }
}

impl From<&StringKey> for BlockId {
    fn from(item: &StringKey) -> BlockId {
        BlockId::Name(*item)
    }
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
    Const(Literal),
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

    pub fn push_code(&mut self, code: LCode) -> ValueId {
        let offset = self.code.len();
        self.code.push(code);
        ValueId(offset as u32)
    }

    pub fn add<E: Extra>(&mut self, node: AstNode<E>) -> Result<ValueId> {
        match node.node {
            Ast::Literal(lit) => Ok(self.push_code(LCode::Const(lit))),

            //Ast::Identifier(label) => {
            //}
            Ast::UnaryOp(op, x) => {
                let vx = self.add(*x)?;
                let code = LCode::Op1(op, vx);
                Ok(self.push_code(code))
            }

            Ast::BinaryOp(op, x, y) => {
                let vx = self.add(*x)?;
                let vy = self.add(*y)?;
                let code = LCode::Op2(op.node, vx, vy);
                Ok(self.push_code(code))
            }
            _ => unimplemented!(),
        }
    }

    pub fn build_block<E: Extra>(
        &mut self,
        node: AstNode<E>,
        name: StringKey,
        params: Vec<ParameterNode<E>>,
        b: &mut NodeBuilder<E>,
    ) -> Result<()> {
        let seq = node.to_vec();
        if !seq.first().unwrap().node.is_label() {
            self.code
                .push(LCode::Label(name.into(), 0, params.len() as u8));
            for p in params {
                self.code.push(LCode::NamedArg(p.name));
            }
        }
        for n in seq {
            self.add(n)?;
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
