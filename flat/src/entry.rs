use crate::{BlockId, Builtin, CodeOffset, LinkId, UseIndex, ValueId, VarDefinitionSpace};
use compile_core::{
    AstType, BinaryOperation, Literal, NaryOperation, SpanId, StringKey, UnaryOperation,
};
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum LCode {
    EndModule,
    Label, // number of positional arguments, number of named arguments
    Noop,
    Declare,
    DeclareFunction(Option<BlockId>), // optional entry block
    Extern,                           // optional entry block
    //Value(LinkId),
    //ValueIndex(LinkId, u8), // index into a struct
    //
    CallValue(CodeOffset),
    Call(CodeOffset),

    Arg(u8), // get the value of a positional arg
    Val(Literal),
    Use(CodeOffset, Vec<UseIndex>),
    Tuple(Vec<LinkId>),
    Op1(UnaryOperation),
    Op2(BinaryOperation),
    NaryOp(NaryOperation),
    Load(LinkId),          // memref
    Store(LinkId, LinkId), // memref, value to store
    Return,                // return values
    Yield,                 // yield values

    // jump to block, with num args
    Jump(BlockId),
    Switch(LinkId, HashMap<usize, BlockId>),
    PlaceholderTerminal,
    PlaceholderCodeReference,

    Branch(CodeOffset, BlockId, BlockId),
    Ternary(CodeOffset, BlockId, BlockId), // condition, then_entry, else_entry
    Builtin(Builtin),
}

impl LCode {
    pub fn is_start(&self) -> bool {
        match self {
            Self::Label => true,
            _ => false,
        }
    }

    pub fn is_term(&self) -> bool {
        match self {
            Self::Jump(_) => true,
            Self::Switch(_, _) => true,
            Self::PlaceholderTerminal => true,
            Self::Branch(_, _, _) => true,
            Self::Return => true,
            Self::Yield => true,
            Self::EndModule => true,
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct CodeEntry {
    pub(super) code: LCode,
    pub name: Option<StringKey>,
    pub link: Option<LinkId>,
    pub value_id: Option<ValueId>,
    pub block_id: BlockId,
    pub ty: AstType,
    pub span_id: SpanId,
    pub mem: VarDefinitionSpace,
}

impl CodeEntry {
    pub fn new(
        block_id: BlockId,
        code: LCode,
        ty: AstType,
        name: Option<StringKey>,
        span_id: SpanId,
        mem: VarDefinitionSpace,
    ) -> Self {
        Self {
            block_id,
            code,
            name,
            value_id: None,
            link: None,
            ty,
            span_id,
            mem,
        }
    }

    pub fn is_load_required(&self) -> bool {
        match self.code {
            LCode::Val(_) => self.mem.is_static(),
            LCode::Declare => true,
            LCode::Arg(_) => false,
            LCode::Load(_) => false,
            LCode::Tuple(_) => false,
            LCode::NaryOp(_) => false,
            LCode::Op1(_) => false,
            LCode::Op2(_) => false,
            LCode::Call(_) => false,
            LCode::Use(_, _) => false,
            LCode::Label => false,
            LCode::Ternary(_, _, _) => false,
            // shouldn't happen
            LCode::DeclareFunction(_) => unimplemented!(),
            LCode::Extern => unimplemented!(),
            LCode::Store(_, _) => unreachable!(),
            LCode::Noop => unreachable!(),
            LCode::Return => unreachable!(),
            LCode::Yield => unreachable!(),
            LCode::Jump(_) => unreachable!(),
            LCode::Switch(_, _) => unreachable!(),
            LCode::PlaceholderTerminal => unreachable!(),
            LCode::PlaceholderCodeReference => false,
            LCode::Branch(_, _, _) => unreachable!(),
            LCode::Builtin(_) => unreachable!(),
            LCode::CallValue(_) => unreachable!(),
            LCode::EndModule => unreachable!(),
        }
    }

    pub fn add_mem(mut self, mem: VarDefinitionSpace) -> Self {
        self.mem = mem;
        self
    }

    pub fn dump(&self) {
        //let name = self.name.map(|key| b.labels.r(key.into())).unwrap_or("".to_string());
        println!(
            "[{}]{:?}, name:{:?}, ty:{}",
            self.block_id, self.code, self.name, self.ty
        );
    }
}
