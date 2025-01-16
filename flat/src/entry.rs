use crate::{BlockId, LCode, LinkId, ValueId, VarDefinitionSpace};
use compile_core::{AstType, SpanId, StringKey};

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
