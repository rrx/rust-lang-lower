use crate::TypeId;
use crate::{InternKey, InternPool, InternValue};

#[derive(Debug, Clone, Copy)]
pub struct BuiltinId(u32);

#[derive(Debug, Eq, PartialEq, Hash)]
pub struct Builtin {
    pub name: String,
    pub ty: TypeId,
}

impl Builtin {
    pub fn new(name: String, ty: TypeId) -> Self {
        Self { name, ty }
    }
}

impl InternValue for Builtin {}

impl InternKey for BuiltinId {
    fn index(&self) -> usize {
        self.0 as usize
    }
    fn new(index: usize) -> Self {
        Self(index as u32)
    }
}

pub type BuiltinPool = InternPool<BuiltinId, Builtin>;
