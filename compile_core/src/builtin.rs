use crate::{InternKey, InternPool, InternValue};

#[derive(Debug, Clone, Copy)]
pub struct BuiltinId(u32);

/*
impl InternValue for Builtin {}

impl InternKey for BuiltinId {
    fn index(&self) -> usize {
        self.0 as usize
    }
    fn new(index: usize) -> Self {
        Self(index as u32)
    }
}

pub type TypePool = InternPool<BuiltinId, Builtin>;
*/
