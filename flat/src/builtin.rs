use compile_core::{AstType, BuiltinId, BuiltinPool};
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum Builtin {
    Assert,
    Print,
    Import,
}

pub fn builtin_from_name(name: &str) -> Option<Builtin> {
    if name == "check" {
        Some(Builtin::Assert)
    } else if name == "print" {
        Some(Builtin::Print)
    } else if name == "use" {
        Some(Builtin::Import)
    } else {
        None
    }
}

impl Builtin {
    pub fn arity(&self) -> usize {
        match self {
            Self::Assert => 1,
            Self::Print => 1,
            Self::Import => 1,
        }
    }

    pub fn get_return_type(&self) -> AstType {
        AstType::Unit
    }
}

pub struct BuiltinBuilder {
    pub pool: BuiltinPool,
    lookup: HashMap<String, BuiltinId>,
}

impl BuiltinBuilder {
    pub fn new() -> Self {
        let s = Self {
            pool: BuiltinPool::new(),
            lookup: HashMap::new(),
        };
        s
    }

    pub fn insert(&mut self, bi: compile_core::Builtin) {
        let name = bi.name.clone();
        let id = self.pool.intern(bi);
        self.lookup.insert(name, id);
    }

    pub fn get_enum(&self, id: BuiltinId) -> Builtin {
        let b = self.pool.resolve(&id);
        builtin_from_name(&b.name).unwrap()
    }

    pub fn get_id(&self, b: Builtin) -> BuiltinId {
        let name = match b {
            Builtin::Assert => "check",
            Builtin::Print => "print",
            Builtin::Import => "use",
        };
        self.lookup.get(name).unwrap().clone()
    }
}
