use std::collections::HashMap;

use lower::{AstType, Extra, NodeBuilder, StringKey};

#[derive(Debug, Clone)]
pub struct Data {
    ty: AstType,
}

impl Data {
    pub fn new(ty: AstType) -> Self {
        Data { ty }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct ScopeId(u32);

#[derive(Debug)]
pub struct ScopeLayer {
    parent_id: ScopeId,
    names: HashMap<StringKey, Data>,
}

impl ScopeLayer {
    fn new(parent_id: ScopeId) -> Self {
        Self {
            parent_id,
            names: HashMap::new(),
        }
    }
}

#[derive(Debug)]
pub struct Environment {
    stack: Vec<ScopeId>,
    layers: Vec<ScopeLayer>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            stack: vec![],
            layers: vec![],
        }
    }

    pub fn dependent_scope(&mut self, parent_id: ScopeId) -> ScopeId {
        let offset = self.layers.len();
        self.layers.push(ScopeLayer::new(parent_id));
        let scope_id = ScopeId(offset as u32);
        self.stack.push(scope_id);
        scope_id
    }

    pub fn enter_scope(&mut self) -> ScopeId {
        let offset = self.layers.len();
        let parent_id = if offset == 0 {
            ScopeId(0)
        } else {
            *self.stack.last().unwrap()
        };
        self.dependent_scope(parent_id)
    }

    pub fn exit_scope(&mut self) {
        self.stack.pop().unwrap();
    }

    pub fn define(&mut self, scope_id: ScopeId, name: StringKey, ty: AstType) {
        let data = Data::new(ty);
        self.layers
            .get_mut(scope_id.0 as usize)
            .unwrap()
            .names
            .insert(name, data);
    }

    pub fn get_scope(&self, scope_id: ScopeId) -> &ScopeLayer {
        self.layers.get(scope_id.0 as usize).unwrap()
    }

    pub fn get_scope_mut(&mut self, scope_id: ScopeId) -> &mut ScopeLayer {
        self.layers.get_mut(scope_id.0 as usize).unwrap()
    }

    pub fn resolve(&self, scope_id: ScopeId, name: StringKey) -> Option<&Data> {
        let current_id = scope_id;
        loop {
            let scope = self.get_scope(current_id);
            if let Some(data) = scope.names.get(&name) {
                return Some(data);
            }

            if current_id == scope.parent_id {
                break;
            }
        }
        None
    }

    pub fn dump<E: Extra>(&self, b: &NodeBuilder<E>) {
        for (index, layer) in self.layers.iter().enumerate() {
            println!("Layer({})", index);
            for (key, data) in layer.names.iter() {
                println!("  {} = {:?}", b.r(*key), data);
            }
        }
    }

    pub fn root(&self) -> ScopeId {
        self.stack.first().unwrap().clone()
    }

    pub fn current_scope(&self) -> ScopeId {
        self.stack.last().unwrap().clone()
    }
}
