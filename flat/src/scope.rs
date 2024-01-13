use std::collections::{HashMap, HashSet};

use lower::{AstType, Extra, NodeBuilder, StringKey, StringLabel};

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct ValueId(pub(crate) u32);

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct BlockId(pub(crate) u32);

#[derive(Debug, Clone)]
pub struct Data {
    pub(crate) ty: AstType,
    pub(crate) value_id: ValueId,
}

impl Data {
    pub fn new(value_id: ValueId, ty: AstType) -> Self {
        Data { value_id, ty }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct ScopeId(pub(crate) u32);
impl std::fmt::Display for ScopeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug)]
pub struct ScopeLayer {
    //parent_id: ScopeId,
    names: HashMap<StringKey, Data>,
    pub(crate) labels: HashMap<StringLabel, ValueId>,
    pub(crate) last_value: Option<ValueId>,
    pub(crate) succ: HashSet<ValueId>,
    pub(crate) pred: HashSet<ValueId>,
    pub(crate) return_block: Option<ValueId>,
}

impl ScopeLayer {
    pub fn new() -> Self {
        Self {
            labels: HashMap::new(),
            names: HashMap::new(),
            last_value: None,
            pred: HashSet::new(),
            succ: HashSet::new(),
            return_block: None,
        }
    }

    pub fn add_pred(&mut self, parent_id: ValueId) {
        self.pred.insert(parent_id);
    }
}

#[derive(Debug)]
pub struct Block {
    pub(crate) last_value: Option<ValueId>,
    pub(crate) succ: HashSet<ValueId>,
    pub(crate) pred: HashSet<ValueId>,
}

impl Block {
    pub fn new() -> Self {
        Self {
            last_value: None,
            pred: HashSet::new(),
            succ: HashSet::new(),
        }
    }

    pub fn add_pred(&mut self, parent_id: ValueId) {
        self.pred.insert(parent_id);
    }

    pub fn add_succ(&mut self, succ_block_id: ValueId) {
        self.pred.insert(succ_block_id);
    }
}

#[derive(Debug)]
pub struct Environment {
    pub(crate) stack: Vec<ScopeId>,
    pub(crate) scopes: Vec<ScopeLayer>,
    pub(crate) blocks: Vec<Block>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            stack: vec![],
            scopes: vec![],
            blocks: vec![],
        }
    }

    pub fn new_scope(&mut self) -> ScopeId {
        let offset = self.scopes.len();
        let scope = ScopeLayer::new();
        self.scopes.push(scope);
        ScopeId(offset as u32)
    }

    pub fn new_block(&mut self) -> BlockId {
        let offset = self.blocks.len();
        let block = Block::new();
        self.blocks.push(block);
        BlockId(offset as u32)
    }

    pub fn enter_scope(&mut self, scope_id: ScopeId) {
        self.stack.push(scope_id);
    }

    pub fn exit_scope(&mut self) {
        self.stack.pop().unwrap();
    }

    pub fn scope_define(
        &mut self,
        scope_id: ScopeId,
        name: StringKey,
        value_id: ValueId,
        ty: AstType,
    ) {
        let data = Data::new(value_id, ty);
        self.scopes
            .get_mut(scope_id.0 as usize)
            .unwrap()
            .names
            .insert(name, data);
    }

    pub fn define(&mut self, name: StringKey, value_id: ValueId, ty: AstType) {
        let scope_id = self.current_scope().unwrap();
        self.scope_define(scope_id, name, value_id, ty);
    }

    pub fn get_scope(&self, scope_id: ScopeId) -> &ScopeLayer {
        self.scopes.get(scope_id.0 as usize).unwrap()
    }

    pub fn get_scope_mut(&mut self, scope_id: ScopeId) -> &mut ScopeLayer {
        self.scopes.get_mut(scope_id.0 as usize).unwrap()
    }

    pub fn get_block(&self, block_id: BlockId) -> &Block {
        self.blocks.get(block_id.0 as usize).unwrap()
    }

    pub fn get_block_mut(&mut self, block_id: BlockId) -> &mut Block {
        self.blocks.get_mut(block_id.0 as usize).unwrap()
    }

    pub fn add_pred(&mut self, block_id: BlockId, pred: ValueId) {
        self.get_block_mut(block_id).pred.insert(pred);
    }

    pub fn add_succ(&mut self, block_id: BlockId, succ: ValueId) {
        self.get_block_mut(block_id).succ.insert(succ);
    }

    pub fn resolve_return_block(&self) -> Option<ValueId> {
        for scope_id in self.stack.iter().rev() {
            let scope = self.get_scope(*scope_id);
            if let Some(value_id) = scope.return_block {
                return Some(value_id);
            }
        }
        None
    }

    pub fn resolve_block(&self, name: StringLabel) -> Option<ValueId> {
        for scope_id in self.stack.iter().rev() {
            let scope = self.get_scope(*scope_id);
            if let Some(value_id) = scope.labels.get(&name) {
                return Some(*value_id);
            }
        }
        None
    }

    pub fn resolve(&self, name: StringKey) -> Option<&Data> {
        // resolve scope through the tree, starting at the current scope
        for scope_id in self.stack.iter().rev() {
            let scope = self.get_scope(*scope_id);
            if let Some(data) = scope.names.get(&name) {
                return Some(data);
            }
        }
        None
    }

    pub fn dump<E: Extra>(&self, b: &NodeBuilder<E>) {
        for (index, block) in self.blocks.iter().enumerate() {
            println!("block({:?}, {:?})", index, block);
        }
        for (index, layer) in self.scopes.iter().enumerate() {
            println!("scope({})", index);
            for (key, data) in layer.names.iter() {
                println!("  name  {} = {:?}", b.r(*key), data);
            }
            for (key, data) in layer.labels.iter() {
                println!("  label {} = {:?}", b.resolve_label(*key), data);
            }
        }
    }

    pub fn current_scope(&self) -> Option<ScopeId> {
        self.stack.last().cloned()
    }
}
