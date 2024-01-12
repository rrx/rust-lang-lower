use std::collections::{HashMap, HashSet};

use lower::{AstType, Extra, NodeBuilder, StringKey};

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
    pub(crate) labels: HashMap<StringKey, ValueId>,
    pub(crate) last_value: Option<ValueId>,
    pub(crate) succ: HashSet<ScopeId>,
    pub(crate) pred: HashSet<ScopeId>,
}

impl ScopeLayer {
    pub fn new() -> Self {
        Self {
            //parent_id,
            labels: HashMap::new(),
            names: HashMap::new(),
            last_value: None,
            pred: HashSet::new(),
            succ: HashSet::new(),
        }
    }

    pub fn add_pred(&mut self, parent_id: ScopeId) {
        self.pred.insert(parent_id);
    }
}

#[derive(Debug)]
pub struct Block {
    pub(crate) last_value: Option<ValueId>,
    pub(crate) succ: HashSet<BlockId>,
    pub(crate) pred: HashSet<BlockId>,
}

impl Block {
    pub fn new() -> Self {
        Self {
            last_value: None,
            pred: HashSet::new(),
            succ: HashSet::new(),
        }
    }

    pub fn add_pred(&mut self, parent_id: BlockId) {
        self.pred.insert(parent_id);
    }

    pub fn add_succ(&mut self, succ_block_id: BlockId) {
        self.pred.insert(succ_block_id);
    }
}

#[derive(Debug)]
pub struct Environment {
    //pub(crate) static_scope: ScopeId,
    pub(crate) stack: Vec<ScopeId>,
    pub(crate) scopes: Vec<ScopeLayer>,
    pub(crate) blocks: Vec<Block>,
}

impl Environment {
    pub fn new() -> Self {
        //let scope = ScopeLayer::new();
        //let scope_id = ScopeId(0);
        Self {
            //static_scope: scope_id,
            stack: vec![],  //scope_id],
            scopes: vec![], //scope],
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

    pub fn dependent_scope(&mut self, parent_id: ScopeId) -> ScopeId {
        let scope_id = self.new_scope();
        //let offset = self.scopes.len();
        //let mut scope = ScopeLayer::new();
        self.add_pred(scope_id, parent_id);
        self.add_succ(parent_id, scope_id);
        scope_id
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

    pub fn add_pred(&mut self, scope_id: ScopeId, pred: ScopeId) {
        self.get_scope_mut(scope_id).pred.insert(pred);
    }

    pub fn add_succ(&mut self, scope_id: ScopeId, succ: ScopeId) {
        self.get_scope_mut(scope_id).succ.insert(succ);
    }

    pub fn resolve_block(&self, name: StringKey) -> Option<ValueId> {
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
        /*

        loop {
            let scope = self.get_scope(current_id);
            if let Some(data) = scope.names.get(&name) {
                return Some(data);
            }

            if scope.pred.contains(&current_id) {
                break;
            }
        }
        None
        */
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
                println!("  label {} = {:?}", b.r(*key), data);
            }
        }
    }

    /*
    pub fn root(&self) -> ScopeId {
        self.stack.first().unwrap().clone()
    }

    */
    /*
        pub fn previous_scope(&self) -> Option<ScopeId> {
            self.prev
        }
    */
    pub fn current_scope(&self) -> Option<ScopeId> {
        self.stack.last().cloned()
        //self.stack.last().unwrap().clone()
    }
}
