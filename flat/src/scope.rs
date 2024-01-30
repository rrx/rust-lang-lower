use indexmap::IndexMap;
use std::collections::{HashMap, HashSet};

use lower::{AstType, Extra, NodeBuilder, StringKey, StringLabel, VarDefinitionSpace};

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct ValueId(pub(crate) u32);

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct BlockId(pub(crate) u32);

#[derive(Debug, Clone)]
pub struct Data {
    pub(crate) ty: AstType,
    pub(crate) mem: VarDefinitionSpace,
    pub(crate) value_id: ValueId,
}

impl Data {
    pub fn new(value_id: ValueId, ty: AstType, mem: VarDefinitionSpace) -> Self {
        Data { value_id, ty, mem }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ScopeType {
    Static,
    Function,
    Block,
    Loop,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct ScopeId(pub(crate) u32);
impl std::fmt::Display for ScopeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct LoopScope {
    name: Option<StringKey>,
    next_block: ValueId,
    start_block: ValueId,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct TemplateId(pub(crate) u32);

#[derive(Debug)]
pub struct ScopeLayer<E> {
    names: HashMap<StringKey, Data>,
    pub(crate) labels: HashMap<StringLabel, ValueId>,
    pub(crate) blocks: Vec<ValueId>,
    pub(crate) return_block: Option<ValueId>,
    pub(crate) next_block: Vec<ValueId>,
    pub(crate) entry_block: Option<ValueId>,
    pub(crate) loop_block: Option<LoopScope>,
    pub(crate) scope_type: ScopeType,
    pub(crate) lambdas: HashMap<StringLabel, TemplateId>,
    _e: std::marker::PhantomData<E>,
}

impl<E> ScopeLayer<E> {
    pub fn new(scope_type: ScopeType) -> Self {
        Self {
            labels: HashMap::new(),
            blocks: vec![],
            names: HashMap::new(),
            return_block: None,
            next_block: vec![],
            entry_block: None,
            loop_block: None,
            scope_type,
            lambdas: HashMap::new(),
            _e: std::marker::PhantomData::default(),
        }
    }

    pub fn lookup(&self, name: StringKey) -> Option<ValueId> {
        self.names.get(&name).cloned().map(|data| data.value_id)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Successor {
    BlockScope,
    Operation,
    FunctionDeclaration,
}

#[derive(Debug)]
pub struct Block {
    pub(crate) count: usize,
    pub(crate) last_value: Option<ValueId>,
    pub(crate) terminator: Option<ValueId>,
    pub(crate) succ: HashSet<(Successor, ValueId)>,
    pub(crate) pred: HashSet<ValueId>,
}

impl Block {
    pub fn new() -> Self {
        Self {
            count: 0,
            last_value: None,
            terminator: None,
            pred: HashSet::new(),
            succ: HashSet::new(),
        }
    }

    pub fn has_term(&self) -> bool {
        self.terminator.is_some()
    }

    pub fn set_term(&mut self, value_id: ValueId) {
        self.terminator = Some(value_id);
    }

    pub fn add_pred(&mut self, parent_id: ValueId) {
        self.pred.insert(parent_id);
    }

    pub fn add_succ(&mut self, succ_block_id: ValueId) {
        self.pred.insert(succ_block_id);
    }
}

#[derive(Debug)]
pub struct Environment<E> {
    pub(crate) stack: Vec<ScopeId>,
    pub(crate) scopes: Vec<ScopeLayer<E>>,
    pub(crate) blocks: IndexMap<ValueId, Block>,
    _e: std::marker::PhantomData<E>,
}

impl<E: Extra> Environment<E> {
    pub fn new() -> Self {
        Self {
            stack: vec![],
            scopes: vec![],
            blocks: IndexMap::new(),
            _e: std::marker::PhantomData::default(),
        }
    }

    pub fn new_scope(&mut self, scope_type: ScopeType) -> ScopeId {
        let offset = self.scopes.len();
        let scope = ScopeLayer::new(scope_type);
        self.scopes.push(scope);
        ScopeId(offset as u32)
    }

    pub fn new_block(&mut self, value_id: ValueId, scope_id: ScopeId) {
        let scope = self.get_scope_mut(scope_id);
        scope.blocks.push(value_id);
        let block = Block::new();
        self.blocks.insert(value_id, block);
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
        mem: VarDefinitionSpace,
    ) {
        let data = Data::new(value_id, ty, mem);
        self.scopes
            .get_mut(scope_id.0 as usize)
            .unwrap()
            .names
            .insert(name, data);
    }

    pub fn define(
        &mut self,
        name: StringKey,
        value_id: ValueId,
        ty: AstType,
        mem: VarDefinitionSpace,
    ) {
        let scope_id = self.current_scope().unwrap();
        self.scope_define(scope_id, name, value_id, ty, mem);
    }

    pub fn static_scope_id(&self) -> ScopeId {
        self.stack.get(0).unwrap().clone()
    }

    pub fn static_block_id(&self) -> ValueId {
        let scope_id = self.stack.get(0).unwrap().clone();
        let scope = self.get_scope(scope_id);
        scope.blocks.get(0).unwrap().clone()
    }

    pub fn get_scope(&self, scope_id: ScopeId) -> &ScopeLayer<E> {
        self.scopes.get(scope_id.0 as usize).unwrap()
    }

    pub fn get_scope_mut(&mut self, scope_id: ScopeId) -> &mut ScopeLayer<E> {
        self.scopes.get_mut(scope_id.0 as usize).unwrap()
    }

    pub fn get_block(&self, block_id: ValueId) -> &Block {
        self.blocks.get(&block_id).unwrap()
    }

    pub fn get_block_mut(&mut self, block_id: ValueId) -> &mut Block {
        self.blocks.get_mut(&block_id).unwrap()
    }

    pub fn add_pred(&mut self, block_id: ValueId, pred: ValueId) {
        self.get_block_mut(block_id).pred.insert(pred);
    }

    pub fn add_succ_op(&mut self, block_id: ValueId, succ: ValueId) {
        self.get_block_mut(block_id)
            .succ
            .insert((Successor::Operation, succ));
    }

    pub fn add_succ_block(&mut self, block_id: ValueId, succ: ValueId) {
        self.get_block_mut(block_id)
            .succ
            .insert((Successor::BlockScope, succ));
    }

    pub fn add_succ_static(&mut self, block_id: ValueId, succ: ValueId) {
        self.get_block_mut(block_id)
            .succ
            .insert((Successor::FunctionDeclaration, succ));
    }

    pub fn add_succ(&mut self, block_id: ValueId, succ: ValueId, successor_type: Successor) {
        self.get_block_mut(block_id)
            .succ
            .insert((successor_type, succ));
    }

    pub fn push_next_block(&mut self, next_id: ValueId) {
        let scope_id = self.current_scope().unwrap();
        let scope = self.get_scope_mut(scope_id);
        scope.next_block.push(next_id);
    }

    pub fn pop_next_block(&mut self) -> Option<ValueId> {
        let scope_id = self.current_scope().unwrap();
        let scope = self.get_scope_mut(scope_id);
        scope.next_block.pop()
    }

    pub fn get_next_block(&self) -> Option<ValueId> {
        let scope_id = self.current_scope().unwrap();
        let scope = self.get_scope(scope_id);
        scope.next_block.last().cloned()
        /*
        for scope_id in self.stack.iter().rev() {
            let scope = self.get_scope(*scope_id);
            if let Some(value_id) = scope.next_block.last().cloned() {
                return Some(value_id);
            }
        }
        */
        //None
    }

    pub fn push_loop_blocks(
        &mut self,
        maybe_name: Option<StringKey>,
        next_id: ValueId,
        restart_id: ValueId,
    ) {
        let scope_id = self.current_scope().unwrap();
        let scope = self.get_scope_mut(scope_id);
        let loop_scope = LoopScope {
            name: maybe_name,
            next_block: next_id,
            start_block: restart_id,
        };
        scope.loop_block = Some(loop_scope);
    }

    pub fn get_loop_scope(&self, maybe_name: Option<StringKey>) -> Option<LoopScope> {
        for scope_id in self.stack.iter().rev() {
            let scope = self.get_scope(*scope_id);
            if let Some(loop_scope) = scope.loop_block {
                if maybe_name.is_none() || loop_scope.name == maybe_name {
                    return Some(loop_scope);
                }
            }
        }
        None
    }

    pub fn get_loop_next_block(&self, maybe_name: Option<StringKey>) -> Option<ValueId> {
        if let Some(loop_scope) = self.get_loop_scope(maybe_name) {
            return Some(loop_scope.next_block);
        }
        None
    }

    pub fn get_loop_start_block(&self, maybe_name: Option<StringKey>) -> Option<ValueId> {
        if let Some(loop_scope) = self.get_loop_scope(maybe_name) {
            return Some(loop_scope.start_block);
        }
        None
    }

    pub fn resolve_static_block(&self) -> Option<ValueId> {
        for scope_id in self.stack.iter().rev() {
            let scope = self.get_scope(*scope_id);
            if scope.scope_type == ScopeType::Static {
                return scope.blocks.get(0).cloned();
            }
        }
        None
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

    pub fn resolve_lambda_scope(&self, name: StringLabel) -> Option<ScopeId> {
        // resolve scope through the tree, starting at the current scope
        for scope_id in self.stack.iter().rev() {
            let scope = self.get_scope(*scope_id);
            if let Some(_data) = scope.lambdas.get(&name) {
                return Some(*scope_id);
            }
        }
        None
    }

    pub fn dump(&self, b: &NodeBuilder<E>) {
        println!("current scope: {:?}", self.current_scope());
        //println!("static block: {:?}", self.static_block_id());
        //println!("static scope: {:?}", self.static_scope_id());
        for (block_id, block) in self.blocks.iter() {
            println!("block({:?}, {:?})", block_id, block);
        }

        for (index, layer) in self.scopes.iter().enumerate() {
            println!("scope({},{:?})", index, layer.scope_type);
            for (key, data) in layer.names.iter() {
                println!("  name  {} = {:?}", b.r(*key), data);
            }
            for (key, data) in layer.labels.iter() {
                println!("  label {} = {:?}", b.resolve_label(*key), data);
            }
            for next_id in layer.next_block.iter() {
                println!("  next  {:?}", next_id);
            }
            for block_id in layer.blocks.iter() {
                println!("  block {:?}", block_id);
            }
            for (name, def) in layer.lambdas.iter() {
                println!("  def {:?}", (b.resolve_label(*name), def));
            }
        }
    }

    pub fn current_scope(&self) -> Option<ScopeId> {
        self.stack.last().cloned()
    }
}
