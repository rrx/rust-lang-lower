use indexmap::IndexMap;
use std::collections::{HashMap, HashSet};

use crate::{BlockId, CodeOffset, StringLabel, ValueId};
use compile_core::{AstType, StringKey, VarDefinitionSpace};

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

impl ScopeId {
    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy)]
pub struct LoopScope {
    pub(crate) name: Option<StringKey>,
    pub(crate) next_block: CodeOffset,
    pub(crate) start_block: CodeOffset,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct TemplateId(pub(crate) u32);
impl TemplateId {
    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug)]
pub struct ScopeLayer {
    pub names: HashMap<StringKey, Data>,
    pub labels: HashMap<StringLabel, ValueId>,
    pub(crate) block_labels: HashMap<StringLabel, BlockId>,
    pub blocks: Vec<ValueId>,
    pub return_block: Option<BlockId>,
    pub next_block: Vec<ValueId>,
    pub(crate) entry_block: Option<BlockId>,
    pub(crate) loop_block: Option<LoopScope>,
    pub scope_type: ScopeType,
    pub lambdas: HashMap<StringLabel, TemplateId>,
}

impl ScopeLayer {
    pub fn new(scope_type: ScopeType) -> Self {
        Self {
            labels: HashMap::new(),
            block_labels: HashMap::new(),
            blocks: vec![],
            names: HashMap::new(),
            return_block: None,
            next_block: vec![],
            entry_block: None,
            loop_block: None,
            scope_type,
            lambdas: HashMap::new(),
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
    pub entry_id: Option<ValueId>,
    pub(crate) last_value: Option<ValueId>,
    pub(crate) terminator: Option<ValueId>,
    pub succ: HashSet<(Successor, CodeOffset)>,
    pub pred: HashSet<ValueId>,
}

impl Block {
    pub fn new() -> Self {
        Self {
            count: 0,
            entry_id: None,
            last_value: None,
            terminator: None,
            pred: HashSet::new(),
            succ: HashSet::new(),
        }
    }

    pub fn has_term(&self) -> bool {
        self.terminator.is_some()
    }

    pub fn set_entry(&mut self, value_id: ValueId) {
        self.entry_id = Some(value_id);
    }

    pub fn set_term(&mut self, value_id: ValueId) {
        self.terminator = Some(value_id);
    }

    pub fn add_pred(&mut self, parent_id: ValueId) {
        self.pred.insert(parent_id);
    }

    pub fn add_succ(&mut self, succ_entry_id: ValueId) {
        self.pred.insert(succ_entry_id);
    }
}

#[derive(Debug)]
pub struct Environment {
    pub(crate) stack: Vec<ScopeId>,
    pub scopes: Vec<ScopeLayer>,
    pub blocks: Vec<Block>,
    pub block_map: IndexMap<ValueId, BlockId>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            stack: vec![],
            scopes: vec![],
            blocks: vec![],
            block_map: IndexMap::new(),
        }
    }

    pub fn new_scope(&mut self, scope_type: ScopeType) -> ScopeId {
        let offset = self.scopes.len();
        let scope = ScopeLayer::new(scope_type);
        self.scopes.push(scope);
        ScopeId(offset as u32)
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

    pub fn static_entry_id(&self) -> CodeOffset {
        let scope_id = self.stack.get(0).unwrap().clone();
        let scope = self.get_scope(scope_id);
        scope.blocks.get(0).unwrap().clone().into()
    }

    pub fn get_scope(&self, scope_id: ScopeId) -> &ScopeLayer {
        self.scopes.get(scope_id.0 as usize).unwrap()
    }

    pub fn get_scope_mut(&mut self, scope_id: ScopeId) -> &mut ScopeLayer {
        self.scopes.get_mut(scope_id.0 as usize).unwrap()
    }

    pub fn new_block(&mut self) -> BlockId {
        let block = Block::new();
        let offset = self.blocks.len();
        self.blocks.push(block);
        BlockId(offset as u32)
    }

    pub fn block_entry(&mut self, block_id: BlockId, entry_id: ValueId) {
        self.blocks
            .get_mut(block_id.index())
            .unwrap()
            .set_entry(entry_id);
        self.block_map.insert(entry_id, block_id);
    }

    pub fn block_name(
        &mut self,
        scope_id: ScopeId,
        name: StringLabel,
        v: ValueId,
        block_id: BlockId,
    ) {
        self.get_scope_mut(scope_id).labels.insert(name, v);
        self.get_scope_mut(scope_id)
            .block_labels
            .insert(name, block_id);
    }

    pub fn get_block_by_block_id(&self, block_id: BlockId) -> &Block {
        self.blocks.get(block_id.index()).unwrap()
    }

    pub fn get_block_mut_by_block_id(&mut self, block_id: BlockId) -> &mut Block {
        self.blocks.get_mut(block_id.index()).unwrap()
    }

    pub fn get_block(&self, value_id: ValueId) -> &Block {
        let block_id = self.block_map.get(&value_id).unwrap();
        self.get_block_by_block_id(*block_id)
    }

    pub fn get_block_mut(&mut self, value_id: ValueId) -> &mut Block {
        let block_id = self.block_map.get(&value_id).unwrap();
        self.get_block_mut_by_block_id(*block_id)
    }

    pub fn resolve_code_offset(&self, code_offset: CodeOffset) -> ValueId {
        match code_offset {
            CodeOffset::Value(v) => v,
            CodeOffset::Block(block_id) => {
                let block = self.get_block_by_block_id(block_id);
                block.entry_id.unwrap()
            }
        }
    }

    pub fn add_pred(&mut self, block_id: ValueId, pred: ValueId) {
        self.get_block_mut(block_id).pred.insert(pred);
    }

    pub fn add_succ_op(&mut self, block_id: BlockId, succ: CodeOffset) {
        self.get_block_mut_by_block_id(block_id)
            .succ
            .insert((Successor::Operation, succ));
    }

    pub fn add_succ_block(&mut self, block_id: BlockId, succ: CodeOffset) {
        self.get_block_mut_by_block_id(block_id)
            .succ
            .insert((Successor::BlockScope, succ));
    }

    pub fn add_succ_static(&mut self, block_id: BlockId, succ: ValueId) {
        self.get_block_mut_by_block_id(block_id)
            .succ
            .insert((Successor::FunctionDeclaration, succ.into()));
    }

    pub fn add_succ(&mut self, block_id: BlockId, succ: CodeOffset, successor_type: Successor) {
        self.get_block_mut_by_block_id(block_id)
            .succ
            .insert((successor_type, succ));
    }

    pub fn push_loop_blocks(
        &mut self,
        maybe_name: Option<StringKey>,
        next_block: CodeOffset,
        start_block: CodeOffset,
    ) {
        let scope_id = self.current_scope().unwrap();
        let scope = self.get_scope_mut(scope_id);
        let loop_scope = LoopScope {
            name: maybe_name,
            next_block,
            start_block,
        };
        scope.loop_block = Some(loop_scope);
    }

    pub fn get_loop_scope(&self, maybe_name: Option<StringKey>) -> Option<LoopScope> {
        // move up the stack until we find a matching loop
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

    pub fn resolve_static_block(&self) -> Option<ValueId> {
        for scope_id in self.stack.iter().rev() {
            let scope = self.get_scope(*scope_id);
            if scope.scope_type == ScopeType::Static {
                return scope.blocks.get(0).cloned();
            }
        }
        None
    }

    pub fn resolve_return_block(&self) -> Option<BlockId> {
        // walk up the stack until we find the containing block, which has the return block
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

    pub fn resolve_block_id(&self, name: StringLabel) -> Option<BlockId> {
        for scope_id in self.stack.iter().rev() {
            let scope = self.get_scope(*scope_id);
            if let Some(block_id) = scope.block_labels.get(&name) {
                return Some(*block_id);
            }
        }
        None
    }

    pub fn resolve_name(&self, name: StringKey) -> Option<&Data> {
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

    pub fn current_scope(&self) -> Option<ScopeId> {
        self.stack.last().cloned()
    }
}
