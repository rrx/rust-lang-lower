use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;

use crate::{
    scope::{Data, LoopScope}, BlockId, CodeOffset, NodeBuilder, ScopeId, ScopeLayer, ScopeType, StringLabel,
};
use compile_core::{AstType, StringKey, VarDefinitionSpace};

pub type ScopeGraph = DiGraph<ScopeLayer, ()>;

impl Into<NodeIndex> for ScopeId {
    fn into(self) -> NodeIndex {
        NodeIndex::new(self.index())
    }
}

impl From<NodeIndex> for ScopeId {
    fn from(item: NodeIndex) -> Self {
        Self(item.index() as u32)
    }
}

pub struct FlattenEnvironment {
    pub(crate) current_block: Option<BlockId>,
    pub(crate) static_block: Option<BlockId>,
    pub(crate) static_scope: Option<ScopeId>,
    pub(crate) scopes: ScopeGraph,
}

impl FlattenEnvironment {
    pub fn new() -> Self {
        Self {
            current_block: None,
            static_block: None,
            static_scope: None,
            scopes: ScopeGraph::new(),
        }
    }

    pub fn static_scope_id(&self) -> ScopeId {
        self.static_scope.unwrap()
    }

    pub fn static_block_id(&self) -> BlockId {
        self.static_block.unwrap()
    }

    pub fn new_scope(&mut self, scope_type: ScopeType) -> ScopeId {
        let scope = ScopeLayer::new(scope_type);
        let index = self.scopes.add_node(scope);
        ScopeId(index.index() as u32)
    }

    pub fn get_scope(&self, scope_id: ScopeId) -> &ScopeLayer {
        let index = NodeIndex::new(scope_id.index());
        self.scopes.node_weight(index).unwrap()
    }

    pub fn get_scope_mut(&mut self, scope_id: ScopeId) -> &mut ScopeLayer {
        let index = NodeIndex::new(scope_id.index());
        self.scopes.node_weight_mut(index).unwrap()
    }

    pub fn scope_succ(&mut self, source_scope_id: ScopeId, target_scope_id: ScopeId) {
        println!("succ: {}, {}", source_scope_id, target_scope_id);
        self.scopes
            .add_edge(source_scope_id.into(), target_scope_id.into(), ());
    }

    pub fn scope_define(
        &mut self,
        scope_id: ScopeId,
        name: StringKey,
        offset: CodeOffset,
        ty: AstType,
        mem: VarDefinitionSpace,
    ) {
        let data = Data::new(offset, ty, mem);
        let scope = self.get_scope_mut(scope_id);
        scope.names.insert(name, data);
    }

    pub fn find_nearest_scope(&self, scope_id: ScopeId, scope_type: ScopeType) -> Option<ScopeId> {
        for scope_id in self.walk_scopes(scope_id) {
            let scope = self.get_scope(scope_id);
            if scope.scope_type == scope_type {
                return Some(scope_id);
            }
        }
        None
    }

    pub fn push_loop_blocks(
        &mut self,
        scope_id: ScopeId,
        maybe_name: Option<StringKey>,
        next_block: CodeOffset,
        start_block: CodeOffset,
    ) {
        let scope = self.get_scope_mut(scope_id);
        let loop_scope = LoopScope {
            name: maybe_name,
            next_block,
            start_block,
        };
        scope.loop_block = Some(loop_scope);
    }

    pub fn get_loop_scope(&self, start_scope_id: ScopeId, maybe_name: Option<StringKey>) -> Option<LoopScope> {
        // move up the stack until we find a matching loop
        for scope_id in self.walk_scopes(start_scope_id) {
            let scope = self.get_scope(scope_id);
            if let Some(loop_scope) = scope.loop_block {
                if maybe_name.is_none() || loop_scope.name == maybe_name {
                    return Some(loop_scope);
                }
            }
        }
        None
    }


    pub fn walk_scopes(&self, scope_id: ScopeId) -> Vec<ScopeId> {
        let mut out = vec![];
        let mut current = scope_id;
        loop {
            out.push(current);
            let incoming = self
                .scopes
                .neighbors_directed(current.into(), petgraph::Direction::Incoming)
                .collect::<Vec<_>>();
            if incoming.len() == 0 {
                break;
            }
            assert_eq!(1, incoming.len());
            current = incoming.first().unwrap().clone().into();
        }
        out
    }

    pub fn resolve_block_id(&self, start_scope_id: ScopeId, name: StringLabel) -> Option<BlockId> {
        for scope_id in self.walk_scopes(start_scope_id) {
            let scope = self.get_scope(scope_id);
            if let Some(block_id) = scope.block_labels.get(&name) {
                return Some(*block_id);
            }
        }
        None
    }

    pub fn dump_scope(&self, scope_id: ScopeId, b: &NodeBuilder) {
        println!("DumpScope: {}, {:?}", scope_id, self.walk_scopes(scope_id));
        for scope_id in self.walk_scopes(scope_id) {
            let scope = self.get_scope(scope_id);
            scope.dump(b);
        }
    }

    /*
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
    */
}
