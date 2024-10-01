use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;

use crate::{
    scope::LoopScope, BlockId, LinkId, NodeBuilder, ScopeId, ScopeLayer, ScopeType, StringLabel,
    VariantId,
};
use compile_core::{AstType, StringKey};
use std::ops::{Deref, DerefMut};

pub struct ScopeGraph(pub(super) DiGraph<ScopeLayer, ()>);

impl Deref for ScopeGraph {
    type Target = DiGraph<ScopeLayer, ()>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl DerefMut for ScopeGraph {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl ScopeGraph {
    pub fn new() -> Self {
        Self(DiGraph::new())
    }

    pub fn new_scope(&mut self, scope_type: ScopeType) -> ScopeId {
        let scope = ScopeLayer::new(scope_type);
        let index = self.add_node(scope);
        ScopeId(index.index() as u32)
    }

    pub fn get_scope(&self, scope_id: ScopeId) -> &ScopeLayer {
        let index = NodeIndex::new(scope_id.index());
        self.node_weight(index).unwrap()
    }

    pub fn get_scope_mut(&mut self, scope_id: ScopeId) -> &mut ScopeLayer {
        let index = NodeIndex::new(scope_id.index());
        self.node_weight_mut(index).unwrap()
    }

    pub fn scope_define(&mut self, scope_id: ScopeId, name: StringKey, v: LinkId) {
        let scope = self.get_scope_mut(scope_id);
        scope.names.insert(name, v);
    }

    pub fn scope_define_declaration(&mut self, scope_id: ScopeId, name: StringKey, v: LinkId) {
        let scope = self.get_scope_mut(scope_id);
        scope.declarations.insert(name, v);
    }

    pub fn scope_define_template(&mut self, scope_id: ScopeId, key: StringKey, link_id: LinkId) {
        let scope = self.get_scope_mut(scope_id);
        scope.templates.insert(key.into(), link_id);
    }

    pub fn scope_succ(&mut self, source_scope_id: ScopeId, target_scope_id: ScopeId) {
        self.add_edge(source_scope_id.into(), target_scope_id.into(), ());
    }

    pub fn find_nearest_scope(
        &self,
        scope_id: ScopeId,
        scope_types: &[ScopeType],
    ) -> Option<ScopeId> {
        for scope_id in self.walk_scopes(scope_id) {
            let scope = self.get_scope(scope_id);
            if scope_types.contains(&scope.scope_type) {
                return Some(scope_id);
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

    pub fn get_entry_block(&self, scope_id: ScopeId) -> BlockId {
        self.get_scope(scope_id).entry_block.unwrap()
    }

    pub fn push_loop_blocks(
        &mut self,
        scope_id: ScopeId,
        maybe_name: Option<StringKey>,
        next_block: BlockId,
        start_block: BlockId,
    ) {
        let scope = self.get_scope_mut(scope_id);
        let loop_scope = LoopScope {
            name: maybe_name,
            next_block,
            start_block,
        };
        scope.loop_block = Some(loop_scope);
    }

    pub fn get_loop_scope(
        &self,
        start_scope_id: ScopeId,
        maybe_name: Option<StringKey>,
    ) -> Option<LoopScope> {
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

    pub fn resolve_block_id(&self, start_scope_id: ScopeId, name: StringLabel) -> Option<BlockId> {
        for scope_id in self.walk_scopes(start_scope_id) {
            let scope = self.get_scope(scope_id);
            if let Some(block_id) = scope.block_labels.get(&name) {
                return Some(*block_id);
            }
        }
        None
    }

    pub fn variant_add(
        &mut self,
        scope_id: ScopeId,
        name: StringKey,
        ty: AstType,
        link_id: LinkId,
    ) -> VariantId {
        let scope = self.get_scope_mut(scope_id);
        scope.variant_add(name, ty, link_id)
    }

    pub fn variant_update(
        &mut self,
        scope_id: ScopeId,
        name: StringKey,
        variant_id: VariantId,
        ty: AstType,
        link_id: LinkId,
    ) {
        let scope = self.get_scope_mut(scope_id);
        scope.variant_update(name, variant_id, ty, link_id);
    }

    pub fn dump_scope(&self, scope_id: ScopeId, b: &NodeBuilder) {
        println!("DumpScope: {}, {:?}", scope_id, self.walk_scopes(scope_id));
        for scope_id in self.walk_scopes(scope_id) {
            let scope = self.get_scope(scope_id);
            scope.dump(b);
        }
    }

    pub fn scope_graph(&self, filename: &str) {
        use petgraph::dot::{Config, Dot};
        let s = format!(
            "{:?}",
            Dot::with_attr_getters(
                &self.0,
                &[Config::EdgeNoLabel, Config::NodeNoLabel],
                &|_, _er| String::new(),
                &|_, (index, scope)| {
                    format!(
                        //"label = \"S{}:{:?}\" shape=\"{:?}\"",
                        "label = \"S{}:{:?}\"",
                        index.index(),
                        &scope.scope_type,
                        //&scope.scope_type
                    )
                }
            )
        );
        println!("saved graph {:?}", filename);
        std::fs::write(filename, s).unwrap();
    }
}

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
    //pub scopes: ScopeGraph,
}

impl FlattenEnvironment {
    pub fn new(block_id: BlockId) -> Self {
        Self {
            //scopes: ScopeGraph::new(),
        }
    }
}
