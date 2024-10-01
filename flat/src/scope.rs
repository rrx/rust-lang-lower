use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;

use std::ops::{Deref, DerefMut};

use std::collections::HashMap;

use crate::{BlockId, LinkId, NodeBuilder, StringLabel, ValueId};
use compile_core::{AstType, StringKey};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ScopeType {
    Static,
    Function,
    Template,
    Block,
    Region,
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
    pub(crate) next_block: BlockId,
    pub(crate) start_block: BlockId,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct TemplateId(pub(crate) u32);
impl TemplateId {
    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct VariantId(pub(crate) u32);
impl std::fmt::Display for VariantId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "V{}", self.0)
    }
}

impl VariantId {
    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug)]
pub struct FunctionVariant {
    pub ty: AstType,
    pub link_id: LinkId,
}

#[derive(Debug)]
pub struct FunctionVariantBuilder {
    pub variants: Vec<FunctionVariant>,
}

impl FunctionVariantBuilder {
    pub fn new() -> Self {
        Self { variants: vec![] }
    }

    pub fn add(&mut self, ty: AstType, link_id: LinkId) -> VariantId {
        let index = self.variants.len();
        self.variants.push(FunctionVariant { ty, link_id });
        VariantId(index as u32)
    }

    pub fn update_type(&mut self, variant_id: VariantId, ty: AstType) {
        let v = self.variants.get_mut(variant_id.index()).unwrap();
        v.ty = ty;
    }

    pub fn update(&mut self, variant_id: VariantId, ty: AstType, link_id: LinkId) {
        let v = self.variants.get_mut(variant_id.index()).unwrap();
        v.ty = ty;
        v.link_id = link_id;
    }
}

#[derive(Debug)]
pub struct ScopeLayer {
    pub names: HashMap<StringKey, LinkId>,
    pub entries: HashMap<StringKey, FunctionVariantBuilder>,
    pub declarations: HashMap<StringKey, LinkId>,
    pub labels: HashMap<StringLabel, ValueId>,
    pub(crate) block_labels: HashMap<StringLabel, BlockId>,
    pub blocks: Vec<ValueId>,
    pub entry_block: Option<BlockId>,
    pub return_block: Option<BlockId>,
    pub next_block: Vec<ValueId>,
    pub(crate) loop_block: Option<LoopScope>,
    pub scope_type: ScopeType,
    pub lambdas: HashMap<StringLabel, TemplateId>,
    pub templates: HashMap<StringKey, LinkId>,
}

impl ScopeLayer {
    pub fn new(scope_type: ScopeType) -> Self {
        Self {
            labels: HashMap::new(),
            block_labels: HashMap::new(),
            blocks: vec![],
            names: HashMap::new(),
            entries: HashMap::new(),
            declarations: HashMap::new(),
            entry_block: None,
            return_block: None,
            next_block: vec![],
            loop_block: None,
            scope_type,
            lambdas: HashMap::new(),
            templates: HashMap::new(),
        }
    }

    pub fn variant_add(&mut self, name: StringKey, ty: AstType, link_id: LinkId) -> VariantId {
        if !self.entries.contains_key(&name) {
            self.entries.insert(name, FunctionVariantBuilder::new());
        }
        let v = self.entries.get_mut(&name).unwrap();
        v.add(ty, link_id)
    }

    pub fn variant_update(
        &mut self,
        name: StringKey,
        variant_id: VariantId,
        ty: AstType,
        link_id: LinkId,
    ) {
        let v = self.entries.get_mut(&name).unwrap();
        v.update(variant_id, ty, link_id)
    }

    pub fn lookup(&self, name: StringKey) -> Option<LinkId> {
        self.names.get(&name).cloned()
    }

    pub fn dump(&self, b: &NodeBuilder) {
        println!("Scope: {:?}", self.scope_type);
        for (k, v) in self.labels.iter() {
            let s = b.labels.r(*k);
            println!("Label: {}:{:?}", s, v);
        }
        for (k, v) in self.entries.iter() {
            let name = b.labels.r((*k).into());
            for v in v.variants.iter() {
                println!("Entry: {}:{}:{}", name, v.ty, v.link_id);
            }
        }
    }
}

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
