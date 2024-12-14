use anyhow::Error;
use anyhow::Result;
use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use petgraph::visit::Bfs;

use std::ops::{Deref, DerefMut};

use std::collections::{HashMap, HashSet};

use crate::{ArgVec, BlockId, BlockifyError, LinkId, NodeBuilder, StringLabel, ValueId, VariantId};
use compile_core::{AbstractionId, Argument, Lambda, SpanId, StringKey};

#[derive(Debug)]
pub enum PlacedBlockId {
    Unclaimed(BlockId),
    Claimed(BlockId),
    ClaimedLambda(BlockId, ScopeId, Lambda, SpanId),
    UnclaimedLambda(ScopeId, Lambda, SpanId),
    Deferred(ScopeId, Lambda, SpanId, DeferredGoto),
    DeferredBlock(DeferredGoto),
    NotFound,
}

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
        write!(f, "S{}", self.index())
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

#[derive(Debug, Clone)]
pub enum DeferredType {
    Goto(LinkId),
    Variant(LinkId, BlockId, VariantId),
    Name(LinkId),
    Ident(LinkId),
}

#[derive(Debug, Clone)]
pub struct DeferredGoto {
    pub scope_id: ScopeId,
    pub block_id: BlockId,
    pub deferred_type: DeferredType,
    pub name: StringKey,
    pub call_span_id: SpanId,
    pub args: Vec<Argument>,
    pub argvec: ArgVec,
}

impl DeferredGoto {
    pub fn new(
        scope_id: ScopeId,
        name: StringKey,
        args: Vec<Argument>,
        call_span_id: SpanId,
        block_id: BlockId,
        deferred_type: DeferredType,
    ) -> Self {
        Self {
            scope_id,
            name,
            args,
            call_span_id,
            block_id,
            deferred_type,
            argvec: vec![],
        }
    }
}

#[derive(Debug, Clone)]
pub struct DeferredGotoList {
    h: Vec<DeferredGoto>,
    cps: Vec<DeferredGoto>,
}
impl DeferredGotoList {
    pub fn new() -> Self {
        Self {
            h: vec![],
            cps: vec![],
        }
    }

    pub fn is_empty(&self) -> bool {
        self.h.is_empty()
    }

    pub fn add_cps(&mut self, d: DeferredGoto) {
        self.cps.push(d);
    }

    pub fn pop_cps(&mut self) -> Option<DeferredGoto> {
        self.cps.pop()
    }

    pub fn add_deferred(&mut self, d: DeferredGoto) {
        self.h.push(d);
    }

    pub fn pop_deferred(&mut self) -> Option<DeferredGoto> {
        self.h.pop()
    }
}

#[derive(Debug)]
pub struct ScopeLayer {
    pub names: HashMap<StringKey, LinkId>,
    pub entries: HashMap<StringKey, HashSet<VariantId>>,
    pub declarations: HashMap<StringKey, LinkId>,
    pub labels: HashMap<StringLabel, ValueId>,
    pub(crate) block_labels: HashMap<StringLabel, BlockId>,
    pub blocks: Vec<ValueId>,
    pub entry_block: Option<BlockId>,
    pub return_block: Option<BlockId>,
    pub(crate) loop_block: Option<LoopScope>,
    pub scope_type: ScopeType,
    pub lambdas: HashMap<StringLabel, AbstractionId>,
    pub templates: HashMap<StringKey, LinkId>,
    pub unclaimed_labels: HashMap<StringLabel, BlockId>,
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
            //next_block: vec![],
            loop_block: None,
            scope_type,
            lambdas: HashMap::new(),
            templates: HashMap::new(),
            unclaimed_labels: HashMap::new(),
        }
    }

    pub fn variant_link(&mut self, name: StringKey, variant_id: VariantId) {
        if let Some(m) = self.entries.get_mut(&name) {
            m.insert(variant_id);
        } else {
            let mut m = HashSet::new();
            m.insert(variant_id);
            self.entries.insert(name, m);
        }
    }

    pub fn lookup(&self, name: StringKey) -> Option<LinkId> {
        self.names.get(&name).cloned()
    }

    pub fn dump(&self, b: &NodeBuilder) {
        println!("Scope: {:?}", self.scope_type);
        for (k, v) in self.labels.iter() {
            let s = b.labels.r(*k);
            println!("\tLabel: {}:{:?}", s, v);
        }
        for (k, v) in self.entries.iter() {
            let name = b.labels.r((*k).into());
            for variant_id in v.iter() {
                println!("\tEntry: {}:{}", name, variant_id);
            }
        }
        for (k, v) in self.names.iter() {
            let name = b.labels.r((*k).into());
            println!("\tName: {}:{}", name, v);
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

    pub fn ensure_claims(&self, b: &mut NodeBuilder) {
        for index in self.0.node_indices() {
            let scope_id: ScopeId = index.into();
            let scope = self.0.node_weight(index).unwrap();
            for (key, block_id) in scope.unclaimed_labels.iter() {
                let s = b.labels.r(*key);
                let span_id = b.spans.get_span_unknown();
                b.push_error(
                    &format!(
                        "Unclaimed label: {}, block {} in scope: {}",
                        s, block_id, scope_id
                    ),
                    span_id,
                );
                //assert!(false);
                //println!("unclaimed:{:?}", (s, block_id, scope_id))
            }
        }
    }

    pub fn in_function_scope(&self, scope_id: ScopeId) -> bool {
        if let Some(_fun_scope_id) = self.find_nearest_scope(scope_id, &[ScopeType::Function]) {
            true
        } else {
            false
        }
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

    pub fn unwind_scopes(
        &self,
        start_scope_id: ScopeId,
        end_scope_id: ScopeId,
    ) -> Result<Vec<ScopeId>> {
        let mut out = vec![];
        let mut current = start_scope_id;
        loop {
            if current == end_scope_id {
                break;
            }

            if let Some(next_scope_id) = self.step_up(current) {
                out.push(current);
                current = next_scope_id;
            } else {
                let msg = format!("{}=>{}", start_scope_id, end_scope_id);
                println!("msg:{}", msg);
                return Err(Error::new(BlockifyError::UnwindNotFound(msg)));
            }
        }
        println!(
            "unwind scopes: {}=>{}, {:?}",
            start_scope_id, end_scope_id, out
        );
        Ok(out)
    }

    pub fn step_up(&self, scope_id: ScopeId) -> Option<ScopeId> {
        self.neighbors_directed(scope_id.into(), petgraph::Direction::Incoming)
            .next()
            .map(|n| (n).into())
    }

    pub fn walk_scopes(&self, scope_id: ScopeId) -> Vec<ScopeId> {
        let mut out = vec![];
        let mut current = scope_id;
        loop {
            out.push(current);
            if let Some(next_scope_id) = self.step_up(current) {
                current = next_scope_id;
            } else {
                break;
            }
        }
        out
    }

    pub fn find_scopes(&self, scope_id: ScopeId) -> Vec<ScopeId> {
        let mut out = vec![];
        let mut bfs = Bfs::new(&self.0, scope_id.into());
        while let Some(index) = bfs.next(&self.0) {
            out.push(index.into());
        }
        out
    }

    pub fn get_entry_block(&self, scope_id: ScopeId) -> BlockId {
        self.get_scope(scope_id).entry_block.unwrap()
    }

    pub fn update_loop_blocks(
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

    pub fn dump_scope(&self, scope_id: ScopeId, b: &NodeBuilder) {
        println!("DumpScope: {}, {:?}", scope_id, self.walk_scopes(scope_id));
        for scope_id in self.walk_scopes(scope_id) {
            let scope = self.get_scope(scope_id);
            scope.dump(b);
        }
    }

    pub fn dump(&self, b: &NodeBuilder) {
        self.0.node_indices().for_each(|index| {
            let scope_id: ScopeId = index.into();
            let scope = self.get_scope(scope_id);
            println!("DumpScope: {}", scope_id);
            scope.dump(b);
        });
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
