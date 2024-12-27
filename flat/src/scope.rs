use anyhow::Error;
use anyhow::Result;
use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use petgraph::visit::Bfs;

use std::ops::{Deref, DerefMut};

use std::collections::{HashMap, HashSet};

use crate::{
    ArgVec, BlockGraph, BlockId, BlockifyError, LinkId, NodeBuilder, StringLabel, ValueId,
    VariantId,
};
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
    pub name: Option<StringKey>,
    pub call_span_id: SpanId,
    pub args: Vec<Argument>,
    pub argvec: ArgVec,
}

impl DeferredGoto {
    pub fn new(
        scope_id: ScopeId,
        name: Option<StringKey>,
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

#[derive(Debug, Clone)]
pub struct ScopeStateFunction {
    return_block: BlockId,
}
impl ScopeStateFunction {
    pub fn new(return_block: BlockId) -> Self {
        Self { return_block }
    }
}

#[derive(Debug, Clone)]
pub struct ScopeStateBlock {}

#[derive(Debug, Clone)]
pub enum ScopeState {
    Function(ScopeStateFunction),
    Block(ScopeStateBlock),
    Static,
    Region,
}
impl ScopeState {
    pub fn function(return_block: BlockId) -> Self {
        Self::Function(ScopeStateFunction::new(return_block))
    }
    pub fn block() -> Self {
        Self::Block(ScopeStateBlock {})
    }
    pub fn static_scope() -> Self {
        Self::Static
    }
    pub fn region() -> Self {
        Self::Region
    }
}

pub trait ScopeTypeState {}
#[derive(Debug)]
pub struct ScopeTypeStateBlock {}
#[derive(Debug)]
pub struct ScopeTypeStateFunction {}
#[derive(Debug)]
pub struct ScopeTypeStateStatic {}
impl ScopeTypeState for ScopeTypeStateBlock {}
impl ScopeTypeState for ScopeTypeStateStatic {}
impl ScopeTypeState for ScopeTypeStateFunction {}

pub struct TypedScope<'a, ScopeTypeState> {
    inner: &'a mut ScopeLayer,
    _s: std::marker::PhantomData<ScopeTypeState>,
}

impl<'a, S: ScopeTypeState> Deref for TypedScope<'a, S> {
    type Target = ScopeLayer;

    fn deref(&self) -> &Self::Target {
        self.inner
    }
}
impl<'a, S: ScopeTypeState> DerefMut for TypedScope<'a, S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner
    }
}

impl<'a> TypedScope<'a, ScopeTypeStateFunction> {
    pub fn return_block(&self) -> BlockId {
        self.inner.return_block.unwrap()
    }
}

#[derive(Debug)]
pub struct ScopeLayer {
    pub names: HashMap<StringKey, LinkId>,
    pub entries: HashMap<StringKey, HashSet<VariantId>>,
    pub declarations: HashMap<StringKey, LinkId>,
    pub labels: HashMap<StringLabel, ValueId>,
    pub(crate) block_labels: HashMap<StringLabel, BlockId>,
    pub entry_block: Option<BlockId>,
    return_block: Option<BlockId>,
    pub(crate) loop_block: Option<LoopScope>,
    scope_type: ScopeType,
    lambdas: HashMap<StringLabel, AbstractionId>,
    unclaimed_labels: HashMap<StringLabel, BlockId>,
}

impl ScopeLayer {
    pub fn new(scope_type: ScopeType) -> Self {
        Self {
            labels: HashMap::new(),
            block_labels: HashMap::new(),
            names: HashMap::new(),
            entries: HashMap::new(),
            declarations: HashMap::new(),
            entry_block: None,
            return_block: None,
            loop_block: None,
            scope_type,
            lambdas: HashMap::new(),
            unclaimed_labels: HashMap::new(),
        }
    }

    pub fn is_static(&self) -> bool {
        self.scope_type == ScopeType::Static
    }

    pub fn make_function_scope(&mut self, state: ScopeStateFunction) {
        self.return_block = Some(state.return_block);
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

impl BlockGraph {
    pub fn scope_graph(&self) -> &DiGraph<ScopeLayer, ()> {
        &self.sg
    }

    pub fn new_scope(&mut self, scope_type: ScopeType) -> ScopeId {
        let scope = ScopeLayer::new(scope_type);
        let index = self.sg.add_node(scope);
        ScopeId(index.index() as u32)
    }

    pub fn get_scope(&self, scope_id: ScopeId) -> &ScopeLayer {
        let index = NodeIndex::new(scope_id.index());
        self.sg.node_weight(index).unwrap()
    }

    pub fn get_scope_mut(&mut self, scope_id: ScopeId) -> &mut ScopeLayer {
        let index = NodeIndex::new(scope_id.index());
        self.sg.node_weight_mut(index).unwrap()
    }

    pub fn scope_define(&mut self, scope_id: ScopeId, name: StringKey, v: LinkId) {
        let scope = self.get_scope_mut(scope_id);
        scope.names.insert(name, v);
    }

    pub fn scope_define_declaration(&mut self, scope_id: ScopeId, name: StringKey, v: LinkId) {
        let scope = self.get_scope_mut(scope_id);
        scope.declarations.insert(name, v);
    }

    pub fn scope_succ(&mut self, source_scope_id: ScopeId, target_scope_id: ScopeId) {
        self.sg
            .add_edge(source_scope_id.into(), target_scope_id.into(), ());
    }

    pub fn ensure_claims(&self, b: &mut NodeBuilder) {
        for index in self.sg.node_indices() {
            let scope_id: ScopeId = index.into();
            let scope = self.sg.node_weight(index).unwrap();
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

    pub fn is_in_scope(&self, start_scope_id: ScopeId, end_scope_id: ScopeId) -> bool {
        for scope_id in self.walk_scopes(start_scope_id) {
            if scope_id == end_scope_id {
                return true;
            }
        }
        false
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
        self.sg
            .neighbors_directed(scope_id.into(), petgraph::Direction::Incoming)
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
        let mut bfs = Bfs::new(&self.sg, scope_id.into());
        while let Some(index) = bfs.next(&self.sg) {
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

    pub fn dump_scopes(&self) {
        petgraph::dot::Dot::with_config(&self.scope_graph(), &[petgraph::dot::Config::EdgeNoLabel]);
    }

    pub fn dump(&self, b: &NodeBuilder) {
        self.sg.node_indices().for_each(|index| {
            let scope_id: ScopeId = index.into();
            let scope = self.get_scope(scope_id);
            println!("DumpScope: {}", scope_id);
            scope.dump(b);
        });
    }

    pub fn get_function_scope_id(&self, scope_id: ScopeId) -> ScopeId {
        self.find_nearest_scope(scope_id, &[ScopeType::Function])
            .expect(&format!("Not in function context, scope_id:{}", scope_id))
    }

    pub fn get_function_scope(&mut self, block_id: BlockId) -> TypedScope<ScopeTypeStateFunction> {
        let block = self.get_block(block_id);
        let function_scope_id = self.get_function_scope_id(block.scope_id);
        let scope = self.get_scope_mut(function_scope_id);
        TypedScope {
            inner: scope,
            _s: std::marker::PhantomData,
        }
    }

    pub fn gen_scope_graph(&self, filename: &str) {
        use petgraph::dot::{Config, Dot};
        let s = format!(
            "{:?}",
            Dot::with_attr_getters(
                &self.sg,
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

    pub fn define_lambda(
        &mut self,
        scope_id: ScopeId,
        name: StringLabel,
        abstraction_id: AbstractionId,
    ) {
        let scope = self.get_scope_mut(scope_id);
        scope.lambdas.insert(name, abstraction_id);
    }

    pub fn resolve_lambda_scope(&self, block_id: BlockId, name: StringLabel) -> Option<ScopeId> {
        // resolve scope through the tree, starting at the current scope
        let block = self.get_block(block_id);
        for scope_id in self.walk_scopes(block.scope_id) {
            let scope = self.get_scope(scope_id);
            if let Some(_template_id) = scope.lambdas.get(&name) {
                return Some(scope_id);
            }
        }
        None
    }

    pub fn resolve_lambda(
        &self,
        block_id: BlockId,
        name: StringKey,
    ) -> Option<(ScopeId, AbstractionId)> {
        match self.resolve_lambda_scope(block_id, name.into()) {
            Some(scope_id) => {
                let scope = self.get_scope(scope_id);
                if let Some(abstraction_id) = scope.lambdas.get(&name.into()).cloned() {
                    //let a = self.abstractions.get(template_id);
                    //let (def, span_id, _) = self.get_ast_template(template_id).clone();
                    Some((scope_id, abstraction_id))
                } else {
                    None
                }
            }
            None => None,
        }
    }

    pub fn resolve_template(
        &self,
        start_scope_id: ScopeId,
        name: StringLabel,
    ) -> Option<AbstractionId> {
        // search scopes to find a template
        for scope_id in self.walk_scopes(start_scope_id) {
            let scope = self.get_scope(scope_id);
            if let Some(template_id) = scope.lambdas.get(&name).cloned() {
                return Some(template_id);
            }
        }
        None
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
