use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use std::collections::HashSet;

use crate::{
    AbstractionId, AbstractionsBuilder, BlockId, CodeOffset, FunctionVariantBuilder, LinkId, Links,
    NodeBuilder, SafeBlock, SafeBlockEmpty, ScopeId, ScopeLayer, VariantId,
};

use std::collections::HashMap;

use compile_core::{AstType, Lambda, SpanId, StringKey};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Successor {
    BlockScope,
    Operation,
    Jump,
    FunctionDeclaration,
    TemplateDeclaration,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BlockStateEnum {
    Start,
    Entry,
    Body,
    Term,
}

#[derive(Debug, Clone)]
pub struct IRBlock {
    scope_id: ScopeId,
    dead: bool,
    entry: Vec<LinkId>,
    terminal: Option<LinkId>,
    decls: Vec<LinkId>,
    links: Vec<LinkId>,
    s: BlockStateEnum,
}

impl IRBlock {
    pub fn new(scope_id: ScopeId) -> Self {
        Self {
            scope_id,
            dead: false,
            entry: vec![],
            terminal: None,
            links: vec![],
            decls: vec![],
            s: BlockStateEnum::Start,
        }
    }

    pub fn scope(&self) -> ScopeId {
        self.scope_id
    }

    pub fn scope_set(&mut self, scope_id: ScopeId) {
        self.scope_id = scope_id;
    }

    pub fn iter_args(&self) -> impl Iterator<Item = LinkId> + '_ {
        self.entry.iter().skip(1).cloned()
    }

    pub fn iter(&self) -> impl Iterator<Item = LinkId> + '_ {
        self.entry
            .iter()
            .copied()
            .chain(self.decls.iter().copied())
            .chain(self.links.iter().copied())
            .chain(self.terminal.iter().copied())
    }

    pub fn is_dead(&self) -> bool {
        self.dead
    }

    pub fn is_term(&self) -> bool {
        self.terminal.is_some()
    }

    pub fn mark_dead(&mut self) {
        self.dead = true;
    }

    pub fn entry(&self) -> LinkId {
        self.entry.first().unwrap().clone()
    }

    pub fn empty(&self) -> bool {
        self.iter().next().is_none()
    }

    pub fn len(&self) -> usize {
        self.iter().count()
    }

    pub fn push_label(&mut self, link_id: LinkId) {
        assert_eq!(self.s, BlockStateEnum::Start);
        self.s = BlockStateEnum::Entry;
        assert!(self.entry.is_empty());
        assert!(self.last().is_none());
        self.entry.push(link_id);
    }

    pub fn push_arg(&mut self, link_id: LinkId) {
        assert_eq!(self.s, BlockStateEnum::Entry);
        assert!(!self.is_term());
        assert!(!self.entry.is_empty());
        self.entry.push(link_id)
    }

    pub fn push_decl(&mut self, link_id: LinkId) {
        assert_ne!(self.s, BlockStateEnum::Start);
        if self.s != BlockStateEnum::Term {
            self.s = BlockStateEnum::Body;
        }
        self.decls.push(link_id);
    }

    pub fn prepend_link(&mut self, link_id: LinkId) {
        self.links.insert(0, link_id);
    }

    pub fn terminate(&mut self, link_id: LinkId) {
        assert_ne!(self.s, BlockStateEnum::Term);
        assert!(!self.is_term());
        assert!(!self.entry.is_empty());
        self.s = BlockStateEnum::Term;
        self.terminal = Some(link_id);
    }

    pub fn push_link(&mut self, link_id: LinkId) {
        assert_ne!(self.s, BlockStateEnum::Term);
        assert!(!self.is_term());
        assert!(!self.entry.is_empty());
        self.s = BlockStateEnum::Body;
        self.links.push(link_id)
    }

    pub fn last_decl(&self) -> Option<LinkId> {
        if let Some(last) = self.decls.last().cloned() {
            return Some(last);
        }
        if let Some(last) = self.entry.last().cloned() {
            return Some(last);
        }
        None
    }

    pub fn last(&self) -> Option<LinkId> {
        if let Some(last) = self.terminal {
            return Some(last);
        }
        if let Some(last) = self.links.last().cloned() {
            return Some(last);
        }
        self.last_decl()
    }

    pub fn pop_terminal(&mut self) -> LinkId {
        assert_eq!(self.s, BlockStateEnum::Term);
        self.s = BlockStateEnum::Body;
        self.terminal.take().unwrap();
        self.last().unwrap()
    }
}

pub trait BlockGraphState {}

pub struct BlockGraphStateStart {}
impl BlockGraphState for BlockGraphStateStart {}

pub struct BlockGraphStateOpen {
    static_scope: ScopeId,
    static_block: BlockId,
}
impl BlockGraphState for BlockGraphStateOpen {}

pub struct BlockGraph<S: BlockGraphState> {
    pub(super) bg: DiGraph<IRBlock, Successor>,
    pub(super) sg: DiGraph<ScopeLayer, ()>,
    pub(super) variants: FunctionVariantBuilder,
    pub(super) abstractions: AbstractionsBuilder,
    pub(super) links: Links,
    pub(super) block_links: HashMap<BlockId, LinkId>,
    extra: S,
}

impl BlockGraph<BlockGraphStateStart> {
    fn start() -> Self {
        Self {
            bg: DiGraph::new(),
            sg: DiGraph::new(),
            variants: FunctionVariantBuilder::new(),
            abstractions: AbstractionsBuilder::new(),
            links: Links::new(),
            block_links: HashMap::new(),
            extra: BlockGraphStateStart {},
        }
    }
}

impl BlockGraph<BlockGraphStateOpen> {
    pub fn new() -> BlockGraph<BlockGraphStateOpen> {
        let start = BlockGraph::start();
        BlockGraph::open(start)
    }

    fn open(mut g: BlockGraph<BlockGraphStateStart>) -> Self {
        let (static_block_id, static_scope_id) = g.root();
        BlockGraph {
            bg: g.bg,
            sg: g.sg,
            variants: g.variants,
            abstractions: g.abstractions,
            links: g.links,
            block_links: g.block_links,
            extra: BlockGraphStateOpen {
                static_scope: static_scope_id,
                static_block: static_block_id,
            },
        }
    }

    pub fn static_scope_id(&self) -> ScopeId {
        self.extra.static_scope
    }

    pub fn static_block_id(&self) -> BlockId {
        self.extra.static_block
    }
}

impl<S: BlockGraphState> BlockGraph<S> {
    pub fn new_block(&mut self, parent_block_id: BlockId, succ: Successor) -> SafeBlockEmpty {
        let parent = self.get_block(parent_block_id);
        self.new_block_different_scope(parent_block_id, parent.scope(), succ)
    }

    pub fn new_block_different_scope(
        &mut self,
        parent_block_id: BlockId,
        scope_id: ScopeId,
        succ: Successor,
    ) -> SafeBlockEmpty {
        let block_id = self.insert_new_block(scope_id);
        self.block_succ(parent_block_id, block_id, succ);
        SafeBlock {
            block_id,
            extra: crate::safe::Empty {},
        }
    }

    pub fn get_block(&self, block_id: BlockId) -> &IRBlock {
        let index = NodeIndex::new(block_id.index());
        self.bg.node_weight(index).unwrap()
    }

    pub fn insert_new_block(&mut self, scope_id: ScopeId) -> BlockId {
        let ir_block = IRBlock::new(scope_id);
        let index = self.bg.add_node(ir_block);
        BlockId::new(index.index())
    }

    pub fn block_succ(
        &mut self,
        source_block_id: BlockId,
        target_block_id: BlockId,
        succ_type: Successor,
    ) {
        self.bg.add_edge(
            NodeIndex::new(source_block_id.index()),
            NodeIndex::new(target_block_id.index()),
            succ_type,
        );
    }
}

impl BlockGraph<BlockGraphStateOpen> {
    pub fn get_block_mut(&mut self, block_id: BlockId) -> &mut IRBlock {
        let index = NodeIndex::new(block_id.index());
        self.bg.node_weight_mut(index).unwrap()
    }

    pub fn get_block_successors(&self, block_id: BlockId) -> Vec<(Successor, CodeOffset)> {
        let index = NodeIndex::new(block_id.index());
        let edges = self
            .bg
            .edges_directed(index, petgraph::Direction::Outgoing)
            .collect::<Vec<_>>();
        let mut out = vec![];
        for edge in edges {
            let succ_type = edge.weight();
            let i = edge.target();
            let block = self.bg.node_weight(i).unwrap();
            if block.dead {
                continue;
            }
            let block_id = BlockId::new(i.index()).into();
            out.push((*succ_type, block_id));
        }
        out
    }

    pub fn find_dead_blocks(&self) -> Vec<BlockId> {
        let entries = self
            .graph_get_entries()
            .into_iter()
            .collect::<Vec<BlockId>>();

        let subgraph = self.bg.filter_map(
            |_n_index, n| Some(n.clone()),
            |_e_index, e| {
                if let Successor::Jump = e {
                    Some(e.clone())
                } else {
                    None
                }
            },
        );

        let mut out = vec![];
        for entry in entries {
            let mut reachable: HashSet<BlockId> = HashSet::new();
            let mut all = HashSet::new();
            reachable.insert(entry);
            all.insert(entry.into());

            let mut dfs = petgraph::visit::Dfs::new(&subgraph, NodeIndex::new(entry.index()));
            while let Some(visited) = dfs.next(&self.bg) {
                for edge in self.bg.edges(visited) {
                    let b: BlockId = BlockId::new(edge.target().index());
                    all.insert(b);
                }
            }

            let mut dfs = petgraph::visit::Dfs::new(&subgraph, NodeIndex::new(entry.index()));
            while let Some(visited) = dfs.next(&subgraph) {
                for edge in subgraph.edges(visited) {
                    if Successor::Jump == *edge.weight() {
                        let b: BlockId = BlockId::new(edge.target().index());
                        reachable.insert(b);
                    }
                }
            }
            let dead = all.difference(&reachable);
            for block_id in dead {
                out.push(*block_id);
            }
        }
        out
    }

    pub fn graph_get_entries(&self) -> HashSet<BlockId> {
        let mut dfs = petgraph::visit::Dfs::new(&self.bg, NodeIndex::new(0));
        let mut entries = HashSet::new();
        while let Some(visited) = dfs.next(&self.bg) {
            for edge in self.bg.edges(visited) {
                if Successor::FunctionDeclaration == *edge.weight() {
                    entries.insert(BlockId::new(edge.target().index()));
                }
            }
        }
        entries
    }

    pub fn post_order_blocks(&self) -> Vec<BlockId> {
        let mut blocks = vec![BlockId::new(0).into()];
        for block_id in self.graph_get_entries() {
            let mut seq: Vec<BlockId> = vec![];
            let mut dfs =
                petgraph::visit::DfsPostOrder::new(&self.bg, NodeIndex::new(block_id.index()));
            while let Some(index) = dfs.next(&self.bg) {
                seq.push(BlockId::new(index.index()));
            }
            blocks.extend(seq.into_iter().rev());
        }
        blocks
    }

    pub fn block_graph(&self) -> &DiGraph<IRBlock, Successor> {
        &self.bg
    }

    pub fn subgraph_jumps(&self) -> DiGraph<IRBlock, Successor> {
        self.bg.filter_map(
            |_n_index, n| Some(n.clone()),
            |_e_index, e| {
                if let Successor::Jump = e {
                    Some(e.clone())
                } else {
                    None
                }
            },
        )
    }

    pub fn dump_blocks(&self) {
        let bg = self.block_graph();
        for node in bg.node_indices() {
            let block_id: BlockId = node.into();
            let block = bg.node_weight(node).unwrap();
            println!("[{}] Block: {:?}", block_id, block);
        }
    }

    pub fn variant_add(
        &mut self,
        scope_id: ScopeId,
        abstraction_id: AbstractionId,
        name: StringKey,
        ty: AstType,
        link_id: LinkId,
        block_id: BlockId,
    ) -> VariantId {
        let variant_id = self
            .variants
            .add(abstraction_id, ty, link_id, block_id, name);
        let scope = self.get_scope_mut(scope_id);
        scope.variant_link(name, variant_id);
        variant_id
    }

    pub fn resolve_function_name(
        &self,
        start_scope_id: ScopeId,
        name: &StringKey,
        call_func_type: &AstType,
        b: &mut NodeBuilder,
    ) -> Option<(AstType, LinkId, ScopeId)> {
        let mut result = None;
        let snapshot = b.types.u.snapshot();
        let ty = call_func_type.clone().into();
        for variant_id in self.list_variants(start_scope_id, name) {
            let v = self.variants.get(variant_id);
            if let Ok(_) = b.types.u.unify(&ty, &v.ty) {
                result = Some((v.ty.clone(), v.link_id, start_scope_id));
                break;
            }
        }
        b.types.u.rollback_to(snapshot);
        result
    }

    pub fn save_abstraction(
        &mut self,
        block_id: BlockId,
        name: &StringKey,
        def: &Lambda,
        span_id: SpanId,
    ) -> AbstractionId {
        let abstraction_id = self.abstractions.add(*name, def.clone(), span_id);
        let block = self.get_block(block_id);
        self.define_lambda(block.scope(), name.into(), abstraction_id);
        abstraction_id
    }
}
