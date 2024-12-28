use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use std::collections::HashSet;

use crate::{BlockId, CodeOffset, LinkId, ScopeId, ScopeLayer};

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
    term: bool,
    size: usize,
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
            term: false,
            entry: vec![],
            terminal: None,
            size: 0,
            links: vec![],
            decls: vec![],
            s: BlockStateEnum::Start,
        }
    }

    pub fn scope(&self) -> ScopeId {
        self.scope_id
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

    pub fn entry(&self) -> LinkId {
        self.entry.first().unwrap().clone()
    }

    pub fn empty(&self) -> bool {
        self.size == 0
    }

    pub fn len(&self) -> usize {
        self.size
    }

    pub fn push_label(&mut self, link_id: LinkId) {
        assert_eq!(self.s, BlockStateEnum::Start);
        self.s = BlockStateEnum::Entry;
        assert!(!self.term);
        assert!(self.entry.is_empty());
        assert!(self.last().is_none());
        self.entry.push(link_id);
        self.size += 1;
    }

    pub fn push_arg(&mut self, link_id: LinkId) {
        assert_eq!(self.s, BlockStateEnum::Entry);
        assert!(!self.term);
        assert!(!self.entry.is_empty());
        self.size += 1;
        self.entry.push(link_id)
    }

    pub fn push_decl(&mut self, link_id: LinkId) {
        assert_ne!(self.s, BlockStateEnum::Start);
        if self.s != BlockStateEnum::Term {
            self.s = BlockStateEnum::Body;
        }
        self.decls.push(link_id);
        self.size += 1;
    }

    pub fn prepend_link(&mut self, link_id: LinkId) {
        self.links.insert(0, link_id);
        self.size += 1;
    }

    pub fn push_link(&mut self, link_id: LinkId, term: bool) {
        assert_ne!(self.s, BlockStateEnum::Term);
        assert!(!self.term);
        assert!(!self.entry.is_empty());

        if term {
            self.s = BlockStateEnum::Term;
            self.terminal = Some(link_id);
        } else {
            self.s = BlockStateEnum::Body;
            self.links.push(link_id)
        }
        self.term = term;
        self.size += 1;
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

    pub fn is_term(&self) -> bool {
        self.terminal.is_some()
    }

    pub fn pop_terminal(&mut self) -> LinkId {
        assert_eq!(self.s, BlockStateEnum::Term);
        self.s = BlockStateEnum::Body;
        self.term = false;
        self.terminal.take().unwrap();
        self.last().unwrap()
    }
}

pub struct BlockGraph {
    pub(super) bg: DiGraph<IRBlock, Successor>,
    pub(super) sg: DiGraph<ScopeLayer, ()>,
}

impl BlockGraph {
    pub fn new() -> Self {
        Self {
            bg: DiGraph::new(),
            sg: DiGraph::new(),
        }
    }

    pub fn new_block(
        &mut self,
        parent_block_id: BlockId,
        scope_id: ScopeId,
        succ: Successor,
    ) -> BlockId {
        let block_id = self.new_block_with_scope(scope_id);
        self.block_succ(parent_block_id, block_id, succ);
        block_id
    }

    pub fn new_block_with_scope(&mut self, scope_id: ScopeId) -> BlockId {
        let ir_block = IRBlock::new(scope_id);
        let index = self.bg.add_node(ir_block);

        // ensure the first block is the static block
        if index.index() > 0 && scope_id.index() == 0 {
            assert!(false);
        }

        BlockId::new(index.index())
    }

    pub fn control_flow(&mut self, source_block_id: BlockId, target_block_ids: &[BlockId]) {
        for target_block_id in target_block_ids {
            self.block_succ(source_block_id, *target_block_id, Successor::Jump);
        }
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

    pub fn get_block(&self, block_id: BlockId) -> &IRBlock {
        let index = NodeIndex::new(block_id.index());
        self.bg.node_weight(index).unwrap()
    }

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
            if !block.dead {
                let block_id = BlockId::new(i.index()).into();
                out.push((*succ_type, block_id));
            }
        }
        out
    }

    pub fn find_dead_blocks_from_graph(&mut self) -> Vec<BlockId> {
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
            //println!("[{:?}] Dead: {:?}", entry, &dead);
            //println!("[{:?}] All: {:?}", entry, &all);
            //println!("[{:?}] Reachable: {:?}", entry, &reachable);
            for block_id in dead {
                let index = NodeIndex::new((*block_id).index());
                let block = self.bg.node_weight_mut(index).unwrap();
                block.dead = true;
                out.push(*block_id);
                //let v = self.get_entry_id_from_block_id(*block_id);
                //let span_id = self.get_span_id(v);
                //b.push_warning(&format!("Dead Block: {}", block_id), span_id);
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
}
