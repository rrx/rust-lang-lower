use compile_core::AstType;
use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use std::collections::HashSet;

use crate::{BlockId, CodeOffset, LinkId, ScopeId};
use std::ops::{Deref, DerefMut};

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
    pub(super) scope_id: ScopeId,
    dead: bool,
    term: bool,
    size: usize,
    entry: Option<LinkId>,
    terminal: Option<LinkId>,
    links: Vec<LinkId>,
    last: Option<LinkId>,
    last_decl: Option<LinkId>,
    pub(super) num_ret_args: HashSet<usize>,
    pub(super) ret_types: HashSet<AstType>,
    s: BlockStateEnum,
}

impl IRBlock {
    pub fn new(scope_id: ScopeId) -> Self {
        Self {
            scope_id,
            dead: false,
            term: false,
            entry: None,
            terminal: None,
            last: None,
            last_decl: None,
            size: 0,
            num_ret_args: HashSet::new(),
            ret_types: HashSet::new(),
            links: vec![],
            s: BlockStateEnum::Start,
        }
    }

    pub fn is_dead(&self) -> bool {
        self.dead
    }

    pub fn entry(&self) -> LinkId {
        self.entry.unwrap()
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
        assert!(self.last.is_none());
        self.entry = Some(link_id);
        self.last = Some(link_id);
        self.last_decl = Some(link_id);
        self.size += 1;
        self.links.push(link_id)
    }

    pub fn push_arg(&mut self, link_id: LinkId) {
        assert_eq!(self.s, BlockStateEnum::Entry);
        assert!(!self.term);
        assert!(self.entry.is_some());
        self.last = Some(link_id);
        self.last_decl = Some(link_id);
        self.size += 1;
        self.links.push(link_id)
    }

    pub fn push_decl(&mut self, link_id: LinkId) {
        assert_ne!(self.s, BlockStateEnum::Start);
        let index = self
            .links
            .iter()
            .position(|x| *x == self.last_decl())
            .unwrap()
            + 1;
        if self.s != BlockStateEnum::Term {
            self.s = BlockStateEnum::Body;
        }
        if self.last.unwrap() == self.last_decl.unwrap() {
            self.last = Some(link_id);
        }
        self.last_decl = Some(link_id);
        self.links.insert(index, link_id);
        self.size += 1;
    }

    pub fn push_link(&mut self, link_id: LinkId, term: bool) {
        assert_ne!(self.s, BlockStateEnum::Term);
        assert!(!self.term);
        assert!(self.entry.is_some());

        if term {
            self.s = BlockStateEnum::Term;
            self.terminal = Some(link_id);
        } else {
            self.s = BlockStateEnum::Body;
            self.links.push(link_id)
        }
        self.term = term;
        self.last = Some(link_id);
        self.size += 1;
    }

    pub fn last(&self) -> Option<LinkId> {
        self.last
    }

    pub fn last_decl(&self) -> LinkId {
        self.last_decl.unwrap()
    }

    pub fn is_term(&self) -> bool {
        self.term
    }

    pub fn pop_terminal(&mut self) -> LinkId {
        assert_eq!(self.s, BlockStateEnum::Term);
        self.s = BlockStateEnum::Body;
        self.term = false;
        self.terminal.take().unwrap();
        self.last = self.links.last().cloned();
        self.last.unwrap()
    }
}

pub struct BlockGraph(pub(super) DiGraph<IRBlock, Successor>);

impl Deref for BlockGraph {
    type Target = DiGraph<IRBlock, Successor>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl DerefMut for BlockGraph {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl BlockGraph {
    pub fn new() -> Self {
        Self(DiGraph::new())
    }

    pub fn new_block(&mut self, scope_id: ScopeId) -> BlockId {
        let ir_block = IRBlock::new(scope_id);
        let index = self.add_node(ir_block);
        //println!("new block: {:?}", (block_id, scope_id));
        if index.index() > 0 && scope_id.index() == 0 {
            assert!(false);
        }
        BlockId::new(index.index())
    }

    pub fn block_succ(
        &mut self,
        source_block_id: BlockId,
        target_block_id: BlockId,
        succ_type: Successor,
    ) {
        self.add_edge(
            NodeIndex::new(source_block_id.index()),
            NodeIndex::new(target_block_id.index()),
            succ_type,
        );
    }

    pub fn get_block(&self, block_id: BlockId) -> &IRBlock {
        let index = NodeIndex::new(block_id.index());
        self.node_weight(index).unwrap()
    }

    pub fn get_block_mut(&mut self, block_id: BlockId) -> &mut IRBlock {
        let index = NodeIndex::new(block_id.index());
        self.node_weight_mut(index).unwrap()
    }

    pub fn get_block_successors(&self, block_id: BlockId) -> Vec<(Successor, CodeOffset)> {
        let index = NodeIndex::new(block_id.index());
        let edges = self
            .edges_directed(index, petgraph::Direction::Outgoing)
            .collect::<Vec<_>>();
        let mut out = vec![];
        for edge in edges {
            let succ_type = edge.weight();
            let i = edge.target();
            let block = self.node_weight(i).unwrap();
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

        let subgraph = self.filter_map(
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
            while let Some(visited) = dfs.next(&self.0) {
                for edge in self.edges(visited) {
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
                let block = self.node_weight_mut(index).unwrap();
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
        let mut dfs = petgraph::visit::Dfs::new(&self.0, NodeIndex::new(0));
        let mut entries = HashSet::new();
        while let Some(visited) = dfs.next(&self.0) {
            for edge in self.0.edges(visited) {
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
                petgraph::visit::DfsPostOrder::new(&self.0, NodeIndex::new(block_id.index()));
            while let Some(index) = dfs.next(&self.0) {
                seq.push(BlockId::new(index.index()));
            }
            blocks.extend(seq.into_iter().rev());
        }
        blocks
    }
}
