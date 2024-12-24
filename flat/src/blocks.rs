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

#[derive(Debug, Clone)]
pub enum Start {}

pub trait BlockState: std::fmt::Debug + Clone {}

impl BlockState for Start {}

#[derive(Debug, Clone)]
pub struct IRBlock<S> {
    pub(super) scope_id: ScopeId,
    pub(super) dead: bool,
    pub(super) term: bool,
    pub(super) size: usize,
    entry: Option<LinkId>,
    links: Vec<LinkId>,
    pub(super) last: Option<LinkId>,
    pub(super) last_decl: Option<LinkId>,
    pub(super) num_ret_args: HashSet<usize>,
    pub(super) ret_types: HashSet<AstType>,
    _state: std::marker::PhantomData<S>,
}

impl<S> IRBlock<S> {
    pub fn new(scope_id: ScopeId) -> Self {
        Self {
            scope_id,
            dead: false,
            term: false,
            entry: None,
            last: None,
            last_decl: None,
            size: 0,
            num_ret_args: HashSet::new(),
            ret_types: HashSet::new(),
            links: vec![],
            _state: std::marker::PhantomData::default(),
        }
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

    pub fn insert(&mut self) {
        self.size += 1;
    }

    pub fn push_label(&mut self, link_id: LinkId) {
        assert!(!self.term);
        assert!(self.last.is_none());
        self.entry = Some(link_id);
        self.last = Some(link_id);
        self.size += 1;
    }

    pub fn push_decl(&mut self, link_id: LinkId) {
        if self.last.unwrap() == link_id {
            self.last = Some(link_id);
        }
        self.last_decl = Some(link_id);
    }

    pub fn push_link(&mut self, link_id: LinkId, term: bool) {
        assert!(!self.term);
        assert!(self.entry.is_some());
        self.term = term;
        self.last = Some(link_id);
        self.size += 1;
    }

    pub fn last(&self) -> Option<LinkId> {
        self.last
    }

    pub fn is_term(&self) -> bool {
        self.term
    }
}

pub struct BlockGraph<S: BlockState>(pub(super) DiGraph<IRBlock<S>, Successor>);

impl<S: BlockState> Deref for BlockGraph<S> {
    type Target = DiGraph<IRBlock<S>, Successor>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<S: BlockState> DerefMut for BlockGraph<S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<S: BlockState> BlockGraph<S> {
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

    pub fn get_block(&self, block_id: BlockId) -> &IRBlock<S> {
        let index = NodeIndex::new(block_id.index());
        self.node_weight(index).unwrap()
    }

    pub fn get_block_mut(&mut self, block_id: BlockId) -> &mut IRBlock<S> {
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
