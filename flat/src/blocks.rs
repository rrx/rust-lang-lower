use compile_core::AstType;
use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use std::collections::HashSet;
use std::convert::From;

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
pub struct IRBlock {
    pub(super) scope_id: ScopeId,
    pub(super) dead: bool,
    pub(super) term: bool,
    pub(super) last: Option<LinkId>,
    pub(super) num_ret_args: HashSet<usize>,
    pub(super) ret_types: HashSet<AstType>,
    pub(super) links: Vec<LinkId>,
}

impl IRBlock {
    pub fn new(scope_id: ScopeId) -> Self {
        Self {
            scope_id,
            dead: false,
            term: false,
            last: None,
            links: vec![],
            num_ret_args: HashSet::new(),
            ret_types: HashSet::new(),
        }
    }

    pub fn push(&mut self, link_id: LinkId, term: bool) {
        assert!(!self.term);
        self.links.push(link_id);
        self.term = term;
        self.last = Some(link_id);
    }

    pub fn last(&self) -> Option<LinkId> {
        self.last
        //self.links.last().cloned()
    }
}

impl Into<NodeIndex> for BlockId {
    fn into(self) -> NodeIndex {
        NodeIndex::new(self.index())
    }
}

impl From<NodeIndex> for BlockId {
    fn from(item: NodeIndex) -> Self {
        Self(item.index() as u32)
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
        BlockId(index.index() as u32)
    }

    pub fn block_succ(
        &mut self,
        source_block_id: BlockId,
        target_block_id: BlockId,
        succ_type: Successor,
    ) {
        self.add_edge(source_block_id.into(), target_block_id.into(), succ_type);
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
                let block_id = BlockId(i.index() as u32).into();
                out.push((*succ_type, block_id));
            }
        }
        out
    }

    pub fn find_dead_blocks_from_graph(&mut self) -> Vec<BlockId> {
        let mut dfs = petgraph::visit::Dfs::new(&self.0, BlockId(0).into());
        let mut entries = HashSet::new();
        while let Some(visited) = dfs.next(&self.0) {
            for edge in self.edges(visited) {
                if Successor::FunctionDeclaration == *edge.weight() {
                    entries.insert(edge.target());
                }
            }
        }

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
            let mut reachable = HashSet::new();
            let mut all = HashSet::new();
            reachable.insert(entry.into());
            all.insert(entry.into());

            let mut dfs = petgraph::visit::Dfs::new(&subgraph, entry.into());
            while let Some(visited) = dfs.next(&self.0) {
                for edge in self.edges(visited) {
                    let b: BlockId = edge.target().into();
                    all.insert(b);
                }
            }

            let mut dfs = petgraph::visit::Dfs::new(&subgraph, entry.into());
            while let Some(visited) = dfs.next(&subgraph) {
                for edge in subgraph.edges(visited) {
                    if Successor::Jump == *edge.weight() {
                        let b: BlockId = edge.target().into();
                        reachable.insert(b);
                    }
                }
            }
            let dead = all.difference(&reachable);
            //println!("[{:?}] Dead: {:?}", entry, &dead);
            //println!("[{:?}] All: {:?}", entry, &all);
            //println!("[{:?}] Reachable: {:?}", entry, &reachable);
            for block_id in dead {
                let index = (*block_id).into();
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
        let mut dfs = petgraph::visit::Dfs::new(&self.0, BlockId(0).into());
        let mut entries = HashSet::new();
        while let Some(visited) = dfs.next(&self.0) {
            for edge in self.0.edges(visited) {
                if Successor::FunctionDeclaration == *edge.weight() {
                    entries.insert(edge.target().into());
                }
            }
        }
        entries
    }
}
