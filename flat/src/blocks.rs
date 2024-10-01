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
    pub(super) num_ret_args: HashSet<usize>,
    pub(super) ret_types: HashSet<AstType>,
    pub(super) next: Option<BlockId>,
    pub(super) links: Vec<LinkId>,
}

impl IRBlock {
    pub fn new(scope_id: ScopeId) -> Self {
        Self {
            scope_id,
            dead: false,
            //ast,
            links: vec![],
            next: None,
            num_ret_args: HashSet::new(),
            ret_types: HashSet::new(),
        }
    }

    pub fn next(&mut self, next_block_id: BlockId) {
        self.next = Some(next_block_id);
    }

    pub fn push(&mut self, link_id: LinkId) {
        self.links.push(link_id);
    }

    pub fn last(&self) -> Option<LinkId> {
        self.links.last().cloned()
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
}
