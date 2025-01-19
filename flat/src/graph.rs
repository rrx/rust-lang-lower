use crate::BlockId;
use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use petgraph::visit::Bfs;
use std::collections::HashMap;

#[derive(Debug)]
pub enum Shape {
    Box,
    Ellipsis,
}
impl Shape {
    pub fn to_string(&self) -> &str {
        match self {
            Self::Box => "box",
            Self::Ellipsis => "circle",
        }
    }
}
#[derive(Debug)]
pub struct Node {
    pub ty: Shape,
    pub name: String,
    pub block_id: BlockId,
}

impl Node {
    pub fn new_block(name: String, block_id: BlockId) -> Self {
        Self {
            ty: Shape::Box,
            name,
            block_id,
        }
    }
}

pub type CFGGraph = DiGraph<Node, ()>;

pub struct CFG {
    pub ids: HashMap<BlockId, NodeIndex>,
    pub g: CFGGraph,
}

impl CFG {
    pub fn new() -> Self {
        Self {
            ids: HashMap::new(),
            g: CFGGraph::new(),
        }
    }

    pub fn leafs(&self, block_id: BlockId) -> Vec<BlockId> {
        let mut out = vec![];
        let mut bfs = Bfs::new(&self.g, *self.ids.get(&block_id).unwrap());
        while let Some(nx) = bfs.next(&self.g) {
            let outgoing = self
                .g
                .edges_directed(nx, petgraph::Direction::Outgoing)
                .collect::<Vec<_>>();
            if outgoing.len() == 0 {
                let node = self.g.node_weight(nx).unwrap();
                out.push(node.block_id);
            }
        }
        out
    }

    pub fn blocks(&self, block_id: BlockId) -> Vec<BlockId> {
        let mut blocks = vec![];
        let mut bfs = Bfs::new(&self.g, *self.ids.get(&block_id).unwrap());
        while let Some(nx) = bfs.next(&self.g) {
            let node = self.g.node_weight(nx).unwrap();
            blocks.push(node.block_id);
        }
        blocks
    }
}
