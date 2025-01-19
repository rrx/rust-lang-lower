use crate::{CodeOffset, LinkId};
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
    pub link: LinkId,
}
impl Node {
    pub fn new_block(name: String, link: LinkId) -> Self {
        Self {
            ty: Shape::Box,
            name,
            link,
        }
    }
}

pub type CFGGraph = DiGraph<Node, ()>;

pub struct CFG {
    pub ids: HashMap<LinkId, NodeIndex>,
    pub g: CFGGraph,
}

impl CFG {
    pub fn new() -> Self {
        Self {
            ids: HashMap::new(),
            g: CFGGraph::new(),
        }
    }

    pub fn leafs(&self, link_id: LinkId) -> Vec<LinkId> {
        let mut out = vec![];
        let mut bfs = Bfs::new(&self.g, *self.ids.get(&link_id).unwrap());
        while let Some(nx) = bfs.next(&self.g) {
            let outgoing = self
                .g
                .edges_directed(nx, petgraph::Direction::Outgoing)
                .collect::<Vec<_>>();
            if outgoing.len() == 0 {
                let node = self.g.node_weight(nx).unwrap();
                out.push(node.link);
            }
        }
        out
    }

    pub fn blocks(&self, link_id: LinkId) -> Vec<LinkId> {
        let mut blocks = vec![];
        let mut bfs = Bfs::new(&self.g, *self.ids.get(&link_id).unwrap());
        while let Some(nx) = bfs.next(&self.g) {
            let node = self.g.node_weight(nx).unwrap();
            blocks.push(node.link);
        }
        blocks
    }
}
