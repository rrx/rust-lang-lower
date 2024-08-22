use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use petgraph::visit::Bfs;
use std::collections::HashMap;
use std::collections::VecDeque;

use crate::NodeBuilder;

use crate::{BlockId, Blockify, CodeOffset, ICodeModule, Successor, ValueId};

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
    pub code_offset: CodeOffset,
}
impl Node {
    pub fn new_block(name: String, code_offset: CodeOffset) -> Self {
        Self {
            ty: Shape::Box,
            name,
            code_offset,
        }
    }
}

pub type CFGGraph = DiGraph<Node, ()>;

pub struct CFG {
    pub ids: HashMap<ValueId, NodeIndex>,
    pub g: CFGGraph,
}

impl CFG {
    pub fn new() -> Self {
        Self {
            ids: HashMap::new(),
            g: CFGGraph::new(),
        }
    }

    pub fn leafs(&self, entry_id: ValueId) -> Vec<CodeOffset> {
        let mut out = vec![];
        let mut bfs = Bfs::new(&self.g, *self.ids.get(&entry_id).unwrap());
        while let Some(nx) = bfs.next(&self.g) {
            let outgoing = self
                .g
                .edges_directed(nx, petgraph::Direction::Outgoing)
                .collect::<Vec<_>>();
            if outgoing.len() == 0 {
                let node = self.g.node_weight(nx).unwrap();
                out.push(node.code_offset);
            }
        }
        out
    }

    pub fn blocks(&self, entry_id: ValueId) -> Vec<CodeOffset> {
        let mut blocks = vec![];
        let mut bfs = Bfs::new(&self.g, *self.ids.get(&entry_id).unwrap());
        while let Some(nx) = bfs.next(&self.g) {
            let node = self.g.node_weight(nx).unwrap();
            blocks.push(node.code_offset);
        }
        blocks
    }
}
