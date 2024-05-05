use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use petgraph::visit::Bfs;
use std::collections::HashMap;
use std::collections::VecDeque;

use compile_core::NodeBuilder;

use crate::{Blockify, CodeOffset, Successor, ValueId};

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

impl Blockify {
    /*
    pub fn save_graph(&self, filename: &str, b: &NodeBuilder) {
        use petgraph::dot::{Config, Dot};
        let cfg = self.get_graph(ValueId(0), None, b);
        let s = format!(
            "{:?}",
            Dot::with_attr_getters(
                &cfg.g,
                &[Config::EdgeNoLabel, Config::NodeNoLabel],
                &|_, _er| String::new(),
                &|_, (_index, data)| {
                    match data.code_offset {
                        CodeOffset::Value(value_id) => {
                            format!(
                                "label = \"V{}:{}\" shape={:?}",
                                value_id.index(),
                                &data.name,
                                &data.ty.to_string()
                            )
                        }
                        CodeOffset::Block(block_id) => {
                            format!(
                                "label = \"B{}:{}\" shape={:?}",
                                block_id.index(),
                                &data.name,
                                &data.ty.to_string()
                            )
                        }
                    }
                }
            )
        );
        println!("saved graph {:?}", filename);
        println!("{}", s);
        std::fs::write(filename, s).unwrap();
    }
    */

    pub fn get_cfg(&self, entry_id: ValueId, b: &NodeBuilder) -> CFG {
        self.get_graph(entry_id, Some(Successor::BlockScope), b)
    }

    pub fn get_graph(&self, entry_id: ValueId, scope: Option<Successor>, b: &NodeBuilder) -> CFG {
        let mut cfg = CFG::new();

        let mut stack = VecDeque::new();
        stack.push_back(entry_id);

        loop {
            if let Some(entry_id) = stack.pop_front() {
                if cfg.ids.contains_key(&entry_id) {
                    continue;
                }
                let name = self.code_to_string(entry_id, b);
                let c = cfg.g.add_node(Node::new_block(name, entry_id.into()));
                cfg.ids.insert(entry_id, c);

                let block = self.env.get_block(entry_id);
                for (succ_type, next_code_offset) in block.succ.iter() {
                    let v = self.env.resolve_code_offset(*next_code_offset);
                    if scope.is_none() || scope == Some(*succ_type) {
                        stack.push_back(v);
                    }
                }
            } else {
                break;
            }
        }

        for entry_id in cfg.ids.keys() {
            let block = self.env.get_block(*entry_id);
            let id = cfg.ids.get(entry_id).unwrap();
            for (succ_type, next_code_offset) in block.succ.iter() {
                if let Successor::BlockScope = succ_type {
                    let v = self.env.resolve_code_offset(*next_code_offset);
                    let child_id = cfg.ids.get(&v).unwrap();
                    cfg.g.add_edge(*id, *child_id, ());
                }
            }
        }
        cfg
    }
}
