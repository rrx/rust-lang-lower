use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
//use petgraph::visit::EdgeRef;
use crate::{BlockId, LinkId};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum ContinuationFlow {
    Block(BlockId),        // Block
    BlockArg(BlockId, u8), // Block Argument
    Variable(LinkId),
    Jump(LinkId),        // Jump
    JumpArg(LinkId, u8), // Jump Argument
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum FlowEdge {
    LOAD,
    A,
    B,
    C,
    D,
    E,
    F,
    G,
    H,
    I,
    J,
    K,

    L,
    M,
    N,
    O,
    P,
    Q,
    R,
    S,
    T,
    U,
    V,
    W,
    X,
    Y,
    Z,
}

#[derive(Debug)]
pub struct ScopedContinuations {
    pub(crate) g: DiGraph<ContinuationFlow, FlowEdge>,
    pub h: HashMap<ContinuationFlow, NodeIndex>,
}

impl ScopedContinuations {
    pub fn new() -> Self {
        Self {
            g: DiGraph::new(),
            h: HashMap::new(),
        }
    }

    pub fn index(&mut self, flow: ContinuationFlow) -> NodeIndex {
        if let Some(index) = self.h.get(&flow) {
            *index
        } else {
            let index = self.g.add_node(flow);
            self.h.insert(flow, index);
            index
        }
    }

    pub fn connect(&mut self, from: ContinuationFlow, to: ContinuationFlow, edge: FlowEdge) {
        let from = self.index(from);
        let to = self.index(to);
        self.g.add_edge(from, to, edge);
    }

    pub fn find_source_blocks(&self, flow: ContinuationFlow) -> Vec<BlockId> {
        println!("find_source_blocks: {:?}", flow);
        let mut out = vec![];
        let mut stack = vec![flow];
        let mut visited = HashSet::new();
        loop {
            if let Some(flow) = stack.pop() {
                visited.insert(flow);
                if let Some(index) = self.h.get(&flow) {
                    for x in self
                        .g
                        .neighbors_directed(*index, petgraph::Direction::Incoming)
                        .map(|index| self.g[index])
                    {
                        if let ContinuationFlow::Block(block_id) = x {
                            out.push(block_id);
                        } else {
                            if visited.contains(&x) {
                                continue;
                            } else {
                                stack.push(x)
                            }
                        }
                    }
                }
            } else {
                break;
            }
        }
        out
    }

    pub fn find_sink_block(&self, flow: ContinuationFlow) -> Option<ContinuationFlow> {
        println!("find_sink_block: {:?}", flow);
        let index = self.h.get(&flow).unwrap();
        for x in self
            .g
            .neighbors_directed(*index, petgraph::Direction::Outgoing)
            .map(|index| self.g[index])
        {
            println!("x: {:?}", x);
            if let ContinuationFlow::Block(_) = x {
                return Some(x);
            } else if let ContinuationFlow::BlockArg(_, _) = x {
                return Some(x);
            } else {
                return self.find_sink_block(x);
            }
        }
        None
    }
}
