use crate::ast::{ParameterNode, Terminator};
use crate::op;
use crate::Diagnostics;
use crate::{AstNode, Extra};
use melior::{
    ir::{block::BlockArgument, Block, ValueLike},
    Context,
};
use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub struct Index(usize);
impl Index {
    pub fn new(offset: usize) -> Self {
        Self(offset)
    }
    pub fn get(&self) -> usize {
        self.0
    }
}

#[derive(Default, Debug)]
pub struct BlockGraph<'c, E> {
    blocks: Vec<Block<'c>>,
    params: Vec<Vec<ParameterNode<E>>>,
    ast: Vec<AstNode<E>>,
    names: HashMap<String, usize>,
    index: HashMap<Index, String>,
    adj: HashMap<Index, HashSet<Index>>,
}

impl<'c, E: Extra> BlockGraph<'c, E> {
    pub fn new() -> Self {
        Self {
            params: vec![],
            blocks: vec![],
            ast: vec![],
            names: HashMap::new(),
            index: HashMap::new(),
            adj: HashMap::new(),
        }
    }

    pub fn dump(&self) {
        for (block_index, block) in self.blocks.iter().enumerate() {
            let index = Index(block_index);
            let name = self.index.get(&index).unwrap();
            println!("\tXBlock: {}, {}", block_index, name);
            for i in 0..block.argument_count() {
                println!(
                    "\t\tXArg: {}, {}, {:?}",
                    block_index,
                    i,
                    block.argument(i).unwrap().r#type(),
                );
            }
        }
    }

    pub fn find_arg(
        &self,
        block_offset: usize,
        arg_offset: usize,
    ) -> Option<BlockArgument<'c, '_>> {
        if self.blocks.len() > 0 {
            let block = self.get_block(Index::new(block_offset));
            Some(block.argument(arg_offset).unwrap())
        } else {
            None
        }
    }

    pub fn take_ast(&mut self) -> Vec<AstNode<E>> {
        self.ast.drain(..).collect()
    }

    pub fn take_blocks(&mut self) -> Vec<Block<'c>> {
        self.blocks.drain(..).collect()
    }

    pub fn first(&self) -> Option<Index> {
        if self.blocks.len() > 0 {
            Some(Index(0))
        } else {
            None
        }
    }

    pub fn get_params(&self, index: Index) -> &Vec<ParameterNode<E>> {
        self.params.get(index.0).unwrap()
    }

    pub fn get_block(&self, index: Index) -> &Block<'c> {
        println!("blocks: {}/{}", index.0, self.blocks.len());
        self.blocks.get(index.0).unwrap()
    }

    pub fn get_block_by_name(&self, name: &str) -> Option<&Block<'c>> {
        if let Some(index) = self.names.get(name) {
            self.blocks.get(*index)
        } else {
            None
        }
    }

    pub fn add_node(
        &mut self,
        context: &'c Context,
        name: &str,
        params: Vec<ParameterNode<E>>,
        ast: AstNode<E>,
        d: &Diagnostics,
    ) -> Index {
        let offset = self.blocks.len();
        let block_args = params
            .iter()
            .map(|a| (op::from_type(context, &a.ty), a.extra.location(context, d)))
            .collect::<Vec<_>>();
        let block = Block::new(&block_args);
        self.blocks.push(block);
        self.params.push(params);
        self.ast.push(ast);
        self.names.insert(name.to_string(), offset);
        self.index.insert(Index(offset), name.to_string());
        Index(offset)
    }

    pub fn add_edge(&mut self, a: Index, b: Index) {
        if self.adj.contains_key(&a) {
            self.adj.get_mut(&a).unwrap().insert(b);
        } else {
            let mut v = HashSet::new();
            v.insert(b);
            self.adj.insert(a, v);
        }
    }

    pub fn build(&mut self) {
        let mut out = vec![];
        for (index, ast) in self.ast.iter().enumerate() {
            let t = ast.node.terminator().unwrap();
            println!("b: {:?}", (index, &t));
            match t {
                Terminator::Jump(name) => {
                    let offset = self.names.get(&name).unwrap();
                    out.push((Index(index), Index(*offset)));
                }
                Terminator::Branch(j1, j2) => {
                    let offset = self.names.get(&j1).unwrap();
                    out.push((Index(index), Index(*offset)));
                    let offset = self.names.get(&j2).unwrap();
                    out.push((Index(index), Index(*offset)));
                }
                Terminator::Return => (),
            };
        }
        for (a, b) in out {
            self.add_edge(a, b);
        }
    }

    pub fn dfs_first(&self) -> Vec<(Index, Vec<Index>)> {
        self.dfs(self.first().unwrap())
    }

    pub fn dfs(&self, start: Index) -> Vec<(Index, Vec<Index>)> {
        let mut stack = vec![];
        let mut dominant_nodes = HashSet::new();
        let mut visited = HashSet::new();
        let mut out = vec![];

        println!("start: {}", self.index.get(&start).unwrap());

        stack.push(start);

        while !stack.is_empty() {
            let current = stack.pop().unwrap();

            if !visited.contains(&current) {
                visited.insert(current);
                println!(
                    "visit {:?}, {:?}",
                    self.index.get(&current).unwrap(),
                    dominant_nodes
                        .iter()
                        .map(|d| { self.index.get(d).unwrap() })
                        .collect::<Vec<_>>()
                );

                dominant_nodes.insert(current);

                let dominant_params = dominant_nodes.iter().map(|i| *i).collect::<Vec<_>>();

                out.push((current, dominant_params));
            }

            for neighbor in self.adj.get(&current).unwrap_or(&HashSet::new()) {
                if !visited.contains(neighbor) {
                    stack.push(*neighbor);
                }
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{AstType, Diagnostics, NodeBuilder, SimpleExtra};
    #[test]
    fn test_block1() {
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let mut b: NodeBuilder<SimpleExtra> = NodeBuilder::new();
        b.enter(file_id, "type.py");
        let context = Context::new();
        let mut g: BlockGraph<SimpleExtra> = BlockGraph::new();

        let ast = b.goto("b");
        let params = vec![b.param("argA", AstType::Int)];
        let ia = g.add_node(&context, "a", params, ast, &d);

        let ast = b.goto("c");
        let params = vec![b.param("argB", AstType::Int)];
        let _ib = g.add_node(&context, "b", params, ast, &d);

        let ast = b.ret(None);
        let params = vec![b.param("argC", AstType::Int)];
        let _ic = g.add_node(&context, "c", params, ast, &d);

        g.build();

        let s = g.dfs(ia);
        for (index, dominants) in s {
            let block = g.blocks.get(index.0).unwrap();
            let params = dominants
                .iter()
                .map(|d| g.params.get(d.0).unwrap())
                .flatten()
                .collect::<Vec<_>>();
            println!(
                "{:?}",
                (
                    index,
                    dominants,
                    block.terminator(),
                    params.iter().map(|p| { &p.name }).collect::<Vec<_>>()
                )
            );
        }
    }
}
