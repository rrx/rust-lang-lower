use crate::ast::{AssignTarget, Ast, AstNode, AstType, Extra, Literal, ParameterNode, Terminator};
use petgraph::algo::dominators::simple_fast;
use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct CFGIndex(NodeIndex, usize);

#[derive(Debug, Clone, Copy)]
pub enum NodeType {
    Module,
    Block,
}

#[derive(Debug)]
pub struct GData<E> {
    name: String,
    node_type: NodeType,
    params: Vec<ParameterNode<E>>,
    names: HashMap<String, CFGIndex>,
}
impl<E: Extra> GData<E> {
    pub fn new(name: &str, node_type: NodeType, params: Vec<ParameterNode<E>>) -> Self {
        Self {
            name: name.to_string(),
            node_type,
            params,
            names: HashMap::new(),
        }
    }
    pub fn add_symbol(&mut self, name: &str, index: CFGIndex) {
        self.names.insert(name.to_string(), index);
    }
}

#[derive(Debug)]
pub struct SymbolData {
    ty: AstType,
}

impl SymbolData {
    pub fn new(ty: AstType) -> Self {
        Self { ty }
    }
}

#[derive(Default)]
pub struct CFG<E> {
    root: NodeIndex,
    index_count: usize,
    g: DiGraph<GData<E>, ()>,
    names: HashMap<String, NodeIndex>,
    symbols: HashMap<CFGIndex, SymbolData>,
}

impl<E: Extra> CFG<E> {
    pub fn new(module_name: &str) -> Self {
        let g = DiGraph::new();
        let data = GData::new(module_name, NodeType::Module, vec![]);

        let mut cfg = Self {
            // dummy
            root: NodeIndex::new(0),
            index_count: 0,
            g,
            names: HashMap::new(),
            symbols: HashMap::new(),
        };
        cfg.add_block(data);
        cfg
    }

    pub fn add_symbol(&mut self, index: CFGIndex, data: SymbolData) {
        self.symbols.insert(index, data);
    }

    pub fn fresh_index(&mut self, block_index: NodeIndex) -> CFGIndex {
        let index = CFGIndex(block_index, self.index_count);
        self.index_count += 1;
        index
    }

    pub fn add_block(&mut self, data: GData<E>) -> NodeIndex {
        let name = data.name.clone();
        let index = self.g.add_node(data);
        self.names.insert(name, index);
        index
    }

    pub fn add_edge(&mut self, a: &str, b: &str) {
        println!("adding {}, {}", a, b);
        let index_a = self.names.get(a).unwrap();
        let index_b = self.names.get(b).unwrap();
        self.g.add_edge(*index_a, *index_b, ());
    }

    pub fn index(&self, name: &str) -> Option<NodeIndex> {
        self.names.get(name).cloned()
    }

    pub fn data_by_index(&self, index: NodeIndex) -> Option<&GData<E>> {
        self.g.node_weight(index)
    }

    pub fn data_mut_by_index(&mut self, index: NodeIndex) -> Option<&mut GData<E>> {
        self.g.node_weight_mut(index)
    }

    pub fn data_mut_by_name(&mut self, name: &str) -> Option<&mut GData<E>> {
        if let Some(index) = self.names.get(name) {
            self.data_mut_by_index(*index)
        } else {
            None
        }
    }

    pub fn save_graph(&self, filename: &str) {
        use petgraph::dot::{Config, Dot};
        let s = format!(
            "{:?}",
            Dot::with_attr_getters(
                &self.g,
                &[Config::EdgeNoLabel, Config::NodeNoLabel],
                &|_, _er| String::new(),
                &|_, (_index, data)| format!("label = \"{}\"", data.name),
            )
        );
        std::fs::write(filename, s).unwrap();
    }

    pub fn type_from_expr(&self, index: NodeIndex, expr: &AstNode<E>) -> AstType {
        match &expr.node {
            Ast::Literal(x) => match x {
                Literal::Int(_) => AstType::Int,
                Literal::Float(_) => AstType::Float,
                Literal::Bool(_) => AstType::Bool,
                Literal::Index(_) => AstType::Index,
                Literal::String(_) => AstType::String,
            },
            Ast::Identifier(name) => {
                // infer type from the operation
                let index = self.name_in_scope(index, name).unwrap();
                self.symbols.get(&index).unwrap().ty.clone()
            }
            Ast::Call(_f, _args, ty) => ty.clone(),

            _ => unreachable!("{:?}", expr),
        }
    }

    pub fn name_in_scope(&self, index: NodeIndex, name: &str) -> Option<CFGIndex> {
        let dom = simple_fast(&self.g, self.root)
            .dominators(index)
            .unwrap()
            .collect::<Vec<_>>();
        println!("dom: {:?} => {:?}", index, dom);
        for i in dom.into_iter().rev() {
            let data = self.data_by_index(i).unwrap();
            let result = data.names.get(name);
            if let Some(r) = result {
                return Some(*r);
            }
        }
        None
    }

    pub fn lower(&mut self, expr: AstNode<E>, stack: &mut Vec<NodeIndex>) {
        println!("lower: {:?}, {:?}", expr.node, stack);
        match expr.node {
            Ast::Sequence(exprs) => {
                for expr in exprs {
                    self.lower(expr, stack);
                }
            }
            Ast::Block(name, params, body) => {
                unreachable!();
                let current = stack.last().unwrap().clone();
                let data = GData::new(&name, NodeType::Block, params);
                let index = self.add_block(data);
                self.g.add_edge(current, index, ());
                let t = body.node.terminator().unwrap();
                self.lower(*body, stack);
            }
            Ast::Builtin(_, _) => (),
            Ast::Literal(_) => (),
            Ast::Return(_) => {}
            Ast::Identifier(name) => {
                let current = stack.last().unwrap();
                let dom = simple_fast(&self.g, self.root)
                    .dominators(*current)
                    .unwrap()
                    .collect::<Vec<_>>();
                println!("X: {:?}", dom);
                let r = self.name_in_scope(*current, &name).unwrap();
                let symbol_data = self.symbols.get(&r).unwrap();
                println!("lookup identifier: {}, {:?}, {:?}", name, r, symbol_data.ty);
                //self.dump_scope(*current);
            }
            Ast::Goto(label) => {
                //self.save_graph("out.dot");
                let current = stack.last().unwrap();
                let index = self.index(&label).unwrap();
                self.g.add_edge(*current, index, ());
            }
            Ast::Mutate(target, expr) => match target.node {
                Ast::Identifier(name) => {
                    let current = stack.last().unwrap();
                    let r = self.name_in_scope(*current, &name).unwrap();
                    let symbol_data = self.symbols.get(&r).unwrap();
                    println!("lookup identifier: {}, {:?}, {:?}", name, r, symbol_data.ty);
                    self.lower(*expr, stack);
                }
                _ => unimplemented!(),
            },
            Ast::Assign(target, expr) => {
                match target {
                    AssignTarget::Identifier(name) | AssignTarget::Alloca(name) => {
                        let block_index = stack.last().unwrap();
                        let index = self.fresh_index(*block_index);
                        let ty = self.type_from_expr(*block_index, &expr);
                        let data = self.data_mut_by_index(*stack.last().unwrap()).unwrap();
                        let symbol_data = SymbolData::new(ty);
                        data.add_symbol(&name, index);
                        self.symbols.insert(index, symbol_data);
                    }
                }
                self.lower(*expr, stack);
            }
            Ast::Definition(mut def) => {
                def = def.normalize();
                let function_name = def.name.clone();
                let current = stack.last().unwrap().clone();
                let data = GData::new(&def.name, NodeType::Block, def.params);
                let index = self.add_block(data);
                stack.push(index);
                self.g.add_edge(current, index, ());

                if let Some(body) = def.body {
                    let mut edges = vec![];
                    let blocks = body.try_seq().unwrap();
                    let mut exprs = vec![];
                    for (i, b) in blocks.into_iter().enumerate() {
                        if let Ast::Block(name, params, expr) = b.node {
                            // connect the first block to the function
                            if i == 0 {
                                edges.push((function_name.clone(), name.clone()));
                            }
                            let data = GData::new(&name, NodeType::Block, params);
                            let index = self.add_block(data);
                            exprs.push((index, *expr));
                        } else {
                            unreachable!()
                        }
                    }
                    for (a, b) in edges {
                        self.add_edge(&a, &b);
                    }

                    for (index, expr) in exprs {
                        stack.push(index);
                        self.dump_scope(index);
                        self.lower(expr, stack);
                        stack.pop();
                    }
                }
                stack.pop().unwrap();
            }
            Ast::Global(name, body) => {
                let block_index = self.index("module").unwrap();
                let index = self.fresh_index(block_index);
                let ty = self.type_from_expr(block_index, &body);
                let data = self.data_mut_by_index(block_index).unwrap();
                let symbol_data = SymbolData::new(ty);
                data.add_symbol(&name, index);
                self.symbols.insert(index, symbol_data);
                self.lower(*body, stack);
            }
            _ => unreachable!("{:?}", expr.node),
        }
    }

    pub fn dump_scope(&self, index: NodeIndex) {
        let dom = simple_fast(&self.g, self.root)
            .dominators(index)
            .unwrap()
            .collect::<Vec<_>>();
        println!("dom: {:?} => {:?}", index, dom);
        for i in dom.into_iter().rev() {
            let data = self.data_by_index(i).unwrap();
            println!("\t{:?}: {}, {:?}", i, data.name, data.names.keys());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{AstType, SimpleExtra};
    use crate::lower::tests::gen_block;
    use crate::{Diagnostics, NodeBuilder};

    #[test]
    fn test_cfg_block() {
        let mut cfg: CFG<SimpleExtra> = CFG::new("module");
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let b = NodeBuilder::new(file_id, "type.py");
        let ast = gen_block(&b);
        let mut stack = vec![cfg.root];
        cfg.lower(ast, &mut stack);
        assert_eq!(1, stack.len());
        cfg.save_graph("out.dot");
    }

    #[test]
    fn test_cfg() {
        let mut cfg: CFG<SimpleExtra> = CFG::new("module");
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let b = NodeBuilder::new(file_id, "type.py");

        (0..8).into_iter().for_each(|i| {
            let p = b.param(&format!("p{}", i), AstType::Int);
            let mut data = GData::new(&format!("b{}", i), NodeType::Module, vec![p]);
            cfg.add_block(data);
            //data.add_symbol(&format!("scope{}", i), cfg.fresh_index());
        });

        cfg.add_edge("module", "b0");
        //cfg.g.add_edge(is[0], is[1], ());
        cfg.add_edge("b0", "b1");
        //cfg.g.add_edge(is[1], is[2], ());
        cfg.add_edge("b1", "b2");
        //cfg.g.add_edge(is[2], is[1], ());
        cfg.add_edge("b2", "b1");
        //cfg.g.add_edge(is[1], is[3], ());
        cfg.add_edge("b1", "b3");
        //cfg.g.add_edge(is[3], is[4], ());
        cfg.add_edge("b3", "b4");
        //cfg.g.add_edge(is[3], is[5], ());
        cfg.add_edge("b3", "b5");
        //cfg.g.add_edge(is[4], is[3], ());
        cfg.add_edge("b4", "b3");
        //cfg.g.add_edge(is[5], is[6], ());
        cfg.add_edge("b5", "b6");
        //cfg.g.add_edge(is[4], is[6], ());
        cfg.add_edge("b4", "b6");
        //cfg.g.add_edge(is[6], is[7], ());
        cfg.add_edge("b6", "b7");

        (0..8).into_iter().for_each(|i| {
            let name = format!("b{}", i);
            let index = cfg.index(&name).unwrap();
            let im = simple_fast(&cfg.g, cfg.root).immediate_dominator(index);
            let w = cfg.g.node_weight(index).unwrap();
            println!("node {} has immediate dominator {:?}", w.name, im);
        });
        (0..8).into_iter().for_each(|i| {
            let name = format!("b{}", i);
            let index = cfg.index(&name).unwrap();
            let im = simple_fast(&cfg.g, cfg.root)
                .immediately_dominated_by(index)
                .collect::<Vec<_>>();
            let w = cfg.g.node_weight(index).unwrap();
            println!("node {} is the immediate dominator of {:?}", w.name, im);
        });
        (0..8).into_iter().for_each(|i| {
            let name = format!("b{}", i);
            let index = cfg.index(&name).unwrap();
            let im = simple_fast(&cfg.g, cfg.root)
                .strict_dominators(index)
                .unwrap()
                .collect::<Vec<_>>();
            let w = cfg.g.node_weight(index).unwrap();
            println!("node {} has strict dominators {:?}", w.name, im);
        });
        (0..8).into_iter().for_each(|i| {
            let name = format!("b{}", i);
            let index = cfg.index(&name).unwrap();
            let im = simple_fast(&cfg.g, cfg.root)
                .dominators(index)
                .unwrap()
                .collect::<Vec<_>>();
            let w = cfg.g.node_weight(index).unwrap();
            println!("node {} has dominators {:?}", w.name, im);
        });
        cfg.save_graph("out.dot");
    }
}
