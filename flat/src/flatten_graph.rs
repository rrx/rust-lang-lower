use anyhow::Result;
use super::FlattenModule;
use crate::{
    BlockId,
    ICodeModule, NodeBuilder as NB,
    Successor,
};
use std::collections::{HashMap, HashSet};
use petgraph::visit::EdgeRef;

impl FlattenModule {
    pub fn block_graph2(&self, filename: &str, b: &NB) -> Result<()> {
        use std::fs::File;
        use std::io::Write;

        let mut dfs = petgraph::visit::Dfs::new(&self.gblocks, BlockId(0).into());
        let mut entries = HashSet::new();
        while let Some(visited) = dfs.next(&self.gblocks) {
            for edge in self.gblocks.edges(visited) {
                if Successor::FunctionDeclaration == *edge.weight() {
                    entries.insert(edge.target());
                }
            }
        }

        let mut s = String::new();
        s.push_str(
            "\n\
---
config:
   look: classic 
   theme: dark
---
graph TD\n\
",
        );

        for entry in entries {
            let fun_block_id: BlockId = entry.into();
            let fun_key = self.get_name(fun_block_id.into()).unwrap();
            let fun_name = b.labels.r(fun_key);
            let mut h: HashMap<String, Vec<String>> = HashMap::new();
            let mut edges = vec![];
            let mut bfs = petgraph::visit::Bfs::new(&self.gblocks, entry);
            while let Some(index) = bfs.next(&self.gblocks) {
                for edge in self
                    .gblocks
                    .edges_directed(index, petgraph::Direction::Outgoing)
                {
                    let succ = edge.weight();
                    let block_id: BlockId = edge.source().into();
                    let target_id: BlockId = edge.target().into();
                    let block = self.gblocks.node_weight(index).unwrap();
                    let target_block = self.gblocks.node_weight(target_id.into()).unwrap();
                    if succ != &Successor::Jump || block.dead || target_block.dead {
                        continue;
                    }
                    let source_key = self.get_name(block_id.into()).unwrap();
                    let target_key = self.get_name(target_id.into()).unwrap();
                    let source_name = b.labels.r(source_key);
                    let target_name = b.labels.r(target_key);
                    let source_scope_name = format!("S{}", block.scope_id.index());
                    let target_scope_name = format!("S{}", target_block.scope_id.index());
                    let source = format!("{}[{}:{}]", block_id, block_id, source_name);
                    let target = format!("{}[{}:{}]", target_id, target_id, target_name);
                    //let line = format!("{}[{}:{}] --> {}[{}:{}]", block_id, block_id, source_name, target_id, target_id, target_name);
                    if !h.contains_key(&source_scope_name) {
                        h.insert(source_scope_name.clone(), vec![]);
                    }
                    if !h.contains_key(&target_scope_name) {
                        h.insert(target_scope_name.clone(), vec![]);
                    }
                    h.get_mut(&source_scope_name).unwrap().push(source);
                    h.get_mut(&target_scope_name).unwrap().push(target);
                    edges.push(format!("{} --> {}", block_id, target_id));
                }
            }

            if h.len() == 0 {
                continue;
            }

            s.push_str(&format!("subgraph {}\n", fun_name));

            for (scope_name, values) in h.iter() {
                if values.len() > 0 {
                    s.push_str(&format!("\tsubgraph {}\n", scope_name));
                    for line in values {
                        s.push_str(&format!("\t\t{}\n", &line));
                    }
                    s.push_str("\tend\n");
                }
            }
            s.push_str("end\n");
            for line in edges {
                s.push_str(&format!("{}\n", line));
            }
        }
        println!("{}", s);
        let mut f = File::create(filename)?;
        f.write(s.as_bytes())?;
        Ok(())
    }

    pub fn block_graph(&self, filename: &str, b: &NB) {
        use petgraph::dot::{Config, Dot};
        let g = self.gblocks.filter_map(
            |_n_index, n| Some(n.clone()),
            |_e_index, e| {
                if let Successor::Jump = e {
                    Some(e.clone())
                } else {
                    None
                }
            },
        );
        let num = petgraph::algo::connected_components(&g);
        println!("components: {}", num);

        let s = format!(
            "{:?}",
            Dot::with_attr_getters(
                &g,
                &[Config::NodeNoLabel],
                &|_, _er| String::new(),
                &|_, (index, block)| {
                    let block_id: BlockId = index.into();
                    let key = self.get_name(block_id.into()).unwrap();
                    let name = b.labels.r(key);
                    format!(
                        "label = \"B{:?}:{}\" shape=\"{:?}\"",
                        index.index(),
                        name,
                        &block.scope_id,
                    )
                }
            )
        );
        println!("saved graph {:?}", filename);
        println!("{}", s);
        std::fs::write(filename, s).unwrap();
    }
}
