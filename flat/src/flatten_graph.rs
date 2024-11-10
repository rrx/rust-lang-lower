use super::FlattenModule;
use crate::{BlockGraph, BlockId, ICodeModule, LCode, NodeBuilder as NB, Successor, ValueId};
use anyhow::Result;
use petgraph::visit::EdgeRef;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::Write;

pub fn write_with_indent(f: &mut File, s: &str, depth: usize) -> Result<()> {
    f.write(format!("{:width$}{}", "", s, width = depth * 2).as_bytes())?;
    Ok(())
}

struct GroupValue {
    key: String,
    display: String,
}

impl GroupValue {
    fn new(key: String, display: String) -> Self {
        Self { key, display }
    }

    fn write(&self, f: &mut File, depth: usize) -> Result<()> {
        let s = format!("{}[\"{}\"]\n", self.key, self.display);
        write_with_indent(f, &s, depth)
    }
}

struct Group {
    name: String,
    children: Vec<GroupEnum>,
    body: String,
}

impl Group {
    fn new(name: String, body: String) -> Self {
        Self {
            name,
            body,
            children: vec![],
        }
    }

    fn push_group(&mut self, group: Group) {
        self.children.push(GroupEnum::Group(group));
    }

    fn push_value(&mut self, value: GroupValue) {
        self.children.push(GroupEnum::Value(value));
    }

    fn write(&self, f: &mut File, depth: usize) -> Result<()> {
        write_with_indent(
            f,
            &format!("subgraph {}[\"{}:{}\"]\n", self.name, self.name, self.body),
            depth,
        )?;
        write_with_indent(f, "direction TB\n", depth + 1)?;
        for c in &self.children {
            match c {
                GroupEnum::Group(group) => group.write(f, depth + 1)?,
                GroupEnum::Value(value) => value.write(f, depth + 1)?,
            }
        }
        write_with_indent(f, "end\n", depth)?;
        Ok(())
    }
}

enum GroupEnum {
    Group(Group),
    Value(GroupValue),
}

struct NestedGraph {
    edges: Vec<(ValueId, ValueId)>,
    group: Group,
}

impl NestedGraph {
    fn new() -> Self {
        Self {
            edges: vec![],
            group: Group::new("module".into(), "".into()),
        }
    }

    fn write(&self, f: &mut File) -> Result<()> {
        let start = "\n\
---
config:
   look: classic 
   theme: dark
---
graph TD\n\
";

        write_with_indent(f, start, 0)?;
        self.group.write(f, 0)?;
        for (src, dst) in &self.edges {
            write_with_indent(f, &format!("{} --> {}\n", src, dst), 0)?;
        }
        Ok(())
    }
}

impl FlattenModule {
    pub fn flow_graph(&self, filename: &str, b: &NB) -> Result<()> {
        flow_graph(self, &self.gblocks, filename, b)
    }

    pub fn block_graph(&self, filename: &str, b: &NB) {
        use petgraph::dot::{Config, Dot};
        let g = self.gblocks.0.filter_map(
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
                &|_, (index, _block)| {
                    let block_id: BlockId = index.into();
                    if self.block_map.contains_key(&block_id) {
                        let key = self.get_name(block_id.into()).unwrap();
                        let name = b.labels.r(key);
                        format!(
                            //"label = \"B{:?}:{}\" shape=\"{:?}\"",
                            "label = \"B{:?}:{}\"",
                            index.index(),
                            name,
                            //&block.scope_id,
                        )
                    } else {
                        format!("label = \"B{:?}:?\"", index.index(),)
                    }
                }
            )
        );
        println!("saved graph {:?}", filename);
        //println!("{}", s);
        std::fs::write(filename, s).unwrap();
    }
}

pub fn flow_graph(m: &dyn ICodeModule, gblocks: &BlockGraph, filename: &str, b: &NB) -> Result<()> {
    let entries = gblocks.graph_get_entries();
    let mut ng = NestedGraph::new();

    for entry in entries {
        let fun_block_id: BlockId = entry.into();
        let fun_key = m.get_name(fun_block_id.into()).unwrap();
        let fun_name = b.labels.r(fun_key);
        let mut fun_group = Group::new(fun_name.clone(), "".to_string());
        let mut h = HashMap::new();
        let mut bfs = petgraph::visit::Bfs::new(&gblocks.0, entry.into());
        while let Some(index) = bfs.next(&gblocks.0) {
            for edge in gblocks
                .0
                .edges_directed(index, petgraph::Direction::Outgoing)
            {
                let succ = edge.weight();
                let block_id: BlockId = edge.source().into();
                let target_id: BlockId = edge.target().into();
                let block = gblocks.0.node_weight(index).unwrap();
                let target_block = gblocks.0.node_weight(target_id.into()).unwrap();
                if succ != &Successor::Jump || block.dead || target_block.dead {
                    continue;
                }
                let source_scope_name = format!("S{}", block.scope_id.index());
                let target_scope_name = format!("S{}", target_block.scope_id.index());
                if !h.contains_key(&source_scope_name) {
                    h.insert(source_scope_name.clone(), vec![]);
                }
                if !h.contains_key(&target_scope_name) {
                    h.insert(target_scope_name.clone(), vec![]);
                }
                h.get_mut(&source_scope_name).unwrap().push(block_id);
                h.get_mut(&target_scope_name).unwrap().push(target_id);
            }
        }

        if h.len() == 0 {
            continue;
        }

        let mut track = HashSet::new();

        for (scope_name, values) in h.iter() {
            if values.len() > 0 {
                let mut scope_group = Group::new(scope_name.clone(), "".into());
                for block_id in values {
                    if !track.contains(block_id) {
                        let block_name = format!("{}", block_id);
                        let block_body = if let Some(key) = m.get_name(block_id.into()) {
                            b.labels.r(key)
                        } else {
                            "".into()
                        };

                        let mut block_group = Group::new(block_name, block_body);

                        let mut v = m.resolve_code_offset(block_id.into());
                        loop {
                            let code = m.get_code(v);
                            match code {
                                LCode::Jump(offset) => {
                                    let v_target = m.resolve_code_offset(*offset);
                                    ng.edges.push((v, v_target));
                                }
                                LCode::Branch(c, b1, b2) => {
                                    let v_target = m.resolve_code_offset(*c);
                                    ng.edges.push((v, v_target));
                                    let v_target = m.resolve_code_offset(b1.into());
                                    ng.edges.push((v, v_target));
                                    let v_target = m.resolve_code_offset(b2.into());
                                    ng.edges.push((v, v_target));
                                }
                                LCode::CallValue(offset) => {
                                    let v_target = m.resolve_code_offset(*offset);
                                    ng.edges.push((v, v_target));
                                }
                                LCode::Call(offset) => {
                                    let v_target = m.resolve_code_offset(*offset);
                                    ng.edges.push((v, v_target));
                                }
                                _ => (),
                            }
                            let s = format!("{}:{}", v, m.code_to_string(v, b));
                            block_group.push_value(GroupValue::new(format!("{}", v), s));
                            if let Some(v_next) = m.get_next(v) {
                                ng.edges.push((v, v_next));
                                v = v_next;
                            } else {
                                break;
                            }
                        }
                        scope_group.push_group(block_group);
                        track.insert(block_id);
                    }
                }
                fun_group.push_group(scope_group);
            }
        }
        ng.group.push_group(fun_group);
    }
    let mut f = File::create(filename)?;
    ng.write(&mut f)?;
    Ok(())
}
