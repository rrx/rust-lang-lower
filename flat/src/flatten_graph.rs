use crate::{
    BlockGraph, BlockId, BlockState, ContinuationFlow, Flatten, ICodeModule, LCode,
    NodeBuilder as NB, Successor, ValueId, VarDefinitionSpace,
};
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
    sources: Vec<(ValueId, ValueId)>,
    group: Group,
}

impl NestedGraph {
    fn new() -> Self {
        Self {
            edges: vec![],
            sources: vec![],
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
        for (src, dst) in &self.sources {
            write_with_indent(f, &format!("{} -.-> {}\n", src, dst), 0)?;
        }
        Ok(())
    }
}

pub fn flow_graph<S: BlockState>(
    m: &dyn ICodeModule,
    gblocks: &BlockGraph<S>,
    filename: &str,
    b: &NB,
) -> Result<()> {
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
                if succ != &Successor::Jump || block.is_dead() || target_block.is_dead() {
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
                        let block = gblocks.get_block(*block_id);
                        if block.is_dead() {
                            continue;
                        }
                        let block_name = format!("{}", block_id);
                        let block_body = if let Some(key) = m.get_name(block_id.into()) {
                            b.labels.r(key)
                        } else {
                            "".into()
                        };

                        let mut block_group = Group::new(block_name, block_body);

                        let maybe_v = m.maybe_resolve_code_offset(block_id.into());

                        if maybe_v.is_none() {
                            continue;
                        }
                        let mut v = maybe_v.unwrap();

                        loop {
                            let entry = m.get_entry(v);
                            let v_decl = match entry.mem {
                                VarDefinitionSpace::Stack(x) => {
                                    let v_source = m.resolve_code_offset(x.into());
                                    ng.sources.push((v, v_source));
                                    Some(v_source)
                                }
                                _ => None,
                            };

                            let code = &entry.code;
                            let s = match code {
                                LCode::Jump(offset) => {
                                    if let Some(v_target) = m.maybe_resolve_code_offset(*offset) {
                                        ng.edges.push((v, v_target));
                                    }
                                    format!("{}:{}", v, m.code_to_string(v, b))
                                }
                                LCode::Switch(link_id, cases) => {
                                    let v_link = m.resolve_code_offset(link_id.into());
                                    ng.sources.push((v, v_link));
                                    for block_id in cases.iter() {
                                        let v_target = m.resolve_code_offset(block_id.into());
                                        ng.edges.push((v, v_target));
                                    }
                                    format!("{}:switch({},{:?})", v, v_link, cases)
                                }
                                LCode::Branch(c, b1, b2) => {
                                    let v_target = m.resolve_code_offset(*c);
                                    ng.sources.push((v, v_target));
                                    let v_target = m.resolve_code_offset(b1.into());
                                    ng.edges.push((v, v_target));
                                    let v_target = m.resolve_code_offset(b2.into());
                                    ng.edges.push((v, v_target));
                                    format!("{}:{}", v, m.code_to_string(v, b))
                                }
                                LCode::CallValue(offset) => {
                                    let v_target = m.resolve_code_offset(*offset);
                                    ng.sources.push((v, v_target));
                                    format!("{}:callvalue({})", v, v_target)
                                }
                                LCode::Load(decl) => {
                                    let v_decl = m.resolve_code_offset(decl.into());
                                    ng.sources.push((v, v_decl));
                                    format!("{}:load({})", v, v_decl)
                                }

                                LCode::Store(decl, source) => {
                                    let v_source = m.resolve_code_offset(source.into());
                                    ng.sources.push((v, v_source));
                                    if let Some(v_decl) = m.maybe_resolve_code_offset(decl.into()) {
                                        ng.sources.push((v, v_decl));
                                        format!("{}:store({},{})", v, v_decl, v_source)
                                    } else {
                                        format!("{}:store(??,{})", v, v_source)
                                    }
                                }
                                LCode::Call(offset) => {
                                    let v_target = m.resolve_code_offset(*offset);
                                    ng.sources.push((v, v_target));
                                    format!("{}:{}", v, m.code_to_string(v, b))
                                }
                                LCode::Arg(num) => {
                                    format!(
                                        "{}:arg({}) => {}",
                                        v,
                                        num,
                                        m.mem_to_string(entry.mem, b)
                                    )
                                }
                                LCode::Label => {
                                    let s_name = if let Some(name) = entry.name {
                                        b.labels.r(name.into())
                                    } else {
                                        "?".to_string()
                                    };
                                    format!("{}:{}:label({})", v, entry.block_id, s_name)
                                }
                                _ => {
                                    if let Some(v_decl) = v_decl {
                                        format!("{}:{} => {}", v, m.code_to_string(v, b), v_decl)
                                    } else {
                                        format!("{}:{}", v, m.code_to_string(v, b))
                                    }
                                }
                            };
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
    println!("saved graph {:?}", filename);
    ng.write(&mut f)?;
    Ok(())
}

impl<S: BlockState> Flatten<S> {
    pub fn cont_graph(&self, filename: &str, b: &NB) {
        let s = format!(
            "{:?}",
            petgraph::dot::Dot::with_attr_getters(
                &self.scoped_continuations.g,
                &[
                    petgraph::dot::Config::EdgeNoLabel,
                    petgraph::dot::Config::NodeNoLabel
                ],
                &|_, edge| {
                    let w = edge.weight();
                    format!("label = \"{:?}\"", w,)
                },
                &|_, (_, c)| {
                    match c {
                        ContinuationFlow::Block(block_id) => {
                            let entry =
                                self.get_entry(self.block_links.get(block_id).unwrap().clone());
                            let s_name = if let Some(name) = entry.name {
                                b.labels.r(name.into())
                            } else {
                                "?".to_string()
                            };
                            format!("label = \"B.{}:{}\"", s_name, block_id)
                        }
                        ContinuationFlow::BlockArg(block_id, arg) => {
                            let entry =
                                self.get_entry(self.block_links.get(block_id).unwrap().clone());
                            let s_name = if let Some(name) = entry.name {
                                b.labels.r(name.into())
                            } else {
                                "?".to_string()
                            };
                            format!("label = \"BA.{}:{}:{}\"", s_name, block_id, arg)
                        }
                        ContinuationFlow::Jump(link_id) => {
                            format!("label = \"JUMP:{}\"", link_id)
                        }
                        ContinuationFlow::JumpArg(link_id, arg) => {
                            format!("label = \"JUMP:{}:{}\"", link_id, arg)
                        }
                        ContinuationFlow::Variable(link_id) => {
                            format!("label = \"VAR:{}\"", link_id)
                        }
                    }
                }
            )
        );
        println!("saved graph {:?}", filename);
        std::fs::write(filename, s).unwrap();
    }
}
