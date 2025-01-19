use crate::{
    BlockId, CodeOffset, ContinuationFlow, Flatten, FlattenInner, LCode, LinkId, Module, Node,
    NodeBuilder as NB, NodeBuilder, Successor, ValueId, VarDefinitionSpace, CFG,
};
use anyhow::Result;
use petgraph::visit::EdgeRef;
use std::collections::{HashMap, HashSet, VecDeque};
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

impl Flatten<Module> {
    pub fn blocks<T: Copy + Into<CodeOffset>>(
        &self,
        block_id: BlockId,
        offset: T,
        b: &NodeBuilder,
    ) -> Vec<CodeOffset> {
        let cfg = self.get_cfg(block_id, b);
        let link_id = self.link(offset);
        cfg.blocks(link_id)
    }

    fn get_cfg(&self, block_id: BlockId, b: &NodeBuilder) -> CFG {
        let entry_link_id = self.link(block_id);
        self.get_graph(entry_link_id, Some(Successor::BlockScope), b)
    }

    fn get_graph(&self, entry_link_id: LinkId, scope: Option<Successor>, b: &NodeBuilder) -> CFG {
        let mut cfg = CFG::new();

        let mut stack = VecDeque::new();
        stack.push_back(entry_link_id);

        loop {
            if let Some(link_id) = stack.pop_front() {
                if cfg.ids.contains_key(&link_id) {
                    continue;
                }
                let name = self.code_to_string(link_id, b);
                let c = cfg.g.add_node(Node::new_block(name, link_id.into()));
                cfg.ids.insert(link_id, c);
                for (succ_type, next_code_offset) in self.get_block_successors(link_id) {
                    if let Some(v) = self.blocks.maybe_link(next_code_offset) {
                        if scope.is_none() || scope == Some(succ_type) {
                            stack.push_back(v);
                        }
                    }
                }
            } else {
                break;
            }
        }

        for entry_id in cfg.ids.keys() {
            //let block = self.env.get_block(*entry_id);
            let id = cfg.ids.get(entry_id).unwrap();
            for (succ_type, next_code_offset) in self.get_block_successors(*entry_id) {
                if let Successor::BlockScope = succ_type {
                    if let Some(v) = self.blocks.maybe_link(next_code_offset) {
                        let child_id = cfg.ids.get(&v).unwrap();
                        cfg.g.add_edge(*id, *child_id, ());
                    }
                }
            }
        }
        cfg
    }

    pub fn flow_graph(&self, filename: &str, b: &NB) -> Result<()> {
        let entries = self.blocks.graph_get_entries();
        let mut ng = NestedGraph::new();

        let mut scope_group = Group::new("static scope".into(), "".into());
        let static_block_id = BlockId::new(0);
        let module = self.blocks.maybe_value(static_block_id).unwrap();
        let static_block = self.blocks.get_block(static_block_id);
        let links: Vec<_> = static_block.iter().collect();
        let mut block_group = Group::new("static block".into(), "".into());
        block_group.push_value(GroupValue::new("V0".into(), "module".into()));
        for v in links {
            let value_id = self.value(v);
            let entry = self.get_entry(v);
            if let LCode::Val(_) = entry.code {
                ng.sources.push((module, value_id));
                let s = format!("{}:{}", v, self.code_to_string(v, b));
                block_group.push_value(GroupValue::new(format!("{}", v), s));
            } else {
                continue;
            }
        }
        scope_group.push_group(block_group);
        ng.group.push_group(scope_group);

        for entry in entries {
            let fun_block_id: BlockId = entry.into();
            let fun_key = self.get_name(fun_block_id.into()).unwrap();
            let fun_name = b.labels.r(fun_key);
            let mut fun_group = Group::new(fun_name.clone(), "".to_string());
            let mut h = HashMap::new();
            let g = self.blocks.block_graph();
            let mut bfs = petgraph::visit::Bfs::new(g, entry.into());
            while let Some(index) = bfs.next(g) {
                for edge in g.edges_directed(index, petgraph::Direction::Outgoing) {
                    let succ = edge.weight();
                    let block_id: BlockId = edge.source().into();
                    let target_id: BlockId = edge.target().into();
                    let block = g.node_weight(index).unwrap();
                    let target_block = g.node_weight(target_id.into()).unwrap();
                    if succ != &Successor::Jump || block.is_dead() || target_block.is_dead() {
                        continue;
                    }
                    let source_scope_name = format!("S{}", block.scope().index());
                    let target_scope_name = format!("S{}", target_block.scope().index());
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
                            let block = self.blocks.get_block(*block_id);
                            if block.is_dead() {
                                continue;
                            }
                            let block_name = format!("{}", block_id);
                            let block_body = if let Some(key) = self.get_name(block_id.into()) {
                                b.labels.r(key)
                            } else {
                                "".into()
                            };

                            let mut block_group = Group::new(block_name, block_body);

                            let mut last = None;
                            for link_id in block.iter() {
                                let entry = self.get_entry(link_id);
                                let v = entry.value_id.unwrap();
                                let code = &entry.code;
                                let v_decl = match entry.mem {
                                    VarDefinitionSpace::Stack(x) => {
                                        let v_source = self.value(x);
                                        ng.sources.push((v, v_source));
                                        Some(v_source)
                                    }
                                    _ => None,
                                };

                                // connect sequential values
                                if let Some(v_last) = last {
                                    ng.edges.push((v_last, v));
                                }
                                last = Some(v);

                                let s = match code {
                                    LCode::Jump(offset) => {
                                        if let Some(v_target) = self.blocks.maybe_value(offset) {
                                            ng.edges.push((v, v_target));
                                        }
                                        format!("{}:{}", v, self.code_to_string(link_id, b))
                                    }
                                    LCode::Switch(link_id, cases) => {
                                        let v_link = self.value(*link_id);
                                        ng.sources.push((v, v_link));
                                        for (_index, block_id) in cases.iter() {
                                            let v_target = self.value(block_id);
                                            ng.edges.push((v, v_target));
                                        }
                                        format!("{}:switch({},{:?})", v, v_link, cases)
                                    }
                                    LCode::Branch(c, b1, b2) => {
                                        let v_target = self.value(c);
                                        ng.sources.push((v, v_target));
                                        let v_target = self.value(b1);
                                        ng.edges.push((v, v_target));
                                        let v_target = self.value(b2);
                                        ng.edges.push((v, v_target));
                                        format!("{}:{}", v, self.code_to_string(link_id, b))
                                    }
                                    LCode::CallValue(offset) => {
                                        let v_target = self.value(offset);
                                        ng.sources.push((v, v_target));
                                        format!("{}:callvalue({})", v, v_target)
                                    }
                                    LCode::Load(decl) => {
                                        let v_decl = self.value(decl);
                                        ng.sources.push((v, v_decl));
                                        format!("{}:load({})", v, v_decl)
                                    }

                                    LCode::Store(decl, source) => {
                                        let v_source = self.value(source);
                                        ng.sources.push((v, v_source));
                                        if let Some(v_decl) = self.blocks.maybe_value(decl) {
                                            ng.sources.push((v, v_decl));
                                            format!("{}:store({},{})", v, v_decl, v_source)
                                        } else {
                                            format!("{}:store(??,{})", v, v_source)
                                        }
                                    }
                                    LCode::Call(offset) => {
                                        let v_target = self.value(offset);
                                        ng.sources.push((v, v_target));
                                        format!("{}:{}", v, self.code_to_string(link_id, b))
                                    }
                                    LCode::Arg(num) => {
                                        format!(
                                            "{}:arg({}) => {}",
                                            v,
                                            num,
                                            self.mem_to_string(entry.mem, b)
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
                                            format!(
                                                "{}:{} => {}",
                                                v,
                                                self.code_to_string(link_id, b),
                                                v_decl
                                            )
                                        } else {
                                            format!("{}:{}", v, self.code_to_string(link_id, b))
                                        }
                                    }
                                };
                                block_group.push_value(GroupValue::new(format!("{}", v), s));
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

    pub fn save_graph(&self, filename: &str, b: &NB) {
        use petgraph::dot::{Config, Dot};
        let value_id = self.link(self.blocks.static_block_id());

        let cfg = self.get_graph(value_id, None, b);
        let s = format!(
            "{:?}",
            Dot::with_attr_getters(
                &cfg.g,
                &[Config::EdgeNoLabel, Config::NodeNoLabel],
                &|_, _er| String::new(),
                &|_, (_index, data)| {
                    match data.code_offset {
                        CodeOffset::Link(link_id) => {
                            format!(
                                //"label = \"L{}:{}\" shape=\"{:?}\"",
                                "label = \"{}:{}\"",
                                link_id,
                                &data.name,
                                //&data.ty.to_string()
                            )
                        }
                        CodeOffset::Value(value_id) => {
                            format!(
                                //"label = \"V{}:{}\" shape={:?}",
                                "label = \"{}:{}\"",
                                value_id,
                                &data.name,
                                //&data.ty.to_string()
                            )
                        }
                        CodeOffset::Block(block_id) => {
                            format!(
                                //"label = \"B{}:{}\" shape={:?}",
                                "label = \"{}:{}\"",
                                block_id,
                                &data.name,
                                //&data.ty.to_string()
                            )
                        }
                    }
                }
            )
        );
        println!("saved graph {:?}", filename);
        std::fs::write(filename, s).unwrap();
    }

    pub fn block_graph(&self, filename: &str, _b: &NB) {
        use petgraph::dot::{Config, Dot};
        let g = self.blocks.subgraph_jumps();

        //let num = petgraph::algo::connected_components(&g);
        //println!("components: {}", num);

        let s = format!(
            "{:?}",
            Dot::with_attr_getters(
                &g,
                &[Config::NodeNoLabel],
                &|_, _er| String::new(),
                &|_, (index, _block)| {
                    let block_id: BlockId = BlockId::new(index.index());
                    let block = self.blocks.get_block(block_id);
                    if block.is_dead() {
                        // block marked dead
                        format!("label = \"B{:?}:dead\"", index.index(),)
                    } else {
                        if let Some(v) = self.blocks.maybe_value(block_id) {
                            let link_id = self.state.values.get(v);
                            let entry = self.get_entry(link_id);
                            if entry.value_id.is_some() {
                                let v = self.value(block_id);
                                // block found
                                format!("label = \"B{:?}:{}\"", index.index(), v)
                            } else {
                                // block is not included in our list
                                format!("label = \"B{:?}:oob\"", index.index(),)
                            }
                        } else {
                            // block not found
                            // this should never happen
                            // it does happen in error cases, like unclaimed labels
                            format!("label = \"B{:?}:?\"", index.index(),)
                            //unreachable!();
                        }
                    }
                }
            )
        );
        println!("saved graph {:?}", filename);
        std::fs::write(filename, s).unwrap();
    }
}

impl FlattenInner {
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
                            let link_id = self.blocks.link(block_id);
                            let entry = self.get_entry(link_id);
                            let s_name = if let Some(name) = entry.name {
                                b.labels.r(name.into())
                            } else {
                                "?".to_string()
                            };
                            format!("label = \"B.{}:{}\"", s_name, block_id)
                        }
                        ContinuationFlow::BlockArg(block_id, arg) => {
                            let link_id = self.blocks.link(block_id);
                            let entry = self.get_entry(link_id);
                            let s_name = if let Some(name) = entry.name {
                                b.labels.r(name.into())
                            } else {
                                "?".to_string()
                            };
                            format!("label = \"BA.{}:{}:{}\"", s_name, block_id, arg)
                        }
                        ContinuationFlow::Jump(link_id) => {
                            if let Some(v) = self.blocks.maybe_value(link_id) {
                                format!("label = \"JUMP:{}\"", v)
                            } else {
                                format!("label = \"JUMP:?{}\"", link_id)
                            }
                        }
                        ContinuationFlow::JumpArg(link_id, arg) => {
                            if let Some(v) = self.blocks.maybe_value(link_id) {
                                format!("label = \"JUMP:{}:{}\"", v, arg)
                            } else {
                                format!("label = \"JUMP:?{}:{}\"", link_id, arg)
                            }
                        }
                        ContinuationFlow::Variable(link_id) => {
                            if let Some(v) = self.blocks.maybe_value(link_id) {
                                format!("label = \"VAR:{}\"", v)
                            } else {
                                format!("label = \"VAR:?\"")
                            }
                        }
                    }
                }
            )
        );
        println!("saved graph {:?}", filename);
        std::fs::write(filename, s).unwrap();
    }

    pub fn save_graph(&self, filename: &str) {
        let s = format!(
            "{:?}",
            petgraph::dot::Dot::with_attr_getters(
                self.blocks.block_graph(),
                &[
                    petgraph::dot::Config::EdgeNoLabel,
                    petgraph::dot::Config::NodeNoLabel
                ],
                &|_, edge| {
                    let w = edge.weight();
                    format!("label = \"{:?}\"", w,)
                },
                &|_, (index, block)| {
                    let block_id: BlockId = index.into();
                    format!("label = \"{}:{}\"", block_id, block.len())
                }
            )
        );
        println!("saved graph {:?}", filename);
        std::fs::write(filename, s).unwrap();
    }

    pub fn gen_scope_graph(&self, filename: &str) {
        use petgraph::dot::{Config, Dot};
        let s = format!(
            "{:?}",
            Dot::with_attr_getters(
                &self.blocks.sg,
                &[Config::EdgeNoLabel, Config::NodeNoLabel],
                &|_, _er| String::new(),
                &|_, (index, scope)| {
                    format!(
                        //"label = \"S{}:{:?}\" shape=\"{:?}\"",
                        "label = \"S{}:{:?}\"",
                        index.index(),
                        &scope.scope_type,
                        //&scope.scope_type
                    )
                }
            )
        );
        println!("saved graph {:?}", filename);
        std::fs::write(filename, s).unwrap();
    }
}
