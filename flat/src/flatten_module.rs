use compile_core::{AstType, LinkOptions, Span, SpanId, StringKey, VarDefinitionSpace};
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use std::collections::{HashMap, HashSet};

use std::convert::Into;

use crate::{
    BlockGraph, BlockId, CodeEntry, CodeOffset, CodeRow, Flatten, FlattenEnvironment, ICodeModule,
    LCode, LinkId, NodeBuilder as NB, ScopeId, ScopeType, StringLabel, Successor, ValueId,
};

use tabled::{settings::Style, Table};

#[derive(Debug, Clone)]
pub struct ModuleEntry {
    value_id: ValueId,
    next: ValueId,
    prev: ValueId,
    code: LCode,
    name: Option<StringKey>,
    link: Option<LinkId>,
    block_id: BlockId,
    scope_id: ScopeId,
    ty: AstType,
    span_id: SpanId,
    mem: VarDefinitionSpace,
    scope_type: ScopeType,
}

impl ModuleEntry {
    pub fn from_code_entry(
        value_id: ValueId,
        next: ValueId,
        prev: ValueId,
        scope_id: ScopeId,
        scope_type: ScopeType,
        entry: CodeEntry,
    ) -> ModuleEntry {
        Self {
            value_id,
            next,
            prev,
            scope_id,
            scope_type,
            code: entry.code,
            name: entry.name,
            link: entry.link,
            block_id: entry.block_id,
            ty: entry.ty,
            span_id: entry.span_id,
            mem: entry.mem,
        }
    }
}

pub struct FlattenModule {
    entries: Vec<ModuleEntry>,
    link_map: HashMap<LinkId, ValueId>,
    block_map: HashMap<BlockId, ValueId>,
    function_entries: HashSet<BlockId>,
    pub(super) link: LinkOptions,
    pub(super) gblocks: BlockGraph,
}

impl ICodeModule for FlattenModule {
    fn shared_libraries(&self) -> Vec<String> {
        self.link.shared_libraries()
    }

    fn get_span_id(&self, value_id: ValueId) -> SpanId {
        let entry = self.get_entry(value_id);
        entry.span_id
    }

    fn get_name(&self, offset: CodeOffset) -> Option<StringLabel> {
        let value_id = self.resolve_code_offset(offset);
        self.get_entry(value_id).name.map(|n| n.into())
    }

    fn get_code(&self, value_id: ValueId) -> &LCode {
        &self.get_entry(value_id).code
    }

    fn get_next(&self, value_id: ValueId) -> Option<ValueId> {
        let entry = self.get_entry(value_id);
        if entry.next != value_id {
            Some(entry.next)
        } else {
            None
        }
    }

    fn get_prev(&self, value_id: ValueId) -> Option<ValueId> {
        let entry = self.get_entry(value_id);
        if entry.prev != value_id {
            Some(entry.prev)
        } else {
            None
        }
    }

    fn get_block_successors(&self, entry_id: ValueId) -> Vec<(Successor, CodeOffset)> {
        let entry = self.get_entry(entry_id);
        let block_id = entry.block_id;
        let index = NodeIndex::new(block_id.index());
        let edges = self
            .gblocks
            .edges_directed(index, petgraph::Direction::Outgoing)
            .collect::<Vec<_>>();
        let mut out = vec![];
        for edge in edges {
            let succ_type = edge.weight();
            let i = edge.target();
            let block = self.gblocks.node_weight(i).unwrap();
            if !block.dead {
                let block_id = BlockId(i.index() as u32).into();
                out.push((*succ_type, block_id));
            }
        }
        out
    }

    fn get_type(&self, v: CodeOffset) -> AstType {
        let value_id = self.resolve_code_offset(v);
        let entry = self.get_entry(value_id);
        entry.clone().ty
    }

    fn get_entry_id(&self, value_id: ValueId) -> ValueId {
        let block_id = self.get_entry(value_id).block_id;
        *self.block_map.get(&block_id).unwrap()
    }

    fn is_in_static_scope(&self, offset: CodeOffset) -> bool {
        let value_id = self.resolve_code_offset(offset);
        let entry = self.get_entry(value_id);
        entry.scope_type == ScopeType::Static
    }

    fn get_mem(&self, offset: CodeOffset) -> &VarDefinitionSpace {
        let value_id = self.resolve_code_offset(offset);
        &self.get_entry(value_id).mem
    }

    fn resolve_code_offset(&self, code_offset: CodeOffset) -> ValueId {
        match code_offset {
            CodeOffset::Value(v) => v,
            CodeOffset::Link(v) => *self.link_map.get(&v).unwrap(),
            CodeOffset::Block(block_id) => *self
                .block_map
                .get(&block_id)
                .expect(&format!("Missing block {}", block_id)),
        }
    }

    fn get_entry_id_from_block_id(&self, block_id: BlockId) -> ValueId {
        self.resolve_code_offset(block_id.into())
    }

    fn code_count(&self) -> usize {
        self.entries.len()
    }

    fn dump(&self, b: &mut NB) {
        let mut rows = vec![];
        for entry in self.entries.iter() {
            let row = self.get_code_row(entry.value_id, b);
            rows.push(row);
        }
        let s = Table::new(rows).with(Style::sharp()).to_string();
        println!("{}", s);
        save_graph(self, "out.dot", b);
    }
}

impl FlattenModule {
    pub fn new() -> Self {
        Self {
            entries: vec![],
            link: LinkOptions::new(),
            link_map: HashMap::new(),
            block_map: HashMap::new(),
            function_entries: HashSet::new(),
            gblocks: BlockGraph::new(),
        }
    }

    pub fn from_builder(flatten: Flatten, fenv: &FlattenEnvironment, b: &mut NB) -> Self {
        // we want to output the blocks in a particular order
        // we use DFS post order search on each function, to ensure that the leaf
        // nodes show up last, such as the return block
        // This seems to create a nice ordering.
        flatten.dump_blocks();
        let mut m = FlattenModule::new();
        m.link = flatten.link.clone();

        let mut dfs = petgraph::visit::Dfs::new(&flatten.gblocks, BlockId(0).into());
        let mut blocks = vec![BlockId(0).into()];

        let mut entries = vec![];
        while let Some(visited) = dfs.next(&flatten.gblocks) {
            for edge in flatten.gblocks.edges(visited) {
                if Successor::FunctionDeclaration == *edge.weight() {
                    entries.push(edge.target());
                }
            }
        }

        let mut value_count = 0;
        for index in entries {
            let mut seq = vec![];
            let mut dfs = petgraph::visit::DfsPostOrder::new(&flatten.gblocks, index);
            while let Some(index) = dfs.next(&flatten.gblocks) {
                seq.push(index);
            }
            blocks.extend(seq.into_iter().rev());
        }

        for index in blocks.into_iter() {
            let block_id = index.into();
            let block = flatten.get_block(block_id);
            for (index, link_id) in block.links.iter().enumerate() {
                let entry = flatten.get_entry(*link_id).clone();
                let v = ValueId(value_count);
                let mut next = v;
                let mut prev = v;
                if index != 0 {
                    prev = ValueId(value_count - 1);
                }
                if index < block.links.len() - 1 {
                    next = ValueId(value_count + 1);
                }
                let scope_id = block.scope_id;
                let scope = fenv.get_scope(scope_id);

                if index == block.links.len() - 1
                    && !entry.code.is_term()
                    && scope.scope_type != ScopeType::Static
                {
                    b.push_error(&format!("Unterminated Block: {}", block_id), entry.span_id);
                }

                let mentry =
                    ModuleEntry::from_code_entry(v, next, prev, scope_id, scope.scope_type, entry);
                m.add(mentry);
                value_count += 1;
            }
        }
        m.gblocks = flatten.gblocks;
        m.find_dead_blocks();
        m
    }

    pub fn find_dead_blocks(&mut self) {
        let mut dfs = petgraph::visit::Dfs::new(&self.gblocks, BlockId(0).into());
        let mut entries = HashSet::new();
        while let Some(visited) = dfs.next(&self.gblocks) {
            for edge in self.gblocks.edges(visited) {
                if Successor::FunctionDeclaration == *edge.weight() {
                    entries.insert(edge.target());
                }
            }
        }

        let subgraph = self.gblocks.filter_map(
            |_n_index, n| Some(n.clone()),
            |_e_index, e| {
                if let Successor::Jump = e {
                    Some(e.clone())
                } else {
                    None
                }
            },
        );

        for entry in entries {
            let mut reachable = HashSet::new();
            let mut all = HashSet::new();
            reachable.insert(entry.into());
            all.insert(entry.into());

            let mut dfs = petgraph::visit::Dfs::new(&subgraph, entry.into());
            while let Some(visited) = dfs.next(&self.gblocks) {
                for edge in self.gblocks.edges(visited) {
                    let b: BlockId = edge.target().into();
                    all.insert(b);
                }
            }

            let mut dfs = petgraph::visit::Dfs::new(&subgraph, entry.into());
            while let Some(visited) = dfs.next(&subgraph) {
                for edge in subgraph.edges(visited) {
                    if Successor::Jump == *edge.weight() {
                        let b: BlockId = edge.target().into();
                        reachable.insert(b);
                    }
                }
            }
            let dead = all.difference(&reachable);
            println!("[{:?}] Dead: {:?}", entry, &dead);
            println!("[{:?}] All: {:?}", entry, &all);
            println!("[{:?}] Reachable: {:?}", entry, &reachable);
            for index in dead {
                let block = self.gblocks.node_weight_mut((*index).into()).unwrap();
                block.dead = true;
            }
        }
    }

    pub fn add(&mut self, mentry: ModuleEntry) {
        self.link_map.insert(mentry.link.unwrap(), mentry.value_id);
        if let LCode::Label = mentry.code {
            self.block_map.insert(mentry.block_id, mentry.value_id);
        }
        self.entries.push(mentry);
    }

    pub fn get_entry(&self, value_id: ValueId) -> &ModuleEntry {
        self.entries.get(value_id.index()).unwrap()
    }

    pub fn get_span(&self, value_id: ValueId, b: &NB) -> Span {
        let span_id = self.get_span_id(value_id);
        b.spans.lookup(span_id)
    }

    pub fn get_code_by_link(&self, link_id: LinkId) -> &LCode {
        let value_id = self.link_map.get(&link_id).unwrap();
        self.get_code(*value_id)
    }

    pub fn get_code_row(&self, v: ValueId, b: &mut NB) -> CodeRow {
        let entry = self.get_entry(v);
        let code = self.get_code(v);
        let ty = self.get_type(v.into());
        let r_ty = b.types.u.resolve(&ty).unwrap();

        let mem = self.get_mem(v.into());
        //let next = self.get_next(v).unwrap_or(v).index();
        //let prev = self.get_prev(v).unwrap_or(v).index();
        let entry_id = self.get_entry_id(v);
        let block_id = entry.block_id;
        let block = self.gblocks.node_weight(block_id.into()).unwrap();

        CodeRow {
            pos: v.index(),
            link: entry.link.unwrap().index(),
            //next: 0,
            //prev: 0,
            value: self.code_to_string(v, b),
            ty: ty.clone(),
            r_ty,
            mem: format!("{:?}", mem),
            name: self
                .get_name(v.into())
                .map(|key| b.labels.r(key))
                .unwrap_or("".to_string())
                .to_string(),
            span_id: self.get_span_id(v).index(),
            scope_id: entry.scope_id.index(),
            entry_id: entry_id.index(),
            block_id: block_id.index(),
            term: code.is_term(),
            dead: block.dead,
            unknown: ty.is_unknown(),
        }
    }
}

fn save_graph(blockify: &dyn ICodeModule, filename: &str, b: &NB) {
    use petgraph::dot::{Config, Dot};
    let cfg = blockify.get_graph(ValueId::new(0), None, b);
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
                            "label = \"L{}:{}\" shape=\"{:?}\"",
                            link_id.index(),
                            &data.name,
                            &data.ty.to_string()
                        )
                    }
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
