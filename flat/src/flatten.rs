use anyhow::Error;
use anyhow::Result;
use compile_core::{
    Argument,
    AssignTarget,
    Ast,
    AstNode,
    AstType,
    ControlFlowMarker,
    //BinaryOperation, BuiltinId, ControlFlowMarker,
    Lambda,
    LinkOptions,
    //Literal,
    ParameterNode,
    Span,
    SpanId,
    StringKey,
    //UnaryOperation,
    VarDefinitionSpace,
};
use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use std::collections::{HashMap, HashSet};

use std::convert::From;
use std::convert::Into;

use crate::{
    scope::Data, BlockId, BlockifyError, Builtin, CodeOffset, CodeRow, FlattenEnvironment,
    ICodeModule, LCode, LinkId, NodeBuilder as NB, ScopeId, ScopeType, SequenceReader, StringLabel,
    Successor, TemplateId, ValueId,
};

use tabled::{settings::Style, Table};

pub type BlockGraph = DiGraph<IRBlock, Successor>;

impl Into<NodeIndex> for BlockId {
    fn into(self) -> NodeIndex {
        NodeIndex::new(self.index())
    }
}

impl From<NodeIndex> for BlockId {
    fn from(item: NodeIndex) -> Self {
        Self(item.index() as u32)
    }
}

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

#[derive(Debug, Clone)]
pub struct CodeEntry {
    code: LCode,
    name: Option<StringKey>,
    link: Option<LinkId>,
    block_id: BlockId,
    ty: AstType,
    span_id: SpanId,
    mem: VarDefinitionSpace,
}

impl CodeEntry {
    pub fn new(
        block_id: BlockId,
        code: LCode,
        ty: AstType,
        name: Option<StringKey>,
        span_id: SpanId,
        mem: VarDefinitionSpace,
    ) -> Self {
        Self {
            block_id,
            code,
            name,
            link: None,
            ty,
            span_id,
            mem,
        }
    }

    pub fn add_mem(mut self, mem: VarDefinitionSpace) -> Self {
        self.mem = mem;
        self
    }
}

#[derive(Debug, Clone)]
pub struct IRBlock {
    scope_id: ScopeId,
    pub dead: bool,
    ast: Option<AstNode>,
    next: Option<BlockId>,
    links: Vec<LinkId>,
}

impl IRBlock {
    pub fn new(scope_id: ScopeId, ast: Option<AstNode>) -> Self {
        Self {
            scope_id,
            dead: false,
            ast,
            links: vec![],
            next: None,
        }
    }

    pub fn next(&mut self, next_block_id: BlockId) {
        self.next = Some(next_block_id);
    }

    pub fn push(&mut self, link_id: LinkId) {
        self.links.push(link_id);
    }
}

#[derive(Debug)]
pub struct FlattenResult {
    link_id: Option<LinkId>,
    block_id: BlockId,
    ty: AstType,
    is_term: bool,
}

impl FlattenResult {
    pub fn new(block_id: BlockId, link_id: Option<LinkId>, ty: AstType, is_term: bool) -> Self {
        Self {
            block_id,
            link_id,
            ty,
            is_term,
        }
    }
}

pub struct FlattenModule {
    entries: Vec<ModuleEntry>,
    link_map: HashMap<LinkId, ValueId>,
    block_map: HashMap<BlockId, ValueId>,
    function_entries: HashSet<BlockId>,
    link: LinkOptions,
    gblocks: BlockGraph,
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

    fn dump(&self, b: &NB) {
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

    pub fn block_graph2(&self, filename: &str, b: &NB) -> Result<()> {
        use std::fs::File;
        use std::io::Write;
        //use std::collections::HashSet;
        use std::collections::HashMap;

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

    pub fn get_code_row(&self, v: ValueId, b: &NB) -> CodeRow {
        let entry = self.get_entry(v);
        let code = self.get_code(v);
        let ty = self.get_type(v.into());
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
            ty,
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
        }
    }
}

pub struct Flatten {
    module_key: Option<StringKey>,
    link: LinkOptions,
    entries: Vec<CodeEntry>,
    gblocks: BlockGraph,
    templates: Vec<Lambda>,
}

impl Flatten {
    pub fn new() -> Self {
        Self {
            module_key: None,
            entries: vec![],
            gblocks: BlockGraph::new(),
            link: LinkOptions::new(),
            templates: vec![],
        }
    }

    pub fn dump_scope(&self, block_id: BlockId, fenv: &FlattenEnvironment, b: &NB) {
        let block = self.get_block(block_id);
        fenv.dump_scope(block.scope_id, b);
    }

    pub fn dump_blocks(&self) {
        for node in self.gblocks.node_indices() {
            let block_id: BlockId = node.into();
            let block = self.gblocks.node_weight(node).unwrap();
            println!("[{}] Block: {:?}", block_id, block);
        }
    }

    pub fn resolve_name(
        &self,
        block_id: BlockId,
        name: StringKey,
        fenv: &FlattenEnvironment,
    ) -> Option<Data> {
        // resolve scope through the tree, starting at the current scope
        let block = self.get_block(block_id);
        for scope_id in fenv.walk_scopes(block.scope_id) {
            let scope = fenv.get_scope(scope_id);
            if let Some(data) = scope.names.get(&name) {
                return Some(data.clone());
            }
        }
        None
    }

    pub fn resolve_lambda_scope(
        &self,
        block_id: BlockId,
        name: StringLabel,
        fenv: &FlattenEnvironment,
    ) -> Option<ScopeId> {
        // resolve scope through the tree, starting at the current scope
        let block = self.get_block(block_id);
        for scope_id in fenv.walk_scopes(block.scope_id) {
            let scope = fenv.get_scope(scope_id);
            if let Some(_data) = scope.lambdas.get(&name) {
                return Some(scope_id);
            }
        }
        None
    }

    pub fn module(self, fenv: &FlattenEnvironment, b: &mut NB) -> FlattenModule {
        // we want to output the blocks in a particular order
        // we use DFS post order search on each function, to ensure that the leaf
        // nodes show up last, such as the return block
        // This seems to create a nice ordering.
        self.dump_blocks();
        let mut m = FlattenModule::new();
        m.link = self.link.clone();

        let mut dfs = petgraph::visit::Dfs::new(&self.gblocks, BlockId(0).into());
        let mut blocks = vec![BlockId(0).into()];

        let mut entries = vec![];
        while let Some(visited) = dfs.next(&self.gblocks) {
            for edge in self.gblocks.edges(visited) {
                if Successor::FunctionDeclaration == *edge.weight() {
                    entries.push(edge.target());
                }
            }
        }

        let mut value_count = 0;
        for index in entries {
            let mut seq = vec![];
            let mut dfs = petgraph::visit::DfsPostOrder::new(&self.gblocks, index);
            while let Some(index) = dfs.next(&self.gblocks) {
                seq.push(index);
            }
            blocks.extend(seq.into_iter().rev());
        }

        for index in blocks.into_iter() {
            let block_id = index.into();
            let block = self.get_block(block_id);
            for (index, link_id) in block.links.iter().enumerate() {
                let entry = self.get_entry(*link_id).clone();
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
        m.gblocks = self.gblocks;
        m.find_dead_blocks();
        m
    }

    pub fn flatten_module(
        node: AstNode,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<Self> {
        let mut f = Self::new();
        if let Ast::Module(key, body) = node.node {
            f.module_key = Some(key);
            let static_scope = fenv.new_scope(ScopeType::Static);
            let block_id = f.new_block(None, static_scope);
            let code = LCode::Label;
            let entry = CodeEntry::new(
                block_id,
                code,
                AstType::Unit,
                Some(key),
                node.span_id,
                VarDefinitionSpace::Static,
            );
            f.push_entry_with_link(entry);
            fenv.static_block = Some(block_id);
            fenv.static_scope = Some(static_scope);
            for ast in body.to_vec() {
                let _ = f.flatten(block_id, ast, fenv, b)?;
            }
            Ok(f)
        } else {
            unreachable!()
        }
    }

    fn _push(&mut self, mut entry: CodeEntry) -> LinkId {
        let index = self.entries.len();
        let link_id = LinkId(index as u32);
        entry.link = Some(link_id);
        //let block_id = entry.block_id;
        self.entries.push(entry);
        link_id
    }

    pub fn push_link(&mut self, block_id: BlockId, link_id: LinkId) {
        self.get_block_mut(block_id).push(link_id);
    }

    pub fn push_entry_with_link(&mut self, entry: CodeEntry) -> LinkId {
        let block_id = entry.block_id;
        let link_id = self._push(entry);
        let block = self.get_block(block_id);
        if let Some(last_link_id) = block.links.last() {
            let last_entry = self.get_entry(*last_link_id);
            let is_term = last_entry.code.is_term();
            if is_term {
                assert!(false, "appending to term block");
            }
        }
        self.get_block_mut(block_id).push(link_id);
        link_id
    }

    pub fn new_block(&mut self, ast: Option<AstNode>, scope_id: ScopeId) -> BlockId {
        let ast = if let Some(ast) = ast {
            Some(Ast::Sequence(ast.to_vec()).into())
        } else {
            None
        };
        let ir_block = IRBlock::new(scope_id, ast);
        let index = self.gblocks.add_node(ir_block);
        BlockId(index.index() as u32)
    }

    pub fn block_succ(
        &mut self,
        source_block_id: BlockId,
        target_block_id: BlockId,
        succ_type: Successor,
    ) {
        self.gblocks
            .add_edge(source_block_id.into(), target_block_id.into(), succ_type);
    }

    pub fn get_block(&self, block_id: BlockId) -> &IRBlock {
        let index = NodeIndex::new(block_id.index());
        self.gblocks.node_weight(index).unwrap()
    }

    pub fn get_block_mut(&mut self, block_id: BlockId) -> &mut IRBlock {
        let index = NodeIndex::new(block_id.index());
        self.gblocks.node_weight_mut(index).unwrap()
    }

    pub fn get_entry(&self, link_id: LinkId) -> &CodeEntry {
        self.entries.get(link_id.index()).unwrap()
    }

    pub fn get_entry_mut(&mut self, link_id: LinkId) -> &mut CodeEntry {
        self.entries.get_mut(link_id.index()).unwrap()
    }

    pub fn push_template(&mut self, def: Lambda) -> TemplateId {
        let offset = self.templates.len();
        self.templates.push(def);
        TemplateId(offset as u32)
    }

    pub fn get_template(&mut self, template_id: TemplateId) -> &Lambda {
        self.templates.get(template_id.index()).unwrap()
    }

    pub fn flatten_sequence(
        &mut self,
        block_id: BlockId,
        seq: Vec<AstNode>,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        let mut current_block_id = block_id;
        let mut ty = AstType::Unit;
        let mut link_id = None;
        let mut is_term = false;

        let mut current_span_id = if let Some(first) = seq.first() {
            first.span_id
        } else {
            b.spans.get_span_unknown()
        };

        let block = self.get_block(block_id);
        let seq_next_block_id = block.next;
        let scope_id = block.scope_id;

        let mut r = SequenceReader::new();
        let mut seq = r.build(seq.clone(), b);

        for expr in seq.iter() {
            match &expr.node {
                Ast::Block(key, args, _body) => {
                    if fenv.resolve_block_id(scope_id, key.into()).is_none() {
                        assert_eq!(0, args.len());
                        let new_block_id = self.new_block(None, scope_id);
                        let new_block = self.get_block_mut(new_block_id);
                        new_block.next = seq_next_block_id;
                        self.block_succ(current_block_id, new_block_id, Successor::BlockScope);
                        let scope = fenv.get_scope_mut(scope_id);
                        scope.block_labels.insert(key.into(), new_block_id);
                    }
                }
                _ => (),
            }
        }

        current_block_id = block_id;
        let mut d = seq.drain(..);
        loop {
            if let Some(expr) = d.next() {
                let span_id = expr.span_id;
                current_span_id = span_id;
                let expr_is_term = expr.node.is_term();
                let is_last = d.len() == 0;

                //println!(
                //"current: {:?}",
                //(is_last, expr_is_term, current_block_id, &expr)
                //);
                //
                //let r = self.flatten(current_block_id, expr, fenv, b)?;

                if expr_is_term && !is_last {
                    let next_seq = d.collect::<Vec<_>>();
                    let next_node = next_seq.first().unwrap();
                    let next_span_id = next_node.span_id;
                    let new_block_id = match &next_node.node {
                        Ast::Block(key, _, _) => {
                            let new_block_id = fenv.resolve_block_id(scope_id, key.into()).unwrap();
                            new_block_id
                        }
                        _ => {
                            let new_block_id = self.new_block(None, scope_id);
                            println!("term new: {:?}", (new_block_id, &next_node));
                            self.start_block(
                                new_block_id,
                                scope_id,
                                &AstType::Unit,
                                &[],
                                &[],
                                AstType::Unit,
                                Some(b.labels.fresh_key("new")),
                                next_node.span_id,
                                VarDefinitionSpace::Default,
                                fenv,
                                b,
                            );
                            self.block_succ(current_block_id, new_block_id, Successor::BlockScope);
                            let new_block = self.get_block_mut(new_block_id);
                            new_block.next = seq_next_block_id;
                            new_block_id
                        }
                    };

                    // set next on current
                    let block = self.get_block_mut(current_block_id);
                    block.next(new_block_id);

                    // flatten expr
                    //println!("expr: {:?}", (&expr));
                    let _ = self.flatten(current_block_id, expr, fenv, b)?;

                    // flatten next
                    let next_node = AstNode {
                        node: Ast::Sequence(next_seq),
                        span_id: next_span_id,
                    };
                    //println!("next: {:?}", (&next_node));
                    let r = self.flatten(new_block_id, next_node, fenv, b)?;
                    //println!("next2: {:?}", (&r));
                    return Ok(r);
                }

                // handle expr
                //match &expr.node {
                //_ => {
                //b.dump_ast(&ast);
                //if is_last {
                //let block = self.get_block_mut(current_block_id);
                //block.next = seq_next_block_id;
                //}
                let r = self.flatten(current_block_id, expr, fenv, b)?;
                let block = self.get_block(r.block_id);
                println!("b: {:?}", (&r, block.next, d.len(), is_last));
                ty = r.ty;
                current_block_id = r.block_id;
                link_id = r.link_id;
                is_term = r.is_term;
                //assert!(!is_term);
                //}
                //};
            } else {
                break;
            }
        }

        if !is_term {
            let block = self.get_block(current_block_id);
            if let Some(next) = block.next {
                println!("adding term on block: {}, jump: {}", current_block_id, next);
                let jump_link_id =
                    self.add_jump(current_block_id, next.into(), vec![], current_span_id);
                link_id = Some(jump_link_id);
            } else {
                println!("missing term on block: {}", current_block_id);
                b.push_error(
                    &format!("Missing next block on block_id={}", current_block_id),
                    current_span_id,
                );
            }
        }

        Ok(FlattenResult::new(current_block_id, link_id, ty, is_term))
    }

    pub fn add_return(
        &mut self,
        block_id: BlockId,
        link_ids: Vec<(LinkId, AstType)>,
        span_id: SpanId,
    ) -> LinkId {
        for (link_id, ty) in link_ids.iter() {
            let code = LCode::CallValue((*link_id).into());
            let entry = CodeEntry::new(
                block_id,
                code,
                ty.clone(),
                None,
                span_id,
                VarDefinitionSpace::Reg,
            );
            self.push_entry_with_link(entry);
        }

        let code = LCode::Return;
        let entry = CodeEntry::new(
            block_id,
            code,
            AstType::Unit,
            None,
            span_id,
            VarDefinitionSpace::Reg,
        );
        self.push_entry_with_link(entry)
    }

    pub fn add_return_block(
        &mut self,
        ret_block_id: BlockId,
        scope_id: ScopeId,
        return_type: AstType,
        span_id: SpanId,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) {
        let name = b.labels.fresh_key("ret");
        let args = match &return_type {
            AstType::Unit => vec![],
            _ => vec![return_type.clone()],
        };

        let v_args = self.start_block(
            ret_block_id,
            scope_id,
            &AstType::Unit,
            &args,
            &[],
            AstType::Unit,
            Some(name),
            span_id,
            VarDefinitionSpace::Reg,
            fenv,
            b,
        );
        self.add_return(ret_block_id, v_args, span_id);
    }

    pub fn add_jump(
        &mut self,
        block_id: BlockId,
        target_id: CodeOffset,
        jump_args: Vec<(LinkId, AstType)>,
        span_id: SpanId,
    ) -> LinkId {
        for (link_id, ty) in jump_args.into_iter() {
            let code = LCode::CallValue(link_id.into());
            let entry = CodeEntry::new(block_id, code, ty, None, span_id, VarDefinitionSpace::Reg);
            self.push_entry_with_link(entry);
        }

        if let CodeOffset::Block(target_block_id) = target_id {
            self.block_succ(block_id, target_block_id, Successor::Jump);
        }

        let code = LCode::Jump(target_id.into());
        let entry = CodeEntry::new(
            block_id,
            code,
            AstType::Unit,
            None,
            span_id,
            VarDefinitionSpace::Reg,
        );

        self.push_entry_with_link(entry)
    }

    pub fn add_function_args(
        &mut self,
        block_id: BlockId,
        fun_ty: AstType,
        args: Vec<Argument>,
        span_id: SpanId,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<(BlockId, AstType, Vec<(LinkId, AstType)>)> {
        if let AstType::Func(func_arg_types, ret) = &fun_ty {
            let fields = func_arg_types.fields();
            let num_args = fields.len();
            if num_args != args.len() {
                b.push_error(
                    &format!("xCall arity mismatch: {}<=>{}", num_args, args.len()),
                    span_id,
                );
                return Err(Error::new(BlockifyError::Invalid));
            }

            let mut values = vec![];
            let mut current_block_id = block_id;
            let mut link_ids = vec![];
            //let mut has_kwargs = false;
            for (a, (maybe_key, ty)) in args.into_iter().zip(fields.iter()) {
                /*
                if let Some(key) = maybe_key {
                    if let Some(expr) =
                    has_kwargs = true;
                } else if has_kwargs {
                    assert!(false, "positional field following named field");
                }
                */

                match a {
                    Argument::Positional(expr) => {
                        let r = self.flatten(current_block_id, *expr, fenv, b)?;
                        current_block_id = r.block_id;
                        let link_id = r.link_id.unwrap();
                        values.push((link_id, ty.clone()));
                        link_ids.push(link_id);
                    }
                    Argument::Named(key, expr) => {
                        let r = self.flatten(current_block_id, *expr, fenv, b)?;
                        current_block_id = r.block_id;
                        let link_id = r.link_id.unwrap();
                        values.push((link_id, ty.clone()));
                        link_ids.push(link_id);
                    }
                }
            }
            Ok((current_block_id, *ret.clone(), values))
        } else {
            b.push_error(&format!("Type not function: {:?}", fun_ty), span_id);
            return Err(Error::new(BlockifyError::Invalid));
        }
    }

    pub fn add_function_call(
        &mut self,
        block_id: BlockId,
        fun_offset: CodeOffset,
        fun_ty: AstType,
        args: Vec<Argument>,
        span_id: SpanId,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        let args_size = args.len();
        println!("Y");
        let (current_block_id, ret_ty, values) =
            self.add_function_args(block_id, fun_ty, args, span_id, fenv, b)?;

        // Add links
        for (link_id, ty) in values {
            let code = LCode::CallValue(link_id.into());
            let entry = CodeEntry::new(
                current_block_id,
                code,
                ty,
                None,
                span_id,
                VarDefinitionSpace::Reg,
            );
            self.push_entry_with_link(entry);
        }

        // Make call
        let code = LCode::Call(fun_offset, args_size as u8, 0);
        let entry = CodeEntry::new(
            current_block_id,
            code,
            ret_ty.clone(),
            None,
            span_id,
            VarDefinitionSpace::Default,
        );
        let link_id = self.push_entry_with_link(entry);
        Ok(FlattenResult::new(
            current_block_id,
            Some(link_id),
            ret_ty.clone(),
            false,
        ))
    }

    fn start_block(
        &mut self,
        block_id: BlockId,
        scope_id: ScopeId,
        arg: &AstType,
        args: &[AstType],
        kwargs: &[ParameterNode],
        ty: AstType,
        name: Option<StringKey>,
        span_id: SpanId,
        _mem: VarDefinitionSpace,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Vec<(LinkId, AstType)> {
        let code = LCode::Label;
        let entry = CodeEntry::new(
            block_id,
            code,
            ty,
            name,
            span_id,
            VarDefinitionSpace::Default,
        );
        self.push_entry_with_link(entry);

        // positional, unnamed, returned as links
        let v_args = args
            .iter()
            .enumerate()
            .map(|(i, arg_ty)| {
                let code = LCode::Arg(i as u8);
                //let name = b.labels.s(&format!(".arg{}", i));
                let entry = CodeEntry::new(
                    block_id,
                    code,
                    arg_ty.clone(),
                    None, //Some(name),
                    span_id,
                    VarDefinitionSpace::Arg,
                );
                (self.push_entry_with_link(entry), arg_ty.clone())
            })
            .collect::<Vec<_>>();

        for (i, (name, ty)) in arg.fields().iter().enumerate() {
            //let ty = b.types.r(p.ty);
            let code = LCode::Arg(i as u8);
            let entry = CodeEntry::new(
                block_id,
                code,
                ty.clone(),
                *name,
                span_id,
                VarDefinitionSpace::Arg,
            );
            let link_id = self.push_entry_with_link(entry);
            if let Some(name) = name {
                fenv.scope_define(
                    scope_id,
                    *name,
                    link_id.into(),
                    ty.clone(),
                    VarDefinitionSpace::Arg,
                );
            }
        }

        // defined in the scope
        for (i, p) in kwargs.iter().enumerate() {
            let ty = b.types.r(p.ty);
            let code = LCode::Arg(i as u8);
            let entry = CodeEntry::new(
                block_id,
                code,
                ty.clone(),
                Some(p.name),
                p.span_id,
                VarDefinitionSpace::Arg,
            );
            let link_id = self.push_entry_with_link(entry);
            fenv.scope_define(
                scope_id,
                p.name,
                link_id.into(),
                ty.clone(),
                VarDefinitionSpace::Arg,
            );
        }

        v_args
    }

    pub fn flatten(
        &mut self,
        block_id: BlockId,
        node: AstNode,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        let block = self.get_block_mut(block_id);
        let span_id = node.span_id;
        let ast = node.node;

        match ast {
            Ast::Module(_, _) => {
                unimplemented!("No nested modules yet")
            }

            Ast::Sequence(exprs) => self.flatten_sequence(block_id, exprs, fenv, b),

            Ast::Global(name, expr) => {
                match expr.node {
                    Ast::Lambda(def) => {
                        let ret_ty = b.types.r(def.return_type).clone();
                        let fun_ty = def_to_type(&def, b);

                        // save template for later use
                        // needed for expressing defaults
                        let template_id = self.push_template(def.clone());
                        let block = self.get_block(block_id);
                        let scope_id = block.scope_id;
                        let scope = fenv.get_scope_mut(scope_id);
                        scope.lambdas.insert(name.into(), template_id);

                        if let Some(body) = def.body {
                            let span_id = body.span_id;

                            // create function scope
                            let fun_scope_id = fenv.new_scope(ScopeType::Function);
                            fenv.scope_succ(fenv.static_scope_id(), fun_scope_id);

                            // create function block and return block
                            let fun_block_id = self.new_block(None, fun_scope_id);
                            let ret_block_id = self.new_block(None, fun_scope_id);

                            // add the name to static scope
                            // do this early for recursive functions
                            fenv.scope_define(
                                fenv.static_scope_id(),
                                name,
                                fun_block_id.into(),
                                fun_ty.clone(),
                                VarDefinitionSpace::Static,
                            );

                            // return in scope
                            let fun_scope = fenv.get_scope_mut(fun_scope_id);
                            fun_scope.return_block = Some(ret_block_id);

                            // next in scope
                            let fun_block = self.get_block_mut(fun_block_id);
                            fun_block.next = Some(ret_block_id);

                            // block graph
                            self.block_succ(
                                fenv.static_block_id(),
                                fun_block_id,
                                Successor::FunctionDeclaration,
                            );
                            self.block_succ(fun_block_id, ret_block_id, Successor::BlockScope);
                            let arg_type = b.types.r(def.arg_type).clone();
                            self.start_block(
                                fun_block_id,
                                fun_scope_id,
                                &arg_type,
                                &[],
                                &[],
                                fun_ty.clone(),
                                Some(name),
                                span_id,
                                VarDefinitionSpace::Static,
                                fenv,
                                b,
                            );
                            let body = jump_if_needed(*body, b);
                            let _ = self.flatten(fun_block_id, body, fenv, b)?;

                            // push declaration into static block
                            let code = LCode::DeclareFunction(Some(fun_block_id));
                            let entry = CodeEntry::new(
                                fenv.static_block_id(),
                                //block_id,
                                code,
                                fun_ty.clone(),
                                Some(name),
                                span_id,
                                VarDefinitionSpace::Static,
                            );
                            let link_id = self.push_entry_with_link(entry);

                            // write out return block
                            self.add_return_block(
                                ret_block_id,
                                fun_scope_id,
                                ret_ty.clone(),
                                span_id,
                                fenv,
                                b,
                            );

                            Ok(FlattenResult::new(block_id, Some(link_id), fun_ty, false))
                        } else {
                            let code = LCode::DeclareFunction(None);
                            let entry = CodeEntry::new(
                                block_id,
                                code,
                                fun_ty.clone(),
                                Some(name),
                                span_id,
                                VarDefinitionSpace::Static,
                            );
                            let link_id = self.push_entry_with_link(entry);
                            Ok(FlattenResult::new(block_id, Some(link_id), fun_ty, false))
                        }
                    }

                    Ast::Literal(lit) => {
                        let scope_id = block.scope_id;
                        let scope = fenv.get_scope(scope_id);

                        let static_block_id = fenv.static_block_id();
                        let global_name = if let ScopeType::Static = scope.scope_type {
                            b.labels.r(name.into()).to_string()
                        } else {
                            // static var with local name
                            let unique_name = b.unique_static_name();
                            let base = b.labels.r(name.into());
                            format!("{}{}", base, unique_name).clone()
                        };

                        let ast_ty: AstType = lit.clone().into();
                        let code = LCode::Const(lit);
                        let global_name_key = b.labels.s(&global_name);
                        let entry = CodeEntry::new(
                            static_block_id,
                            code,
                            ast_ty.clone(),
                            Some(global_name_key),
                            node.span_id,
                            VarDefinitionSpace::Static,
                        );
                        let link_id = self.push_entry_with_link(entry);

                        let code = LCode::Value(link_id.into());
                        let entry = CodeEntry::new(
                            block_id,
                            code,
                            ast_ty.clone(),
                            Some(name),
                            node.span_id,
                            VarDefinitionSpace::Static,
                        );
                        let link_id = self.push_entry_with_link(entry);

                        fenv.scope_define(
                            scope_id,
                            name,
                            link_id.into(),
                            ast_ty.clone(),
                            VarDefinitionSpace::Static,
                        );

                        Ok(FlattenResult::new(block_id, Some(link_id), ast_ty, false))
                    }
                    _ => unreachable!(),
                }
            }

            Ast::Builtin(id, mut args) => {
                let bi = b.builtins.get_enum(id);
                match bi {
                    Builtin::Import => {
                        let arg = args.pop().unwrap();
                        if let Some(s) = arg.try_string() {
                            //println!("adding: {}", s);
                            self.link.add_library(&s);
                        } else {
                            b.push_error("Expected string", span_id);
                        }
                        Ok(FlattenResult::new(block_id, None, AstType::Unit, false))
                    }
                    _ => {
                        let mut current_block_id = block_id;
                        let ty = bi.get_return_type();
                        let args_size = args.len();
                        assert_eq!(args_size, bi.arity());
                        let mut values = vec![];
                        for a in args.into_iter() {
                            let expr = a.expr();
                            //let Argument::Positional(expr) = a;
                            let r = self.flatten(current_block_id, expr, fenv, b)?;
                            current_block_id = r.block_id;
                            let link_id = r.link_id.unwrap();
                            let entry = self.get_entry(link_id);
                            values.push((link_id, entry.ty.clone()));
                        }

                        for (link_id, ty) in values {
                            let code = LCode::CallValue(link_id.into());
                            let entry = CodeEntry::new(
                                current_block_id,
                                code,
                                ty,
                                None,
                                node.span_id,
                                VarDefinitionSpace::Reg,
                            );
                            self.push_entry_with_link(entry);
                        }

                        let code = LCode::Builtin(id, args_size as u8, 0);
                        let entry = CodeEntry::new(
                            current_block_id,
                            code,
                            ty.clone(),
                            None,
                            node.span_id,
                            VarDefinitionSpace::Default,
                        );
                        let link_id = self.push_entry_with_link(entry);
                        Ok(FlattenResult::new(
                            current_block_id,
                            Some(link_id),
                            ty,
                            false,
                        ))
                    }
                }
            }

            Ast::Return(maybe_expr) => {
                let fun_scope_id = fenv
                    .find_nearest_scope(block.scope_id, ScopeType::Function)
                    .unwrap();

                let mut jump_args = vec![];
                let mut block_id = block_id;
                let span_id = if let Some(expr) = maybe_expr {
                    let expr_span_id = expr.span_id;
                    let r = self.flatten(block_id, *expr, fenv, b)?;
                    block_id = r.block_id;
                    let link_id = r.link_id.unwrap();
                    let entry = self.get_entry(link_id);
                    jump_args.push((link_id, entry.ty.clone()));
                    expr_span_id
                } else {
                    node.span_id
                };

                let scope = fenv.get_scope(fun_scope_id);
                self.add_jump(
                    block_id,
                    scope.return_block.unwrap().into(),
                    jump_args,
                    span_id,
                );
                Ok(FlattenResult::new(block_id, None, AstType::Unit, true))
            }

            Ast::Literal(lit) => {
                // literal is expression, non-terminal
                let ty: AstType = lit.clone().into();
                let code = LCode::Const(lit);
                let entry = CodeEntry::new(
                    block_id,
                    code,
                    ty.clone(),
                    None,
                    node.span_id,
                    VarDefinitionSpace::Default,
                );
                let link_id = self.push_entry_with_link(entry);
                Ok(FlattenResult::new(block_id, Some(link_id), ty, false))
            }

            Ast::BinaryOp(op, x, y) => {
                // expression, non-terminal
                let x_span_id = x.span_id;
                let rx = self.flatten(block_id, *x, fenv, b)?;
                let ry = self.flatten(rx.block_id, *y, fenv, b)?;
                let current_block_id = ry.block_id;
                let vx = rx.link_id.unwrap();
                let vy = ry.link_id.unwrap();

                //let x_ty = rx.ty;
                //let y_ty = ry.ty;
                if &rx.ty != &ry.ty {
                    b.push_error(
                        &format!("Binary op type mismatch: {}, {}", &rx.ty, &ry.ty),
                        x_span_id,
                    );
                }

                for (v, ty) in [(vx, &rx.ty), (vy, &ry.ty)] {
                    let code = LCode::Value(v.into());
                    let entry = CodeEntry::new(
                        current_block_id,
                        code,
                        ty.clone(),
                        None,
                        node.span_id,
                        VarDefinitionSpace::Reg,
                    );
                    let _ = self.push_entry_with_link(entry);
                }

                let code = LCode::Op2(op.node);
                let ret_ty = op.node.get_type(&rx.ty, &ry.ty);
                //let entry = self.get_entry(vx);
                //let ty = entry.ty.clone();
                let entry = CodeEntry::new(
                    ry.block_id,
                    code,
                    ret_ty.clone(),
                    None,
                    node.span_id,
                    VarDefinitionSpace::Default,
                );
                let link_id = self.push_entry_with_link(entry);
                Ok(FlattenResult::new(
                    ry.block_id,
                    Some(link_id),
                    ret_ty,
                    false,
                ))
            }

            Ast::Identifier(key) => {
                // identifier is expression, non-terminal
                self.dump_scope(block_id, fenv, b);
                if let Some(data) = self.resolve_name(block_id, key, fenv) {
                    let ty = data.ty.clone();
                    let code = if let VarDefinitionSpace::Arg = data.mem {
                        LCode::Value(data.offset)
                    } else {
                        LCode::Load(data.offset)
                    };
                    let entry =
                        CodeEntry::new(block_id, code, ty.clone(), None, node.span_id, data.mem);
                    let link_id = self.push_entry_with_link(entry);
                    Ok(FlattenResult::new(block_id, Some(link_id), ty, false))
                } else {
                    b.push_error("Name not found", node.span_id);
                    let s = b.labels.r(key.into());
                    Err(Error::new(BlockifyError::NotFound(s)))
                }
            }

            Ast::Assign(target, expr) => {
                // assign is expression, non-terminal
                let name = match target {
                    AssignTarget::Identifier(name) | AssignTarget::Alloca(name) => name,
                };

                // push the definition into the lambda list
                if let Ast::Lambda(def) = expr.node {
                    let ty = def_to_type(&def, b);
                    let template_id = self.push_template(def);
                    let block = self.get_block(block_id);
                    let scope_id = block.scope_id;
                    let scope = fenv.get_scope_mut(scope_id);
                    scope.lambdas.insert(name.into(), template_id);
                    return Ok(FlattenResult::new(block_id, None, ty, false));
                }

                let r = self.flatten(block_id, *expr, fenv, b)?;
                let current_block_id = r.block_id;
                let v_expr = r.link_id.unwrap();
                let expr_ty = self.get_entry(v_expr).ty.clone();

                let offset_decl =
                    if let Some(data) = self.resolve_name(current_block_id, name, fenv) {
                        if data.ty != expr_ty {
                            b.push_error(
                                &format!("Type Mismatch: {:?}, {:?}", data.ty, expr_ty),
                                node.span_id,
                            );
                        }
                        //assert_eq!(data.ty, expr_ty);
                        data.offset
                    } else {
                        let block = self.get_block(current_block_id);
                        let scope_id = block.scope_id;
                        let code = LCode::Declare;
                        let expr_ty = self.get_entry(v_expr).ty.clone();
                        let entry = CodeEntry::new(
                            current_block_id,
                            code,
                            expr_ty.clone(),
                            Some(name),
                            node.span_id,
                            VarDefinitionSpace::Default,
                        );
                        let link_id = self.push_entry_with_link(entry);
                        fenv.scope_define(
                            scope_id,
                            name,
                            link_id.into(),
                            expr_ty,
                            VarDefinitionSpace::Stack,
                        );
                        link_id.into()
                    };

                let code = LCode::Store(offset_decl, v_expr.into());
                let entry = CodeEntry::new(
                    current_block_id,
                    code,
                    AstType::Unit,
                    Some(name),
                    node.span_id,
                    VarDefinitionSpace::Default,
                );
                let link_id = self.push_entry_with_link(entry);
                Ok(FlattenResult::new(
                    current_block_id,
                    Some(link_id),
                    AstType::Unit,
                    false,
                ))
            }

            Ast::Call(expr, mut args, _ret_ty) => {
                match &expr.node {
                    // call is an expression, it's non-terminal
                    // lambdas should also be non-terminal
                    Ast::Identifier(ident) => {
                        let name = b.labels.r(ident.into());
                        if let Some(data) = self.resolve_name(block_id, *ident, fenv) {
                            return self.add_function_call(
                                block_id,
                                data.offset,
                                data.ty,
                                args,
                                node.span_id,
                                fenv,
                                b,
                            );
                        }

                        match self.resolve_lambda_scope(block_id, ident.into(), fenv) {
                            Some(scope_id) => {
                                // create a new block for the lambda
                                // we call the lambda by jumping to it
                                // the new block points to a next block
                                // which we create here, and we return next block to the sequence
                                // This involves creating a new lambda block for each call site.  This
                                // is not efficient, if we call more than once.  In this other case, we
                                // want to pass the continuation into the block, so next is not
                                // required.

                                let scope = fenv.get_scope(scope_id);
                                let label: StringLabel = (*ident).into();
                                let template_id = scope.lambdas.get(&label).unwrap();
                                let def = self.get_template(*template_id).clone();
                                let fun_ty = def_to_type(&def, b);

                                // New Lambda Scope
                                let fun_scope_id = fenv.new_scope(ScopeType::Function);
                                fenv.scope_succ(scope_id, fun_scope_id);

                                // Lambda Block
                                let fun_block_id = self.new_block(None, fun_scope_id);
                                self.block_succ(block_id, fun_block_id, Successor::BlockScope);

                                // process arguments
                                // block may have changed so we use the new block returned from the
                                // args
                                let (fun_arg, ret) = if let AstType::Func(arg, ret) = &fun_ty {
                                    (arg, ret)
                                } else {
                                    unreachable!()
                                };

                                let fields = fun_arg.fields();
                                if args.len() < fields.len() {
                                    println!("missing: {:?}", (args.len(), fields.len()));
                                    // missing fields
                                    // search for defaults
                                    for i in args.len()..fields.len() {
                                        println!("missing: {:?}", (i, fields.get(i)));
                                        match fields.get(i).unwrap() {
                                            (Some(key), _) => {
                                                // field has a name, check for default
                                                if let Some(v) = def.defaults.get(key) {
                                                    let arg =
                                                        Argument::Positional(v.clone().into());
                                                    args.push(arg);
                                                } else {
                                                    b.push_error(
                                                        &format!("Call name not found: {}", name),
                                                        node.span_id,
                                                    );
                                                }
                                            }
                                            _ => (),
                                        }
                                    }
                                }

                                //let args_size = args.len();
                                println!(
                                    "X: {}, {}, {:?}",
                                    args.len(),
                                    fields.len(),
                                    (&fun_ty, fields)
                                );
                                let (current_block_id, ret_ty, call_values) = self
                                    .add_function_args(block_id, fun_ty, args, span_id, fenv, b)?;
                                // now that we have the arguments calculated
                                // jump to the function baked as a block
                                // complete this block with a jump
                                self.add_jump(
                                    current_block_id,
                                    fun_block_id.into(),
                                    call_values,
                                    node.span_id,
                                );

                                // NEXT BLOCK(ret_ty)
                                // We create a new block for the lambda to return to
                                // this is the continuation
                                let next_block_id = self.new_block(None, scope_id);
                                self.block_succ(block_id, next_block_id, Successor::BlockScope);

                                // Lambda Body
                                let body = jump_if_needed(*def.body.unwrap(), b);

                                // get the next block
                                let block = self.get_block(current_block_id);
                                let next = block.next;

                                // set next for lambda block, which is the new continuation we just
                                // created
                                let next_block = self.get_block_mut(fun_block_id);
                                next_block.next(next_block_id);

                                let fun_scope = fenv.get_scope_mut(fun_scope_id);
                                fun_scope.return_block = Some(next_block_id);

                                // set next for the continuation block, which should be next of the
                                // containing block
                                let next_block = self.get_block_mut(next_block_id);
                                next_block.next = next;

                                // setup arguments for continuation block with appropriate parameters
                                // matching the return type of the lambda block
                                let next_args = match &ret_ty {
                                    AstType::Unit => vec![],
                                    _ => vec![ret_ty.clone()],
                                };
                                // start next block
                                let next_link_ids = self.start_block(
                                    next_block_id,
                                    scope_id,
                                    &AstType::Unit,
                                    &next_args,
                                    &[],
                                    AstType::Unit,
                                    Some(b.labels.fresh_key("cont")),
                                    span_id,
                                    VarDefinitionSpace::Reg,
                                    fenv,
                                    b,
                                );

                                let next_link_id = match &ret_ty {
                                    AstType::Unit => None,
                                    _ => Some(next_link_ids.first().unwrap().0),
                                };

                                // Start lambda block
                                let arg_type = b.types.r(def.arg_type).clone();
                                let lambda_name = b.labels.fresh_key("lambda");
                                self.start_block(
                                    fun_block_id,
                                    fun_scope_id,
                                    &arg_type,
                                    &[],
                                    &[],
                                    AstType::Unit,
                                    Some(lambda_name),
                                    span_id,
                                    VarDefinitionSpace::Reg,
                                    fenv,
                                    b,
                                );
                                // flatten lambda block
                                let _ = self.flatten(fun_block_id, body, fenv, b)?;

                                Ok(FlattenResult::new(
                                    next_block_id,
                                    next_link_id,
                                    ret_ty,
                                    true,
                                ))
                            }
                            None => {
                                b.push_error(
                                    &format!("Call name not found: {}", name),
                                    node.span_id,
                                );
                                Err(Error::new(BlockifyError::Invalid))
                            }
                        }
                    }
                    _ => unimplemented!("{:?}", expr.node),
                }
            }

            Ast::UnaryOp(op, x) => {
                // op1 is expression, non-terminal
                let r = self.flatten(block_id, *x, fenv, b)?;
                let current_block_id = r.block_id;

                let code = LCode::Value(r.link_id.unwrap().into());
                let entry = CodeEntry::new(
                    current_block_id,
                    code,
                    r.ty.clone(),
                    None,
                    node.span_id,
                    VarDefinitionSpace::Reg,
                );
                let _ = self.push_entry_with_link(entry);

                let code = LCode::Op1(op);
                let entry = CodeEntry::new(
                    current_block_id,
                    code,
                    r.ty.clone(),
                    None,
                    node.span_id,
                    VarDefinitionSpace::Reg,
                );
                let link_id = self.push_entry_with_link(entry);
                Ok(FlattenResult::new(
                    current_block_id,
                    Some(link_id),
                    r.ty,
                    false,
                ))
            }

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
                let block = self.get_block(block_id);
                let v_next = block.next.unwrap();
                let parent_scope_id = block.scope_id;

                // THEN
                let then_scope_id = fenv.new_scope(ScopeType::Block);
                fenv.scope_succ(parent_scope_id, then_scope_id);
                let then_span_id = then_expr.span_id;
                let then_block_id = self.new_block(None, then_scope_id);
                self.block_succ(block_id, then_block_id, Successor::BlockScope);
                self.block_succ(block_id, then_block_id, Successor::Jump);
                let block = self.get_block_mut(then_block_id);
                block.next(v_next);

                let name = b.labels.fresh_key("then");
                let code = LCode::Label;
                let entry = CodeEntry::new(
                    then_block_id,
                    code,
                    AstType::Unit,
                    Some(name),
                    then_span_id,
                    VarDefinitionSpace::Reg,
                );
                self.push_entry_with_link(entry);
                self.flatten(then_block_id, NB::ensure_seq(*then_expr), fenv, b)?;

                // ELSE
                let else_block_id = if let Some(else_expr) = maybe_else_expr {
                    let else_scope_id = fenv.new_scope(ScopeType::Block);
                    let else_span_id = else_expr.span_id;
                    fenv.scope_succ(parent_scope_id, else_scope_id);

                    let else_block_id = self.new_block(None, else_scope_id);
                    self.block_succ(block_id, else_block_id, Successor::BlockScope);
                    self.block_succ(block_id, else_block_id, Successor::Jump);
                    let block = self.get_block_mut(else_block_id);
                    block.next = Some(v_next);

                    let name = b.labels.fresh_key("else");
                    let code = LCode::Label;
                    let entry = CodeEntry::new(
                        else_block_id,
                        code,
                        AstType::Unit,
                        Some(name),
                        else_span_id,
                        VarDefinitionSpace::Reg,
                    );
                    self.push_entry_with_link(entry);
                    self.flatten(else_block_id, NB::ensure_seq(*else_expr), fenv, b)?;
                    else_block_id
                } else {
                    self.block_succ(block_id, v_next, Successor::Jump);
                    v_next
                };

                // condition
                let span_id = condition.span_id;
                let r = self.flatten(block_id, *condition, fenv, b)?;
                let code = LCode::Branch(
                    r.link_id.unwrap().into(),
                    then_block_id.into(),
                    else_block_id.into(),
                );
                let entry = CodeEntry::new(
                    block_id,
                    code,
                    AstType::Unit,
                    None,
                    span_id,
                    VarDefinitionSpace::Reg,
                );
                let v = self.push_entry_with_link(entry);
                Ok(FlattenResult::new(r.block_id, Some(v), AstType::Unit, true))
            }

            Ast::Block(name, args, body) => {
                let new_block_id =
                    fenv.resolve_block_id(block.scope_id, name.into())
                        .expect(&format!(
                            "block not found: {}, {:?}",
                            b.labels.r(name.into()),
                            name
                        ));

                let new_block = self.get_block(new_block_id);
                let new_scope_id = new_block.scope_id;
                self.block_succ(block_id, new_block_id, Successor::BlockScope);
                self.start_block(
                    new_block_id,
                    new_scope_id,
                    &AstType::Unit,
                    &[],
                    &args,
                    AstType::Unit,
                    Some(name),
                    span_id,
                    VarDefinitionSpace::Default,
                    fenv,
                    b,
                );
                let r = self.flatten(new_block_id, NB::ensure_seq(*body), fenv, b)?;

                Ok(FlattenResult::new(
                    new_block_id,
                    r.link_id,
                    AstType::Unit,
                    true,
                ))
            }

            Ast::Ternary(c, x, y) => {
                // expression, non-terminal
                let block = self.get_block(block_id);
                let scope_id = block.scope_id;

                // Condition
                let rc = self.flatten(block_id, *c, fenv, b)?;

                // THEN
                let then_scope_id = fenv.new_scope(ScopeType::Region);
                fenv.scope_succ(scope_id, then_scope_id);
                let then_span_id = x.span_id;
                //let then_ty = AstType::Int; //b.types.r(then_ty_id);
                let then_ast = AstNode::make_yield(*x);
                let then_block_id = self.new_block(None, then_scope_id);
                self.block_succ(rc.block_id, then_block_id, Successor::Operation);
                self.block_succ(rc.block_id, then_block_id, Successor::Jump);

                let name = b.labels.fresh_key("t_then");
                let code = LCode::Label;
                let entry = CodeEntry::new(
                    then_block_id,
                    code,
                    AstType::Unit,
                    Some(name),
                    then_span_id,
                    VarDefinitionSpace::Reg,
                );
                let _then_link_id = self.push_entry_with_link(entry);
                let r = self.flatten(then_block_id, then_ast, fenv, b)?;
                let then_ty = r.ty;

                // ELSE
                let else_span_id = y.span_id;
                let else_scope_id = fenv.new_scope(ScopeType::Region);
                fenv.scope_succ(scope_id, else_scope_id);
                let else_ast = AstNode::make_yield(*y);
                let else_block_id = self.new_block(None, else_scope_id);
                self.block_succ(rc.block_id, else_block_id, Successor::Operation);
                self.block_succ(rc.block_id, else_block_id, Successor::Jump);
                let code = LCode::Label;
                let name = b.labels.fresh_key("t_else");
                let entry = CodeEntry::new(
                    else_block_id,
                    code,
                    AstType::Unit,
                    Some(name),
                    else_span_id,
                    VarDefinitionSpace::Reg,
                );
                let _else_link_id = self.push_entry_with_link(entry);
                let r = self.flatten(else_block_id, else_ast, fenv, b)?;
                let else_ty = r.ty;
                if else_ty != then_ty {
                    b.push_error(
                        &format!("Ternary branches type mismatch: {}, {}", then_ty, else_ty),
                        then_span_id,
                    );
                }
                //assert_eq!(else_ty, then_ty);

                let code = LCode::Ternary(
                    rc.link_id.unwrap().into(),
                    then_block_id.into(),
                    else_block_id.into(),
                );
                let entry = CodeEntry::new(
                    rc.block_id,
                    code,
                    then_ty.clone(),
                    None,
                    span_id,
                    VarDefinitionSpace::Reg,
                );
                let v = self.push_entry_with_link(entry);
                Ok(FlattenResult::new(rc.block_id, Some(v), then_ty, false))
            }

            Ast::Yield(maybe_expr) => {
                // yield is terminal
                let mut v_block = block_id;
                let mut ty = AstType::Unit;
                if let Some(expr) = maybe_expr {
                    let r = self.flatten(block_id, *expr, fenv, b)?;
                    if let Some(v) = r.link_id {
                        v_block = r.block_id;
                        ty = r.ty.clone();
                        // push single arg
                        let code = LCode::CallValue(v.into());
                        let entry = CodeEntry::new(
                            v_block,
                            code,
                            r.ty,
                            None,
                            node.span_id,
                            VarDefinitionSpace::Reg,
                        );
                        let _ = self.push_entry_with_link(entry);
                    }
                }

                let code = LCode::Yield;
                let entry = CodeEntry::new(
                    v_block,
                    code,
                    ty.clone(),
                    None,
                    node.span_id,
                    VarDefinitionSpace::Reg,
                );
                let v = self.push_entry_with_link(entry);
                Ok(FlattenResult::new(v_block, Some(v), ty, true))
            }

            Ast::ControlFlowMarker(ControlFlowMarker::BlockStart(name, args)) => {
                // all blocks should have been forward declared in the sequence
                let name = name.unwrap();
                let current_block_id = fenv.resolve_block_id(block.scope_id, name.into()).unwrap();
                assert_eq!(0, args.len());
                let next = block.next;
                let current_block = self.get_block_mut(current_block_id);
                current_block.next = next;
                let current_scope_id = current_block.scope_id;
                self.block_succ(block_id, current_block_id, Successor::BlockScope);

                self.start_block(
                    current_block_id,
                    current_scope_id,
                    &AstType::Unit,
                    &[],
                    &[],
                    AstType::Unit,
                    Some(name),
                    span_id,
                    VarDefinitionSpace::Reg,
                    fenv,
                    b,
                );

                Ok(FlattenResult::new(
                    current_block_id,
                    None,
                    AstType::Unit,
                    false,
                ))
            }

            Ast::ControlFlowMarker(ControlFlowMarker::Goto(label)) => {
                // Goto is terminal
                if let Some(target_block_id) = fenv.resolve_block_id(block.scope_id, label.into()) {
                    let link_id =
                        self.add_jump(block_id, target_block_id.into(), vec![], node.span_id);
                    Ok(FlattenResult::new(
                        block_id,
                        Some(link_id),
                        AstType::Unit,
                        true,
                    ))
                } else {
                    b.push_error(
                        &format!("Block name not found: {}", b.labels.r(label.into())),
                        node.span_id,
                    );
                    Err(Error::new(BlockifyError::Invalid))
                }
            }

            Ast::Loop(name, body) => {
                let block = self.get_block(block_id);
                let next = block.next.unwrap();
                let scope_id = block.scope_id;
                let loop_scope_id = fenv.new_scope(ScopeType::Region);
                fenv.scope_succ(scope_id, loop_scope_id);
                let loop_block_id = self.new_block(None, loop_scope_id);
                self.block_succ(block_id, loop_block_id, Successor::BlockScope);
                fenv.push_loop_blocks(loop_scope_id, Some(name), next.into(), loop_block_id.into());

                let loop_block = self.get_block_mut(loop_block_id);
                loop_block.next = Some(loop_block_id);

                let code = LCode::Label;
                let entry = CodeEntry::new(
                    loop_block_id,
                    code,
                    AstType::Unit,
                    Some(name),
                    body.span_id,
                    VarDefinitionSpace::Reg,
                );
                let _loop_link_id = self.push_entry_with_link(entry);

                self.add_jump(block_id, loop_block_id.into(), vec![], node.span_id);

                self.flatten(loop_block_id, *body, fenv, b)?;

                Ok(FlattenResult::new(block_id, None, AstType::Unit, true))
            }

            Ast::Continue(maybe_name, args) => {
                let block = self.get_block(block_id);
                let scope_id = block.scope_id;

                // args not implemented yet
                assert_eq!(args.len(), 0);
                // loop up loop blocks by name
                if let Some(loop_scope) = fenv.get_loop_scope(scope_id, maybe_name) {
                    let link_id =
                        self.add_jump(block_id, loop_scope.start_block, vec![], node.span_id);
                    Ok(FlattenResult::new(
                        block_id,
                        Some(link_id),
                        AstType::Unit,
                        true,
                    ))
                } else {
                    // mismatch name
                    b.push_error(&format!("Continue without loop"), node.span_id);
                    Err(Error::new(BlockifyError::Invalid))
                }
            }

            Ast::Break(maybe_name, args) => {
                let block = self.get_block(block_id);
                let scope_id = block.scope_id;

                // args not implemented yet
                assert_eq!(args.len(), 0);
                // loop up loop blocks by name
                if let Some(loop_scope) = fenv.get_loop_scope(scope_id, maybe_name) {
                    let link_id =
                        self.add_jump(block_id, loop_scope.next_block, vec![], node.span_id);
                    Ok(FlattenResult::new(
                        block_id,
                        Some(link_id),
                        AstType::Unit,
                        true,
                    ))
                } else {
                    // mismatch name
                    b.push_error(&format!("Break without loop"), node.span_id);
                    Err(Error::new(BlockifyError::Invalid))
                }
            }

            Ast::CloseBlock => {
                let block = self.get_block(block_id);
                if let Some(next) = block.next {
                    let link_id = self.add_jump(block_id, next.into(), vec![], node.span_id);
                    Ok(FlattenResult::new(
                        block_id,
                        Some(link_id),
                        AstType::Unit,
                        true,
                    ))
                } else {
                    Ok(FlattenResult::new(block_id, None, AstType::Unit, true))
                }
            }

            Ast::Array(type_id, dims) => {
                let mut link_ids = vec![];
                let mut current_block_id = block_id;
                for d in dims {
                    let r = self.flatten(current_block_id, d, fenv, b)?;
                    current_block_id = r.block_id;
                    link_ids.push(r.link_id.unwrap());
                }
                b.push_error(&format!("AST Error"), node.span_id);
                Err(Error::new(BlockifyError::Invalid))
            }

            /*
            Ast::Lambda(_def) => {
            }

            */
            Ast::Error => {
                b.push_error(&format!("AST Error"), node.span_id);
                Err(Error::new(BlockifyError::Invalid))
            }

            _ => unimplemented!("{:?}", ast),
        }
    }
}

pub fn scope_graph(filename: &str, fenv: &FlattenEnvironment) {
    use petgraph::dot::{Config, Dot};
    let s = format!(
        "{:?}",
        Dot::with_attr_getters(
            &fenv.scopes,
            &[Config::EdgeNoLabel, Config::NodeNoLabel],
            &|_, _er| String::new(),
            &|_, (index, scope)| {
                format!(
                    "label = \"S{}:{:?}\" shape=\"{:?}\"",
                    index.index(),
                    &scope.scope_type,
                    &scope.scope_type
                )
            }
        )
    );
    println!("saved graph {:?}", filename);
    println!("{}", s);
    std::fs::write(filename, s).unwrap();
}

pub fn save_graph(blockify: &dyn ICodeModule, filename: &str, b: &NB) {
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

fn def_to_type(def: &Lambda, b: &mut NB) -> AstType {
    /*
    let params = def
        .params
        .iter()
        .map(|p| {
            let ty = b.types.r(p.ty);
            ty.clone()
        })
        .collect();
    */

    let arg_type = b.types.r(def.arg_type).clone();
    let return_type = b.types.r(def.return_type).clone();
    let fun_ty = AstType::Func(arg_type.into(), return_type.into());
    fun_ty
}

fn jump_if_needed(ast: AstNode, b: &mut NB) -> AstNode {
    let span_id = ast.span_id;
    let mut reader = SequenceReader::new();
    let mut seq = reader.build(ast.to_vec(), b);
    if let Some(first) = seq.first() {
        if let Ast::Block(key, _args, _body) = &first.node {
            let jump = NB::goto(*key).node(span_id);
            seq.insert(0, jump);
        }
    }
    NB::seq(seq, span_id)
}
