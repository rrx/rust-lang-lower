use super::resolve_attribute;
use anyhow::Error;
use anyhow::Result;
use compile_core::{
    Argument,
    AssignTarget,
    Ast,
    AstNode,
    AstType,
    BuiltinId,
    ControlFlowMarker,
    //BinaryOperation, BuiltinId, ControlFlowMarker,
    Lambda,
    LinkOptions,
    Literal,
    NaryOperation,
    ReturnType,
    //ParameterNode,
    SpanId,
    StringKey,
    //UnaryOperation,
    VarDefinitionSpace,
};

use std::collections::{HashMap, HashSet};

use std::convert::Into;

use crate::{
    BlockGraph, BlockId, BlockifyError, Builtin, CodeOffset, CodeRow, ICodeModule, LCode, LinkId,
    NodeBuilder as NB, ScopeGraph, ScopeId, ScopeType, StringLabel, Successor, TemplateId, ValueId,
    VariantId,
};

use tabled::{settings::Style, Table};

#[derive(Debug, Clone)]
pub struct CodeEntry {
    next: LinkId,
    prev: LinkId,
    pub(super) code: LCode,
    pub(super) name: Option<StringKey>,
    pub(super) link: Option<LinkId>,
    pub(super) block_id: BlockId,
    pub(super) ty: AstType,
    pub(super) span_id: SpanId,
    pub(super) mem: VarDefinitionSpace,
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
            next: LinkId(0),
            prev: LinkId(0),
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

    pub fn dump(&self) {
        //let name = self.name.map(|key| b.labels.r(key.into())).unwrap_or("".to_string());
        println!(
            "[{}]{:?}, name:{:?}, ty:{}",
            self.block_id, self.code, self.name, self.ty
        );
    }
}

#[derive(Debug)]
pub struct FlattenResult {
    link_id: Option<LinkId>,
}

impl FlattenResult {
    pub fn link(link_id: LinkId) -> Self {
        Self {
            link_id: Some(link_id),
        }
    }
    pub fn statement() -> Self {
        Self { link_id: None }
    }
}

#[derive(PartialEq)]
pub enum FlattenMode {
    Function,
    Template,
}

pub struct Flatten {
    module_key: Option<StringKey>,
    pub(super) link: LinkOptions,
    entries: Vec<CodeEntry>,
    pub(super) blocks: BlockGraph,
    ast_templates: Vec<(Lambda, SpanId)>,
    messages: Vec<(String, SpanId)>,
    pub mode: FlattenMode,
    pub(crate) static_scope: Option<ScopeId>,
    pub(crate) static_block: Option<BlockId>,
    pub(crate) current_block: BlockId,
    pub scopes: ScopeGraph,
    block_links: HashMap<BlockId, LinkId>,
    functions: HashMap<StringKey, LinkId>,
}

impl ICodeModule for Flatten {
    fn shared_libraries(&self) -> Vec<String> {
        self.link.shared_libraries()
    }

    fn lookup_name(&self, name: &StringKey) -> Option<LinkId> {
        self.functions.get(name).cloned()
    }

    fn get_span_id(&self, value_id: ValueId) -> SpanId {
        let link_id = LinkId(value_id.index() as u32);
        let entry = self.get_entry(link_id);
        entry.span_id
    }

    fn get_name(&self, offset: CodeOffset) -> Option<StringLabel> {
        let value_id = self.resolve_code_offset(offset);
        let link_id = LinkId(value_id.index() as u32);
        self.get_entry(link_id).name.map(|n| n.into())
    }

    fn get_code(&self, value_id: ValueId) -> &LCode {
        let link_id = LinkId(value_id.index() as u32);
        &self.get_entry(link_id).code
    }

    fn get_next(&self, value_id: ValueId) -> Option<ValueId> {
        let value_id = LinkId(value_id.index() as u32);
        let entry = self.get_entry(value_id);
        if entry.next != value_id {
            Some(ValueId(entry.next.index() as u32))
        } else {
            None
        }
    }

    /*
    fn get_prev(&self, value_id: ValueId) -> Option<ValueId> {
        let value_id = LinkId(value_id.index() as u32);
        let entry = self.get_entry(value_id);
        if entry.prev != value_id {
            Some(ValueId(entry.prev.index() as u32))
        } else {
            None
        }
    }
    */

    fn get_block_successors(&self, entry_id: ValueId) -> Vec<(Successor, CodeOffset)> {
        let entry_id = LinkId(entry_id.index() as u32);
        let entry = self.get_entry(entry_id);
        let block_id = entry.block_id;
        self.blocks.get_block_successors(block_id)
    }

    fn get_type(&self, v: CodeOffset) -> AstType {
        let value_id = self.resolve_code_offset(v);
        let value_id = LinkId(value_id.index() as u32);
        let entry = self.get_entry(value_id);
        entry.clone().ty
    }

    fn get_entry_id(&self, value_id: ValueId) -> ValueId {
        let value_id = LinkId(value_id.index() as u32);
        let block_id = self.get_entry(value_id).block_id;
        let link_id = *self
            .block_links
            .get(&block_id)
            .expect(&format!("Unable to find block {}", block_id));
        ValueId(link_id.index() as u32)
    }

    fn is_in_static_scope(&self, offset: CodeOffset) -> bool {
        let value_id = self.resolve_code_offset(offset);
        let value_id = LinkId(value_id.index() as u32);
        let entry = self.get_entry(value_id);
        let block = self.blocks.get_block(entry.block_id);
        let scope = self.scopes.get_scope(block.scope_id);
        scope.scope_type == ScopeType::Static
    }

    fn get_mem(&self, offset: CodeOffset) -> &VarDefinitionSpace {
        let value_id = self.resolve_code_offset(offset);
        let value_id = LinkId(value_id.index() as u32);
        &self.get_entry(value_id).mem
    }

    fn resolve_code_offset(&self, code_offset: CodeOffset) -> ValueId {
        match code_offset {
            CodeOffset::Value(v) => v,
            CodeOffset::Link(v) => ValueId(v.index() as u32),
            CodeOffset::Block(block_id) => {
                let link_id = *self
                    .block_links
                    .get(&block_id)
                    .expect(&format!("Missing block {}", block_id));
                ValueId(link_id.index() as u32)
            }
        }
    }

    fn get_entry_id_from_block_id(&self, block_id: BlockId) -> ValueId {
        self.resolve_code_offset(block_id.into())
    }

    fn code_count(&self) -> usize {
        self.entries.len()
    }

    fn dump_code_table(&self, filename: &str, b: &mut NB) {
        let mut rows = vec![];
        for entry in self.entries.iter() {
            let link_id = entry.link.unwrap();
            let value_id = ValueId(link_id.index() as u32);
            if let Some(row) = self.get_code_row(value_id, b) {
                rows.push(row);
            } else {
                println!("Unable to load entry: {}", value_id);
            }
        }
        let s = Table::new(rows).with(Style::sharp()).to_string();
        println!("{}", s);
        std::fs::write(filename, s).unwrap();
    }
}

impl Flatten {
    pub fn new() -> Self {
        let blocks = BlockGraph::new();

        Self {
            module_key: None,
            entries: vec![],
            blocks,
            link: LinkOptions::new(),
            ast_templates: vec![],
            messages: vec![],
            mode: FlattenMode::Function,
            static_scope: None,
            static_block: None,
            current_block: BlockId(0),
            scopes: ScopeGraph::new(),
            block_links: HashMap::new(),
            functions: HashMap::new(),
        }
    }

    pub fn get_code_row(&self, v: ValueId, b: &mut NB) -> Option<CodeRow> {
        let link_id = LinkId(v.index() as u32);
        let entry = self.get_entry(link_id);
        let code = self.get_code(v);
        //let ty = self.get_type(v.into());

        let mem = self.get_mem(v.into());
        let block_id = entry.block_id;
        let block = self.blocks.node_weight(block_id.into()).unwrap();
        //println!("block: {:?}", (block_id, block, v, entry));

        //let next = self.get_next(v).unwrap_or(v).index();
        //let prev = self.get_prev(v).unwrap_or(v).index();
        //println!("row: {}, {:?}", v, (self.entries.len()));
        let entry_id = self.get_entry_id(v);

        let r_ty = if let Some(r_ty) = b.types.u.resolve(&entry.ty) {
            r_ty
        } else {
            entry.ty.clone()
        };
        //println!("X: {} => {}", &entry.ty, &r_ty);

        //let is_unknown = r_ty.as_ref().map(|ty| ty.is_unknown()).unwrap_or(true);
        //let s_ty = format!("{}", &r_ty.unwrap_or(ty)); //AstType::Error));
        let is_unknown = r_ty.is_unknown();
        let s_ty = format!("{}", &r_ty);

        let scope_id = block.scope_id;

        Some(CodeRow {
            pos: v.index(),
            link: entry.link.unwrap().index(),
            next: entry.next.index(),
            //prev: entry.prev.index(),
            value: self.code_to_string(v, b),
            //ty: ty.clone(),
            ty: s_ty,
            //r_ty: r_ty.unwrap_or(AstType::Error),
            mem: format!("{:?}", mem),
            name: self
                .get_name(v.into())
                .map(|key| b.labels.r(key))
                .unwrap_or("".to_string())
                .to_string(),
            span_id: self.get_span_id(v).index(),
            scope_id: scope_id.index(),
            entry_id: entry_id.index(),
            block_id: block_id.index(),
            term: code.is_term(),
            dead: block.dead,
            unknown: is_unknown,
        })
    }

    pub fn type_inference_enforce(&mut self, b: &mut NB) {
        b.types.dump();
        for entry in self.entries.iter_mut() {
            if !entry.ty.is_unknown() {
                continue;
            }

            if let Some(ty) = b.types.u.resolve(&entry.ty) {
                /*
                b.push_warning(
                    &format!("Late Unresolved Type: {}=>{}", &entry.ty, &ty),
                    entry.span_id,
                );
                */
                entry.ty = ty;
            } else {
                b.push_error(&format!("Unresolved Type: {}", &entry.ty), entry.span_id);
            }
        }
    }

    pub fn dump_code_table(&self, filename: &str, b: &mut NB) {
        let mut rows = vec![];
        for entry in self.entries.iter() {
            let link_id = entry.link.unwrap();
            let value_id = ValueId(link_id.index() as u32);
            if let Some(row) = self.get_code_row(value_id, b) {
                rows.push(row);
            } else {
                println!("Unable to load entry: {}", value_id);
            }
        }
        let s = Table::new(rows).with(Style::sharp()).to_string();
        println!("{}", s);
        std::fs::write(filename, s).unwrap();
    }

    pub fn flow_graph(&self, filename: &str, b: &NB) -> Result<()> {
        crate::flatten_graph::flow_graph(self, &self.blocks, filename, b)
    }

    pub fn dump_scopes(&self, _b: &NB) {
        petgraph::dot::Dot::with_config(&self.scopes.0, &[petgraph::dot::Config::EdgeNoLabel]);
    }

    pub fn static_scope_id(&self) -> ScopeId {
        self.static_scope.unwrap()
    }

    pub fn static_block_id(&self) -> BlockId {
        self.static_block.unwrap()
    }

    pub fn switch_blocks(&mut self, block_id: BlockId) {
        self.current_block = block_id;
    }

    pub fn current_block_id(&self) -> BlockId {
        self.current_block
    }

    pub fn dump_scope(&self, block_id: BlockId, b: &NB) {
        let block = self.blocks.get_block(block_id);
        self.scopes.dump_scope(block.scope_id, b);
    }

    pub fn dump_blocks(&self) {
        for node in self.blocks.node_indices() {
            let block_id: BlockId = node.into();
            let block = self.blocks.node_weight(node).unwrap();
            println!("[{}] Block: {:?}", block_id, block);
        }
    }

    pub fn save_graph(&self, filename: &str) {
        let s = format!(
            "{:?}",
            petgraph::dot::Dot::with_attr_getters(
                &self.blocks.0,
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

    pub fn resolve_all_function_name(
        &self,
        block_id: BlockId,
        name: &StringKey,
    ) -> Vec<(VariantId, AstType, LinkId)> {
        let mut out = vec![];
        let block = self.blocks.get_block(block_id);
        for scope_id in self.scopes.walk_scopes(block.scope_id) {
            let scope = self.scopes.get_scope(scope_id);
            //println!("resolve: {}, {}", scope_id, scope.entries.len());
            if let Some(e) = scope.entries.get(name) {
                for (index, v) in e.variants.iter().enumerate() {
                    let variant_id = VariantId(index as u32);
                    out.push((variant_id, v.ty.clone(), v.link_id));
                }
            }
        }
        out
    }

    pub fn resolve_function_name(
        &self,
        block_id: BlockId,
        name: &StringKey,
        ty: &AstType,
        b: &mut NB,
    ) -> Option<(VariantId, AstType, LinkId)> {
        let mut result = None;
        let snapshot = b.types.u.snapshot();
        for (variant_id, r_ty, link_id) in self.resolve_all_function_name(block_id, &name) {
            println!("trying {}, {}<=>{}", variant_id, &ty, &r_ty);
            if let Ok(_) = b.types.u.unify(&ty, &r_ty) {
                result = Some((variant_id, r_ty, link_id));
                break;
            }
        }
        b.types.u.rollback_to(snapshot);
        result
    }

    pub fn resolve_name(&self, block_id: BlockId, name: StringKey) -> Option<LinkId> {
        // resolve scope through the tree, starting at the current scope
        let block = self.blocks.get_block(block_id);
        for scope_id in self.scopes.walk_scopes(block.scope_id) {
            let scope = self.scopes.get_scope(scope_id);
            if let Some(data) = scope.names.get(&name) {
                return Some(data.clone());
            }
        }
        None
    }

    pub fn resolve_declaration(&self, block_id: BlockId, name: StringKey) -> Option<LinkId> {
        // resolve scope through the tree, starting at the current scope
        let block = self.blocks.get_block(block_id);
        for scope_id in self.scopes.walk_scopes(block.scope_id) {
            let scope = self.scopes.get_scope(scope_id);
            if let Some(data) = scope.declarations.get(&name) {
                return Some(data.clone());
            }
        }
        None
    }

    pub fn resolve_lambda_scope(&self, block_id: BlockId, name: StringLabel) -> Option<ScopeId> {
        // resolve scope through the tree, starting at the current scope
        let block = self.blocks.get_block(block_id);
        for scope_id in self.scopes.walk_scopes(block.scope_id) {
            let scope = self.scopes.get_scope(scope_id);
            if let Some(_data) = scope.lambdas.get(&name) {
                return Some(scope_id);
            }
        }
        None
    }

    pub fn resolve_template(&self, block_id: BlockId, name: StringKey) -> Option<LinkId> {
        // resolve scope through the tree, starting at the current scope
        let block = self.blocks.get_block(block_id);
        for scope_id in self.scopes.walk_scopes(block.scope_id) {
            let scope = self.scopes.get_scope(scope_id);
            if let Some(link_id) = scope.templates.get(&name) {
                return Some(*link_id);
            }
        }
        None
    }

    pub fn resolve_lambda(
        &self,
        block_id: BlockId,
        name: StringKey,
    ) -> Option<(ScopeId, Lambda, SpanId)> {
        match self.resolve_lambda_scope(block_id, name.into()) {
            Some(scope_id) => {
                let scope = self.scopes.get_scope(scope_id);
                if let Some(template_id) = scope.lambdas.get(&name.into()).cloned() {
                    let (def, span_id) = self.get_ast_template(template_id).clone();
                    Some((scope_id, def, span_id))
                } else {
                    None
                }
            }
            None => None,
        }
    }

    pub fn flatten_module(node: AstNode, mode: FlattenMode, b: &mut NB) -> Result<Self> {
        // setup environment with static scope and block
        // blocks will be moved into environment eventually
        // FlattenEnvironment represents the module level structures
        let mut f = Self::new();

        let scope_id = f.scopes.new_scope(ScopeType::Static);
        f.static_scope = Some(scope_id);

        let static_scope = f.static_scope_id();
        let block_id = f.blocks.new_block(static_scope);
        f.current_block = block_id;
        f.static_block = Some(block_id);

        if let Ast::Module(key, body) = node.node {
            f.mode = mode;
            let static_block_id = f.current_block_id();
            f.module_key = Some(key);

            let block = f.blocks.get_block(static_block_id);
            let static_scope_id = block.scope_id;
            let static_scope = f.scopes.get_scope_mut(static_scope_id);
            static_scope.entry_block = Some(static_block_id);

            f.switch_blocks(static_block_id);
            f.push_start_block(
                static_scope_id,
                AstType::Func(
                    AstType::Struct(vec![]).into(),
                    ReturnType::Single(AstType::Unit).into(),
                ),
                Some(key),
                node.span_id,
                VarDefinitionSpace::Static,
            );

            f.static_block = Some(static_block_id);
            f.static_scope = Some(static_scope_id);
            f.switch_blocks(static_block_id);
            let _ = f.push_node(*body, b)?;
            assert_eq!(static_block_id, f.current_block_id());

            //let result = f.push_bake_templates(static_block_id, b);
            //let result = f.push_bake_main_template(b);
            f.drain_diagnostics(b);
            Ok(f)
        } else {
            b.push_error("Not a module", node.span_id);
            Err(Error::new(BlockifyError::Invalid))
        }
    }

    fn drain_diagnostics(&mut self, b: &mut NB) {
        // XXX: This needs to be run before any errors kick in, there must be a better way.
        for (msg, span_id) in self.messages.drain(..) {
            b.push_error(&msg, span_id);
        }
    }

    pub fn finish(&mut self, b: &mut NB) -> Result<()> {
        let dead_blocks = self.blocks.find_dead_blocks_from_graph();
        for block_id in dead_blocks {
            if let Some(link_id) = self.block_links.get(&block_id).cloned() {
                //let v = self.get_entry_id_from_block_id(block_id);
                let entry = self.get_entry(link_id);
                b.push_warning(&format!("Dead Block: {}", block_id), entry.span_id);
            } else {
                let span_id = b.spans.get_span_unknown();
                b.push_warning(&format!("Missing Block: {}", block_id), span_id);
            }
            //let span_id = self.get_span_id(v);
        }
        self.type_inference_enforce(b);
        Ok(())
    }

    pub fn push_bake_main(&mut self, b: &mut NB) -> Result<LinkId> {
        let current_block_id = self.current_block_id();
        let name = b.labels.s("main");
        // reset the block position before each function
        // main is always static context
        self.switch_blocks(self.static_block_id());
        let ty = AstType::func(vec![], AstType::Int);
        let r = self.push_bake(name, ty, b);
        // switch back after bake
        self.switch_blocks(current_block_id);
        r
    }

    pub fn push_bake_templates2(
        &mut self,
        //block_id: BlockId,
        _b: &mut NB,
    ) -> Result<Vec<LinkId>> {
        let block_id = self.static_block_id();
        let block = self.blocks.get_block(block_id);
        let scope_id = block.scope_id;
        let scope = self.scopes.get_scope(scope_id);
        let keys = scope
            .templates
            .iter()
            .map(|s| s.0.clone())
            .collect::<Vec<_>>();

        let links = vec![];
        for _key in keys.iter() {
            // reset the block position before each function
            //let name = b.labels.r(key.into());
            //println!("bake {}", name);
            self.switch_blocks(block_id);
            //let link_id = self.push_bake(*key, None, b)?;
            //links.push(link_id);
        }
        Ok(links)
    }

    pub fn push_bake_all2(&mut self, _b: &mut NB) -> Result<Vec<LinkId>> {
        let static_block_id = self.static_block_id();
        let scope_id = self.static_scope_id();
        let scope = self.scopes.get_scope(scope_id);
        let keys = scope
            .declarations
            .iter()
            .map(|s| s.0.clone())
            .collect::<Vec<_>>();

        let links = vec![];
        for _key in keys.iter() {
            // reset the block position before each function
            self.switch_blocks(static_block_id);
            //let link_id = self.push_bake(*key, None, b)?;
            //links.push(link_id);
        }
        Ok(links)
    }

    fn _insert_entry(&mut self, mut entry: CodeEntry, prev: Option<LinkId>) -> LinkId {
        let index = self.entries.len();
        let link_id = LinkId(index as u32);
        entry.link = Some(link_id);
        if let Some(prev) = prev {
            entry.prev = prev;
        } else {
            entry.prev = link_id;
        }
        entry.next = link_id;
        self.entries.push(entry);
        link_id
    }

    pub fn push_entry_with_link(&mut self, entry: CodeEntry) -> LinkId {
        let entry_is_term = entry.code.is_term();
        let block_id = entry.block_id;
        let span_id = entry.span_id;
        let block = self.blocks.get_block(block_id);
        let link_id = self._insert_entry(entry, block.last());
        let block = self.blocks.get_block(block_id);
        if let Some(last_link_id) = block.last() {
            let last_entry = self.get_entry_mut(last_link_id);
            last_entry.next = link_id;
            let is_term = last_entry.code.is_term();
            if is_term {
                let backtrace = std::backtrace::Backtrace::capture();
                self.messages.push((
                    format!("appending to term block={}\n{}", block_id, backtrace),
                    span_id,
                ));
            }
        }
        self.blocks
            .get_block_mut(block_id)
            .push(link_id, entry_is_term);
        link_id
    }

    pub fn new_scope_and_block(
        &mut self,
        scope_type: ScopeType,
        parent_scope_id: ScopeId,
    ) -> (BlockId, ScopeId) {
        let scope_id = self.scopes.new_scope(scope_type);
        let scope = self.scopes.get_scope_mut(scope_id);
        let block_id = self.blocks.new_block(scope_id);
        scope.entry_block = Some(block_id);
        self.scopes.scope_succ(parent_scope_id, scope_id);
        //println!("new block and scope: {:?}", (block_id, scope_id));
        (block_id, scope_id)
    }

    pub fn get_entry(&self, link_id: LinkId) -> &CodeEntry {
        self.entries.get(link_id.index()).unwrap()
    }

    pub fn get_type(&self, link_id: LinkId) -> &AstType {
        &self.get_entry(link_id).ty
    }

    pub fn get_entry_mut(&mut self, link_id: LinkId) -> &mut CodeEntry {
        self.entries.get_mut(link_id.index()).unwrap()
    }

    pub fn insert_ast_template(&mut self, def: Lambda, span_id: SpanId) -> TemplateId {
        let offset = self.ast_templates.len();
        self.ast_templates.push((def, span_id));
        TemplateId(offset as u32)
    }

    pub fn get_ast_template(&self, template_id: TemplateId) -> &(Lambda, SpanId) {
        self.ast_templates.get(template_id.index()).unwrap()
    }

    pub fn push_sequence(
        &mut self,
        seq: Vec<AstNode>,
        span_id: SpanId,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        let block = self.blocks.get_block(self.current_block_id());
        let start_stack = self.scopes.walk_scopes(block.scope_id);

        for expr in seq {
            let _ = self.push_node(expr, b)?;
        }

        // ensure that we close any blocks that were opened
        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        let scope_id = block.scope_id;
        let end_stack = self.scopes.walk_scopes(scope_id);
        for _ in 0..end_stack.len() - start_stack.len() {
            let ast: Ast = ControlFlowMarker::BlockEnd.into();
            let node = ast.node(span_id);
            let _ = self.push_node(node, b)?;
        }

        // ensure we have no unclaimed labels.
        // throw an error if we do
        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        let scope = self.scopes.get_scope(block.scope_id);
        assert_eq!(scope.unclaimed_labels.len(), 0);

        let link_id = block.last().unwrap();
        Ok(FlattenResult::link(link_id))
    }

    pub fn push_return(
        &mut self,
        values: Vec<(Option<StringKey>, LinkId, AstType, SpanId)>,
        span_id: SpanId,
    ) -> LinkId {
        let _ = self.push_call_values(&values);

        self.push_code(
            LCode::Return,
            AstType::Unit,
            None,
            span_id,
            VarDefinitionSpace::Reg,
        )
    }

    pub fn push_return_block_start(
        &mut self,
        scope_id: ScopeId,
        return_type: AstType,
        span_id: SpanId,
        b: &mut NB,
    ) {
        assert!(return_type.is_composite());
        let name = b.labels.fresh_key("ret");

        let (_v_block, v_args) = self.push_start_block(
            scope_id,
            AstType::Func(
                return_type.clone().into(),
                ReturnType::Single(AstType::Unit).into(),
            ),
            Some(name),
            span_id,
            VarDefinitionSpace::Reg,
        );
        self.push_return(v_args, span_id);
    }

    pub fn is_load_required(&mut self, v: LinkId) -> bool {
        let entry = self.get_entry(v);
        match entry.code {
            LCode::Val(_) => entry.mem.is_static(),
            LCode::Declare => true,
            LCode::Arg(_) => false,
            LCode::Load(_) => false,
            LCode::Tuple(_) => false,
            LCode::NaryOp(_) => false,
            LCode::Op1(_) => false,
            LCode::Op2(_) => false,
            LCode::Call(_) => false,
            LCode::Use(_, _) => false,
            LCode::Label => false,
            LCode::Ternary(_, _, _) => false,
            // shouldn't happen
            LCode::DeclareFunction(_) => unimplemented!(),
            LCode::Extern => unimplemented!(),
            LCode::Store(_, _) => unreachable!(),
            LCode::Noop => unreachable!(),
            LCode::DeclareTemplate(_) => unreachable!(),
            LCode::Return => unreachable!(),
            LCode::Yield => unreachable!(),
            LCode::Jump(_) => unreachable!(),
            LCode::Branch(_, _, _) => unreachable!(),
            LCode::Builtin(_) => unreachable!(),
            LCode::CallValue(_) => unreachable!(),
        }
    }

    pub fn push_loads_if_needed(
        &mut self,
        values: &[(Option<StringKey>, LinkId, AstType, SpanId)],
    ) -> Vec<LinkId> {
        let mut links = vec![];
        for (maybe_key, v, ty, span_id) in values {
            let out = if self.is_load_required(*v) {
                let link_id = self.push_code(
                    LCode::Load(*v),
                    ty.clone(),
                    *maybe_key,
                    *span_id,
                    VarDefinitionSpace::Reg,
                );
                link_id
            } else {
                *v
            };
            links.push(out);
        }
        links
    }

    pub fn push_call_values(
        &mut self,
        values: &[(Option<StringKey>, LinkId, AstType, SpanId)],
    ) -> Vec<LinkId> {
        let mut updated_values = vec![];
        for (maybe_key, v, ty, span_id) in values {
            let out = if self.is_load_required(*v) {
                let link_id = self.push_code(
                    LCode::Load(*v),
                    ty.clone(),
                    *maybe_key,
                    *span_id,
                    VarDefinitionSpace::Reg,
                );
                (*maybe_key, link_id, ty, *span_id)
            } else {
                (*maybe_key, *v, ty, *span_id)
            };

            updated_values.push(out);
        }

        return updated_values
            .into_iter()
            .map(|(maybe_key, v, ty, span_id)| {
                self.push_code(
                    LCode::CallValue(v.into()),
                    ty.clone(),
                    maybe_key,
                    span_id,
                    VarDefinitionSpace::Reg,
                )
            })
            .collect::<Vec<_>>();
    }

    pub fn push_jump(
        &mut self,
        target_id: BlockId,
        jump_args: Vec<(Option<StringKey>, LinkId, AstType, SpanId)>,
        span_id: SpanId,
    ) -> LinkId {
        // Construct the argument type
        let arg_ty = AstType::Struct(
            jump_args
                .iter()
                .map(|j| (j.0, j.2.clone()))
                .collect::<Vec<_>>(),
        );

        let _link_ids = self.push_call_values(
            &jump_args
                .into_iter()
                .map(|(key, v, ty, span_id)| (key, v, ty, span_id))
                .collect::<Vec<_>>(),
        );

        self.blocks
            .block_succ(self.current_block_id(), target_id, Successor::Jump);
        self.blocks
            .block_succ(self.current_block_id(), target_id, Successor::BlockScope);

        self.push_code(
            LCode::Jump(target_id.into()),
            AstType::Func(arg_ty.into(), ReturnType::Single(AstType::Unit).into()),
            None,
            span_id,
            VarDefinitionSpace::Reg,
        )
    }

    pub fn push_function_args(
        &mut self,
        def: &Lambda,
        args: Vec<Argument>,
        span_id: SpanId,
        b: &mut NB,
    ) -> Result<(
        AstType,
        Vec<(Option<StringKey>, LinkId, AstType, SpanId)>,
        AstType,
    )> {
        let func_arg = b.types.r(def.arg_type).clone();
        let ret = b.types.r(def.return_type).clone();

        // A rough outline of this large function
        // - We need to take in a list of calling args, and the function definition,
        //   and merge them together to create the actual args that will call the function
        // - There are a number of transformations that need to happen here.
        // - We populate defaults before calling the function.  Removing defaults is an
        //   optimization that can happen elsewhere.
        // - We handle *args, and **kwargs here, to make sure those variables are typed
        //   correctly.
        //
        // 1. Create value map, with capacity = to the number of fields
        // 2. Copy defaults into the map
        // 3. Keep a list of fields that have been populated_set
        // 4. Iterate over the argument list
        // 4a. For each positional, lookup the associated field in the definition
        //    for normal types, add the value to the value map
        //    add the field name to the populated_set
        // 4b. For args type, we start an args sequence.  Any positionals after this get added
        //    to the args sequence
        // 4c. For named args, we add them to the value map
        //    Check to make sure it hasn't already been added by checking the populated_set
        // 4d. For kwargs type, this is the final one in the list
        //    If the value is known, we can populate the value map
        //    Remaining values go into the kwargs map
        //    If the value is only known at runtime, then we iterate over the fields in kwargs
        //    - add them to the value map, ensure we aren't double adding with the
        //    populated_set
        //    If the item isn't in the field list, then it gets added to the kwargs map
        // 5. Add the args sequence, and the kwargs map to the values map
        // 6. Iterate over the field list, and create an ordered arguments list
        // 7. Pass that to the function

        let fields_list = func_arg.fields();
        let mut value_map = HashMap::with_capacity(fields_list.len());
        let mut populated_set = HashSet::with_capacity(fields_list.len());
        let mut args_seq = vec![];
        let kwargs_map = HashMap::new();
        let mut def_has_args = false;
        let mut args_seq_started = false;
        //let mut def_has_kwargs = false;

        // copy defaults into value map
        for (key, value) in def.defaults.iter() {
            value_map.insert(*key, value.clone());
        }

        for (index, arg) in args.iter().enumerate() {
            let is_last_arg = index == args.len() - 1;
            match arg {
                // these are the first args, and they don't have associated names
                // so we look them up in the field list
                // We only need to look until we reach the args type
                // If we reach the kwargs type before we reach the args type,
                // then that means we don't have an open_args function
                // we just handle it by copying it to the kwargs_map
                Argument::Positional(expr) => {
                    if args_seq_started {
                        args_seq.push(*(*expr).clone());
                    } else {
                        if let Some((key, ty)) = fields_list.get(index) {
                            let key = key.unwrap(); // field names should exist?
                                                    // we have the field, it can either be a regular type, Args, or
                                                    // Kwargs type
                            match ty {
                                AstType::Args(_) => {
                                    args_seq_started = true;
                                    // push arg into sequence
                                    args_seq.push(*(*expr).clone());
                                }
                                AstType::KwArgs(_) => {
                                    // not sure how to copy this to the kwargs map, we are
                                    // missing some types
                                    unimplemented!()
                                }
                                _ => {
                                    // just add to the value map
                                    value_map.insert(key, *(*expr).clone());
                                    populated_set.insert(key);
                                }
                            }
                        } else {
                            b.push_error(&format!("Extra positional field: {}", index), span_id);
                        }
                    }
                }

                // named arguments follow positional args
                Argument::Named(key, expr) => {
                    // make sure we don't double add
                    if populated_set.contains(key) {
                        let name = b.labels.r(key.into());
                        b.push_error(&format!("Keyword argument duplicate: {}", name), span_id);
                    }
                    //assert!(!populated_set.contains(key));
                    value_map.insert(*key, *(*expr).clone());
                    populated_set.insert(*key);
                }
                Argument::Args(_key, expr) => {
                    // just extend the args sequence
                    // this probably needs to be done at run time, not compile time
                    args_seq.extend(
                        expr.clone()
                            .to_vec()
                            .into_iter()
                            .map(|x| x)
                            .collect::<Vec<_>>(),
                    );
                    def_has_args = true;
                }
                Argument::KwArgs(_key, _expr) => {
                    assert!(is_last_arg); //kwargs should be last in the args
                                          // not quite sure how to proceed here.
                                          //def_has_kwargs = true;
                    unimplemented!()
                }
            }
        }

        //if let Some(key) = def.open_args {
        //value_map.insert(key, Ast::Sequence(args_seq).into());
        //}
        // Do the same with kwargs eventually

        let args: Vec<Argument> = fields_list
            .iter()
            .map(|(field_key, field_ty)| {
                let field_key = field_key.unwrap();
                match field_ty {
                    AstType::Args(_) => Argument::Args(field_key, args_seq.clone()),
                    AstType::KwArgs(_) => Argument::KwArgs(field_key, kwargs_map.clone()),
                    _ => Argument::Named(field_key, value_map.remove(&field_key).unwrap().into()),
                }
            })
            .collect();

        if args_seq.len() > 0 && def_has_args {
            // extra fields
            b.push_error(
                &format!("extra fields, no args field: {:?}", args_seq),
                span_id,
            );
        }

        if fields_list.len() != args.len() {
            b.push_error(
                &format!(
                    "Call arity mismatch: {}<=>{}",
                    fields_list.len(),
                    args.len()
                ),
                span_id,
            );
            assert!(false);
            return Err(Error::new(BlockifyError::Invalid));
        }

        let values = self.push_arguments(args, span_id, b)?;

        let call_ty = AstType::Struct(
            values
                .iter()
                .map(|v| (v.0, v.2.clone()))
                .collect::<Vec<_>>(),
        );

        Ok((ret.clone(), values, call_ty))
    }

    fn push_arguments(
        &mut self,
        args: Vec<Argument>,
        span_id: SpanId,
        b: &mut NB,
    ) -> Result<Vec<(Option<StringKey>, LinkId, AstType, SpanId)>> {
        //let mut current_block_id = self.block_id;
        let mut link_ids = vec![];
        let mut values = vec![];
        for a in args.into_iter() {
            match a {
                Argument::Positional(expr) => {
                    //self.switch_blocks(current_block_id);
                    let r = self.push_node(*expr, b)?;
                    let link_id = r.link_id.unwrap();
                    let ty = self.get_type(link_id).clone();
                    values.push((None, link_id, ty, span_id));
                    link_ids.push(link_id);
                }
                Argument::Named(key, expr) => {
                    //self.switch_blocks(current_block_id);
                    let r = self.push_node(*expr, b)?;
                    let link_id = r.link_id.unwrap();
                    let ty = self.get_type(link_id).clone();
                    values.push((Some(key), link_id, ty, span_id));
                    link_ids.push(link_id);
                }
                Argument::Args(key, exprs) => {
                    let mut args_values = vec![];
                    for expr in exprs {
                        let span_id = expr.span_id;
                        //self.switch_blocks(current_block_id);
                        let r = self.push_node(expr, b)?;
                        let link_id = r.link_id.unwrap();
                        let ty = self.get_type(link_id).clone();
                        args_values.push((Some(key), link_id, ty, span_id));
                    }

                    self.push_call_values(&args_values);

                    let struct_ty = AstType::Struct(
                        args_values
                            .iter()
                            .map(|(key, _, ty, _)| (*key, ty.clone()))
                            .collect::<Vec<_>>(),
                    );
                    let link_id = self.push_code(
                        LCode::NaryOp(NaryOperation::Struct),
                        struct_ty.clone(),
                        None,
                        span_id,
                        VarDefinitionSpace::Stack,
                    );
                    values.push((Some(key), link_id, struct_ty.clone(), span_id));
                    link_ids.push(link_id);
                }
                Argument::KwArgs(key, _expr) => {
                    let node: AstNode = 1.into();
                    //self.switch_blocks(current_block_id);
                    let r = self.push_node(node, b)?;
                    let link_id = r.link_id.unwrap();
                    let ty = self.get_type(link_id).clone();
                    values.push((Some(key), link_id, ty, span_id));
                    link_ids.push(link_id);
                }
            }
        }
        //self.block_id = current_block_id;
        Ok(values)
    }

    fn push_bake_static(
        &mut self,
        name: StringKey,
        def: Lambda,
        def_span_id: SpanId,
        call_ty: AstType,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> Result<(LinkId, AstType, AstType)> {
        let s = b.labels.r(name.into());
        let global_key = b.labels.fresh_key(&s);
        //let s_global = b.labels.r(global_key.into());
        let current_block_id = self.current_block_id();
        self.switch_blocks(self.static_block_id());

        let def_func_type = b.types.r(def.fun_type).clone();

        // refresh variables
        let (def_arg_ty, ret_ty) = if let AstType::Func(arg, ret) = def_func_type {
            if let ReturnType::Single(ret_ty) = *ret {
                (b.types.refresh(*arg.clone()), b.types.refresh(ret_ty))
            } else {
                unreachable!()
            }
        } else {
            unreachable!()
        };
        let def_func_type = AstType::Func(
            def_arg_ty.clone().into(),
            ReturnType::Single(ret_ty.clone()).into(),
        );
        //println!("bake_static: call: {}, def: {}", &call_ty, &def_func_type);

        // construct call function type
        // function type, based on the caller
        let call_func_type = AstType::Func(
            AstType::Struct(call_ty.fields()).into(),
            ReturnType::Single(ret_ty.clone()).into(),
        );

        // match call type with function type
        //println!(
        //"call_func: {}, def_func: {}",
        //&call_func_type, def_func_type
        //);
        if b.types.u.unify(&call_func_type, &def_func_type).is_err() {
            let ty1 = b.types.u.resolve(&call_func_type).unwrap();
            let ty2 = b.types.u.resolve(&def_func_type).unwrap();
            b.push_error_labels(vec![
                b.primary_label(
                    &format!("Type Mismatch Func: caller: {}", &ty1),
                    call_span_id,
                ),
                b.secondary_label(&format!("source type: {}", &ty2), def_span_id),
            ]);
        }

        // if it's defined in static scope, just call it
        //println!("[{},{}] RX:  {}", s, s_global, &call_func_type);
        let (_variant_id, v_entry) = if let Some((variant_id, r_ty, v_entry)) =
            self.resolve_function_name(current_block_id, &name, &call_func_type, b)
        {
            println!("[{}] R2: {}, {:?}", s, call_func_type, (v_entry));
            if b.types.u.unify(&call_func_type, &r_ty).is_err() {
                b.push_error_labels(vec![
                    b.primary_label(
                        &format!("Type Mismatch Func: caller: {}", &call_func_type),
                        call_span_id,
                    ),
                    b.secondary_label(&format!("source type: {}", &r_ty), def_span_id),
                ]);
            }

            (variant_id, v_entry)
        } else {
            // if it's not already baked, we need to do that here
            self.switch_blocks(self.static_block_id());
            let result = self.push_bake_function(
                //v_entry,
                def,
                call_func_type.clone(),
                name,
                global_key,
                ScopeType::Function,
                Successor::FunctionDeclaration,
                b,
            );
            if result.is_err() {
                self.drain_diagnostics(b);
            }
            let (variant_id, r) = result?;
            let v_entry = r.link_id.unwrap();

            self.drain_diagnostics(b);
            self.switch_blocks(current_block_id);
            let r_ty2 = b.types.u.resolve(&call_func_type).unwrap();
            self.scopes.variant_update(
                self.static_scope_id(),
                name,
                variant_id,
                r_ty2.clone(),
                v_entry,
            );
            (variant_id, v_entry)
        };
        self.functions.insert(name, v_entry);

        Ok((v_entry, call_func_type, ret_ty))
    }

    fn push_call_by_name(
        &mut self,
        name: StringKey,
        args: Vec<Argument>,
        span_id: SpanId,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        let current_block_id = self.current_block_id();
        // look up the lambda
        // If the lambda is in the static scope, we do a normal call
        // If it's in a non-static scope, then we bake a lambda and jump to it
        // If we wanted to so some inlining, we just have to switch to doing lambdas instead

        // 1. look up the def
        // 2. find an already baked function if it exists
        // 3. if no function exists, bake it
        // - for static, we just write the function to the static scope
        // - for lambdas and inline, it's easier, because we just write out the entire function
        // anyways

        // look up the prototype
        if let Some((scope_id, def, def_span_id)) = self.resolve_lambda(current_block_id, name) {
            // calculate the calling arguments
            let (_ret_ty, call_values, call_ty) =
                self.push_function_args(&def, args, span_id, b)?;

            let is_static = self.static_scope_id() == scope_id;
            if is_static {
                let r =
                    self.push_bake_static(name, def, def_span_id, call_ty.clone(), span_id, b)?;
                self.drain_diagnostics(b);
                let (fun_link_id, _bake_ty, ret_ty) = r;

                self.switch_blocks(current_block_id);
                //println!(
                //"call: call_ty: {}, bake_ty:{}, ret_ty: {}",
                //call_ty, bake_ty, ret_ty
                //);
                self.push_function_call(fun_link_id, call_values, ret_ty, span_id)
            } else {
                self.switch_blocks(current_block_id);

                println!(
                    "bake lambda: {:?}",
                    (scope_id, current_block_id, b.labels.r(name.into()))
                );

                let r = self.push_bake_lambda(Some(name), def, def_span_id, call_ty, span_id, b)?;
                self.drain_diagnostics(b);
                let (fun_block_id, _, _, next_block_id, next_link_id, _) = r;

                self.switch_blocks(next_block_id);

                // Lambda Block
                self.blocks
                    .block_succ(current_block_id, fun_block_id, Successor::BlockScope);

                // now that we have the arguments calculated, and the lambda baked, jump!
                self.switch_blocks(current_block_id);
                self.push_jump(fun_block_id.into(), call_values, span_id);
                self.switch_blocks(next_block_id);

                // block termination
                return Ok(FlattenResult::link(next_link_id));
            }
        } else {
            let name = b.labels.r(name.into());
            b.push_error(&format!("Call name not found: {}", name), span_id);
            Err(Error::new(BlockifyError::Invalid))
        }
    }

    pub fn push_code(
        &mut self,
        code: LCode,
        ty: AstType,
        name: Option<StringKey>,
        span_id: SpanId,
        mem: VarDefinitionSpace,
    ) -> LinkId {
        let entry = CodeEntry::new(self.current_block_id(), code, ty, name, span_id, mem);
        //println!("push code: {:?}", entry.dump());
        self.push_entry_with_link(entry)
    }

    pub fn push_function_call(
        &mut self,
        v_fun: LinkId,
        values: Vec<(Option<StringKey>, LinkId, AstType, SpanId)>,
        ret_ty: AstType,
        span_id: SpanId,
    ) -> Result<FlattenResult> {
        // Add links
        self.push_call_values(&values);

        // Make call
        let link_id = self.push_code(
            LCode::Call(v_fun.into()),
            ret_ty.clone(),
            None,
            span_id,
            VarDefinitionSpace::Default,
        );

        Ok(FlattenResult::link(link_id))
    }

    pub fn push_builtin_call(
        &mut self,
        def: &Lambda,
        id: BuiltinId,
        args: Vec<Argument>,
        span_id: SpanId,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        let (ret_ty, values, _call_ty) = self.push_function_args(&def, args, span_id, b)?;

        let current_block_id = self.current_block_id();

        // Add links
        self.push_call_values(&values);

        let link_id = self.push_code(
            LCode::Builtin(id),
            ret_ty.clone(),
            None,
            span_id,
            VarDefinitionSpace::Default,
        );
        self.switch_blocks(current_block_id);
        Ok(FlattenResult::link(link_id))
    }

    fn push_empty_label(&mut self, span_id: SpanId) -> LinkId {
        self.push_code(
            LCode::Label,
            AstType::Unit,
            None,
            span_id,
            VarDefinitionSpace::Default,
        )
    }

    fn replace_label(
        &mut self,
        link_id: LinkId,
        ty: AstType,
        name: Option<StringKey>,
        span_id: SpanId,
        mem: VarDefinitionSpace,
    ) {
        assert!(name.is_some());
        let entry = self.get_entry_mut(link_id);
        entry.ty = ty;
        entry.span_id = span_id;
        entry.mem = mem;
        entry.name = name;
    }

    fn push_start_block_args(
        &mut self,
        scope_id: ScopeId,
        block_ty: AstType,
        span_id: SpanId,
    ) -> Vec<(Option<StringKey>, LinkId, AstType, SpanId)> {
        if let AstType::Func(arg_ty, _ret_ty) = &block_ty {
            assert!(arg_ty.is_composite());

            let mut v_args = vec![];
            for (i, (name, ty)) in arg_ty.fields().iter().enumerate() {
                let link_id = self.push_code(
                    LCode::Arg(i as u8),
                    ty.clone(),
                    *name,
                    span_id,
                    VarDefinitionSpace::Arg,
                );
                v_args.push((*name, link_id, ty.clone(), span_id));
                if let Some(name) = name {
                    self.scopes.scope_define(scope_id, *name, link_id.into());
                }
            }
            v_args
        } else {
            unreachable!()
        }
    }

    fn push_start_block(
        &mut self,
        scope_id: ScopeId,
        block_ty: AstType,
        name: Option<StringKey>,
        span_id: SpanId,
        mem: VarDefinitionSpace,
    ) -> (LinkId, Vec<(Option<StringKey>, LinkId, AstType, SpanId)>) {
        let block_link_id = self.push_empty_label(span_id);
        let v_args = self.push_start_block_args(scope_id, block_ty.clone(), span_id);
        self.replace_label(block_link_id, block_ty, name, span_id, mem);
        self.block_links
            .insert(self.current_block_id(), block_link_id);
        (block_link_id, v_args)
    }

    pub fn save_ast_template(
        &mut self,
        block_id: BlockId,
        name: &StringKey,
        def: &Lambda,
        span_id: SpanId,
    ) -> Result<()> {
        let template_id = self.insert_ast_template(def.clone(), span_id);
        let block = self.blocks.get_block(block_id);
        let scope_id = block.scope_id;
        let scope = self.scopes.get_scope_mut(scope_id);
        scope.lambdas.insert(name.into(), template_id);
        Ok(())
    }

    fn push_bake_function(
        &mut self,
        def: Lambda,
        def_func_ty: AstType,
        name: StringKey,
        global_name: StringKey,
        scope_type: ScopeType,
        succ_type: Successor,
        b: &mut NB,
    ) -> Result<(VariantId, FlattenResult)> {
        let current_block_id = self.current_block_id();

        let func_ret_ty = if let AstType::Func(_arg, ret) = def_func_ty.clone() {
            if let ReturnType::Single(ret) = *ret {
                ret.clone()
            } else {
                unreachable!()
            }
        } else {
            unreachable!()
        };

        let body = def.body.unwrap();
        let span_id = body.span_id;
        // create function scope
        let (fun_block_id, fun_scope_id) =
            self.new_scope_and_block(scope_type, self.static_scope_id());
        // create function block and return block
        let ret_block_id = self.blocks.new_block(fun_scope_id);

        // return in scope
        let fun_scope = self.scopes.get_scope_mut(fun_scope_id);
        fun_scope.return_block = Some(ret_block_id);

        // block graph
        self.blocks
            .block_succ(self.static_block_id(), fun_block_id, succ_type);
        self.blocks
            .block_succ(fun_block_id, ret_block_id, Successor::BlockScope);
        self.switch_blocks(fun_block_id);
        let (entry_link_id, _) = self.push_start_block(
            fun_scope_id,
            def_func_ty.clone(),
            Some(global_name),
            span_id,
            VarDefinitionSpace::Static,
        );

        // add entry to static scope, for recursion
        let r_ty1 = b.types.u.resolve(&def_func_ty).unwrap();
        // we need to know the link
        //let variant_id = if let Some(global_name) = global_name {
        let variant_id =
            self.scopes
                .variant_add(self.static_scope_id(), name, r_ty1, entry_link_id);
        //} else {
        //None
        //};

        // add the name to static scope
        // do this early for recursive functions
        self.scopes
            .scope_define(self.static_scope_id(), global_name, entry_link_id);

        self.switch_blocks(fun_block_id);
        let _ = self.push_node(*body, b)?;
        self.maybe_terminate_block(ret_block_id, span_id);

        // write out return block
        let fun_block = self.blocks.get_block(fun_block_id);

        if fun_block.num_ret_args.len() > 1 {
            b.push_error(
                &format!("Return type mismatch: {:?}", &fun_block.num_ret_args),
                span_id,
            );
        }

        let num_ret_args = fun_block.num_ret_args.iter().next().unwrap_or(&0).clone();

        // we need to know at least the arity of the return value
        // is it something or nothing
        let arity = if num_ret_args == 0 {
            if b.types.u.unify(&AstType::Unit, &func_ret_ty).is_err() {
                b.push_error(
                    &format!(
                        "1-Type Mismatch: LHS: {}, RHS: {}",
                        &func_ret_ty,
                        &AstType::Unit
                    ),
                    span_id,
                );
            }
            0
        } else {
            num_ret_args
        };
        assert!(num_ret_args <= 1);

        // all the possible return types, unify them
        for ty in fun_block.ret_types.iter() {
            if b.types.u.unify(ty, &func_ret_ty).is_err() {
                b.push_error(
                    &format!("7-Type Mismatch: LHS: {}, RHS: {}", ty, &func_ret_ty),
                    span_id,
                );
            }
        }
        // resolve the return types
        let ret_types = fun_block
            .ret_types
            .iter()
            .map(|t| b.types.u.resolve(&t).unwrap_or(t.clone()))
            .collect::<HashSet<_>>();

        let single_ty = ret_types.iter().next().unwrap_or(&AstType::Unit).clone();

        let ret_arg_type = if arity == 0 || AstType::Unit == single_ty {
            AstType::Struct(vec![])
        } else {
            //println!("ret_types: {:?}", &ret_types);
            assert!(ret_types.len() == 1);
            AstType::Struct(vec![(None, single_ty.clone())])
        };

        let resolved_ret_ty = if self.mode == FlattenMode::Template || true {
            ret_arg_type.clone()
        } else if let Some(ty) = b.types.u.resolve(&ret_arg_type) {
            ty
        } else {
            let s = b.labels.r(name.into());
            println!("unable to resolve: {}", &s);
            b.types.dump();
            b.push_error(
                &format!(
                    "[{}] Return Type Must Resolve: {}, arity: {}",
                    &s, &func_ret_ty, arity
                ),
                span_id,
            );
            ret_arg_type.clone()
        };

        if b.types.u.unify(&func_ret_ty, &single_ty).is_err() {
            b.push_error(
                &format!(
                    "8-Type Mismatch: LHS: {}, RHS: {}",
                    &resolved_ret_ty, &func_ret_ty
                ),
                span_id,
            );
        }

        self.switch_blocks(ret_block_id);
        self.push_return_block_start(fun_scope_id, resolved_ret_ty.clone(), span_id, b);

        // restore position back to where we started
        self.switch_blocks(current_block_id);
        Ok((variant_id, FlattenResult::link(entry_link_id)))
    }

    fn push_bake_lambda(
        &mut self,
        name: Option<StringKey>,
        def: Lambda,
        def_span_id: SpanId,
        call_ty: AstType,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> Result<(BlockId, LinkId, AstType, BlockId, LinkId, AstType)> {
        // BAKE LAMBDA
        // TODO: There's a better way to do this.  Use continuations
        // eventually.
        // create a new block for the lambda
        // we call the lambda by jumping to it
        // the new block points to a next block
        // which we create here, and we return next block to the sequence
        // This involves creating a new lambda block for each call site.  This
        // is not efficient, if we call more than once.  In this other case, we
        // want to pass the continuation into the block, so next is not
        // required.
        //
        // Bake the lambda, this involes writing out the blocks, and passing the next block
        // as a continuation.  This currently requires one lambda for each call.
        // Eventually switch to CPS

        let def_func_type = b.types.r(def.fun_type).clone();

        // refresh variables
        let (def_arg_ty, ret_ty) = if let AstType::Func(arg, ret) = def_func_type {
            if let ReturnType::Single(ret_ty) = *ret {
                (b.types.refresh(*arg.clone()), b.types.refresh(ret_ty))
            } else {
                unreachable!()
            }
        } else {
            unreachable!()
        };
        let def_func_type = AstType::Func(
            def_arg_ty.clone().into(),
            ReturnType::Single(ret_ty.clone()).into(),
        );

        // construct call function type
        let call_func_type = AstType::func(
            call_ty.fields().iter().map(|(_, ty)| ty.clone()).collect(),
            ret_ty.clone(),
        );

        // match call type with function type
        println!("push_bake_lambda: {}<=>{}", &call_func_type, &def_func_type);
        if b.types.u.unify(&call_func_type, &def_func_type).is_err() {
            b.push_error_labels(vec![
                b.primary_label(
                    &format!("Type Mismatch: caller: {}", &call_func_type),
                    def_span_id,
                ),
                b.secondary_label(&format!("source type: {}", &def_func_type), def_span_id),
            ]);
        }

        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        let scope_id = block.scope_id;

        // New Lambda Scope
        let (fun_block_id, fun_scope_id) = self.new_scope_and_block(ScopeType::Function, scope_id);

        // NEXT BLOCK(ret_ty)
        // We create a new block for the lambda to return to
        // this is the continuation
        let next_block_id = self.blocks.new_block(scope_id);
        self.blocks
            .block_succ(current_block_id, next_block_id, Successor::BlockScope);

        // Lambda Body
        let body = *def.body.unwrap();

        let fun_scope = self.scopes.get_scope_mut(fun_scope_id);
        fun_scope.return_block = Some(next_block_id);

        // setup arguments for continuation block with appropriate parameters
        // matching the return type of the lambda block
        let next_arg_ty = AstType::Struct(match &ret_ty {
            AstType::Unit => vec![],
            _ => vec![(None, ret_ty.clone())],
        });
        // start next block
        self.switch_blocks(next_block_id);

        let s_name = name.map(|key| b.labels.r(key.into()));

        let next_fun_ty = AstType::Func(
            next_arg_ty.clone().into(),
            ReturnType::Single(AstType::Unit).into(),
        );

        let prefix = s_name
            .map(|s| format!("{}.cont", s))
            .unwrap_or("cont".to_string());
        let (_v_block, next_link_ids) = self.push_start_block(
            scope_id,
            next_fun_ty.clone(),
            Some(b.labels.fresh_key(&prefix)),
            call_span_id,
            VarDefinitionSpace::Reg,
        );

        let next_link_id = match &ret_ty {
            AstType::Unit => None,
            _ => Some(next_link_ids.first().unwrap().1),
        };

        // Start lambda block
        let s_name = if let Some(name) = name {
            b.labels.r(name.into())
        } else {
            "lambda".to_string()
        };

        let lambda_name = b.labels.fresh_key(&s_name);
        self.switch_blocks(fun_block_id);
        let (fun_link_id, _) = self.push_start_block(
            fun_scope_id,
            def_func_type.clone(),
            Some(lambda_name),
            def_span_id,
            VarDefinitionSpace::Reg,
        );
        // flatten lambda block
        self.switch_blocks(fun_block_id);
        let _ = self.push_node(body, b)?;
        self.maybe_terminate_block(next_block_id, call_span_id);
        self.switch_blocks(next_block_id);

        // match return type with the jump target
        println!("push_bake_lambda_next: {}<=>{}", &next_arg_ty, &def_arg_ty);
        if b.types.u.unify(&next_arg_ty, &def_arg_ty).is_err() {
            let ty1 = b.types.u.resolve(&next_arg_ty).unwrap();
            let ty2 = b.types.u.resolve(&def_arg_ty).unwrap();
            b.push_error_labels(vec![
                b.primary_label(
                    &format!("Type Mismatch Lambda Next: caller: {}", &ty1),
                    call_span_id,
                ),
                b.secondary_label(&format!("source type: {}", &ty2), def_span_id),
            ]);
        }

        Ok((
            fun_block_id,
            fun_link_id,
            def_func_type.clone(),
            next_block_id,
            next_link_id.unwrap(),
            next_fun_ty,
        ))
    }

    pub fn push_bake(&mut self, name: StringKey, func_type: AstType, b: &mut NB) -> Result<LinkId> {
        match self.mode {
            FlattenMode::Function => self.push_bake_func(name, func_type, b),
            //FlattenMode::Template => self.push_bake_template(name, func_type, b),
            _ => unimplemented!(),
        }
    }

    pub fn push_bake_func(
        &mut self,
        name: StringKey,
        func_type: AstType,
        b: &mut NB,
    ) -> Result<LinkId> {
        let current_block_id = self.current_block_id();
        if let Some((__scope_id, def, _def_span_id)) = self.resolve_lambda(current_block_id, name) {
            //println!(
            //"bake: {:?}",
            //(scope_id, current_block_id, b.labels.r(name.into()))
            //);
            /*
            if let Some(ty) = maybe_ty {
                let fun_ty = b.types.r(def.fun_type).clone();
                println!("match: {}<=>{}", &ty, &fun_ty);
                if b.types.u.unify(&ty, &fun_ty).is_err() {
                    let span_id = b.spans.get_span_unknown();

                    b.push_error(
                        &format!("Bake Func Mismatch: caller: {}, def: {}", &ty, fun_ty),
                        span_id,
                    );
                }
            }
            */

            // update declaration
            /*
            let decl_link_id = if let Some(decl_link_id) =
                self.resolve_declaration(current_block_id, name)
            {
                decl_link_id
            } else {
                unreachable!()
            };
            */

            let result = self.push_bake_function(
                def,
                func_type,
                name,
                name,
                ScopeType::Function,
                Successor::FunctionDeclaration,
                b,
            );
            if result.is_err() {
                self.drain_diagnostics(b);
            }
            let (_variant_id, r) = result?;

            //let entry_block_id = self.get_entry(r.link_id.unwrap()).block_id;

            // update declaration
            //
            /*
            let entry = self.get_entry_mut(decl_link_id);
            if let LCode::DeclareFunction(_) = entry.code {
            } else {
                assert!(false);
            }
            entry.code = LCode::DeclareFunction(Some(entry_block_id));
            */

            self.drain_diagnostics(b);
            self.switch_blocks(current_block_id);
            Ok(r.link_id.unwrap())
        } else {
            let s = b.labels.r(name.into());
            let u = b.spans.get_span_unknown();
            b.push_error(&format!("push_bake: not found: {}", s), u);
            Err(Error::new(BlockifyError::NotFound(s)))
        }
    }

    pub fn push_bake_template2(
        &mut self,
        name: StringKey,
        def: &Lambda,
        span_id: SpanId,
        b: &mut NB,
    ) -> Result<LinkId> {
        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        let scope_id = block.scope_id;

        let fun_ty = def_to_type(&def, b);

        let decl_link_id = self.push_code(
            LCode::DeclareTemplate(None),
            fun_ty.clone(),
            Some(name),
            span_id,
            VarDefinitionSpace::Default,
        );

        self.scopes
            .scope_define_template(scope_id, name, decl_link_id);

        let result = self.push_bake_function(
            def.clone(),
            fun_ty,
            name,
            name,
            ScopeType::Template,
            Successor::TemplateDeclaration,
            b,
        );

        if result.is_err() {
            self.drain_diagnostics(b);
        }
        let (_, r) = result?;

        let entry_block_id = self.get_entry(r.link_id.unwrap()).block_id;
        let entry = self.get_entry_mut(decl_link_id);
        if let LCode::DeclareTemplate(_) = entry.code {
        } else {
            unreachable!()
        }
        entry.code = LCode::DeclareTemplate(Some(entry_block_id));
        self.drain_diagnostics(b);
        self.switch_blocks(current_block_id);
        Ok(r.link_id.unwrap())
    }

    pub fn push_bake_template3(
        &mut self,
        name: StringKey,
        func_ty: AstType,
        b: &mut NB,
    ) -> Result<LinkId> {
        let current_block_id = self.current_block_id();
        if let Some((_scope_id, def, _def_span_id)) = self.resolve_lambda(current_block_id, name) {
            //println!(
            //"bake: {:?}",
            //(scope_id, current_block_id, b.labels.r(name.into()))
            //);
            /*
            if let Some(ty) = maybe_ty {
                let fun_ty = b.types.r(def.fun_type).clone();
                if b.types.u.unify(&ty, &fun_ty).is_err() {
                    let span_id = b.spans.get_span_unknown();

                    b.push_error(
                        &format!("Func Mismatch: caller: {}, def: {}", &ty, fun_ty),
                        span_id,
                    );
                }
            }
            */

            // update declaration
            let decl_link_id =
                if let Some(decl_link_id) = self.resolve_template(current_block_id, name.into()) {
                    decl_link_id
                } else {
                    unreachable!()
                };

            let result = self.push_bake_function(
                def.clone(),
                func_ty,
                name,
                name,
                ScopeType::Template,
                Successor::TemplateDeclaration,
                b,
            );

            //let result = self.push_bake_function(def, name, ScopeType::Function, Successor::FunctionDeclaration, b);

            if result.is_err() {
                self.drain_diagnostics(b);
            }
            let (_, r) = result?;

            let entry_block_id = self.get_entry(r.link_id.unwrap()).block_id;
            let entry = self.get_entry_mut(decl_link_id);
            if let LCode::DeclareTemplate(_) = entry.code {
            } else {
                assert!(false);
            }
            entry.code = LCode::DeclareTemplate(Some(entry_block_id));

            self.drain_diagnostics(b);
            self.switch_blocks(current_block_id);
            Ok(r.link_id.unwrap())
        } else {
            let s = b.labels.r(name.into());
            let u = b.spans.get_span_unknown();
            b.push_error(&format!("push_bake_template: not found: {}", s), u);
            Err(Error::new(BlockifyError::NotFound(s)))
        }
    }

    pub fn push_node(&mut self, node: AstNode, b: &mut NB) -> Result<FlattenResult> {
        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block_mut(current_block_id);
        let span_id = node.span_id;
        //println!("push: {}, {}", current_block_id, block.scope_id);
        //b.dump_ast(&node);
        let ast = node.node;

        match ast {
            Ast::Module(_, _) => {
                unimplemented!("No nested modules yet")
            }

            Ast::Sequence(exprs) => {
                self.switch_blocks(current_block_id);
                self.push_sequence(exprs, span_id, b)
            }

            Ast::Global(name, ref expr) => {
                match &expr.node {
                    Ast::Lambda(def) => {
                        let fun_ty = def_to_type(&def, b);

                        match self.mode {
                            FlattenMode::Function => {}
                            FlattenMode::Template => {
                                if let Some(_) = &def.body {
                                    let template_link_id = self.push_code(
                                        LCode::DeclareTemplate(None),
                                        fun_ty.clone(),
                                        Some(name),
                                        span_id,
                                        VarDefinitionSpace::Static,
                                    );
                                    self.switch_blocks(current_block_id);
                                    self.scopes.scope_define_template(
                                        self.static_scope_id(),
                                        name,
                                        template_link_id,
                                    );
                                }
                            }
                        }

                        // save template for later use
                        if def.body.is_some() {
                            self.save_ast_template(current_block_id, &name, &def, span_id)?;
                        }

                        if let Some(_body) = &def.body {
                            Ok(FlattenResult::statement())
                        } else {
                            Ok(FlattenResult::statement())
                        }
                    }

                    Ast::Literal(lit) => {
                        let scope_id = block.scope_id;
                        let scope = self.scopes.get_scope(scope_id);

                        let static_block_id = self.static_block_id();

                        // Generate the global name, unique if it's local
                        let global_name = if let ScopeType::Static = scope.scope_type {
                            b.labels.r(name.into()).to_string()
                        } else {
                            // static var with local name
                            let unique_name = b.unique_static_name();
                            let base = b.labels.r(name.into());
                            format!("{}{}", base, unique_name).clone()
                        };
                        let global_name_key = b.labels.s(&global_name);

                        let ast_ty: AstType = lit.clone().into();
                        self.switch_blocks(static_block_id);
                        let link_id = self.push_code(
                            LCode::Val(lit.clone()),
                            ast_ty.clone(),
                            Some(global_name_key),
                            node.span_id,
                            VarDefinitionSpace::Static,
                        );

                        self.scopes.scope_define(scope_id, name, link_id.into());

                        self.switch_blocks(current_block_id);
                        Ok(FlattenResult::link(link_id))
                    }
                    _ => {
                        unreachable!("{:?}", ast)
                    }
                }
            }

            Ast::Builtin(id, mut args) => {
                let bi = b.builtins.get_enum(id);
                println!("bi: {:?}", bi);
                match bi {
                    Builtin::Import => {
                        let arg = args.pop().unwrap();
                        if let Some(s) = arg.try_string() {
                            self.link.add_library(&s);
                        } else {
                            b.push_error("Expected string", span_id);
                        }
                        self.switch_blocks(current_block_id);
                        Ok(FlattenResult::statement())
                    }
                    _ => {
                        let args_size = args.len();
                        assert_eq!(args_size, bi.arity());

                        //let ret_type_id = b.types.s(&ty);
                        let def = bi.get_lambda(b);
                        self.switch_blocks(current_block_id);
                        self.push_builtin_call(&def, id, args, span_id, b)
                    }
                }
            }

            Ast::Return(maybe_expr) => {
                let block = self.blocks.get_block(current_block_id);
                //println!("return: {:?}", (block_id, block.scope_id));
                let fun_scope_id = self
                    .scopes
                    .find_nearest_scope(block.scope_id, &[ScopeType::Template, ScopeType::Function])
                    .expect(&format!(
                        "Not in function context, scope_id:{}",
                        block.scope_id
                    ));

                let fun_block_id = self.scopes.get_entry_block(fun_scope_id);

                let mut jump_args = vec![];
                let span_id = if let Some(expr) = maybe_expr {
                    let expr_span_id = expr.span_id;
                    self.switch_blocks(current_block_id);
                    let r = self.push_node(*expr, b)?;
                    let link_id = r.link_id.unwrap();
                    let entry = self.get_entry(link_id);
                    jump_args.push((None, link_id, entry.ty.clone(), span_id));
                    expr_span_id
                } else {
                    node.span_id
                };

                let fun_block = self.blocks.get_block_mut(fun_block_id);
                fun_block.num_ret_args.insert(jump_args.len());
                for (_, _, ty, _) in jump_args.iter() {
                    fun_block.ret_types.insert(ty.clone());
                }

                let scope = self.scopes.get_scope(fun_scope_id);
                self.push_jump(scope.return_block.unwrap().into(), jump_args, span_id);
                Ok(FlattenResult::statement())
            }

            Ast::Literal(lit) => {
                //self.ensure_open();
                // literal is expression, non-terminal
                let ty: AstType = lit.clone().into();
                //let mem = if block.scope_id == fenv.static_scope_id() {
                //VarDefinitionSpace::Static
                //} else {
                //VarDefinitionSpace::Default
                //};
                let mem = VarDefinitionSpace::Default;

                let link_id = self.push_code(LCode::Val(lit), ty.clone(), None, node.span_id, mem);
                Ok(FlattenResult::link(link_id))
            }

            Ast::BinaryOp(op, x, y) => {
                // expression, non-terminal
                let x_span_id = x.span_id;
                self.switch_blocks(current_block_id);
                let rx = self.push_node(*x, b)?;
                let ry = self.push_node(*y, b)?;
                let vx = rx.link_id.unwrap();
                let vy = ry.link_id.unwrap();
                let rx_ty = self.get_type(vx).clone();
                let ry_ty = self.get_type(vy).clone();

                if b.types.u.unify(&rx_ty, &ry_ty).is_err() {
                    b.push_error(
                        &format!("3-Type Mismatch: LHS: {}, RHS: {}", rx_ty, ry_ty),
                        x_span_id,
                    );
                }

                let _ = self.push_call_values(&[
                    (None, vx, rx_ty.clone(), node.span_id),
                    (None, vy, ry_ty.clone(), node.span_id),
                ]);

                let ret_ty = op.node.get_type(&rx_ty, &ry_ty);
                let link_id = self.push_code(
                    LCode::Op2(op.node),
                    ret_ty.clone(),
                    None,
                    op.span_id,
                    VarDefinitionSpace::Default,
                );

                //self.switch_blocks(current_block_id);
                Ok(FlattenResult::link(link_id))
            }

            Ast::Identifier(key) => {
                // identifier is expression, non-terminal
                if let Some(def_link_id) = self.resolve_name(current_block_id, key) {
                    let link_id = def_link_id;
                    Ok(FlattenResult::link(link_id))
                } else {
                    let s = b.labels.r(key.into());
                    b.push_error(&format!("ident: not found: {}", s), span_id);
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
                    self.switch_blocks(current_block_id);

                    // push template
                    // we might not need this, we inline everything we need
                    // at this point all scope rules should have been applied.
                    // we have to monomorphize here in order to have correct scope
                    // there are two ways to scope the lambda function
                    // we scope in place, so that the function is able to access
                    // variables in this scope.  We can accomplish this by inserting the entry
                    // here.  The lambda is subordinate to the variables in scope, so it should
                    // just work.
                    // The other method is to use the scope at the point of the call.  This is
                    // less intuitive, but also possible.
                    // The third method is to be able to provide arbitrary scope.
                    // We can only do the first method if we have CPS, which isn't yet implemented.
                    // The 3rd method is easiest, as we insert the code at the caller.
                    // It's simpler, and get's us most of the way there.

                    if self.mode == FlattenMode::Template {
                        self.push_bake_template2(name, &def, span_id, b)?;
                    }

                    self.save_ast_template(current_block_id, &name, &def, expr.span_id)?;
                    self.switch_blocks(current_block_id);
                    return Ok(FlattenResult::statement());
                }

                self.switch_blocks(current_block_id);
                let r = self.push_node(*expr, b)?;
                let v_expr = r.link_id.unwrap();
                let expr_ty = self.get_entry(v_expr).ty.clone();

                let offset_decl =
                    if let Some(v_decl) = self.resolve_name(self.current_block_id(), name) {
                        // already declared
                        let ty = self.get_type(v_decl).clone();
                        if b.types.u.unify(&ty, &expr_ty).is_err() {
                            b.push_error(
                                &format!("Assisgn Type Mismatch: {:?}, {:?}", ty, expr_ty),
                                node.span_id,
                            );
                        }
                        v_decl
                    } else {
                        // need to declare it
                        let block = self.blocks.get_block(self.current_block_id());
                        let scope_id = block.scope_id;
                        let expr_ty = self.get_entry(v_expr).ty.clone();
                        let link_id = self.push_code(
                            LCode::Declare,
                            expr_ty.clone(),
                            Some(name),
                            node.span_id,
                            VarDefinitionSpace::Stack,
                        );
                        self.scopes.scope_define(scope_id, name, link_id);
                        link_id.into()
                    };

                let load_link_id = if self.is_load_required(v_expr) {
                    let link_id = self.push_code(
                        LCode::Load(v_expr),
                        expr_ty,
                        None,
                        node.span_id,
                        VarDefinitionSpace::Default,
                    );
                    link_id
                } else {
                    v_expr
                };

                let link_id = self.push_code(
                    LCode::Store(offset_decl, load_link_id),
                    AstType::Unit,
                    None,
                    node.span_id,
                    VarDefinitionSpace::Default,
                );
                //self.switch_blocks(current_block_id);
                Ok(FlattenResult::link(link_id))
            }

            Ast::Import(module_key, args) => {
                let module_name = b.labels.r(module_key.into());
                let scope_id = block.scope_id;

                if &module_name == "prelude" {
                    let print = b.labels.s("print");
                    let ty = AstType::Struct(vec![
                        (
                            Some(print),
                            AstType::func(vec![AstType::Int], AstType::Unit),
                        ),
                        (
                            Some(print),
                            AstType::func(vec![AstType::Float], AstType::Unit),
                        ),
                        (
                            Some(print),
                            AstType::func(vec![AstType::Bool], AstType::Unit),
                        ),
                    ]);
                    let link_id = self.push_code(
                        LCode::Extern,
                        ty,
                        Some(module_key),
                        node.span_id,
                        VarDefinitionSpace::Default,
                    );

                    for (attr_key, local_key) in args.iter() {
                        let attr_name = b.labels.r(attr_key.into());
                        if &attr_name == "q" {
                            self.scopes.scope_define(scope_id, *local_key, link_id);
                        } else {
                            b.push_error_labels(vec![b.primary_label(
                                &format!("Attribute of prelude not found: {}", &attr_name),
                                span_id,
                            )]);
                        }
                    }
                } else {
                    unimplemented!("module {}", module_name)
                }
                Ok(FlattenResult::statement())
            }

            Ast::Call(expr, args) => {
                match &expr.node {
                    // call is an expression, it's non-terminal
                    // lambdas should also be non-terminal
                    Ast::Identifier(ident) => self.push_call_by_name(*ident, args, node.span_id, b),
                    Ast::Attribute(ident, attr) => {
                        let node = attr;
                        let ast = resolve_attribute(*ident, &node, span_id, args, b)?;
                        self.push_node(ast, b)
                    }
                    _ => unimplemented!("{:?}", expr.node),
                }
            }

            Ast::UnaryOp(op, x) => {
                // op1 is expression, non-terminal
                self.switch_blocks(current_block_id);
                let r = self.push_node(*x, b)?;
                let link_id = r.link_id.unwrap();
                let ty = self.get_type(link_id).clone();

                self.push_call_values(&[(None, link_id, ty.clone(), span_id)]);

                let link_id = self.push_code(
                    LCode::Op1(op),
                    ty.clone(),
                    None,
                    node.span_id,
                    VarDefinitionSpace::Reg,
                );
                //self.switch_blocks(current_block_id);
                Ok(FlattenResult::link(link_id))
            }

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
                let current_block_id = self.current_block_id();
                let block = self.blocks.get_block(current_block_id);
                let parent_scope_id = block.scope_id;

                let v_next = self.blocks.new_block(parent_scope_id);
                self.switch_blocks(v_next);
                self.push_start_block(
                    parent_scope_id,
                    AstType::func(vec![], AstType::Unit), // void=>void
                    Some(b.labels.fresh_key("cond_new")),
                    span_id,
                    VarDefinitionSpace::Default,
                );
                self.switch_blocks(current_block_id);

                // THEN
                let (then_block_id, then_scope_id) =
                    self.new_scope_and_block(ScopeType::Block, parent_scope_id);
                let then_span_id = then_expr.span_id;
                self.blocks
                    .block_succ(current_block_id, then_block_id, Successor::BlockScope);
                self.blocks
                    .block_succ(current_block_id, then_block_id, Successor::Jump);

                let branch_block_type = AstType::Func(
                    AstType::Struct(vec![]).into(),
                    ReturnType::Single(AstType::Unit).into(),
                );

                let name = b.labels.fresh_key("then");
                self.switch_blocks(then_block_id);
                self.push_start_block(
                    then_scope_id,
                    branch_block_type.clone(),
                    Some(name),
                    then_span_id,
                    VarDefinitionSpace::Reg,
                );
                self.switch_blocks(then_block_id);
                let _ = self.push_node(NB::ensure_seq(*then_expr), b)?;
                self.maybe_terminate_block(v_next, span_id);

                // ELSE
                let else_block_id = if let Some(else_expr) = maybe_else_expr {
                    let (else_block_id, else_scope_id) =
                        self.new_scope_and_block(ScopeType::Block, parent_scope_id);
                    let else_span_id = else_expr.span_id;
                    self.blocks
                        .block_succ(current_block_id, else_block_id, Successor::BlockScope);
                    self.blocks
                        .block_succ(current_block_id, else_block_id, Successor::Jump);

                    let name = b.labels.fresh_key("else");

                    self.switch_blocks(else_block_id);
                    self.push_start_block(
                        else_scope_id,
                        branch_block_type,
                        Some(name),
                        else_span_id,
                        VarDefinitionSpace::Reg,
                    );

                    self.switch_blocks(else_block_id);
                    let _ = self.push_node(NB::ensure_seq(*else_expr), b)?;
                    self.maybe_terminate_block(v_next, span_id);
                    else_block_id
                } else {
                    self.blocks
                        .block_succ(current_block_id, v_next, Successor::BlockScope);
                    self.blocks
                        .block_succ(current_block_id, v_next, Successor::Jump);
                    v_next
                };

                // condition
                let span_id = condition.span_id;
                self.switch_blocks(current_block_id);
                let r = self.push_node(*condition, b)?;
                let v = self.push_code(
                    LCode::Branch(
                        r.link_id.unwrap().into(),
                        then_block_id.into(),
                        else_block_id.into(),
                    ),
                    AstType::Unit,
                    None,
                    span_id,
                    VarDefinitionSpace::Reg,
                );
                self.switch_blocks(v_next);
                Ok(FlattenResult::link(v))
            }

            Ast::ControlFlowMarker(ControlFlowMarker::BlockStart(name, args)) => {
                let name = name.unwrap();

                // push a new block.  But check to make sure the previous block was closed
                let scope_id = block.scope_id;

                //let (new_block_id, next_block_id) = self.create_new_block_in_scope(name, scope_id);
                let maybe_new_block_id = self.scopes.resolve_block_id(scope_id, name.into());
                let new_block_id = if let Some(new_block_id) = maybe_new_block_id {
                    println!("block start existing: {}", new_block_id);
                    new_block_id
                } else {
                    assert_eq!(0, args.len());
                    let new_block_id = self.blocks.new_block(scope_id);
                    println!("block start new: {}", new_block_id);
                    self.blocks.block_succ(
                        self.current_block_id(),
                        new_block_id,
                        Successor::BlockScope,
                    );
                    let scope = self.scopes.get_scope_mut(scope_id);
                    scope.block_labels.insert(name.into(), new_block_id);
                    //println!("creating block: {} in {}", b.labels.r(key.into()), scope_id);
                    new_block_id
                };

                // start a new block.  If the last block isn't terminated, then we create a new
                // block and jump to it.
                // TODO: We can also check if the previous block was empty and compatible, and reuse it.
                let block = self.blocks.get_block(current_block_id);
                if let Some(last_link_id) = block.last() {
                    let entry = self.get_entry(last_link_id);
                    if !entry.code.is_term() {
                        assert_eq!(args.len(), 0);
                        let link_id = self.push_jump(new_block_id, vec![], span_id);
                        println!("block start 1: {}, link: {}", new_block_id, link_id);
                    }
                }

                let block = self.blocks.get_block(current_block_id);
                // this is a new block, check to make sure the last block terminated
                // if not, we close it out with a jump to this block
                if let Some(last) = block.last() {
                    let entry = self.get_entry(last);
                    if !entry.code.is_term() {
                        let _ = self.push_jump(new_block_id.into(), vec![], span_id);
                    }
                }

                let new_block = self.blocks.get_block(new_block_id);
                let new_scope_id = new_block.scope_id;

                let scope = self.scopes.get_scope(new_scope_id);

                // ensure this block is not an entry block, this should never happen.
                assert!(scope.entry_block != Some(new_block_id));

                self.blocks
                    .block_succ(current_block_id, new_block_id, Successor::BlockScope);

                let arg_ty = AstType::Struct(
                    args.iter()
                        .map(|p| {
                            let ty = b.types.r(p.ty);
                            (Some(p.name), ty.clone())
                        })
                        .collect::<Vec<_>>(),
                );

                println!("block start: {}", new_block_id);
                self.switch_blocks(new_block_id);
                let (link_id, _) = self.push_start_block(
                    new_scope_id,
                    AstType::Func(
                        arg_ty.clone().into(),
                        ReturnType::Single(AstType::Unit).into(),
                    ),
                    Some(name),
                    span_id,
                    VarDefinitionSpace::Default,
                );
                self.switch_blocks(new_block_id);
                Ok(FlattenResult::link(link_id))
            }

            /*
            Ast::Block(name, args, body) => {
                unimplemented!();
                let ast: Ast = ControlFlowMarker::BlockStart(Some(name), args).into();
                self.push_node(ast.node(span_id), b)?;
                self.push_node(NB::ensure_seq(*body), b)
                //let _ = self.push_node(NB::ensure_seq(*body), b);
                //self.switch_blocks(next_block_id);
                //Ok(FlattenResult::link(next_link_id))
            }
            */
            Ast::Ternary(c, x, y) => {
                // expression, non-terminal
                let block = self.blocks.get_block(current_block_id);
                let scope_id = block.scope_id;

                // Condition
                self.switch_blocks(current_block_id);
                let rc = self.push_node(*c, b)?;
                //assert_eq!(self.block_id, rc.block_id);
                let current_block_id = self.current_block_id();

                let branch_block_type = AstType::Func(
                    AstType::Struct(vec![]).into(),
                    ReturnType::Single(AstType::Unit).into(),
                );

                // THEN
                let (then_block_id, then_scope_id) =
                    self.new_scope_and_block(ScopeType::Region, scope_id);
                let then_span_id = x.span_id;
                let then_ast = AstNode::make_yield(*x);
                self.blocks
                    .block_succ(current_block_id, then_block_id, Successor::Operation);
                self.blocks
                    .block_succ(current_block_id, then_block_id, Successor::Jump);

                let name = b.labels.fresh_key("t_then");

                self.switch_blocks(then_block_id);
                self.push_start_block(
                    then_scope_id,
                    branch_block_type.clone(),
                    Some(name),
                    then_span_id,
                    VarDefinitionSpace::Reg,
                );

                self.switch_blocks(then_block_id);
                let r = self.push_node(then_ast, b)?;
                let then_link_id = r.link_id.unwrap();
                let then_ty = self.get_type(then_link_id).clone();
                //let then_ty = r.ty;

                // ELSE
                let else_span_id = y.span_id;
                let (else_block_id, else_scope_id) =
                    self.new_scope_and_block(ScopeType::Region, scope_id);
                let else_ast = AstNode::make_yield(*y);
                self.blocks
                    .block_succ(current_block_id, else_block_id, Successor::Operation);
                self.blocks
                    .block_succ(current_block_id, else_block_id, Successor::Jump);

                self.switch_blocks(else_block_id);
                self.push_start_block(
                    else_scope_id,
                    branch_block_type,
                    Some(name),
                    else_span_id,
                    VarDefinitionSpace::Reg,
                );

                self.switch_blocks(else_block_id);
                let r = self.push_node(else_ast, b)?;
                let else_link_id = r.link_id.unwrap();
                let else_ty = self.get_type(else_link_id).clone();

                if b.types.u.unify(&then_ty, &else_ty).is_err() {
                    b.push_error(
                        &format!(
                            "Ternary Type Mismatch: then: {}, else: {}",
                            &then_ty, &else_ty
                        ),
                        span_id,
                    );
                }

                // switch back to the original block
                self.switch_blocks(current_block_id);
                let v = self.push_code(
                    LCode::Ternary(
                        rc.link_id.unwrap().into(),
                        then_block_id.into(),
                        else_block_id.into(),
                    ),
                    then_ty.clone(),
                    None,
                    span_id,
                    VarDefinitionSpace::Reg,
                );
                //self.switch_blocks(rc.block_id);
                Ok(FlattenResult::link(v))
            }

            Ast::Yield(maybe_expr) => {
                // yield is terminal
                let mut ty = AstType::Unit;
                if let Some(expr) = maybe_expr {
                    self.switch_blocks(current_block_id);
                    let r = self.push_node(*expr, b)?;
                    if let Some(v) = r.link_id {
                        //v_block = self.block_id;
                        ty = self.get_type(v).clone();
                        // push single arg
                        self.push_call_values(&[(None, v.into(), ty.clone(), node.span_id)]);
                    }
                }

                let v = self.push_code(
                    LCode::Yield,
                    ty.clone(),
                    None,
                    node.span_id,
                    VarDefinitionSpace::Reg,
                );
                Ok(FlattenResult::link(v))
            }

            Ast::ControlFlowMarker(ControlFlowMarker::Goto(label)) => {
                // Goto is terminal
                let scope_id = block.scope_id;
                let target_block_id = if let Some(target_block_id) =
                    self.scopes.resolve_block_id(scope_id, label.into())
                {
                    println!("block goto resolved: {}", target_block_id);
                    target_block_id
                } else {
                    let scope = self.scopes.get_scope_mut(scope_id);

                    if let Some(unclaimed_block_id) = scope.unclaimed_labels.get(&label.into()) {
                        println!("block goto existing claim: {}", unclaimed_block_id);
                        // already declared as unclaimed
                        *unclaimed_block_id
                    } else {
                        let unclaimed_block_id = self.blocks.new_block(scope_id);
                        scope
                            .unclaimed_labels
                            .insert(label.into(), unclaimed_block_id);
                        println!("block goto new claim: {}", unclaimed_block_id);
                        unclaimed_block_id
                    }
                };

                self.switch_blocks(current_block_id);
                let link_id = self.push_jump(target_block_id.into(), vec![], node.span_id);
                println!("block goto: {}, link: {}", target_block_id, link_id);
                self.switch_blocks(current_block_id);
                Ok(FlattenResult::link(link_id))
            }

            Ast::ControlFlowMarker(ControlFlowMarker::BlockEnd) | Ast::CloseBlock => {
                let scope_id = block.scope_id;
                let scope = self.scopes.get_scope(scope_id);
                if let Some(loop_block) = scope.loop_block {
                    let link_id = self.maybe_terminate_block(loop_block.start_block, span_id);
                    println!("block loop end: {}, {}", loop_block.next_block, link_id);
                    self.switch_blocks(loop_block.next_block);
                    Ok(FlattenResult::link(link_id))
                } else {
                    unimplemented!()
                }
            }

            Ast::ControlFlowMarker(ControlFlowMarker::LoopStart(maybe_key)) => {
                let block = self.blocks.get_block(current_block_id);
                let parent_scope_id = block.scope_id;

                let v_next = self.blocks.new_block(parent_scope_id);
                self.switch_blocks(v_next);
                self.push_start_block(
                    parent_scope_id,
                    AstType::func(vec![], AstType::Unit), // void=>void
                    Some(b.labels.fresh_key("postloop")),
                    span_id,
                    VarDefinitionSpace::Default,
                );
                self.switch_blocks(current_block_id);

                let (loop_block_id, loop_scope_id) =
                    self.new_scope_and_block(ScopeType::Region, parent_scope_id);
                let scope = self.scopes.get_scope_mut(loop_scope_id);
                scope.entry_block = Some(loop_block_id);
                self.blocks
                    .block_succ(current_block_id, loop_block_id, Successor::BlockScope);

                self.scopes.update_loop_blocks(
                    loop_scope_id,
                    maybe_key,
                    v_next.into(),
                    loop_block_id.into(),
                );

                let key = if let Some(key) = maybe_key {
                    key
                } else {
                    b.labels.fresh_key("default_loop")
                };

                self.switch_blocks(loop_block_id);
                self.push_start_block(
                    loop_scope_id,
                    AstType::Func(
                        AstType::Struct(vec![]).into(),
                        ReturnType::Single(AstType::Unit).into(),
                    ),
                    Some(key),
                    span_id,
                    VarDefinitionSpace::Reg,
                );

                self.switch_blocks(current_block_id);
                let link_id = self.push_jump(loop_block_id.into(), vec![], node.span_id);

                // open loop block
                self.switch_blocks(loop_block_id);
                Ok(FlattenResult::link(link_id))
            }

            /*
            Ast::Loop(name, body) => {
                unimplemented!();
                let scope_id = block.scope_id;
                let ast: Ast = ControlFlowMarker::LoopStart(Some(name)).into();
                let _ = self.push_node(ast.node(span_id), b);
                let _ = self.push_node(*body, b)?;
                // terminate block by looping
                let scope = self.scopes.get_scope(scope_id);
                let loop_block = scope.loop_block.unwrap();
                self.maybe_terminate_block(loop_block.start_block, span_id);
                self.switch_blocks(current_block_id);
                self.maybe_terminate_block(loop_block.next_block, span_id);
                self.switch_blocks(loop_block.next_block);
                Ok(FlattenResult::statement())
            }
            */
            Ast::ControlFlowMarker(ControlFlowMarker::LoopContinue(maybe_key)) => {
                let block = self.blocks.get_block(current_block_id);
                let scope_id = block.scope_id;

                // loop up loop blocks by name
                if let Some(loop_scope) = self.scopes.get_loop_scope(scope_id, maybe_key) {
                    self.switch_blocks(current_block_id);
                    let link_id =
                        self.push_jump(loop_scope.start_block.into(), vec![], node.span_id);
                    self.switch_blocks(current_block_id);
                    Ok(FlattenResult::link(link_id))
                } else {
                    // mismatch name
                    b.push_error(&format!("Continue without loop"), node.span_id);
                    Err(Error::new(BlockifyError::Invalid))
                }
            }

            Ast::Continue(maybe_name, args) => {
                let block = self.blocks.get_block(current_block_id);
                let scope_id = block.scope_id;

                // args not implemented yet
                assert_eq!(args.len(), 0);
                // loop up loop blocks by name
                if let Some(loop_scope) = self.scopes.get_loop_scope(scope_id, maybe_name) {
                    self.switch_blocks(current_block_id);
                    let link_id =
                        self.push_jump(loop_scope.start_block.into(), vec![], node.span_id);
                    self.switch_blocks(current_block_id);
                    Ok(FlattenResult::link(link_id))
                } else {
                    // mismatch name
                    b.push_error(&format!("Continue without loop"), node.span_id);
                    Err(Error::new(BlockifyError::Invalid))
                }
            }

            Ast::ControlFlowMarker(ControlFlowMarker::LoopBreak(maybe_key)) => {
                let block = self.blocks.get_block(current_block_id);
                let scope_id = block.scope_id;
                // loop up loop blocks by name
                if let Some(loop_scope) = self.scopes.get_loop_scope(scope_id, maybe_key) {
                    self.switch_blocks(current_block_id);
                    let link_id =
                        self.push_jump(loop_scope.next_block.into(), vec![], node.span_id);
                    println!(
                        "loop break jump: {}, link: {}",
                        loop_scope.next_block, link_id
                    );

                    let v_next = self.blocks.new_block(scope_id);
                    self.switch_blocks(v_next);
                    let (link_id, _) = self.push_start_block(
                        scope_id,
                        AstType::func(vec![], AstType::Unit), // void=>void
                        Some(b.labels.fresh_key("postloopbreak")),
                        span_id,
                        VarDefinitionSpace::Default,
                    );
                    Ok(FlattenResult::link(link_id))
                } else {
                    // mismatch name
                    b.push_error(&format!("Break without loop"), node.span_id);
                    Err(Error::new(BlockifyError::Invalid))
                }
            }

            Ast::Break(maybe_name, args) => {
                let block = self.blocks.get_block(current_block_id);
                let scope_id = block.scope_id;

                // args not implemented yet
                assert_eq!(args.len(), 0);
                // loop up loop blocks by name
                if let Some(loop_scope) = self.scopes.get_loop_scope(scope_id, maybe_name) {
                    self.switch_blocks(current_block_id);
                    let link_id =
                        self.push_jump(loop_scope.next_block.into(), vec![], node.span_id);
                    self.switch_blocks(current_block_id);
                    Ok(FlattenResult::link(link_id))
                } else {
                    // mismatch name
                    b.push_error(&format!("Break without loop"), node.span_id);
                    Err(Error::new(BlockifyError::Invalid))
                }
            }

            Ast::Array(_type_id, dims) => {
                let mut link_ids = vec![];
                for d in dims {
                    let r = self.push_node(d, b)?;
                    link_ids.push(r.link_id.unwrap());
                }
                b.push_error(&format!("AST Error"), node.span_id);
                Err(Error::new(BlockifyError::Invalid))
            }

            Ast::Tuple(exprs) => {
                let mut link_ids = vec![];
                let mut types = vec![];
                let mut values = vec![];
                for e in exprs {
                    let span_id = e.span_id;
                    self.switch_blocks(current_block_id);
                    let r = self.push_node(e, b)?;
                    let link_id = r.link_id.unwrap();
                    let ty = self.get_type(link_id).clone();
                    link_ids.push(link_id);
                    types.push(ty.clone()); //r.ty.clone());
                    values.push((None, link_id, ty, span_id));
                }

                let ty = AstType::build_tuple(types);

                let update_link_ids = self.push_loads_if_needed(&values);

                let link_id = self.push_code(
                    LCode::Tuple(update_link_ids),
                    ty,
                    None,
                    span_id,
                    VarDefinitionSpace::Default,
                );

                Ok(FlattenResult::link(link_id))
            }

            Ast::Index(node, index) => {
                let r_node = self.push_node(*node, b)?;
                let r_index = self.push_node(*index, b)?;

                let indicies = vec![r_index.link_id.unwrap().into()];

                let entry = self.get_entry(r_index.link_id.unwrap());
                let index = if let LCode::Val(Literal::Int(index)) = entry.code {
                    index as usize
                } else {
                    unimplemented!()
                };
                let entry = self.get_entry_mut(r_index.link_id.unwrap());
                entry.code = LCode::Val(Literal::Index(index));

                let ty = self.get_type(r_node.link_id.unwrap());
                println!("index: {:?}", (ty, index));
                let (_, ty_field) = ty.fields().get(index as usize).unwrap().clone();

                let code = LCode::Use(r_node.link_id.unwrap().into(), indicies);
                let link_id = self.push_code(
                    code,
                    ty_field.clone(),
                    None,
                    span_id,
                    VarDefinitionSpace::Default,
                );

                Ok(FlattenResult::link(link_id))
            }

            Ast::Attribute(ident, attr) => {
                // <ident>.<attr>
                // currently all attributes can be resolved this way, and they
                // resolve to an ast node, which we can then lower.
                let node = attr;
                let ast = resolve_attribute(ident, &node, span_id, vec![], b)?;
                self.push_node(ast, b)
            }

            Ast::Error => {
                b.push_error(&format!("AST Error"), node.span_id);
                Err(Error::new(BlockifyError::Invalid))
            }
            _ => {
                b.push_error(&format!("AST Unimplemented"), node.span_id);
                unimplemented!("{:?}", ast);
                //Err(Error::new(BlockifyError::Unimplemented))
            }
        }
    }

    pub fn ensure_open(&self) {
        let block = self.blocks.get_block(self.current_block_id());
        let link_id = block.last().unwrap().clone();
        let entry = self.get_entry(link_id);
        assert!(!entry.code.is_term());
    }

    pub fn maybe_terminate_block(&mut self, v_next: BlockId, span_id: SpanId) -> LinkId {
        // is the block isn't terminated, terminate it with a jump to another block
        let block = self.blocks.get_block(self.current_block_id());
        let mut link_id = block.last().unwrap().clone();
        let entry = self.get_entry(link_id);
        if !entry.code.is_term() {
            link_id = self.push_jump(v_next, vec![], span_id);
            println!("maybe term jump: {}, link: {}", v_next, link_id);
            self.blocks
                .block_succ(self.current_block_id(), v_next, Successor::BlockScope);
        }
        link_id
    }
}

fn def_to_type(def: &Lambda, b: &mut NB) -> AstType {
    let arg_type = b.types.r(def.arg_type).clone();
    let return_type = b.types.r(def.return_type).clone();
    let fun_ty = AstType::Func(arg_type.into(), ReturnType::Single(return_type).into());
    fun_ty
}
