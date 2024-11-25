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
    BlockGraph, BlockId, BlockifyError, Builtin, DeferredGoto, LCode, LinkId, NodeBuilder as NB,
    ScopeGraph, ScopeId, ScopeType, StringLabel, Successor, TemplateId, ValueId, VariantId,
};

type ArgVec = Vec<(Option<StringKey>, LinkId, AstType, SpanId)>;

pub fn argvec_type(values: &ArgVec) -> AstType {
    AstType::Struct(
        values
            .iter()
            .map(|v| (v.0, v.2.clone()))
            .collect::<Vec<_>>(),
    )
}

#[derive(Debug, Clone)]
pub struct CodeEntry {
    pub(super) next: LinkId,
    prev: LinkId,
    pub(super) code: LCode,
    pub(super) name: Option<StringKey>,
    pub(super) link: Option<LinkId>,
    pub(super) value_id: Option<ValueId>,
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
            value_id: None,
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
    pub(super) link: LinkOptions,
    pub(super) entries: Vec<CodeEntry>,
    pub blocks: BlockGraph,
    ast_templates: Vec<(Lambda, SpanId)>,
    pub(super) messages: Vec<(String, SpanId)>,
    pub mode: FlattenMode,
    pub(crate) static_scope: Option<ScopeId>,
    pub(crate) static_block: Option<BlockId>,
    pub(crate) current_block: BlockId,
    pub scopes: ScopeGraph,
    pub(super) block_links: HashMap<BlockId, LinkId>,
    pub(crate) functions: HashMap<StringKey, LinkId>,
    pub(crate) statics: HashMap<StringKey, Literal>,
}

impl Flatten {
    pub fn new() -> Self {
        let blocks = BlockGraph::new();

        Self {
            entries: vec![],
            blocks,
            link: LinkOptions::new(),
            ast_templates: vec![],
            messages: vec![],
            mode: FlattenMode::Function,
            static_scope: None,
            static_block: None,
            current_block: BlockId::new(0),
            scopes: ScopeGraph::new(),
            block_links: HashMap::new(),
            functions: HashMap::new(),
            statics: HashMap::new(),
        }
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
            if let Some(_template_id) = scope.lambdas.get(&name) {
                return Some(scope_id);
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

    pub fn resolve_template(
        &self,
        start_scope_id: ScopeId,
        name: StringLabel,
    ) -> Option<TemplateId> {
        // search scopes to find a template
        for scope_id in self.scopes.walk_scopes(start_scope_id) {
            let scope = self.scopes.get_scope(scope_id);
            if let Some(template_id) = scope.lambdas.get(&name).cloned() {
                return Some(template_id);
            }
        }
        None
    }

    pub fn resolve_label(&self, start_scope_id: ScopeId, name: StringLabel) -> Option<BlockId> {
        // search scopes to find a template
        for scope_id in self.scopes.walk_scopes(start_scope_id) {
            let scope = self.scopes.get_scope(scope_id);
            if let Some(block_id) = scope.block_labels.get(&name) {
                return Some(*block_id);
            }
        }
        None
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

    pub fn inject_builtin_prototypes(&mut self, b: &mut NB) {
        // inject builtin prototypes
        let print_index = b.labels.s("print_index".into());
        let print_float = b.labels.s("print_float".into());
        let print_bool = b.labels.s("print_bool".into());
        let builtins = vec![
            (print_index, AstType::Int, AstType::Unit),
            (print_float, AstType::Float, AstType::Unit),
            (print_bool, AstType::Bool, AstType::Unit),
        ];
        let unknown = b.spans.get_span_unknown();
        for (key, var_ty, ret_ty) in builtins {
            let func_ty = AstType::func(vec![var_ty], ret_ty);
            self.push_code(
                LCode::DeclareFunction(None),
                func_ty,
                Some(key),
                unknown,
                VarDefinitionSpace::Static,
            );
        }
    }

    pub(super) fn finish(mut self, b: &mut NB) -> Result<(Flatten, Vec<LinkId>)> {
        self.inject_builtin_prototypes(b);

        // make sure all claims have been handled
        self.scopes.ensure_claims(b);

        // DEAD BLOCKS
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
        }

        // declare functions
        for block_id in self.blocks.graph_get_entries() {
            let block = self.blocks.get_block(block_id);
            let label_link_id = block.entry.unwrap();
            let entry = self.get_entry(label_link_id).clone();
            let ty = self.get_type(label_link_id).clone();
            assert_eq!(entry.mem, VarDefinitionSpace::Static);

            if let Some(key) = entry.name {
                self.functions.insert(key, label_link_id);
            }

            self.push_code(
                LCode::DeclareFunction(Some(block_id)),
                ty,
                entry.name,
                entry.span_id,
                entry.mem,
            );
        }

        // get block ordering
        let blocks = self.blocks.post_order_blocks();
        let mut values = vec![];

        for block_id in blocks.into_iter() {
            println!("X: {}", block_id);
            let block = self.blocks.get_block(block_id);
            let size = block.len();
            let scope_id = block.scope_id;
            if block.entry.is_none() {
                continue;
            }

            let entry_id = block.entry.unwrap();

            let mut entries = vec![];
            let mut v = entry_id;
            loop {
                let entry = self.get_entry(v).clone();
                let next = entry.next;
                entries.push(entry);
                if next == v {
                    break;
                } else {
                    v = next;
                }
            }

            let mut index = 0;
            for mut entry in entries.into_iter() {
                if let Some(ty) = b.types.u.resolve(&entry.ty) {
                    entry.ty = ty;
                }

                if entry.mem == VarDefinitionSpace::Static {
                    match &entry.code {
                        LCode::Val(lit) => {
                            self.statics.insert(entry.name.unwrap(), lit.clone());
                        }
                        _ => (),
                    }
                }

                let scope = self.scopes.get_scope(scope_id);
                let scope_type = scope.scope_type;
                let is_term = entry.code.is_term();
                if index == size && !is_term && scope_type != ScopeType::Static {
                    b.push_error(&format!("Unterminated Block: {}", block_id), entry.span_id);
                }

                let link_id = entry.link.unwrap();
                let value_id = ValueId::new(values.len() as u32);
                values.push(link_id);
                let entry = self.get_entry_mut(link_id);
                entry.value_id = Some(value_id);
                index += 1;
            }
        }

        self.type_inference_enforce(b);

        Ok((self, values))
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

        for (i, expr) in seq.into_iter().enumerate() {
            let block = self.blocks.get_block(self.current_block_id());
            let scope_id = block.scope_id;
            println!("push: {} - {}:{}", i, scope_id, self.current_block_id());
            //b.dump_ast(&expr);
            let r = self.push_node(expr, b)?;
            let block = self.blocks.get_block(self.current_block_id());
            let scope_id = block.scope_id;
            println!(
                "push: {} - {}:{} - {:?}",
                i,
                scope_id,
                self.current_block_id(),
                r
            );
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

        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        let link_id = block.last().unwrap();
        Ok(FlattenResult::link(link_id))
    }

    pub fn push_return(&mut self, values: ArgVec, span_id: SpanId) -> LinkId {
        let _ = self.push_call_values(&values);

        self.push_code(
            LCode::Return,
            AstType::Unit,
            None,
            span_id,
            VarDefinitionSpace::Reg,
        )
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
            LCode::PlaceholderTerminal(_) => unreachable!(),
            LCode::PlaceholderCodeReference => unreachable!(),
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
        // handle leaving scope here?
        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        let _start_stack = self.scopes.walk_scopes(block.scope_id);

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

        println!("jump to: {}=>{}", self.current_block_id(), target_id);
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

    pub fn calculate_function_arguments(
        &mut self,
        def: &Lambda,
        args: &[Argument],
        def_span_id: SpanId,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> Result<(
        AstType, // return type
        Vec<Argument>,
    )> {
        //println!("args: {:?}", args);

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
                            b.push_error(
                                &format!("Extra positional field: {}", index),
                                call_span_id,
                            );
                        }
                    }
                }

                // named arguments follow positional args
                Argument::Named(key, expr) => {
                    // make sure we don't double add
                    if populated_set.contains(key) {
                        let name = b.labels.r(key.into());
                        b.push_error(
                            &format!("Keyword argument duplicate: {}", name),
                            call_span_id,
                        );
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
        //println!("field_list: {:?}", fields_list);

        let args: Vec<Argument> = fields_list
            .iter()
            .filter_map(|(field_key, field_ty)| {
                let field_key = field_key.unwrap();
                match field_ty {
                    AstType::Args(_) => Some(Argument::Args(field_key, args_seq.clone())),
                    AstType::KwArgs(_) => Some(Argument::KwArgs(field_key, kwargs_map.clone())),
                    _ => {
                        if let Some(v) = value_map.remove(&field_key) {
                            Some(Argument::Named(field_key, v.into()))
                        } else {
                            let s_name = b.labels.r(field_key.into());
                            b.push_error(
                                &format!("caller missing named field: {}", s_name),
                                call_span_id,
                            );
                            None
                        }
                    }
                }
            })
            .collect();

        if fields_list.len() != args.len() {
            b.push_error_labels(vec![
                b.primary_label(&format!("Call arity mismatch: call"), call_span_id),
                b.secondary_label(&format!("function"), def_span_id),
            ]);
            //assert!(false);
            //return Err(Error::new(BlockifyError::Invalid));
        }

        if args_seq.len() > 0 && def_has_args {
            // extra fields
            b.push_error(
                &format!("extra fields, no args field: {:?}", args_seq),
                call_span_id,
            );
        }
        Ok((ret.clone(), args))
    }

    fn push_call_arguments(
        &mut self,
        args: Vec<Argument>,
        span_id: SpanId,
        b: &mut NB,
    ) -> Result<ArgVec> {
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
        Ok(values)
    }

    fn push_bake_static(
        &mut self,
        name: StringKey,
        def: Lambda,
        def_span_id: SpanId,
        call_func_type: AstType,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> Result<(LinkId, AstType)> {
        let s = b.labels.r(name.into());
        let global_key = b.labels.fresh_key(&s);
        //let s_global = b.labels.r(global_key.into());
        let current_block_id = self.current_block_id();
        self.switch_blocks(self.static_block_id());

        // if it's defined in static scope, just call it
        //println!("[{},{}] RX:  {}", s, s_global, &call_func_type);
        let (_variant_id, v_entry) = if let Some((variant_id, r_ty, v_entry)) =
            self.resolve_function_name(current_block_id, &name, &call_func_type, b)
        {
            //println!("[{}] R2: {}, {:?}", s, call_func_type, (v_entry));
            // unify the resolved function with the caller
            // the function should be resolved, this resolves any thing missing in the caller
            b.unify(&call_func_type, call_span_id, &r_ty, def_span_id);
            (variant_id, v_entry)
        } else {
            // if it's not already baked, we need to do that here
            self.switch_blocks(self.static_block_id());

            let result = self.push_bake_function(
                def,
                call_func_type.clone(),
                def_span_id,
                name,
                global_key,
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

            // update the variant with the resolved type
            self.scopes.variant_update(
                self.static_scope_id(),
                name,
                variant_id,
                r_ty2.clone(),
                v_entry,
            );
            (variant_id, v_entry)
        };

        // we are keeping a list of function names so we can look them up later
        // there's a better way to do this.  A function only makes sense in the context of a call
        // so our lookups should actually be resolved by the caller
        self.functions.insert(name, v_entry);

        Ok((v_entry, call_func_type))
    }

    fn push_call(
        &mut self,
        name: StringKey,
        scope_id: ScopeId,
        def: Lambda,
        def_span_id: SpanId,
        call_span_id: SpanId,
        args: Vec<Argument>,
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

        let s_name = b.labels.r(name.into());
        println!(
            "{}: push_call: {:?}",
            s_name,
            (scope_id, self.current_block_id())
        );

        // look up the prototype
        // calculate the calling arguments
        let (_, args) =
            self.calculate_function_arguments(&def, &args, def_span_id, call_span_id, b)?;

        let call_values = self.push_call_arguments(args, call_span_id, b)?;
        let call_ty = argvec_type(&call_values);

        let (def_func_type, _def_arg_ty, def_ret_ty) = self.refresh_func_type(&def, b);

        // construct call function type
        let call_func_type = AstType::Func(
            AstType::Struct(call_ty.fields()).into(),
            ReturnType::Single(def_ret_ty.clone()).into(),
        );

        b.unify(&call_func_type, call_span_id, &def_func_type, def_span_id);

        let is_static = self.static_scope_id() == scope_id;
        if is_static {
            let r =
                self.push_bake_static(name, def, def_span_id, call_func_type, call_span_id, b)?;
            self.drain_diagnostics(b);
            let (fun_link_id, _bake_ty) = r;

            self.switch_blocks(current_block_id);
            //println!(
            //"call: call_ty: {}, bake_ty:{}, ret_ty: {}",
            //call_ty, bake_ty, ret_ty
            //);
            self.push_function_call(fun_link_id, call_values, def_ret_ty, call_span_id)
        } else {
            self.switch_blocks(current_block_id);

            println!(
                "bake lambda: {:?}",
                (scope_id, current_block_id, b.labels.r(name.into()))
            );

            let next_block_id = self.blocks.new_block(scope_id);

            let result = self.push_bake_lambda_inner(
                name,
                name,
                scope_id,
                next_block_id,
                def,
                def_func_type.clone(),
                def_span_id,
                call_span_id,
                ScopeType::Function,
                Successor::BlockScope,
                VarDefinitionSpace::Reg,
                b,
            )?;

            self.drain_diagnostics(b);
            let (_variant_id, _, fun_block_id, _, _, _, r) = result;

            self.switch_blocks(next_block_id);

            // now that we have the arguments calculated, and the lambda baked, jump!
            self.switch_blocks(current_block_id);
            self.push_jump(fun_block_id.into(), call_values, call_span_id);
            self.switch_blocks(next_block_id);
            Ok(r)
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
        call_span_id: SpanId,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        let block_id = self.current_block_id();
        let block = self.blocks.get_block(block_id);
        println!("push_builtin_call: {:?}, scope: {}", id, block.scope_id);

        let def_span_id = b.spans.get_span_unknown();
        let (ret_ty, args) =
            self.calculate_function_arguments(&def, &args, def_span_id, call_span_id, b)?;

        let call_values = self.push_call_arguments(args, call_span_id, b)?;
        let call_ty = argvec_type(&call_values);

        let current_block_id = self.current_block_id();

        // Add links
        self.push_call_values(&call_values);

        let link_id = self.push_code(
            LCode::Builtin(id),
            ret_ty.clone(),
            None,
            call_span_id,
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
    ) -> ArgVec {
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
    ) -> Result<TemplateId> {
        let template_id = self.insert_ast_template(def.clone(), span_id);
        let block = self.blocks.get_block(block_id);
        let scope_id = block.scope_id;
        let scope = self.scopes.get_scope_mut(scope_id);
        scope.lambdas.insert(name.into(), template_id);
        Ok(template_id)
    }

    pub fn push_close_block(&mut self, span_id: SpanId, _b: &mut NB) -> Result<FlattenResult> {
        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        let scope_id = block.scope_id;
        let scope = self.scopes.get_scope(scope_id);
        if let Some(loop_block) = scope.loop_block {
            let link_id = self.maybe_terminate_block(loop_block.start_block, span_id);
            println!("block loop end: {}, {}", loop_block.next_block, link_id);
            self.switch_blocks(loop_block.next_block);
            Ok(FlattenResult::link(link_id))
        } else {
            let block_id = scope.entry_block.unwrap();
            let block = self.blocks.get_block(block_id);
            //unimplemented!("{:?}", (scope_id, scope, block_id, block))
            Ok(FlattenResult::link(block.last().unwrap()))
        }
    }

    pub fn push_goto(
        &mut self,
        label: StringKey,
        args: Vec<Argument>,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        // push a goto
        // if the label exists, then it's straightforward
        // if it doesn't exist, then we save a marker to be picked up by a future definition
        // A definition could be a CPS function, or it could be a label
        // The problem here is that we can't really define the goto, until we know what function we
        // are calling, so we need to defer writing out the goto until we have the definition
        // We need to do the goto and the function definition at the same time, so we can do type
        // unification, as well as monomorphization.
        // Also save the caller span, so we can present a good error

        // goto may not get pushed here, it may be deferred
        // if it exists, then we might handle it here properly.
        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        // Goto is terminal
        let scope_id = block.scope_id;

        let s_name = b.labels.r(label.into());

        // if a template exists, use it
        if let Some(template_id) = self.resolve_template(scope_id, label.into()) {
            let scope = self.scopes.get_scope(scope_id);
            let parent_block_id = scope.entry_block.unwrap();
            let goto_block_id = self.current_block_id();

            let (def, def_span_id) = self.get_ast_template(template_id).clone();
            // New Func Scope
            let (fun_block_id, fun_scope_id) = self.new_scope_and_block(ScopeType::Block, scope_id);
            // block graph
            self.blocks
                .block_succ(parent_block_id, fun_block_id, Successor::BlockScope);

            let (fun_scope_id, fun_block_id, def_func_type, def_arg_type, _) = self
                .push_cps_block(
                    Some(label.into()),
                    scope_id,
                    fun_scope_id,
                    fun_block_id,
                    def.clone(),
                    def_span_id,
                    b,
                )?;

            // switch back to goto block
            self.switch_blocks(goto_block_id);
            let link_id = self.push_cps_jump(
                &def,
                def_func_type,
                def_arg_type,
                fun_block_id,
                def_span_id,
                call_span_id,
                args,
                b,
            )?;

            println!(
                "{}: push_goto lambda: from {}:{}=>{}:{}, link: {}",
                s_name, scope_id, current_block_id, fun_scope_id, fun_block_id, link_id
            );
            //self.switch_blocks(current_block_id);
            return Ok(FlattenResult::statement());
        }

        // if a label exists, then jump to it
        if let Some(target_block_id) = self.resolve_label(scope_id, label.into()) {
            // not possible to pass args to a label, use a CPS function instead
            assert_eq!(args.len(), 0);
            let target_block = self.blocks.get_block(target_block_id);
            let target_scope_id = target_block.scope_id;
            let jump_args = self.push_call_arguments(args, call_span_id, b)?;
            let link_id = self.push_jump(target_block_id.into(), jump_args, call_span_id);
            println!(
                "{}: push_goto label: {}:{}=>{}:{}, link: {}",
                s_name, scope_id, current_block_id, target_scope_id, target_block_id, link_id
            );
            self.switch_blocks(current_block_id);
            return Ok(FlattenResult::statement());
        }

        // if we don't have a template or a label already, then we defer
        if let Some(fun_scope_id) = self
            .scopes
            .find_nearest_scope(scope_id, &[ScopeType::Function])
        {
            let link_id = block.last().unwrap();
            self.push_code(
                LCode::PlaceholderTerminal(link_id),
                AstType::Unit,
                None,
                call_span_id,
                VarDefinitionSpace::Default,
            );

            let scope = self.scopes.get_scope_mut(fun_scope_id);
            let d = DeferredGoto::new(label.into(), args, call_span_id, current_block_id, link_id);
            println!(
                "{}: push_goto, defer goto: {:?} in scope: {}",
                s_name, d, fun_scope_id
            );
            scope.deferred_goto.add(d);
            return Ok(FlattenResult::statement());
        } else {
            // goto without function scope
            unreachable!()
        }
    }

    fn push_cps_jump(
        &mut self,
        def: &Lambda,
        def_func_type: AstType,
        def_arg_type: AstType,
        target_block_id: BlockId,
        def_span_id: SpanId,
        call_span_id: SpanId,
        args: Vec<Argument>,
        b: &mut NB,
    ) -> Result<LinkId> {
        let (_ret_ty, args) =
            self.calculate_function_arguments(&def, &args, def_span_id, call_span_id, b)?;

        let call_values = self.push_call_arguments(args, call_span_id, b)?;
        let call_func_type = argvec_type(&call_values);

        // unify the caller args and the refreshed function args
        b.unify(&call_func_type, call_span_id, &def_arg_type, def_span_id);

        // now that we have the arguments calculated, and the lambda baked, jump!
        let link_id = self.push_jump(target_block_id.into(), call_values, call_span_id);
        Ok(link_id)
    }

    fn push_cps_block(
        &mut self,
        name: Option<StringKey>,
        scope_id: ScopeId,
        fun_scope_id: ScopeId,
        fun_block_id: BlockId,
        def: Lambda,
        def_span_id: SpanId,
        b: &mut NB,
    ) -> Result<(ScopeId, BlockId, AstType, AstType, AstType)> {
        let current_block_id = self.current_block_id();

        //let fun_scope = self.scopes.get_scope_mut(fun_scope_id);
        // we might want to handle this later
        // return in a CPS will return from the scoped function
        //fun_scope.return_block = Some(next_block_id);

        // This expects to be called in a block that is ready to jump
        let (def_func_type, def_arg_type, def_ret_type) = self.refresh_func_type(&def, b);

        // Start lambda block
        let s_name = if let Some(name) = name {
            b.labels.r(name.into())
        } else {
            "anon".to_string()
        };
        let lambda_name = b.labels.fresh_key(&s_name);

        println!(
            "{}: push_cps_block in {}:{} => {}:{}",
            s_name,
            scope_id,
            self.current_block_id(),
            fun_scope_id,
            fun_block_id
        );

        let body = *def.body.unwrap();

        self.switch_blocks(fun_block_id);
        let (entry_link_id, _) = self.push_start_block(
            fun_scope_id,
            def_func_type.clone(),
            Some(lambda_name),
            def_span_id,
            VarDefinitionSpace::Default,
        );
        // add the name to scope
        // do this early for recursive functions
        self.scopes
            .scope_define(scope_id, lambda_name, entry_link_id);

        // add entry to scope, for recursion
        let r_ty1 = b.types.u.resolve(&def_func_type).unwrap();
        // we need to know the link
        //let variant_id = if let Some(global_name) = global_name {
        let _variant_id = self
            .scopes
            .variant_add(scope_id, lambda_name, r_ty1, entry_link_id);
        //} else {
        //None
        //};

        // flatten function, and switch to next
        let _ = self.push_node(body, b)?;

        // terminate if not already terminated
        // this is for dead code
        let block = self.blocks.get_block(self.current_block_id());
        if !block.is_term() {
            self.push_code(
                LCode::PlaceholderTerminal(block.last().unwrap()),
                AstType::Unit,
                None,
                def_span_id,
                VarDefinitionSpace::Default,
            );
        }

        // if this really is a CPS function, then it should never return
        // TODO: verify that it never returns, could be with the function signature
        // If the function returns, it has no meaning, because a goto must be terminal,
        // it's too confusing to try to treat it like a call in that case, it's better
        // to just error out
        // What does it even mean that a CPS function never calls it's continuation?

        self.drain_diagnostics(b);

        // switch back to where it was called
        self.switch_blocks(current_block_id);

        return Ok((
            fun_scope_id,
            fun_block_id,
            def_func_type,
            def_arg_type,
            def_ret_type,
        ));
    }

    /*
    fn push_bake_block(
        &mut self,
        local_name: StringKey,
        global_name: StringKey,
        def: Lambda,
        def_func_type: AstType,
        def_span_id: SpanId,
        b: &mut NB,
    ) -> Result<(VariantId, ScopeId, BlockId)> {
        let fun_block_id = self.current_block_id();
        let block = self.blocks.get_block(fun_block_id);
        assert!(block.len() == 0);
        let fun_scope_id = block.scope_id;

        let (entry_link_id, _) = self.push_start_block(
            fun_scope_id,
            def_func_type.clone(),
            Some(global_name),
            def_span_id,
            VarDefinitionSpace::Default,
        );

        // block graph
        // make sure it's not orphaned
        let scope = self.scopes.get_scope(fun_scope_id);
        let parent = scope.entry_block.unwrap();
        self.blocks
            .block_succ(parent, fun_block_id, Successor::BlockScope);

        // add entry to scope, for recursion
        let r_ty1 = b.types.u.resolve(&def_func_type).unwrap();
        let variant_id = self
            .scopes
            .variant_add(fun_scope_id, local_name, r_ty1, entry_link_id);

        // add the name to scope
        // do this early for recursive functions
        self.scopes
            .scope_define(fun_scope_id, global_name, entry_link_id);

        // flatten function, and switch to next
        self.switch_blocks(fun_block_id);
        let body = def.body.unwrap();
        let _ = self.push_node(*body, b)?;
        let block = self.blocks.get_block(self.current_block_id());
        assert!(block.is_term());

        Ok((variant_id, fun_scope_id, fun_block_id))
    }
    */

    fn push_bake_lambda_inner(
        &mut self,
        local_name: StringKey,
        global_name: StringKey,
        next_scope_id: ScopeId,
        next_block_id: BlockId,
        def: Lambda,
        def_func_type: AstType,
        def_span_id: SpanId,
        call_span_id: SpanId,
        scope_type: ScopeType,
        succ_type: Successor,
        mem: VarDefinitionSpace,
        b: &mut NB,
    ) -> Result<(
        VariantId,
        ScopeId,
        BlockId,
        LinkId,
        AstType,
        ArgVec,
        FlattenResult,
    )> {
        // create a new scope and block
        // build the function body in that scope and block
        // allow for recursion
        //
        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        let scope_id = block.scope_id;

        // New Func Scope
        let (fun_block_id, fun_scope_id) = self.new_scope_and_block(scope_type, next_scope_id);
        let body = *def.body.unwrap();

        let fun_scope = self.scopes.get_scope_mut(fun_scope_id);
        fun_scope.return_block = Some(next_block_id);

        // block graph
        self.blocks
            .block_succ(current_block_id, fun_block_id, succ_type);

        self.switch_blocks(fun_block_id);
        let (entry_link_id, _) = self.push_start_block(
            fun_scope_id,
            def_func_type.clone(),
            Some(global_name),
            def_span_id,
            mem,
        );

        // add entry to scope, for recursion
        let r_ty1 = b.types.u.resolve(&def_func_type).unwrap();
        // we need to know the link
        //let variant_id = if let Some(global_name) = global_name {
        let variant_id = self
            .scopes
            .variant_add(scope_id, local_name, r_ty1, entry_link_id);
        //} else {
        //None
        //};

        // add the name to scope
        // do this early for recursive functions
        self.scopes
            .scope_define(scope_id, global_name, entry_link_id);

        // flatten function, and switch to next
        self.switch_blocks(fun_block_id);
        let _ = self.push_node(body, b)?;
        self.maybe_terminate_block(next_block_id, def_span_id);

        let next_arg_ty =
            self.resolve_return_type(fun_block_id, def_func_type.clone(), call_span_id, b);

        assert!(next_arg_ty.is_composite());
        let block_ty = AstType::Func(
            next_arg_ty.clone().into(),
            ReturnType::Single(AstType::Unit).into(),
        );
        let s_name = b.labels.r(local_name.into());
        let cont_name = format!("{}.cont", s_name);

        self.switch_blocks(next_block_id);
        let (_v_block, v_args) = self.push_start_block(
            next_scope_id,
            block_ty.clone(),
            Some(b.labels.s(&cont_name)),
            call_span_id,
            VarDefinitionSpace::Reg,
        );

        let next_link_id = match &next_arg_ty {
            AstType::Unit => None,
            _ => {
                if v_args.len() == 0 {
                    None
                } else {
                    Some(v_args.first().unwrap().1)
                }
            }
        };

        let r = if let Some(link_id) = next_link_id {
            FlattenResult::link(link_id)
        } else {
            FlattenResult::statement()
        };

        Ok((
            variant_id,
            fun_scope_id,
            fun_block_id,
            entry_link_id,
            next_arg_ty,
            v_args,
            r,
        ))
    }

    fn push_bake_function(
        &mut self,
        def: Lambda,
        def_func_ty: AstType,
        def_span_id: SpanId,
        name: StringKey,
        global_name: StringKey,
        b: &mut NB,
    ) -> Result<(VariantId, FlattenResult)> {
        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        let scope_id = block.scope_id;

        // create a next scope, that includes the function
        // when the function returns it jumps to the return block, which is the next function
        // which is out of scope for the function.  This requires that the function cleanup the
        // stack before jumping to the return block
        // This scope is empty, and isn't used for anything other than including the function scope
        // This behavior is slightly different than inline functions that jump back into the same
        // scope from which they were called.

        let (next_block_id, next_scope_id) = self.new_scope_and_block(ScopeType::Block, scope_id);

        let (v_id, _scope, _block, entry_link_id, _, v_args, _r) = self.push_bake_lambda_inner(
            name,
            global_name,
            next_scope_id,
            next_block_id,
            def,
            def_func_ty,
            def_span_id,
            def_span_id,
            ScopeType::Function,
            Successor::FunctionDeclaration,
            VarDefinitionSpace::Static,
            b,
        )?;

        self.push_return(v_args, def_span_id);

        // restore position back to where we started
        self.switch_blocks(current_block_id);
        Ok((v_id, FlattenResult::link(entry_link_id)))
    }

    fn resolve_return_type(
        &self,
        fun_block_id: BlockId,
        def_func_ty: AstType,
        span_id: SpanId,
        b: &mut NB,
    ) -> AstType {
        let func_ret_ty = if let AstType::Func(_arg, ret) = def_func_ty.clone() {
            if let ReturnType::Single(ret) = *ret {
                ret.clone()
            } else {
                unreachable!()
            }
        } else {
            unreachable!()
        };

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
            b.types.dump();
            b.push_error(
                &format!(
                    "Return Type Must Resolve: {}, arity: {}",
                    &func_ret_ty, arity
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
        //if func_ret_ty != resolved_ret_ty {
        //println!("ret res: {}=>{}", func_ret_ty, resolved_ret_ty);
        //}
        resolved_ret_ty
    }

    fn refresh_func_type(&self, def: &Lambda, b: &mut NB) -> (AstType, AstType, AstType) {
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
        (def_func_type, def_arg_ty, ret_ty)
    }

    pub fn push_bake(&mut self, name: StringKey, func_type: AstType, b: &mut NB) -> Result<LinkId> {
        let current_block_id = self.current_block_id();
        if let Some((__scope_id, def, def_span_id)) = self.resolve_lambda(current_block_id, name) {
            let result = self.push_bake_function(def, func_type, def_span_id, name, name, b);
            if result.is_err() {
                self.drain_diagnostics(b);
            }
            let (_variant_id, r) = result?;

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

    pub fn push_cps_and_jump(
        &mut self,
        name: StringKey,
        template_id: TemplateId,
        args: Vec<Argument>,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> Result<LinkId> {
        // we want to handle monomorphization here.
        /*
                        let ty = AstType::func(vec![], AstType::Unit);
                        if let Some((_variant_id, resolve_type, link_id)) =
                            self.resolve_function_name(current_block_id, key, &ty, b)
                        {
                            let entry = self.get_entry(link_id);
                            entry.block_id
        */
        let goto_block_id = self.current_block_id();

        let block = self.blocks.get_block(goto_block_id);
        let scope_id = block.scope_id;
        let last_link_id = block.last().unwrap();
        let entry = self.get_entry_mut(last_link_id);
        if let LCode::PlaceholderTerminal(prev_link_id) = entry.code {
            // invalidate dummy jump
            entry.next = prev_link_id;
            let block = self.blocks.get_block_mut(goto_block_id);
            // remove last entry in the block
            block.last = Some(prev_link_id);
            block.term = false;
        }

        let (def, def_span_id) = self.get_ast_template(template_id).clone();
        // New Func Scope
        let (fun_block_id, fun_scope_id) = self.new_scope_and_block(ScopeType::Block, scope_id);
        // block graph
        self.blocks
            .block_succ(goto_block_id, fun_block_id, Successor::BlockScope);

        let (_, fun_block_id, def_func_type, def_arg_type, _) = self.push_cps_block(
            Some(name.into()),
            scope_id,
            fun_scope_id,
            fun_block_id,
            def.clone(),
            def_span_id,
            b,
        )?;

        // switch back to goto block
        self.switch_blocks(goto_block_id);
        let link_id = self.push_cps_jump(
            &def,
            def_func_type,
            def_arg_type,
            fun_block_id,
            def_span_id,
            call_span_id,
            args,
            b,
        )?;
        println!("bake deferred goto: link: {}", link_id);
        Ok(link_id)
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
                //println!("bi: {:?}", bi);
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
                self.ensure_open(span_id, b);
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
                let y_span_id = y.span_id;
                self.switch_blocks(current_block_id);
                let rx = self.push_node(*x, b)?;
                let ry = self.push_node(*y, b)?;
                let vx = rx.link_id.unwrap();
                let vy = ry.link_id.unwrap();
                let rx_ty = self.get_type(vx).clone();
                let ry_ty = self.get_type(vy).clone();

                b.unify(&rx_ty, x_span_id, &ry_ty, y_span_id);

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
                let scope_id = block.scope_id;
                if let Some(def_link_id) = self.resolve_name(current_block_id, key) {
                    let link_id = def_link_id;
                    Ok(FlattenResult::link(link_id))
                } else {
                    let s = b.labels.r(key.into());
                    b.push_error(&format!("ident `{}` not found in {}", s, scope_id), span_id);
                    let backtrace = std::backtrace::Backtrace::capture();
                    self.messages
                        .push((format!("ident: not found {}\n{}", s, backtrace), span_id));

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
                    let scope_id = block.scope_id;
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

                    //if self.mode == FlattenMode::Template {
                    //self.push_bake_template2(name, &def, span_id, b)?;
                    //}

                    // save the template
                    let def_span_id = expr.span_id;
                    let template_id =
                        self.save_ast_template(current_block_id, &name, &def, def_span_id)?;

                    // check for deferrals and apply them
                    let scope = self.scopes.get_scope_mut(scope_id);
                    let deferrals = scope.deferred_goto.pop_all(name.into());

                    for d in deferrals {
                        self.switch_blocks(d.block_id);
                        self.push_cps_and_jump(name, template_id, d.args, d.call_span_id, b)?;
                    }
                    self.switch_blocks(current_block_id);
                    return Ok(FlattenResult::statement());
                }

                self.switch_blocks(current_block_id);
                let r = self.push_node(*expr, b)?;
                let v_expr = r.link_id.unwrap();
                let expr_entry = self.get_entry(v_expr);
                let expr_ty = expr_entry.ty.clone();
                let expr_span_id = expr_entry.span_id;

                let offset_decl =
                    if let Some(v_decl) = self.resolve_name(self.current_block_id(), name) {
                        // already declared
                        let decl_entry = self.get_entry(v_decl);
                        b.unify(&decl_entry.ty, decl_entry.span_id, &expr_ty, expr_span_id);
                        v_decl
                    } else {
                        // need to declare it
                        let block = self.blocks.get_block(self.current_block_id());
                        let scope_id = block.scope_id;
                        //let expr_ty = self.get_entry(v_expr).ty.clone();
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
                        expr_ty.clone(),
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
                    Ast::Identifier(ident) => {
                        if let Some((scope_id, def, def_span_id)) =
                            self.resolve_lambda(current_block_id, *ident)
                        {
                            self.push_call(*ident, scope_id, def, def_span_id, span_id, args, b)
                        } else {
                            let name = b.labels.r(ident.into());
                            b.push_error(&format!("Call name not found: {}", name), span_id);
                            Err(Error::new(BlockifyError::Invalid))
                        }
                    }
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
                let term = block.term;
                let parent_scope_id = block.scope_id;

                let v_next = self.blocks.new_block(parent_scope_id);
                self.switch_blocks(v_next);
                self.push_start_block(
                    parent_scope_id,
                    AstType::func(vec![], AstType::Unit), // void=>void
                    Some(b.labels.fresh_key("cond_next")),
                    span_id,
                    VarDefinitionSpace::Default,
                );
                self.switch_blocks(current_block_id);

                // THEN
                let (then_block_id, then_scope_id) =
                    self.new_scope_and_block(ScopeType::Block, parent_scope_id);
                let then_span_id = then_expr.span_id;
                println!(
                    "cond jump to: {}=>{}, {:?}",
                    current_block_id, then_block_id, term
                );
                // only jump if we are in an open block
                if !term {
                    self.blocks
                        .block_succ(current_block_id, then_block_id, Successor::BlockScope);

                    self.blocks
                        .block_succ(current_block_id, then_block_id, Successor::Jump);
                }

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
                    println!("else jump to: {}=>{}", current_block_id, else_block_id);
                    if !term {
                        self.blocks.block_succ(
                            current_block_id,
                            else_block_id,
                            Successor::BlockScope,
                        );
                        self.blocks
                            .block_succ(current_block_id, else_block_id, Successor::Jump);
                    }

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
                    println!("else default jump to: {}=>{}", current_block_id, v_next);
                    if !term {
                        self.blocks
                            .block_succ(current_block_id, v_next, Successor::BlockScope);
                        self.blocks
                            .block_succ(current_block_id, v_next, Successor::Jump);
                    }
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

            Ast::ControlFlowMarker(ControlFlowMarker::BlockReference(expr)) => {
                let block_id = match &expr.node {
                    Ast::Identifier(key) => {
                        let ty = AstType::func(vec![], AstType::Unit);
                        if let Some((_variant_id, resolve_type, link_id)) =
                            self.resolve_function_name(current_block_id, key, &ty, b)
                        {
                            let entry = self.get_entry(link_id);
                            entry.block_id
                        } else {
                            let link_id = self.push_node(*expr, b)?.link_id.unwrap();
                            let entry = self.get_entry(link_id);
                            if entry.code.is_start() {
                                entry.block_id
                            } else {
                                unimplemented!()
                            }
                        }
                    }
                    _ => unimplemented!("{:?}", expr),
                };
                let code = LCode::Val(Literal::Block(block_id));
                let link_id = self.push_code(
                    code,
                    AstType::JumpTarget,
                    None,
                    span_id,
                    VarDefinitionSpace::Default,
                );
                Ok(FlattenResult::link(link_id))
            }

            Ast::ControlFlowMarker(ControlFlowMarker::BlockStart(name, args)) => {
                // LABEL

                let name = name.unwrap();
                //let s_name = name.map(|key| b.labels.r(key)).unwrap_or(String::new());
                let s_name = b.labels.r(name.into());

                // push a new block.  But check to make sure the previous block was closed
                let scope_id = block.scope_id;

                // check for duplicates
                if let Some(block_id) = self.resolve_label(scope_id, name.into()) {
                    //block_id
                    unimplemented!("duplicate label: {}", block_id);
                }

                // create a new block
                assert_eq!(0, args.len());
                let new_block_id = self.blocks.new_block(scope_id);
                println!(
                    "{}: block start new: {}, in scope: {}",
                    s_name, new_block_id, scope_id
                );
                self.blocks.block_succ(
                    self.current_block_id(),
                    new_block_id,
                    Successor::BlockScope,
                );
                let scope = self.scopes.get_scope_mut(scope_id);
                scope.block_labels.insert(name.into(), new_block_id);

                // get all deferrals in this scope
                // and generate jumps to the new block
                let scope = self.scopes.get_scope_mut(scope_id);
                let deferrals = scope.deferred_goto.pop_all(name.into());

                // terminate deferred blocks, with a call to the new block we are instantiating
                // here
                // TODO: but what we actually want to do is make the CPS for the specific call
                for d in deferrals {
                    self.switch_blocks(d.block_id);

                    // invalidate dummy jump
                    let entry = self.get_entry_mut(d.link_id);
                    entry.next = d.link_id;
                    let block = self.blocks.get_block_mut(d.block_id);
                    // remove last entry in the block
                    block.last = Some(d.link_id);
                    block.term = false;

                    // delete the dummy jump and replace it
                    // we are only jumping to a label here, so we don't need to monomorphize
                    // monomorphization happens at the function level instead
                    let jump_args = self.push_call_arguments(d.args.clone(), d.call_span_id, b)?;
                    let link_id = self.push_jump(new_block_id.into(), jump_args, d.call_span_id);
                    println!("{}: bake deferred: {:?}, link: {}", s_name, d, link_id);
                }

                self.switch_blocks(current_block_id);

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

                b.unify(&then_ty, then_span_id, &else_ty, else_span_id);

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

            Ast::ControlFlowMarker(ControlFlowMarker::Goto(label, args)) => {
                self.push_goto(label, args, span_id, b)
            }

            Ast::ControlFlowMarker(ControlFlowMarker::BlockEnd) | Ast::CloseBlock => {
                self.push_close_block(span_id, b)
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

    pub fn ensure_open(&mut self, span_id: SpanId, b: &mut NB) {
        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(self.current_block_id());
        let scope_id = block.scope_id;
        if block.term {
            let new_block_id = self.blocks.new_block(scope_id);
            let name = b.labels.fresh_key("dead");
            let scope = self.scopes.get_scope(scope_id);
            println!(
                "ensure open: {}:{} => {}:{}",
                scope_id, current_block_id, scope_id, new_block_id
            );
            self.blocks.block_succ(
                scope.entry_block.unwrap(),
                new_block_id,
                Successor::BlockScope,
            );

            self.switch_blocks(new_block_id);
            self.push_start_block(
                scope_id,
                AstType::Func(
                    AstType::Struct(vec![]).into(),
                    ReturnType::Single(AstType::Unit).into(),
                ),
                Some(name),
                span_id,
                VarDefinitionSpace::Reg,
            );
        }
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
