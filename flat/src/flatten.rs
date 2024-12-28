use super::resolve_attribute;
use anyhow::Error;
use anyhow::Result;
use compile_core::{
    AbstractionId, Argument, AssignTarget, Ast, AstFuncType, AstNode, AstType, BuiltinId,
    ControlFlowMarker, Lambda, LinkOptions, Literal, ReturnType, SpanId, StringKey,
};

use std::collections::{HashMap, HashSet, VecDeque};

use std::convert::Into;

use crate::{
    AbstractionsBuilder, BlockGraph, BlockId, BlockifyError, Builtin, CodeEntry, CodeOffset,
    ContinuationFlow, DeferredGotoList, FlowEdge, FunctionVariantBuilder, LCode, LinkId,
    NodeBuilder as NB, ScopeId, ScopeState, ScopeType, ScopedContinuations, Successor, ValueId,
    VarDefinitionSpace, VariantId,
};
use std::ops::{Deref, DerefMut};

pub type ArgVec = Vec<(Option<StringKey>, LinkId, AstType, SpanId)>;
pub type ArgVecRef<'a> = &'a ArgVec;

pub fn argvec_type(values: &ArgVec) -> AstType {
    AstType::Struct(
        values
            .iter()
            .map(|v| (v.0, v.2.clone()))
            .collect::<Vec<_>>(),
    )
}

#[derive(Debug)]
pub struct FlattenResult {
    pub link_id: Option<LinkId>,
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

pub trait FlattenState: std::fmt::Debug + Clone {}
#[derive(Debug, Clone)]
pub struct Start {}
impl FlattenState for Start {}

#[derive(Debug, Clone)]
pub struct FirstPass {}
impl FlattenState for FirstPass {}

#[derive(Debug, Clone)]
pub struct Module {
    pub values: Vec<LinkId>,
}
impl FlattenState for Module {}

pub struct FlattenInner {
    pub(super) link: LinkOptions,
    pub(super) entries: Vec<CodeEntry>,
    pub blocks: BlockGraph,
    static_scope: ScopeId,
    static_block: BlockId,
    pub(crate) current_block: BlockId,
    pub(super) block_links: HashMap<BlockId, LinkId>,
    pub(crate) functions: HashMap<StringKey, LinkId>,
    pub(crate) open_identifiers: Vec<LinkId>,
    pub(crate) scoped_continuations: ScopedContinuations,
    pub(super) deferred_goto: DeferredGotoList,
    pub(super) variants: FunctionVariantBuilder,
    pub(super) abstractions: AbstractionsBuilder,
}

pub struct Flatten<S: FlattenState> {
    pub inner: Box<FlattenInner>,
    pub state: S,
}

impl<S: FlattenState> Deref for Flatten<S> {
    type Target = FlattenInner;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<S: FlattenState> DerefMut for Flatten<S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl Flatten<Start> {
    pub fn next(self) -> Flatten<FirstPass> {
        Flatten {
            inner: self.inner,
            state: FirstPass {},
        }
    }

    pub fn flatten_module(node: AstNode, b: &mut NB) -> Result<Flatten<FirstPass>> {
        // setup environment with static scope and block
        // blocks will be moved into environment eventually
        // FlattenEnvironment represents the module level structures

        let mut blocks = BlockGraph::new();
        let (static_block_id, static_scope_id) = blocks.root();
        let inner = FlattenInner {
            entries: vec![],
            blocks,
            link: LinkOptions::new(),
            static_scope: static_scope_id,
            static_block: static_block_id,
            current_block: static_block_id,
            block_links: HashMap::new(),
            functions: HashMap::new(),
            open_identifiers: vec![],
            scoped_continuations: ScopedContinuations::new(),
            deferred_goto: DeferredGotoList::new(),
            variants: FunctionVariantBuilder::new(),
            abstractions: AbstractionsBuilder::new(),
        };

        let mut f = Self {
            inner: inner.into(),
            state: Start {},
        };

        let static_block_id = f.static_block;

        if let Ast::Module(key, body) = node.node {
            // start module block
            f.push_start_block_static(AstFuncType::new_void_void().into(), Some(key), node.span_id);
            let _ = f.push_node(*body, b)?;

            // return control to the root block
            f.switch_blocks(static_block_id);
            Ok(f.next())
        } else {
            b.push_error("Not a module", node.span_id);
            Err(Error::new(BlockifyError::Invalid))
        }
    }
}

impl Flatten<FirstPass> {
    pub fn finish(self, b: &mut NB) -> Result<Flatten<Module>> {
        let (f, values) = self.inner._finish(b)?;
        let m = Flatten {
            inner: f.into(),
            state: Module { values },
        };
        Ok(m)
    }
}

impl FlattenInner {
    pub fn resolve_code_offset(&self, code_offset: CodeOffset) -> ValueId {
        self.maybe_resolve_code_offset(code_offset)
            .expect(&format!("Unable to resolve: {}", code_offset))
    }

    pub fn maybe_resolve_code_offset(&self, code_offset: CodeOffset) -> Option<ValueId> {
        match code_offset {
            CodeOffset::Value(v) => Some(v),
            CodeOffset::Link(link_id) => {
                let entry = self.get_entry(link_id);
                entry.value_id
            }
            CodeOffset::Block(block_id) => {
                if let Some(link_id) = self.block_links.get(&block_id) {
                    let entry = self.get_entry(*link_id);
                    entry.value_id
                } else {
                    None
                }
            }
        }
    }

    pub fn type_inference(&mut self, b: &mut NB) {
        for entry in self.entries.iter_mut() {
            if !entry.ty.is_unknown() {
                continue;
            }
            b.types.u.resolve(&entry.ty);
        }
    }

    pub fn type_inference_enforce(&mut self, b: &mut NB) {
        //b.types.dump();
        for entry in self.entries.iter_mut() {
            if !entry.ty.is_unknown() {
                continue;
            }

            if let Some(ty) = b.types.u.resolve(&entry.ty) {
                /*
                b.push_warning(
                    &format!(
                        "Late Unresolved Type: {}=>{} @ {}",
                        &entry.ty,
                        &ty,
                        entry.link.unwrap()
                    ),
                    entry.span_id,
                );
                */
                entry.ty = ty;
            } else {
                b.push_error(
                    &format!("Unresolved Type: {} @ {}", &entry.ty, entry.link.unwrap()),
                    entry.span_id,
                );
            }
        }
    }

    pub fn static_scope_id(&self) -> ScopeId {
        self.static_scope
    }

    pub fn static_block_id(&self) -> BlockId {
        self.static_block
    }

    pub fn switch_blocks(&mut self, block_id: BlockId) {
        self.current_block = block_id;
    }

    pub fn current_block_id(&self) -> BlockId {
        self.current_block
    }

    pub fn dump_scope(&self, block_id: BlockId, b: &NB) {
        let block = self.blocks.get_block(block_id);
        self.blocks.dump_scope(block.scope(), b);
    }

    pub fn variant_add(
        &mut self,
        scope_id: ScopeId,
        name: StringKey,
        ty: AstType,
        link_id: LinkId,
        block_id: BlockId,
    ) -> VariantId {
        let variant_id = self.variants.add(ty, link_id, block_id, name);
        let scope = self.blocks.get_scope_mut(scope_id);
        scope.variant_link(name, variant_id);
        variant_id
    }

    pub fn variant_update(&mut self, variant_id: VariantId, ty: AstType, link_id: LinkId) {
        let v = self.variants.get_mut(variant_id);
        v.link_id = link_id;
        v.ty = ty;
    }

    pub fn resolve_all_function_name(
        &self,
        start_scope_id: ScopeId,
        name: &StringKey,
    ) -> Vec<(VariantId, AstType, LinkId, ScopeId)> {
        let mut out = vec![];
        for variant_id in self.blocks.list_variants_by_name(start_scope_id, name) {
            let v = self.variants.get(variant_id);
            out.push((variant_id, v.ty.clone(), v.link_id, start_scope_id));
        }
        out
    }

    pub fn resolve_function_name(
        &self,
        start_scope_id: ScopeId,
        name: &StringKey,
        call_func_type: &AstType,
        b: &mut NB,
    ) -> Option<(VariantId, AstType, LinkId, ScopeId)> {
        let mut result = None;
        let snapshot = b.types.u.snapshot();
        let ty = call_func_type.clone().into();
        for (variant_id, r_ty, link_id, scope_id) in
            self.resolve_all_function_name(start_scope_id, &name)
        {
            if let Ok(_) = b.types.u.unify(&ty, &r_ty) {
                result = Some((variant_id, r_ty, link_id, scope_id));
                break;
            }
        }
        b.types.u.rollback_to(snapshot);
        result
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

    pub fn resolve_open_abstractions(
        &mut self,
        link_id: LinkId,
        abstraction_id: AbstractionId,
        b: &mut NB,
    ) -> Result<()> {
        let current_block_id = self.current_block_id();
        let entry = self.get_entry(link_id).clone();
        let ty = self.get_type(link_id).clone();
        let span_id = entry.span_id;
        let name = entry.name.unwrap();
        let block_id = entry.block_id;
        let block = self.blocks.get_block(block_id);
        let scope_id = block.scope();

        let (_variant_id, _fun_scope_id, fun_block_id, _) =
            self.gen_cps_block_with_type(name, scope_id, abstraction_id, &ty, span_id, true, b)?;

        // now replace the abstraction code
        let entry = self.get_entry_mut(link_id);
        entry.code = LCode::Val(Literal::Block(fun_block_id));
        b.unify(&entry.ty, entry.span_id, &ty, span_id);
        self.update_connections(link_id);
        self.switch_blocks(current_block_id);
        Ok(())
    }

    pub(super) fn finish_values(&mut self, b: &mut NB) -> Vec<LinkId> {
        let blocks = self.blocks.post_order_blocks();
        let mut values = vec![];

        for block_id in blocks.into_iter() {
            let block = self.blocks.get_block(block_id);
            let scope_id = block.scope();
            if block.empty() {
                continue;
            }

            let scope = self.blocks.get_scope(scope_id);
            if !block.is_term() && !scope.is_static() {
                let entry = self.get_entry(block.last().unwrap());
                b.push_error(&format!("Unterminated Block: {}", block_id), entry.span_id);
            }

            let links = block.iter().collect::<Vec<_>>();
            for link_id in links {
                let value_id = ValueId::new(values.len() as u32);
                values.push(link_id);
                let entry = self.get_entry_mut(link_id);
                entry.value_id = Some(value_id);
            }
        }
        values
    }

    fn _finish(mut self, b: &mut NB) -> Result<(Self, Vec<LinkId>)> {
        self.switch_blocks(self.static_block_id());
        let _ = self.push_code(
            LCode::EndModule,
            AstType::Unit,
            None,
            b.spans.get_span_unknown(),
            VarDefinitionSpace::Default,
        );

        // make sure all claims have been handled
        self.blocks.ensure_claims(b);

        // add prototypes for builtins
        self.inject_builtin_prototypes(b);

        self.resolve_deferred(b)?;
        assert!(self.deferred_goto.is_empty());

        // ensure types are resolved
        self.type_inference_enforce(b);

        self.cont_graph("cont.dot", b);

        self.resolve_open_identifiers(b)?;
        self.resolve_cps(b)?;

        self.switch_blocks(self.static_block_id());

        // DEAD BLOCKS
        let dead_blocks = self.blocks.find_dead_blocks_from_graph();
        for block_id in dead_blocks {
            if let Some(link_id) = self.block_links.get(&block_id).cloned() {
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
            let label_link_id = block.entry();
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

        // the last thing we do is calculate the values, which is the post order traversal of the
        // blocks.
        let values = self.finish_values(b);
        Ok((self, values))
    }

    fn insert_entry(&mut self, mut entry: CodeEntry) -> LinkId {
        let index = self.entries.len();
        let link_id = LinkId(index as u32);
        entry.link = Some(link_id);
        self.entries.push(entry);
        link_id
    }

    fn insert_decl(&mut self, block_id: BlockId, entry: CodeEntry) -> LinkId {
        let link_id = self.insert_entry(entry);
        self.blocks.get_block_mut(block_id).push_decl(link_id);
        link_id
    }

    pub fn push_decl(&mut self, ty: AstType, name: StringKey, span_id: SpanId) -> LinkId {
        let block_id = self.current_block_id();
        let block = self.blocks.get_block(block_id);
        let scope = self.blocks.get_scope(block.scope());
        let entry_block_id = scope.entry_block();

        let entry = CodeEntry::new(
            entry_block_id,
            LCode::Declare,
            ty,
            Some(name),
            span_id,
            VarDefinitionSpace::Default,
        );
        self.switch_blocks(entry_block_id);
        let link_id = self.insert_decl(entry_block_id, entry);
        self.switch_blocks(block_id);
        link_id
    }

    fn _push_entry_normal(&mut self, entry: CodeEntry) -> LinkId {
        let block_id = entry.block_id;
        let code = entry.code.clone();
        let link_id = self.insert_entry(entry);
        let block = self.blocks.get_block_mut(block_id);
        block.push_link(link_id, code.is_term());
        link_id
    }

    pub fn push_entry_with_link(&mut self, mut entry: CodeEntry) -> LinkId {
        let code = entry.code.clone();
        let block_id = entry.block_id;

        let v = match &code {
            LCode::Label => {
                let block = self.blocks.get_block(block_id);
                assert!(block.last().is_none());
                let link_id = self.insert_entry(entry);
                let block = self.blocks.get_block_mut(block_id);
                block.push_label(link_id);
                link_id
            }
            LCode::Arg(_) => {
                let link_id = self.insert_entry(entry);
                self.update_connections(link_id);
                let block = self.blocks.get_block_mut(block_id);
                block.push_arg(link_id);
                link_id
            }
            LCode::Declare | LCode::DeclareFunction(_) => {
                let block = self.blocks.get_block(block_id);
                let scope_id = block.scope();
                let scope = self.blocks.get_scope(scope_id);
                let entry_block_id = scope.entry_block();
                entry.block_id = entry_block_id;
                let link_id = self.insert_decl(entry_block_id, entry);
                link_id
            }
            _ => self._push_entry_normal(entry),
        };
        self.update_connections(v);
        v
    }

    pub(super) fn update_connections(&mut self, link_id: LinkId) {
        let code = self.get_entry(link_id).code.clone();
        match code {
            LCode::Arg(i) => self.scoped_continuations.connect(
                ContinuationFlow::BlockArg(self.current_block_id(), i),
                ContinuationFlow::Variable(link_id),
                FlowEdge::BlockArg,
            ),

            LCode::Branch(_, b1, b2) => {
                self.scoped_continuations.connect(
                    ContinuationFlow::Jump(link_id),
                    ContinuationFlow::Block(b1),
                    FlowEdge::CondThen,
                );
                self.scoped_continuations.connect(
                    ContinuationFlow::Jump(link_id),
                    ContinuationFlow::Block(b2),
                    FlowEdge::CondElse,
                );
            }
            LCode::Jump(b) => {
                self.scoped_continuations.connect(
                    ContinuationFlow::Jump(link_id),
                    ContinuationFlow::Block(b),
                    FlowEdge::JumpLabel,
                );
            }

            LCode::Store(offset_decl, v_expr) => {
                self.scoped_continuations.connect(
                    ContinuationFlow::Variable(v_expr),
                    ContinuationFlow::Variable(offset_decl),
                    FlowEdge::Store,
                );
            }

            LCode::Load(decl_link_id) => {
                self.scoped_continuations.connect(
                    ContinuationFlow::Variable(decl_link_id),
                    ContinuationFlow::Variable(link_id),
                    FlowEdge::LoadBlockArg,
                );
            }

            LCode::Val(Literal::Block(fun_block_id)) => {
                self.scoped_continuations.connect(
                    ContinuationFlow::Block(fun_block_id),
                    ContinuationFlow::Variable(link_id),
                    FlowEdge::BlockRef,
                );
            }

            _ => (),
        }
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

    pub fn push_sequence(
        &mut self,
        seq: Vec<AstNode>,
        span_id: SpanId,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        let block = self.blocks.get_block(self.current_block_id());
        let start_stack = self.blocks.walk_scopes(block.scope());

        for (_i, expr) in seq.into_iter().enumerate() {
            let _ = self.push_node(expr, b)?;
        }

        // ensure that we close any blocks that were opened
        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        let scope_id = block.scope();
        let end_stack = self.blocks.walk_scopes(scope_id);
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

    pub fn push_return(&mut self, values: ArgVec, span_id: SpanId, b: &mut NB) -> LinkId {
        let _ = self.push_call_values(&values, b);

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
        entry.is_load_required()
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
        b: &mut NB,
    ) -> Vec<LinkId> {
        let mut updated_values = vec![];
        let block_id = self.current_block_id();
        let block = self.blocks.get_block(block_id);
        let scope_id = block.scope();
        for (maybe_key, v, ty, span_id) in values {
            let mut v = *v;
            let entry = self.get_entry(v);
            let v_block_id = entry.block_id;
            let v_block = self.blocks.get_block(v_block_id);
            let v_scope_id = v_block.scope();
            let v_scope = self.blocks.get_scope(v_scope_id);
            let v_entry_block_id = v_scope.entry_block();
            let in_entry = v_entry_block_id == v_block_id;
            let in_block = v_block_id == block_id;

            let is_decl = if let LCode::Declare = entry.code {
                true
            } else {
                false
            };

            self.blocks
                .find_nearest_scope(v_scope_id, &[ScopeType::Function, ScopeType::Block]);
            assert!(self.blocks.is_in_scope(scope_id, v_scope_id));

            if !in_entry && !in_block && !is_decl {
                // checking if it's in entry is easier than checking if the block is dominant
                // This could be make more efficient.
                // get a link the value declaration in the scope entry
                println!(
                    "@{}: {}{}=>{}{}, {}",
                    v, block_id, scope_id, v_block_id, v_scope_id, ty
                );
                let key = b.labels.fresh_key("r");
                // create space on the stack in the entry block
                let decl_link_id = self.push_decl(ty.clone(), key, *span_id);
                let entry = self.get_entry_mut(v);
                entry.mem = VarDefinitionSpace::Stack(decl_link_id);
                v = decl_link_id;
            }

            let out = (*maybe_key, v, ty, *span_id);

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
        target_block_id: BlockId,
        jump_args: ArgVec,
        span_id: SpanId,
        b: &mut NB,
    ) -> LinkId {
        // handle leaving scope here?
        // We need to unwind the target, as well as any CPS parameters we send
        // We unwind at the caller.

        // TODO: unwind when leaving this scope
        //let unwind_next = self.push_unwind(v_next, span_id, b);
        //let unwind_next = v_next;

        let current_block_id = self.current_block_id();
        let current_scope_id = self.blocks.get_block(current_block_id).scope();
        let target_scope_id = self.blocks.get_block(target_block_id).scope();
        assert_ne!(current_block_id, target_block_id);
        println!(
            "jump: {}{}=>{}{}",
            current_block_id, current_scope_id, target_block_id, target_scope_id
        );

        // Construct the argument type
        let arg_ty = AstType::Struct(
            jump_args
                .iter()
                .map(|j| (j.0, j.2.clone()))
                .collect::<Vec<_>>(),
        );

        let var_link_ids = jump_args.iter().map(|j| j.1).collect::<Vec<_>>();

        let _ = self.push_call_values(
            &jump_args
                .into_iter()
                .map(|(key, v, ty, span_id)| (key, v, ty, span_id))
                .collect::<Vec<_>>(),
            b,
        );

        self.blocks
            .block_succ(self.current_block_id(), target_block_id, Successor::Jump);
        self.blocks.block_succ(
            self.current_block_id(),
            target_block_id,
            Successor::BlockScope,
        );

        let jump_link_id = self.push_code(
            LCode::Jump(target_block_id.into()),
            AstFuncType::new(arg_ty, ReturnType::Single(AstType::Unit)).into(),
            None,
            span_id,
            VarDefinitionSpace::Reg,
        );

        // it would be better to move this to be close to the other connections
        // but it's more convenient to have it here
        // We could read in the call values, but how that works is likely to change
        // so we are keeping these here.
        for (i, var_link_id) in var_link_ids.iter().enumerate() {
            self.scoped_continuations.connect(
                ContinuationFlow::Variable(*var_link_id),
                ContinuationFlow::JumpArg(jump_link_id, i as u8),
                FlowEdge::VarJumpArgInline,
            );
            self.scoped_continuations.connect(
                ContinuationFlow::JumpArg(jump_link_id, i as u8),
                ContinuationFlow::BlockArg(target_block_id, i as u8),
                FlowEdge::JumpArgInline,
            );
        }

        jump_link_id
    }

    pub fn resolve_value(&self, link_id: LinkId) -> LinkId {
        let mut current = link_id;
        loop {
            let entry = self.get_entry(current);

            if let LCode::CallValue(base) = &entry.code {
                match base {
                    CodeOffset::Link(next_link_id) => {
                        current = *next_link_id;
                        continue;
                    }
                    _ => unimplemented!(),
                }
            }

            break;
        }
        current
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
        self.push_entry_with_link(entry)
    }

    pub fn push_function_call(
        &mut self,
        v_fun: LinkId,
        values: ArgVec,
        ret_ty: ReturnType,
        span_id: SpanId,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        self.push_call_values(&values, b);

        if let ReturnType::Single(ty) = &ret_ty {
            let link_id = self.push_code(
                LCode::Call(v_fun.into()),
                ty.clone(),
                None,
                span_id,
                VarDefinitionSpace::Default,
            );
            Ok(FlattenResult::link(link_id))
        } else {
            unimplemented!()
        }
    }

    pub fn push_builtin_call(
        &mut self,
        def: &Lambda,
        id: BuiltinId,
        args: Vec<Argument>,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        let def_span_id = b.spans.get_span_unknown();
        let (args, func_type) =
            Self::calculate_function_arguments(&def, &args, &[], def_span_id, call_span_id, b)?;
        let call_values = self.push_call_arguments(args, call_span_id, b)?;
        self.push_call_values(&call_values, b);

        let call_types = call_values.iter().map(|v| v.2.clone()).collect::<Vec<_>>();

        // unify args
        // TODO: return type should also be unified
        b.unify(
            &func_type.args,
            call_span_id,
            &AstType::build_struct(call_types),
            call_span_id,
        );

        let link_id = self.push_code(
            LCode::Builtin(id),
            func_type.into(),
            None,
            call_span_id,
            VarDefinitionSpace::Default,
        );
        Ok(FlattenResult::link(link_id))
    }

    fn push_start_block_args(&mut self, block_ty: AstFuncType, span_id: SpanId) -> ArgVec {
        assert!(block_ty.args.is_composite());

        let block_id = self.current_block_id();
        let scope_id = self.blocks.get_block(block_id).scope();

        let mut v_args = vec![];
        for (i, (name, ty)) in block_ty.args.fields().iter().enumerate() {
            let link_id = self.push_code(
                LCode::Arg(i as u8),
                ty.clone(),
                *name,
                span_id,
                VarDefinitionSpace::Arg,
            );
            v_args.push((*name, link_id, ty.clone(), span_id));
            if let Some(name) = name {
                self.blocks.scope_define(scope_id, *name, link_id.into());
            }
        }
        v_args
    }

    pub(super) fn push_start_block_static(
        &mut self,
        block_ty: AstFuncType,
        name: Option<StringKey>,
        span_id: SpanId,
    ) -> (LinkId, ArgVec) {
        self.push_start_block_mem(block_ty, name, span_id, VarDefinitionSpace::Static)
    }

    pub(super) fn push_start_block(
        &mut self,
        block_ty: AstFuncType,
        name: Option<StringKey>,
        span_id: SpanId,
    ) -> (LinkId, ArgVec) {
        self.push_start_block_mem(block_ty, name, span_id, VarDefinitionSpace::Default)
    }

    pub(super) fn push_start_block_mem(
        &mut self,
        block_ty: AstFuncType,
        name: Option<StringKey>,
        span_id: SpanId,
        mem: VarDefinitionSpace,
    ) -> (LinkId, ArgVec) {
        let block_link_id =
            self.push_code(LCode::Label, block_ty.clone().into(), name, span_id, mem);
        let v_args = self.push_start_block_args(block_ty, span_id);
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
    ) -> AbstractionId {
        let abstraction_id = self.abstractions.add(*name, def.clone(), span_id);
        let block = self.blocks.get_block(block_id);
        self.blocks
            .define_lambda(block.scope(), name.into(), abstraction_id);
        abstraction_id
    }

    pub fn push_close_block(&mut self, span_id: SpanId, b: &mut NB) -> Result<FlattenResult> {
        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        let scope_id = block.scope();

        if let Some(scope) = self.blocks.try_loop_scope(scope_id) {
            let start_block = scope.start_block();
            let next_block = scope.next_block();
            let link_id = self.maybe_terminate_block(start_block, span_id, b);
            self.switch_blocks(next_block);
            Ok(FlattenResult::link(link_id))
        } else {
            unimplemented!();
        }
    }

    pub fn dump_position(&self) {
        let block_id = self.current_block_id();
        let block = self.blocks.get_block(block_id);
        let scope_id = block.scope();
        println!("pos: {}{}", scope_id, block_id);
    }

    pub(super) fn resolve_return_type(
        &self,
        fun_block_id: BlockId,
        def_func_ty: AstType,
        span_id: SpanId,
        b: &mut NB,
    ) -> AstType {
        let func_ret_ty = if let AstType::Func(f) = def_func_ty.clone() {
            if let ReturnType::Single(ret) = f.ret {
                ret.clone()
            } else {
                unreachable!()
            }
        } else {
            unreachable!()
        };

        // write out return block
        let fun_scope = self.blocks.get_function_scope(fun_block_id);
        let num_ret_args = fun_scope.num_ret_args();
        let ret_types = fun_scope.ret_types();

        if num_ret_args.len() > 1 {
            b.push_error(
                &format!("Return type mismatch: {:?}", num_ret_args),
                span_id,
            );
        }

        let num_ret_args = num_ret_args.iter().next().unwrap_or(&0).clone();

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
        for ty in ret_types.iter() {
            if b.types.u.unify(ty, &func_ret_ty).is_err() {
                b.push_error(
                    &format!("7-Type Mismatch: LHS: {}, RHS: {}", ty, &func_ret_ty),
                    span_id,
                );
            }
        }
        // resolve the return types
        let ret_types = ret_types
            .iter()
            .map(|t| b.types.u.resolve(&t).unwrap_or(t.clone()))
            .collect::<HashSet<_>>();

        let single_ty = ret_types.iter().next().unwrap_or(&AstType::Unit).clone();

        let ret_arg_type = if arity == 0 || AstType::Unit == single_ty {
            AstType::Struct(vec![])
        } else {
            assert!(ret_types.len() == 1);
            AstType::Struct(vec![(None, single_ty.clone())])
        };

        let resolved_ret_ty = ret_arg_type.clone();

        if b.types.u.unify(&func_ret_ty, &single_ty).is_err() {
            b.push_error(
                &format!(
                    "8-Type Mismatch: LHS: {}, RHS: {}",
                    &resolved_ret_ty, &func_ret_ty
                ),
                span_id,
            );
        }
        resolved_ret_ty
    }

    pub(super) fn refresh_func_type(&self, def_func_type: &AstFuncType, b: &mut NB) -> AstFuncType {
        // refresh variables
        match &def_func_type.ret {
            ReturnType::Single(ret_ty) => AstFuncType::new(
                b.types.refresh(def_func_type.args.clone()),
                ReturnType::Single(b.types.refresh(ret_ty.clone())),
            ),
            ReturnType::Never => AstFuncType::new(
                b.types.refresh(def_func_type.args.clone()),
                ReturnType::Never,
            ),
            _ => unreachable!(),
        }
    }

    pub fn remove_placeholder_terminal(&mut self, goto_block_id: BlockId) {
        let block = self.blocks.get_block(goto_block_id);
        let last_link_id = block.last().unwrap();
        let entry = self.get_entry(last_link_id);
        if let LCode::PlaceholderTerminal = entry.code {
            let block = self.blocks.get_block_mut(goto_block_id);
            let _ = block.pop_terminal();
        }
    }

    pub fn replace_placeholder_terminal(
        &mut self,
        goto_block_id: BlockId,
        arg_link_id: LinkId,
        mut target_block_ids: Vec<BlockId>,
        b: &mut NB,
    ) -> LinkId {
        let block = self.blocks.get_block(goto_block_id);
        println!("replace: {}, {}", goto_block_id, block.is_dead());
        let last_link_id = block.last().unwrap();

        for block_id in &target_block_ids {
            self.blocks
                .block_succ(self.current_block_id(), *block_id, Successor::Jump);
            self.blocks
                .block_succ(self.current_block_id(), *block_id, Successor::BlockScope);
        }

        let entry = self.get_entry(last_link_id);

        let code = if let LCode::PlaceholderTerminal = entry.code {
            if target_block_ids.len() == 1 {
                let block_id = target_block_ids.last().unwrap();
                Some(LCode::Jump(*block_id))
            } else if target_block_ids.len() > 1 {
                target_block_ids.sort();
                let mut m = HashSet::new();
                for block_id in target_block_ids.iter() {
                    m.insert(*block_id);
                }

                // connects here aren't actually used to calculate the flows
                // This function is called when we have calculated the static flow and we update
                // the graph.

                Some(LCode::Switch(arg_link_id, m))
            } else {
                b.push_warning("Missing Targets", entry.span_id);
                None
                //unreachable!();
            }
        } else {
            unreachable!();
        };
        if let Some(code) = code {
            let entry = self.get_entry_mut(last_link_id);
            entry.code = code;
        }

        last_link_id
    }

    pub fn push_node(&mut self, node: AstNode, b: &mut NB) -> Result<FlattenResult> {
        // we can only push into an open block
        self.ensure_open(node.span_id, b);

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
                        // save template for later use
                        if def.body.is_some() {
                            self.save_ast_template(current_block_id, &name, &def, span_id);
                        }

                        // TODO: The function doesn't actually exist until we call it
                        // So we have no way of returning a reference to it yet
                        // We only add it to the graph when it's monomorphized
                        // We could return the abstraction_id, and allow the program to
                        // perform the monomorphization itself.
                        if let Some(_body) = &def.body {
                            Ok(FlattenResult::statement())
                        } else {
                            Ok(FlattenResult::statement())
                        }
                    }

                    Ast::Literal(lit) => {
                        let scope_id = block.scope();
                        let scope = self.blocks.get_scope(scope_id);

                        let static_block_id = self.static_block_id();

                        // Generate the global name, unique if it's local
                        let global_name = if scope.is_static() {
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

                        self.blocks.scope_define(scope_id, name, link_id.into());

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

                        let def = bi.get_lambda(b);
                        self.switch_blocks(current_block_id);
                        self.push_builtin_call(&def, id, args, span_id, b)
                    }
                }
            }

            Ast::Return(maybe_expr) => {
                let block = self.blocks.get_block(current_block_id);
                let fun_scope_id = self.blocks.get_function_scope_id(block.scope());
                let fun_block_id = self.blocks.get_entry_block(fun_scope_id);

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

                let fun_scope = self.blocks.get_scope_mut(fun_scope_id);
                let jump_types = jump_args
                    .iter()
                    .map(|(_, _, ty, _)| ty.clone())
                    .collect::<Vec<_>>();
                fun_scope.insert_ret_arg(jump_types);

                let scope = self.blocks.get_function_scope(fun_block_id);
                let ret_block_id = scope.return_block();
                self.push_jump(ret_block_id, jump_args, span_id, b);
                Ok(FlattenResult::statement())
            }

            Ast::Literal(lit) => {
                // literal is expression, non-terminal
                let ty: AstType = match &lit {
                    Literal::Block(_block_id) => b.types.fresh_unknown(),
                    Literal::Link(_link_id) => b.types.fresh_unknown(),
                    _ => lit.clone().into(),
                };
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

                let _ = self.push_call_values(
                    &[
                        (None, vx, rx_ty.clone(), node.span_id),
                        (None, vy, ry_ty.clone(), node.span_id),
                    ],
                    b,
                );

                let ret_ty = op.node.get_type(&rx_ty, &ry_ty);
                let link_id = self.push_code(
                    LCode::Op2(op.node),
                    ret_ty.clone(),
                    None,
                    op.span_id,
                    VarDefinitionSpace::Default,
                );

                Ok(FlattenResult::link(link_id))
            }

            Ast::Identifier(key) => {
                // identifier is expression, non-terminal
                let scope_id = block.scope();

                // resolve identifier lexically
                if let Some(def_link_id) = self.blocks.resolve_name(current_block_id, key) {
                    let link_id = def_link_id;
                    return Ok(FlattenResult::link(link_id));
                }

                // we are resolving the abstraction lexically here, but it could also be defined
                // later.  TODO: if we don't find it, it might be defined later, so we should defer
                // and throw the error later if it's not found.
                if let Some(abstraction_id) = self.blocks.resolve_template(scope_id, key.into()) {
                    let code = LCode::Val(Literal::Abstraction(abstraction_id));
                    let ty = b.types.fresh_unknown();
                    let link_id = self.push_code(
                        code,
                        ty,
                        Some(key),
                        node.span_id,
                        VarDefinitionSpace::Default,
                    );
                    self.resolve_open_abstractions(link_id, abstraction_id, b)?;
                    return Ok(FlattenResult::link(link_id));
                }

                /*
                 * The ident may not yet be defined if it's a label.
                 * If we don't find it immediately in lexical scope, then defer.
                 */
                let code = LCode::PlaceholderCodeReference;
                let ty = b.types.fresh_unknown();
                let link_id = self.push_code(
                    code,
                    ty,
                    Some(key),
                    node.span_id,
                    VarDefinitionSpace::Default,
                );
                self.open_identifiers.push(link_id);
                Ok(FlattenResult::link(link_id))
            }

            Ast::Assign(target, expr) => {
                // assign is expression, non-terminal
                let name = match target {
                    AssignTarget::Identifier(name) | AssignTarget::Alloca(name) => name,
                };

                // push the definition into the lambda list
                if let Ast::Lambda(def) = expr.node {
                    self.switch_blocks(current_block_id);

                    // save the template
                    let def_span_id = expr.span_id;
                    let _ = self.save_ast_template(current_block_id, &name, &def, def_span_id);
                    self.switch_blocks(current_block_id);
                    return Ok(FlattenResult::statement());
                }

                self.switch_blocks(current_block_id);
                let r = self.push_node(*expr, b)?;
                let v_expr = r.link_id.unwrap();
                let expr_entry = self.get_entry(v_expr);
                let expr_ty = expr_entry.ty.clone();
                let expr_span_id = expr_entry.span_id;

                let block_id = self.current_block_id();
                let block = self.blocks.get_block(block_id);
                let scope_id = block.scope();

                let offset_decl =
                    if let Some(v_decl) = self.blocks.resolve_name_in_scope(scope_id, name) {
                        // already declared
                        let decl_entry = self.get_entry(v_decl);
                        b.unify(&decl_entry.ty, decl_entry.span_id, &expr_ty, expr_span_id);
                        v_decl
                    } else {
                        // need to declare it
                        let block = self.blocks.get_block(self.current_block_id());
                        let scope_id = block.scope();

                        let link_id = self.push_code(
                            LCode::Declare,
                            expr_ty.clone(),
                            Some(name),
                            node.span_id,
                            VarDefinitionSpace::Default,
                        );
                        self.blocks.scope_define(scope_id, name, link_id);
                        link_id
                    };

                // explicit store for assign
                self.push_code(
                    LCode::Store(offset_decl, v_expr),
                    AstType::Unit,
                    None,
                    node.span_id,
                    VarDefinitionSpace::Default,
                );
                Ok(FlattenResult::link(offset_decl))
            }

            Ast::Import(module_key, args) => {
                let module_name = b.labels.r(module_key.into());
                let scope_id = block.scope();

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
                            self.blocks.scope_define(scope_id, *local_key, link_id);
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
                        if let Some((scope_id, abstraction_id)) =
                            self.blocks.resolve_lambda(current_block_id, *ident)
                        {
                            self.push_call(scope_id, abstraction_id, span_id, args, b)
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

                self.push_call_values(&[(None, link_id, ty.clone(), span_id)], b);

                let link_id = self.push_code(
                    LCode::Op1(op),
                    ty.clone(),
                    None,
                    node.span_id,
                    VarDefinitionSpace::Reg,
                );
                Ok(FlattenResult::link(link_id))
            }

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
                let current_block_id = self.current_block_id();
                let block = self.blocks.get_block(current_block_id);
                assert!(!block.is_term());

                let parent_scope_id = block.scope();

                // Start Next Block
                let v_next =
                    self.blocks
                        .new_block(current_block_id, parent_scope_id, Successor::BlockScope);
                self.switch_blocks(v_next);
                self.push_start_block(
                    AstFuncType::new_void_void(),
                    Some(b.labels.fresh_key("cond_next")),
                    span_id,
                );
                self.switch_blocks(current_block_id);

                // THEN Block
                let (then_block_id, _) = self.blocks.new_scope_and_block(
                    ScopeType::Block,
                    ScopeState::block(),
                    current_block_id,
                    Successor::BlockScope,
                );
                self.blocks.control_flow(current_block_id, &[then_block_id]);

                let then_span_id = then_expr.span_id;

                let branch_block_type = AstFuncType {
                    args: AstType::Struct(vec![]).into(),
                    ret: ReturnType::Single(AstType::Unit).into(),
                };

                let name = b.labels.fresh_key("then");
                self.switch_blocks(then_block_id);
                self.push_start_block(branch_block_type.clone().into(), Some(name), then_span_id);
                self.switch_blocks(then_block_id);
                let _ = self.push_node(NB::ensure_seq(*then_expr), b)?;
                self.maybe_terminate_block(v_next, span_id, b);

                // ELSE Block
                let else_block_id = if let Some(else_expr) = maybe_else_expr {
                    let (else_block_id, _) = self.blocks.new_scope_and_block(
                        ScopeType::Block,
                        ScopeState::block(),
                        current_block_id,
                        Successor::BlockScope,
                    );
                    self.blocks.control_flow(current_block_id, &[else_block_id]);

                    let else_span_id = else_expr.span_id;
                    let name = b.labels.fresh_key("else");

                    self.switch_blocks(else_block_id);
                    self.push_start_block(branch_block_type.into(), Some(name), else_span_id);

                    self.switch_blocks(else_block_id);
                    let _ = self.push_node(NB::ensure_seq(*else_expr), b)?;
                    // TODO: unwind when leaving this scope
                    self.maybe_terminate_block(v_next, span_id, b);
                    else_block_id
                } else {
                    self.blocks
                        .block_succ(current_block_id, v_next, Successor::BlockScope);
                    self.blocks
                        .block_succ(current_block_id, v_next, Successor::Jump);
                    v_next
                };

                // condition
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
                let (_variant_id, block_id) = match &expr.node {
                    Ast::Identifier(key) => {
                        let key = *key;
                        let ty = AstType::func(vec![], AstType::Unit);
                        let scope_id = block.scope();
                        if let Some((variant_id, _resolve_type, link_id, _scope_id)) =
                            self.resolve_function_name(scope_id, &key, &ty, b)
                        {
                            let entry = self.get_entry(link_id);
                            (variant_id, entry.block_id)
                        } else {
                            let link_id = self.push_node(*expr, b)?.link_id.unwrap();
                            let entry = self.get_entry(link_id);
                            match &entry.code {
                                LCode::Label => {
                                    let variant_id =
                                        self.variants.block_lookup.get(&entry.block_id).unwrap();
                                    let _v = self.variants.get_by_block(entry.block_id).unwrap();
                                    (*variant_id, entry.block_id)
                                }
                                LCode::PlaceholderCodeReference => {
                                    let s_name = b.labels.r(key.into());
                                    unimplemented!("{:?}", (s_name, entry));
                                }
                                _ => {
                                    unimplemented!("{:?}", entry);
                                }
                            }
                        }
                    }
                    _ => unimplemented!("{:?}", expr),
                };
                let ty = AstType::JumpTarget;
                let code = LCode::Val(Literal::Block(block_id));
                let link_id = self.push_code(code, ty, None, span_id, VarDefinitionSpace::Default);
                Ok(FlattenResult::link(link_id))
            }

            Ast::ControlFlowMarker(ControlFlowMarker::BlockStart(name, args)) => {
                // LABEL
                let name = name.unwrap();
                // push a new block.  But check to make sure the previous block was closed
                let scope_id = block.scope();

                // check for duplicates
                if let Some(block_id) = self.blocks.resolve_label(scope_id, name.into()) {
                    unimplemented!("duplicate label: {}", block_id);
                }

                // create a new block
                assert_eq!(0, args.len());
                let new_block_id =
                    self.blocks
                        .new_block(self.current_block_id(), scope_id, Successor::BlockScope);
                self.blocks.define_label(scope_id, new_block_id, name);

                self.switch_blocks(current_block_id);

                // start a new block.  If the last block isn't terminated, then we create a new
                // block and jump to it.
                // TODO: We can also check if the previous block was empty and compatible, and reuse it.
                let block = self.blocks.get_block(current_block_id);
                if let Some(last_link_id) = block.last() {
                    let entry = self.get_entry(last_link_id);
                    if !entry.code.is_term() {
                        assert_eq!(args.len(), 0);
                        let _link_id = self.push_jump(new_block_id, vec![], span_id, b);
                    }
                }

                let block = self.blocks.get_block(current_block_id);
                // this is a new block, check to make sure the last block terminated
                // if not, we close it out with a jump to this block
                if let Some(last) = block.last() {
                    let entry = self.get_entry(last);
                    if !entry.code.is_term() {
                        let _ = self.push_jump(new_block_id.into(), vec![], span_id, b);
                    }
                }

                let scope = self.blocks.get_scope(scope_id);

                // ensure this block is not an entry block, this should never happen.
                assert!(scope.entry_block() != new_block_id);

                let arg_ty = AstType::Struct(
                    args.iter()
                        .map(|p| {
                            let ty = b.types.r(p.ty);
                            (Some(p.name), ty.clone())
                        })
                        .collect::<Vec<_>>(),
                );

                self.switch_blocks(new_block_id);
                let (link_id, _) = self.push_start_block(
                    AstFuncType {
                        args: arg_ty.clone().into(),
                        ret: ReturnType::Single(AstType::Unit).into(),
                    }
                    .into(),
                    Some(name),
                    span_id,
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

                // Condition
                self.switch_blocks(current_block_id);
                let rc = self.push_node(*c, b)?;
                let current_block_id = self.current_block_id();

                let branch_block_type = AstFuncType {
                    args: AstType::Struct(vec![]).into(),
                    ret: ReturnType::Single(AstType::Unit).into(),
                };

                // THEN
                let (then_block_id, _) = self.blocks.new_scope_and_block(
                    ScopeType::Region,
                    ScopeState::region(),
                    current_block_id,
                    Successor::Operation,
                );
                self.blocks.control_flow(current_block_id, &[then_block_id]);
                let then_span_id = x.span_id;
                let then_ast = AstNode::make_yield(*x);

                let name = b.labels.fresh_key("t_then");

                self.switch_blocks(then_block_id);
                self.push_start_block(branch_block_type.clone().into(), Some(name), then_span_id);

                self.switch_blocks(then_block_id);
                let r = self.push_node(then_ast, b)?;
                let then_link_id = r.link_id.unwrap();
                let then_ty = self.get_type(then_link_id).clone();

                // ELSE
                let else_span_id = y.span_id;
                let (else_block_id, _) = self.blocks.new_scope_and_block(
                    ScopeType::Region,
                    ScopeState::region(),
                    current_block_id,
                    Successor::Operation,
                );
                self.blocks.control_flow(current_block_id, &[else_block_id]);
                let else_ast = AstNode::make_yield(*y);

                self.switch_blocks(else_block_id);
                self.push_start_block(branch_block_type.into(), Some(name), else_span_id);

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
                Ok(FlattenResult::link(v))
            }

            Ast::Yield(maybe_expr) => {
                // yield is terminal
                let mut ty = AstType::Unit;
                if let Some(expr) = maybe_expr {
                    self.switch_blocks(current_block_id);
                    let r = self.push_node(*expr, b)?;
                    if let Some(v) = r.link_id {
                        ty = self.get_type(v).clone();
                        // push single arg
                        self.push_call_values(&[(None, v.into(), ty.clone(), node.span_id)], b);
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

            Ast::ControlFlowMarker(ControlFlowMarker::GotoChain(args)) => {
                let argvec = self.push_call_arguments(args, span_id, b)?;
                let mut argvec = VecDeque::from(argvec);
                let mut acc = VecDeque::new();
                let block = self.blocks.get_block(current_block_id);
                let parent_scope_id = block.scope();
                let current_block_id = self.current_block_id();
                let mut out_link_id = None;
                if argvec.is_empty() {
                    unreachable!();
                }

                loop {
                    let (_key, link_id, ty, span_id) = argvec.pop_back().unwrap();
                    let entry = self.get_entry(link_id);
                    let code = entry.code.clone();
                    match &code {
                        LCode::Val(Literal::Block(block_id)) => {
                            let block_id = *block_id;
                            let arg_types = ty.fields();
                            // lengths should match
                            assert!(arg_types.len() == acc.len());

                            let mut acc_types = vec![];
                            for ((_, ty1), (_, _, ty2, span_id2)) in
                                arg_types.iter().zip(acc.iter())
                            {
                                b.unify(&ty1, span_id, &ty2, *span_id2);
                                acc_types.push((None, ty2.clone()));
                            }

                            let label = b.labels.fresh_key("chain");
                            let v_next = self.blocks.new_block(
                                current_block_id,
                                parent_scope_id,
                                Successor::BlockScope,
                            );
                            self.switch_blocks(v_next);
                            self.push_start_block(
                                AstFuncType::new(
                                    AstType::Struct(acc_types).into(),
                                    ReturnType::Single(AstType::Unit),
                                ),
                                Some(label),
                                span_id,
                            );
                            let jump_args = acc.drain(..).collect::<Vec<_>>();
                            let link_id =
                                self.push_jump(block_id.into(), jump_args, node.span_id, b);
                            acc.clear();
                            out_link_id = Some(link_id);
                        }
                        LCode::PlaceholderCodeReference => {
                            acc.push_front((None, link_id, ty, span_id));
                        }
                        _ => {
                            b.push_error(&format!("Invalid goto: {:?}", code), span_id);
                            return Err(Error::new(BlockifyError::Invalid));
                        }
                    }

                    if argvec.is_empty() {
                        break;
                    }
                }
                self.switch_blocks(current_block_id);
                Ok(FlattenResult::link(out_link_id.unwrap()))
            }

            Ast::ControlFlowMarker(ControlFlowMarker::BlockEnd) | Ast::CloseBlock => {
                self.push_close_block(span_id, b)
            }

            Ast::ControlFlowMarker(ControlFlowMarker::LoopStart(maybe_key)) => {
                let block = self.blocks.get_block(current_block_id);
                let parent_scope_id = block.scope();

                let (loop_block_id, loop_scope_id) = self.blocks.new_scope_and_block(
                    ScopeType::Region,
                    ScopeState::region(),
                    current_block_id,
                    Successor::BlockScope,
                );
                self.blocks.control_flow(current_block_id, &[loop_block_id]);

                let v_next =
                    self.blocks
                        .new_block(current_block_id, parent_scope_id, Successor::BlockScope);
                self.switch_blocks(v_next);
                self.push_start_block(
                    AstFuncType::new_void_void(),
                    Some(b.labels.fresh_key("postloop")),
                    span_id,
                );
                self.switch_blocks(current_block_id);

                self.blocks.update_loop_blocks(
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
                    AstFuncType {
                        args: AstType::Struct(vec![]).into(),
                        ret: ReturnType::Single(AstType::Unit).into(),
                    }
                    .into(),
                    Some(key),
                    span_id,
                );

                self.switch_blocks(current_block_id);
                let link_id = self.push_jump(loop_block_id.into(), vec![], node.span_id, b);

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
                let scope_id = block.scope();

                // loop up loop blocks by name
                if let Some(loop_scope) = self.blocks.get_loop_scope(scope_id, maybe_key) {
                    self.switch_blocks(current_block_id);
                    let link_id =
                        self.push_jump(loop_scope.start_block.into(), vec![], node.span_id, b);
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
                let scope_id = block.scope();

                // args not implemented yet
                assert_eq!(args.len(), 0);
                // loop up loop blocks by name
                if let Some(loop_scope) = self.blocks.get_loop_scope(scope_id, maybe_name) {
                    self.switch_blocks(current_block_id);
                    let link_id =
                        self.push_jump(loop_scope.start_block.into(), vec![], node.span_id, b);
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
                let scope_id = block.scope();
                // loop up loop blocks by name
                if let Some(loop_scope) = self.blocks.get_loop_scope(scope_id, maybe_key) {
                    self.switch_blocks(current_block_id);
                    let _link_id =
                        self.push_jump(loop_scope.next_block.into(), vec![], node.span_id, b);

                    let v_next =
                        self.blocks
                            .new_block(current_block_id, scope_id, Successor::BlockScope);
                    self.switch_blocks(v_next);
                    let (link_id, _) = self.push_start_block(
                        AstFuncType::new_void_void(),
                        Some(b.labels.fresh_key("postloopbreak")),
                        span_id,
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
                let scope_id = block.scope();

                // args not implemented yet
                assert_eq!(args.len(), 0);
                // loop up loop blocks by name
                if let Some(loop_scope) = self.blocks.get_loop_scope(scope_id, maybe_name) {
                    self.switch_blocks(current_block_id);
                    let link_id =
                        self.push_jump(loop_scope.next_block.into(), vec![], node.span_id, b);
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
                    types.push(ty.clone());
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

            Ast::Defer(expr) => {
                // defer is terminal
                let r = self.push_node(*expr, b)?;
                let func_link_id = r.link_id.unwrap();
                // expression must be a function with no arguments.  We bake it here.
                let ty = self.get_type(func_link_id).clone();
                println!("ty: {:?}", ty);

                let entry = self.get_entry(func_link_id);
                println!("entry: {:?}", entry);

                let func_block_id = match &entry.code {
                    LCode::Val(Literal::Block(block_id)) => *block_id,
                    _ => {
                        b.push_error(
                            &format!("Defer must be a function with no arguments"),
                            node.span_id,
                        );
                        return Err(Error::new(BlockifyError::Invalid));
                    }
                };

                let current_block_id = self.current_block_id();
                let block = self.blocks.get_block(current_block_id);
                let scope_id = block.scope();
                let scope = self.blocks.get_scope_mut(scope_id);
                scope.prepend_deferral(func_block_id);

                let unwind_block_id = self.gen_unwind_cps(scope_id, span_id, b);

                let ty = AstType::Unit;

                let code = LCode::Call(func_link_id.into());
                let call_link_id = self.insert_entry(CodeEntry::new(
                    unwind_block_id,
                    code,
                    ty,
                    None,
                    span_id,
                    VarDefinitionSpace::Reg,
                ));

                let unwind_block = self.blocks.get_block_mut(unwind_block_id);
                unwind_block.prepend_link(call_link_id);

                Ok(FlattenResult::statement())
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

    pub(super) fn ensure_open(&mut self, span_id: SpanId, b: &mut NB) {
        // we we want to add a node, and the current block is terminated
        // we create a new block for the dead code that follows.
        let block = self.blocks.get_block(self.current_block_id());
        let scope_id = block.scope();
        if block.is_term() {
            let new_block_id =
                self.blocks
                    .new_block(self.current_block_id(), scope_id, Successor::BlockScope);
            let name = b.labels.fresh_key("dead");

            self.switch_blocks(new_block_id);
            self.push_start_block(
                AstFuncType::new(AstType::Struct(vec![]), ReturnType::Single(AstType::Unit)).into(),
                Some(name),
                span_id,
            );
        }
    }

    pub(super) fn maybe_terminate_block(
        &mut self,
        v_next: BlockId,
        span_id: SpanId,
        b: &mut NB,
    ) -> LinkId {
        // is the block isn't terminated, terminate it with a jump to another block
        let block = self.blocks.get_block(self.current_block_id());
        let mut link_id = block.last().unwrap().clone();
        let entry = self.get_entry(link_id);
        if !entry.code.is_term() {
            link_id = self.push_jump(v_next, vec![], span_id, b);
        }
        link_id
    }
}
