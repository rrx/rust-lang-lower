use super::resolve_attribute;
use anyhow::Result;
use compile_core::{
    AbstractionId, Argument, AssignTarget, Ast, AstFuncType, AstNode, AstType, BuiltinId,
    ControlFlowMarker, LinkOptions, Literal, ReturnType, SpanId, StringKey,
};

use std::collections::{HashMap, HashSet, VecDeque};

use std::convert::Into;

use crate::{
    BlockGraph, BlockGraphStateOpen, BlockId, BlockifyError, Builtin, CodeEntry, CodeOffset,
    ContinuationFlow, DeferredGotoList, FlowEdge, LCode, LinkId, NodeBuilder as NB, SafeBlock,
    SafeBlockClosed, SafeBlockEmpty, SafeBlockOpen, SafeBlockState, SafeBlockUnknown, ScopeId,
    ScopeState, ScopeType, ScopedContinuations, Successor, ValueId, Values, VarDefinitionSpace,
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

#[derive(Debug, Clone, Copy)]
pub enum PushContext {
    Function,
    Return,
    BlockEnd,
    Module,
    Default,
    SeqLast,
    SeqFirst,
    Seq,
    CondThen,
    CondElse,
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
    pub values: Values,
}
impl FlattenState for Module {}

pub struct FlattenInner {
    pub(super) link: LinkOptions,
    pub(super) blocks: BlockGraph<BlockGraphStateOpen>,
    pub(super) open_identifiers: Vec<LinkId>,
    pub(super) scoped_continuations: ScopedContinuations,
    pub(super) deferred_goto: DeferredGotoList,
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

        if let Ast::Module(key, body) = node.node {
            let blocks = BlockGraph::new(key);
            let inner = FlattenInner {
                blocks,
                link: LinkOptions::new(),
                open_identifiers: vec![],
                scoped_continuations: ScopedContinuations::new(),
                deferred_goto: DeferredGotoList::new(),
            };

            let mut f = Self {
                inner: inner.into(),
                state: Start {},
            };

            for bi in &[Builtin::Print, Builtin::Assert, Builtin::Import] {
                let a = bi.make_abstraction(b);
                let id = f.blocks.abstractions.insert(a);
                b.builtins.add_abstraction(*bi, id);
            }

            let static_block_id = f.blocks.static_block_id();
            let unk = f.blocks.safe_block_unknown(static_block_id);
            let empty = f.blocks.safe_block_try_empty(&unk).unwrap();
            // start module block
            f.push_start_block_static(
                empty,
                AstFuncType::new_void_void().into(),
                Some(key),
                node.span_id,
            );
            let open = f.open_block(static_block_id);
            f.push_node(open, *body, PushContext::Module, b);

            // return control to the root block
            f.blocks.switch_blocks(static_block_id);
            Ok(f.next())
        } else {
            b.push_error("Not a module", node.span_id);
            Err(BlockifyError::Invalid.into())
        }
    }
}

impl Flatten<FirstPass> {
    pub fn finish(self, b: &mut NB) -> Flatten<Module> {
        let (f, values) = self.inner._finish(b);
        let m = Flatten {
            inner: f.into(),
            state: Module { values },
        };
        m
    }
}

impl Flatten<Module> {
    pub fn get_link_entry(&self, link_id: LinkId) -> &CodeEntry {
        self.blocks.links.get(link_id)
    }

    pub fn entry_links(&self, block_id: BlockId) -> Vec<LinkId> {
        let block = self.blocks.get_block(block_id);
        let links: Vec<_> = block.iter().collect();
        links
    }

    pub fn dump(&self, b: &NB) {
        self.blocks.dump(b);
    }
}

impl FlattenInner {
    pub fn resolve_code_offset_link(&self, code_offset: CodeOffset) -> LinkId {
        self.maybe_resolve_code_offset_link(code_offset)
            .expect(&format!("Unable to resolve: {}", code_offset))
    }

    pub fn resolve_code_offset(&self, code_offset: CodeOffset) -> ValueId {
        self.maybe_resolve_code_offset(code_offset)
            .expect(&format!("Unable to resolve: {}", code_offset))
    }

    pub fn maybe_resolve_code_offset_link(&self, code_offset: CodeOffset) -> Option<LinkId> {
        match code_offset {
            CodeOffset::Value(_) => {
                unreachable!()
            }
            CodeOffset::Link(link_id) => Some(link_id),
            CodeOffset::Block(block_id) => {
                if let Some(link_id) = self.blocks.block_links.get(&block_id) {
                    Some(*link_id)
                } else {
                    None
                }
            }
        }
    }
    pub fn maybe_resolve_code_offset(&self, code_offset: CodeOffset) -> Option<ValueId> {
        match code_offset {
            CodeOffset::Value(v) => Some(v),
            CodeOffset::Link(link_id) => {
                let entry = self.get_entry(link_id);
                entry.value_id
            }
            CodeOffset::Block(block_id) => {
                if let Some(link_id) = self.blocks.block_links.get(&block_id) {
                    let entry = self.get_entry(*link_id);
                    entry.value_id
                } else {
                    None
                }
            }
        }
    }

    pub fn type_inference(&mut self, b: &mut NB) {
        for (_link_id, entry) in self.blocks.links.iter_mut() {
            if !entry.ty.is_unknown() {
                continue;
            }
            b.types.u.resolve(&entry.ty);
        }
    }

    pub fn type_inference_enforce(&mut self, b: &mut NB) {
        for (link_id, entry) in self.blocks.links.iter_mut() {
            if !entry.ty.is_unknown() {
                continue;
            }

            if let Some(ty) = b.types.u.resolve(&entry.ty) {
                b.push_warning(
                    &format!("Late Unresolved Type: {}=>{} @ {}", &entry.ty, &ty, link_id,),
                    entry.span_id,
                );
                entry.ty = ty;
            } else {
                b.push_error(
                    &format!("Unresolved Type: {} @ {}", &entry.ty, link_id),
                    entry.span_id,
                );
            }
        }
    }

    pub fn dump_scope(&self, block_id: BlockId, b: &NB) {
        let block = self.blocks.get_block(block_id);
        self.blocks.dump_scope(block.scope(), b);
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
            let closed = self.safe_static();
            let entry = CodeEntry::new(
                closed.block_id,
                LCode::DeclareFunction(None),
                func_ty,
                Some(key),
                unknown,
                VarDefinitionSpace::Static,
            );
            self.push_entry_with_link(entry);
        }
    }

    pub fn resolve_open_abstractions(
        &mut self,
        link_id: LinkId,
        abstraction_id: AbstractionId,
        b: &mut NB,
    ) {
        let entry = self.get_entry(link_id);
        let ty = &entry.ty.clone();
        let span_id = entry.span_id;
        let name = entry.name.unwrap();
        let scope_id = self.blocks.get_block(entry.block_id).scope();

        let fun_block_id =
            self.gen_cps_block_with_type(name, scope_id, abstraction_id, ty, span_id, false, b);

        // now replace the abstraction code
        let entry = self.get_entry_mut(link_id);
        entry.code = LCode::Val(Literal::Block(fun_block_id));
        b.unify(&entry.ty, entry.span_id, ty, span_id);
        self.update_connections(link_id);
    }

    pub(super) fn finish_values(&mut self, b: &mut NB) -> Values {
        let blocks = self.blocks.post_order_blocks();
        let mut values = Values::new();

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
                let value_id = values.insert(link_id);
                let entry = self.get_entry_mut(link_id);
                entry.value_id = Some(value_id);
            }
        }
        values
    }

    fn _finish(mut self, b: &mut NB) -> (Self, Values) {
        self.blocks.switch_blocks(self.blocks.static_block_id());

        // make sure all claims have been handled
        self.blocks.ensure_claims(b);

        // add prototypes for builtins
        self.inject_builtin_prototypes(b);

        self.resolve_deferred(b);
        assert!(self.deferred_goto.is_empty());

        // ensure types are resolved
        self.type_inference_enforce(b);

        self.cont_graph("cont.dot", b);

        self.resolve_open_identifiers(b);
        self.resolve_cps(b);

        // declare static functions
        // TODO: we can move this into the static function generator
        self.blocks.switch_blocks(self.blocks.static_block_id());
        for block_id in self.blocks.graph_get_entries() {
            let block = self.blocks.get_block(block_id);
            let label_link_id = block.entry();
            let entry = self.get_entry(label_link_id).clone();
            let ty = self.get_type(label_link_id).clone();
            assert_eq!(entry.mem, VarDefinitionSpace::Static);

            let closed = self.safe_static();
            let entry = CodeEntry::new(
                closed.block_id,
                LCode::DeclareFunction(Some(block_id)),
                ty,
                entry.name,
                entry.span_id,
                VarDefinitionSpace::Static,
            );
            self.push_entry_with_link(entry);
        }

        // DEAD BLOCKS
        let dead_blocks = self.blocks.find_dead_blocks_from_graph();
        for block_id in dead_blocks {
            self.blocks.get_block_mut(block_id).mark_dead();

            if let Some(link_id) = self.blocks.block_links.get(&block_id).cloned() {
                let entry = self.get_entry(link_id);
                b.push_warning(&format!("Dead Block: {}", block_id), entry.span_id);
            } else {
                let span_id = b.spans.get_span_unknown();
                b.push_warning(&format!("Missing Block: {}", block_id), span_id);
            }
        }

        let static_block_id = self.blocks.static_block_id();
        let entry = CodeEntry::new(
            static_block_id,
            LCode::EndModule,
            AstType::Unit,
            None,
            b.spans.get_span_unknown(),
            VarDefinitionSpace::Static,
        );
        self.push_entry_with_link(entry);

        // the last thing we do is calculate the values, which is the post order traversal of the
        // blocks.
        let values = self.finish_values(b);
        (self, values)
    }

    fn insert_decl_entry(&mut self, block_id: BlockId, entry: CodeEntry) -> LinkId {
        let link_id = self.blocks.links.insert(entry);
        self.blocks.get_block_mut(block_id).push_decl(link_id);
        link_id
    }

    pub fn insert_decl<S: SafeBlockState>(
        &mut self,
        sblock: &SafeBlock<S>,
        ty: AstType,
        name: StringKey,
        span_id: SpanId,
    ) -> LinkId {
        let block = self.blocks.get_block(sblock.block_id);
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
        self.insert_decl_entry(entry_block_id, entry)
    }

    pub fn push_entry_with_link(&mut self, mut entry: CodeEntry) -> LinkId {
        let code = entry.code.clone();
        let block_id = entry.block_id;

        let v = match (code.is_term(), &code) {
            (true, _) => {
                let link_id = self.blocks.links.insert(entry);
                self.blocks.get_block_mut(block_id).terminate(link_id);
                link_id
            }

            (_, LCode::Label) => {
                let link_id = self.blocks.links.insert(entry);
                let block = self.blocks.get_block_mut(block_id);
                block.push_label(link_id);
                link_id
            }

            (_, LCode::Arg(_)) => {
                let link_id = self.blocks.links.insert(entry);
                let block = self.blocks.get_block_mut(block_id);
                block.push_arg(link_id);
                link_id
            }

            (_, LCode::Declare | LCode::DeclareFunction(_)) => {
                let block = self.blocks.get_block(block_id);
                let scope_id = block.scope();
                let scope = self.blocks.get_scope(scope_id);
                let entry_block_id = scope.entry_block();
                entry.block_id = entry_block_id;
                let link_id = self.insert_decl_entry(entry_block_id, entry);
                link_id
            }

            _ => {
                let link_id = self.blocks.links.insert(entry);
                let block = self.blocks.get_block_mut(block_id);
                block.push_link(link_id);
                link_id
            }
        };
        self.update_connections(v);
        v
    }

    pub(super) fn update_connections(&mut self, link_id: LinkId) {
        let code = self.get_entry(link_id).code.clone();
        match code {
            LCode::Arg(i) => self.scoped_continuations.connect(
                ContinuationFlow::BlockArg(self.blocks.current_block_id(), i),
                ContinuationFlow::Variable(link_id),
                FlowEdge::BlockArg,
            ),

            LCode::Switch(_, branches) => {
                for b in branches.values() {
                    self.blocks
                        .block_succ(self.blocks.current_block_id(), *b, Successor::Jump);
                    self.blocks.block_succ(
                        self.blocks.current_block_id(),
                        *b,
                        Successor::BlockScope,
                    );

                    self.scoped_continuations.connect(
                        ContinuationFlow::Jump(link_id),
                        ContinuationFlow::Block(*b),
                        FlowEdge::Switch,
                    );
                }
            }

            LCode::Branch(_, b1, b2) => {
                for b in vec![b1, b2] {
                    self.blocks
                        .block_succ(self.blocks.current_block_id(), b, Successor::Jump);
                    self.blocks.block_succ(
                        self.blocks.current_block_id(),
                        b,
                        Successor::BlockScope,
                    );
                }

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
                self.blocks
                    .block_succ(self.blocks.current_block_id(), b, Successor::Jump);
                self.blocks
                    .block_succ(self.blocks.current_block_id(), b, Successor::BlockScope);

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
        self.blocks.links.get(link_id)
    }

    pub fn get_type(&self, link_id: LinkId) -> &AstType {
        &self.get_entry(link_id).ty
    }

    pub fn get_entry_mut(&mut self, link_id: LinkId) -> &mut CodeEntry {
        self.blocks.links.get_mut(link_id)
    }

    pub fn push_sequence(
        &mut self,
        mut open: SafeBlockOpen,
        seq: Vec<AstNode>,
        span_id: SpanId,
        b: &mut NB,
    ) -> (SafeBlockUnknown, LinkId) {
        self.blocks.switch_blocks(open.block_id);
        let scope_id = self.blocks.get_block(open.block_id).scope();
        let start_stack = self.blocks.walk_scopes(scope_id);

        let length = seq.len();

        let mut unk_block = open.unknown();
        for (i, expr) in seq.into_iter().enumerate() {
            let context = if i == length - 1 {
                PushContext::SeqLast
            } else if i == 0 {
                PushContext::SeqFirst
            } else {
                PushContext::Seq
            };

            let span_id = expr.span_id;
            open = self.ensure_open(span_id, b);
            let (unk, _) = self.safe_push_node_result(open, expr, context, b);
            unk_block = unk;
        }

        // ensure that we close any blocks that were opened
        let scope_id = self.blocks.scope_id(&unk_block);
        let end_stack = self.blocks.walk_scopes(scope_id);
        for _ in 0..end_stack.len() - start_stack.len() {
            let ast: Ast = ControlFlowMarker::BlockEnd.into();
            let node = ast.node(span_id);
            open = self.ensure_open(span_id, b);
            let (unk, _) = self.safe_push_node_result(open, node, PushContext::BlockEnd, b);
            unk_block = unk;
        }

        self.blocks.switch_blocks(unk_block.block_id);
        let link_id = self.blocks.get_block(unk_block.block_id).last().unwrap();
        (self.blocks.safe_unknown(), link_id)
    }

    pub fn safe_push_node(
        &mut self,
        open: SafeBlockOpen,
        node: AstNode,
        context: PushContext,
        b: &mut NB,
    ) -> (SafeBlockUnknown, LinkId) {
        self.blocks.switch_blocks(open.block_id);
        let (unk, r) = self.push_node(open, node, context, b);
        let link_id = r.link_id.unwrap();
        (unk, link_id)
    }

    pub fn safe_push_node_result(
        &mut self,
        open: SafeBlockOpen,
        node: AstNode,
        context: PushContext,
        b: &mut NB,
    ) -> (SafeBlockUnknown, FlattenResult) {
        self.blocks.switch_blocks(open.block_id);
        let (unk, r) = self.push_node(open, node, context, b);
        (unk, r)
    }

    pub fn push_return(
        &mut self,
        open: SafeBlockOpen,
        values: ArgVec,
        span_id: SpanId,
        b: &mut NB,
    ) -> (SafeBlockClosed, LinkId) {
        let (open, _) = self.safe_push_call_values(open, &values, b);

        let (closed, link_id) = self.safe_push_code_term(
            open,
            LCode::Return,
            AstType::Unit,
            None,
            span_id,
            VarDefinitionSpace::Reg,
        );
        (closed, link_id)
    }

    pub fn push_loads_if_needed(
        &mut self,
        mut open: SafeBlockOpen,
        values: &[(Option<StringKey>, LinkId, AstType, SpanId)],
    ) -> (SafeBlockOpen, Vec<LinkId>) {
        let mut links = vec![];
        for (maybe_key, v, ty, span_id) in values {
            let out = if self.blocks.links.is_load_required(*v) {
                let (this_open, link_id) = self.safe_push_code_open(
                    open,
                    LCode::Load(*v),
                    ty.clone(),
                    *maybe_key,
                    *span_id,
                    VarDefinitionSpace::Reg,
                );
                open = this_open;
                link_id
            } else {
                *v
            };
            links.push(out);
        }
        (open, links)
    }

    pub fn safe_push_call_values(
        &mut self,
        mut open: SafeBlockOpen,
        values: &[(Option<StringKey>, LinkId, AstType, SpanId)],
        b: &mut NB,
    ) -> (SafeBlockOpen, Vec<LinkId>) {
        self.blocks.switch_blocks(open.block_id);
        let mut updated_values = vec![];
        let scope_id = self.blocks.get_block(open.block_id).scope();
        for (maybe_key, v, ty, span_id) in values {
            let mut v = *v;
            let entry = self.get_entry(v);
            let v_block_id = entry.block_id;
            let v_block = self.blocks.get_block(v_block_id);
            let v_scope_id = v_block.scope();
            let v_scope = self.blocks.get_scope(v_scope_id);
            let v_entry_block_id = v_scope.entry_block();
            let in_entry = v_entry_block_id == v_block_id;
            let in_block = v_block_id == open.block_id;

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
                    v, open.block_id, scope_id, v_block_id, v_scope_id, ty
                );
                let key = b.labels.fresh_key("r");
                // create space on the stack in the entry block
                let decl_link_id = self.insert_decl(&open, ty.clone(), key, *span_id);
                let entry = self.get_entry_mut(v);
                entry.mem = VarDefinitionSpace::Stack(decl_link_id);
                v = decl_link_id;
            }

            let out = (*maybe_key, v, ty, *span_id);

            updated_values.push(out);
        }

        let mut links = vec![];
        for (maybe_key, v, ty, span_id) in updated_values {
            let (this_open, link_id) = self.safe_push_code_open(
                open,
                LCode::CallValue(v.into()),
                ty.clone(),
                maybe_key,
                span_id,
                VarDefinitionSpace::Reg,
            );
            open = this_open;
            links.push(link_id);
        }

        assert_eq!(self.blocks.current_block_id(), open.block_id);
        self.blocks.switch_blocks(open.block_id);
        (open, links)
    }

    pub fn safe_push_expr(
        &mut self,
        open: SafeBlockOpen,
        expr: AstNode,
        context: PushContext,
        b: &mut NB,
    ) -> (SafeBlockOpen, LinkId) {
        self.blocks.switch_blocks(open.block_id);
        b.dump_ast(&expr);
        let (unk, r) = self.push_node(open, expr, context, b);
        let link_id = r.link_id.unwrap();
        let open = self.blocks.safe_block_try_open(&unk).unwrap();
        (open, link_id)
    }

    fn safe_jump(
        &mut self,
        open: SafeBlockOpen,
        target_block_id: BlockId,
        jump_args: ArgVec,
        span_id: SpanId,
        b: &mut NB,
    ) -> SafeBlockClosed {
        self.push_jump(open, target_block_id, jump_args, span_id, b);
        SafeBlock {
            block_id: self.blocks.current_block_id(),
            extra: crate::safe::Closed {},
        }
    }

    pub fn push_jump(
        &mut self,
        open: SafeBlockOpen,
        target_block_id: BlockId,
        jump_args: ArgVec,
        span_id: SpanId,
        b: &mut NB,
    ) -> SafeBlockClosed {
        self.blocks.switch_blocks(open.block_id);
        let (target_block_id, jump_args) =
            self.push_jump_unwind(target_block_id, jump_args, span_id, b);
        let open = self.open();
        self.push_jump_direct(open, target_block_id, jump_args, span_id, b)
    }

    pub fn push_store_args(
        &mut self,
        decl_scope_id: ScopeId,
        jump_args: ArgVec,
        span_id: SpanId,
        b: &mut NB,
    ) -> ArgVec {
        // for all of the return links, copy them into the target scope
        // Anything we are referencing here is potentially going to be destroyed
        // We copy everything for now, but don't need to do this in all circumstances
        // For example, if the value is already in the target scope, or it's on the heap.
        let start_block_id = self.blocks.current_block_id();
        let scope = self.blocks.get_scope(decl_scope_id);
        let decl_block_id = scope.entry_block();
        let mut copied_link_ids = vec![];
        for (_, link_id, _, _) in jump_args.iter() {
            let entry = self.get_entry(*link_id);
            let ty = entry.ty.clone();
            let key = b.labels.fresh_key("r");

            // switch to the target block, so we can create the declaration
            self.blocks.switch_blocks(decl_block_id);
            let sblock = self.blocks.safe_unknown();
            let decl_link_id = self.insert_decl(&sblock, ty.clone(), key, span_id);

            // switch back to the start block, so we can store the value
            self.blocks.switch_blocks(start_block_id);
            let open = self.open_block(start_block_id);
            self.safe_push_code_open(
                open,
                LCode::Store(decl_link_id, *link_id),
                AstType::Unit,
                None,
                span_id,
                VarDefinitionSpace::Default,
            );
            copied_link_ids.push((None, decl_link_id, ty, span_id));
        }
        copied_link_ids
    }

    pub fn push_jump_unwind(
        &mut self,
        target_block_id: BlockId,
        jump_args: ArgVec,
        span_id: SpanId,
        b: &mut NB,
    ) -> (BlockId, ArgVec) {
        // handle leaving scope here?
        // We need to unwind the target, as well as any CPS parameters we send
        // We unwind at the caller.

        // TODO: unwind when leaving this scope
        let start_block_id = self.blocks.current_block_id();
        let start_scope_id = self.blocks.get_block(start_block_id).scope();
        let target_scope_id = self.blocks.get_block(target_block_id).scope();
        assert_ne!(start_block_id, target_block_id);

        log::debug!(
            "jump: {}{}=>{}{}",
            start_block_id,
            start_scope_id,
            target_block_id,
            target_scope_id
        );

        let scope_changed = start_scope_id != target_scope_id;
        if scope_changed {
            let unwind = self.blocks.unwind_scopes(start_scope_id, target_scope_id);
            if unwind.is_empty() {
                let down = self
                    .blocks
                    .find_scope_next_down(start_scope_id, target_scope_id)
                    .unwrap();
                log::debug!("down: {:?}", down);
                (target_block_id, jump_args)
            } else {
                log::debug!("unwind: {:?}", unwind);
                let copied_link_ids = self.push_store_args(target_scope_id, jump_args, span_id, b);
                let target = self.push_unwind(target_block_id, copied_link_ids, span_id, b);
                (target, vec![])
            }
        } else {
            log::debug!("nochange: {:?}", start_scope_id);
            (target_block_id, jump_args)
        }
    }

    pub fn push_jump_direct(
        &mut self,
        open: SafeBlockOpen,
        target_block_id: BlockId,
        jump_args: ArgVec,
        span_id: SpanId,
        b: &mut NB,
    ) -> SafeBlockClosed {
        // Construct the argument type
        let arg_ty = AstType::Struct(
            jump_args
                .iter()
                .map(|j| (j.0, j.2.clone()))
                .collect::<Vec<_>>(),
        );

        let var_link_ids = jump_args.iter().map(|j| j.1).collect::<Vec<_>>();

        let (open, _) = self.safe_push_call_values(
            open,
            &jump_args
                .into_iter()
                .map(|(key, v, ty, span_id)| (key, v, ty, span_id))
                .collect::<Vec<_>>(),
            b,
        );

        let (closed, jump_link_id) = self.safe_push_code_term(
            open,
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
        closed
    }

    pub fn safe_push_code_open(
        &mut self,
        open: SafeBlockOpen,
        code: LCode,
        ty: AstType,
        name: Option<StringKey>,
        span_id: SpanId,
        mem: VarDefinitionSpace,
    ) -> (SafeBlockOpen, LinkId) {
        assert!(!code.is_term());
        let entry = CodeEntry::new(open.block_id, code, ty, name, span_id, mem);
        self.blocks.switch_blocks(open.block_id);
        (open, self.push_entry_with_link(entry))
    }

    pub fn safe_push_code_term(
        &mut self,
        open: SafeBlockOpen,
        code: LCode,
        ty: AstType,
        name: Option<StringKey>,
        span_id: SpanId,
        mem: VarDefinitionSpace,
    ) -> (SafeBlockClosed, LinkId) {
        assert!(code.is_term());
        let entry = CodeEntry::new(open.block_id, code, ty, name, span_id, mem);
        self.blocks.switch_blocks(open.block_id);
        let closed = SafeBlock {
            block_id: self.blocks.current_block_id(),
            extra: crate::safe::Closed {},
        };
        (closed, self.push_entry_with_link(entry))
    }

    pub fn push_function_call(
        &mut self,
        open: SafeBlockOpen,
        v_fun: LinkId,
        values: ArgVec,
        ret_ty: ReturnType,
        span_id: SpanId,
        b: &mut NB,
    ) -> (SafeBlockOpen, FlattenResult) {
        let (open, _) = self.safe_push_call_values(open, &values, b);

        if let ReturnType::Single(ty) = &ret_ty {
            let (open, link_id) = self.safe_push_code_open(
                open,
                LCode::Call(v_fun.into()),
                ty.clone(),
                None,
                span_id,
                VarDefinitionSpace::Default,
            );
            (open, FlattenResult::link(link_id))
        } else {
            unimplemented!()
        }
    }

    pub fn push_builtin_call(
        &mut self,
        id: BuiltinId,
        args: Vec<Argument>,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> (SafeBlockOpen, FlattenResult) {
        let bi = b.builtins.get_enum(id);
        let abstraction_id = b.builtins.get_abstraction(bi);
        let (args, def_func_type) =
            self.calculate_function_arguments(abstraction_id, &args, &[], call_span_id, b);
        let def_func_type = b.types.refresh_func_type(&def_func_type);

        let open = self.open();
        let (open, call_values) = self.push_call_arguments(open, args, call_span_id, b);
        let (open, _) = self.safe_push_call_values(open, &call_values, b);

        let call_types = call_values.iter().map(|v| v.2.clone()).collect::<Vec<_>>();

        // unify args
        // TODO: return type should also be unified
        b.unify(
            &def_func_type.args,
            call_span_id,
            &AstType::build_struct(call_types),
            call_span_id,
        );

        let (open, link_id) = self.safe_push_code_open(
            open,
            LCode::Builtin(id),
            def_func_type.into(),
            None,
            call_span_id,
            VarDefinitionSpace::Default,
        );
        (open, FlattenResult::link(link_id))
    }

    fn push_start_block_args(&mut self, block_ty: AstFuncType, span_id: SpanId) -> ArgVec {
        assert!(block_ty.args.is_composite());

        let mut open = self.open();
        let block_id = self.blocks.current_block_id();
        let scope_id = self.blocks.get_block(block_id).scope();

        let mut v_args = vec![];
        for (i, (name, ty)) in block_ty.args.fields().iter().enumerate() {
            let (this_open, link_id) = self.safe_push_code_open(
                open,
                LCode::Arg(i as u8),
                ty.clone(),
                *name,
                span_id,
                VarDefinitionSpace::Arg,
            );
            open = this_open;
            v_args.push((*name, link_id, ty.clone(), span_id));
            if let Some(name) = name {
                self.blocks.scope_define(scope_id, *name, link_id.into());
            }
        }
        v_args
    }

    pub(super) fn push_start_block_static(
        &mut self,
        empty: SafeBlockEmpty,
        block_ty: AstFuncType,
        name: Option<StringKey>,
        span_id: SpanId,
    ) -> (SafeBlockOpen, LinkId, ArgVec) {
        self.push_start_block_mem(empty, block_ty, name, span_id, VarDefinitionSpace::Static)
    }

    pub(super) fn push_start_block(
        &mut self,
        empty: SafeBlockEmpty,
        block_ty: AstFuncType,
        name: Option<StringKey>,
        span_id: SpanId,
    ) -> (SafeBlockOpen, LinkId, ArgVec) {
        self.push_start_block_mem(empty, block_ty, name, span_id, VarDefinitionSpace::Default)
    }

    pub(super) fn push_start_block_mem(
        &mut self,
        empty: SafeBlockEmpty,
        block_ty: AstFuncType,
        name: Option<StringKey>,
        span_id: SpanId,
        mem: VarDefinitionSpace,
    ) -> (SafeBlockOpen, LinkId, ArgVec) {
        let entry = CodeEntry::new(
            empty.block_id,
            LCode::Label,
            block_ty.clone().into(),
            name,
            span_id,
            mem,
        );
        self.blocks.switch_blocks(empty.block_id);
        let block_link_id = self.push_entry_with_link(entry);
        let v_args = self.push_start_block_args(block_ty, span_id);
        self.blocks
            .block_links
            .insert(self.blocks.current_block_id(), block_link_id);

        let open = self.open();
        (open, block_link_id, v_args)
    }

    pub fn push_close_block(
        &mut self,
        span_id: SpanId,
        push_context: PushContext,
        b: &mut NB,
    ) -> (SafeBlockClosed, FlattenResult) {
        let current_block_id = self.blocks.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        let scope_id = block.scope();

        if let Some(scope) = self.blocks.try_loop_scope(scope_id) {
            let start_block = scope.start_block();
            let next_block = scope.next_block();
            let unk = self.blocks.safe_unknown();
            self.maybe_terminate_block(unk, start_block, span_id, push_context, b);
            self.blocks.switch_blocks(next_block);
            let closed = SafeBlock {
                block_id: self.blocks.current_block_id(),
                extra: crate::safe::Closed {},
            };
            (closed, FlattenResult::statement())
        } else {
            unimplemented!();
        }
    }

    pub fn dump_position(&self) {
        let block_id = self.blocks.current_block_id();
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

    pub fn remove_placeholder_terminal(
        &mut self,
        goto_block_id: BlockId,
    ) -> (SafeBlockOpen, LinkId) {
        let block = self.blocks.get_block(goto_block_id);
        let last_link_id = block.last().unwrap();
        let entry = self.get_entry(last_link_id);
        if let LCode::PlaceholderTerminal = entry.code {
            let block = self.blocks.get_block_mut(goto_block_id);
            let _ = block.pop_terminal();
        } else {
            unreachable!()
        }
        let open = self.open_block(goto_block_id);
        (open, last_link_id)
    }

    pub fn calc_jump_code(
        &mut self,
        arg_link_id: LinkId,
        mut target_block_ids: Vec<BlockId>,
        span_id: SpanId,
        b: &mut NB,
    ) -> Option<LCode> {
        if target_block_ids.len() == 1 {
            let block_id = *target_block_ids.last().unwrap();
            Some(LCode::Jump(block_id))
        } else if target_block_ids.len() > 1 {
            // It's not necessary to sort these, but we do it so that the list is consistent
            // between builds
            // Currently we are passing around the actual block_ids, which is very simple,
            // but it's also very hacky.
            target_block_ids.sort();
            let mut m = HashMap::new();
            for block_id in target_block_ids.iter() {
                m.insert(block_id.index(), *block_id);
            }
            Some(LCode::Switch(arg_link_id, m))
        } else {
            b.push_warning("Missing Targets", span_id);
            None
        }
    }

    pub fn push_noop(&mut self, open: SafeBlockOpen, span_id: SpanId) -> (SafeBlockOpen, LinkId) {
        let (open, link_id) = self.safe_push_code_open(
            open,
            LCode::Noop,
            AstType::Unit,
            None,
            span_id,
            VarDefinitionSpace::Default,
        );
        (open, link_id)
    }

    pub fn safe_static(&mut self) -> SafeBlockOpen {
        SafeBlock {
            block_id: self.blocks.static_block_id(),
            extra: crate::safe::Open {},
        }
    }

    pub fn open(&mut self) -> SafeBlockOpen {
        self.blocks
            .safe_switch_block(self.blocks.current_block_id())
    }

    pub fn open_block(&mut self, block_id: BlockId) -> SafeBlockOpen {
        self.blocks.safe_switch_block(block_id)
    }

    pub fn push_node_in_static(
        &mut self,
        node: AstNode,
        push_context: PushContext,
        b: &mut NB,
    ) -> FlattenResult {
        let block = self.safe_static();
        let open = SafeBlock {
            block_id: block.block_id,
            extra: crate::safe::Open {},
        };

        let (_, r) = self.push_node(open, node, push_context, b);
        r
    }

    pub fn push_node(
        &mut self,
        open: SafeBlockOpen,
        node: AstNode,
        push_context: PushContext,
        b: &mut NB,
    ) -> (SafeBlockUnknown, FlattenResult) {
        let current_block_id = open.block_id;
        let block = self.blocks.get_block_mut(current_block_id);
        let span_id = node.span_id;
        let ast = node.node;

        match ast {
            Ast::Module(_, _) => {
                unimplemented!("No nested modules yet")
            }

            Ast::Sequence(exprs) => {
                let (unk, link_id) = self.push_sequence(open, exprs, span_id, b);
                (unk, FlattenResult::link(link_id))
            }

            Ast::Global(name, ref expr) => {
                match &expr.node {
                    Ast::Lambda(def) => {
                        // save template for later use
                        if def.body.is_some() {
                            self.blocks
                                .save_abstraction(current_block_id, &name, &def, span_id);
                        }

                        // TODO: The function doesn't actually exist until we call it
                        // So we have no way of returning a reference to it yet
                        // We only add it to the graph when it's monomorphized
                        // We could return the abstraction_id, and allow the program to
                        // perform the monomorphization itself.
                        if let Some(_body) = &def.body {
                            (open.unknown(), FlattenResult::statement())
                        } else {
                            (open.unknown(), FlattenResult::statement())
                        }
                    }

                    Ast::Literal(lit) => {
                        let scope_id = block.scope();
                        let scope = self.blocks.get_scope(scope_id);

                        let static_block_id = self.blocks.static_block_id();

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
                        self.blocks.switch_blocks(static_block_id);
                        let link_id = self.insert_decl_entry(
                            static_block_id,
                            CodeEntry::new(
                                static_block_id,
                                LCode::Val(lit.clone()),
                                ast_ty.clone(),
                                Some(global_name_key),
                                node.span_id,
                                VarDefinitionSpace::Static,
                            ),
                        );

                        self.blocks.scope_define(scope_id, name, link_id.into());

                        self.blocks.switch_blocks(current_block_id);
                        let open = self.open();
                        (open.unknown(), FlattenResult::link(link_id))
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
                        self.blocks.switch_blocks(current_block_id);
                        (open.unknown(), FlattenResult::statement())
                    }
                    _ => {
                        let args_size = args.len();
                        assert_eq!(args_size, bi.arity());
                        self.blocks.switch_blocks(current_block_id);
                        let (open, r) = self.push_builtin_call(id, args, span_id, b);
                        (open.unknown(), r)
                    }
                }
            }

            Ast::Return(maybe_expr) => {
                let block = self.blocks.block(&open);

                let fun_scope_id = self.blocks.get_function_scope_id(block.scope());
                let fun_block_id = self.blocks.get_entry_block(fun_scope_id);

                let mut jump_args = vec![];
                let (open, span_id) = if let Some(expr) = maybe_expr {
                    let expr_span_id = expr.span_id;
                    let (open, link_id) = self.safe_push_expr(open, *expr, PushContext::Return, b);
                    let entry = self.get_entry(link_id);
                    jump_args.push((None, link_id, entry.ty.clone(), span_id));
                    (open, expr_span_id)
                } else {
                    (open, node.span_id)
                };

                let fun_scope = self.blocks.get_scope_mut(fun_scope_id);
                let jump_types = jump_args
                    .iter()
                    .map(|(_, _, ty, _)| ty.clone())
                    .collect::<Vec<_>>();
                fun_scope.insert_ret_arg(jump_types);

                let scope = self.blocks.get_function_scope(fun_block_id);
                let ret_block_id = scope.return_block();

                let closed = self.safe_jump(open, ret_block_id, jump_args, span_id, b);
                (closed.unknown(), FlattenResult::statement())
            }

            Ast::Literal(lit) => {
                // literal is expression, non-terminal
                let ty: AstType = match &lit {
                    Literal::Block(_block_id) => b.types.fresh_unknown(),
                    _ => lit.clone().into(),
                };
                let mem = VarDefinitionSpace::Default;

                let (open, link_id) = self.safe_push_code_open(
                    open,
                    LCode::Val(lit),
                    ty.clone(),
                    None,
                    node.span_id,
                    mem,
                );
                (open.unknown(), FlattenResult::link(link_id))
            }

            Ast::BinaryOp(op, x, y) => {
                // expression, non-terminal
                let x_span_id = x.span_id;
                let y_span_id = y.span_id;

                let (open, vx) = self.safe_push_expr(open, *x, PushContext::Default, b);
                let (open, vy) = self.safe_push_expr(open, *y, PushContext::Default, b);

                let rx_ty = self.get_type(vx).clone();
                let ry_ty = self.get_type(vy).clone();

                b.unify(&rx_ty, x_span_id, &ry_ty, y_span_id);

                let (open, _) = self.safe_push_call_values(
                    open,
                    &[
                        (None, vx, rx_ty.clone(), node.span_id),
                        (None, vy, ry_ty.clone(), node.span_id),
                    ],
                    b,
                );

                let ret_ty = op.node.get_type(&rx_ty, &ry_ty);
                let (open, link_id) = self.safe_push_code_open(
                    open,
                    LCode::Op2(op.node),
                    ret_ty.clone(),
                    None,
                    op.span_id,
                    VarDefinitionSpace::Default,
                );

                self.blocks.switch_blocks(open.block_id);

                (open.unknown(), FlattenResult::link(link_id))
            }

            Ast::Identifier(key) => {
                // identifier is expression, non-terminal
                let scope_id = block.scope();

                // resolve identifier lexically
                if let Some(def_link_id) = self.blocks.resolve_name(current_block_id, key) {
                    let link_id = def_link_id;
                    return (open.unknown(), FlattenResult::link(link_id));
                }

                // we are resolving the abstraction lexically here, but it could also be defined
                // later.  TODO: if we don't find it, it might be defined later, so we should defer
                // and throw the error later if it's not found.
                if let Some(abstraction_id) = self.blocks.resolve_template(scope_id, key.into()) {
                    let code = LCode::Val(Literal::Abstraction(abstraction_id));
                    let ty = b.types.fresh_unknown();
                    let (open, link_id) = self.safe_push_code_open(
                        open,
                        code,
                        ty,
                        Some(key),
                        node.span_id,
                        VarDefinitionSpace::Default,
                    );
                    self.resolve_open_abstractions(link_id, abstraction_id, b);
                    return (open.unknown(), FlattenResult::link(link_id));
                }

                /*
                 * The ident may not yet be defined if it's a label.
                 * If we don't find it immediately in lexical scope, then defer.
                 */
                let code = LCode::PlaceholderCodeReference;
                let ty = b.types.fresh_unknown();
                let (open, link_id) = self.safe_push_code_open(
                    open,
                    code,
                    ty,
                    Some(key),
                    node.span_id,
                    VarDefinitionSpace::Default,
                );
                self.open_identifiers.push(link_id);
                (open.unknown(), FlattenResult::link(link_id))
            }

            Ast::Assign(target, expr) => {
                // assign is expression, non-terminal
                let name = match target {
                    AssignTarget::Identifier(name) | AssignTarget::Alloca(name) => name,
                };

                // push the definition into the lambda list
                if let Ast::Lambda(def) = expr.node {
                    self.blocks.switch_blocks(current_block_id);

                    // save the template
                    let def_span_id = expr.span_id;
                    let _ =
                        self.blocks
                            .save_abstraction(current_block_id, &name, &def, def_span_id);
                    self.blocks.switch_blocks(current_block_id);
                    return (open.unknown(), FlattenResult::statement());
                }

                self.blocks.switch_blocks(current_block_id);
                let (open, v_expr) = self.safe_push_expr(open, *expr, PushContext::Default, b);
                let expr_entry = self.get_entry(v_expr);
                let expr_ty = expr_entry.ty.clone();
                let expr_span_id = expr_entry.span_id;

                let block_id = self.blocks.current_block_id();
                let block = self.blocks.get_block(block_id);
                let scope_id = block.scope();

                let (open, offset_decl) =
                    if let Some(v_decl) = self.blocks.resolve_name_in_scope(scope_id, name) {
                        // already declared
                        let decl_entry = self.get_entry(v_decl);
                        b.unify(&decl_entry.ty, decl_entry.span_id, &expr_ty, expr_span_id);
                        (open, v_decl)
                    } else {
                        // need to declare it
                        let block = self.blocks.get_block(self.blocks.current_block_id());
                        let scope_id = block.scope();

                        let (open, link_id) = self.safe_push_code_open(
                            open,
                            LCode::Declare,
                            expr_ty.clone(),
                            Some(name),
                            node.span_id,
                            VarDefinitionSpace::Default,
                        );
                        self.blocks.scope_define(scope_id, name, link_id);
                        (open, link_id)
                    };

                // explicit store for assign
                let (open, _) = self.safe_push_code_open(
                    open,
                    LCode::Store(offset_decl, v_expr),
                    AstType::Unit,
                    None,
                    node.span_id,
                    VarDefinitionSpace::Default,
                );
                (open.unknown(), FlattenResult::link(offset_decl))
            }

            Ast::Import(module_key, args) => {
                let module_name = b.labels.r(module_key.into());
                let scope_id = block.scope();

                let open = if &module_name == "prelude" {
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

                    let (open, link_id) = self.safe_push_code_open(
                        open,
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
                    open
                } else {
                    unimplemented!("module {}", module_name)
                };
                (open.unknown(), FlattenResult::statement())
            }

            Ast::Call(expr, args) => {
                match &expr.node {
                    // call is an expression, it's non-terminal
                    // lambdas should also be non-terminal
                    Ast::Identifier(ident) => {
                        if let Some((scope_id, abstraction_id)) =
                            self.blocks.resolve_lambda(current_block_id, *ident)
                        {
                            let (open, r) =
                                self.push_call(open, scope_id, abstraction_id, span_id, args, b);
                            (open.unknown(), r)
                        } else {
                            let name = b.labels.r(ident.into());
                            b.push_error(&format!("Call name not found: {}", name), span_id);
                            let (open, link_id) = self.push_noop(open, span_id);
                            (open.unknown(), FlattenResult::link(link_id))
                        }
                    }
                    Ast::Attribute(ident, attr) => {
                        let node = attr;
                        if let Some(ast) = resolve_attribute(*ident, &node, span_id, args, b) {
                            let (unk, r) = self.safe_push_node_result(open, ast, push_context, b);
                            (unk, r)
                        } else {
                            let name = b.labels.r(ident.into());
                            b.push_error_labels(vec![b.primary_label(
                                &format!("Builtin not found: {}", name),
                                attr.span_id,
                            )]);
                            let (open, link_id) = self.push_noop(open, span_id);
                            (open.unknown(), FlattenResult::link(link_id))
                        }
                    }
                    _ => unimplemented!("{:?}", expr.node),
                }
            }

            Ast::UnaryOp(op, x) => {
                // op1 is expression, non-terminal
                let (open, link_id) = self.safe_push_expr(open, *x, PushContext::Default, b);
                self.blocks.switch_blocks(current_block_id);
                let ty = self.get_type(link_id).clone();

                let (open, _) =
                    self.safe_push_call_values(open, &[(None, link_id, ty.clone(), span_id)], b);

                let (open, link_id) = self.safe_push_code_open(
                    open,
                    LCode::Op1(op),
                    ty.clone(),
                    None,
                    node.span_id,
                    VarDefinitionSpace::Reg,
                );
                (open.unknown(), FlattenResult::link(link_id))
            }

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
                let current_block_id = self.blocks.current_block_id();
                let block = self.blocks.get_block(current_block_id);
                assert!(!block.is_term());

                // Start Next Block, we might not need this
                let next_block = self
                    .blocks
                    .new_block(current_block_id, Successor::BlockScope);

                // THEN Block
                let (then_block, then_start_block_id, _) = self.blocks.new_scope_and_block(
                    ScopeType::Block,
                    ScopeState::block(),
                    current_block_id,
                    Successor::BlockScope,
                );

                let then_span_id = then_expr.span_id;

                let branch_block_type = AstFuncType {
                    args: AstType::Struct(vec![]).into(),
                    ret: ReturnType::Single(AstType::Unit).into(),
                };

                let name = b.labels.fresh_key("then");
                self.blocks.switch_blocks(then_start_block_id);
                let (then_block, _, _) = self.push_start_block(
                    then_block,
                    branch_block_type.clone().into(),
                    Some(name),
                    then_span_id,
                );
                self.blocks.switch_blocks(then_block.block_id);
                let (then_block, _) =
                    self.safe_push_node_result(then_block, *then_expr, PushContext::CondThen, b);
                let then_end_block_id = then_block.block_id;
                let then_is_term = self.blocks.get_block(then_block.block_id).is_term();

                // ELSE Block
                let (has_else, else_is_term, else_start_block_id, else_end_block_id) =
                    if let Some(else_expr) = maybe_else_expr {
                        let (else_block, else_start_block_id, _) = self.blocks.new_scope_and_block(
                            ScopeType::Block,
                            ScopeState::block(),
                            current_block_id,
                            Successor::BlockScope,
                        );

                        let else_span_id = else_expr.span_id;
                        let name = b.labels.fresh_key("else");

                        self.blocks.switch_blocks(else_block.block_id);
                        let (else_block, _, _) = self.push_start_block(
                            else_block,
                            branch_block_type.into(),
                            Some(name),
                            else_span_id,
                        );

                        self.blocks.switch_blocks(else_block.block_id);
                        let (else_block, _) = self.safe_push_node_result(
                            else_block,
                            *else_expr,
                            PushContext::CondThen,
                            b,
                        );
                        let else_end_block_id = else_block.block_id;
                        let else_is_term = self.blocks.get_block(else_end_block_id).is_term();
                        (true, else_is_term, else_start_block_id, else_end_block_id)
                    } else {
                        self.blocks.block_succ(
                            current_block_id,
                            next_block.block_id,
                            Successor::BlockScope,
                        );
                        self.blocks.block_succ(
                            current_block_id,
                            next_block.block_id,
                            Successor::Jump,
                        );
                        (false, false, next_block.block_id, next_block.block_id)
                    };

                // we only want to create a next block if either of the branches are not terminated
                // Otherwise we need it
                // If both branches are terminal, then this block should be terminal
                // if either of the branches are not terminal, then we need to create a next block,
                // and leave the block open
                let is_next_needed = !then_is_term || !else_is_term;

                let v_next = if is_next_needed {
                    if has_else {
                        self.blocks.switch_blocks(else_end_block_id);
                        let unk = self.blocks.safe_unknown();
                        self.maybe_terminate_block(
                            unk,
                            next_block.block_id,
                            span_id,
                            push_context,
                            b,
                        );
                    }

                    self.blocks.switch_blocks(then_end_block_id);
                    let unk = self.blocks.safe_unknown();
                    self.maybe_terminate_block(unk, next_block.block_id, span_id, push_context, b);

                    // start the next block
                    self.blocks.switch_blocks(next_block.block_id);
                    let (next_block, _, _) = self.push_start_block(
                        next_block,
                        AstFuncType::new_void_void(),
                        Some(b.labels.fresh_key("cond_next")),
                        span_id,
                    );

                    Some(next_block.block_id)
                } else {
                    None
                };

                // condition
                self.blocks.switch_blocks(current_block_id);
                let open = self.open_block(current_block_id);
                let (open, link_id) =
                    self.safe_push_expr(open, *condition, PushContext::Default, b);

                let (_, v) = self.safe_push_code_term(
                    open,
                    LCode::Branch(
                        link_id.into(),
                        then_start_block_id.into(),
                        else_start_block_id.into(),
                    ),
                    AstType::Unit,
                    None,
                    span_id,
                    VarDefinitionSpace::Reg,
                );

                if let Some(v_next) = v_next {
                    // if next is used, leave the block open
                    self.blocks.switch_blocks(v_next);
                }
                (self.blocks.safe_unknown(), FlattenResult::link(v))
            }

            Ast::ControlFlowMarker(ControlFlowMarker::BlockReference(expr)) => {
                let (open, block_id) = match &expr.node {
                    Ast::Identifier(key) => {
                        let key = *key;
                        let ty = AstType::func(vec![], AstType::Unit);
                        let scope_id = block.scope();
                        if let Some((_resolve_type, link_id, _scope_id)) =
                            self.blocks.resolve_function_name(scope_id, &key, &ty, b)
                        {
                            let entry = self.get_entry(link_id);
                            (open, entry.block_id)
                        } else {
                            let (open, link_id) =
                                self.safe_push_expr(open, *expr, PushContext::Default, b);
                            let entry = self.get_entry(link_id);
                            let block_id = match &entry.code {
                                LCode::Label => entry.block_id,
                                LCode::PlaceholderCodeReference => {
                                    let s_name = b.labels.r(key.into());
                                    unimplemented!("{:?}", (s_name, entry));
                                }
                                _ => {
                                    unimplemented!("{:?}", entry);
                                }
                            };
                            (open, block_id)
                        }
                    }
                    _ => unimplemented!("{:?}", expr),
                };
                let ty = AstType::JumpTarget;
                let code = LCode::Val(Literal::Block(block_id));

                let (open, link_id) = self.safe_push_code_open(
                    open,
                    code,
                    ty,
                    None,
                    node.span_id,
                    VarDefinitionSpace::Reg,
                );
                (open.unknown(), FlattenResult::link(link_id))
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
                let new_block = self
                    .blocks
                    .new_block(self.blocks.current_block_id(), Successor::BlockScope);
                self.blocks.define_label(scope_id, new_block.block_id, name);

                // start a new block.  If the last block isn't terminated, then we create a new
                // block and jump to it.
                // TODO: We can also check if the previous block was empty and compatible, and reuse it.
                if let Some(open) = self.blocks.safe_block_try_open(&open.unknown()) {
                    assert_eq!(args.len(), 0);
                    self.push_jump(open, new_block.block_id, vec![], span_id, b);
                } else {
                    unreachable!();
                }

                // ensure this block is not an entry block, this should never happen.
                let scope = self.blocks.get_scope(scope_id);
                assert!(scope.entry_block() != new_block.block_id);

                let arg_ty = AstType::Struct(
                    args.iter()
                        .map(|p| {
                            let ty = b.types.r(p.ty);
                            (Some(p.name), ty.clone())
                        })
                        .collect::<Vec<_>>(),
                );

                let (new_block, link_id, _) = self.push_start_block(
                    new_block,
                    AstFuncType {
                        args: arg_ty.clone().into(),
                        ret: ReturnType::Single(AstType::Unit).into(),
                    }
                    .into(),
                    Some(name),
                    span_id,
                );
                self.blocks.switch_blocks(new_block.block_id);
                (new_block.unknown(), FlattenResult::link(link_id))
            }

            Ast::Ternary(c, x, y) => {
                // expression, non-terminal

                // Condition
                let (open, c_link_id) = self.safe_push_expr(open, *c, PushContext::Default, b);

                let branch_block_type = AstFuncType {
                    args: AstType::Struct(vec![]).into(),
                    ret: ReturnType::Single(AstType::Unit).into(),
                };

                // THEN
                let (then_block, then_block_id, _) = self.blocks.new_scope_and_block(
                    ScopeType::Region,
                    ScopeState::region(),
                    current_block_id,
                    Successor::Operation,
                );
                let then_span_id = x.span_id;
                let then_ast = AstNode::make_yield(*x);

                let name = b.labels.fresh_key("t_then");

                let (then_block, _, _) = self.push_start_block(
                    then_block,
                    branch_block_type.clone().into(),
                    Some(name),
                    then_span_id,
                );

                let (_, then_link_id) =
                    self.safe_push_node(then_block, then_ast, PushContext::Default, b);
                let then_ty = self.get_type(then_link_id).clone();

                // ELSE
                let else_span_id = y.span_id;
                let (else_block, else_block_id, _) = self.blocks.new_scope_and_block(
                    ScopeType::Region,
                    ScopeState::region(),
                    current_block_id,
                    Successor::Operation,
                );
                let else_ast = AstNode::make_yield(*y);

                let (else_block, _, _) = self.push_start_block(
                    else_block,
                    branch_block_type.into(),
                    Some(name),
                    else_span_id,
                );

                let (_, else_link_id) =
                    self.safe_push_node(else_block, else_ast, PushContext::Default, b);
                let else_ty = self.get_type(else_link_id).clone();

                b.unify(&then_ty, then_span_id, &else_ty, else_span_id);

                // switch back to the original block
                let (open, v) = self.safe_push_code_open(
                    open,
                    LCode::Ternary(c_link_id.into(), then_block_id.into(), else_block_id.into()),
                    then_ty,
                    None,
                    node.span_id,
                    VarDefinitionSpace::Reg,
                );
                (open.unknown(), FlattenResult::link(v))
            }

            Ast::Yield(maybe_expr) => {
                // yield is terminal
                let mut ty = AstType::Unit;
                let open = if let Some(expr) = maybe_expr {
                    self.blocks.switch_blocks(current_block_id);
                    let (open, v) = self.safe_push_expr(open, *expr, PushContext::Default, b);
                    ty = self.get_type(v).clone();
                    // push single arg
                    let (open, _) = self.safe_push_call_values(
                        open,
                        &[(None, v.into(), ty.clone(), node.span_id)],
                        b,
                    );
                    open
                } else {
                    open
                };

                let (closed, v) = self.safe_push_code_term(
                    open,
                    LCode::Yield,
                    ty.clone(),
                    None,
                    node.span_id,
                    VarDefinitionSpace::Reg,
                );
                (closed.unknown(), FlattenResult::link(v))
            }

            Ast::ControlFlowMarker(ControlFlowMarker::Goto(label, args)) => {
                let r = self.push_goto(label, args, span_id, b);
                (open.unknown(), r)
            }

            Ast::ControlFlowMarker(ControlFlowMarker::GotoChain(args)) => {
                let (open, argvec) = self.push_call_arguments(open, args, span_id, b);
                let mut argvec = VecDeque::from(argvec);
                let mut acc = VecDeque::new();
                let current_block_id = self.blocks.current_block_id();
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
                            let v_next = self
                                .blocks
                                .new_block(current_block_id, Successor::BlockScope);
                            self.blocks.switch_blocks(v_next.block_id);
                            let open = self
                                .push_start_block(
                                    v_next,
                                    AstFuncType::new(
                                        AstType::Struct(acc_types).into(),
                                        ReturnType::Single(AstType::Unit),
                                    ),
                                    Some(label),
                                    span_id,
                                )
                                .0;
                            let jump_args = acc.drain(..).collect::<Vec<_>>();
                            self.push_jump(open, block_id.into(), jump_args, node.span_id, b);
                            acc.clear();
                        }
                        LCode::PlaceholderCodeReference => {
                            acc.push_front((None, link_id, ty, span_id));
                        }
                        _ => {
                            b.push_error(&format!("Invalid goto: {:?}", code), span_id);
                            let (open, link_id) = self.push_noop(open, span_id);
                            return (open.unknown(), FlattenResult::link(link_id));
                        }
                    }

                    if argvec.is_empty() {
                        break;
                    }
                }
                self.blocks.switch_blocks(current_block_id);
                let open = self.open();
                (open.unknown(), FlattenResult::statement())
            }

            Ast::ControlFlowMarker(ControlFlowMarker::BlockEnd) | Ast::CloseBlock => {
                let (closed, r) = self.push_close_block(span_id, push_context, b);
                (closed.unknown(), r)
            }

            Ast::ControlFlowMarker(ControlFlowMarker::LoopStart(maybe_key)) => {
                let (loop_block, loop_block_id, loop_scope_id) = self.blocks.new_scope_and_block(
                    ScopeType::Region,
                    ScopeState::region(),
                    current_block_id,
                    Successor::BlockScope,
                );

                let v_next = self
                    .blocks
                    .new_block(current_block_id, Successor::BlockScope);
                self.blocks.switch_blocks(v_next.block_id);
                let open = self
                    .push_start_block(
                        v_next,
                        AstFuncType::new_void_void(),
                        Some(b.labels.fresh_key("postloop")),
                        span_id,
                    )
                    .0;

                self.blocks.switch_blocks(current_block_id);

                self.blocks.update_loop_blocks(
                    loop_scope_id,
                    maybe_key,
                    open.block_id.into(),
                    loop_block_id.into(),
                );

                let key = if let Some(key) = maybe_key {
                    key
                } else {
                    b.labels.fresh_key("default_loop")
                };

                self.blocks.switch_blocks(loop_block_id);
                let loop_block = self
                    .push_start_block(
                        loop_block,
                        AstFuncType {
                            args: AstType::Struct(vec![]).into(),
                            ret: ReturnType::Single(AstType::Unit).into(),
                        }
                        .into(),
                        Some(key),
                        span_id,
                    )
                    .0;

                self.blocks.switch_blocks(current_block_id);
                let open = self.open();
                self.push_jump(open, loop_block_id.into(), vec![], node.span_id, b);

                // open loop block
                self.blocks.switch_blocks(loop_block_id);
                (loop_block.unknown(), FlattenResult::statement())
            }

            Ast::ControlFlowMarker(ControlFlowMarker::LoopContinue(maybe_key)) => {
                let block = self.blocks.get_block(current_block_id);
                let scope_id = block.scope();

                // loop up loop blocks by name
                if let Some(loop_scope) = self.blocks.get_loop_scope(scope_id, maybe_key) {
                    let closed = self.push_jump(
                        open,
                        loop_scope.start_block.into(),
                        vec![],
                        node.span_id,
                        b,
                    );
                    self.blocks.switch_blocks(current_block_id);
                    (closed.unknown(), FlattenResult::statement())
                } else {
                    // mismatch name
                    b.push_error(&format!("Continue without loop"), node.span_id);
                    let (open, link_id) = self.push_noop(open, node.span_id);
                    (open.unknown(), FlattenResult::link(link_id))
                }
            }

            Ast::Continue(maybe_name, args) => {
                let block = self.blocks.get_block(current_block_id);
                let scope_id = block.scope();

                // args not implemented yet
                assert_eq!(args.len(), 0);
                // loop up loop blocks by name
                if let Some(loop_scope) = self.blocks.get_loop_scope(scope_id, maybe_name) {
                    let closed = self.push_jump(
                        open,
                        loop_scope.start_block.into(),
                        vec![],
                        node.span_id,
                        b,
                    );
                    self.blocks.switch_blocks(current_block_id);
                    (closed.unknown(), FlattenResult::statement())
                } else {
                    // mismatch name
                    b.push_error(&format!("Continue without loop"), node.span_id);
                    let (open, link_id) = self.push_noop(open, node.span_id);
                    (open.unknown(), FlattenResult::link(link_id))
                }
            }

            Ast::ControlFlowMarker(ControlFlowMarker::LoopBreak(maybe_key)) => {
                let block = self.blocks.get_block(current_block_id);
                let scope_id = block.scope();
                // loop up loop blocks by name
                if let Some(loop_scope) = self.blocks.get_loop_scope(scope_id, maybe_key) {
                    self.blocks.switch_blocks(current_block_id);
                    self.push_jump(open, loop_scope.next_block.into(), vec![], node.span_id, b);

                    let v_next = self
                        .blocks
                        .new_block(current_block_id, Successor::BlockScope);
                    self.blocks.switch_blocks(v_next.block_id);
                    let (open, link_id, _) = self.push_start_block(
                        v_next,
                        AstFuncType::new_void_void(),
                        Some(b.labels.fresh_key("postloopbreak")),
                        span_id,
                    );
                    (open.unknown(), FlattenResult::link(link_id))
                } else {
                    // mismatch name
                    b.push_error(&format!("Break without loop"), node.span_id);
                    let (open, link_id) = self.push_noop(open, node.span_id);
                    (open.unknown(), FlattenResult::link(link_id))
                }
            }

            Ast::Break(maybe_name, args) => {
                let block = self.blocks.get_block(current_block_id);
                let scope_id = block.scope();

                // args not implemented yet
                assert_eq!(args.len(), 0);
                // loop up loop blocks by name
                if let Some(loop_scope) = self.blocks.get_loop_scope(scope_id, maybe_name) {
                    self.blocks.switch_blocks(current_block_id);
                    self.push_jump(open, loop_scope.next_block.into(), vec![], node.span_id, b);
                    self.blocks.switch_blocks(current_block_id);
                    let open = self.open();
                    (open.unknown(), FlattenResult::statement())
                } else {
                    // mismatch name
                    b.push_error(&format!("Break without loop"), node.span_id);
                    let (open, link_id) = self.push_noop(open, node.span_id);
                    (open.unknown(), FlattenResult::link(link_id))
                }
            }

            Ast::Array(_type_id, dims) => {
                let mut link_ids = vec![];
                let mut open = open;
                for d in dims {
                    let (this_open, link_id) =
                        self.safe_push_expr(open, d, PushContext::Default, b);
                    open = this_open;
                    link_ids.push(link_id);
                }
                b.push_error(&format!("AST Error"), node.span_id);
                let (open, link_id) = self.push_noop(open, node.span_id);
                (open.unknown(), FlattenResult::link(link_id))
            }

            Ast::Tuple(exprs) => {
                let mut link_ids = vec![];
                let mut types = vec![];
                let mut values = vec![];

                let mut open = open;
                for e in exprs {
                    let span_id = e.span_id;
                    self.blocks.switch_blocks(current_block_id);
                    let (this_open, link_id) =
                        self.safe_push_expr(open, e, PushContext::Default, b);
                    open = this_open;
                    let ty = self.get_type(link_id).clone();
                    link_ids.push(link_id);
                    types.push(ty.clone());
                    values.push((None, link_id, ty, span_id));
                }

                let ty = AstType::build_tuple(types);

                let (open, update_link_ids) = self.push_loads_if_needed(open, &values);

                let (open, link_id) = self.safe_push_code_open(
                    open,
                    LCode::Tuple(update_link_ids),
                    ty,
                    None,
                    span_id,
                    VarDefinitionSpace::Default,
                );
                (open.unknown(), FlattenResult::link(link_id))
            }

            Ast::Index(node, index) => {
                let (open, v_node) = self.safe_push_expr(open, *node, PushContext::Default, b);
                let (open, v_index) = self.safe_push_expr(open, *index, PushContext::Default, b);

                let indicies = vec![v_index.into()];

                let entry = self.get_entry(v_index);
                let index = if let LCode::Val(Literal::Int(index)) = entry.code {
                    index as usize
                } else {
                    unimplemented!()
                };
                let entry = self.get_entry_mut(v_index);
                entry.code = LCode::Val(Literal::Index(index));

                let ty = self.get_type(v_node);
                let (_, ty_field) = ty.fields().get(index as usize).unwrap().clone();

                let code = LCode::Use(v_node.into(), indicies);

                let (open, link_id) = self.safe_push_code_open(
                    open,
                    code,
                    ty_field.clone(),
                    None,
                    span_id,
                    VarDefinitionSpace::Default,
                );
                (open.unknown(), FlattenResult::link(link_id))
            }

            Ast::Attribute(ident, attr) => {
                // <ident>.<attr>
                // currently all attributes can be resolved this way, and they
                // resolve to an ast node, which we can then lower.
                let node = attr;
                if let Some(ast) = resolve_attribute(ident, &node, span_id, vec![], b) {
                    let (open, r) = self.safe_push_node_result(open, ast, PushContext::Default, b);
                    (open.unknown(), r)
                } else {
                    unimplemented!();
                }
            }

            Ast::Defer(expr) => {
                // defer is terminal
                let (open, func_link_id) =
                    self.safe_push_expr(open, *expr, PushContext::Default, b);
                // expression must be a function with no arguments.  We bake it here.
                let ty = self.get_type(func_link_id).clone();
                let entry = self.get_entry(func_link_id);

                let func_block_id = match &entry.code {
                    LCode::Val(Literal::Block(block_id)) => *block_id,
                    _ => {
                        b.push_error(
                            &format!("Defer must be a function with no arguments"),
                            node.span_id,
                        );
                        let (open, link_id) = self.push_noop(open, node.span_id);
                        return (open.unknown(), FlattenResult::link(link_id));
                    }
                };

                let required_ty = AstFuncType::new(
                    AstType::Struct(vec![(None, AstFuncType::new_void_void().into())]),
                    ReturnType::Never,
                );
                b.unify(&ty, node.span_id, &required_ty.into(), node.span_id);

                let current_block_id = self.blocks.current_block_id();
                let block = self.blocks.get_block(current_block_id);
                let scope_id = block.scope();
                let scope = self.blocks.get_scope_mut(scope_id);
                scope.prepend_deferral(func_block_id);

                (open.unknown(), FlattenResult::statement())
            }

            Ast::Error => {
                b.push_error(&format!("AST Error"), node.span_id);
                let (open, link_id) = self.push_noop(open, node.span_id);
                (open.unknown(), FlattenResult::link(link_id))
            }

            _ => {
                b.push_error(&format!("AST Unimplemented"), node.span_id);
                unimplemented!("{:?}", ast);
            }
        }
    }

    pub(super) fn ensure_open(&mut self, span_id: SpanId, b: &mut NB) -> SafeBlockOpen {
        // we we want to add a node, and the current block is terminated
        // we create a new block for the dead code that follows.
        let block = self.blocks.get_block(self.blocks.current_block_id());
        if block.is_term() {
            let new_block = self
                .blocks
                .new_block(self.blocks.current_block_id(), Successor::BlockScope);
            let name = b.labels.fresh_key("dead");

            self.blocks.switch_blocks(new_block.block_id);
            self.push_start_block(
                new_block,
                AstFuncType::new(AstType::Struct(vec![]), ReturnType::Single(AstType::Unit)).into(),
                Some(name),
                span_id,
            );
        }
        self.open()
    }

    pub(super) fn maybe_terminate_block(
        &mut self,
        block: SafeBlockUnknown,
        v_next: BlockId,
        span_id: SpanId,
        _push_context: PushContext,
        b: &mut NB,
    ) -> SafeBlockClosed {
        // is the block isn't terminated, terminate it with a jump to another block
        if let Some(closed) = self.blocks.safe_block_try_closed(&block) {
            closed
        } else {
            let open = self.open();
            self.push_jump(open, v_next, vec![], span_id, b)
        }
    }
}
