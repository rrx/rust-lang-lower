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
    AbstractionsBuilder, BlockGraph, BlockId, BlockState, BlockifyError, Builtin, CodeOffset,
    ContinuationFlow, DeferredGotoList, FlowEdge, FunctionVariantBuilder, LCode, LinkId,
    NodeBuilder as NB, ScopeGraph, ScopeId, ScopeType, ScopedContinuations, StringLabel, Successor,
    ValueId, VarDefinitionSpace, VariantId,
};

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

#[derive(Debug, Clone)]
pub struct CodeEntry {
    pub(super) next: LinkId,
    prev: LinkId,
    pub(super) code: LCode,
    pub(super) name: Option<StringKey>,
    pub link: Option<LinkId>,
    pub(super) value_id: Option<ValueId>,
    pub block_id: BlockId,
    pub(super) ty: AstType,
    pub(super) span_id: SpanId,
    pub mem: VarDefinitionSpace,
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

pub struct Flatten<S: BlockState> {
    pub(super) link: LinkOptions,
    pub(super) entries: Vec<CodeEntry>,
    pub blocks: BlockGraph<S>,
    pub(crate) static_scope: Option<ScopeId>,
    pub(crate) static_block: Option<BlockId>,
    pub(crate) current_block: BlockId,
    pub scopes: ScopeGraph,
    pub(super) block_links: HashMap<BlockId, LinkId>,
    pub(crate) functions: HashMap<StringKey, LinkId>,
    pub(crate) statics: HashMap<StringKey, Literal>,
    pub(crate) open_identifiers: Vec<LinkId>,
    pub(crate) scoped_continuations: ScopedContinuations,
    pub deferred_goto: DeferredGotoList,
    pub variants: FunctionVariantBuilder,
    pub abstractions: AbstractionsBuilder,
}

impl Flatten<super::Start> {
    pub fn new() -> Self {
        let blocks = BlockGraph::new();

        Self {
            entries: vec![],
            blocks,
            link: LinkOptions::new(),
            //messages: vec![],
            static_scope: None,
            static_block: None,
            current_block: BlockId::new(0),
            scopes: ScopeGraph::new(),
            block_links: HashMap::new(),
            functions: HashMap::new(),
            statics: HashMap::new(),
            open_identifiers: vec![],
            scoped_continuations: ScopedContinuations::new(),
            deferred_goto: DeferredGotoList::new(),
            variants: FunctionVariantBuilder::new(),
            abstractions: AbstractionsBuilder::new(),
        }
    }

    pub fn flatten_module(node: AstNode, b: &mut NB) -> Result<Self> {
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
            let static_block_id = f.current_block_id();

            let block = f.blocks.get_block(static_block_id);
            let static_scope_id = block.scope_id;
            let static_scope = f.scopes.get_scope_mut(static_scope_id);
            static_scope.entry_block = Some(static_block_id);

            f.switch_blocks(static_block_id);
            f.push_start_block(
                static_scope_id,
                AstFuncType::new(AstType::Struct(vec![]), ReturnType::Single(AstType::Unit)).into(),
                Some(key),
                node.span_id,
                VarDefinitionSpace::Static,
            );

            f.static_block = Some(static_block_id);
            f.static_scope = Some(static_scope_id);
            f.switch_blocks(static_block_id);
            let _ = f.push_node(*body, b)?;
            assert_eq!(static_block_id, f.current_block_id());
            //f.drain_diagnostics(b);
            Ok(f)
        } else {
            b.push_error("Not a module", node.span_id);
            Err(Error::new(BlockifyError::Invalid))
        }
    }
}

impl<S: BlockState> Flatten<S> {
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

    pub fn list_variants_by_name(
        &self,
        start_scope_id: ScopeId,
        name: &StringKey,
    ) -> Vec<VariantId> {
        let mut out = vec![];
        for scope_id in self.scopes.walk_scopes(start_scope_id) {
            let scope = self.scopes.get_scope(scope_id);
            if let Some(e) = scope.entries.get(name) {
                for variant_id in e.iter() {
                    out.push(*variant_id);
                }
            }
        }
        out
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
        let scope = self.scopes.get_scope_mut(scope_id);
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
        for variant_id in self.list_variants_by_name(start_scope_id, name) {
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

    pub fn resolve_name_in_scope(&self, scope_id: ScopeId, name: StringKey) -> Option<LinkId> {
        // resolve scope through the tree, starting at the current scope
        for scope_id in self.scopes.walk_scopes(scope_id) {
            let scope = self.scopes.get_scope(scope_id);
            if let Some(data) = scope.names.get(&name) {
                return Some(data.clone());
            }
        }
        None
    }

    pub fn resolve_name(&self, block_id: BlockId, name: StringKey) -> Option<LinkId> {
        // resolve scope through the tree, starting at the current scope
        let block = self.blocks.get_block(block_id);
        self.resolve_name_in_scope(block.scope_id, name)
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
    ) -> Option<(ScopeId, AbstractionId)> {
        match self.resolve_lambda_scope(block_id, name.into()) {
            Some(scope_id) => {
                let scope = self.scopes.get_scope(scope_id);
                if let Some(abstraction_id) = scope.lambdas.get(&name.into()).cloned() {
                    //let a = self.abstractions.get(template_id);
                    //let (def, span_id, _) = self.get_ast_template(template_id).clone();
                    Some((scope_id, abstraction_id))
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
    ) -> Option<AbstractionId> {
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

    /*
    pub(super) fn drain_diagnostics(&mut self, b: &mut NB) {
        // XXX: This needs to be run before any errors kick in, there must be a better way.
        for (msg, span_id) in self.messages.drain(..) {
            b.push_error(&msg, span_id);
        }
    }
    */

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
        let scope_id = block.scope_id;
        //let target_field_types = ty.field_types();

        self.switch_blocks(block_id);
        let (_variant_id, _fun_scope_id, fun_block_id, _) =
            self.push_cps_block_with_type(name, scope_id, abstraction_id, &ty, span_id, b)?;

        self.scoped_continuations.connect(
            ContinuationFlow::Block(fun_block_id),
            ContinuationFlow::Variable(link_id),
            FlowEdge::BlockRef,
        );

        // now replace the abstraction code
        let entry = self.get_entry_mut(link_id);
        entry.code = LCode::Val(Literal::Block(fun_block_id));

        b.unify(&entry.ty, entry.span_id, &ty, span_id);
        self.switch_blocks(current_block_id);
        Ok(())
    }

    pub(super) fn finish_values(&mut self, b: &mut NB) -> Vec<LinkId> {
        let blocks = self.blocks.post_order_blocks();
        let mut values = vec![];

        for block_id in blocks.into_iter() {
            let block = self.blocks.get_block(block_id);
            let size = block.len();
            let scope_id = block.scope_id;
            if block.empty() {
                continue;
            }

            let entry_id = block.entry();

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
                    b.push_error(
                        &format!(
                            "Unterminated Block: {}, {:?}",
                            block_id,
                            (index, size, is_term, scope_type)
                        ),
                        entry.span_id,
                    );
                }

                let link_id = entry.link.unwrap();
                let value_id = ValueId::new(values.len() as u32);
                values.push(link_id);
                let entry = self.get_entry_mut(link_id);
                entry.value_id = Some(value_id);
                index += 1;
            }
        }
        values
    }

    /*
    pub(super) fn finish_block(&mut self, block_id: BlockId, _b: &mut NB) {
        // trying to walk the graph, this is a bit awkward
        // get block ordering
        //let blocks = self.blocks.post_order_blocks();
        //for block_id in blocks.into_iter() {
            //self.finish_block(block_id, b);
        //}
        let block = self.blocks.get_block(block_id);
        if block.entry.is_none() {
            return;
        }

        if block_id != self.static_block_id() {
            if let Some(last_link_id) = block.last() {
                let entry = self.get_entry(last_link_id);
                let (_ty, _targets) = match entry.code {
                    LCode::PlaceholderTerminal(_link_id) => {
                        let ty = self.get_type(last_link_id).clone();
                        (ty, vec![])
                    }
                    LCode::Switch(_, ref m) => {
                        let ty = self.get_type(last_link_id).clone();
                        let mut targets = m.iter().map(|block_id| *block_id).collect::<Vec<_>>();
                        targets.sort();
                        (ty, targets)
                    }
                    LCode::Jump(offset) => {
                        let ty = self.get_type(last_link_id).clone();
                        let targets = match offset {
                            CodeOffset::Block(block_id) => {
                                //let block = self.blocks.get_block(block_id);
                                //let entry = self.get_entry(block.entry.unwrap());
                                //let ty = entry.ty.clone();
                                vec![block_id]
                            }
                            _ => unreachable!(),
                        };
                        (ty, targets)
                    }
                    LCode::Branch(_, then_block_id, else_block_id) => {
                        let ty = self.get_type(last_link_id).clone();
                        (ty, vec![then_block_id, else_block_id])
                    }
                    LCode::Return => {
                        let ty = self.get_type(last_link_id).clone();
                        (ty, vec![])
                    }
                    LCode::Yield => {
                        let ty = self.get_type(last_link_id).clone();
                        (ty, vec![])
                    }
                    _ => unreachable!("{:?}", entry.code),
                };
            } else {
                unreachable!()
            }
        }
    }
    */

    pub(super) fn finish(mut self, b: &mut NB) -> Result<(Flatten<S>, Vec<LinkId>)> {
        // make sure all claims have been handled
        self.scopes.ensure_claims(b);

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

    pub fn insert_entry_after(&mut self, before_link_id: LinkId, entry: CodeEntry) -> LinkId {
        let before_entry = self.get_entry(before_link_id);
        println!(
            "insert0: {}, {}, {}",
            before_entry.prev, before_link_id, before_entry.next
        );
        let before_entry_next = before_entry.next;
        let next_link_id = self._insert_entry(entry, Some(before_link_id));

        // update the entry
        let entry = self.get_entry_mut(next_link_id);
        if before_entry_next == before_link_id {
            entry.next = next_link_id;
        } else {
            entry.next = before_entry_next;
        }
        println!("insert1: {}, {}, {}", entry.prev, next_link_id, entry.next);

        let before_entry = self.get_entry_mut(before_link_id);
        let block_id = before_entry.block_id;
        before_entry.next = next_link_id;
        println!(
            "insert2: {}, {}, {}",
            before_entry.prev, before_link_id, before_entry.next
        );
        self.blocks.get_block_mut(block_id).insert();
        next_link_id
    }

    pub fn insert_decl(&mut self, scope_id: ScopeId, mut entry: CodeEntry) -> LinkId {
        let scope = self.scopes.get_scope(scope_id);
        let entry_block_id = scope.entry_block.unwrap();
        entry.block_id = entry_block_id;
        let block = self.blocks.get_block_mut(entry_block_id);
        let last_decl = block.last_decl.unwrap();
        let link_id = self.insert_entry_after(last_decl, entry);
        println!("insert3: {:?}", self.blocks.get_block(entry_block_id));
        self.blocks.get_block_mut(entry_block_id).push_decl(link_id);
        println!("insert4: {:?}", self.blocks.get_block(entry_block_id));
        link_id
    }

    pub fn push_decl(&mut self, ty: AstType, name: StringKey, span_id: SpanId) -> LinkId {
        let block_id = self.current_block_id();
        let block = self.blocks.get_block(block_id);
        let scope = self.scopes.get_scope(block.scope_id);
        let entry_block_id = scope.entry_block.unwrap();

        let entry = CodeEntry::new(
            entry_block_id,
            LCode::Declare,
            ty,
            Some(name),
            span_id,
            VarDefinitionSpace::Default,
        );
        let block = self.blocks.get_block(entry_block_id);
        let scope_id = block.scope_id;
        //assert!(!block.is_term());
        let link_id = self.insert_decl(scope_id, entry);
        link_id
    }

    pub fn push_entry_with_link(&mut self, entry: CodeEntry) -> LinkId {
        let code = entry.code.clone();
        let block_id = entry.block_id;

        match &code {
            LCode::Label => {
                let link_id = self._insert_entry(entry, None);
                let block = self.blocks.get_block(block_id);
                if let Some(last_link_id) = block.last() {
                    let last_entry = self.get_entry_mut(last_link_id);
                    last_entry.next = link_id;
                }

                let block = self.blocks.get_block_mut(block_id);
                block.push_label(link_id);
                link_id
            }
            /*
            LCode::Declare => {
                //assert!(false);
                let scope_id = block.scope_id;
                //let scope = self.scopes.get_scope(scope_id);
                //let entry_block_id = scope.entry_block.unwrap();
                let link_id = self.insert_decl(scope_id, entry);
                //block.push_decl(link_id);
                link_id
            }
            */
            _ => {
                let block = self.blocks.get_block(block_id);
                let last = block.last();
                let link_id = self._insert_entry(entry, last);
                let block = self.blocks.get_block(block_id);
                if let Some(last_link_id) = block.last() {
                    let last_entry = self.get_entry_mut(last_link_id);
                    last_entry.next = link_id;
                }
                let block = self.blocks.get_block_mut(block_id);
                block.push_link(link_id, code.is_term());
                link_id
            }
        }
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

    pub fn push_sequence(
        &mut self,
        seq: Vec<AstNode>,
        span_id: SpanId,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        let block = self.blocks.get_block(self.current_block_id());
        let start_stack = self.scopes.walk_scopes(block.scope_id);

        for (_i, expr) in seq.into_iter().enumerate() {
            let _r = self.push_node(expr, b)?;
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
            LCode::Switch(_, _) => unreachable!(),
            LCode::PlaceholderTerminal(_) => unreachable!(),
            LCode::PlaceholderCodeReference => false,
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
        b: &mut NB,
    ) -> Vec<LinkId> {
        let mut updated_values = vec![];
        let block_id = self.current_block_id();
        let block = self.blocks.get_block(block_id);
        let scope_id = block.scope_id;
        for (maybe_key, v, ty, span_id) in values {
            let mut v = *v;
            let entry = self.get_entry(v);
            let v_block_id = entry.block_id;
            let v_block = self.blocks.get_block(v_block_id);
            let v_scope_id = v_block.scope_id;
            let v_scope = self.scopes.get_scope(v_scope_id);
            let v_entry_block_id = v_scope.entry_block.unwrap();
            let in_entry = v_entry_block_id == v_block_id;
            let in_block = v_block_id == block_id;

            let is_decl = if let LCode::Declare = entry.code {
                true
            } else {
                false
            };

            self.scopes
                .find_nearest_scope(v_scope_id, &[ScopeType::Function, ScopeType::Block]);
            assert!(self.scopes.is_in_scope(scope_id, v_scope_id));

            if !in_entry && !in_block && !is_decl {
                // checking if it's in entry is easier than checking if the block is dominant
                // This could be make more efficient.
                // get a link the value declaration in the scope entry
                println!(
                    "{}: {}{}=>{}{}, {}",
                    v, block_id, scope_id, v_block_id, v_scope_id, ty
                );
                let current_block_id = self.current_block_id();
                let key = b.labels.fresh_key("r");
                // create space on the stack in the entry block
                self.switch_blocks(v_entry_block_id);
                let decl_link_id = self.push_decl(ty.clone(), key, *span_id);
                self.switch_blocks(current_block_id);
                self.scopes
                    .make_stack_variable(v_scope_id, v, decl_link_id, ty.clone());

                self.insert_entry_after(
                    v,
                    CodeEntry::new(
                        block_id,
                        LCode::Store(decl_link_id, v),
                        ty.clone(),
                        None,
                        *span_id,
                        VarDefinitionSpace::Default,
                    ),
                );
                v = decl_link_id;
            }

            let out = if self.is_load_required(v) {
                let link_id = self.push_code(
                    LCode::Load(v),
                    ty.clone(),
                    *maybe_key,
                    *span_id,
                    VarDefinitionSpace::Reg,
                );
                (*maybe_key, link_id, ty, *span_id)
            } else {
                (*maybe_key, v, ty, *span_id)
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
        target_block_id: BlockId,
        jump_args: ArgVec,
        span_id: SpanId,
        b: &mut NB,
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

        let _field_types = arg_ty.field_types();

        let _link_ids = self.push_call_values(
            &jump_args
                .into_iter()
                .map(|(key, v, ty, span_id)| (key, v, ty, span_id))
                .collect::<Vec<_>>(),
            b,
        );

        //println!(
        //"jump to: {}{}=>{}{}",
        //current_scope_id,
        //self.current_block_id(),
        //target_scope_id,
        //target_block_id
        //);
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
        // Add links
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
        let ret_ty = b.types.r(def.return_type).clone();
        let blocks = vec![];
        let (args, _) =
            Self::calculate_function_arguments(&def, &args, &blocks, def_span_id, call_span_id, b)?;

        let call_values = self.push_call_arguments(args, call_span_id, b)?;
        let _call_ty = argvec_type(&call_values);

        let current_block_id = self.current_block_id();

        // Add links
        self.push_call_values(&call_values, b);

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
        if let AstType::Func(f) = &block_ty {
            assert!(f.args.is_composite());

            let mut v_args = vec![];
            for (i, (name, ty)) in f.args.fields().iter().enumerate() {
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
                self.scoped_continuations.connect(
                    ContinuationFlow::BlockArg(self.current_block_id(), i as u8),
                    ContinuationFlow::Variable(link_id),
                    FlowEdge::BlockArg,
                );
            }
            v_args
        } else {
            unreachable!("{:?}", block_ty)
        }
    }

    pub(super) fn push_start_block(
        &mut self,
        scope_id: ScopeId,
        block_ty: AstType,
        name: Option<StringKey>,
        span_id: SpanId,
        mem: VarDefinitionSpace,
    ) -> (LinkId, ArgVec) {
        let block_link_id = self.push_empty_label(span_id);
        let v_args = self.push_start_block_args(scope_id, block_ty.clone(), span_id);
        self.replace_label(block_link_id, block_ty, name, span_id, mem);
        self.block_links
            .insert(self.current_block_id(), block_link_id);
        let block = self.blocks.get_block_mut(self.current_block_id());
        block.last_decl = block.last();
        (block_link_id, v_args)
    }

    /*
    pub fn save_ast_template_caller(&mut self, abs_id: AbstractionId, block_id: BlockId) {
        let a = self.abstractions.get_mut(abs_id);
        a.caller_blocks.insert(block_id);
    }
    */

    pub fn save_ast_template(
        &mut self,
        block_id: BlockId,
        name: &StringKey,
        def: &Lambda,
        span_id: SpanId,
    ) -> Result<AbstractionId> {
        let template_id = self.abstractions.add(def.clone(), span_id);
        let block = self.blocks.get_block(block_id);
        let scope_id = block.scope_id;
        let scope = self.scopes.get_scope_mut(scope_id);
        scope.lambdas.insert(name.into(), template_id);
        Ok(template_id)
    }

    pub fn push_close_block(&mut self, span_id: SpanId, b: &mut NB) -> Result<FlattenResult> {
        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        let scope_id = block.scope_id;
        let scope = self.scopes.get_scope(scope_id);
        if let Some(loop_block) = scope.loop_block {
            let link_id = self.maybe_terminate_block(loop_block.start_block, span_id, b);
            self.switch_blocks(loop_block.next_block);
            Ok(FlattenResult::link(link_id))
        } else {
            let block_id = scope.entry_block.unwrap();
            let block = self.blocks.get_block(block_id);
            Ok(FlattenResult::link(block.last().unwrap()))
        }
    }

    pub fn dump_position(&self) {
        let block_id = self.current_block_id();
        let block = self.blocks.get_block(block_id);
        let scope_id = block.scope_id;
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
        if let ReturnType::Single(ret_ty) = &def_func_type.ret {
            AstFuncType::new(
                b.types.refresh(def_func_type.args.clone()),
                ReturnType::Single(b.types.refresh(ret_ty.clone())),
            )
        } else {
            unreachable!()
        }
    }

    pub fn remove_placeholder_terminal(&mut self, goto_block_id: BlockId) {
        let block = self.blocks.get_block(goto_block_id);
        let last_link_id = block.last().unwrap();
        let entry = self.get_entry_mut(last_link_id);
        if let LCode::PlaceholderTerminal(prev_link_id) = entry.code {
            // invalidate dummy jump
            entry.next = prev_link_id;
            let block = self.blocks.get_block_mut(goto_block_id);
            // remove last entry in the block
            block.replace_terminal(prev_link_id);
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
        let last_link_id = block.last().unwrap();

        for block_id in &target_block_ids {
            self.blocks
                .block_succ(self.current_block_id(), *block_id, Successor::Jump);
            self.blocks
                .block_succ(self.current_block_id(), *block_id, Successor::BlockScope);
        }

        println!("replace: {}=>{:?}", last_link_id, target_block_ids);
        let entry = self.get_entry(last_link_id);

        let code = if let LCode::PlaceholderTerminal(_) = entry.code {
            if target_block_ids.len() == 1 {
                let block_id = target_block_ids.last().unwrap();
                Some(LCode::Jump(block_id.into()))
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
                b.push_error("Missing Targets", entry.span_id);
                None
                //unreachable!();
            }
        } else {
            unreachable!();
        };
        if let Some(code) = code {
            let entry = self.get_entry_mut(last_link_id);
            println!("replace: {} {:?}=>{:?}", last_link_id, entry.code, code);
            entry.code = code;
        }

        last_link_id
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
                self.push_jump(scope.return_block.unwrap().into(), jump_args, span_id, b);
                Ok(FlattenResult::statement())
            }

            Ast::Literal(lit) => {
                self.ensure_open(span_id, b);
                // literal is expression, non-terminal
                let ty: AstType = match &lit {
                    Literal::Block(_block_id) => b.types.fresh_unknown(),
                    Literal::Link(_link_id) => b.types.fresh_unknown(),
                    _ => lit.clone().into(),
                };
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
                let scope_id = block.scope_id;

                // resolve identifier lexically
                if let Some(def_link_id) = self.resolve_name(current_block_id, key) {
                    let link_id = def_link_id;
                    return Ok(FlattenResult::link(link_id));
                }

                // we are resolving the abstraction lexically here, but it could also be defined
                // later.  TODO: if we don't find it, it might be defined later, so we should defer
                // and throw the error later if it's not found.
                if let Some(abstraction_id) = self.resolve_template(scope_id, key.into()) {
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

                    // save the template
                    let def_span_id = expr.span_id;
                    let _ = self.save_ast_template(current_block_id, &name, &def, def_span_id)?;
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
                let scope_id = block.scope_id;

                let offset_decl = if let Some(v_decl) = self.resolve_name_in_scope(scope_id, name) {
                    // already declared
                    let decl_entry = self.get_entry(v_decl);
                    b.unify(&decl_entry.ty, decl_entry.span_id, &expr_ty, expr_span_id);
                    v_decl
                } else {
                    // need to declare it
                    let scope = self.scopes.get_scope(scope_id);
                    let entry_block_id = scope.entry_block.unwrap();
                    let _current_block_id = self.current_block_id();
                    //let link_id = if current_block_id == entry_block_id {
                    let block = self.blocks.get_block(self.current_block_id());
                    let scope_id = block.scope_id;
                    //let link_id = self.push_decl(expr_ty.clone(), name, node.span_id);

                    // TODO: switch this over to the new method
                    let link_id = if true {
                        self.push_code(
                            LCode::Declare,
                            expr_ty.clone(),
                            Some(name),
                            node.span_id,
                            VarDefinitionSpace::Default,
                        )
                    } else {
                        self.switch_blocks(entry_block_id);
                        let link_id = self.push_decl(expr_ty.clone(), name, node.span_id);
                        println!("link_id1: {}{}", scope_id, link_id);
                        self.switch_blocks(current_block_id);
                        link_id
                    };
                    println!("link_id2: {}{}", scope_id, link_id);
                    //link_id
                    /*
                                        } else {
                                        };

                    */
                    self.scopes.scope_define(scope_id, name, link_id);
                    link_id
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

                self.scoped_continuations.connect(
                    ContinuationFlow::Variable(load_link_id),
                    ContinuationFlow::Variable(offset_decl),
                    FlowEdge::Store,
                );

                let link_id = self.push_code(
                    LCode::Store(offset_decl, load_link_id),
                    AstType::Unit,
                    None,
                    node.span_id,
                    VarDefinitionSpace::Default,
                );
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
                        if let Some((scope_id, abstraction_id)) =
                            self.resolve_lambda(current_block_id, *ident)
                        {
                            self.push_call(*ident, scope_id, abstraction_id, span_id, args, b)
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
                let term = block.is_term();
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
                // only jump if we are in an open block
                if !term {
                    self.blocks
                        .block_succ(current_block_id, then_block_id, Successor::BlockScope);

                    self.blocks
                        .block_succ(current_block_id, then_block_id, Successor::Jump);
                }

                let branch_block_type = AstFuncType {
                    args: AstType::Struct(vec![]).into(),
                    ret: ReturnType::Single(AstType::Unit).into(),
                };

                let name = b.labels.fresh_key("then");
                self.switch_blocks(then_block_id);
                self.push_start_block(
                    then_scope_id,
                    branch_block_type.clone().into(),
                    Some(name),
                    then_span_id,
                    VarDefinitionSpace::Reg,
                );
                self.switch_blocks(then_block_id);
                let _ = self.push_node(NB::ensure_seq(*then_expr), b)?;
                self.maybe_terminate_block(v_next, span_id, b);

                // ELSE
                let else_block_id = if let Some(else_expr) = maybe_else_expr {
                    let (else_block_id, else_scope_id) =
                        self.new_scope_and_block(ScopeType::Block, parent_scope_id);
                    let else_span_id = else_expr.span_id;
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
                        branch_block_type.into(),
                        Some(name),
                        else_span_id,
                        VarDefinitionSpace::Reg,
                    );

                    self.switch_blocks(else_block_id);
                    let _ = self.push_node(NB::ensure_seq(*else_expr), b)?;
                    self.maybe_terminate_block(v_next, span_id, b);
                    else_block_id
                } else {
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
                self.scoped_continuations.connect(
                    ContinuationFlow::Jump(v),
                    ContinuationFlow::Block(then_block_id),
                    FlowEdge::CondThen,
                );
                self.scoped_continuations.connect(
                    ContinuationFlow::Jump(v),
                    ContinuationFlow::Block(else_block_id),
                    FlowEdge::CondElse,
                );
                self.switch_blocks(v_next);
                Ok(FlattenResult::link(v))
            }

            Ast::ControlFlowMarker(ControlFlowMarker::BlockReference(expr)) => {
                let (_variant_id, block_id) = match &expr.node {
                    Ast::Identifier(key) => {
                        let key = *key;
                        let ty = AstType::func(vec![], AstType::Unit);
                        //let func_ty = ty.get_func();
                        let scope_id = block.scope_id;
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
                let scope_id = block.scope_id;

                // check for duplicates
                if let Some(block_id) = self.resolve_label(scope_id, name.into()) {
                    unimplemented!("duplicate label: {}", block_id);
                }

                // create a new block
                assert_eq!(0, args.len());
                let new_block_id = self.blocks.new_block(scope_id);
                self.blocks.block_succ(
                    self.current_block_id(),
                    new_block_id,
                    Successor::BlockScope,
                );
                let scope = self.scopes.get_scope_mut(scope_id);
                scope.block_labels.insert(name.into(), new_block_id);

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

                self.switch_blocks(new_block_id);
                let (link_id, _) = self.push_start_block(
                    new_scope_id,
                    AstFuncType {
                        args: arg_ty.clone().into(),
                        ret: ReturnType::Single(AstType::Unit).into(),
                    }
                    .into(),
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
                let current_block_id = self.current_block_id();

                let branch_block_type = AstFuncType {
                    args: AstType::Struct(vec![]).into(),
                    ret: ReturnType::Single(AstType::Unit).into(),
                };

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
                    branch_block_type.clone().into(),
                    Some(name),
                    then_span_id,
                    VarDefinitionSpace::Reg,
                );

                self.switch_blocks(then_block_id);
                let r = self.push_node(then_ast, b)?;
                let then_link_id = r.link_id.unwrap();
                let then_ty = self.get_type(then_link_id).clone();

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
                    branch_block_type.into(),
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
                let parent_scope_id = block.scope_id;
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
                                acc_types.push(ty2.clone());
                            }

                            let label = b.labels.fresh_key("chain");
                            let v_next = self.blocks.new_block(parent_scope_id);
                            self.switch_blocks(v_next);
                            self.push_start_block(
                                parent_scope_id,
                                AstType::func(acc_types, AstType::Unit),
                                Some(label),
                                span_id,
                                VarDefinitionSpace::Default,
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
                let parent_scope_id = block.scope_id;

                let (loop_block_id, loop_scope_id) =
                    self.new_scope_and_block(ScopeType::Region, parent_scope_id);

                //let (v_next, next_scope_id) = self.new_scope_and_block(ScopeType::Block, parent_scope_id);
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
                    AstFuncType {
                        args: AstType::Struct(vec![]).into(),
                        ret: ReturnType::Single(AstType::Unit).into(),
                    }
                    .into(),
                    Some(key),
                    span_id,
                    VarDefinitionSpace::Reg,
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
                let scope_id = block.scope_id;

                // loop up loop blocks by name
                if let Some(loop_scope) = self.scopes.get_loop_scope(scope_id, maybe_key) {
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
                let scope_id = block.scope_id;

                // args not implemented yet
                assert_eq!(args.len(), 0);
                // loop up loop blocks by name
                if let Some(loop_scope) = self.scopes.get_loop_scope(scope_id, maybe_name) {
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
                let scope_id = block.scope_id;
                // loop up loop blocks by name
                if let Some(loop_scope) = self.scopes.get_loop_scope(scope_id, maybe_key) {
                    self.switch_blocks(current_block_id);
                    let _link_id =
                        self.push_jump(loop_scope.next_block.into(), vec![], node.span_id, b);

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
        //let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(self.current_block_id());
        let scope_id = block.scope_id;
        if block.is_term() {
            let new_block_id = self.blocks.new_block(scope_id);
            let name = b.labels.fresh_key("dead");
            let scope = self.scopes.get_scope(scope_id);
            self.blocks.block_succ(
                scope.entry_block.unwrap(),
                new_block_id,
                Successor::BlockScope,
            );

            self.switch_blocks(new_block_id);
            self.push_start_block(
                scope_id,
                AstFuncType::new(AstType::Struct(vec![]), ReturnType::Single(AstType::Unit)).into(),
                Some(name),
                span_id,
                VarDefinitionSpace::Reg,
            );
        }
    }

    pub fn maybe_terminate_block(
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
            self.blocks
                .block_succ(self.current_block_id(), v_next, Successor::BlockScope);
        }
        link_id
    }
}
