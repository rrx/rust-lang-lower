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
    NaryOperation,
    ReturnType,
    //Literal,
    //ParameterNode,
    SpanId,
    StringKey,
    //UnaryOperation,
    VarDefinitionSpace,
};
use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use std::collections::{HashMap, HashSet};

use std::convert::From;
use std::convert::Into;

use crate::{
    BlockId, BlockifyError, Builtin, CodeOffset, FlattenEnvironment, LCode, LinkId,
    NodeBuilder as NB, ScopeId, ScopeLayer, ScopeType, SequenceReader, StringLabel, Successor,
    TemplateId,
};

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
pub struct CodeEntry {
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
    pub(super) scope_id: ScopeId,
    pub(super) dead: bool,
    num_ret_args: HashSet<usize>,
    ret_types: HashSet<AstType>,
    pub(super) next: Option<BlockId>,
    pub(super) links: Vec<LinkId>,
}

impl IRBlock {
    pub fn new(scope_id: ScopeId) -> Self {
        Self {
            scope_id,
            dead: false,
            //ast,
            links: vec![],
            next: None,
            num_ret_args: HashSet::new(),
            ret_types: HashSet::new(),
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

pub struct Flatten {
    block_id: BlockId,
    module_key: Option<StringKey>,
    pub(super) link: LinkOptions,
    entries: Vec<CodeEntry>,
    pub(super) gblocks: BlockGraph,
    ast_templates: Vec<Lambda>,
    messages: Vec<(String, SpanId)>,
}

impl Flatten {
    pub fn new(fenv: &mut FlattenEnvironment) -> Self {
        let scope_id = Self::new_scope(ScopeType::Static, fenv);
        let ir_block = IRBlock::new(scope_id);
        let mut gblocks = BlockGraph::new();
        let index = gblocks.add_node(ir_block);
        let block_id = BlockId(index.index() as u32);

        Self {
            block_id,
            module_key: None,
            entries: vec![],
            gblocks,
            link: LinkOptions::new(),
            ast_templates: vec![],
            messages: vec![],
        }
    }

    pub fn switch_blocks(&mut self, block_id: BlockId) {
        self.block_id = block_id;
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
    ) -> Option<LinkId> {
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

    pub fn resolve_declaration(
        &self,
        block_id: BlockId,
        name: StringKey,
        fenv: &FlattenEnvironment,
    ) -> Option<LinkId> {
        // resolve scope through the tree, starting at the current scope
        let block = self.get_block(block_id);
        for scope_id in fenv.walk_scopes(block.scope_id) {
            let scope = fenv.get_scope(scope_id);
            if let Some(data) = scope.declarations.get(&name) {
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

    pub fn flatten_module(
        node: AstNode,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<Self> {
        let mut f = Self::new(fenv);
        if let Ast::Module(key, body) = node.node {
            f.module_key = Some(key);

            let block = f.get_block(f.block_id);
            let static_scope_id = block.scope_id;
            let static_scope = fenv.get_scope_mut(static_scope_id);
            static_scope.entry_block = Some(f.block_id);

            let top_block_id = f.block_id;
            f.switch_blocks(f.block_id);
            f.push_start_block(
                static_scope_id,
                AstType::Func(
                    AstType::Struct(vec![]).into(),
                    ReturnType::Single(AstType::Unit).into(),
                ),
                Some(key),
                node.span_id,
                VarDefinitionSpace::Static,
                fenv,
            );

            fenv.static_block = Some(f.block_id);
            fenv.static_scope = Some(static_scope_id);
            for ast in body.to_vec() {
                f.switch_blocks(top_block_id);
                let r = f.push_node(ast, fenv, b)?;
                assert_eq!(f.block_id, r.block_id);
                //f.block_id = r.block_id;
            }
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

    pub fn push_bake_main(&mut self, fenv: &mut FlattenEnvironment, b: &mut NB) -> Result<LinkId> {
        let current_block_id = self.block_id;
        let name = b.labels.s("main");
        // reset the block position before each function
        // main is always static context
        self.switch_blocks(fenv.static_block_id());
        self.push_bake_template(name, None, fenv, b)?;
        //self.block_id = block_id;
        self.switch_blocks(fenv.static_block_id());
        let r = self.push_bake(name, None, fenv, b);
        // switch back after bake
        self.switch_blocks(current_block_id);
        r
    }

    pub fn push_bake_all(
        &mut self,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<Vec<LinkId>> {
        let static_block_id = fenv.static_block_id();
        let scope_id = fenv.static_scope_id();
        let scope = fenv.get_scope(scope_id);
        let keys = scope
            .declarations
            .iter()
            .map(|s| s.0.clone())
            .collect::<Vec<_>>();

        let mut links = vec![];
        for key in keys.iter() {
            // reset the block position before each function
            self.switch_blocks(static_block_id);
            let link_id = self.push_bake(*key, None, fenv, b)?;
            links.push(link_id);
        }
        Ok(links)
    }

    fn _insert_entry(&mut self, mut entry: CodeEntry) -> LinkId {
        let index = self.entries.len();
        let link_id = LinkId(index as u32);
        entry.link = Some(link_id);
        self.entries.push(entry);
        link_id
    }

    pub fn push_entry_with_link(&mut self, entry: CodeEntry) -> LinkId {
        let block_id = entry.block_id;
        let span_id = entry.span_id;
        let link_id = self._insert_entry(entry);
        let block = self.get_block(block_id);
        if let Some(last_link_id) = block.links.last() {
            let last_entry = self.get_entry(*last_link_id);
            let is_term = last_entry.code.is_term();
            if is_term {
                let backtrace = std::backtrace::Backtrace::capture();
                self.messages.push((
                    format!("appending to term block={}\n{}", block_id, backtrace),
                    span_id,
                ));
            }
        }
        self.get_block_mut(block_id).push(link_id);
        link_id
    }

    pub fn new_scope_and_block(
        &mut self,
        scope_type: ScopeType,
        parent_scope_id: ScopeId,
        fenv: &mut FlattenEnvironment,
    ) -> (BlockId, ScopeId) {
        let scope_id = Self::new_scope(scope_type, fenv);
        let scope = fenv.get_scope_mut(scope_id);
        let block_id = self.new_block(scope_id);
        scope.entry_block = Some(block_id);
        fenv.scope_succ(parent_scope_id, scope_id);
        //println!("new block and scope: {:?}", (block_id, scope_id));
        (block_id, scope_id)
    }

    fn new_scope(scope_type: ScopeType, fenv: &mut FlattenEnvironment) -> ScopeId {
        let scope = ScopeLayer::new(scope_type);
        let index = fenv.scopes.add_node(scope);
        ScopeId(index.index() as u32)
    }

    pub fn new_block(&mut self, scope_id: ScopeId) -> BlockId {
        let ir_block = IRBlock::new(scope_id);
        let index = self.gblocks.add_node(ir_block);
        //println!("new block: {:?}", (block_id, scope_id));
        if index.index() > 0 && scope_id.index() == 0 {
            assert!(false);
        }
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

    pub fn get_type(&self, link_id: LinkId) -> &AstType {
        &self.get_entry(link_id).ty
    }

    pub fn get_entry_mut(&mut self, link_id: LinkId) -> &mut CodeEntry {
        self.entries.get_mut(link_id.index()).unwrap()
    }

    pub fn insert_ast_template(&mut self, def: Lambda) -> TemplateId {
        let offset = self.ast_templates.len();
        self.ast_templates.push(def);
        TemplateId(offset as u32)
    }

    pub fn get_ast_template(&self, template_id: TemplateId) -> &Lambda {
        self.ast_templates.get(template_id.index()).unwrap()
    }

    pub fn push_sequence(
        &mut self,
        seq: Vec<AstNode>,
        seq_span_id: SpanId,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        let mut ty = AstType::Unit;
        let mut link_id = None;
        let mut is_term = false;

        let mut current_span_id = seq_span_id;

        let block = self.get_block(self.block_id);
        let seq_next_block_id = block.next;
        let scope_id = block.scope_id;

        let mut r = SequenceReader::new();
        let mut seq = r.build(seq.clone(), b);

        for expr in seq.iter() {
            match &expr.node {
                Ast::Block(key, args, _body) => {
                    if fenv.resolve_block_id(scope_id, key.into()).is_none() {
                        assert_eq!(0, args.len());
                        let new_block_id = self.new_block(scope_id);
                        let new_block = self.get_block_mut(new_block_id);
                        new_block.next = seq_next_block_id;
                        self.block_succ(self.block_id, new_block_id, Successor::BlockScope);
                        let scope = fenv.get_scope_mut(scope_id);
                        scope.block_labels.insert(key.into(), new_block_id);
                        //println!("creating block: {} in {}", b.labels.r(key.into()), scope_id);
                    }
                }
                _ => (),
            }
        }

        let mut d = seq.drain(..);
        loop {
            if let Some(expr) = d.next() {
                let span_id = expr.span_id;
                current_span_id = span_id;
                let expr_is_term = expr.node.is_term();
                let is_last = d.len() == 0;

                if expr_is_term && !is_last {
                    let next_seq = d.collect::<Vec<_>>();
                    let next_node = next_seq.first().unwrap();
                    let next_span_id = next_node.span_id;
                    let current_block_id = self.block_id;
                    let new_block_id = match &next_node.node {
                        Ast::Block(key, _, _) => {
                            let new_block_id = fenv.resolve_block_id(scope_id, key.into()).unwrap();
                            new_block_id
                        }
                        _ => {
                            let new_block_id = self.new_block(scope_id);
                            //println!("term new: {:?}", (new_block_id, &next_node));
                            self.switch_blocks(new_block_id);
                            self.push_start_block(
                                scope_id,
                                AstType::Func(
                                    AstType::Struct(vec![]).into(),
                                    ReturnType::Single(AstType::Unit).into(),
                                ),
                                Some(b.labels.fresh_key("new")),
                                next_node.span_id,
                                VarDefinitionSpace::Default,
                                fenv,
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
                    self.switch_blocks(current_block_id);
                    let r = self.push_node(expr, fenv, b)?;
                    assert_eq!(self.block_id, r.block_id);

                    // flatten next
                    let next_node = AstNode {
                        node: Ast::Sequence(next_seq),
                        span_id: next_span_id,
                    };
                    //println!("next: {:?}", (&next_node));
                    self.switch_blocks(new_block_id);
                    let r = self.push_node(next_node, fenv, b)?;
                    assert_eq!(self.block_id, r.block_id);
                    //println!("next2: {:?}", (&r));
                    return Ok(r);
                }

                // handle expr
                let r = self.push_node(expr, fenv, b)?;
                assert_eq!(self.block_id, r.block_id);
                ty = r.ty;
                link_id = r.link_id;
                is_term = r.is_term;
            } else {
                break;
            }
        }

        if !is_term {
            let block = self.get_block(self.block_id);
            if let Some(next) = block.next {
                println!("adding term on block: {}, jump: {}", self.block_id, next);
                let jump_link_id = self.push_jump(next.into(), vec![], current_span_id);
                link_id = Some(jump_link_id);
            } else {
                println!("missing term on block: {}", self.block_id);
                b.push_error(
                    &format!("Missing next block on block_id={}", self.block_id),
                    current_span_id,
                );
            }
        }

        Ok(FlattenResult::new(self.block_id, link_id, ty, is_term))
    }

    pub fn push_return(&mut self, link_ids: Vec<(LinkId, AstType)>, span_id: SpanId) -> LinkId {
        for (link_id, ty) in link_ids.iter() {
            self.push_code(
                LCode::CallValue((*link_id).into()),
                ty.clone(),
                None,
                span_id,
                VarDefinitionSpace::Reg,
            );
        }

        self.push_code(
            LCode::Return,
            AstType::Unit,
            None,
            span_id,
            VarDefinitionSpace::Reg,
        )
    }

    pub fn push_return_block(
        &mut self,
        scope_id: ScopeId,
        return_type: AstType,
        span_id: SpanId,
        fenv: &mut FlattenEnvironment,
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
            fenv,
        );
        self.push_return(v_args, span_id);
    }

    pub fn push_jump(
        &mut self,
        target_id: CodeOffset,
        jump_args: Vec<(Option<StringKey>, LinkId, AstType)>,
        span_id: SpanId,
    ) -> LinkId {
        for (key, link_id, ty) in jump_args.iter() {
            self.push_code(
                LCode::CallValue(link_id.into()),
                ty.clone(),
                key.clone(),
                span_id,
                VarDefinitionSpace::Reg,
            );
        }

        if let CodeOffset::Block(target_block_id) = target_id {
            self.block_succ(self.block_id, target_block_id, Successor::Jump);
        } else {
            unimplemented!()
        }

        let ty = AstType::Struct(
            jump_args
                .iter()
                .map(|j| (j.0, j.2.clone()))
                .collect::<Vec<_>>(),
        );

        self.push_code(
            LCode::Jump(target_id.into()),
            AstType::Func(ty.into(), ReturnType::Single(AstType::Unit).into()),
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
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<(
        BlockId,
        AstType,
        Vec<(Option<StringKey>, LinkId, AstType)>,
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
                    AstType::Args(_) => {
                        Argument::Args(field_key, args_seq.clone()) //value_map.remove(&field_key).unwrap().into())
                    }
                    AstType::KwArgs(_) => {
                        Argument::KwArgs(field_key, kwargs_map.clone()) //NB::index())//value_map.remove(&field_key).unwrap().into())
                    }
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

        let mut values = vec![];
        let mut current_block_id = self.block_id;
        let mut link_ids = vec![];
        //let mut has_kwargs = false;
        // block may have changed so we use the new block returned from the
        // args
        //println!("start");
        for a in args.into_iter() {
            match a {
                Argument::Positional(expr) => {
                    self.switch_blocks(current_block_id);
                    let r = self.push_node(*expr, fenv, b)?;
                    assert_eq!(self.block_id, r.block_id);
                    current_block_id = r.block_id;
                    let link_id = r.link_id.unwrap();
                    values.push((None, link_id, r.ty.clone()));
                    link_ids.push(link_id);
                }
                Argument::Named(key, expr) => {
                    self.switch_blocks(current_block_id);
                    let r = self.push_node(*expr, fenv, b)?;
                    assert_eq!(self.block_id, r.block_id);
                    current_block_id = r.block_id;
                    let link_id = r.link_id.unwrap();
                    values.push((Some(key), link_id, r.ty.clone()));
                    link_ids.push(link_id);
                }
                Argument::Args(key, exprs) => {
                    let mut args_values = vec![];
                    for expr in exprs {
                        self.switch_blocks(current_block_id);
                        let r = self.push_node(expr, fenv, b)?;
                        assert_eq!(self.block_id, r.block_id);
                        current_block_id = r.block_id;
                        let link_id = r.link_id.unwrap();
                        args_values.push((link_id, r.ty.clone()));
                    }

                    for (link_id, ty) in args_values.iter() {
                        self.push_code(
                            LCode::CallValue(link_id.into()),
                            ty.clone(),
                            None,
                            span_id,
                            VarDefinitionSpace::Reg,
                        );
                    }

                    let struct_ty = AstType::Struct(
                        args_values
                            .iter()
                            .map(|v| (None, v.1.clone()))
                            .collect::<Vec<_>>(),
                    );
                    let link_id = self.push_code(
                        LCode::NaryOp(NaryOperation::Struct),
                        struct_ty.clone(),
                        None,
                        span_id,
                        VarDefinitionSpace::Stack,
                    );
                    values.push((Some(key), link_id, struct_ty.clone()));
                    link_ids.push(link_id);
                }
                Argument::KwArgs(key, _expr) => {
                    let node: AstNode = 1.into();
                    self.switch_blocks(current_block_id);
                    let r = self.push_node(node, fenv, b)?;
                    assert_eq!(self.block_id, r.block_id);
                    current_block_id = r.block_id;
                    let link_id = r.link_id.unwrap();
                    values.push((Some(key), link_id, r.ty.clone()));
                    link_ids.push(link_id);
                }
            }
        }

        let call_ty = AstType::Struct(
            values
                .iter()
                .map(|v| (v.0, v.2.clone()))
                .collect::<Vec<_>>(),
        );

        if b.types.u.unify(&func_arg, &call_ty).is_err() {
            b.push_error(
                &format!("5-Type Mismatch: func: {}, call: {}", &func_arg, &call_ty),
                span_id,
            );
        }

        //let _call_type_id = b.types.s(&call_ty);
        //println!("blocks: {:?}", (block_id, current_block_id));
        Ok((current_block_id, ret.clone(), values, call_ty))
    }

    fn push_call_by_name(
        &mut self,
        name: StringKey,
        args: Vec<Argument>,
        span_id: SpanId,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        let current_block_id = self.block_id;
        // look up the lambda
        // If the lambda is in the static scope, we do a normal call
        // If it's in a non-static scope, then we bake a lambda and jump to it
        // If we wanted to so some inlining, we just have to switch to doing lambdas instead
        if let Some((scope_id, def)) = self.find_lambda(current_block_id, name, fenv) {
            //let current_block_id = self.block_id;
            let (current_block_id, ret_ty, call_values, call_ty) =
                self.push_function_args(&def, args, span_id, fenv, b)?;

            // function type, based on the caller
            let func_ty = AstType::func(
                call_ty.fields().iter().map(|(_, ty)| ty.clone()).collect(),
                ret_ty.clone(),
            );
            println!("call ty: {}, {}", call_ty, func_ty);

            let def_func_ty = def_to_type(&def, b);
            if b.types.u.unify(&func_ty, &def_func_ty).is_err() {
                b.push_error(
                    &format!("Type Mismatch: caller: {}, def: {}", &call_ty, &def_func_ty),
                    span_id,
                );
            }

            let is_static = fenv.static_scope_id() == scope_id;
            if is_static {
                // if it's defined in static scope, just call it
                let v_decl = if let Some(v_decl) = self.resolve_name(current_block_id, name, fenv) {
                    v_decl
                } else {
                    // if it's not already baked, we need to do that here
                    self.block_id = fenv.static_block_id(); //block_id;
                    let v_decl = self.push_bake(name, None, fenv, b)?;
                    v_decl
                };

                self.switch_blocks(current_block_id);
                self.push_function_call(v_decl, call_values, ret_ty, span_id)
            } else {
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
                self.switch_blocks(current_block_id);
                let (fun_block_id, next_block_id, next_link_id) =
                    self.push_bake_lambda(name, None, span_id, fenv, b)?;
                self.switch_blocks(next_block_id);

                // Lambda Block
                self.block_succ(current_block_id, fun_block_id, Successor::BlockScope);

                // now that we have the arguments calculated, and the lambda baked, jump!
                self.switch_blocks(current_block_id);
                self.push_jump(fun_block_id.into(), call_values, span_id);
                self.switch_blocks(next_block_id);

                // block termination
                Ok(FlattenResult::new(
                    next_block_id,
                    Some(next_link_id),
                    ret_ty,
                    true,
                ))
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
        let entry = CodeEntry::new(self.block_id, code, ty, name, span_id, mem);
        self.push_entry_with_link(entry)
    }

    pub fn push_function_call(
        &mut self,
        v_fun: LinkId,
        values: Vec<(Option<StringKey>, LinkId, AstType)>,
        ret_ty: AstType,
        span_id: SpanId,
    ) -> Result<FlattenResult> {
        let current_block_id = self.block_id;
        // Add links
        for (key, link_id, ty) in values {
            self.push_code(
                LCode::CallValue(link_id.into()),
                ty,
                key,
                span_id,
                VarDefinitionSpace::Reg,
            );
        }

        // Make call
        let link_id = self.push_code(
            LCode::Call(v_fun.into()),
            ret_ty.clone(),
            None,
            span_id,
            VarDefinitionSpace::Default,
        );

        Ok(FlattenResult::new(
            current_block_id,
            Some(link_id),
            ret_ty,
            false,
        ))
    }

    pub fn push_builtin_call(
        &mut self,
        def: &Lambda,
        id: BuiltinId,
        args: Vec<Argument>,
        span_id: SpanId,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        let (current_block_id, ret_ty, values, _call_ty) =
            self.push_function_args(&def, args, span_id, fenv, b)?;

        // Add links
        for (key, link_id, ty) in values {
            self.push_code(
                LCode::CallValue(link_id.into()),
                ty,
                key,
                span_id,
                VarDefinitionSpace::Reg,
            );
        }

        let link_id = self.push_code(
            LCode::Builtin(id),
            ret_ty.clone(),
            None,
            span_id,
            VarDefinitionSpace::Default,
        );
        self.switch_blocks(current_block_id);
        Ok(FlattenResult::new(
            current_block_id,
            Some(link_id),
            ret_ty,
            false,
        ))
    }

    fn push_start_block(
        &mut self,
        scope_id: ScopeId,
        block_ty: AstType,
        name: Option<StringKey>,
        span_id: SpanId,
        mem: VarDefinitionSpace,
        fenv: &mut FlattenEnvironment,
    ) -> (LinkId, Vec<(LinkId, AstType)>) {
        //println!("start block: {:?}", (&block_ty));
        let block_link_id = self.push_code(LCode::Label, block_ty.clone(), name, span_id, mem);
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
                v_args.push((link_id, ty.clone()));
                if let Some(name) = name {
                    fenv.scope_define(scope_id, *name, link_id.into());
                }
            }
            (block_link_id, v_args)
        } else {
            unreachable!()
        }
    }

    pub fn insert_code_template(
        &mut self,
        scope_id: ScopeId,
        key: StringKey,
        link_id: LinkId,
        fenv: &mut FlattenEnvironment,
    ) {
        let scope = fenv.get_scope_mut(scope_id);
        scope.templates.insert(key.into(), link_id);
    }

    pub fn save_ast_template(
        &mut self,
        block_id: BlockId,
        name: &StringKey,
        def: &Lambda,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<()> {
        let template_id = self.insert_ast_template(def.clone());
        let block = self.get_block(block_id);
        let scope_id = block.scope_id;
        let scope = fenv.get_scope_mut(scope_id);
        scope.lambdas.insert(name.into(), template_id);
        Ok(())
    }

    fn push_bake_function(
        &mut self,
        def: Lambda,
        name: StringKey,
        scope_type: ScopeType,
        succ_type: Successor,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        let current_block_id = self.block_id;
        let block = self.get_block(current_block_id);
        println!("bake_function: {:?}", (block.scope_id, current_block_id));

        let ret_ty = b.types.r(def.return_type).clone();
        let fun_ty = def_to_type(&def, b);
        let body = def.body.unwrap();
        let span_id = body.span_id;
        // create function scope
        let (fun_block_id, fun_scope_id) =
            self.new_scope_and_block(scope_type, fenv.static_scope_id(), fenv);
        // create function block and return block
        //self.switch_blocks(fun_block_id);
        let ret_block_id = self.new_block(fun_scope_id);

        // return in scope
        let fun_scope = fenv.get_scope_mut(fun_scope_id);
        fun_scope.return_block = Some(ret_block_id);

        // next in scope
        let fun_block = self.get_block_mut(fun_block_id);
        fun_block.next = Some(ret_block_id);

        // block graph
        self.block_succ(fenv.static_block_id(), fun_block_id, succ_type);
        self.block_succ(fun_block_id, ret_block_id, Successor::BlockScope);
        self.switch_blocks(fun_block_id);
        let (entry_link_id, _) = self.push_start_block(
            fun_scope_id,
            fun_ty.clone(),
            Some(name),
            span_id,
            VarDefinitionSpace::Static,
            fenv,
        );
        // add the name to static scope
        // do this early for recursive functions
        fenv.scope_define(fenv.static_scope_id(), name, entry_link_id);

        let body = jump_if_needed(*body, b);

        self.switch_blocks(fun_block_id);
        let r = self.push_node(body, fenv, b)?;
        assert_eq!(self.block_id, r.block_id);

        // write out return block
        let fun_block = self.get_block(fun_block_id);

        if fun_block.num_ret_args.len() > 1 {
            b.push_error(
                &format!("Return type mismatch: {:?}", &fun_block.num_ret_args),
                span_id,
            );
        }

        if fun_block.num_ret_args.is_empty() {
            if b.types.u.unify(&AstType::Unit, &ret_ty).is_err() {
                b.push_error(
                    &format!("6-Type Mismatch: LHS: {}, RHS: {}", AstType::Unit, &ret_ty),
                    span_id,
                );
            }
        } else {
            let num_ret_args = fun_block.num_ret_args.iter().next().unwrap().clone();
            if num_ret_args == 0 {
                if b.types.u.unify(&AstType::Unit, &ret_ty).is_err() {
                    b.push_error(
                        &format!("1-Type Mismatch: LHS: {}, RHS: {}", &ret_ty, &AstType::Unit),
                        span_id,
                    );
                }
            }
        }

        for ty in fun_block.ret_types.iter() {
            if b.types.u.unify(ty, &ret_ty).is_err() {
                b.push_error(
                    &format!("7-Type Mismatch: LHS: {}, RHS: {}", ty, &ret_ty),
                    span_id,
                );
            }
        }

        let ret_arg_type = if let AstType::Unit = &ret_ty {
            AstType::Struct(vec![])
        } else {
            AstType::Struct(vec![(None, ret_ty.clone())])
        };

        let ret_ty = if let Some(ty) = b.types.u.resolve(&ret_arg_type) {
            ty
        } else {
            let s = b.labels.r(name.into());
            b.push_error(
                &format!("[{}] Return Type Must Resolve: {}", &s, &ret_ty),
                span_id,
            );
            ret_arg_type
        };

        self.switch_blocks(ret_block_id);
        self.push_return_block(fun_scope_id, ret_ty.clone(), span_id, fenv, b);

        // restore position back to where we started
        self.switch_blocks(current_block_id);
        Ok(FlattenResult::new(
            current_block_id,
            Some(entry_link_id),
            fun_ty,
            false,
        ))
    }

    pub fn find_template(
        &self,
        block_id: BlockId,
        name: StringLabel,
        fenv: &FlattenEnvironment,
    ) -> Option<LinkId> {
        // resolve scope through the tree, starting at the current scope
        let block = self.get_block(block_id);
        for scope_id in fenv.walk_scopes(block.scope_id) {
            let scope = fenv.get_scope(scope_id);
            if let Some(link_id) = scope.templates.get(&name) {
                return Some(*link_id);
            }
        }
        None
    }

    pub fn find_lambda(
        &self,
        block_id: BlockId,
        name: StringKey,
        fenv: &mut FlattenEnvironment,
    ) -> Option<(ScopeId, Lambda)> {
        match self.resolve_lambda_scope(block_id, name.into(), fenv) {
            Some(scope_id) => {
                let scope = fenv.get_scope(scope_id);
                if let Some(template_id) = scope.lambdas.get(&name.into()).cloned() {
                    let def = self.get_ast_template(template_id).clone();
                    Some((scope_id, def))
                } else {
                    None
                }
            }
            None => None,
        }
    }

    fn push_bake_lambda_inner(
        &mut self,
        def: Lambda,
        span_id: SpanId,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<(BlockId, BlockId, LinkId)> {
        let current_block_id = self.block_id;
        let block = self.get_block(current_block_id);
        let scope_id = block.scope_id;
        let ret_ty = b.types.r(def.return_type).clone();

        // New Lambda Scope
        let (fun_block_id, fun_scope_id) =
            self.new_scope_and_block(ScopeType::Function, scope_id, fenv);

        // NEXT BLOCK(ret_ty)
        // We create a new block for the lambda to return to
        // this is the continuation
        let next_block_id = self.new_block(scope_id);
        self.block_succ(current_block_id, next_block_id, Successor::BlockScope);

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
        let next_arg_ty = AstType::Struct(match &ret_ty {
            AstType::Unit => vec![],
            _ => vec![(None, ret_ty.clone())],
        });
        // start next block
        self.switch_blocks(next_block_id);
        let (_v_block, next_link_ids) = self.push_start_block(
            scope_id,
            AstType::Func(
                next_arg_ty.clone().into(),
                ReturnType::Single(AstType::Unit).into(),
            ),
            Some(b.labels.fresh_key("cont")),
            span_id,
            VarDefinitionSpace::Reg,
            fenv,
        );

        let next_link_id = match &ret_ty {
            AstType::Unit => None,
            _ => Some(next_link_ids.first().unwrap().0),
        };

        // Start lambda block
        let lambda_name = b.labels.fresh_key("lambda");
        let fun_ty = b.types.r(def.fun_type);
        self.switch_blocks(fun_block_id);
        self.push_start_block(
            fun_scope_id,
            fun_ty.clone(),
            Some(lambda_name),
            span_id,
            VarDefinitionSpace::Reg,
            fenv,
        );
        // flatten lambda block
        self.switch_blocks(fun_block_id);
        let r = self.push_node(body, fenv, b)?;
        assert_eq!(self.block_id, r.block_id);
        self.switch_blocks(next_block_id);
        Ok((fun_block_id, next_block_id, next_link_id.unwrap()))
    }

    fn push_bake_lambda(
        &mut self,
        name: StringKey,
        maybe_ty: Option<AstType>,
        span_id: SpanId,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<(BlockId, BlockId, LinkId)> {
        if let Some((scope_id, def)) = self.find_lambda(self.block_id, name, fenv) {
            println!(
                "bake lambda: {:?}",
                (scope_id, self.block_id, b.labels.r(name.into()))
            );
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
            let r = self.push_bake_lambda_inner(def, span_id, fenv, b)?;
            self.drain_diagnostics(b);
            Ok(r)
        } else {
            let s = b.labels.r(name.into());
            Err(Error::new(BlockifyError::NotFound(s)))
        }
    }

    pub fn push_bake(
        &mut self,
        name: StringKey,
        maybe_ty: Option<AstType>,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<LinkId> {
        let current_block_id = self.block_id;
        if let Some((scope_id, def)) = self.find_lambda(current_block_id, name, fenv) {
            println!(
                "bake: {:?}",
                (scope_id, current_block_id, b.labels.r(name.into()))
            );
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
            // update declaration
            let decl_link_id = if let Some(decl_link_id) =
                self.resolve_declaration(current_block_id, name, fenv)
            {
                decl_link_id
            } else {
                unreachable!()
            };

            let result = self.push_bake_function(
                def,
                name,
                ScopeType::Function,
                Successor::FunctionDeclaration,
                fenv,
                b,
            );
            if result.is_err() {
                self.drain_diagnostics(b);
            }
            let r = result?;

            let entry_block_id = self.get_entry(r.link_id.unwrap()).block_id;
            let entry = self.get_entry_mut(decl_link_id);
            if let LCode::DeclareFunction(_) = entry.code {
            } else {
                assert!(false);
            }
            entry.code = LCode::DeclareFunction(Some(entry_block_id));

            self.drain_diagnostics(b);
            self.switch_blocks(current_block_id);
            Ok(r.link_id.unwrap())
        } else {
            let s = b.labels.r(name.into());
            Err(Error::new(BlockifyError::NotFound(s)))
        }
    }

    pub fn push_bake_template(
        &mut self,
        name: StringKey,
        maybe_ty: Option<AstType>,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<LinkId> {
        let current_block_id = self.block_id;
        if let Some((scope_id, def)) = self.find_lambda(current_block_id, name, fenv) {
            println!(
                "bake: {:?}",
                (scope_id, current_block_id, b.labels.r(name.into()))
            );
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

            //println!("scope: {:?}", (scope_id, &scope));
            //let top_block_id = scope.entry_block.unwrap();
            //self.switch_blocks(top_block_id);
            let result = self.push_bake_function(
                def.clone(),
                name,
                ScopeType::Template,
                Successor::TemplateDeclaration,
                fenv,
                b,
            );
            //self.switch_blocks(block_id);

            /*
            // update declaration
            let decl_link_id = if let Some(decl_link_id) =
                self.resolve_declaration(current_block_id, name, fenv)
            {
                decl_link_id
            } else {
                unreachable!()
            };

            let result = self.push_bake_function(def, name, ScopeType::Function, Successor::FunctionDeclaration, fenv, b);
            */
            if result.is_err() {
                self.drain_diagnostics(b);
            }
            let r = result?;

            /*
            let entry_block_id = self.get_entry(r.link_id.unwrap()).block_id;
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
            Err(Error::new(BlockifyError::NotFound(s)))
        }
    }

    pub fn push_node(
        &mut self,
        node: AstNode,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        let current_block_id = self.block_id;
        let block = self.get_block_mut(current_block_id);
        let span_id = node.span_id;
        let ast = node.node;

        match ast {
            Ast::Module(_, _) => {
                unimplemented!("No nested modules yet")
            }

            Ast::Sequence(exprs) => {
                self.switch_blocks(current_block_id);
                self.push_sequence(exprs, span_id, fenv, b)
            }

            Ast::Global(name, expr) => {
                match expr.node {
                    Ast::Lambda(def) => {
                        //let ret_ty = b.types.r(def.return_type).clone();
                        let fun_ty = def_to_type(&def, b);

                        let link_id = self.push_code(
                            LCode::DeclareFunction(None),
                            fun_ty.clone(),
                            Some(name),
                            span_id,
                            VarDefinitionSpace::Static,
                        );

                        self.switch_blocks(current_block_id);
                        fenv.scope_define_declaration(fenv.static_scope_id(), name, link_id);

                        // save template for later use
                        if def.body.is_some() {
                            self.save_ast_template(current_block_id, &name, &def, fenv, b)?;
                        }

                        if let Some(_body) = &def.body {
                            Ok(FlattenResult::new(current_block_id, None, fun_ty, false))
                        } else {
                            Ok(FlattenResult::new(current_block_id, None, fun_ty, false))
                        }
                    }

                    Ast::Literal(lit) => {
                        let scope_id = block.scope_id;
                        let scope = fenv.get_scope(scope_id);

                        let static_block_id = fenv.static_block_id();

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
                            LCode::Const(lit),
                            ast_ty.clone(),
                            Some(global_name_key),
                            node.span_id,
                            VarDefinitionSpace::Static,
                        );

                        fenv.scope_define(scope_id, name, link_id.into());

                        self.switch_blocks(current_block_id);
                        Ok(FlattenResult::new(
                            current_block_id,
                            Some(link_id),
                            ast_ty,
                            false,
                        ))
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
                            self.link.add_library(&s);
                        } else {
                            b.push_error("Expected string", span_id);
                        }
                        self.switch_blocks(current_block_id);
                        Ok(FlattenResult::new(
                            current_block_id,
                            None,
                            AstType::Unit,
                            false,
                        ))
                    }
                    _ => {
                        let args_size = args.len();
                        assert_eq!(args_size, bi.arity());

                        //let ret_type_id = b.types.s(&ty);
                        let def = bi.get_lambda(b);
                        self.switch_blocks(current_block_id);
                        self.push_builtin_call(&def, id, args, span_id, fenv, b)
                    }
                }
            }

            Ast::Return(maybe_expr) => {
                //self.dump_scope(block_id, fenv, b);
                //println!(
                //"{:?}",
                //petgraph::dot::Dot::with_config(
                //&fenv.scopes,
                //&[petgraph::dot::Config::EdgeNoLabel]
                //)
                //);

                let block = self.get_block(current_block_id);
                //println!("return: {:?}", (block_id, block.scope_id));
                let fun_scope_id = fenv
                    .find_nearest_scope(block.scope_id, &[ScopeType::Template, ScopeType::Function])
                    .expect(&format!(
                        "Not in function context, scope_id:{}",
                        block.scope_id
                    ));

                let fun_block_id = fenv.get_entry_block(fun_scope_id);

                let mut jump_args = vec![];
                let mut current_block_id = current_block_id;
                //let block_id = current_block_id;
                let span_id = if let Some(expr) = maybe_expr {
                    let expr_span_id = expr.span_id;
                    self.switch_blocks(current_block_id);
                    let r = self.push_node(*expr, fenv, b)?;
                    assert_eq!(self.block_id, r.block_id);
                    current_block_id = r.block_id;
                    //block_id = r.block_id;
                    let link_id = r.link_id.unwrap();
                    let entry = self.get_entry(link_id);
                    jump_args.push((None, link_id, entry.ty.clone()));
                    expr_span_id
                } else {
                    node.span_id
                };

                let fun_block = self.get_block_mut(fun_block_id);
                fun_block.num_ret_args.insert(jump_args.len());
                for (_, _, ty) in jump_args.iter() {
                    fun_block.ret_types.insert(ty.clone());
                }

                let scope = fenv.get_scope(fun_scope_id);
                self.switch_blocks(current_block_id);
                self.push_jump(scope.return_block.unwrap().into(), jump_args, span_id);
                self.switch_blocks(current_block_id);
                Ok(FlattenResult::new(
                    current_block_id,
                    None,
                    AstType::Unit,
                    true,
                ))
            }

            Ast::Literal(lit) => {
                // literal is expression, non-terminal
                let ty: AstType = lit.clone().into();
                let link_id = self.push_code(
                    LCode::Const(lit),
                    ty.clone(),
                    None,
                    node.span_id,
                    VarDefinitionSpace::Default,
                );
                Ok(FlattenResult::new(
                    current_block_id,
                    Some(link_id),
                    ty,
                    false,
                ))
            }

            Ast::BinaryOp(op, x, y) => {
                // expression, non-terminal
                let x_span_id = x.span_id;
                self.switch_blocks(current_block_id);
                let rx = self.push_node(*x, fenv, b)?;
                assert_eq!(self.block_id, rx.block_id);
                self.switch_blocks(rx.block_id);
                let ry = self.push_node(*y, fenv, b)?;
                assert_eq!(self.block_id, ry.block_id);
                let current_block_id = ry.block_id;
                let vx = rx.link_id.unwrap();
                let vy = ry.link_id.unwrap();

                if b.types.u.unify(&rx.ty, &ry.ty).is_err() {
                    b.push_error(
                        &format!("3-Type Mismatch: LHS: {}, RHS: {}", &rx.ty, &ry.ty),
                        x_span_id,
                    );
                }

                for (v, ty) in [(vx, &rx.ty), (vy, &ry.ty)] {
                    self.push_code(
                        LCode::Value(v.into()),
                        ty.clone(),
                        None,
                        node.span_id,
                        VarDefinitionSpace::Reg,
                    );
                }

                let ret_ty = op.node.get_type(&rx.ty, &ry.ty);
                let link_id = self.push_code(
                    LCode::Op2(op.node),
                    ret_ty.clone(),
                    None,
                    op.span_id,
                    VarDefinitionSpace::Default,
                );

                self.switch_blocks(current_block_id);
                Ok(FlattenResult::new(
                    current_block_id,
                    Some(link_id),
                    ret_ty,
                    false,
                ))
            }

            Ast::Identifier(key) => {
                // identifier is expression, non-terminal
                if let Some(def_link_id) = self.resolve_name(current_block_id, key, fenv) {
                    let entry = self.get_entry(def_link_id).clone();
                    let ty = entry.ty.clone();
                    let mem = entry.mem;

                    let link_id = if let VarDefinitionSpace::Arg = mem {
                        def_link_id
                    } else {
                        self.push_code(
                            LCode::Load(def_link_id),
                            ty.clone(),
                            None,
                            node.span_id,
                            entry.mem,
                        )
                    };
                    Ok(FlattenResult::new(
                        current_block_id,
                        Some(link_id),
                        ty.clone(),
                        false,
                    ))
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
                    self.save_ast_template(current_block_id, &name, &def, fenv, b)?;
                    self.switch_blocks(current_block_id);
                    return Ok(FlattenResult::new(current_block_id, None, ty, false));
                }

                self.switch_blocks(current_block_id);
                let r = self.push_node(*expr, fenv, b)?;
                assert_eq!(self.block_id, r.block_id);
                let current_block_id = r.block_id;
                let v_expr = r.link_id.unwrap();
                let expr_ty = self.get_entry(v_expr).ty.clone();

                let offset_decl =
                    if let Some(v_decl) = self.resolve_name(current_block_id, name, fenv) {
                        let ty = self.get_type(v_decl).clone();
                        if b.types.u.unify(&ty, &expr_ty).is_err() {
                            b.push_error(
                                &format!("Assisgn Type Mismatch: {:?}, {:?}", ty, expr_ty),
                                node.span_id,
                            );
                        }
                        v_decl
                    } else {
                        let block = self.get_block(current_block_id);
                        let scope_id = block.scope_id;
                        let expr_ty = self.get_entry(v_expr).ty.clone();
                        let link_id = self.push_code(
                            LCode::Declare,
                            expr_ty.clone(),
                            Some(name),
                            node.span_id,
                            VarDefinitionSpace::Default,
                        );
                        fenv.scope_define(scope_id, name, link_id);
                        link_id.into()
                    };

                let link_id = self.push_code(
                    LCode::Store(offset_decl, v_expr),
                    AstType::Unit,
                    Some(name),
                    node.span_id,
                    VarDefinitionSpace::Default,
                );
                self.switch_blocks(current_block_id);
                Ok(FlattenResult::new(
                    current_block_id,
                    Some(link_id),
                    AstType::Unit,
                    false,
                ))
            }

            Ast::Call(expr, args) => {
                match &expr.node {
                    // call is an expression, it's non-terminal
                    // lambdas should also be non-terminal
                    Ast::Identifier(ident) => {
                        self.push_call_by_name(*ident, args, node.span_id, fenv, b)
                    }
                    _ => unimplemented!("{:?}", expr.node),
                }
            }

            Ast::UnaryOp(op, x) => {
                // op1 is expression, non-terminal
                self.switch_blocks(current_block_id);
                let r = self.push_node(*x, fenv, b)?;
                assert_eq!(self.block_id, r.block_id);
                let current_block_id = r.block_id;

                self.push_code(
                    LCode::Value(r.link_id.unwrap().into()),
                    r.ty.clone(),
                    None,
                    node.span_id,
                    VarDefinitionSpace::Reg,
                );

                let link_id = self.push_code(
                    LCode::Op1(op),
                    r.ty.clone(),
                    None,
                    node.span_id,
                    VarDefinitionSpace::Reg,
                );
                self.switch_blocks(current_block_id);
                Ok(FlattenResult::new(
                    current_block_id,
                    Some(link_id),
                    r.ty,
                    false,
                ))
            }

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
                let block = self.get_block(current_block_id);
                let v_next = block.next.unwrap();
                let parent_scope_id = block.scope_id;

                // THEN
                let (then_block_id, then_scope_id) =
                    self.new_scope_and_block(ScopeType::Block, parent_scope_id, fenv);
                let then_span_id = then_expr.span_id;
                self.block_succ(current_block_id, then_block_id, Successor::BlockScope);
                self.block_succ(current_block_id, then_block_id, Successor::Jump);
                let block = self.get_block_mut(then_block_id);
                block.next(v_next);

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
                    fenv,
                );
                self.switch_blocks(then_block_id);
                let r = self.push_node(NB::ensure_seq(*then_expr), fenv, b)?;
                assert_eq!(self.block_id, r.block_id);

                // ELSE
                let else_block_id = if let Some(else_expr) = maybe_else_expr {
                    let (else_block_id, else_scope_id) =
                        self.new_scope_and_block(ScopeType::Block, parent_scope_id, fenv);
                    let else_span_id = else_expr.span_id;
                    self.block_succ(current_block_id, else_block_id, Successor::BlockScope);
                    self.block_succ(current_block_id, else_block_id, Successor::Jump);
                    let block = self.get_block_mut(else_block_id);
                    block.next = Some(v_next);

                    let name = b.labels.fresh_key("else");

                    self.switch_blocks(else_block_id);
                    self.push_start_block(
                        else_scope_id,
                        branch_block_type,
                        Some(name),
                        else_span_id,
                        VarDefinitionSpace::Reg,
                        fenv,
                    );

                    self.switch_blocks(else_block_id);
                    let r = self.push_node(NB::ensure_seq(*else_expr), fenv, b)?;
                    assert_eq!(self.block_id, r.block_id);
                    else_block_id
                } else {
                    self.block_succ(current_block_id, v_next, Successor::BlockScope);
                    self.block_succ(current_block_id, v_next, Successor::Jump);
                    v_next
                };

                // condition
                let span_id = condition.span_id;
                self.switch_blocks(current_block_id);
                let r = self.push_node(*condition, fenv, b)?;
                assert_eq!(self.block_id, r.block_id);
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
                self.switch_blocks(r.block_id);
                Ok(FlattenResult::new(r.block_id, Some(v), AstType::Unit, true))
            }

            Ast::Block(name, args, body) => {
                //block already exists, and it is not an entry block
                let new_block_id =
                    fenv.resolve_block_id(block.scope_id, name.into())
                        .expect(&format!(
                            "block not found: {}, {:?}",
                            b.labels.r(name.into()),
                            name
                        ));

                let new_block = self.get_block(new_block_id);
                let new_scope_id = new_block.scope_id;

                let scope = fenv.get_scope(new_scope_id);

                // ensure this block is not an entry block, this should never happen.
                assert!(scope.entry_block != Some(new_block_id));

                self.block_succ(current_block_id, new_block_id, Successor::BlockScope);

                let arg_ty = AstType::Struct(
                    args.iter()
                        .map(|p| {
                            let ty = b.types.r(p.ty);
                            (Some(p.name), ty.clone())
                        })
                        .collect::<Vec<_>>(),
                );

                self.switch_blocks(new_block_id);
                self.push_start_block(
                    new_scope_id,
                    //&arg_ty,
                    AstType::Func(
                        arg_ty.clone().into(),
                        ReturnType::Single(AstType::Unit).into(),
                    ),
                    //AstType::Unit,
                    Some(name),
                    span_id,
                    VarDefinitionSpace::Default,
                    fenv,
                );
                self.switch_blocks(new_block_id);
                let r = self.push_node(NB::ensure_seq(*body), fenv, b)?;
                assert_eq!(self.block_id, r.block_id);

                self.switch_blocks(r.block_id);
                Ok(FlattenResult::new(
                    r.block_id,
                    r.link_id,
                    AstType::Unit,
                    true,
                ))
            }

            Ast::Ternary(c, x, y) => {
                // expression, non-terminal
                let block = self.get_block(current_block_id);
                let scope_id = block.scope_id;

                // Condition
                self.switch_blocks(current_block_id);
                let rc = self.push_node(*c, fenv, b)?;
                assert_eq!(self.block_id, rc.block_id);

                let branch_block_type = AstType::Func(
                    AstType::Struct(vec![]).into(),
                    ReturnType::Single(AstType::Unit).into(),
                );

                // THEN
                let (then_block_id, then_scope_id) =
                    self.new_scope_and_block(ScopeType::Region, scope_id, fenv);
                let then_span_id = x.span_id;
                let then_ast = AstNode::make_yield(*x);
                self.block_succ(rc.block_id, then_block_id, Successor::Operation);
                self.block_succ(rc.block_id, then_block_id, Successor::Jump);

                let name = b.labels.fresh_key("t_then");

                self.switch_blocks(then_block_id);
                self.push_start_block(
                    then_scope_id,
                    branch_block_type.clone(),
                    Some(name),
                    then_span_id,
                    VarDefinitionSpace::Reg,
                    fenv,
                );

                self.switch_blocks(then_block_id);
                let r = self.push_node(then_ast, fenv, b)?;
                assert_eq!(self.block_id, r.block_id);
                let then_ty = r.ty;

                // ELSE
                let else_span_id = y.span_id;
                let (else_block_id, else_scope_id) =
                    self.new_scope_and_block(ScopeType::Region, scope_id, fenv);
                let else_ast = AstNode::make_yield(*y);
                self.block_succ(rc.block_id, else_block_id, Successor::Operation);
                self.block_succ(rc.block_id, else_block_id, Successor::Jump);

                self.switch_blocks(else_block_id);
                self.push_start_block(
                    else_scope_id,
                    branch_block_type,
                    Some(name),
                    else_span_id,
                    VarDefinitionSpace::Reg,
                    fenv,
                );

                self.switch_blocks(else_block_id);
                let r = self.push_node(else_ast, fenv, b)?;
                assert_eq!(self.block_id, r.block_id);
                let else_ty = r.ty;

                if b.types.u.unify(&then_ty, &else_ty).is_err() {
                    b.push_error(
                        &format!(
                            "Ternary Type Mismatch: then: {}, else: {}",
                            &then_ty, &else_ty
                        ),
                        span_id,
                    );
                }

                self.switch_blocks(rc.block_id);
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
                self.switch_blocks(rc.block_id);
                Ok(FlattenResult::new(rc.block_id, Some(v), then_ty, false))
            }

            Ast::Yield(maybe_expr) => {
                // yield is terminal
                let mut v_block = current_block_id;
                let mut ty = AstType::Unit;
                if let Some(expr) = maybe_expr {
                    self.switch_blocks(current_block_id);
                    let r = self.push_node(*expr, fenv, b)?;
                    assert_eq!(self.block_id, r.block_id);
                    if let Some(v) = r.link_id {
                        v_block = r.block_id;
                        ty = r.ty.clone();
                        // push single arg
                        self.push_code(
                            LCode::CallValue(v.into()),
                            r.ty,
                            None,
                            node.span_id,
                            VarDefinitionSpace::Reg,
                        );
                    }
                }

                self.switch_blocks(v_block);
                let v = self.push_code(
                    LCode::Yield,
                    ty.clone(),
                    None,
                    node.span_id,
                    VarDefinitionSpace::Reg,
                );
                self.switch_blocks(v_block);
                Ok(FlattenResult::new(v_block, Some(v), ty, true))
            }

            Ast::ControlFlowMarker(ControlFlowMarker::BlockStart(name, args)) => {
                // all blocks should have been forward declared in the sequence
                let name = name.unwrap();
                let current_dom_block_id =
                    fenv.resolve_block_id(block.scope_id, name.into()).unwrap();
                assert_eq!(0, args.len());
                let next = block.next;
                let current_dom_block = self.get_block_mut(current_dom_block_id);
                current_dom_block.next = next;
                let current_scope_id = current_dom_block.scope_id;
                self.block_succ(
                    current_block_id,
                    current_dom_block_id,
                    Successor::BlockScope,
                );

                let arg_ty = AstType::Struct(vec![]);
                let block_ty = AstType::Func(
                    arg_ty.clone().into(),
                    ReturnType::Single(AstType::Unit).into(),
                );
                self.switch_blocks(current_dom_block_id);
                self.push_start_block(
                    current_scope_id,
                    block_ty,
                    Some(name),
                    span_id,
                    VarDefinitionSpace::Reg,
                    fenv,
                );
                Ok(FlattenResult::new(
                    current_dom_block_id,
                    None,
                    AstType::Unit,
                    false,
                ))
            }

            Ast::ControlFlowMarker(ControlFlowMarker::Goto(label)) => {
                // Goto is terminal
                if let Some(target_block_id) = fenv.resolve_block_id(block.scope_id, label.into()) {
                    self.switch_blocks(current_block_id);
                    let link_id = self.push_jump(target_block_id.into(), vec![], node.span_id);
                    self.switch_blocks(current_block_id);
                    Ok(FlattenResult::new(
                        current_block_id,
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
                let block = self.get_block(current_block_id);
                let next = block.next.unwrap();
                let scope_id = block.scope_id;
                let (loop_block_id, loop_scope_id) =
                    self.new_scope_and_block(ScopeType::Region, scope_id, fenv);
                let scope = fenv.get_scope_mut(loop_scope_id);
                scope.entry_block = Some(loop_block_id);
                self.block_succ(current_block_id, loop_block_id, Successor::BlockScope);
                fenv.push_loop_blocks(loop_scope_id, Some(name), next.into(), loop_block_id.into());

                let loop_block = self.get_block_mut(loop_block_id);
                loop_block.next = Some(loop_block_id);

                self.switch_blocks(loop_block_id);
                self.push_start_block(
                    loop_scope_id,
                    AstType::Func(
                        AstType::Struct(vec![]).into(),
                        ReturnType::Single(AstType::Unit).into(),
                    ),
                    Some(name),
                    body.span_id,
                    VarDefinitionSpace::Reg,
                    fenv,
                );

                self.switch_blocks(current_block_id);
                self.push_jump(loop_block_id.into(), vec![], node.span_id);
                self.switch_blocks(loop_block_id);

                self.switch_blocks(loop_block_id);
                let r = self.push_node(*body, fenv, b)?;
                assert_eq!(self.block_id, r.block_id);

                self.switch_blocks(current_block_id);
                Ok(FlattenResult::new(
                    current_block_id,
                    None,
                    AstType::Unit,
                    true,
                ))
            }

            Ast::Continue(maybe_name, args) => {
                let block = self.get_block(current_block_id);
                let scope_id = block.scope_id;

                // args not implemented yet
                assert_eq!(args.len(), 0);
                // loop up loop blocks by name
                if let Some(loop_scope) = fenv.get_loop_scope(scope_id, maybe_name) {
                    self.switch_blocks(current_block_id);
                    let link_id = self.push_jump(loop_scope.start_block, vec![], node.span_id);
                    self.switch_blocks(current_block_id);
                    Ok(FlattenResult::new(
                        current_block_id,
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
                let block = self.get_block(current_block_id);
                let scope_id = block.scope_id;

                // args not implemented yet
                assert_eq!(args.len(), 0);
                // loop up loop blocks by name
                if let Some(loop_scope) = fenv.get_loop_scope(scope_id, maybe_name) {
                    self.switch_blocks(current_block_id);
                    let link_id = self.push_jump(loop_scope.next_block, vec![], node.span_id);
                    self.switch_blocks(current_block_id);
                    Ok(FlattenResult::new(
                        current_block_id,
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
                let block = self.get_block(current_block_id);
                let v_last = block.links.last().unwrap().clone();
                let entry_last = self.get_entry(v_last);
                let is_term = entry_last.code.is_term();
                if is_term {
                    // XXX: We are closing an already closed block
                    // Possible malformed AST
                    b.push_warning(
                        &format!(
                            "Closing already closed block: block={}, link={}",
                            current_block_id, v_last
                        ),
                        node.span_id,
                    );
                    self.switch_blocks(current_block_id);
                    return Ok(FlattenResult::new(
                        current_block_id,
                        None,
                        AstType::Unit,
                        true,
                    ));
                }

                if let Some(next) = block.next {
                    self.switch_blocks(current_block_id);
                    let link_id = self.push_jump(next.into(), vec![], node.span_id);
                    self.switch_blocks(current_block_id);
                    Ok(FlattenResult::new(
                        current_block_id,
                        Some(link_id),
                        AstType::Unit,
                        true,
                    ))
                } else {
                    self.switch_blocks(current_block_id);
                    Ok(FlattenResult::new(
                        current_block_id,
                        None,
                        AstType::Unit,
                        true,
                    ))
                }
            }

            Ast::Array(_type_id, dims) => {
                let mut link_ids = vec![];
                let mut current_block_id = current_block_id;
                for d in dims {
                    self.switch_blocks(current_block_id);
                    let r = self.push_node(d, fenv, b)?;
                    assert_eq!(self.block_id, r.block_id);
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
    //println!("{}", s);
    std::fs::write(filename, s).unwrap();
}

fn def_to_type(def: &Lambda, b: &mut NB) -> AstType {
    let arg_type = b.types.r(def.arg_type).clone();
    let return_type = b.types.r(def.return_type).clone();
    let fun_ty = AstType::Func(arg_type.into(), ReturnType::Single(return_type).into());
    fun_ty
}

fn jump_if_needed(ast: AstNode, b: &mut NB) -> AstNode {
    let span_id = ast.span_id;
    let mut reader = SequenceReader::new();
    let mut seq = reader.build(ast.to_vec(), b);
    if let Some(first) = seq.first() {
        if let Ast::Block(key, args, _body) = &first.node {
            assert_eq!(args.len(), 0);
            let jump = NB::goto(*key).node(span_id);
            seq.insert(0, jump);
        }
    }
    NB::seq(seq, span_id)
}
