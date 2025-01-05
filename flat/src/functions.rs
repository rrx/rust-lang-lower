use crate::{
    ArgVec, BlockId, BlockifyError, FlattenInner, FlattenResult, LCode, LinkId, NodeBuilder as NB,
    PushContext, ScopeId, ScopeState, ScopeStateFunction, ScopeType, Successor, VarDefinitionSpace,
};
use anyhow::Error;
use anyhow::Result;
use compile_core::{
    AbstractionId, Argument, Ast, AstFuncType, AstNode, AstType, Lambda, Literal, NaryOperation,
    ReturnType, SpanId, StringKey,
};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct VariantId(u32);
impl std::fmt::Display for VariantId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "V{}", self.0)
    }
}

impl VariantId {
    pub fn new(index: usize) -> Self {
        Self(index as u32)
    }
    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone)]
pub struct Caller {
    pub block_id: BlockId,
    pub link_id: LinkId,
    pub args: Vec<LinkId>,
}

#[derive(Debug)]
pub struct FunctionVariant {
    pub ty: AstType,
    pub link_id: LinkId,
    pub block_id: BlockId,
    pub name: StringKey,
}

#[derive(Debug)]
pub struct VariantIterator {
    index: usize,
    len: usize,
}

impl VariantIterator {
    pub fn new(len: usize) -> Self {
        Self { index: 0, len }
    }
}

impl Iterator for VariantIterator {
    type Item = VariantId;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.len {
            let index = self.index;
            self.index += 1;
            Some(VariantId::new(index))
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct FunctionVariantBuilder {
    pub variants: Vec<FunctionVariant>,
    pub block_lookup: HashMap<BlockId, VariantId>,
}

impl FunctionVariantBuilder {
    pub fn new() -> Self {
        Self {
            variants: vec![],
            block_lookup: HashMap::new(),
        }
    }

    pub fn iter(&self) -> VariantIterator {
        VariantIterator::new(self.variants.len())
    }

    pub fn get_by_block(&self, block_id: BlockId) -> Option<VariantId> {
        if let Some(variant_id) = self.block_lookup.get(&block_id) {
            Some(*variant_id)
        } else {
            None
        }
    }

    pub fn get(&self, variant_id: VariantId) -> &FunctionVariant {
        self.variants.get(variant_id.index()).unwrap()
    }

    pub fn get_mut(&mut self, variant_id: VariantId) -> &mut FunctionVariant {
        self.variants.get_mut(variant_id.index()).unwrap()
    }

    pub fn add(
        &mut self,
        ty: AstType,
        link_id: LinkId,
        block_id: BlockId,
        name: StringKey,
    ) -> VariantId {
        let index = self.variants.len();
        self.variants.push(FunctionVariant {
            ty,
            link_id,
            block_id,
            name,
        });
        let variant_id = VariantId(index as u32);
        self.block_lookup.insert(block_id, variant_id);
        variant_id
    }
}

#[derive(Debug)]
pub struct Abstraction {
    pub def: Lambda,
    pub def_span_id: SpanId,
    pub name: StringKey,
}

#[derive(Debug)]
pub struct AbstractionsBuilder(Vec<Abstraction>);

impl AbstractionsBuilder {
    pub fn new() -> Self {
        Self(vec![])
    }

    pub fn get(&self, abstraction_id: AbstractionId) -> &Abstraction {
        self.0.get(abstraction_id.index()).unwrap()
    }

    pub fn get_mut(&mut self, abstraction_id: AbstractionId) -> &mut Abstraction {
        self.0.get_mut(abstraction_id.index()).unwrap()
    }

    pub fn add(&mut self, name: StringKey, def: Lambda, def_span_id: SpanId) -> AbstractionId {
        let index = self.0.len();
        self.0.push(Abstraction {
            def,
            def_span_id,
            name,
            //caller_blocks: HashSet::new(),
        });
        AbstractionId::new(index)
    }
}

impl FlattenInner {
    pub fn push_bake_main(&mut self, b: &mut NB) -> Result<LinkId> {
        let current_block_id = self.current_block_id();
        let name = b.labels.s("main");
        // reset the block position before each function
        // main is always static context
        self.switch_blocks(self.static_block_id());
        let ty = AstType::func(vec![], AstType::Int);
        let r = self.push_bake(name, ty.get_func().clone(), b);
        // switch back after bake
        self.switch_blocks(current_block_id);
        r
    }

    pub fn calculate_function_arguments(
        def: &Lambda,
        args: &[Argument],
        system: &[Argument],
        def_span_id: SpanId,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> (Vec<Argument>, AstFuncType) {
        let func_arg = def.func_type.args.clone();

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

        let mut fields_list = func_arg.fields();
        let size = fields_list.len() + system.len();

        let mut value_map = HashMap::with_capacity(size);
        let mut populated_set = HashSet::with_capacity(size);
        let mut args_seq = vec![];
        let kwargs_map = HashMap::new();
        let mut def_has_args = false;
        let mut args_seq_started = false;
        //let mut def_has_kwargs = false;

        // copy defaults into value map
        for (key, value) in def.defaults.iter() {
            value_map.insert(*key, value.clone());
        }

        for arg in system.iter() {
            if let Argument::System(key, _) = arg {
                let ty = b.types.fresh_unknown();
                fields_list.push((Some(*key), ty.clone()));
            }
        }

        for (index, arg) in args.iter().chain(system.iter()).enumerate() {
            let is_last_arg = index == args.len() + system.len() - 1;
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
                                expr.span_id,
                            );
                        }
                    }
                }

                // named arguments follow positional args
                Argument::Named(key, expr) | Argument::System(key, expr) => {
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
        }

        if args_seq.len() > 0 && def_has_args {
            // extra fields
            b.push_error(
                &format!("extra fields, no args field: {:?}", args_seq),
                call_span_id,
            );
        }

        let def_func_type =
            AstFuncType::new(AstType::Struct(fields_list), def.func_type.ret.clone());

        (args, def_func_type)
    }

    fn push_bake_static(
        &mut self,
        abstraction_id: AbstractionId,
        call_func_type: AstFuncType,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> (LinkId, AstType) {
        let a = self.abstractions.get(abstraction_id);
        let def_span_id = a.def_span_id;
        let name = a.name;

        let s = b.labels.r(name.into());
        let global_key = b.labels.fresh_key(&s);
        //let s_global = b.labels.r(global_key.into());
        let current_block_id = self.current_block_id();
        self.switch_blocks(self.static_block_id());
        let block = self.blocks.get_block(current_block_id);

        // if it's defined in static scope, just call it
        let v_entry = if let Some((r_ty, v_entry, _scope_id)) =
            self.resolve_function_name(block.scope(), &name, &call_func_type.clone().into(), b)
        {
            // unify the resolved function with the caller
            // the function should be resolved, this resolves any thing missing in the caller
            b.unify(
                &call_func_type.clone().into(),
                call_span_id,
                &r_ty,
                def_span_id,
            );
            v_entry
        } else {
            // if it's not already baked, we need to do that here
            self.switch_blocks(self.static_block_id());

            let r = self.push_bake_function(abstraction_id, call_func_type.clone(), global_key, b);
            let v_entry = r.link_id.unwrap();
            self.switch_blocks(current_block_id);
            v_entry
        };

        // we are keeping a list of function names so we can look them up later
        // there's a better way to do this.  A function only makes sense in the context of a call
        // so our lookups should actually be resolved by the caller
        self.functions.insert(name, v_entry);

        (v_entry, call_func_type.into())
    }

    pub fn push_bake(
        &mut self,
        name: StringKey,
        func_type: AstFuncType,
        b: &mut NB,
    ) -> Result<LinkId> {
        let current_block_id = self.current_block_id();
        if let Some((_, abstraction_id)) = self.blocks.resolve_lambda(current_block_id, name) {
            let r = self.push_bake_function(abstraction_id, func_type, name, b);
            self.switch_blocks(current_block_id);
            Ok(r.link_id.unwrap())
        } else {
            let s = b.labels.r(name.into());
            let u = b.spans.get_span_unknown();
            b.push_error(&format!("push_bake: not found: {}", s), u);
            Err(Error::new(BlockifyError::NotFound(s)))
        }
    }

    fn push_bake_function(
        &mut self,
        abstraction_id: AbstractionId,
        def_func_ty: AstFuncType,
        global_name: StringKey,
        b: &mut NB,
    ) -> FlattenResult {
        // returns the entry to the function

        let current_block_id = self.current_block_id();
        let a = self.abstractions.get(abstraction_id);
        let def_span_id = a.def_span_id;

        // create a next scope, that includes the function
        // when the function returns it jumps to the return block, which is the next function
        // which is out of scope for the function.  This requires that the function cleanup the
        // stack before jumping to the return block
        // This scope is empty, and isn't used for anything other than including the function scope
        // This behavior is slightly different than inline functions that jump back into the same
        // scope from which they were called.

        // New Func Scope
        let (fun_block_id, fun_scope_id) = self.blocks.new_scope_and_block(
            ScopeType::Function,
            // hack: return block is set in the bake
            ScopeState::block(),
            current_block_id,
            Successor::BlockScope,
        );

        let next_block_id =
            self.blocks
                .new_block(current_block_id, fun_scope_id, Successor::BlockScope);

        let (_block_id, entry_link_id, _, argvec, _, _r, _entry_args) = self
            .push_bake_lambda_and_update_next(
                abstraction_id,
                global_name,
                fun_scope_id,
                fun_block_id,
                next_block_id,
                def_func_ty.clone(),
                def_span_id,
                Successor::FunctionDeclaration,
                VarDefinitionSpace::Static,
                b,
            );

        self.push_return(argvec, def_span_id, b);
        // restore position back to where we started
        self.switch_blocks(current_block_id);
        FlattenResult::link(entry_link_id)
    }

    fn push_bake_lambda_and_update_next(
        &mut self,
        abstraction_id: AbstractionId,
        global_name: StringKey,
        fun_scope_id: ScopeId,
        fun_block_id: BlockId,
        next_block_id: BlockId,
        def_func_type: AstFuncType,
        call_span_id: SpanId,
        succ_type: Successor,
        mem: VarDefinitionSpace,
        b: &mut NB,
    ) -> (
        BlockId,
        LinkId,
        AstType,       // next block arg type
        ArgVec,        // return the argvec for the next block, which depends on the function
        AstFuncType,   // next block return type
        FlattenResult, // return value if it exists
        ArgVec,        // entry args
    ) {
        let a = self.abstractions.get(abstraction_id);
        let def_span_id = a.def_span_id;
        let body = a.def.body.clone().unwrap();
        let local_name = a.name;

        let result = self.push_bake_lambda(
            local_name,
            global_name,
            fun_scope_id,
            fun_block_id,
            next_block_id,
            *body,
            def_func_type,
            def_span_id,
            call_span_id,
            succ_type,
            mem,
            b,
        );

        let (fun_block_id, entry_link_id, ret_block_ty, entry_args) = result;
        let next_arg_ty = ret_block_ty.args.clone();

        // push the continuation block to which the function returns control
        let s_name = b.labels.r(local_name.into());
        let cont_name = format!("{}.next", s_name);

        self.switch_blocks(next_block_id);

        let (_v_block, v_args) = self.push_start_block(
            ret_block_ty.clone().into(),
            Some(b.labels.fresh_key(&cont_name)),
            call_span_id,
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

        // return a link to the return argument if it has one, otherwise return a statement
        let r = if let Some(link_id) = next_link_id {
            FlattenResult::link(link_id)
        } else {
            FlattenResult::statement()
        };

        (
            fun_block_id,
            entry_link_id,
            next_arg_ty,
            v_args,
            ret_block_ty,
            r,
            entry_args,
        )
    }

    fn push_bake_lambda(
        &mut self,
        local_name: StringKey,
        global_name: StringKey,
        fun_scope_id: ScopeId,
        fun_block_id: BlockId,
        next_block_id: BlockId,
        body: AstNode,
        def_func_type: AstFuncType,
        def_span_id: SpanId,
        call_span_id: SpanId,
        succ_type: Successor,
        mem: VarDefinitionSpace,
        b: &mut NB,
    ) -> (
        BlockId,
        LinkId,
        AstFuncType, // next block return type
        ArgVec,      // entry args
    ) {
        // lower a function as an inline block
        // returning from the function passes control the next block which is static
        //
        // create a new scope and block
        // build the function body in that scope and block
        // allow for recursion
        //
        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        let scope_id = block.scope();

        let fun_scope = self.blocks.get_scope_mut(fun_scope_id);
        //fun_scope.return_block = Some(next_block_id);
        fun_scope.make_function_scope(ScopeStateFunction::new(next_block_id));

        // block graph
        self.blocks
            .block_succ(current_block_id, fun_block_id, succ_type);

        self.switch_blocks(fun_block_id);
        let (entry_link_id, entry_args) =
            self.push_start_block_mem(def_func_type.clone(), Some(global_name), def_span_id, mem);

        // add entry to scope, for recursion
        let variant_ty = b.types.u.resolve(&def_func_type.clone().into()).unwrap();
        // we need to know the link
        let variant_id = self.variant_add(
            scope_id,
            local_name,
            variant_ty.clone(),
            entry_link_id,
            fun_block_id,
        );

        // add the name to scope
        // do this early for recursive functions
        self.blocks
            .scope_define(scope_id, global_name, entry_link_id);

        // flatten function, and switch to next
        self.switch_blocks(fun_block_id);
        let _ = self.push_node(body, PushContext::Default, b);
        self.maybe_terminate_block(next_block_id, def_span_id, PushContext::Function, b);

        let variant_ty = b.types.u.resolve(&variant_ty).unwrap();
        self.variant_update(variant_id, variant_ty.clone(), entry_link_id);

        let next_arg_ty =
            self.resolve_return_type(fun_block_id, def_func_type.into(), call_span_id, b);

        assert!(next_arg_ty.is_composite());
        let ret_block_ty = AstFuncType {
            args: next_arg_ty.clone().into(),
            ret: ReturnType::Single(AstType::Unit).into(),
        };

        (fun_block_id, entry_link_id, ret_block_ty, entry_args)
    }

    pub(super) fn push_call_arguments(
        &mut self,
        args: Vec<Argument>,
        span_id: SpanId,
        b: &mut NB,
    ) -> ArgVec {
        let mut link_ids = vec![];
        let mut values = vec![];
        for a in args.into_iter() {
            match a {
                Argument::Positional(expr) => {
                    let r = self.push_node(*expr, PushContext::Default, b);
                    let link_id = r.link_id.unwrap();
                    let entry = self.get_entry(link_id);
                    values.push((entry.name, link_id, entry.ty.clone(), span_id));
                    link_ids.push(link_id);
                }

                Argument::Named(key, expr) | Argument::System(key, expr) => {
                    let r = self.push_node(*expr, PushContext::Default, b);
                    let link_id = r.link_id.unwrap();
                    let entry = self.get_entry(link_id);
                    values.push((Some(key), link_id, entry.ty.clone(), span_id));
                    link_ids.push(link_id);
                }

                Argument::Args(key, exprs) => {
                    let mut args_values = vec![];
                    for expr in exprs {
                        let span_id = expr.span_id;
                        let r = self.push_node(expr, PushContext::Default, b);
                        let link_id = r.link_id.unwrap();
                        let ty = self.get_type(link_id).clone();
                        args_values.push((Some(key), link_id, ty, span_id));
                    }

                    self.push_call_values(&args_values, b);

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
                        VarDefinitionSpace::Default,
                    );
                    values.push((Some(key), link_id, struct_ty.clone(), span_id));
                    link_ids.push(link_id);
                }

                Argument::KwArgs(key, _expr) => {
                    let node: AstNode = 1.into();
                    let r = self.push_node(node, PushContext::Default, b);
                    let link_id = r.link_id.unwrap();
                    let ty = self.get_type(link_id).clone();
                    values.push((Some(key), link_id, ty, span_id));
                    link_ids.push(link_id);
                }
            }
        }
        values
    }

    pub fn push_function_call_arguments(
        &mut self,
        abstraction_id: AbstractionId,
        args: Vec<Argument>,
        system: Vec<Argument>,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> (
        ArgVec,
        AstFuncType, // call_func_type
        AstFuncType, // def_func_type
    ) {
        let a = self.abstractions.get(abstraction_id);
        let def_span_id = a.def_span_id;

        // look up the prototype
        // calculate the calling arguments
        let (args, def_func_type) = Self::calculate_function_arguments(
            &a.def,
            &args,
            &system,
            def_span_id,
            call_span_id,
            b,
        );
        let call_values = self.push_call_arguments(args.clone(), call_span_id, b);
        let call_ty = crate::argvec_type(&call_values);
        let def_func_type = self.refresh_func_type(&def_func_type, b);

        // construct call function type
        let call_func_type =
            AstFuncType::new(AstType::Struct(call_ty.fields()), def_func_type.ret.clone());

        b.unify(
            &call_func_type.clone().into(),
            call_span_id,
            &def_func_type.clone().into(),
            def_span_id,
        );
        (call_values, call_func_type, def_func_type)
    }

    pub(super) fn push_call(
        &mut self,
        scope_id: ScopeId,
        abstraction_id: AbstractionId,
        call_span_id: SpanId,
        args: Vec<Argument>,
        b: &mut NB,
    ) -> FlattenResult {
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

        let is_static = self.static_scope_id() == scope_id;
        //let blocks = vec![];
        if is_static {
            let (call_values, call_func_type, def_func_type) =
                self.push_function_call_arguments(abstraction_id, args, vec![], call_span_id, b);
            let r = self.push_bake_static(abstraction_id, call_func_type, call_span_id, b);
            let (fun_link_id, _bake_ty) = r;
            self.switch_blocks(current_block_id);
            self.push_function_call(
                fun_link_id,
                call_values,
                def_func_type.ret.clone(),
                call_span_id,
                b,
            )
        } else {
            self.switch_blocks(current_block_id);

            // call the inline function
            // returns a link, which points to the result, which should be a single value
            // if it's void, then it's a statement
            // We want to support both of these options
            // TODO: break this out into a compile parameter for the function
            if false {
                self.push_call_inline(abstraction_id, scope_id, args, call_span_id, b)
            } else {
                self.push_call_inline_cps(abstraction_id, scope_id, args, call_span_id, b)
            }
        }
    }

    fn push_call_inline(
        &mut self,
        abstraction_id: AbstractionId,
        scope_id: ScopeId,
        args: Vec<Argument>,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> FlattenResult {
        // we inline here for nested functions
        // we bake the lambda, and then jump to it
        // This is a very simple inliner, that doesn't rewrite the function signature
        // We make a new function each time we call it, which is inefficient if we
        // call it multiple times.

        // start the call
        // calculate the arguments
        let (call_values, _call_func_type, def_func_type) =
            self.push_function_call_arguments(abstraction_id, args, vec![], call_span_id, b);

        // bookmark this position, to continue later
        let current_block_id = self.current_block_id();

        let a = self.abstractions.get(abstraction_id);
        let name = a.name;

        let s_name = b.labels.r(name.into());
        let global_name = b.labels.fresh_key(&s_name);

        // create a new block
        let scope = self.blocks.get_scope(scope_id);
        let scope_block_id = scope.entry_block();
        let next_block_id = self
            .blocks
            .new_block(scope_block_id, scope_id, Successor::BlockScope);

        // New Func Scope
        let (fun_block_id, fun_scope_id) = self.blocks.new_scope_and_block(
            ScopeType::Function,
            ScopeState::function(next_block_id),
            current_block_id,
            Successor::BlockScope,
        );

        let result = self.push_bake_lambda_and_update_next(
            abstraction_id,
            global_name,
            fun_scope_id,
            fun_block_id,
            next_block_id,
            def_func_type.clone(),
            call_span_id,
            Successor::BlockScope,
            VarDefinitionSpace::Reg,
            b,
        );

        let (fun_block_id, _, next_arg_ty, _, _, r, _entry_args) = result;

        // now that we have the arguments calculated, and the lambda baked, jump!

        // Complete the call, returning cursor to the caller
        self.switch_blocks(current_block_id);

        // DECLARE
        // if the function returns a value, then we need to copy it out of the next block arguments
        // this should be unique per call
        let decl = if let Some(link_id) = r.link_id {
            let key = b.labels.fresh_key("r");
            let ty = next_arg_ty.field_types().first().unwrap().clone();
            let decl_link_id = self.push_decl(ty.clone(), key, call_span_id);
            Some((decl_link_id, link_id, ty, key))
        } else {
            None
        };

        // JUMP
        // jump into the the lambda
        self.push_jump(fun_block_id.into(), call_values, call_span_id, b);

        self.switch_blocks(next_block_id);

        // STORE ARG
        // r contains the link to the return value
        // r contains the return result link, which is part of the next block arguments.
        if let Some((decl_link_id, arg_link_id, _ty, _key)) = decl {
            // specify that the arg is stored on the stack
            // let mlir handle the rest
            let entry = self.get_entry_mut(arg_link_id);
            entry.mem = VarDefinitionSpace::Stack(decl_link_id);
            FlattenResult::link(decl_link_id)
        } else {
            r
        }
    }

    fn push_call_inline_cps(
        &mut self,
        abstraction_id: AbstractionId,
        scope_id: ScopeId,
        args: Vec<Argument>,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> FlattenResult {
        // create a new block static blocks, which is the final destination
        let scope = self.blocks.get_scope(scope_id);
        let scope_block_id = scope.entry_block();
        let exit_block_id = self
            .blocks
            .new_block(scope_block_id, scope_id, Successor::BlockScope);

        let key = b.labels.fresh_key("b");
        let mut system = vec![];
        let arg = Argument::System(
            key,
            Ast::Literal(Literal::Block(exit_block_id))
                .node(call_span_id)
                .into(),
        );
        system.push(arg);

        // Entry arguments, including continuation
        // calculate the arguments for the CPS function
        let (call_values, _call_func_type, top_def_func_type) =
            self.push_function_call_arguments(abstraction_id, args, system, call_span_id, b);

        let arg = call_values.last().unwrap();
        let _arg_index = call_values.len() - 1;
        let call_link_id = arg.1;
        let next_ty = arg.2.clone();

        self.update_connections(call_link_id);

        // bookmark position
        let current_block_id = self.current_block_id();

        // generate the CPS function, that's it
        // and jump to it, passing the exit continuation
        let (fun_block_id, ret_block_ty) = self.push_call_inline_cps_inner(
            abstraction_id,
            scope_id,
            call_span_id,
            top_def_func_type.clone(),
            b,
        );
        let next_arg_ty = ret_block_ty.args.clone();

        b.unify(
            &next_ty,
            call_span_id,
            &ret_block_ty.clone().into(),
            call_span_id,
        );

        let a = self.abstractions.get(abstraction_id);
        // push the continuation block to which the function returns control
        // this might just be the return block
        let s_name = b.labels.r(a.name.into());
        let cont_name = format!("{}.exit", s_name);
        let cont_key = b.labels.fresh_key(&cont_name);

        // block graph
        self.blocks
            .block_succ(current_block_id, fun_block_id, Successor::BlockScope);
        self.blocks
            .block_succ(fun_block_id, exit_block_id, Successor::BlockScope);

        self.switch_blocks(exit_block_id);
        let (_v_block, v_args) =
            self.push_start_block(ret_block_ty.clone().into(), Some(cont_key), call_span_id);

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

        // Call the lambda that we just created
        // now that we have the arguments calculated, and the lambda baked, jump!
        self.switch_blocks(current_block_id);

        // DECLARE
        // if the function returns a value, then we need to copy it out of the next block arguments
        let v_decl = if let Some(link_id) = r.link_id {
            let key = b.labels.fresh_key("r");
            let ty = next_arg_ty.field_types().first().unwrap().clone();
            let decl_link_id = self.push_decl(ty.clone(), key, call_span_id);
            let entry = self.get_entry_mut(link_id);
            entry.mem = VarDefinitionSpace::Stack(decl_link_id);
            Some(decl_link_id)
        } else {
            None
        };

        // jump into the the lambda
        let _goto_link_id =
            self.push_jump(fun_block_id.into(), call_values.clone(), call_span_id, b);

        self.switch_blocks(exit_block_id);
        // in the next block

        // STORE ARG
        // r contains the link to the return value
        // r contains the return result link, which is part of the next block arguments.
        if let Some(decl_link_id) = v_decl {
            FlattenResult::link(decl_link_id)
        } else {
            // r contains the link to the return value
            r
        }
    }

    fn push_call_inline_cps_inner(
        &mut self,
        abstraction_id: AbstractionId,
        scope_id: ScopeId,
        call_span_id: SpanId,
        def_func_type: AstFuncType,
        b: &mut NB,
    ) -> (BlockId, AstFuncType) {
        let a = self.abstractions.get(abstraction_id);
        let lookup_name = a.name;
        let def_span_id = a.def_span_id;
        let succ_type = Successor::BlockScope;
        let mem = VarDefinitionSpace::Reg;

        let call_func_type = def_func_type.clone().into();
        let (fun_block_id, ret_block_ty) = if let Some((variant_ty, link_id, _fun_scope_id)) =
            self.resolve_function_name(scope_id, &lookup_name, &call_func_type, b)
        {
            let entry = self.get_entry(link_id);
            let fun_block_id = entry.block_id;

            let ty = variant_ty.clone().into();
            b.unify(&ty, call_span_id, &variant_ty, def_span_id);
            let variant_ty = b.types.u.resolve(&variant_ty).unwrap();
            let resolve_func_type = variant_ty.get_func().clone();
            let ret_func_type = if let ReturnType::Single(ret) = resolve_func_type.ret {
                AstFuncType::new(
                    AstType::build_struct(vec![ret]),
                    ReturnType::Single(AstType::Unit),
                )
            } else {
                unimplemented!();
            };
            (fun_block_id, ret_func_type)
        } else {
            let scope = self.blocks.get_scope(scope_id);
            let block_id = scope.entry_block();

            // New Func Scope
            let (fun_block_id, fun_scope_id) = self.blocks.new_scope_and_block(
                ScopeType::Function,
                // hack: we turn this into function scope later
                //ScopeState::function(next_block_id),
                ScopeState::block(),
                block_id,
                Successor::BlockScope,
            );

            // hack: this needs to be defined after fun_block, for some reason
            // The ordering shouldn't matter
            let next_block_id = self.blocks.new_block(block_id, fun_scope_id, succ_type);

            let result = self.push_bake_lambda_and_update_next(
                abstraction_id,
                lookup_name,
                fun_scope_id,
                fun_block_id,
                next_block_id,
                def_func_type,
                call_span_id,
                succ_type,
                mem,
                b,
            );
            let (fun_block_id, _, _next_arg_ty, call_values, ret_func_type, _, entry_args) = result;
            let arg = entry_args.last().unwrap();

            let call_link_id = arg.1;

            // complete the lambda bake with a jump to the continuation, this is the exit of
            // the lambda.  The continuation is part of the signature, so we can call it again
            let _goto_link_id =
                self.push_goto_link(call_link_id, call_values.clone(), call_span_id, b);

            (fun_block_id, ret_func_type)
        };

        // restore position back to where we started
        (fun_block_id, ret_block_ty)
    }
}
