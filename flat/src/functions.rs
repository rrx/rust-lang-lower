use crate::{
    ArgVec, BlockId, BlockifyError, ContinuationFlow, Flatten, FlattenResult, FlowEdge, LCode,
    LinkId, NodeBuilder as NB, ScopeId, ScopeType, Successor,
};
use anyhow::Error;
use anyhow::Result;
use compile_core::{
    AbstractionId, Argument, Ast, AstFuncType, AstNode, AstType, Lambda, Literal, NaryOperation,
    ReturnType, SpanId, StringKey, VarDefinitionSpace,
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
    //pub caller_blocks: HashSet<BlockId>,
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

    pub fn add(&mut self, def: Lambda, def_span_id: SpanId) -> AbstractionId {
        let index = self.0.len();
        self.0.push(Abstraction {
            def,
            def_span_id,
            //caller_blocks: HashSet::new(),
        });
        AbstractionId::new(index)
    }
}

impl Flatten {
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
    ) -> Result<(Vec<Argument>, AstFuncType)> {
        //println!("args: {:?}", args);

        let func_arg = b.types.r(def.arg_type).clone();

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
        }

        if args_seq.len() > 0 && def_has_args {
            // extra fields
            b.push_error(
                &format!("extra fields, no args field: {:?}", args_seq),
                call_span_id,
            );
        }

        let def_ret_type = b.types.r(def.return_type).clone();
        let def_func_type = AstFuncType::new(
            AstType::Struct(fields_list),
            ReturnType::Single(def_ret_type),
        );

        Ok((args, def_func_type))
    }

    fn push_bake_static(
        &mut self,
        name: StringKey,
        abstraction_id: AbstractionId,
        call_func_type: AstFuncType,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> Result<(LinkId, AstType)> {
        let s = b.labels.r(name.into());
        let global_key = b.labels.fresh_key(&s);
        //let s_global = b.labels.r(global_key.into());
        let current_block_id = self.current_block_id();
        self.switch_blocks(self.static_block_id());
        let block = self.blocks.get_block(current_block_id);

        let a = self.abstractions.get(abstraction_id);
        //let def = a.def.clone();
        let def_span_id = a.def_span_id;

        // if it's defined in static scope, just call it
        let (_variant_id, v_entry) = if let Some((variant_id, r_ty, v_entry, _scope_id)) =
            self.resolve_function_name(block.scope_id, &name, &call_func_type.clone().into(), b)
        {
            // unify the resolved function with the caller
            // the function should be resolved, this resolves any thing missing in the caller
            b.unify(
                &call_func_type.clone().into(),
                call_span_id,
                &r_ty,
                def_span_id,
            );
            (variant_id, v_entry)
        } else {
            // if it's not already baked, we need to do that here
            self.switch_blocks(self.static_block_id());

            let result = self.push_bake_function(
                abstraction_id,
                call_func_type.clone(),
                name,
                global_key,
                b,
            );
            let (variant_id, r) = result?;
            let v_entry = r.link_id.unwrap();
            self.switch_blocks(current_block_id);
            let r_ty2 = b.types.u.resolve(&call_func_type.clone().into()).unwrap();

            // update the variant with the resolved type
            self.variant_update(variant_id, r_ty2.clone(), v_entry);
            (variant_id, v_entry)
        };

        // we are keeping a list of function names so we can look them up later
        // there's a better way to do this.  A function only makes sense in the context of a call
        // so our lookups should actually be resolved by the caller
        self.functions.insert(name, v_entry);

        Ok((v_entry, call_func_type.into()))
    }

    pub fn push_bake(
        &mut self,
        name: StringKey,
        func_type: AstFuncType,
        b: &mut NB,
    ) -> Result<LinkId> {
        let current_block_id = self.current_block_id();
        if let Some((_, abstraction_id)) = self.resolve_lambda(current_block_id, name) {
            let result = self.push_bake_function(abstraction_id, func_type, name, name, b);
            let (_variant_id, r) = result?;
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
        name: StringKey,
        global_name: StringKey,
        b: &mut NB,
    ) -> Result<(VariantId, FlattenResult)> {
        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        let scope_id = block.scope_id;

        let a = self.abstractions.get(abstraction_id);
        let def_span_id = a.def_span_id;
        let body = a.def.body.clone().unwrap();

        // create a next scope, that includes the function
        // when the function returns it jumps to the return block, which is the next function
        // which is out of scope for the function.  This requires that the function cleanup the
        // stack before jumping to the return block
        // This scope is empty, and isn't used for anything other than including the function scope
        // This behavior is slightly different than inline functions that jump back into the same
        // scope from which they were called.

        let (next_block_id, next_scope_id) = self.new_scope_and_block(ScopeType::Block, scope_id);

        let (v_id, _scope, _block_id, entry_link_id, _, argvec, _, _, _, entry_args) = self
            .push_bake_lambda_and_update_next(
                name,
                global_name,
                next_scope_id,
                next_block_id,
                *body,
                def_func_ty,
                def_span_id,
                def_span_id,
                ScopeType::Function,
                Successor::FunctionDeclaration,
                VarDefinitionSpace::Static,
                b,
            )?;

        self.push_return(argvec, def_span_id);
        // restore position back to where we started
        self.switch_blocks(current_block_id);
        Ok((v_id, FlattenResult::link(entry_link_id)))
    }

    fn push_bake_lambda_and_update_next(
        &mut self,
        local_name: StringKey,
        global_name: StringKey,
        next_scope_id: ScopeId,
        next_block_id: BlockId,
        body: AstNode,
        def_func_type: AstFuncType,
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
        AstType,     // next block arg type
        ArgVec,      // return the argvec for the next block, which depends on the function
        AstFuncType, // next block return type
        AstType,     // variant type
        FlattenResult,
        ArgVec, // entry args
    )> {
        let result = self.push_bake_lambda(
            local_name,
            global_name,
            next_scope_id,
            next_block_id,
            body,
            def_func_type,
            def_span_id,
            call_span_id,
            scope_type,
            succ_type,
            mem,
            b,
        )?;

        let (
            variant_id,
            fun_scope_id,
            fun_block_id,
            entry_link_id,
            next_arg_ty,
            ret_block_ty,
            variant_ty,
            entry_args,
        ) = result;

        // push the continuation block to which the function returns control
        // this might just be the return block
        let s_name = b.labels.r(local_name.into());
        let cont_name = format!("{}.next", s_name);

        self.switch_blocks(next_block_id);

        let (_v_block, v_args) = self.push_start_block(
            next_scope_id,
            ret_block_ty.clone().into(),
            Some(b.labels.fresh_key(&cont_name)),
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
            ret_block_ty,
            variant_ty,
            r,
            entry_args,
        ))
    }

    fn push_bake_lambda(
        &mut self,
        local_name: StringKey,
        global_name: StringKey,
        next_scope_id: ScopeId,
        next_block_id: BlockId,
        body: AstNode,
        def_func_type: AstFuncType,
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
        AstFuncType, // next block return type
        AstType,     // variant type
        ArgVec,      // entry args
    )> {
        // lower a function as an inline block
        // returning from the function passes control the next block which is static
        //
        // create a new scope and block
        // build the function body in that scope and block
        // allow for recursion
        //
        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        let scope_id = block.scope_id;

        let block_ty: AstType = def_func_type.into();

        // New Func Scope
        let (fun_block_id, fun_scope_id) = self.new_scope_and_block(scope_type, next_scope_id);

        let fun_scope = self.scopes.get_scope_mut(fun_scope_id);
        fun_scope.return_block = Some(next_block_id);

        // block graph
        self.blocks
            .block_succ(current_block_id, fun_block_id, succ_type);

        self.switch_blocks(fun_block_id);
        let (entry_link_id, entry_args) = self.push_start_block(
            fun_scope_id,
            block_ty.clone(),
            Some(global_name),
            def_span_id,
            mem,
        );

        // add entry to scope, for recursion
        let variant_ty = b.types.u.resolve(&block_ty).unwrap();
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
        self.scopes
            .scope_define(scope_id, global_name, entry_link_id);

        // flatten function, and switch to next
        self.switch_blocks(fun_block_id);
        let _ = self.push_node(body, b)?;
        self.maybe_terminate_block(next_block_id, def_span_id);

        let variant_ty = b.types.u.resolve(&variant_ty).unwrap();
        self.variant_update(variant_id, variant_ty.clone(), entry_link_id);

        let next_arg_ty = self.resolve_return_type(fun_block_id, block_ty.into(), call_span_id, b);
        println!("next_arg_ty: {}", next_arg_ty);

        assert!(next_arg_ty.is_composite());
        let ret_block_ty = AstFuncType {
            args: next_arg_ty.clone().into(),
            ret: ReturnType::Single(AstType::Unit).into(),
        };

        Ok((
            variant_id,
            fun_scope_id,
            fun_block_id,
            entry_link_id,
            next_arg_ty,
            ret_block_ty,
            variant_ty,
            entry_args,
        ))
    }

    pub(super) fn push_call_arguments(
        &mut self,
        args: Vec<Argument>,
        //blocks: ArgVecRef,
        span_id: SpanId,
        b: &mut NB,
    ) -> Result<ArgVec> {
        let mut link_ids = vec![];
        let mut values = vec![];
        for a in args.into_iter() {
            match a {
                Argument::Positional(expr) => {
                    //if let AstNode::Literal(Literal::Block(block_id)) = expr {
                    //} else {
                    let r = self.push_node(*expr, b)?;
                    let link_id = r.link_id.unwrap();
                    let entry = self.get_entry(link_id);
                    values.push((entry.name, link_id, entry.ty.clone(), span_id));
                    link_ids.push(link_id);
                    //}
                }

                Argument::Named(key, expr) | Argument::System(key, expr) => {
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
                    let r = self.push_node(node, b)?;
                    let link_id = r.link_id.unwrap();
                    let ty = self.get_type(link_id).clone();
                    values.push((Some(key), link_id, ty, span_id));
                    link_ids.push(link_id);
                }
            }
        }
        //for (key, link_id, ty, span_id) in blocks.iter() {
        //values.push((*key, *link_id, ty.clone(), *span_id));
        //link_ids.push(*link_id);
        //}
        Ok(values)
    }

    pub fn push_function_call_arguments(
        &mut self,
        abstraction_id: AbstractionId,
        args: Vec<Argument>,
        system: Vec<Argument>,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> Result<(
        ArgVec,
        AstFuncType, // call_func_type
        AstFuncType, // def_func_type
    )> {
        let a = self.abstractions.get(abstraction_id);
        let def_span_id = a.def_span_id;

        // look up the prototype
        // calculate the calling arguments
        println!("args1: {:?}", args);
        let (args, def_func_type) = Self::calculate_function_arguments(
            &a.def,
            &args,
            &system,
            def_span_id,
            call_span_id,
            b,
        )?;
        println!("args2: {:?}", args);
        let call_values = self.push_call_arguments(args.clone(), call_span_id, b)?;
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
        Ok((call_values, call_func_type, def_func_type))
    }

    pub(super) fn push_call(
        &mut self,
        name: StringKey,
        scope_id: ScopeId,
        abstraction_id: AbstractionId,
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

        let is_static = self.static_scope_id() == scope_id;
        //let blocks = vec![];
        if is_static {
            let (call_values, call_func_type, def_func_type) =
                self.push_function_call_arguments(abstraction_id, args, vec![], call_span_id, b)?;
            let r = self.push_bake_static(name, abstraction_id, call_func_type, call_span_id, b)?;
            let (fun_link_id, _bake_ty) = r;
            self.switch_blocks(current_block_id);
            self.push_function_call(
                fun_link_id,
                call_values,
                def_func_type.ret.clone(),
                call_span_id,
            )
        } else {
            self.switch_blocks(current_block_id);

            // call the inline function
            // returns a link, which points to the result, which should be a single value
            // if it's void, then it's a statement
            if true {
                // calculate the arguments
                // start the call
                let (call_values, _call_func_type, def_func_type) = self
                    .push_function_call_arguments(abstraction_id, args, vec![], call_span_id, b)?;

                // bookmark
                let current_block_id = self.current_block_id();

                let (fun_block_id, call_values, next_block_id, r) = self.push_call_inline(
                    abstraction_id,
                    name,
                    scope_id,
                    call_values,
                    def_func_type,
                    call_span_id,
                    b,
                )?;
                // now that we have the arguments calculated, and the lambda baked, jump!

                // Complete the call
                self.switch_blocks(current_block_id);
                // jump into the the lambda
                self.push_jump(fun_block_id.into(), call_values, call_span_id);

                self.switch_blocks(next_block_id);

                // r contains the return result link, which is part of the next block arguments.
                Ok(r)
            } else {
                self.push_call_inline_cps(abstraction_id, name, scope_id, args, call_span_id, b)
            }
        }
    }

    fn push_call_inline(
        &mut self,
        abstraction_id: AbstractionId,
        name: StringKey,
        scope_id: ScopeId,
        call_values: ArgVec,
        def_func_type: AstFuncType,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> Result<(BlockId, ArgVec, BlockId, FlattenResult)> {
        // we inline here for nested functions
        // we bake the lambda, and then jump to it
        // This is a very simple inliner, that doesn't rewrite the function signature
        // We make a new function each time we call it, which is inefficient if we
        // call it multiple times.

        // bookmark this position, to continue later
        //let current_block_id = self.current_block_id();

        let a = self.abstractions.get(abstraction_id);
        let body = a.def.body.clone().unwrap();
        let def_span_id = a.def_span_id;

        let s_name = b.labels.r(name.into());
        let global_name = b.labels.fresh_key(&format!("{}.call", s_name));
        // create a new block
        let next_block_id = self.blocks.new_block(scope_id);
        println!("body: {:?}", body);
        let result = self.push_bake_lambda_and_update_next(
            name,
            global_name,
            scope_id,
            next_block_id,
            *body,
            def_func_type.clone(),
            def_span_id,
            call_span_id,
            ScopeType::Function,
            Successor::BlockScope,
            VarDefinitionSpace::Reg,
            b,
        )?;
        let (_variant_id, _, fun_block_id, _, _next_arg_ty, _, _, _, r, entry_args) = result;

        // lambda is incomplete
        // waiting for the final jump

        // r contains the link to the return value
        Ok((fun_block_id, call_values, next_block_id, r))
    }

    fn push_call_inline_cps(
        &mut self,
        abstraction_id: AbstractionId,
        name: StringKey,
        scope_id: ScopeId,
        args: Vec<Argument>,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        // create a new block static blocks, which is the final destination
        let exit_block_id = self.blocks.new_block(scope_id);

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
            self.push_function_call_arguments(abstraction_id, args, system, call_span_id, b)?;

        let arg = call_values.last().unwrap();
        let _arg_index = call_values.len() - 1;
        let call_link_id = arg.1;
        println!("call_link_id1: {}", call_link_id);
        let next_ty = arg.2.clone();

        self.scoped_continuations.connect(
            ContinuationFlow::Block(exit_block_id),
            ContinuationFlow::Variable(call_link_id),
            FlowEdge::VarJumpArgInline,
        );

        // bookmark position
        let current_block_id = self.current_block_id();

        let s_name = b.labels.r(name.into());
        println!("s_name: {}", s_name);
        println!("top_def_func_type: {:?}", top_def_func_type);

        // generate the CPS function, that's it
        // and jump to it, passing the exit continuation
        let result = self.push_call_inline_cps_inner(
            abstraction_id,
            name,
            scope_id,
            call_link_id,
            call_span_id,
            top_def_func_type.clone(),
            b,
        )?;
        let (fun_block_id, ret_block_ty, next_arg_ty) = result;
        println!("fun_block_id: {}", fun_block_id);

        b.unify(
            &next_ty,
            call_span_id,
            &ret_block_ty.clone().into(),
            call_span_id,
        );

        //self.switch_blocks(current_block_id);
        println!("top_def_func_type: {}", top_def_func_type);
        let r_ty = b.types.u.resolve(&top_def_func_type.into()).unwrap();
        println!("r_ty: {}", r_ty);

        // push the continuation block to which the function returns control
        // this might just be the return block
        let s_name = b.labels.r(name.into());
        let cont_name = format!("{}.exit", s_name);
        let cont_key = b.labels.fresh_key(&cont_name);

        // block graph
        self.blocks
            .block_succ(current_block_id, fun_block_id, Successor::BlockScope);
        self.blocks
            .block_succ(fun_block_id, exit_block_id, Successor::BlockScope);

        self.switch_blocks(exit_block_id);
        let (_v_block, v_args) = self.push_start_block(
            scope_id,
            ret_block_ty.clone().into(),
            Some(cont_key),
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

        // Call the lambda that we just created
        // now that we have the arguments calculated, and the lambda baked, jump!
        self.switch_blocks(current_block_id);
        // jump into the the lambda
        let goto_link_id = self.push_jump(fun_block_id.into(), call_values.clone(), call_span_id);

        for (i, (_, var_link_id, _ty, _)) in call_values.iter().enumerate() {
            self.scoped_continuations.connect(
                ContinuationFlow::Variable(*var_link_id),
                ContinuationFlow::JumpArg(goto_link_id, i as u8),
                FlowEdge::VarJumpArgInline,
            );
            self.scoped_continuations.connect(
                ContinuationFlow::JumpArg(goto_link_id, i as u8),
                ContinuationFlow::BlockArg(fun_block_id, i as u8),
                FlowEdge::JumpArgInline,
            );
        }

        //self.scoped_continuations.connect(
        //ContinuationFlow::Variable(call_link_id),
        //ContinuationFlow::Jump(goto_link_id),
        //FlowEdge::JumpArg,
        //);
        self.scoped_continuations.connect(
            ContinuationFlow::Jump(goto_link_id),
            ContinuationFlow::Block(fun_block_id),
            FlowEdge::JumpInline,
        );

        self.switch_blocks(exit_block_id);
        // in the next block

        // r contains the link to the return value
        Ok(r)
    }

    fn push_call_inline_cps_inner(
        &mut self,
        abstraction_id: AbstractionId,
        name: StringKey,
        scope_id: ScopeId,
        call_link_id: LinkId,
        call_span_id: SpanId,
        def_func_type: AstFuncType,
        b: &mut NB,
    ) -> Result<(BlockId, AstFuncType, AstType)> {
        let a = self.abstractions.get(abstraction_id);
        println!("a: {:?}", a);
        let def_span_id = a.def_span_id;
        let scope_type = ScopeType::Function;
        let succ_type = Successor::BlockScope;
        let mem = VarDefinitionSpace::Reg;

        let call_func_type = def_func_type.clone().into();
        let (_variant_id, fun_block_id, _fun_scope_id, _def_func_type, ret_block_ty, next_arg_ty) =
            if let Some((variant_id, variant_ty, link_id, fun_scope_id)) =
                self.resolve_function_name(scope_id, &name, &call_func_type, b)
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
                let next_arg_ty = resolve_func_type.args.clone();
                println!("fun_block_id2: {}", fun_block_id);
                println!("variant_ty2: {}", variant_ty);
                println!("ret_func_type2: {}", ret_func_type);
                println!("next_arg_ty2: {}", next_arg_ty);
                (
                    variant_id,
                    fun_block_id,
                    fun_scope_id,
                    variant_ty,
                    ret_func_type,
                    next_arg_ty,
                )
            } else {
                // create the new empty block
                let next_block_id = self.blocks.new_block(scope_id);
                println!("next_block_id2: {}", next_block_id);

                let body = a.def.body.clone().unwrap();
                let result = self.push_bake_lambda_and_update_next(
                    name,
                    name,
                    scope_id,
                    next_block_id,
                    *body,
                    def_func_type,
                    def_span_id,
                    call_span_id,
                    scope_type,
                    succ_type,
                    mem,
                    b,
                )?;
                let (
                    variant_id,
                    fun_scope_id,
                    fun_block_id,
                    _,
                    next_arg_ty,
                    call_values,
                    ret_func_type,
                    variant_ty,
                    _,
                    entry_args,
                ) = result;
                println!("fun_block_id1: {}", fun_block_id);
                println!("variant_ty1: {}", variant_ty);
                println!("ret_func_type1: {}", ret_func_type);
                println!("next_arg_ty1: {}", next_arg_ty);

                let arg = entry_args.last().unwrap();
                //let arg_index = call_values.len() - 1;
                let call_link_id = arg.1;
                println!("call_link_id2: {}", call_link_id);
                //let next_ty = arg.2.clone();

                let _ = self.push_call_values(&call_values);
                // complete the lambda bake with a jump to the continuation, this is the exit of
                // the lambda.  The continuation is part of the signature, so we can call it again
                let _goto_link_id =
                    self.push_goto_link(call_link_id, call_values.clone(), call_span_id)?;

                (
                    variant_id,
                    fun_block_id,
                    fun_scope_id,
                    variant_ty,
                    ret_func_type,
                    next_arg_ty,
                )
            };

        // restore position back to where we started
        Ok((fun_block_id, ret_block_ty, next_arg_ty))
    }
}
