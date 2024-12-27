use anyhow::Result;
use compile_core::{
    AbstractionId, Argument, AstFuncType, AstType, Literal, ReturnType, SpanId, StringKey,
};

use std::convert::Into;

use crate::{
    argvec_type, ArgVec, BlockId, ContinuationFlow, DeferredGoto, DeferredType, FlattenInner,
    FlattenResult, FlowEdge, LCode, LinkId, NodeBuilder as NB, ScopeId, ScopeState, ScopeType,
    Successor, VarDefinitionSpace, VariantId,
};

impl FlattenInner {
    pub(super) fn push_cps_block_with_type(
        &mut self,
        name: StringKey,
        scope_id: ScopeId,
        abstraction_id: AbstractionId,
        call_func_type: &AstType,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> Result<(VariantId, ScopeId, BlockId, AstType)> {
        let s_name = b.labels.r(name.into());
        // call in the context of the caller, which is a goto
        let current_block_id = self.current_block_id();

        let a = self.abstractions.get(abstraction_id);
        let def_span_id = a.def_span_id;
        let func_type = b.types.r(a.def.fun_type).get_func().clone();
        let mut func_type = self.refresh_func_type(&func_type, b);
        func_type.ret = ReturnType::Never;
        let call_arg_type = AstType::Struct(call_func_type.fields());
        b.unify(&call_arg_type, call_span_id, &func_type.args, def_span_id);

        let def_func_type = func_type.into();
        b.unify(&def_func_type, call_span_id, &call_func_type, def_span_id);

        let (variant_id, fun_block_id, fun_scope_id, def_arg_type) =
            if let Some((variant_id, resolve_type, link_id, fun_scope_id)) =
                self.resolve_function_name(scope_id, &name, &call_arg_type, b)
            {
                let entry = self.get_entry(link_id);
                let fun_block_id = entry.block_id;
                b.unify(&call_arg_type, call_span_id, &resolve_type, def_span_id);
                (variant_id, fun_block_id, fun_scope_id, resolve_type)
            } else {
                let scope = self.blocks.get_scope(scope_id);
                let block_id = scope.entry_block();

                let (fun_block_id, fun_scope_id) = self.blocks.new_scope_and_block(
                    ScopeType::Block,
                    ScopeState::block(),
                    block_id,
                    scope_id,
                    Successor::BlockScope,
                );
                self.blocks.control_flow(block_id, &[fun_block_id]);

                // Start lambda block
                let lambda_name = b.labels.fresh_key(&s_name);

                // make a copy of the body
                let a = self.abstractions.get(abstraction_id);
                let body = a.def.body.clone().unwrap();

                self.switch_blocks(fun_block_id);

                let r_ty1 = b.types.u.resolve(&def_func_type.into()).unwrap();

                let (entry_link_id, _) = self.push_start_block(
                    fun_scope_id,
                    r_ty1.clone(),
                    Some(lambda_name),
                    def_span_id,
                    VarDefinitionSpace::Default,
                );
                // add the name to scope
                // do this early for recursive functions
                // add entry to scope, for recursion
                self.blocks
                    .scope_define(scope_id, lambda_name, entry_link_id);

                let variant_id =
                    self.variant_add(scope_id, name, r_ty1.clone(), entry_link_id, fun_block_id);

                // flatten function, and switch to next
                // lower first, so we resolve types
                let _ = self.push_node(*body, b)?;

                let r_ty2 = b
                    .types
                    .u
                    .resolve(&call_arg_type)
                    .unwrap_or(call_arg_type.clone());
                self.variant_update(variant_id, r_ty2.clone(), entry_link_id);

                // terminate if not already terminated
                // this is for dead code
                let block = self.blocks.get_block(self.current_block_id());
                if !block.is_term() {
                    self.push_placeholder_terminal(block.last().unwrap(), r_ty1, def_span_id);
                    //println!("placeholder4: {}", p_link_id);
                }

                (variant_id, fun_block_id, fun_scope_id, r_ty2)
            };

        self.switch_blocks(current_block_id);

        Ok((variant_id, fun_scope_id, fun_block_id, def_arg_type))
    }

    pub(super) fn push_cps_block(
        &mut self,
        name: StringKey,
        scope_id: ScopeId,
        abstraction_id: AbstractionId,
        args: Vec<Argument>,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> Result<(
        VariantId,
        ScopeId,
        BlockId,
        AstType,
        AstType,
        ReturnType,
        ArgVec,
        LinkId, // return goto link
    )> {
        // call in the context of the caller, which is a goto
        let a = self.abstractions.get(abstraction_id);
        let def_span_id = a.def_span_id;
        let def = a.def.clone();

        //let fun_scope = self.blocks.get_scope_mut(fun_scope_id);
        // we might want to handle this later
        // return in a CPS will return from the scoped function
        //fun_scope.return_block = Some(next_block_id);
        //
        // WRITE GOTO
        let (args, _) =
            Self::calculate_function_arguments(&def, &args, &[], def_span_id, call_span_id, b)?;
        let call_values = self.push_call_arguments(args, call_span_id, b)?;
        let goto_block_id = self.current_block_id();
        let block = self.blocks.get_block(goto_block_id);
        let goto_scope_id = block.scope_id;
        //let s_name = b.labels.r(name.into());
        let call_arg_type = argvec_type(&call_values);
        let call_func_type =
            AstFuncType::new(call_arg_type.clone().into(), ReturnType::Never.into()).into();

        let (variant_id, fun_scope_id, fun_block_id, def_arg_type) = self
            .push_cps_block_with_type(
                name,
                scope_id,
                abstraction_id,
                &call_func_type,
                call_span_id,
                b,
            )?;

        self.switch_blocks(goto_block_id);
        // NOW JUMP
        // now that we have the arguments calculated, and the lambda baked, jump!
        self.remove_placeholder_terminal(goto_block_id);

        let _call_links = call_values
            .iter()
            .map(|(_, link_id, _, _)| *link_id)
            .collect::<Vec<_>>();

        // TODO: now that we know the target, we need to replace any call values with unwind
        // functions. We also need to do this for the goto_block_id.
        let unwind_scopes = self.blocks.unwind_scopes(fun_scope_id, goto_scope_id)?;
        println!("unwind scopes: {:?}", unwind_scopes);

        let goto_link_id =
            self.push_jump(fun_block_id.into(), call_values.clone(), call_span_id, b);

        for (i, (_, var_link_id, _ty, _)) in call_values.iter().enumerate() {
            self.scoped_continuations.connect(
                ContinuationFlow::Variable(*var_link_id),
                ContinuationFlow::JumpArg(goto_link_id, i as u8),
                FlowEdge::VarJumpArg,
            );
            self.scoped_continuations.connect(
                ContinuationFlow::JumpArg(goto_link_id, i as u8),
                ContinuationFlow::BlockArg(fun_block_id, i as u8),
                FlowEdge::JumpArg,
            );
        }

        self.scoped_continuations.connect(
            ContinuationFlow::Jump(goto_link_id),
            ContinuationFlow::Block(fun_block_id),
            FlowEdge::Jump,
        );

        // if this really is a CPS function, then it should never return
        // TODO: verify that it never returns, could be with the function signature
        // If the function returns, it has no meaning, because a goto must be terminal,
        // it's too confusing to try to treat it like a call in that case, it's better
        // to just error out
        // What does it even mean that a CPS function never calls it's continuation?

        // control is returned to the goto

        let def_func_type = AstFuncType::new(def_arg_type.clone(), ReturnType::Never).into();
        let def_ret_type = ReturnType::Never;

        return Ok((
            variant_id,
            fun_scope_id,
            fun_block_id,
            def_func_type,
            def_arg_type,
            def_ret_type,
            call_values,
            goto_link_id,
        ));
    }

    pub fn push_placeholder_terminal(
        &mut self,
        link_id: LinkId,
        ty: AstType,
        call_span_id: SpanId,
    ) -> LinkId {
        self.push_code(
            LCode::PlaceholderTerminal(link_id),
            ty,
            None,
            call_span_id,
            VarDefinitionSpace::Default,
        )
    }

    pub fn push_goto_link(
        &mut self,
        goto_link_id: LinkId,
        argvec: ArgVec,
        call_span_id: SpanId,
    ) -> Result<FlattenResult> {
        // push a goto
        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        let scope_id = block.scope_id;
        let link_id = block.last().unwrap();
        let ty = AstFuncType::new(argvec_type(&argvec), ReturnType::Never).into();

        self.push_placeholder_terminal(link_id, ty, call_span_id);

        let mut d = DeferredGoto::new(
            scope_id,
            None,
            vec![],
            call_span_id,
            current_block_id,
            DeferredType::Name(goto_link_id),
        );
        d.argvec = argvec;
        self.deferred_goto.add_cps(d);
        return Ok(FlattenResult::statement());
    }

    pub fn push_goto(
        &mut self,
        name: StringKey,
        args: Vec<Argument>,
        call_span_id: SpanId,
        b: &mut NB,
    ) -> Result<FlattenResult> {
        // push a goto
        // to keep things simpler, we just defer all resolution of the gotos until the end
        // Goto is terminal, so we write out placeholders
        let current_block_id = self.current_block_id();
        let block = self.blocks.get_block(current_block_id);
        let scope_id = block.scope_id;

        let _s_name = b.labels.r(name.into());

        // if this is a name, we can resolve now, no need to defer
        // this happens in a CPS function, where we try to jump to a variable.
        // we don't need to defer because we know the target
        // We will rewrite in a later step, this goto will become a select

        if let Some(name_link_id) = self.resolve_name_in_scope(scope_id, name.into()) {
            let link_id = block.last().unwrap();
            self.push_placeholder_terminal(link_id, AstType::Unit, call_span_id);

            let d = DeferredGoto::new(
                scope_id,
                name.into(),
                args,
                call_span_id,
                current_block_id,
                DeferredType::Name(name_link_id),
            );
            self.deferred_goto.add_deferred(d);
            return Ok(FlattenResult::statement());
        }

        // if we don't have a template or a label already, then we defer
        // ensure we are in function scope
        if self.blocks.in_function_scope(scope_id) {
            let link_id = block.last().unwrap();
            self.push_placeholder_terminal(link_id, AstType::Unit, call_span_id);

            let d = DeferredGoto::new(
                scope_id,
                name.into(),
                args,
                call_span_id,
                current_block_id,
                DeferredType::Goto(link_id),
            );
            self.deferred_goto.add_deferred(d);
            return Ok(FlattenResult::statement());
        } else {
            // goto without function scope
            unreachable!("goto without function scope")
        }
    }

    fn resolve_deferred_single(&mut self, d: DeferredGoto, b: &mut NB) -> Result<bool> {
        /*
         * name resolution should not be deferred as it can assume lexical scope
         * but since we can't actually lower a jump to a variable, we are going to
         * do some rewriting here, so CPS functions become static
         * we replace the variable representing the block with an integer, and use
         * a switch statement in the jump to route things appropriately.
         *
         */

        match &d.deferred_type {
            DeferredType::Name(def_target_link_id) => {
                // is it a variable in scope?
                // This happens if we try to jump to a variable
                // We have no way of lowering this, so we need to handle this later
                // This will be rewritten in a later step based on the type
                // we type check and then add a placeholder jump, that will be replaced later
                // based on the graph.
                //
                self.switch_blocks(d.block_id);
                self.remove_placeholder_terminal(d.block_id);

                // push the arguments, and unify the type,
                // but keep the placeholder, we will replace it in the rewrite step
                // we do just enough calculation here to resolve the types, and we push it back on the
                // stack
                //
                //

                // Push load if required.  This is needed if the target is stored in memory,
                // rather than a register
                let load_link_id = if self.is_load_required(*def_target_link_id) {
                    let entry = self.get_entry(*def_target_link_id).clone();
                    let link_id = self.push_code(
                        LCode::Load(*def_target_link_id),
                        entry.ty,
                        entry.name,
                        entry.span_id,
                        VarDefinitionSpace::Default,
                    );
                    self.scoped_continuations.connect(
                        ContinuationFlow::Variable(*def_target_link_id),
                        ContinuationFlow::Variable(link_id),
                        FlowEdge::LoadBlockArg,
                    );
                    link_id
                } else {
                    *def_target_link_id
                };

                // we don't know the function yet, so we can't calculate the args
                // For this reason we should consider moving the args calculation to the function
                // side, rather than the call side
                /*
                let (args, def_func_type) = Self::calculate_function_arguments(
                    &a.def,
                    &d.args,
                    &[],
                    def_span_id,
                    d.call_span_id,
                    b,
                )?;
                */

                // calculate the type, so we can unify
                let goto_values = self.push_call_arguments(d.args.clone(), d.call_span_id, b)?;
                let goto_arg_type = argvec_type(&goto_values);
                let goto_func_type =
                    AstFuncType::new(goto_arg_type.clone(), ReturnType::Never).into();

                // unify
                let entry = self.get_entry(*def_target_link_id);
                let var_ty = entry.ty.clone();
                b.unify(&var_ty, entry.span_id, &goto_func_type, d.call_span_id);

                // save the argvec, so we can properly terminate later
                let mut d = d;
                d.deferred_type = DeferredType::Name(load_link_id);
                d.argvec = goto_values;

                let block = self.blocks.get_block(self.current_block_id());
                self.push_placeholder_terminal(
                    block.last().unwrap(),
                    goto_func_type,
                    d.call_span_id,
                );

                self.deferred_goto.add_cps(d);
                return Ok(true);
            }

            DeferredType::Goto(goto_link_id) => {
                // are we jumping to an abstraction?
                if let Some(abstraction_id) = self
                    .blocks
                    .resolve_template(d.scope_id, d.name.unwrap().into())
                {
                    self.switch_blocks(d.block_id);
                    self.remove_placeholder_terminal(d.block_id);

                    // push and jump
                    // TODO: this function needs to handle unwind
                    let (variant_id, _fun_scope_id, _fun_block_id, _, _, _, _, _link_id) = self
                        .push_cps_block(
                            d.name.unwrap(),
                            d.scope_id,
                            abstraction_id,
                            d.args.clone(),
                            d.call_span_id,
                            b,
                        )?;

                    let dt = DeferredType::Variant(*goto_link_id, d.block_id, variant_id);
                    let mut d = d;
                    d.deferred_type = dt;
                    self.deferred_goto.add_cps(d);
                    return Ok(true);
                }

                // is it a label?
                if let Some(target_block_id) =
                    self.resolve_label(d.scope_id, d.name.unwrap().into())
                {
                    assert_eq!(d.args.len(), 0);
                    // not possible to pass args to a label, use a CPS function instead
                    self.switch_blocks(d.block_id);
                    self.remove_placeholder_terminal(d.block_id);

                    // TODO: we just have a label, so we need to handle unwind here.  We can't jump
                    // directly, we need to jump to the unwind function

                    // TODO: args should be unwound before jumping
                    // by replacing jumps out of scope to the unwind function
                    let jump_args = self.push_call_arguments(d.args.clone(), d.call_span_id, b)?;
                    let link_id =
                        self.push_jump(target_block_id.into(), jump_args, d.call_span_id, b);
                    self.scoped_continuations.connect(
                        ContinuationFlow::Jump(link_id),
                        ContinuationFlow::Block(target_block_id),
                        FlowEdge::JumpLabel,
                    );

                    return Ok(true);
                }

                // otherwise it's not defined, return an error
                let s = b.labels.r(d.name.unwrap().into());
                b.push_error(
                    &format!("ident `{}` not found in {}{}", s, d.scope_id, d.block_id),
                    d.call_span_id,
                );
            }
            _ => {
                unimplemented!();
            }
        }
        Ok(false)
    }

    fn resolve_cps_single(&mut self, d: DeferredGoto, b: &mut NB) -> Result<()> {
        // this is where we actually do the rewrite
        match d.deferred_type {
            DeferredType::Name(arg_link_id) => {
                // we replace the placeholder here
                self.switch_blocks(d.block_id);
                let entry = self.get_entry(arg_link_id).clone();
                let code = entry.code;
                let arg_block_id = entry.block_id;

                let sources = match &code {
                    LCode::Arg(arg_num) => {
                        println!("arg: {}:{}", arg_link_id, arg_num);
                        self.scoped_continuations
                            .find_source_blocks(ContinuationFlow::BlockArg(arg_block_id, *arg_num))
                    }

                    LCode::Declare | LCode::Load(_) => {
                        println!("decl: {}", arg_link_id);
                        self.scoped_continuations
                            .find_source_blocks(ContinuationFlow::Variable(arg_link_id))
                    }

                    LCode::Val(Literal::Block(block_id)) => {
                        let sink = self
                            .scoped_continuations
                            .find_sink_block(ContinuationFlow::Variable(arg_link_id))
                            .unwrap();
                        let sources = self.scoped_continuations.find_source_blocks(sink);
                        println!(
                            "block: {} => {}, sink: {:?}",
                            arg_link_id,
                            block_id,
                            (sink, &sources)
                        );
                        sources
                    }
                    _ => {
                        unreachable!("{:?}", code);
                    }
                };

                let _jump_link_id =
                    self.replace_placeholder_terminal(d.block_id, arg_link_id, sources.clone(), b);
            }
            DeferredType::Variant(_goto_link_id, _source_block_id, _variant_id) => {}
            _ => {
                unreachable!("{:?}", d);
            }
        }
        Ok(())
    }

    pub(super) fn resolve_open_identifiers(&mut self, b: &mut NB) -> Result<()> {
        let mut abstractions = vec![];
        let mut blocks = vec![];
        let mut errors = vec![];

        for link_id in &self.open_identifiers {
            let entry = self.get_entry(*link_id);
            let block_id = entry.block_id;
            let block = self.blocks.get_block(block_id);
            let scope_id = block.scope_id;
            let key = entry.name.unwrap();
            if let Some(label_block_id) = self.resolve_label(scope_id, key.into()) {
                blocks.push((*link_id, label_block_id));
            } else if let Some(abstraction_id) = self.blocks.resolve_template(scope_id, key.into())
            {
                abstractions.push((*link_id, abstraction_id));
            } else {
                errors.push(*link_id);
            }
        }

        for (link_id, block_id) in blocks {
            let block = self.blocks.get_block(block_id);
            let block_entry_id = block.entry();
            let block_entry = self.get_entry(block_entry_id);
            let block_ty = block_entry.ty.clone();
            let block_span_id = block_entry.span_id;

            self.switch_blocks(block_id);
            self.scoped_continuations.connect(
                ContinuationFlow::Block(block_id),
                ContinuationFlow::Variable(link_id),
                FlowEdge::BlockRef,
            );

            // now replace the abstraction code
            let entry = self.get_entry_mut(link_id);
            entry.code = LCode::Val(Literal::Block(block_id));
            b.unify(&entry.ty, entry.span_id, &block_ty, block_span_id);
        }

        for (link_id, abstraction_id) in abstractions {
            self.resolve_open_abstractions(link_id, abstraction_id, b)?;
        }

        for link_id in errors {
            let entry = self.get_entry(link_id);
            let name = entry.name.unwrap();
            let s_name = b.labels.r(name.into());
            b.push_error(&format!("Identifier not found: {}", s_name), entry.span_id);
        }
        Ok(())
    }

    pub(super) fn resolve_cps(&mut self, b: &mut NB) -> Result<()> {
        loop {
            if let Some(d) = self.deferred_goto.pop_cps() {
                self.resolve_cps_single(d, b)?;
            } else {
                break;
            }
        }
        Ok(())
    }

    pub(super) fn resolve_deferred(&mut self, b: &mut NB) -> Result<()> {
        loop {
            if let Some(d) = self.deferred_goto.pop_deferred() {
                let _ = self.resolve_deferred_single(d, b)?;
            } else {
                break;
            }
        }
        Ok(())
    }
}
