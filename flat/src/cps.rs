use anyhow::Result;
use compile_core::{
    AbstractionId, Argument, AstType, ReturnType, SpanId, StringKey, VarDefinitionSpace,
};

use std::convert::Into;

use crate::{
    argvec_type, ArgVec, BlockId, ContinuationFlow, Flatten, FlowEdge, LCode, LinkId,
    NodeBuilder as NB, ScopeId, ScopeType, Successor, VariantId,
};

impl Flatten {
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
        let (_, def_arg_type, _) = self.refresh_func_type(&a.def, b);
        let def_func_type = AstType::Func(def_arg_type.clone().into(), ReturnType::Never.into());
        let call_arg_type = AstType::Struct(call_func_type.fields());
        b.unify(&call_arg_type, call_span_id, &def_arg_type, def_span_id);
        b.unify(&def_func_type, call_span_id, &call_func_type, def_span_id);

        let (variant_id, fun_block_id, fun_scope_id, ty) =
            if let Some((variant_id, resolve_type, link_id, fun_scope_id)) =
                self.resolve_function_name(scope_id, &name, &call_arg_type, b)
            {
                let entry = self.get_entry(link_id);
                let fun_block_id = entry.block_id;
                b.unify(&call_arg_type, call_span_id, &resolve_type, a.def_span_id);
                (variant_id, fun_block_id, fun_scope_id, resolve_type)
            } else {
                let (fun_block_id, fun_scope_id) =
                    self.new_scope_and_block(ScopeType::Block, scope_id);
                // block graph
                self.blocks.block_succ(
                    self.current_block_id(),
                    fun_block_id,
                    Successor::BlockScope,
                );
                // Start lambda block
                let lambda_name = b.labels.fresh_key(&s_name);

                // make a copy of the body
                let a = self.abstractions.get(abstraction_id);
                let body = a.def.body.clone().unwrap();

                self.switch_blocks(fun_block_id);

                let r_ty1 = b.types.u.resolve(&def_func_type).unwrap();

                //println!("push start block5: {}{}", fun_scope_id, fun_block_id);
                let (entry_link_id, _) = self.push_start_block(
                    fun_scope_id,
                    r_ty1.clone(),
                    //r_ty1.clone(),
                    Some(lambda_name),
                    def_span_id,
                    VarDefinitionSpace::Default,
                );
                // add the name to scope
                // do this early for recursive functions
                // add entry to scope, for recursion
                self.scopes
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
                    let _p_link_id = self.push_code(
                        LCode::PlaceholderTerminal(block.last().unwrap()),
                        AstType::Unit,
                        None,
                        def_span_id,
                        VarDefinitionSpace::Default,
                    );
                    //println!("placeholder4: {}", p_link_id);
                }

                (variant_id, fun_block_id, fun_scope_id, r_ty2)
            };

        self.switch_blocks(current_block_id);

        Ok((variant_id, fun_scope_id, fun_block_id, ty))
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
        AstType,
        ArgVec,
        LinkId, // return goto link
    )> {
        // call in the context of the caller, which is a goto
        let current_block_id = self.current_block_id();
        let s_name = b.labels.r(name.into());
        let a = self.abstractions.get(abstraction_id);
        let def_span_id = a.def_span_id;
        let def = a.def.clone();

        //let fun_scope = self.scopes.get_scope_mut(fun_scope_id);
        // we might want to handle this later
        // return in a CPS will return from the scoped function
        //fun_scope.return_block = Some(next_block_id);
        //
        // WRITE GOTO
        let (args, _) =
            self.calculate_function_arguments(&def, &args, def_span_id, call_span_id, b)?;
        let call_values = self.push_call_arguments(args, call_span_id, b)?;
        let goto_block_id = self.current_block_id();
        let block = self.blocks.get_block(goto_block_id);
        let goto_scope_id = block.scope_id;
        //let s_name = b.labels.r(name.into());
        let call_arg_type = argvec_type(&call_values);
        let call_func_type = AstType::Func(call_arg_type.clone().into(), ReturnType::Never.into());

        /*
        let (variant_id, fun_scope_id, fun_block_id, def_arg_type) = self.push_cps_block_with_type(name, scope_id, abstraction_id, &call_func_type, call_span_id, b)?;
        b.unify(&call_arg_type, call_span_id, &def_arg_type, def_span_id);
         */

        // This expects to be called in a block that is ready to jump
        let a = self.abstractions.get(abstraction_id);
        let def_span_id = a.def_span_id;
        let (_, def_arg_type, _) = self.refresh_func_type(&a.def, b);
        let def_func_type = AstType::Func(def_arg_type.clone().into(), ReturnType::Never.into());
        let call_arg_type = AstType::Struct(call_func_type.fields());
        b.unify(&call_arg_type, call_span_id, &def_arg_type, def_span_id);
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
                let (fun_block_id, fun_scope_id) =
                    self.new_scope_and_block(ScopeType::Block, scope_id);
                // block graph
                self.blocks.block_succ(
                    self.current_block_id(),
                    fun_block_id,
                    Successor::BlockScope,
                );
                // Start lambda block
                let lambda_name = b.labels.fresh_key(&s_name);

                // make a copy of the body
                let a = self.abstractions.get(abstraction_id);
                let body = a.def.body.clone().unwrap();

                self.switch_blocks(fun_block_id);

                let r_ty1 = b.types.u.resolve(&def_func_type).unwrap();

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
                self.scopes
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
                self.variant_update(variant_id, r_ty2.clone(), entry_link_id); // caller_blocks);

                // terminate if not already terminated
                // this is for dead code
                let block = self.blocks.get_block(self.current_block_id());
                if !block.is_term() {
                    let _p_link_id = self.push_code(
                        LCode::PlaceholderTerminal(block.last().unwrap()),
                        AstType::Unit,
                        None,
                        def_span_id,
                        VarDefinitionSpace::Default,
                    );
                    //println!("placeholder5: {}", p_link_id);
                }

                (variant_id, fun_block_id, fun_scope_id, r_ty2)
            };

        //b.unify(&call_arg_type, call_span_id, &def_arg_type, def_span_id);
        //b.unify(&call_func_type, call_span_id, &def_func_type, def_span_id);

        // NOW JUMP
        // now that we have the arguments calculated, and the lambda baked, jump!
        self.switch_blocks(goto_block_id);
        self.remove_placeholder_terminal(goto_block_id);
        //let block = self.blocks.get_block(goto_block_id);
        //let entry = self.get_entry(block.last().unwrap());
        //println!(
        //"call_values: {:?}",
        //(block.scope_id, goto_block_id, &call_values, &entry)
        //);

        let _call_links = call_values
            .iter()
            .map(|(_, link_id, _, _)| *link_id)
            .collect::<Vec<_>>();

        // TODO: now that we know the target, we need to replace any call values with unwind
        // functions. We also need to do this for the goto_block_id.
        let unwind_scopes = self.scopes.unwind_scopes(fun_scope_id, goto_scope_id)?;
        println!("unwind scopes: {:?}", unwind_scopes);

        let goto_link_id = self.push_jump(fun_block_id.into(), call_values.clone(), call_span_id);

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

        self.drain_diagnostics(b);

        // control is returned to the goto

        let def_func_type = AstType::Func(def_arg_type.clone().into(), ReturnType::Never.into());
        //let def_arg_type = AstType::Struct(def_func_type.fields());
        let def_ret_type = AstType::Unit;

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
}
