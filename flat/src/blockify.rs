use anyhow::Error;
use anyhow::Result;
use indexmap::IndexMap;
use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use petgraph::visit::Bfs;
use std::collections::HashMap;
use std::collections::VecDeque;

use lower::{
    ast::AssignTarget, ast::Builtin, Argument, Ast, AstNode, AstType, BinaryOperation, Definition,
    Diagnostic, Diagnostics, Extra, Label, LinkOptions, Literal, NodeBuilder, ParameterNode,
    ParseError, Span, SpanId, StringKey, StringLabel, UnaryOperation, VarDefinitionSpace,
};

use crate::{Environment, ScopeId, ScopeType, Successor, TemplateId, ValueId};

#[derive(Debug)]
pub struct AstBlock {
    name: ValueId,
}

#[derive(Debug, Copy, Clone)]
pub struct BlockLayerId(u32);

#[derive(Debug)]
pub struct BlockLayer {
    labels: HashMap<StringKey, ValueId>,
}
impl BlockLayer {
    pub fn new() -> Self {
        Self {
            labels: HashMap::new(),
        }
    }
}

#[derive(Debug)]
pub struct LoopLayer {
    next: ValueId,
    restart: ValueId,
}

#[derive(Debug)]
pub enum LCode {
    Label(u8, u8), // BlockId, number of positional arguments, number of named arguments
    Noop,
    Declare,
    DeclareFunction(Option<ValueId>), // optional entry block
    Value(ValueId),
    Arg(u8), // get the value of a positional arg
    Const(Literal),
    Op1(UnaryOperation, ValueId),
    Op2(BinaryOperation, ValueId, ValueId),
    Load(ValueId),
    Store(ValueId, ValueId), // memref, value to store
    Return(u8),              // return values
    Goto(StringKey),
    Jump(ValueId, u8),
    Branch(ValueId, ValueId, ValueId),
    Ternary(ValueId, ValueId, ValueId), // condition, then_entry, else_entry
    Builtin(Builtin, u8, u8),
    Call(ValueId, u8, u8),
}

impl LCode {
    pub fn is_start(&self) -> bool {
        match self {
            Self::Label(_, _) => true,
            _ => false,
        }
    }

    pub fn is_term(&self) -> bool {
        match self {
            Self::Jump(_, _) => true,
            Self::Goto(_) => true,
            Self::Branch(_, _, _) => true,
            Self::Return(_) => true,
            _ => false,
        }
    }
}

pub fn error(msg: &str, span: Span) -> Diagnostic<usize> {
    let r = span.begin.pos as usize..span.end.pos as usize;
    let labels = vec![Label::primary(span.file_id, r).with_message(msg)];
    let error = Diagnostic::error()
        .with_labels(labels)
        .with_message("error");
    error
}

#[derive(Debug)]
pub enum NextSeqState {
    Empty,                // no nodes follow
    NextLabel(StringKey), // next node is a label, we can reuse it possibly
    //NextReturn,           // next node is a return statement
    Other, // all other options
}

impl NextSeqState {
    pub fn get<E: Extra>(
        _env: &Environment<E>,
        node: &AstNode<E>,
        next_node: Option<&AstNode<E>>,
    ) -> (bool, Self) {
        let is_term = match node.node {
            Ast::Branch(_, _, _) => true,
            Ast::Conditional(_, _, _) => true,
            Ast::Test(_, _) => true,
            Ast::While(_, _) => true,
            Ast::Return(_) => true,
            Ast::Loop(_, _) => true,
            Ast::Module(_, _) => true,
            Ast::Break(_, _) => true,
            Ast::Continue(_, _) => true,
            Ast::Goto(_) => true,
            _ => false,
        };

        if let Some(next_node) = next_node {
            match next_node.node {
                //Ast::Return(_) => Self::NextReturn,
                Ast::Label(key) => (is_term, Self::NextLabel(key)),
                _ => (is_term, Self::Other),
            }
        } else {
            (is_term, Self::Empty)
        }
    }
}

#[derive(Debug, Clone)]
pub struct AddResult {
    value_id: Option<ValueId>,
    is_term: bool,
    block_id: ValueId,
}
impl AddResult {
    pub fn new(value_id: Option<ValueId>, is_term: bool, block_id: ValueId) -> Self {
        Self {
            value_id,
            is_term,
            block_id,
        }
    }
}

#[derive(Debug)]
pub struct Blockify<E> {
    // table entries
    code: Vec<LCode>,
    types: Vec<AstType>,
    mem: Vec<VarDefinitionSpace>,
    scopes: Vec<ScopeId>,
    next_pos: Vec<ValueId>,
    prev_pos: Vec<ValueId>,
    entries: Vec<ValueId>,
    span: Vec<SpanId>,
    loop_stack: Vec<LoopLayer>,
    templates: Vec<Definition<E>>,

    // other
    pub(crate) env: Environment<E>,
    // sparse names
    names: IndexMap<ValueId, StringLabel>,
    link: LinkOptions,
}

impl<E: Extra> Blockify<E> {
    pub fn new() -> Self {
        Self {
            code: vec![],
            types: vec![],
            mem: vec![],
            scopes: vec![],
            next_pos: vec![],
            prev_pos: vec![],
            loop_stack: vec![],
            entries: vec![],
            templates: vec![],
            span: vec![],

            names: IndexMap::new(),
            env: Environment::new(),
            link: LinkOptions::new(),
        }
    }

    pub fn code_count(&self) -> usize {
        self.code.len()
    }

    pub fn shared_libraries(&self) -> Vec<String> {
        self.link.shared_libraries()
    }

    pub fn block_name(&mut self, scope_id: ScopeId, name: StringLabel, v: ValueId) {
        self.env.get_scope_mut(scope_id).labels.insert(name, v);
    }

    pub fn push_template(&mut self, def: Definition<E>) -> TemplateId {
        let offset = self.templates.len();
        self.templates.push(def);
        TemplateId(offset as u32)
    }

    pub fn get_template(&mut self, template_id: TemplateId) -> &Definition<E> {
        self.templates.get(template_id.0 as usize).unwrap()
    }

    pub fn get_code(&self, value_id: ValueId) -> &LCode {
        self.code.get(value_id.0 as usize).unwrap()
    }

    pub fn get_span_id(&self, value_id: ValueId) -> SpanId {
        self.span.get(value_id.0 as usize).unwrap().clone()
    }

    pub fn get_mem(&self, value_id: ValueId) -> &VarDefinitionSpace {
        self.mem.get(value_id.0 as usize).unwrap()
    }

    pub fn get_block_id(&self, value_id: ValueId) -> ValueId {
        *self.entries.get(value_id.0 as usize).unwrap()
    }

    pub fn get_scope_id(&self, value_id: ValueId) -> ScopeId {
        *self.scopes.get(value_id.0 as usize).unwrap()
    }

    pub fn get_name(&self, v: ValueId) -> Option<StringLabel> {
        self.names.get(&v).cloned()
    }

    pub fn is_in_static_scope(&self, v: ValueId) -> bool {
        let scope_id = self.get_scope_id(v);
        let scope = self.env.get_scope(scope_id);
        if let ScopeType::Static = scope.scope_type {
            true
        } else {
            false
        }
    }

    pub fn get_next(&self, value_id: ValueId) -> Option<ValueId> {
        let next = self.next_pos[value_id.index()];
        if next != value_id {
            Some(next)
        } else {
            None
        }
    }

    pub fn get_prev(&self, value_id: ValueId) -> Option<ValueId> {
        let prev = self.prev_pos[value_id.index()];
        if prev != value_id {
            Some(prev)
        } else {
            None
        }
    }

    pub fn push_code_with_name(
        &mut self,
        code: LCode,
        span_id: SpanId,
        scope_id: ScopeId,
        block_id: ValueId,
        ty: AstType,
        mem: VarDefinitionSpace,
        name: StringKey,
    ) -> ValueId {
        let value_id = self.push_code(code, span_id, scope_id, block_id, ty.clone(), mem);
        self.env.scope_define(scope_id, name, value_id, ty, mem);
        self.names.insert(value_id, name.into());
        value_id
    }

    pub fn push_code_new_block(
        &mut self,
        code: LCode,
        span_id: SpanId,
        scope_id: ScopeId,
        ty: AstType,
    ) -> ValueId {
        let block_id = self._push_code(
            code,
            span_id,
            scope_id,
            ValueId(0),
            ty,
            VarDefinitionSpace::Reg,
        );
        self.env.new_block(block_id, scope_id);
        self.entries[block_id.0 as usize] = block_id;
        self._update_code(block_id, block_id);
        block_id
    }

    pub fn push_code(
        &mut self,
        code: LCode,
        span_id: SpanId,
        scope_id: ScopeId,
        block_id: ValueId,
        ty: AstType,
        mem: VarDefinitionSpace,
    ) -> ValueId {
        // update successor blocks
        match &code {
            LCode::Jump(target, _) => {
                // XXX: This is causing us to terminate the loop we are currently generating
                // If it knows about the loop, then it tries to terminate it
                self.env.add_succ_block(block_id, *target);
            }

            LCode::Branch(_, v_then, v_else) => {
                self.env.add_succ_block(block_id, *v_then);
                self.env.add_succ_block(block_id, *v_else);
            }

            LCode::Ternary(_, v_then, v_else) => {
                self.env.add_succ_op(block_id, *v_then);
                self.env.add_succ_op(block_id, *v_else);
            }
            _ => (),
        }

        let v = self._push_code(code, span_id, scope_id, block_id, ty, mem);
        self._update_code(v, block_id);

        v
    }

    pub fn _update_code(&mut self, value_id: ValueId, block_id: ValueId) {
        let offset = value_id.0 as usize;
        let block = self.env.get_block(block_id);
        let is_term = self.get_code(value_id).is_term();

        if let Some(last_value) = block.last_value {
            self.prev_pos[offset] = last_value;
            self.next_pos[last_value.0 as usize] = value_id;
            // check to ensure that nothing follows the terminator
            //assert!(!block.has_term());
        }

        let block = self.env.get_block_mut(block_id);

        if is_term {
            block.set_term(value_id);
        }

        block.count += 1;
        block.last_value = Some(value_id);
    }

    pub fn _push_code(
        &mut self,
        code: LCode,
        span_id: SpanId,
        scope_id: ScopeId,
        block_id: ValueId,
        ty: AstType,
        mem: VarDefinitionSpace,
    ) -> ValueId {
        let offset = self.code.len();
        let v = ValueId(offset as u32);
        self.prev_pos.push(v);
        self.next_pos.push(v);
        self.scopes.push(scope_id);
        self.entries.push(block_id);
        self.code.push(code);
        self.types.push(ty);
        self.mem.push(mem);
        self.span.push(span_id);
        v
    }

    pub fn push_label(
        &mut self,
        name: StringLabel,
        span_id: SpanId,
        scope_id: ScopeId,
        args: &[AstType],
        kwargs: &[ParameterNode],
    ) -> ValueId {
        let block_id = self.push_code_new_block(
            LCode::Label(args.len() as u8, kwargs.len() as u8),
            span_id,
            scope_id,
            AstType::Unit,
        );
        self.names.insert(block_id, name);
        self.block_name(scope_id, name, block_id);
        let block = self.env.get_block_mut(block_id);
        block.last_value = Some(block_id);
        for (i, p) in kwargs.iter().enumerate() {
            let v = self.push_code(
                LCode::Arg(i as u8),
                span_id,
                scope_id,
                block_id,
                p.ty.clone(),
                VarDefinitionSpace::Arg,
            );
            self.names.insert(v, p.name.into());
            self.env
                .define(p.name, v, p.ty.clone(), VarDefinitionSpace::Arg);
        }
        block_id
    }

    pub fn resolve_block_label(&self, k: ValueId, b: &NodeBuilder<E>) -> String {
        if let Some(key) = self.names.get(&k) {
            b.resolve_label(*key).to_string()
        } else {
            format!("b{}", k.0)
        }
    }

    pub fn get_type(&self, v: ValueId) -> AstType {
        self.types.get(v.0 as usize).unwrap().clone()
    }

    pub fn build_module(
        &mut self,
        node: AstNode<E>,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<ValueId> {
        match node.node {
            Ast::Module(name, body) => {
                let static_scope = self.env.new_scope(ScopeType::Static);
                let block_id = self.push_label(name.into(), node.span_id, static_scope, &[], &[]);
                self.env.enter_scope(static_scope);
                self.add(block_id, None, *body, b, d)?;
                self.env.exit_scope();
                Ok(block_id)
            }
            _ => unreachable!(),
        }
    }

    pub fn add_sequence(
        &mut self,
        block_id: ValueId,
        maybe_next: Option<ValueId>,
        node: AstNode<E>,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<AddResult> {
        let scope_id = self.env.current_scope().unwrap();
        // flatten
        let exprs = node.to_vec();

        // generate blocks for all predefined labels
        // this needs to be done first as a forward declaration
        for expr in exprs.iter() {
            if let Ast::Label(name) = &expr.node {
                let _ = self.push_label(name.into(), expr.span_id, scope_id, &[], &[]);
            }
        }

        let mut value_id = None;
        let mut current_block_id = Some(block_id);
        let mut iter = exprs.into_iter().peekable();
        let mut current_is_term = false;
        loop {
            if let Some(expr) = iter.next() {
                let expr_span_id = expr.span_id;
                let (is_term, next_state) = NextSeqState::get(&self.env, &expr, iter.peek());
                match (is_term, next_state) {
                    (_, NextSeqState::NextLabel(key)) => {
                        // next label handles implicit jumps
                        if let Some(target_value_id) = self.env.resolve_block(key.into()) {
                            // ensure target block exists
                            //let scope = self.env.get_scope_mut(scope_id);
                            //scope.next_block = Some(target_value_id);
                            //current_block_id = Some(target_value_id);
                            let r = self.add(
                                current_block_id.unwrap(),
                                Some(target_value_id),
                                expr,
                                b,
                                d,
                            )?;
                            let v = r.value_id.unwrap();
                            current_is_term = r.is_term;
                            assert_eq!(current_is_term, is_term);
                            //current_block_id = Some(*self.entries.get(v.0 as usize).unwrap());
                            current_block_id = Some(r.block_id);
                            //assert_eq!(current_block_id.unwrap(), r.block_id);
                            value_id = Some(v);
                            println!("r6: {:?}", r);
                            //
                        } else {
                            unreachable!()
                        }
                    }

                    /*
                        (false, NextSeqState::NextLabel(_key)) => {
                            // TODO: Add implicit jump to the next label
                            // alternatively, we can perform the jump when we add the label
                            // we just have to check if the last item was terminal
                            let r = self.add(current_block_id.unwrap(), None, expr, b, d)?;
                            let v = r.value_id.unwrap();
                            current_is_term = r.is_term;
                            assert_eq!(current_is_term, is_term);
                            //current_block_id = Some(*self.entries.get(v.0 as usize).unwrap());
                            current_block_id = Some(r.block_id);
                            //assert_eq!(current_block_id.unwrap(), r.block_id);
                            value_id = Some(v);
                            println!("r5: {:?}", r);
                            //unreachable!();
                            /*
                            if let Some(target_value_id) = self.env.resolve_block(key.into()) {
                                let code = LCode::Jump(target_value_id, 0);
                                self.push_code(
                                    code,
                                    scope_id,
                                    current_block_id.unwrap(),
                                    AstType::Unit,
                                    VarDefinitionSpace::Reg,
                                );
                                current_block_id = Some(target_value_id);
                            } else {
                                unreachable!()
                            }
                            let v = self.add(current_block_id.unwrap(), expr, b, d)?.unwrap();
                            current_block_id = Some(*self.entries.get(v.0 as usize).unwrap());
                            value_id = Some(v);
                            */
                        }
                    */
                    (false, NextSeqState::Other) => {
                        let r = self.add(current_block_id.unwrap(), maybe_next, expr, b, d)?;
                        // skip noops
                        if let Some(v) = r.value_id {
                            current_is_term = r.is_term;
                            //assert_eq!(current_is_term, is_term);
                            current_block_id = Some(r.block_id);
                            //assert_eq!(current_block_id.unwrap(), r.block_id);
                            value_id = Some(v);
                        }
                        println!("r3: {:?}", r);
                    }

                    (true, NextSeqState::Empty) => {
                        // terminal at the end of the sequence, nothing special here
                        // but we do need to pass the next block in, so that it knows
                        // what to do for sub expressions
                        let r = self.add(current_block_id.unwrap(), maybe_next, expr, b, d)?;
                        let v = r.value_id.unwrap();
                        current_is_term = r.is_term;
                        assert!(r.is_term);
                        assert_eq!(current_is_term, is_term);
                        current_block_id = Some(r.block_id);
                        value_id = Some(v);
                        println!("r4: {:?}", r);
                    }

                    (false, NextSeqState::Empty) => {
                        // end of sequence, with non-terminal node
                        let r = if let Some(v_next) = maybe_next {
                            //let r = if let Some(v_next) = self.env.get_next_block() {
                            assert_eq!(v_next, maybe_next.unwrap());
                            // terminates with a jump to next
                            self.add_with_next(current_block_id.unwrap(), expr, v_next, b, d)?
                        } else {
                            // must terminate, unless it's at the static level
                            self.add(current_block_id.unwrap(), None, expr, b, d)?
                        };

                        let v = r.value_id.unwrap();
                        current_is_term = r.is_term;
                        current_block_id = Some(r.block_id);
                        value_id = Some(v);
                        println!("r2: {:?}", r);

                        // check that this terminates correctly
                        // exception for module level
                        assert!(r.is_term || self.env.static_block_id() == r.block_id);
                    }

                    (true, NextSeqState::Other) => {
                        // a terminal, followed by other statements
                        // we create a next block for the statements to follow
                        let name = b.s("next");
                        let v_next = self.push_label(name.into(), expr_span_id, scope_id, &[], &[]);
                        let r =
                            self.add_with_next(current_block_id.unwrap(), expr, v_next, b, d)?;
                        let v = r.value_id.unwrap();
                        current_is_term = r.is_term;
                        println!("r1: {:?}", r);
                        assert!(r.is_term);
                        assert_eq!(current_is_term, is_term);
                        // next block is the next block
                        current_block_id = Some(r.block_id);
                        //assert_eq!(current_block_id.unwrap(), r.block_id);
                        value_id = Some(v);
                    }
                }
            } else {
                break;
            }
        }

        //println!(
        //"x: {:?}",
        //(value_id, current_is_term, block_id, current_block_id)
        //);
        // sequence is terminal, unless it's the module sequence
        assert!(current_is_term || self.env.static_block_id() == current_block_id.unwrap());
        Ok(AddResult::new(
            value_id,
            current_is_term,
            current_block_id.unwrap(),
        ))
    }

    pub fn add_lambda_and_call(
        &mut self,
        block_id: ValueId,
        template_id: TemplateId,
        args: Vec<Argument<E>>,
        span_id: SpanId,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<AddResult> {
        // TODO: Emit blocks for the definition, and jump to the entry block
        // return value for body is the next block, which we need to create here
        let scope_id = self.env.current_scope().unwrap();

        // get clone and push back
        let mut def = self.get_template(template_id).clone();

        //let params = def.params.iter().map(|p| p.ty.clone()).collect::<Vec<_>>();

        let args_size = args.len() as u8;

        let body = def.body.take().unwrap();
        let body_scope_id = self.env.new_scope(ScopeType::Block);

        // entry first
        let label_name = b.labels.fresh_var_id();
        let entry_id = self.push_label(label_name, span_id, body_scope_id, &[], &def.params);

        let mut jump_args = vec![];
        for a in args.into_iter() {
            let Argument::Positional(expr) = a;
            jump_args.push(*expr);
        }

        assert_eq!(args_size as usize, jump_args.len());
        // jump to entry
        let _r = self.add_jump(block_id, entry_id, jump_args, span_id, b, d)?;
        self.env.add_succ_block(block_id, entry_id);
        // return block is the next block

        // handle body
        let return_type = *def.return_type;
        let return_type_args = match &return_type {
            AstType::Unit => vec![],
            _ => vec![return_type.clone()],
        };

        let name = b.s("lambda_result");
        let v_next = self.push_label(name.into(), span_id, scope_id, &return_type_args, &[]);

        // push Arg to next block
        let v_expr = self.push_code(
            LCode::Arg(0),
            span_id,
            scope_id,
            v_next,
            return_type,
            VarDefinitionSpace::Reg,
        );

        let scope = self.env.get_scope_mut(body_scope_id);
        scope.return_block = Some(v_next);
        scope.entry_block = Some(entry_id);
        self.env.enter_scope(body_scope_id);
        let r1 = self.add_with_next(entry_id, *body, v_next, b, d)?;
        self.env.exit_scope();

        // we return the value of the arg in the next block
        let r2 = AddResult::new(Some(v_expr), false, v_next);
        println!("lambda: {:?}", (&r1, &r2));
        Ok(r2)
    }

    pub fn add_function(
        &mut self,
        block_id: ValueId,
        def: Definition<E>,
        span_id: SpanId,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<AddResult> {
        let scope_id = self.env.current_scope().unwrap();

        let params = def.params.iter().map(|p| p.ty.clone()).collect();
        //let spans = def.params.iter().map(|p| p.span_id).collect::<Vec<_>>();
        let ty = AstType::Func(params, def.return_type.clone());

        if let Some(body) = def.body {
            let body_scope_id = self.env.new_scope(ScopeType::Function);
            //let body_span_id = body.span_id;

            // entry first
            let entry_id =
                self.push_label(def.name.into(), span_id, body_scope_id, &[], &def.params);

            // return block
            let name = b.s("ret");
            let return_type = *def.return_type;
            let args = match &return_type {
                AstType::Unit => vec![],
                _ => vec![return_type.clone()],
            };

            // return block follows entry
            let return_block = self.push_label(name.into(), span_id, body_scope_id, &args, &[]);
            let v_args = args
                .iter()
                .enumerate()
                .map(|(i, _arg)| {
                    let v_arg = self.push_code(
                        LCode::Arg(i as u8),
                        span_id,
                        body_scope_id,
                        return_block,
                        return_type.clone(),
                        VarDefinitionSpace::Arg,
                    );
                    v_arg
                })
                .collect::<Vec<_>>();

            for v_arg in v_args.iter() {
                self.push_code(
                    LCode::Value(*v_arg),
                    span_id,
                    body_scope_id,
                    return_block,
                    return_type.clone(),
                    VarDefinitionSpace::Arg,
                );
            }

            self.push_code(
                LCode::Return(v_args.len() as u8),
                span_id,
                body_scope_id,
                return_block,
                AstType::Unit,
                VarDefinitionSpace::Reg,
            );

            // handle body

            let scope = self.env.get_scope_mut(body_scope_id);
            scope.return_block = Some(return_block);
            scope.entry_block = Some(entry_id);

            // declare function before adding the body, for recursion
            let v_decl = self.push_code_with_name(
                LCode::DeclareFunction(Some(entry_id)),
                span_id,
                scope_id,
                block_id,
                ty.clone(),
                VarDefinitionSpace::Static,
                def.name,
            );

            self.env.enter_scope(body_scope_id);
            // next block in body scope
            self.add_with_next(entry_id, *body, return_block, b, d)?;
            self.env.exit_scope();
            self.env.add_succ_static(block_id, entry_id);
            Ok(AddResult::new(Some(v_decl), false, block_id))
        } else {
            Ok(AddResult::new(
                Some(self.push_code_with_name(
                    LCode::DeclareFunction(None),
                    span_id,
                    scope_id,
                    block_id,
                    ty.clone(),
                    VarDefinitionSpace::Static,
                    def.name,
                )),
                false,
                block_id,
            ))
        }
    }

    pub fn error(msg: &str, span_id: SpanId, d: &mut Diagnostics) -> Result<AddResult> {
        let span = d.lookup(span_id);
        d.push_diagnostic(error(msg, span));
        return Err(Error::new(ParseError::Invalid));
    }

    pub fn add_loop(
        &mut self,
        block_id: ValueId,
        v_next: ValueId,
        name: StringKey,
        body: AstNode<E>,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<AddResult> {
        let span_id = body.span_id;
        let loop_scope_id = self.env.new_scope(ScopeType::Loop);
        let v_loop = self.push_label(name.into(), span_id, loop_scope_id, &[], &[]);
        self.env.push_loop_blocks(Some(name), v_next, v_loop);
        self.env.enter_scope(loop_scope_id);
        let _ = self.add_with_next(v_loop, body, v_next, b, d)?;
        self.env.exit_scope();

        // enter loop
        let r = self.add_jump(block_id, v_loop, vec![], span_id, b, d)?;
        Ok(AddResult::new(Some(r.value_id.unwrap()), true, v_next))
    }

    pub fn add_jump(
        &mut self,
        block_id: ValueId,
        target_id: ValueId,
        jump_args: Vec<AstNode<E>>,
        span_id: SpanId,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<AddResult> {
        let target = self.get_code(target_id);
        // make sure we match the arity of the next block
        let args = if let LCode::Label(args, _) = target {
            args
        } else {
            unreachable!();
        };
        self._add_jump(
            block_id,
            target_id,
            *args as usize,
            jump_args,
            span_id,
            b,
            d,
        )
    }

    pub fn _add_jump(
        &mut self,
        block_id: ValueId,
        target_id: ValueId,
        num_args: usize,
        jump_args: Vec<AstNode<E>>,
        span_id: SpanId,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<AddResult> {
        let scope_id = self.env.current_scope().unwrap();
        let count = jump_args.len();

        let mut values = vec![];
        for arg in jump_args.into_iter() {
            let r = self.add(block_id, None, arg, b, d)?;
            let expr_value_id = r.value_id.unwrap();
            values.push(expr_value_id);
        }

        for value_id in values {
            self.push_code(
                LCode::Value(value_id),
                span_id,
                scope_id,
                block_id,
                self.get_type(value_id),
                VarDefinitionSpace::Reg,
            );
        }

        if num_args as usize == count {
            let v = self.push_code(
                LCode::Jump(target_id, num_args as u8),
                span_id,
                scope_id,
                block_id,
                AstType::Unit,
                VarDefinitionSpace::Reg,
            );
            Ok(AddResult::new(Some(v), true, block_id))
        } else {
            Self::error(
                &format!("End of block expects {} values", num_args),
                span_id,
                d,
            )
        }
    }

    pub fn add_with_next(
        &mut self,
        block_id: ValueId,
        node: AstNode<E>,
        v_next: ValueId,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<AddResult> {
        let span_id = node.span_id;
        let r = self.add(block_id, Some(v_next), node, b, d)?;
        let v_block = r.block_id;
        let v = r.value_id.unwrap();
        let last_block_id = self.get_block_id(v);
        //assert_eq!(last_block_id, r.block_id);
        let block = self.env.get_block(last_block_id);

        if !block.has_term() {
            // if the block doesn't explicitely terminate, then we jump to the next block
            self.add_jump(v_block, v_next, vec![], span_id, b, d)
        } else {
            Ok(r)
        }
    }

    pub fn add_function_call(
        &mut self,
        scope_id: ScopeId,
        block_id: ValueId,
        v_func: ValueId,
        args: Vec<Argument<E>>,
        span_id: SpanId,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<AddResult> {
        let ty = self.get_type(v_func);

        if let AstType::Func(func_arg_types, ret) = &ty {
            if func_arg_types.len() != args.len() {
                return Self::error(
                    &format!(
                        "Call arity mismatch: {}<=>{}",
                        func_arg_types.len(),
                        args.len()
                    ),
                    span_id,
                    d,
                );
            }

            let args_size = args.len() as u8;
            let mut values = vec![];
            for (a, ty) in args.into_iter().zip(func_arg_types.iter()) {
                match a {
                    Argument::Positional(expr) => {
                        let r = self.add(block_id, None, *expr, b, d)?;
                        let v = r.value_id.unwrap();
                        values.push((LCode::Value(v), ty.clone()));
                    }
                }
            }
            for (code, ty) in values {
                self.push_code(
                    code,
                    span_id,
                    scope_id,
                    block_id,
                    ty,
                    VarDefinitionSpace::Reg,
                );
            }
            let v = self.push_code(
                LCode::Call(v_func, args_size, 0),
                span_id,
                scope_id,
                block_id,
                *ret.clone(),
                VarDefinitionSpace::Reg,
            );
            Ok(AddResult::new(Some(v), false, block_id))
        } else {
            let name = b.resolve_label(self.get_name(v_func).unwrap());
            return Self::error(
                &format!("Type not function: {}, {:?}", name, ty),
                span_id,
                d,
            );
        }
    }

    pub fn add_noop(&mut self, block_id: ValueId, span_id: SpanId) -> Result<Option<ValueId>> {
        let scope_id = self.env.current_scope().unwrap();
        Ok(Some(self.push_code(
            LCode::Noop,
            span_id,
            scope_id,
            block_id,
            AstType::Unit,
            VarDefinitionSpace::Reg,
        )))
    }

    pub fn add(
        &mut self,
        block_id: ValueId,
        maybe_next: Option<ValueId>,
        node: AstNode<E>,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<AddResult> {
        let scope_id = self.env.current_scope().unwrap();
        match node.node {
            Ast::Module(_, _) => {
                // nested modules are not yet implemented
                unimplemented!()
            }

            Ast::Sequence(ref _exprs) => self.add_sequence(block_id, maybe_next, node, b, d),

            Ast::Definition(def) => {
                // definition is non-terminal
                if block_id == self.env.static_block_id() {
                    self.add_function(block_id, def, node.span_id, b, d)
                } else {
                    let name = def.name.into();
                    let template_id = self.push_template(def);
                    let scope = self.env.get_scope_mut(scope_id);
                    scope.lambdas.insert(name, template_id);
                    Ok(AddResult::new(None, false, block_id))
                }
            }

            Ast::Call(expr, args, _ret_ty) => match &expr.node {
                // call is an expression, it's non-terminal
                // lambdas should also be non-terminal
                Ast::Identifier(ident) => {
                    let name = b.resolve_label(ident.into());
                    if let Some(data) = self.env.resolve(*ident) {
                        return self.add_function_call(
                            scope_id,
                            block_id,
                            data.value_id,
                            args,
                            node.span_id,
                            b,
                            d,
                        );
                    }

                    if let Some(scope_id) = self.env.resolve_lambda_scope(ident.into()) {
                        let scope = self.env.get_scope(scope_id);
                        let label: StringLabel = (*ident).into();
                        let template_id = scope.lambdas.get(&label).unwrap();
                        return self.add_lambda_and_call(
                            block_id,
                            *template_id,
                            args,
                            node.span_id,
                            b,
                            d,
                        );
                    }

                    return Self::error(&format!("Call name not found: {}", name), node.span_id, d);
                }
                _ => {
                    unimplemented!("{:?}", expr.node);
                }
            },

            Ast::Label(name) => {
                // all blocks should have been forward declared in the sequence
                let value_id = self.env.resolve_block(name.into()).unwrap();

                let block = self.env.get_block(block_id);
                if let Some(last_value) = block.last_value {
                    // check to ensure that the previous block was terminated
                    let code = self.code.get(last_value.0 as usize).unwrap();
                    if !code.is_term() {
                        // TODO: add implicit jump to this block
                        // Ast labels have no arguments, so this should be trivial
                        unreachable!();
                    }
                }

                Ok(AddResult::new(Some(value_id), false, value_id))
            }

            Ast::Identifier(key) => {
                // identifier is expression, non-terminal
                if let Some(data) = self.env.resolve(key) {
                    let ty = data.ty.clone();
                    let code = if let VarDefinitionSpace::Arg = data.mem {
                        LCode::Value(data.value_id)
                    } else {
                        LCode::Load(data.value_id)
                    };
                    let v = self.push_code(
                        code,
                        node.span_id,
                        scope_id,
                        block_id,
                        ty,
                        data.mem.clone(),
                    );
                    Ok(AddResult::new(Some(v), false, block_id))
                } else {
                    let span = d.lookup(node.span_id);
                    d.push_diagnostic(error("Name not found", span));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            Ast::Assign(target, expr) => {
                // assign is expression, non-terminal
                let name = match target {
                    AssignTarget::Identifier(name) | AssignTarget::Alloca(name) => name,
                };

                let r = self.add(block_id, None, *expr, b, d)?;

                let v_expr = r.value_id.unwrap();
                let v_block = r.block_id;

                let expr_ty = self.get_type(v_expr);

                let v_decl = if let Some(data) = self.env.resolve(name) {
                    assert_eq!(data.ty, expr_ty);
                    data.value_id
                } else {
                    self.push_code_with_name(
                        LCode::Declare,
                        node.span_id,
                        scope_id,
                        v_block,
                        expr_ty.clone(),
                        VarDefinitionSpace::Stack,
                        name,
                    )
                };

                let v = self.push_code(
                    LCode::Store(v_decl, v_expr),
                    node.span_id,
                    scope_id,
                    v_block,
                    AstType::Unit,
                    VarDefinitionSpace::Stack,
                );
                Ok(AddResult::new(Some(v), false, v_block))
            }

            Ast::Builtin(bi, mut args) => match bi {
                Builtin::Import => {
                    let arg = args.pop().unwrap();
                    if let Some(s) = arg.try_string() {
                        self.link.add_library(&s);
                    } else {
                        let span = d.lookup(node.span_id);
                        d.push_diagnostic(error("Expected string", span));
                    }
                    Ok(AddResult::new(None, false, block_id))
                }
                _ => {
                    let _ty = bi.get_return_type();
                    let args_size = args.len();
                    assert_eq!(args_size, bi.arity());
                    let mut values = vec![];
                    for a in args.into_iter() {
                        let Argument::Positional(expr) = a;
                        let r = self.add(block_id, None, *expr, b, d)?;
                        let v = r.value_id.unwrap();
                        let ty = self.get_type(v);
                        values.push((v, ty));
                    }

                    for (v, ty) in values {
                        self.push_code(
                            LCode::Value(v),
                            node.span_id,
                            scope_id,
                            block_id,
                            ty,
                            VarDefinitionSpace::Reg,
                        );
                    }

                    let ty = bi.get_return_type();
                    let value_id = self.push_code(
                        LCode::Builtin(bi, args_size as u8, 0),
                        node.span_id,
                        scope_id,
                        block_id,
                        ty,
                        VarDefinitionSpace::Reg,
                    );
                    Ok(AddResult::new(Some(value_id), false, block_id))
                }
            },

            Ast::Literal(lit) => {
                // literal is expression, non-terminal
                let ty: AstType = lit.clone().into();
                let v = self.push_code(
                    LCode::Const(lit),
                    node.span_id,
                    scope_id,
                    block_id,
                    ty,
                    VarDefinitionSpace::Reg,
                );
                Ok(AddResult::new(Some(v), false, block_id))
            }

            Ast::UnaryOp(op, x) => {
                // op1 is expression, non-terminal
                let r = self.add(block_id, None, *x, b, d)?;
                let v_block = r.block_id;
                let vx = r.value_id.unwrap();
                let code = LCode::Op1(op, vx);
                let v = self.push_code(
                    code,
                    node.span_id,
                    scope_id,
                    v_block,
                    self.get_type(vx),
                    VarDefinitionSpace::Reg,
                );
                Ok(AddResult::new(Some(v), false, v_block))
            }

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
                // conditional is terminal

                //let v_next = self.env.get_next_block().unwrap();
                let v_next = maybe_next.unwrap();
                assert_eq!(v_next, maybe_next.unwrap());

                let name = b.s("then");
                let then_scope_id = self.env.new_scope(ScopeType::Block);
                let v_then =
                    self.push_label(name.into(), then_expr.span_id, then_scope_id, &[], &[]);
                self.env.enter_scope(then_scope_id);
                let r = self.add_with_next(v_then, *then_expr, v_next, b, d)?;
                let _ = r.value_id.unwrap();
                self.env.exit_scope();

                let v_else = if let Some(else_expr) = maybe_else_expr {
                    let name = b.s("else");
                    let else_scope_id = self.env.new_scope(ScopeType::Block);
                    let v_else =
                        self.push_label(name.into(), else_expr.span_id, else_scope_id, &[], &[]);
                    self.env.enter_scope(else_scope_id);
                    let r = self.add_with_next(v_else, *else_expr, v_next, b, d)?;
                    let _ = r.value_id.unwrap();
                    self.env.exit_scope();
                    v_else
                } else {
                    v_next
                };

                let span_id = condition.span_id;
                let r = self.add(block_id, None, *condition, b, d)?;
                let v = r.value_id.unwrap();
                let code = LCode::Branch(v, v_then, v_else);
                let v = self.push_code(
                    code,
                    span_id,
                    scope_id,
                    r.block_id,
                    AstType::Unit,
                    VarDefinitionSpace::Reg,
                );

                Ok(AddResult::new(Some(v), true, v_next))
            }

            Ast::Ternary(c, x, y) => {
                // expression, non-terminal
                let condition_span_id = c.span_id;
                let r = self.add(block_id, None, *c, b, d)?;
                let v_c = r.value_id.unwrap();

                let then_scope_id = self.env.new_scope(ScopeType::Block);
                let name = b.s("then");
                self.env.enter_scope(then_scope_id);
                let v_then = self.push_label(name.into(), x.span_id, then_scope_id, &[], &[]);
                let r = self.add(v_then, None, *x, b, d)?;
                let v_then_result = r.value_id.unwrap();
                self.env.exit_scope();
                let then_ty = self.get_type(v_then_result);

                let else_scope_id = self.env.new_scope(ScopeType::Block);
                let name = b.s("else");
                self.env.enter_scope(else_scope_id);
                let v_else = self.push_label(name.into(), y.span_id, else_scope_id, &[], &[]);
                let r = self.add(v_else, None, *y, b, d)?;
                let v_else_result = r.value_id.unwrap();
                self.env.exit_scope();
                let else_ty = self.get_type(v_else_result);
                assert_eq!(then_ty, else_ty);

                // TODO: we need to ensure that the cfg terminates with a yield

                let code = LCode::Ternary(v_c, v_then, v_else);

                let v = self.push_code(
                    code,
                    condition_span_id,
                    scope_id,
                    block_id,
                    then_ty,
                    VarDefinitionSpace::Reg,
                );
                Ok(AddResult::new(Some(v), false, block_id))
            }

            Ast::BinaryOp(op, x, y) => {
                // expression, non-terminal
                let r = self.add(block_id, None, *x, b, d)?;
                let vx = r.value_id.unwrap();
                let v_block = r.block_id;
                let r = self.add(v_block, None, *y, b, d)?;
                let vy = r.value_id.unwrap();
                let v_block = r.block_id;
                let code = LCode::Op2(op.node, vx, vy);
                let ty = self.get_type(vx);
                let v = self.push_code(
                    code,
                    node.span_id,
                    scope_id,
                    v_block,
                    ty,
                    VarDefinitionSpace::Reg,
                );
                Ok(AddResult::new(Some(v), false, v_block))
            }

            Ast::Goto(label) => {
                // Goto is terminal
                if let Some(target_value_id) = self.env.resolve_block(label.into()) {
                    self.add_jump(block_id, target_value_id, vec![], node.span_id, b, d)
                } else {
                    let span = d.lookup(node.span_id);
                    d.push_diagnostic(error(
                        &format!("Block name not found: {}", b.r(label)),
                        span,
                    ));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            Ast::Return(maybe_expr) => {
                // return is terminal, anything after it should be ignored.
                if let Some(v_return) = self.env.resolve_return_block() {
                    let args = if let Some(expr) = maybe_expr {
                        vec![*expr]
                    } else {
                        vec![]
                    };
                    self.add_jump(block_id, v_return, args, node.span_id, b, d)
                } else {
                    let span = d.lookup(node.span_id);
                    d.push_diagnostic(error(&format!("Return without function context"), span));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            Ast::Global(name, expr) => {
                if let Ast::Literal(lit) = expr.node {
                    let static_scope_id = self.env.static_scope_id();
                    let static_block_id = self.env.static_block_id();
                    let scope = self.env.get_scope(scope_id);

                    let global_name = if let ScopeType::Static = scope.scope_type {
                        b.r(name).to_string()
                    } else {
                        let unique_name = b.unique_static_name();
                        let base = b.r(name);
                        format!("{}{}", base, unique_name).clone()
                    };

                    let ast_ty: AstType = lit.clone().into();

                    let code = LCode::Const(lit);
                    let v = self.push_code_with_name(
                        code,
                        node.span_id,
                        static_scope_id,
                        static_block_id,
                        ast_ty.clone(),
                        VarDefinitionSpace::Static,
                        b.s(&global_name),
                    );

                    let v = self.push_code_with_name(
                        LCode::Value(v),
                        expr.span_id,
                        scope_id,
                        block_id,
                        ast_ty,
                        VarDefinitionSpace::Static,
                        name,
                    );

                    Ok(AddResult::new(Some(v), false, block_id))
                } else {
                    unreachable!()
                }
            }

            Ast::Loop(name, body) => {
                // loop is a terminal, so we are expecting a next block
                self.add_loop(block_id, maybe_next.unwrap(), name, *body, b, d)
            }

            Ast::Break(maybe_name, args) => {
                // args not implemented yet
                assert_eq!(args.len(), 0);
                // loop up loop blocks by name
                if let Some(v_next) = self.env.get_loop_next_block(maybe_name) {
                    self.add_jump(block_id, v_next, vec![], node.span_id, b, d)
                } else {
                    let span = d.lookup(node.span_id);
                    d.push_diagnostic(error(&format!("Break without loop"), span));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            Ast::Continue(maybe_name, args) => {
                // args not implemented yet
                assert_eq!(args.len(), 0);
                // loop up loop blocks by name
                if let Some(v_start) = self.env.get_loop_start_block(maybe_name) {
                    self.add_jump(block_id, v_start, vec![], node.span_id, b, d)
                } else {
                    // mismatch name
                    let span = d.lookup(node.span_id);
                    d.push_diagnostic(error(&format!("Continue without loop"), span));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            Ast::Error => {
                let span = d.lookup(node.span_id);
                d.push_diagnostic(error(&format!("AST Error"), span));
                Err(Error::new(ParseError::Invalid))
            }

            _ => unimplemented!("{:?}", node.node),
        }
    }

    pub fn save_graph(&self, filename: &str, b: &NodeBuilder<E>) {
        use petgraph::dot::{Config, Dot};
        let cfg = self.get_graph(ValueId(0), None, b);
        let s = format!(
            "{:?}",
            Dot::with_attr_getters(
                &cfg.g,
                &[Config::EdgeNoLabel, Config::NodeNoLabel],
                &|_, _er| String::new(),
                &|_, (_index, data)| {
                    format!(
                        "label = \"[{}]{}\" shape={:?}",
                        data.block_id.0,
                        &data.name,
                        &data.ty.to_string()
                    )
                }
            )
        );
        println!("saved graph {:?}", filename);
        println!("{}", s);
        std::fs::write(filename, s).unwrap();
    }
}

#[derive(Debug)]
pub enum Shape {
    Box,
    Ellipsis,
}
impl Shape {
    fn to_string(&self) -> &str {
        match self {
            Self::Box => "box",
            Self::Ellipsis => "circle",
        }
    }
}
#[derive(Debug)]
pub struct Node {
    ty: Shape,
    pub(crate) name: String,
    pub(crate) block_id: ValueId,
}
impl Node {
    fn new_block(name: String, block_id: ValueId) -> Self {
        Self {
            ty: Shape::Box,
            name,
            block_id,
        }
    }
}

pub type CFGGraph = DiGraph<Node, ()>;

pub struct CFG {
    pub(crate) ids: HashMap<ValueId, NodeIndex>,
    pub(crate) g: CFGGraph,
}

impl CFG {
    pub fn new() -> Self {
        Self {
            ids: HashMap::new(),
            g: CFGGraph::new(),
        }
    }

    pub fn leafs(&self, block_id: ValueId) -> Vec<ValueId> {
        let mut out = vec![];
        let mut bfs = Bfs::new(&self.g, *self.ids.get(&block_id).unwrap());
        while let Some(nx) = bfs.next(&self.g) {
            let outgoing = self
                .g
                .edges_directed(nx, petgraph::Direction::Outgoing)
                .collect::<Vec<_>>();
            if outgoing.len() == 0 {
                let node = self.g.node_weight(nx).unwrap();
                out.push(node.block_id);
            }
        }
        out
    }

    pub fn blocks(&self, block_id: ValueId) -> Vec<ValueId> {
        let mut blocks = vec![];
        let mut bfs = Bfs::new(&self.g, *self.ids.get(&block_id).unwrap());
        while let Some(nx) = bfs.next(&self.g) {
            let node = self.g.node_weight(nx).unwrap();
            blocks.push(node.block_id);
        }
        blocks
    }
}

impl<E: Extra> Blockify<E> {
    pub fn get_cfg(&self, block_id: ValueId, b: &NodeBuilder<E>) -> CFG {
        self.get_graph(block_id, Some(Successor::BlockScope), b)
    }

    pub fn get_graph(
        &self,
        block_id: ValueId,
        scope: Option<Successor>,
        b: &NodeBuilder<E>,
    ) -> CFG {
        let mut cfg = CFG::new();

        let mut stack = VecDeque::new();
        stack.push_back(block_id);

        loop {
            if let Some(block_id) = stack.pop_front() {
                if cfg.ids.contains_key(&block_id) {
                    continue;
                }
                let name = self.code_to_string(block_id, b);
                let c = cfg.g.add_node(Node::new_block(name, block_id));
                cfg.ids.insert(block_id, c);

                let block = self.env.get_block(block_id);
                for (succ_type, next_block_id) in block.succ.iter() {
                    if scope.is_none() || scope == Some(*succ_type) {
                        stack.push_back(*next_block_id);
                    }
                }
            } else {
                break;
            }
        }

        for block_id in cfg.ids.keys() {
            let block = self.env.get_block(*block_id);
            let id = cfg.ids.get(block_id).unwrap();
            for (succ_type, next_block_id) in block.succ.iter() {
                if let Successor::BlockScope = succ_type {
                    let child_id = cfg.ids.get(next_block_id).unwrap();
                    cfg.g.add_edge(*id, *child_id, ());
                }
            }
        }
        cfg
    }
}
