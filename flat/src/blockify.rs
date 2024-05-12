use anyhow::Error;
use anyhow::Result;
use indexmap::IndexMap;
use thiserror::Error;

use compile_core::{
    Argument, AssignTarget, Ast, AstNode, AstType, BinaryOperation, BuiltinId, Lambda, LinkOptions,
    Literal, ParameterNode, SpanId, StringKey, UnaryOperation, VarDefinitionSpace,
};

use crate::{
    BlockId,
    Builtin,
    CodeOffset,
    Environment,
    NodeBuilder,
    //NodeBuilder as NB,
    ScopeId,
    ScopeType,
    StringLabel,
    TemplateId,
    ValueId,
};

#[derive(Error, Debug)]
pub enum BlockifyError {
    #[error("BlockifyError")]
    Invalid,
}

#[derive(Debug)]
pub struct LoopLayer {
    next: ValueId,
    restart: ValueId,
}

#[derive(Debug)]
pub enum LCode {
    Label(u8, u8), // number of positional arguments, number of named arguments
    Noop,
    Declare,
    DeclareFunction(Option<BlockId>), // optional entry block
    Value(ValueId),
    Arg(u8), // get the value of a positional arg
    Const(Literal),
    Op1(UnaryOperation, ValueId),
    Op2(BinaryOperation, ValueId, ValueId),
    Load(ValueId),
    Store(ValueId, ValueId), // memref, value to store
    Return(u8),              // return values
    Yield(u8),               // yield values

    //jump to named block, with 0 args
    //Goto(StringKey),

    // jump to block, with num args
    Jump(BlockId, u8),

    Branch(ValueId, BlockId, BlockId),
    Ternary(ValueId, BlockId, BlockId), // condition, then_entry, else_entry
    Builtin(BuiltinId, u8, u8),
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
            //Self::Goto(_) => true,
            Self::Branch(_, _, _) => true,
            Self::Return(_) => true,
            Self::Yield(_) => true,
            _ => false,
        }
    }
}

#[derive(Debug)]
pub enum NextSeqState {
    Empty,                // no nodes follow
    NextLabel(StringKey), // next node is a label, we can reuse it possibly
    //NextReturn,           // next node is a return statement
    Other, // all other options
}

impl NextSeqState {
    pub fn get(_env: &Environment, node: &AstNode, next_node: Option<&AstNode>) -> (bool, Self) {
        let is_term = match node.node {
            Ast::Branch(_, _, _) => true,
            Ast::Conditional(_, _, _) => true,
            //Ast::Test(_, _) => true,
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
                Ast::BlockStart(key, _) => (is_term, Self::NextLabel(key)),
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
    entry_id: CodeOffset,
}
impl AddResult {
    pub fn new(value_id: Option<ValueId>, is_term: bool, entry_id: CodeOffset) -> Self {
        Self {
            value_id,
            is_term,
            entry_id,
        }
    }
}

#[derive(Debug)]
pub struct Pending {
    name: StringLabel,
    scope_id: ScopeId,
    expr: AstNode,
    block_id: BlockId,
    next_block_id: Option<BlockId>,
    ty: AstType,
}

#[derive(Debug)]
pub struct PendingResult {
    block_id: BlockId,
    ty: AstType,
}

#[derive(Debug)]
pub struct Blockify {
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
    templates: Vec<Lambda>,
    pending: Vec<Pending>,

    // other
    pub env: Environment,
    // sparse names
    names: IndexMap<ValueId, StringLabel>,
    link: LinkOptions,
}

impl Blockify {
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
            pending: vec![],

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

    pub fn push_template(&mut self, def: Lambda) -> TemplateId {
        let offset = self.templates.len();
        self.templates.push(def);
        TemplateId(offset as u32)
    }

    pub fn get_template(&mut self, template_id: TemplateId) -> &Lambda {
        self.templates.get(template_id.index()).unwrap()
    }

    pub fn get_code(&self, value_id: ValueId) -> &LCode {
        self.code.get(value_id.index()).unwrap()
    }

    pub fn get_span_id(&self, value_id: ValueId) -> SpanId {
        self.span.get(value_id.index()).unwrap().clone()
    }

    pub fn get_mem(&self, value_id: ValueId) -> &VarDefinitionSpace {
        self.mem.get(value_id.index()).unwrap()
    }

    pub fn get_entry_id(&self, value_id: ValueId) -> ValueId {
        *self.entries.get(value_id.index()).unwrap()
    }

    pub fn get_scope_id(&self, value_id: ValueId) -> ScopeId {
        *self.scopes.get(value_id.index()).unwrap()
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

    pub fn get_previous_values(&self, v: ValueId, num: usize) -> Vec<ValueId> {
        let mut values = vec![];
        for i in 0..num {
            let v = ValueId((v.0 as usize - num + i) as u32);
            let code = self.get_code(v);
            if let LCode::Value(value_id) = code {
                values.push(*value_id);
            }
        }
        values
    }

    pub fn resolve_declaration<'c>(&self, value_id: ValueId) -> Option<ValueId> {
        let mut current = value_id;
        loop {
            let code = self.get_code(current);
            if let LCode::Value(next_value_id) = code {
                current = *next_value_id;
            } else {
                return Some(current);
            }
        }
    }

    pub fn push_code_with_name(
        &mut self,
        code: LCode,
        span_id: SpanId,
        scope_id: ScopeId,
        entry_id: BlockId,
        ty: AstType,
        mem: VarDefinitionSpace,
        name: StringKey,
    ) -> ValueId {
        let entry_id = self.env.resolve_code_offset(entry_id.into());
        let value_id = self.push_code(code, span_id, scope_id, entry_id.into(), ty.clone(), mem);
        self.env.scope_define(scope_id, name, value_id, ty, mem);
        self.names.insert(value_id, name.into());
        value_id
    }

    pub fn push_block_label(
        &mut self,
        name: StringLabel,
        span_id: SpanId,
        scope_id: ScopeId,
        block_id: BlockId,
        args: &[AstType],
        kwargs: &[ParameterNode],
        b: &mut NodeBuilder,
    ) -> ValueId {
        let code = LCode::Label(args.len() as u8, kwargs.len() as u8);

        let v_block = self._push_code(
            code,
            span_id,
            scope_id,
            // update later in function
            ValueId(0), // entry_id
            AstType::Unit,
            VarDefinitionSpace::Reg,
        );

        // update
        self.names.insert(v_block, name);
        self.env.block_name(scope_id, name, v_block, block_id);

        for (i, p) in kwargs.iter().enumerate() {
            let ty = b.types.r(p.ty);
            let v = self.push_code_with_name(
                LCode::Arg(i as u8),
                span_id,
                scope_id,
                block_id,
                ty.clone(),
                VarDefinitionSpace::Arg,
                p.name.into(),
            );
            self.names.insert(v, p.name.into());
            self.env
                .define(p.name, v, ty.clone(), VarDefinitionSpace::Arg);
        }

        self.env.block_entry(block_id, v_block);
        let scope = self.env.get_scope_mut(scope_id);
        scope.blocks.push(v_block);
        self.entries[v_block.index()] = v_block;

        // update these last
        let block = self.env.get_block_mut(v_block);
        block.last_value = Some(v_block);
        self._update_code(v_block, v_block);
        v_block
    }

    pub fn push_code_new_block(
        &mut self,
        code: LCode,
        span_id: SpanId,
        scope_id: ScopeId,
        ty: AstType,
    ) -> (BlockId, ValueId) {
        let v_block = self._push_code(
            code,
            span_id,
            scope_id,
            ValueId(0),
            ty,
            VarDefinitionSpace::Reg,
        );
        let block_id = self.env.new_block();
        self.env.block_entry(block_id, v_block);
        let scope = self.env.get_scope_mut(scope_id);
        scope.blocks.push(v_block);

        self.entries[v_block.index()] = v_block;
        self._update_code(v_block, v_block);
        (block_id, v_block)
    }

    pub fn push_code(
        &mut self,
        code: LCode,
        span_id: SpanId,
        scope_id: ScopeId,
        entry_id: CodeOffset,
        ty: AstType,
        mem: VarDefinitionSpace,
    ) -> ValueId {
        // update successor blocks
        let entry_id = self.env.resolve_code_offset(entry_id);
        match &code {
            LCode::Jump(target, _) => {
                // XXX: This is causing us to terminate the loop we are currently generating
                // If it knows about the loop, then it tries to terminate it
                self.env.add_succ_block(entry_id, (*target).into());
            }

            LCode::Branch(_, v_then, v_else) => {
                self.env.add_succ_block(entry_id, v_then.clone().into());
                self.env.add_succ_block(entry_id, v_else.clone().into());
            }

            LCode::Ternary(_, v_then, v_else) => {
                self.env.add_succ_op(entry_id, v_then.clone().into());
                self.env.add_succ_op(entry_id, v_else.clone().into());
            }
            _ => (),
        }

        let v = self._push_code(code, span_id, scope_id, entry_id, ty, mem);
        self._update_code(v, entry_id);

        v
    }

    pub fn _update_code(&mut self, value_id: ValueId, entry_id: ValueId) {
        let offset = value_id.0 as usize;
        let block = self.env.get_block(entry_id);
        let is_term = self.get_code(value_id).is_term();

        if let Some(last_value) = block.last_value {
            self.prev_pos[offset] = last_value;
            self.next_pos[last_value.0 as usize] = value_id;
            // check to ensure that nothing follows the terminator
            //assert!(!block.has_term());
        }

        let block = self.env.get_block_mut(entry_id);

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
        entry_id: ValueId,
        ty: AstType,
        mem: VarDefinitionSpace,
    ) -> ValueId {
        let offset = self.code.len();
        let v = ValueId(offset as u32);
        self.prev_pos.push(v);
        self.next_pos.push(v);
        self.scopes.push(scope_id);
        self.entries.push(entry_id);
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
        b: &mut NodeBuilder,
    ) -> ValueId {
        let (block_id, v_block) = self.push_code_new_block(
            LCode::Label(args.len() as u8, kwargs.len() as u8),
            span_id,
            scope_id,
            AstType::Unit,
        );
        self.names.insert(v_block, name);
        self.env.block_name(scope_id, name, v_block, block_id);
        let block = self.env.get_block_mut(v_block);
        block.last_value = Some(v_block);
        for (i, p) in kwargs.iter().enumerate() {
            let ty = b.types.r(p.ty);
            let v = self.push_code(
                LCode::Arg(i as u8),
                span_id,
                scope_id,
                v_block.into(),
                ty.clone(),
                VarDefinitionSpace::Arg,
            );
            self.names.insert(v, p.name.into());
            self.env
                .define(p.name, v, ty.clone(), VarDefinitionSpace::Arg);
        }
        v_block
    }

    pub fn resolve_block_label(&self, k: ValueId, b: &NodeBuilder) -> String {
        if let Some(key) = self.names.get(&k) {
            b.labels.r(*key).to_string()
        } else {
            format!("b{}", k.0)
        }
    }

    pub fn resolve_block_id(&self, offset: CodeOffset) -> BlockId {
        match offset {
            CodeOffset::Value(value_id) => self.env.block_map.get(&value_id).unwrap().clone(),
            CodeOffset::Block(block_id) => block_id,
        }
    }

    pub fn get_type(&self, v: ValueId) -> AstType {
        self.types.get(v.0 as usize).unwrap().clone()
    }

    pub fn build_module(&mut self, node: AstNode, b: &mut NodeBuilder) -> Result<ValueId> {
        match node.node {
            Ast::Module(name, body) => {
                let static_scope = self.env.new_scope(ScopeType::Static);
                let entry_id =
                    self.push_label(name.into(), node.span_id, static_scope, &[], &[], b);
                self.env.enter_scope(static_scope);
                self.add(entry_id.into(), None, *body, b)?;
                self.env.exit_scope();
                Ok(entry_id)
            }
            _ => unreachable!(),
        }
    }

    pub fn add_sequence(
        &mut self,
        entry_id: CodeOffset,
        maybe_next: Option<BlockId>,
        node: AstNode,
        b: &mut NodeBuilder,
    ) -> Result<AddResult> {
        let scope_id = self.env.current_scope().unwrap();
        // flatten
        let exprs = node.to_vec();

        // generate blocks for all predefined labels
        // this needs to be done first as a forward declaration
        for expr in exprs.iter() {
            if let Ast::BlockStart(name, args) = &expr.node {
                assert_eq!(0, args.len());
                let _ = self.push_label(name.into(), expr.span_id, scope_id, &[], &[], b);
            }
        }

        let mut value_id = None;
        let mut current_entry_id = Some(entry_id);
        let mut iter = exprs.into_iter().peekable();
        let mut current_is_term = false;
        loop {
            if let Some(expr) = iter.next() {
                let expr_span_id = expr.span_id;
                let (is_term, next_state) = NextSeqState::get(&self.env, &expr, iter.peek());
                match (is_term, next_state) {
                    (_, NextSeqState::NextLabel(key)) => {
                        // next label handles implicit jumps
                        if let Some(target_block_id) = self.env.resolve_block_id(key.into()) {
                            // ensure target block exists
                            //let scope = self.env.get_scope_mut(scope_id);
                            //scope.next_block = Some(target_value_id);
                            //current_entry_id = Some(target_value_id);
                            let r = self.add(
                                current_entry_id.unwrap(),
                                Some(target_block_id),
                                expr,
                                b,
                            )?;
                            let v = r.value_id.unwrap();
                            current_is_term = r.is_term;
                            assert_eq!(current_is_term, is_term);
                            //current_entry_id = Some(*self.entries.get(v.0 as usize).unwrap());
                            current_entry_id = Some(r.entry_id.into());
                            //assert_eq!(current_block_id.unwrap(), r.block_id);
                            value_id = Some(v);
                            //println!("r6: {:?}", r);
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
                        let r = self.add(current_entry_id.unwrap(), maybe_next, expr, b)?;
                        // skip noops
                        if let Some(v) = r.value_id {
                            current_is_term = r.is_term;
                            //assert_eq!(current_is_term, is_term);
                            current_entry_id = Some(r.entry_id.into());
                            //assert_eq!(current_block_id.unwrap(), r.block_id);
                            value_id = Some(v);
                        }
                        //println!("r3: {:?}", r);
                    }

                    (true, NextSeqState::Empty) => {
                        // terminal at the end of the sequence, nothing special here
                        // but we do need to pass the next block in, so that it knows
                        // what to do for sub expressions
                        let r = self.add(current_entry_id.unwrap(), maybe_next, expr, b)?;
                        let v = r.value_id.unwrap();
                        current_is_term = r.is_term;
                        assert!(r.is_term);
                        assert_eq!(current_is_term, is_term);
                        current_entry_id = Some(r.entry_id.into());
                        value_id = Some(v);
                        //println!("r4: {:?}", r);
                    }

                    (false, NextSeqState::Empty) => {
                        // end of sequence, with non-terminal node
                        let r = if let Some(v_next) = maybe_next {
                            //let r = if let Some(v_next) = self.env.get_next_block() {
                            assert_eq!(v_next, maybe_next.unwrap());
                            // terminates with a jump to next
                            self.add_with_next(current_entry_id.unwrap(), expr, v_next.into(), b)?
                        } else {
                            // must terminate, unless it's at the static level
                            self.add(current_entry_id.unwrap(), None, expr, b)?
                        };

                        let v = r.value_id.unwrap();
                        current_is_term = r.is_term;
                        current_entry_id = Some(r.entry_id.into());
                        value_id = Some(v);
                        //println!("r2: {:?}", r);

                        // check that this terminates correctly
                        // exception for module level
                        assert!(r.is_term || self.env.static_entry_id() == r.entry_id.into());
                    }

                    (true, NextSeqState::Other) => {
                        // a terminal, followed by other statements
                        // we create a next block for the statements to follow
                        let name = b.labels.s("next");
                        let v_next =
                            self.push_label(name.into(), expr_span_id, scope_id, &[], &[], b);
                        let v_next = self.resolve_block_id(v_next.into());
                        let r = self.add_with_next(current_entry_id.unwrap(), expr, v_next, b)?;
                        let v = r.value_id.unwrap();
                        current_is_term = r.is_term;
                        //println!("r1: {:?}", r);
                        assert!(r.is_term);
                        assert_eq!(current_is_term, is_term);
                        // next block is the next block
                        current_entry_id = Some(r.entry_id.into());
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
        assert!(current_is_term || self.env.static_entry_id() == current_entry_id.unwrap());
        Ok(AddResult::new(
            value_id,
            current_is_term,
            current_entry_id.unwrap(),
        ))
    }

    pub fn add_lambda_and_call(
        &mut self,
        current_entry_id: CodeOffset,
        template_id: TemplateId,
        args: Vec<Argument>,
        span_id: SpanId,
        b: &mut NodeBuilder,
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
        let new_entry_id = self.push_label(label_name, span_id, body_scope_id, &[], &def.params, b);

        let mut jump_args = vec![];
        for a in args.into_iter() {
            let Argument::Positional(expr) = a;
            jump_args.push(*expr);
        }

        assert_eq!(args_size as usize, jump_args.len());
        // jump to entry
        let new_block_id = self.resolve_block_id(new_entry_id.into());
        let _r = self.add_jump(current_entry_id, new_block_id, jump_args, span_id, b)?;
        self.env.add_succ_block(
            self.env.resolve_code_offset(current_entry_id),
            new_entry_id.into(),
        );
        // return block is the next block

        // handle body
        //let return_type = *def.return_type;
        let return_type = b.types.r(def.return_type).clone();
        let return_type_args = match &return_type {
            AstType::Unit => vec![],
            _ => vec![return_type.clone()],
        };

        let name = b.labels.s("lambda_result");
        let v_next = self.push_label(name.into(), span_id, scope_id, &return_type_args, &[], b);
        let v_next = self.resolve_block_id(v_next.into());

        // push Arg to next block
        let v_expr = self.push_code(
            LCode::Arg(0),
            span_id,
            scope_id,
            v_next.into(),
            return_type,
            VarDefinitionSpace::Reg,
        );

        let ret_block_id = self.resolve_block_id(v_next.into());
        let scope = self.env.get_scope_mut(body_scope_id);
        scope.return_block = Some(ret_block_id);
        scope.entry_block = Some(new_entry_id.into());
        self.env.enter_scope(body_scope_id);
        let _r1 = self.add_with_next(current_entry_id.into(), *body, v_next, b)?;
        self.env.exit_scope();

        // we return the value of the arg in the next block
        let r2 = AddResult::new(Some(v_expr), false, v_next.into());
        //println!("lambda: {:?}", (&r1, &r2));
        Ok(r2)
    }

    pub fn add_return_block(
        &mut self,
        scope_id: ScopeId,
        block_id: BlockId,
        span_id: SpanId,
        return_type: AstType,
        b: &mut NodeBuilder,
    ) -> Result<()> {
        let name = b.labels.s("ret");
        let args = match &return_type {
            AstType::Unit => vec![],
            _ => vec![return_type.clone()],
        };
        let entry_id =
            self.push_block_label(name.into(), span_id, scope_id, block_id, &args, &[], b);

        let v_args = args
            .iter()
            .enumerate()
            .map(|(i, _arg)| {
                let v_arg = self.push_code(
                    LCode::Arg(i as u8),
                    span_id,
                    scope_id,
                    entry_id.into(),
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
                scope_id,
                entry_id.into(),
                return_type.clone(),
                VarDefinitionSpace::Arg,
            );
        }

        self.push_code(
            LCode::Return(v_args.len() as u8),
            span_id,
            scope_id,
            entry_id.into(),
            AstType::Unit,
            VarDefinitionSpace::Reg,
        );
        Ok(())
    }

    pub fn add_function(
        &mut self,
        current_entry_id: CodeOffset,
        function_name: StringKey,
        def: Lambda,
        span_id: SpanId,
        b: &mut NodeBuilder,
    ) -> Result<AddResult> {
        //println!("add_function: {}", b.labels.r(function_name.into()));
        let scope_id = self.env.current_scope().unwrap();

        let params = def
            .params
            .iter()
            .map(|p| {
                let ty = b.types.r(p.ty);
                ty.clone()
            })
            .collect();
        //let spans = def.params.iter().map(|p| p.span_id).collect::<Vec<_>>();
        let return_type = b.types.r(def.return_type).clone();
        let ty = AstType::Func(params, return_type.clone().into());

        if let Some(body) = def.body {
            let body_scope_id = self.env.new_scope(ScopeType::Function);

            //let new_block_id = self.env.new_block();
            //
            // entry first
            let new_entry_id = self.push_label(
                function_name.into(),
                span_id,
                body_scope_id,
                //new_block_id,
                &[],
                &def.params,
                b,
            );

            // return block
            //
            let ret_block_id = self.env.new_block();
            let _ = self.add_return_block(body_scope_id, ret_block_id, span_id, return_type, b)?;

            //self.new_pending(name, b.ret()

            // handle body

            let scope = self.env.get_scope_mut(body_scope_id);
            scope.return_block = Some(ret_block_id);
            scope.entry_block = Some(new_entry_id);

            // declare function before adding the body, for recursion
            let v_decl = self.push_code_with_name(
                LCode::DeclareFunction(Some(self.resolve_block_id(new_entry_id.into()))),
                span_id,
                scope_id,
                self.resolve_block_id(current_entry_id),
                ty.clone(),
                VarDefinitionSpace::Static,
                function_name,
            );

            self.env.enter_scope(body_scope_id);
            // next block in body scope
            self.add_with_next(new_entry_id.into(), *body, ret_block_id.into(), b)?;
            self.env.exit_scope();
            self.env
                .add_succ_static(self.env.resolve_code_offset(current_entry_id), new_entry_id);

            Ok(AddResult::new(Some(v_decl), false, current_entry_id))
        } else {
            Ok(AddResult::new(
                Some(self.push_code_with_name(
                    LCode::DeclareFunction(None),
                    span_id,
                    scope_id,
                    self.resolve_block_id(current_entry_id),
                    //current_entry_id,
                    ty.clone(),
                    VarDefinitionSpace::Static,
                    function_name,
                )),
                false,
                current_entry_id,
            ))
        }
    }

    pub fn add_loop(
        &mut self,
        entry_id: CodeOffset,
        v_next: BlockId,
        name: StringKey,
        body: AstNode,
        b: &mut NodeBuilder,
    ) -> Result<AddResult> {
        let span_id = body.span_id;
        let loop_scope_id = self.env.new_scope(ScopeType::Loop);
        let v_loop = self.push_label(name.into(), span_id, loop_scope_id, &[], &[], b);
        let b_loop = self.resolve_block_id(v_loop.into());
        self.env
            .push_loop_blocks(Some(name), v_next.into(), v_loop.into());

        self.env.enter_scope(loop_scope_id);
        let _ = self.add_with_next(v_loop.into(), body, v_next.into(), b)?;
        self.env.exit_scope();

        // enter loop
        let r = self.add_jump(entry_id, b_loop, vec![], span_id, b)?;
        Ok(AddResult::new(
            Some(r.value_id.unwrap()),
            true,
            v_next.into(),
        ))
    }

    pub fn add_jump(
        &mut self,
        entry_id: CodeOffset,
        target_id: BlockId,
        jump_args: Vec<AstNode>,
        span_id: SpanId,
        b: &mut NodeBuilder,
    ) -> Result<AddResult> {
        let scope_id = self.env.current_scope().unwrap();
        let num_args = jump_args.len();

        let mut values = vec![];
        for arg in jump_args.into_iter() {
            let r = self.add(entry_id, None, arg, b)?;
            let expr_value_id = r.value_id.unwrap();
            values.push(expr_value_id);
        }

        for value_id in values {
            self.push_code(
                LCode::Value(value_id),
                span_id,
                scope_id,
                entry_id,
                self.get_type(value_id),
                VarDefinitionSpace::Reg,
            );
        }

        let v = self.push_code(
            LCode::Jump(target_id.into(), num_args as u8),
            span_id,
            scope_id,
            entry_id,
            AstType::Unit,
            VarDefinitionSpace::Reg,
        );
        Ok(AddResult::new(Some(v), true, entry_id))
    }

    pub fn add_with_next(
        &mut self,
        entry_id: CodeOffset,
        node: AstNode,
        v_next: BlockId,
        b: &mut NodeBuilder,
    ) -> Result<AddResult> {
        let span_id = node.span_id;
        let r = self.add(entry_id.into(), Some(v_next), node, b)?;
        let v_block = r.entry_id;
        let v = r.value_id.unwrap();
        let last_entry_id = self.get_entry_id(v);
        //assert_eq!(last_entry_id, r.entry_id);
        let block = self.env.get_block(last_entry_id);

        //let v_next = self.resolve_block_id(v_next);
        if !block.has_term() {
            // if the block doesn't explicitely terminate, then we jump to the next block
            self.add_jump(v_block, v_next, vec![], span_id, b)
        } else {
            Ok(r)
        }
    }

    pub fn add_function_call(
        &mut self,
        scope_id: ScopeId,
        entry_id: CodeOffset,
        v_func: ValueId,
        args: Vec<Argument>,
        span_id: SpanId,
        b: &mut NodeBuilder,
    ) -> Result<AddResult> {
        let ty = self.get_type(v_func);

        if let AstType::Func(func_arg_types, ret) = &ty {
            if func_arg_types.len() != args.len() {
                b.push_error(
                    &format!(
                        "Call arity mismatch: {}<=>{}",
                        func_arg_types.len(),
                        args.len()
                    ),
                    span_id,
                );
                return Err(Error::new(BlockifyError::Invalid));
            }

            let args_size = args.len() as u8;
            let mut values = vec![];
            for (a, ty) in args.into_iter().zip(func_arg_types.iter()) {
                match a {
                    Argument::Positional(expr) => {
                        let r = self.add(entry_id, None, *expr, b)?;
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
                    entry_id,
                    ty,
                    VarDefinitionSpace::Reg,
                );
            }
            let v = self.push_code(
                LCode::Call(v_func, args_size, 0),
                span_id,
                scope_id,
                entry_id,
                *ret.clone(),
                VarDefinitionSpace::Reg,
            );
            Ok(AddResult::new(Some(v), false, entry_id))
        } else {
            let name = b.labels.r(self.get_name(v_func).unwrap());
            b.push_error(&format!("Type not function: {}, {:?}", name, ty), span_id);
            return Err(Error::new(BlockifyError::Invalid));
        }
    }

    pub fn add_noop(&mut self, entry_id: CodeOffset, span_id: SpanId) -> Result<Option<ValueId>> {
        let scope_id = self.env.current_scope().unwrap();
        Ok(Some(self.push_code(
            LCode::Noop,
            span_id,
            scope_id,
            entry_id,
            AstType::Unit,
            VarDefinitionSpace::Reg,
        )))
    }

    pub fn add_block_with_expr(
        &mut self,
        name: StringLabel,
        block_id: BlockId,
        v_next: Option<BlockId>,
        expr: AstNode,
        args: &[AstType],
        kwargs: &[ParameterNode],
        b: &mut NodeBuilder,
    ) -> Result<AddResult> {
        let scope_id = self.env.new_scope(ScopeType::Block);
        let v_then = self.push_block_label(
            name.into(),
            expr.span_id,
            scope_id,
            block_id,
            args,
            kwargs,
            b,
        );
        self.env.enter_scope(scope_id);
        let r = if let Some(v_next) = v_next {
            self.add_with_next(v_then.into(), expr, v_next, b)?
        } else {
            self.add(v_then.into(), None, expr, b)?
        };
        let _ = r.value_id.unwrap();
        self.env.exit_scope();
        Ok(r)
    }

    pub fn new_pending(
        &mut self,
        name: StringLabel,
        expr: AstNode,
        scope_id: ScopeId,
        next_block_id: Option<BlockId>,
        args: &[AstType],
        kwargs: &[ParameterNode],
        b: &mut NodeBuilder,
    ) -> Pending {
        let entry_id = self.push_label(name, expr.span_id, scope_id, args, kwargs, b);
        let block_id = self.resolve_block_id(entry_id.into());
        let ty = b.types.fresh_unknown();
        Pending {
            name,
            expr,
            scope_id,
            block_id,
            next_block_id,
            ty,
        }
    }

    pub fn add_pending(&mut self, pending: Pending, b: &mut NodeBuilder) -> Result<PendingResult> {
        self.env.enter_scope(pending.scope_id);
        let r = self.add(
            pending.block_id.into(),
            pending.next_block_id,
            pending.expr,
            b,
        )?;
        self.env.exit_scope();
        let block_id = self.resolve_block_id(pending.block_id.into());
        let v_result = r.value_id.unwrap();
        let ty = self.get_type(v_result);
        let type_id1 = b.types.s(&pending.ty);
        let type_id2 = b.types.s(&ty);
        b.types.unify(type_id1, type_id2);
        Ok(PendingResult { block_id, ty })
    }

    pub fn push_pending(&mut self, pending: Pending) {
        self.pending.push(pending);
    }

    pub fn add(
        &mut self,
        entry_id: CodeOffset,
        maybe_next: Option<BlockId>,
        node: AstNode,
        b: &mut NodeBuilder,
    ) -> Result<AddResult> {
        let r = self._add(entry_id, maybe_next, node, b)?;
        if r.is_term {
            let pendings = self.pending.drain(..).collect::<Vec<_>>();
            for pending in pendings {
                self.add_pending(pending, b)?;
            }
        }
        Ok(r)
    }

    pub fn _add(
        &mut self,
        entry_id: CodeOffset,
        maybe_next: Option<BlockId>,
        node: AstNode,
        b: &mut NodeBuilder,
    ) -> Result<AddResult> {
        let scope_id = self.env.current_scope().unwrap();
        match node.node {
            Ast::Module(_, _) => {
                // nested modules are not yet implemented
                unimplemented!()
            }

            Ast::Sequence(ref _exprs) => self.add_sequence(entry_id, maybe_next, node, b),

            Ast::Lambda(_def) => {
                unreachable!();
            }

            Ast::Call(expr, args, _ret_ty) => match &expr.node {
                // call is an expression, it's non-terminal
                // lambdas should also be non-terminal
                Ast::Identifier(ident) => {
                    let name = b.labels.r(ident.into());
                    if let Some(data) = self.env.resolve_name(*ident) {
                        return self.add_function_call(
                            scope_id,
                            entry_id,
                            data.value_id,
                            args,
                            node.span_id,
                            b,
                        );
                    }

                    if let Some(scope_id) = self.env.resolve_lambda_scope(ident.into()) {
                        let scope = self.env.get_scope(scope_id);
                        let label: StringLabel = (*ident).into();
                        let template_id = scope.lambdas.get(&label).unwrap();
                        return self.add_lambda_and_call(
                            entry_id,
                            *template_id,
                            args,
                            node.span_id,
                            b,
                        );
                    }
                    b.push_error(&format!("Call name not found: {}", name), node.span_id);
                    return Err(Error::new(BlockifyError::Invalid));
                }
                _ => {
                    unimplemented!("{:?}", expr.node);
                }
            },

            Ast::BlockStart(name, args) => {
                // all blocks should have been forward declared in the sequence
                let value_id = self.env.resolve_block(name.into()).unwrap();
                assert_eq!(0, args.len());

                let block = self.env.get_block(self.env.resolve_code_offset(entry_id));
                if let Some(last_value) = block.last_value {
                    // check to ensure that the previous block was terminated
                    let code = self.code.get(last_value.0 as usize).unwrap();
                    if !code.is_term() {
                        // TODO: add implicit jump to this block
                        // Ast labels have no arguments, so this should be trivial
                        unreachable!();
                    }
                }

                Ok(AddResult::new(Some(value_id), false, value_id.into()))
            }

            Ast::Identifier(key) => {
                // identifier is expression, non-terminal
                if let Some(data) = self.env.resolve_name(key) {
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
                        entry_id,
                        ty,
                        data.mem.clone(),
                    );
                    Ok(AddResult::new(Some(v), false, entry_id))
                } else {
                    b.push_error("Name not found", node.span_id);
                    Err(Error::new(BlockifyError::Invalid))
                }
            }

            Ast::Assign(target, expr) => {
                // assign is expression, non-terminal
                let name = match target {
                    AssignTarget::Identifier(name) | AssignTarget::Alloca(name) => name,
                };

                // push the definition into the lambda list
                if let Ast::Lambda(def) = expr.node {
                    let template_id = self.push_template(def);
                    let scope = self.env.get_scope_mut(scope_id);
                    scope.lambdas.insert(name.into(), template_id);
                    return Ok(AddResult::new(None, false, entry_id));
                }

                let r = self.add(entry_id, None, *expr, b)?;

                let v_expr = r.value_id.unwrap();
                let v_block = r.entry_id;

                let expr_ty = self.get_type(v_expr);

                let v_decl = if let Some(data) = self.env.resolve_name(name) {
                    assert_eq!(data.ty, expr_ty);
                    data.value_id
                } else {
                    self.push_code_with_name(
                        LCode::Declare,
                        node.span_id,
                        scope_id,
                        self.resolve_block_id(v_block),
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

            Ast::Builtin(id, mut args) => {
                let bi = b.builtins.get_enum(id);
                match bi {
                    Builtin::Import => {
                        let arg = args.pop().unwrap();
                        if let Some(s) = arg.try_string() {
                            self.link.add_library(&s);
                        } else {
                            b.push_error("Expected string", node.span_id);
                        }
                        Ok(AddResult::new(None, false, entry_id))
                    }
                    _ => {
                        let _ty = bi.get_return_type();
                        let args_size = args.len();
                        assert_eq!(args_size, bi.arity());
                        let mut values = vec![];
                        for a in args.into_iter() {
                            let Argument::Positional(expr) = a;
                            let r = self.add(entry_id, None, *expr, b)?;
                            let v = r.value_id.unwrap();
                            let ty = self.get_type(v);
                            values.push((v, ty));
                        }

                        for (v, ty) in values {
                            self.push_code(
                                LCode::Value(v),
                                node.span_id,
                                scope_id,
                                entry_id,
                                ty,
                                VarDefinitionSpace::Reg,
                            );
                        }

                        let ty = bi.get_return_type();
                        let value_id = self.push_code(
                            LCode::Builtin(id, args_size as u8, 0),
                            node.span_id,
                            scope_id,
                            entry_id,
                            ty,
                            VarDefinitionSpace::Reg,
                        );
                        Ok(AddResult::new(Some(value_id), false, entry_id))
                    }
                }
            }

            Ast::Literal(lit) => {
                // literal is expression, non-terminal
                let ty: AstType = lit.clone().into();
                let v = self.push_code(
                    LCode::Const(lit),
                    node.span_id,
                    scope_id,
                    entry_id,
                    ty,
                    VarDefinitionSpace::Reg,
                );
                Ok(AddResult::new(Some(v), false, entry_id))
            }

            Ast::UnaryOp(op, x) => {
                // op1 is expression, non-terminal
                let r = self.add(entry_id, None, *x, b)?;
                let v_block = r.entry_id;
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

                let v_next = maybe_next.unwrap();
                assert_eq!(v_next, maybe_next.unwrap());

                let then_block_id = self.env.new_block();

                let else_block_id = if let Some(_) = maybe_else_expr {
                    self.env.new_block()
                } else {
                    v_next
                    //self.resolve_block_id(v_next)
                };

                // condition
                let span_id = condition.span_id;
                let r = self.add(entry_id, None, *condition, b)?;
                let v = r.value_id.unwrap();

                // branch
                let code = LCode::Branch(v, then_block_id.into(), else_block_id.into());
                let v = self.push_code(
                    code,
                    span_id,
                    scope_id,
                    r.entry_id,
                    AstType::Unit,
                    VarDefinitionSpace::Reg,
                );

                // THEN
                // push block then_block_id, with expr then_expr
                let name = b.labels.s("then");
                let _ = self.add_block_with_expr(
                    name.into(),
                    then_block_id,
                    Some(v_next),
                    *then_expr,
                    &[],
                    &[],
                    b,
                )?;

                // ELSE
                if let Some(else_expr) = maybe_else_expr {
                    let name = b.labels.s("else");
                    let _ = self.add_block_with_expr(
                        name.into(),
                        else_block_id,
                        Some(v_next),
                        *else_expr,
                        &[],
                        &[],
                        b,
                    )?;
                }

                Ok(AddResult::new(Some(v), true, v_next.into()))
            }

            Ast::Ternary(c, x, y) => {
                // expression, non-terminal
                let condition_span_id = c.span_id;
                let r = self.add(entry_id, None, *c, b)?;
                let v_c = r.value_id.unwrap();

                let scope_id = self.env.new_scope(ScopeType::Block);
                let p_then = self.new_pending(
                    b.labels.s("then").into(),
                    AstNode::make_yield(*x),
                    scope_id,
                    None,
                    &[],
                    &[],
                    b,
                );
                let then_block_id = p_then.block_id;
                let then_ty = p_then.ty.clone();

                let scope_id = self.env.new_scope(ScopeType::Block);
                let p_else = self.new_pending(
                    b.labels.s("else").into(),
                    AstNode::make_yield(*y),
                    scope_id,
                    None,
                    &[],
                    &[],
                    b,
                );
                let else_block_id = p_else.block_id;

                // two unknowns needs to be unified
                /*
                let else_ty = p_else.ty.clone();
                let then_type_id = b.types.s(&then_ty);
                let else_type_id = b.types.s(&else_ty);
                b.types.unify(then_type_id, else_type_id);
                */

                /*
                let result = self.add_pending(p_then, b)?;
                let then_ty = result.ty;
                let result = self.add_pending(p_else, b)?;
                let else_ty = result.ty;
                */

                self.push_pending(p_then);
                self.push_pending(p_else);

                //assert_eq!(then_ty, else_ty);

                let code = LCode::Ternary(v_c, then_block_id, else_block_id);
                let v = self.push_code(
                    code,
                    condition_span_id,
                    scope_id,
                    entry_id,
                    then_ty, // the branches should match
                    VarDefinitionSpace::Reg,
                );

                Ok(AddResult::new(Some(v), false, entry_id))
            }

            Ast::BinaryOp(op, x, y) => {
                // expression, non-terminal
                let r = self.add(entry_id, None, *x, b)?;
                let vx = r.value_id.unwrap();
                let v_block = r.entry_id;
                let r = self.add(v_block, None, *y, b)?;
                let vy = r.value_id.unwrap();
                let v_block = r.entry_id;
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
                if let Some(target_block_id) = self.env.resolve_block_id(label.into()) {
                    self.add_jump(entry_id, target_block_id, vec![], node.span_id, b)
                } else {
                    b.push_error(
                        &format!("Block name not found: {}", b.labels.r(label.into())),
                        node.span_id,
                    );
                    Err(Error::new(BlockifyError::Invalid))
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
                    self.add_jump(entry_id, v_return.into(), args, node.span_id, b)
                } else {
                    b.push_error(&format!("Return without function context"), node.span_id);
                    Err(Error::new(BlockifyError::Invalid))
                }
            }

            Ast::Yield(maybe_expr) => {
                // yield is terminal
                let mut n_args = 0;
                let mut v_block = entry_id;
                let mut ty = AstType::Unit;
                if let Some(expr) = maybe_expr {
                    let r = self.add(entry_id, None, *expr, b)?;
                    if let Some(v) = r.value_id {
                        ty = self.get_type(v);
                        n_args = 1;
                        v_block = r.entry_id;

                        // push single arg
                        let code = LCode::Value(v);
                        self.push_code(
                            code,
                            node.span_id,
                            scope_id,
                            v_block,
                            ty.clone(),
                            VarDefinitionSpace::Reg,
                        );
                    }
                }

                let v = self.push_code(
                    LCode::Yield(n_args),
                    node.span_id,
                    scope_id,
                    v_block,
                    ty,
                    VarDefinitionSpace::Reg,
                );

                Ok(AddResult::new(Some(v), true, v_block))
            }

            Ast::Global(name, expr) => match expr.node {
                Ast::Lambda(def) => self.add_function(entry_id, name, def, node.span_id, b),
                Ast::Literal(lit) => {
                    let static_scope_id = self.env.static_scope_id();
                    let static_entry_id = self.env.static_entry_id();
                    let scope = self.env.get_scope(scope_id);

                    let global_name = if let ScopeType::Static = scope.scope_type {
                        b.labels.r(name.into()).to_string()
                    } else {
                        let unique_name = b.unique_static_name();
                        let base = b.labels.r(name.into());
                        format!("{}{}", base, unique_name).clone()
                    };

                    let ast_ty: AstType = lit.clone().into();

                    let code = LCode::Const(lit);
                    let v = self.push_code_with_name(
                        code,
                        node.span_id,
                        static_scope_id,
                        self.resolve_block_id(static_entry_id),
                        ast_ty.clone(),
                        VarDefinitionSpace::Static,
                        b.labels.s(&global_name),
                    );

                    let v = self.push_code_with_name(
                        LCode::Value(v),
                        expr.span_id,
                        scope_id,
                        self.resolve_block_id(entry_id),
                        //entry_id,
                        ast_ty,
                        VarDefinitionSpace::Static,
                        name,
                    );

                    Ok(AddResult::new(Some(v), false, entry_id))
                }
                _ => unreachable!(),
            },

            Ast::Loop(name, body) => {
                // loop is a terminal, so we are expecting a next block
                self.add_loop(entry_id, maybe_next.unwrap(), name, *body, b)
            }

            Ast::Break(maybe_name, args) => {
                // args not implemented yet
                assert_eq!(args.len(), 0);
                // loop up loop blocks by name
                if let Some(loop_scope) = self.env.get_loop_scope(maybe_name) {
                    let v_next = loop_scope.next_block;
                    let v_next = self.resolve_block_id(v_next);
                    self.add_jump(entry_id, v_next, vec![], node.span_id, b)
                } else {
                    b.push_error(&format!("Break without loop"), node.span_id);
                    Err(Error::new(BlockifyError::Invalid))
                }
            }

            Ast::Continue(maybe_name, args) => {
                // args not implemented yet
                assert_eq!(args.len(), 0);
                // loop up loop blocks by name
                if let Some(loop_scope) = self.env.get_loop_scope(maybe_name) {
                    let v_start = loop_scope.start_block;
                    let v_start = self.resolve_block_id(v_start);
                    self.add_jump(entry_id, v_start, vec![], node.span_id, b)
                } else {
                    // mismatch name
                    b.push_error(&format!("Continue without loop"), node.span_id);
                    Err(Error::new(BlockifyError::Invalid))
                }
            }

            Ast::Error => {
                b.push_error(&format!("AST Error"), node.span_id);
                Err(Error::new(BlockifyError::Invalid))
            }

            _ => unimplemented!("{:?}", node.node),
        }
    }
}
