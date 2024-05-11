use anyhow::Error;
use anyhow::Result;
use indexmap::IndexMap;
use std::collections::HashMap;
use thiserror::Error;

use compile_core::{
    Argument, AssignTarget, Ast, AstNode, AstType, BinaryOperation, BuiltinId, Definition,
    Diagnostic, Label, LinkOptions, Literal, ParameterNode, Span, SpanId, StringKey,
    UnaryOperation, VarDefinitionSpace,
};

use crate::{
    BlockId, Builtin, CodeOffset, Environment, NodeBuilder, ScopeId, ScopeType, StringLabel,
    TemplateId, ValueId,
};

#[derive(Error, Debug)]
pub enum BlockifyError {
    #[error("BlockifyError")]
    Invalid,
}

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

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum SymIndex {
    Op(ValueId, usize),
    Arg(ValueId, usize),
    Def(ValueId, usize),
}

impl SymIndex {
    pub fn block(&self) -> ValueId {
        match self {
            SymIndex::Op(block_index, _)
            | SymIndex::Arg(block_index, _)
            | SymIndex::Def(block_index, _) => *block_index,
        }
    }

    pub fn offset(&self) -> usize {
        match self {
            SymIndex::Op(_, offset) | SymIndex::Arg(_, offset) | SymIndex::Def(_, offset) => {
                *offset
            }
        }
    }

    pub fn is_op(&self) -> bool {
        if let SymIndex::Op(_, _) = self {
            true
        } else {
            false
        }
    }

    pub fn is_arg(&self) -> bool {
        if let SymIndex::Arg(_, _) = self {
            true
        } else {
            false
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
    Label(u8, u8), // number of positional arguments, number of named arguments
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
    Jump(CodeOffset, u8),
    Branch(ValueId, ValueId, ValueId),
    Ternary(ValueId, ValueId, ValueId), // condition, then_entry, else_entry
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
            Self::Goto(_) => true,
            Self::Branch(_, _, _) => true,
            Self::Return(_) => true,
            _ => false,
        }
    }
}

pub fn error(msg: &str, span: Span) -> Diagnostic<usize> {
    let mut labels = vec![];
    if let Span::Loc(span) = span {
        let r = span.begin.pos as usize..span.end.pos as usize;
        labels = vec![Label::primary(span.file_id, r).with_message(msg)];
    }

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
    entry_id: ValueId,
}
impl AddResult {
    pub fn new(value_id: Option<ValueId>, is_term: bool, entry_id: ValueId) -> Self {
        Self {
            value_id,
            is_term,
            entry_id,
        }
    }
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
    templates: Vec<Definition>,

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

    pub fn push_template(&mut self, def: Definition) -> TemplateId {
        let offset = self.templates.len();
        self.templates.push(def);
        TemplateId(offset as u32)
    }

    pub fn get_template(&mut self, template_id: TemplateId) -> &Definition {
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
        entry_id: ValueId,
        ty: AstType,
        mem: VarDefinitionSpace,
        name: StringKey,
    ) -> ValueId {
        let value_id = self.push_code(code, span_id, scope_id, entry_id, ty.clone(), mem);
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
        entry_id: ValueId,
        ty: AstType,
        mem: VarDefinitionSpace,
    ) -> ValueId {
        // update successor blocks
        match &code {
            LCode::Jump(target, _) => {
                // XXX: This is causing us to terminate the loop we are currently generating
                // If it knows about the loop, then it tries to terminate it
                match target {
                    CodeOffset::Value(value_id) => {
                        self.env.add_succ_block(entry_id, (*value_id).into());
                    }
                    CodeOffset::Block(block_id) => {
                        self.env.add_succ_block(entry_id, (*block_id).into());
                    }
                }
            }

            LCode::Branch(_, v_then, v_else) => {
                self.env.add_succ_block(entry_id, (*v_then).into());
                self.env.add_succ_block(entry_id, (*v_else).into());
            }

            LCode::Ternary(_, v_then, v_else) => {
                self.env.add_succ_op(entry_id, *v_then);
                self.env.add_succ_op(entry_id, *v_else);
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
                v_block,
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
                self.add(entry_id, None, *body, b)?;
                self.env.exit_scope();
                Ok(entry_id)
            }
            _ => unreachable!(),
        }
    }

    pub fn add_sequence(
        &mut self,
        entry_id: ValueId,
        maybe_next: Option<ValueId>,
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
                        if let Some(target_value_id) = self.env.resolve_block(key.into()) {
                            // ensure target block exists
                            //let scope = self.env.get_scope_mut(scope_id);
                            //scope.next_block = Some(target_value_id);
                            //current_entry_id = Some(target_value_id);
                            let r = self.add(
                                current_entry_id.unwrap(),
                                Some(target_value_id),
                                expr,
                                b,
                            )?;
                            let v = r.value_id.unwrap();
                            current_is_term = r.is_term;
                            assert_eq!(current_is_term, is_term);
                            //current_entry_id = Some(*self.entries.get(v.0 as usize).unwrap());
                            current_entry_id = Some(r.entry_id);
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
                        let r = self.add(current_entry_id.unwrap(), maybe_next, expr, b)?;
                        // skip noops
                        if let Some(v) = r.value_id {
                            current_is_term = r.is_term;
                            //assert_eq!(current_is_term, is_term);
                            current_entry_id = Some(r.entry_id);
                            //assert_eq!(current_block_id.unwrap(), r.block_id);
                            value_id = Some(v);
                        }
                        println!("r3: {:?}", r);
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
                        current_entry_id = Some(r.entry_id);
                        value_id = Some(v);
                        println!("r4: {:?}", r);
                    }

                    (false, NextSeqState::Empty) => {
                        // end of sequence, with non-terminal node
                        let r = if let Some(v_next) = maybe_next {
                            //let r = if let Some(v_next) = self.env.get_next_block() {
                            assert_eq!(v_next, maybe_next.unwrap());
                            // terminates with a jump to next
                            self.add_with_next(current_entry_id.unwrap(), expr, v_next, b)?
                        } else {
                            // must terminate, unless it's at the static level
                            self.add(current_entry_id.unwrap(), None, expr, b)?
                        };

                        let v = r.value_id.unwrap();
                        current_is_term = r.is_term;
                        current_entry_id = Some(r.entry_id);
                        value_id = Some(v);
                        println!("r2: {:?}", r);

                        // check that this terminates correctly
                        // exception for module level
                        assert!(r.is_term || self.env.static_entry_id() == r.entry_id);
                    }

                    (true, NextSeqState::Other) => {
                        // a terminal, followed by other statements
                        // we create a next block for the statements to follow
                        let name = b.labels.s("next");
                        let v_next =
                            self.push_label(name.into(), expr_span_id, scope_id, &[], &[], b);
                        let r = self.add_with_next(current_entry_id.unwrap(), expr, v_next, b)?;
                        let v = r.value_id.unwrap();
                        current_is_term = r.is_term;
                        println!("r1: {:?}", r);
                        assert!(r.is_term);
                        assert_eq!(current_is_term, is_term);
                        // next block is the next block
                        current_entry_id = Some(r.entry_id);
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
        current_entry_id: ValueId,
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
        let _r = self.add_jump(current_entry_id, new_entry_id, jump_args, span_id, b)?;
        self.env
            .add_succ_block(current_entry_id, new_entry_id.into());
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
        scope.entry_block = Some(new_entry_id);
        self.env.enter_scope(body_scope_id);
        let r1 = self.add_with_next(current_entry_id, *body, v_next, b)?;
        self.env.exit_scope();

        // we return the value of the arg in the next block
        let r2 = AddResult::new(Some(v_expr), false, v_next);
        println!("lambda: {:?}", (&r1, &r2));
        Ok(r2)
    }

    pub fn add_function(
        &mut self,
        current_entry_id: ValueId,
        function_name: StringKey,
        def: Definition,
        span_id: SpanId,
        b: &mut NodeBuilder,
    ) -> Result<AddResult> {
        println!("add_function: {}", b.labels.r(function_name.into()));
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
            //let body_span_id = body.span_id;

            // entry first
            let new_entry_id = self.push_label(
                function_name.into(),
                span_id,
                body_scope_id,
                &[],
                &def.params,
                b,
            );

            // return block
            let name = b.labels.s("ret");
            //let return_type = *def.return_type;
            let args = match &return_type {
                AstType::Unit => vec![],
                _ => vec![return_type.clone()],
            };

            // return block follows entry
            let return_block = self.push_label(name.into(), span_id, body_scope_id, &args, &[], b);
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
            scope.entry_block = Some(new_entry_id);

            // declare function before adding the body, for recursion
            let v_decl = self.push_code_with_name(
                LCode::DeclareFunction(Some(new_entry_id)),
                span_id,
                scope_id,
                current_entry_id,
                ty.clone(),
                VarDefinitionSpace::Static,
                function_name,
            );

            self.env.enter_scope(body_scope_id);
            // next block in body scope
            self.add_with_next(new_entry_id, *body, return_block, b)?;
            self.env.exit_scope();
            self.env.add_succ_static(current_entry_id, new_entry_id);
            Ok(AddResult::new(Some(v_decl), false, current_entry_id))
        } else {
            Ok(AddResult::new(
                Some(self.push_code_with_name(
                    LCode::DeclareFunction(None),
                    span_id,
                    scope_id,
                    current_entry_id,
                    ty.clone(),
                    VarDefinitionSpace::Static,
                    function_name,
                )),
                false,
                current_entry_id,
            ))
        }
    }

    pub fn error(msg: &str, span_id: SpanId, b: &mut NodeBuilder) -> Result<AddResult> {
        let span = b.spans.lookup(span_id);
        b.spans.push_diagnostic(error(msg, span));
        return Err(Error::new(BlockifyError::Invalid));
    }

    pub fn add_loop(
        &mut self,
        entry_id: ValueId,
        v_next: ValueId,
        name: StringKey,
        body: AstNode,
        b: &mut NodeBuilder,
    ) -> Result<AddResult> {
        let span_id = body.span_id;
        let loop_scope_id = self.env.new_scope(ScopeType::Loop);
        let v_loop = self.push_label(name.into(), span_id, loop_scope_id, &[], &[], b);
        self.env.push_loop_blocks(Some(name), v_next, v_loop);
        self.env.enter_scope(loop_scope_id);
        let _ = self.add_with_next(v_loop, body, v_next, b)?;
        self.env.exit_scope();

        // enter loop
        let r = self.add_jump(entry_id, v_loop, vec![], span_id, b)?;
        Ok(AddResult::new(Some(r.value_id.unwrap()), true, v_next))
    }

    pub fn add_jump_by_block(
        &mut self,
        entry_id: ValueId,
        target_block: BlockId,
        jump_args: Vec<AstNode>,
        span_id: SpanId,
        b: &mut NodeBuilder,
    ) -> Result<AddResult> {
        self._add_jump(
            entry_id,
            target_block.into(),
            jump_args.len(),
            jump_args,
            span_id,
            b,
        )
    }

    pub fn add_jump(
        &mut self,
        entry_id: ValueId,
        target_id: ValueId,
        jump_args: Vec<AstNode>,
        span_id: SpanId,
        b: &mut NodeBuilder,
    ) -> Result<AddResult> {
        let target = self.get_code(target_id);
        // make sure we match the arity of the next block
        let args = if let LCode::Label(args, _) = target {
            args
        } else {
            unreachable!();
        };
        self._add_jump(
            entry_id,
            target_id.into(),
            *args as usize,
            jump_args,
            span_id,
            b,
        )
    }

    pub fn _add_jump(
        &mut self,
        entry_id: ValueId,
        target: CodeOffset,
        num_args: usize,
        jump_args: Vec<AstNode>,
        span_id: SpanId,
        b: &mut NodeBuilder,
    ) -> Result<AddResult> {
        let scope_id = self.env.current_scope().unwrap();
        let count = jump_args.len();

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

        if num_args as usize == count {
            let v = self.push_code(
                LCode::Jump(target, num_args as u8),
                span_id,
                scope_id,
                entry_id,
                AstType::Unit,
                VarDefinitionSpace::Reg,
            );
            Ok(AddResult::new(Some(v), true, entry_id))
        } else {
            Self::error(
                &format!("End of block expects {} values", num_args),
                span_id,
                b,
            )
        }
    }

    pub fn add_with_next(
        &mut self,
        entry_id: ValueId,
        node: AstNode,
        v_next: ValueId,
        b: &mut NodeBuilder,
    ) -> Result<AddResult> {
        let span_id = node.span_id;
        let r = self.add(entry_id, Some(v_next), node, b)?;
        let v_block = r.entry_id;
        let v = r.value_id.unwrap();
        let last_entry_id = self.get_entry_id(v);
        //assert_eq!(last_entry_id, r.entry_id);
        let block = self.env.get_block(last_entry_id);

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
        entry_id: ValueId,
        v_func: ValueId,
        args: Vec<Argument>,
        span_id: SpanId,
        b: &mut NodeBuilder,
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
                    b,
                );
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
            return Self::error(
                &format!("Type not function: {}, {:?}", name, ty),
                span_id,
                b,
            );
        }
    }

    pub fn add_noop(&mut self, entry_id: ValueId, span_id: SpanId) -> Result<Option<ValueId>> {
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

    pub fn add(
        &mut self,
        entry_id: ValueId,
        maybe_next: Option<ValueId>,
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

            Ast::Definition(_def) => {
                unreachable!();
                // definition is non-terminal
                //if block_id == self.env.static_block_id() {
                //static function
                //self.add_function(block_id, def, node.span_id, b)
                //} else {
                // lambda block in current scope, called by name
                //let name = def.name.into();
                //let template_id = self.push_template(def);
                //let scope = self.env.get_scope_mut(scope_id);
                //scope.lambdas.insert(name, template_id);
                //Ok(AddResult::new(None, false, block_id))
                //}
            }

            Ast::Call(expr, args, _ret_ty) => match &expr.node {
                // call is an expression, it's non-terminal
                // lambdas should also be non-terminal
                Ast::Identifier(ident) => {
                    let name = b.labels.r(ident.into());
                    if let Some(data) = self.env.resolve(*ident) {
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

                    return Self::error(&format!("Call name not found: {}", name), node.span_id, b);
                }
                _ => {
                    unimplemented!("{:?}", expr.node);
                }
            },

            Ast::BlockStart(name, args) => {
                //Ast::Label(name) => {
                // all blocks should have been forward declared in the sequence
                let value_id = self.env.resolve_block(name.into()).unwrap();
                assert_eq!(0, args.len());

                let block = self.env.get_block(entry_id);
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
                        entry_id,
                        ty,
                        data.mem.clone(),
                    );
                    Ok(AddResult::new(Some(v), false, entry_id))
                } else {
                    let span = b.spans.lookup(node.span_id);
                    b.spans.push_diagnostic(error("Name not found", span));
                    Err(Error::new(BlockifyError::Invalid))
                }
            }

            Ast::Assign(target, expr) => {
                // assign is expression, non-terminal
                let name = match target {
                    AssignTarget::Identifier(name) | AssignTarget::Alloca(name) => name,
                };

                // push the definition into the lambda list
                if let Ast::Definition(def) = expr.node {
                    let template_id = self.push_template(def);
                    let scope = self.env.get_scope_mut(scope_id);
                    scope.lambdas.insert(name.into(), template_id);
                    return Ok(AddResult::new(None, false, entry_id));
                }

                let r = self.add(entry_id, None, *expr, b)?;

                let v_expr = r.value_id.unwrap();
                let v_block = r.entry_id;

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

            Ast::Builtin(id, mut args) => {
                let bi = b.builtins.get_enum(id);
                match bi {
                    Builtin::Import => {
                        let arg = args.pop().unwrap();
                        if let Some(s) = arg.try_string() {
                            self.link.add_library(&s);
                        } else {
                            let span = b.spans.lookup(node.span_id);
                            b.spans.push_diagnostic(error("Expected string", span));
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

                //let v_next = self.env.get_next_block().unwrap();
                let v_next = maybe_next.unwrap();
                assert_eq!(v_next, maybe_next.unwrap());

                let name = b.labels.s("then");
                let then_scope_id = self.env.new_scope(ScopeType::Block);
                let v_then =
                    self.push_label(name.into(), then_expr.span_id, then_scope_id, &[], &[], b);
                self.env.enter_scope(then_scope_id);
                let r = self.add_with_next(v_then, *then_expr, v_next, b)?;
                let _ = r.value_id.unwrap();
                self.env.exit_scope();

                let v_else = if let Some(else_expr) = maybe_else_expr {
                    let name = b.labels.s("else");
                    let else_scope_id = self.env.new_scope(ScopeType::Block);
                    let v_else =
                        self.push_label(name.into(), else_expr.span_id, else_scope_id, &[], &[], b);
                    self.env.enter_scope(else_scope_id);
                    let r = self.add_with_next(v_else, *else_expr, v_next, b)?;
                    let _ = r.value_id.unwrap();
                    self.env.exit_scope();
                    v_else
                } else {
                    v_next
                };

                let span_id = condition.span_id;
                let r = self.add(entry_id, None, *condition, b)?;
                let v = r.value_id.unwrap();
                let code = LCode::Branch(v, v_then, v_else);
                let v = self.push_code(
                    code,
                    span_id,
                    scope_id,
                    r.entry_id,
                    AstType::Unit,
                    VarDefinitionSpace::Reg,
                );

                Ok(AddResult::new(Some(v), true, v_next))
            }

            Ast::Ternary(c, x, y) => {
                // expression, non-terminal
                let condition_span_id = c.span_id;
                let r = self.add(entry_id, None, *c, b)?;
                let v_c = r.value_id.unwrap();

                let then_scope_id = self.env.new_scope(ScopeType::Block);
                let name = b.labels.s("then");
                self.env.enter_scope(then_scope_id);
                let v_then = self.push_label(name.into(), x.span_id, then_scope_id, &[], &[], b);
                let r = self.add(v_then, None, *x, b)?;
                let v_then_result = r.value_id.unwrap();
                self.env.exit_scope();
                let then_ty = self.get_type(v_then_result);

                let else_scope_id = self.env.new_scope(ScopeType::Block);
                let name = b.labels.s("else");
                self.env.enter_scope(else_scope_id);
                let v_else = self.push_label(name.into(), y.span_id, else_scope_id, &[], &[], b);
                let r = self.add(v_else, None, *y, b)?;
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
                    entry_id,
                    then_ty,
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
                    self.add_jump_by_block(entry_id, target_block_id, vec![], node.span_id, b)
                } else {
                    let span = b.spans.lookup(node.span_id);
                    b.spans.push_diagnostic(error(
                        &format!("Block name not found: {}", b.labels.r(label.into())),
                        span,
                    ));
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
                    self.add_jump(entry_id, v_return, args, node.span_id, b)
                } else {
                    let span = b.spans.lookup(node.span_id);
                    b.spans
                        .push_diagnostic(error(&format!("Return without function context"), span));
                    Err(Error::new(BlockifyError::Invalid))
                }
            }

            Ast::Global(name, expr) => match expr.node {
                Ast::Definition(def) => self.add_function(entry_id, name, def, node.span_id, b),
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
                        static_entry_id,
                        ast_ty.clone(),
                        VarDefinitionSpace::Static,
                        b.labels.s(&global_name),
                    );

                    let v = self.push_code_with_name(
                        LCode::Value(v),
                        expr.span_id,
                        scope_id,
                        entry_id,
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
                if let Some(v_next) = self.env.get_loop_next_block(maybe_name) {
                    self.add_jump(entry_id, v_next, vec![], node.span_id, b)
                } else {
                    let span = b.spans.lookup(node.span_id);
                    b.spans
                        .push_diagnostic(error(&format!("Break without loop"), span));
                    Err(Error::new(BlockifyError::Invalid))
                }
            }

            Ast::Continue(maybe_name, args) => {
                // args not implemented yet
                assert_eq!(args.len(), 0);
                // loop up loop blocks by name
                if let Some(v_start) = self.env.get_loop_start_block(maybe_name) {
                    self.add_jump(entry_id, v_start, vec![], node.span_id, b)
                } else {
                    // mismatch name
                    let span = b.spans.lookup(node.span_id);
                    b.spans
                        .push_diagnostic(error(&format!("Continue without loop"), span));
                    Err(Error::new(BlockifyError::Invalid))
                }
            }

            Ast::Error => {
                let span = b.spans.lookup(node.span_id);
                b.spans.push_diagnostic(error(&format!("AST Error"), span));
                Err(Error::new(BlockifyError::Invalid))
            }

            _ => unimplemented!("{:?}", node.node),
        }
    }
}
