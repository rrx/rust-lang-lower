use anyhow::Error;
use anyhow::Result;
use indexmap::IndexMap;
use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use petgraph::visit::Bfs;
use std::collections::HashMap;
use std::collections::VecDeque;

use lower::{
    ast::AssignTarget,
    ast::Builtin,
    //op,
    Argument,
    Ast,
    AstNode,
    AstType,
    BinaryOperation,
    Definition,
    Diagnostic,
    Diagnostics,
    Extra,
    Label,
    LinkOptions,
    Literal,
    NodeBuilder,
    ParameterNode,
    ParseError,
    Span,
    StringKey,
    StringLabel,
    UnaryOperation,
    //Definition,
    VarDefinitionSpace,
};

use crate::{Environment, ScopeId, ScopeType, Successor, ValueId};

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
    Arg(u8),            // get the value of a positional arg
    NamedParameter(u8), // get the value of a positional arg
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
    pub fn get<E: Extra>(node: &AstNode<E>, next_node: Option<&AstNode<E>>) -> (bool, Self) {
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
    loop_stack: Vec<LoopLayer>,

    // other
    pub(crate) env: Environment,
    // sparse names
    pub(crate) names: IndexMap<ValueId, StringLabel>,
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

            names: IndexMap::new(),
            env: Environment::new(),
            link: LinkOptions::new(),
        }
    }

    pub fn shared_libraries(&self) -> Vec<String> {
        self.link.shared_libraries()
    }

    pub fn block_name(&mut self, scope_id: ScopeId, name: StringLabel, v: ValueId) {
        self.env.get_scope_mut(scope_id).labels.insert(name, v);
    }

    pub fn get_code(&self, value_id: ValueId) -> &LCode {
        self.code.get(value_id.0 as usize).unwrap()
    }

    pub fn get_block_id(&self, value_id: ValueId) -> ValueId {
        *self.entries.get(value_id.0 as usize).unwrap()
    }

    pub fn get_scope_id(&self, value_id: ValueId) -> ScopeId {
        *self.scopes.get(value_id.0 as usize).unwrap()
    }

    pub fn get_next(&self, value_id: ValueId) -> Option<ValueId> {
        let next = self.next_pos[value_id.0 as usize];
        if next != value_id {
            Some(next)
        } else {
            None
        }
    }

    pub fn code_to_string<E: Extra>(&self, v: ValueId, b: &NodeBuilder<E>) -> String {
        let offset = v.0 as usize;
        let code = self.code.get(offset).unwrap();
        match code {
            LCode::Declare => {
                format!(
                    "declare {}: {:?}",
                    b.resolve_label(*self.names.get(&v).unwrap()),
                    self.get_type(v)
                )
            }
            LCode::DeclareFunction(maybe_entry) => {
                let name = b.resolve_label(*self.names.get(&v).unwrap());
                if let Some(entry_id) = maybe_entry {
                    format!("declare_function({},{})", name, entry_id.0)
                } else {
                    format!("declare_function({})", name)
                }
            }
            LCode::Label(args, kwargs) => {
                if let Some(key) = self.names.get(&v) {
                    format!("label({}, {}, {})", b.resolve_label(*key), args, kwargs,)
                } else {
                    format!("label(-, {}, {})", args, kwargs,)
                }
            }
            LCode::Goto(block_id) => {
                format!("goto({})", b.r(*block_id))
            }
            LCode::Jump(value_id, args) => {
                format!("jump({}, {})", value_id.0, args,)
            }

            LCode::NamedParameter(pos) => {
                let key = self.names.get(&v).unwrap();
                format!("namedparam({}, {})", pos, b.resolve_label(*key))
            }

            LCode::Const(Literal::String(s)) => {
                format!("String({})", s)
            }

            LCode::Ternary(c, x, y) => {
                format!("Ternary({},{},{})", c.0, x.0, y.0)
            }

            LCode::Branch(c, x, y) => {
                format!("Branch({},{},{})", c.0, x.0, y.0)
            }

            _ => {
                format!("{:?}", code)
            }
        }
    }

    pub fn dump_codes<E: Extra>(&self, b: &NodeBuilder<E>, filter_block_id: Option<ValueId>) {
        use tabled::{
            settings::{object::Rows, Border, Style},
            Table, Tabled,
        };

        #[derive(Tabled)]
        struct CodeRow<'a> {
            pos: usize,
            next: usize,
            prev: usize,
            value: String,
            ty: &'a AstType,
            mem: String,
            name: String,
            scope_id: usize,
            block_id: usize,
            term: bool,
        }

        if filter_block_id.is_none() {
            let mut out = vec![];
            let mut labels = vec![];
            let iter = LCodeIterator::new(self);
            for (i, value_id) in iter.enumerate() {
                let pos = value_id.0 as usize;
                let code = self.code.get(pos).unwrap();
                let ty = self.types.get(pos).unwrap();
                let mem = self.mem.get(pos).unwrap();
                let next = self.next_pos[pos].0 as usize;
                let scope_id = self.scopes[pos];
                let block_id = self.entries[pos];

                if code.is_start() {
                    labels.push(i + 1);
                }

                out.push(CodeRow {
                    pos,
                    next,
                    prev: self.prev_pos[pos].0 as usize,
                    value: self.code_to_string(value_id, b),
                    ty,
                    mem: format!("{:?}", mem),
                    name: self
                        .names
                        .get(&value_id)
                        .map(|key| b.resolve_label(*key))
                        .unwrap_or("".to_string())
                        .to_string(),
                    scope_id: scope_id.0 as usize,
                    block_id: block_id.0 as usize,
                    term: code.is_term(),
                });
            }

            let mut t = Table::new(out);

            t.with(Style::sharp());

            for i in labels {
                let rows = Rows::single(i);
                t.modify(rows, Border::new().set_top('-'));
            }
            let s = t.to_string();
            println!("{}", s);
        }

        let mut out = vec![];
        let mut pos = 0;
        loop {
            let code = self.code.get(pos).unwrap();
            let ty = self.types.get(pos).unwrap();
            let mem = self.mem.get(pos).unwrap();
            let next = self.next_pos[pos].0 as usize;
            let scope_id = self.scopes[pos];
            let block_id = self.entries[pos];
            let v = ValueId(pos as u32);
            let mut display = true;
            if let Some(filter_block_id) = filter_block_id {
                if filter_block_id != block_id {
                    display = false;
                }
            }

            if display {
                out.push(CodeRow {
                    pos,
                    next,
                    prev: self.prev_pos[pos].0 as usize,
                    value: self.code_to_string(v, b),
                    ty,
                    mem: format!("{:?}", mem),
                    name: self
                        .names
                        .get(&v)
                        .map(|key| b.resolve_label(*key))
                        .unwrap_or("".to_string())
                        .to_string(),
                    scope_id: scope_id.0 as usize,
                    block_id: block_id.0 as usize,
                    term: code.is_term(),
                });
            }

            pos += 1;
            if pos == self.code.len() {
                break;
            }
        }
        println!("{}", Table::new(out).with(Style::sharp()).to_string());
    }

    pub fn dump<E: Extra>(&self, b: &NodeBuilder<E>) {
        self.dump_codes(b, None);
        self.env.dump(b);

        for (block_id, block) in self.env.blocks.iter() {
            println!("block({:?}, {:?})", block_id, block);
            self.dump_codes(b, Some(*block_id));
        }
    }

    pub fn push_code_with_name(
        &mut self,
        code: LCode,
        scope_id: ScopeId,
        block_id: ValueId,
        ty: AstType,
        mem: VarDefinitionSpace,
        name: StringKey,
    ) -> ValueId {
        let value_id = self.push_code(code, scope_id, block_id, ty.clone(), mem);
        self.env.scope_define(scope_id, name, value_id, ty, mem);
        self.names.insert(value_id, name.into());
        value_id
    }

    pub fn push_code_new_block(&mut self, code: LCode, scope_id: ScopeId, ty: AstType) -> ValueId {
        let block_id = self._push_code(code, scope_id, ValueId(0), ty, VarDefinitionSpace::Reg);
        self.env.new_block(block_id, scope_id);
        self.entries[block_id.0 as usize] = block_id;
        self._update_code(block_id, block_id);
        block_id
    }

    pub fn push_code(
        &mut self,
        code: LCode,
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

        let v = self._push_code(code, scope_id, block_id, ty, mem);
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
        v
    }

    pub fn push_label<E: Extra>(
        &mut self,
        name: StringLabel,
        scope_id: ScopeId,
        args: &[AstType],
        kwargs: &[ParameterNode<E>],
    ) -> ValueId {
        let block_id = self.push_code_new_block(
            LCode::Label(args.len() as u8, kwargs.len() as u8),
            scope_id,
            AstType::Unit,
        );
        self.names.insert(block_id, name);
        self.block_name(scope_id, name, block_id);
        let block = self.env.get_block_mut(block_id);
        block.last_value = Some(block_id);
        for (i, p) in kwargs.iter().enumerate() {
            let v = self.push_code(
                LCode::NamedParameter(i as u8),
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

    pub fn resolve_block_label<E: Extra>(&self, k: ValueId, b: &NodeBuilder<E>) -> String {
        if let Some(key) = self.names.get(&k) {
            b.resolve_label(*key).to_string()
        } else {
            format!("b{}", k.0)
        }
    }

    pub fn get_type(&self, v: ValueId) -> AstType {
        self.types.get(v.0 as usize).unwrap().clone()
    }

    pub fn get_name(&self, v: ValueId) -> StringLabel {
        self.names.get(&v).unwrap().clone()
    }

    pub fn build_module<E: Extra>(
        &mut self,
        node: AstNode<E>,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<ValueId> {
        match node.node {
            Ast::Module(name, body) => {
                let static_scope = self.env.new_scope(ScopeType::Static);
                let block_id = self.push_label::<E>(name.into(), static_scope, &[], &[]);
                self.env.enter_scope(static_scope);
                self.add(block_id, *body, b, d)?;
                self.env.exit_scope();
                //self.build_edges()?;
                Ok(block_id)
            }
            _ => unreachable!(),
        }
    }

    /*
    pub fn build_edges(&mut self) -> Result<()> {
        for (i, code) in self.code.iter().enumerate() {
            match code {
                LCode::Ternary(_, x, y) => {
                    //let block_id = self.entries[i];
                    //self.env.add_succ_op(block_id, *x);
                    //self.env.add_succ_op(block_id, *y);
                }

                LCode::Branch(_, x, y) => {
                    //let block_id = self.entries[i];
                    //self.env.add_succ_block(block_id, *x);
                    //self.env.add_succ_block(block_id, *y);
                }

                LCode::DeclareFunction(Some(_entry_id)) => {
                    //let decl_block_id = self.entries[i];
                    //self.env.add_succ_static(decl_block_id, *entry_id);
                }

                LCode::Jump(target_id, _) => {
                    let block_id = self.entries[i];
                    self.env.add_succ_block(block_id, *target_id);
                }

                LCode::Goto(_key) => {
                    unreachable!();
                }
                _ => (),
            }
        }
        Ok(())
    }
                */

    pub fn emit_sequence<E: Extra>(
        &mut self,
        block_id: ValueId,
        node: AstNode<E>,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<Option<ValueId>> {
        let scope_id = self.env.current_scope().unwrap();
        // flatten
        let exprs = node.to_vec();

        // generate blocks for all predefined labels
        // this needs to be done first as a forward declaration
        for expr in exprs.iter() {
            if let Ast::Label(name) = &expr.node {
                let _ = self.push_label::<E>(name.into(), scope_id, &[], &[]);
            }
        }

        let mut value_id = None;
        let mut current_block_id = Some(block_id);
        let mut iter = exprs.into_iter().peekable();
        loop {
            if let Some(expr) = iter.next() {
                //let span = expr.extra.get_span();
                let (is_term, next_state) = NextSeqState::get(&expr, iter.peek());
                match (is_term, next_state) {
                    (true, NextSeqState::NextLabel(key)) => {
                        if let Some(_target_value_id) = self.env.resolve_block(key.into()) {
                            //let scope = self.env.get_scope_mut(scope_id);
                            //scope.next_block = Some(target_value_id);
                            //current_block_id = Some(target_value_id);
                        } else {
                            unreachable!()
                        }
                        let v = self.add(current_block_id.unwrap(), expr, b, d)?.unwrap();
                        current_block_id = Some(*self.entries.get(v.0 as usize).unwrap());
                        value_id = Some(v);
                    }

                    (false, NextSeqState::NextLabel(_key)) => {
                        unreachable!();
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

                    (true, NextSeqState::Empty) => {
                        let v = self.add(current_block_id.unwrap(), expr, b, d)?.unwrap();
                        current_block_id = Some(*self.entries.get(v.0 as usize).unwrap());
                        value_id = Some(v);
                    }

                    (false, NextSeqState::Other) => {
                        if let Some(v) = self.add(current_block_id.unwrap(), expr, b, d)? {
                            current_block_id = Some(*self.entries.get(v.0 as usize).unwrap());
                            value_id = Some(v);
                        }
                    }

                    (false, NextSeqState::Empty) => {
                        //println!("{:?}", (&expr, &self.env.stack));
                        //self.env.dump(b);
                        // end of sequence, with non-terminal node
                        // implicit jump to next
                        //let target_value_id = self.env.pop_next_block().unwrap();
                        /*
                        if let Some(target_value_id) = self.env.get_next_block() {
                            let v = self.add(current_block_id.unwrap(), expr, b, d)?.unwrap();
                            current_block_id = Some(*self.entries.get(v.0 as usize).unwrap());
                            d.push_diagnostic(error(
                                    &format!("Implicit Jump required: {:?}", (block_id, v, target_value_id, current_block_id, &self.env.stack)),
                                    span,
                                    ));
                            value_id = Some(v);

                            //return Err(Error::new(ParseError::Invalid));
                            //unreachable!();
                            /*
                            let code = LCode::Jump(target_value_id, 0);
                            self.push_code(
                                code,
                                scope_id,
                                current_block_id.unwrap(),
                                AstType::Unit,
                                VarDefinitionSpace::Static,
                            );
                            current_block_id = Some(target_value_id);
                            */
                        } else {
                        */
                        let v = self.add(current_block_id.unwrap(), expr, b, d)?.unwrap();
                        current_block_id = Some(*self.entries.get(v.0 as usize).unwrap());
                        value_id = Some(v);
                        //}
                    }

                    (true, NextSeqState::Other) => {
                        /*
                        let v = self.add(current_block_id.unwrap(), expr, b, d)?.unwrap();
                        current_block_id = Some(*self.entries.get(v.0 as usize).unwrap());
                        value_id = Some(v);
                        */

                        let name = b.s("next");
                        let v_next = self.push_label::<E>(name.into(), scope_id, &[], &[]);
                        self.env.push_next_block(v_next);
                        let v = self.add(current_block_id.unwrap(), expr, b, d)?.unwrap();
                        self.env.pop_next_block();
                        // next block is the next block
                        current_block_id = Some(v_next);
                        value_id = Some(v);
                    }
                }
            } else {
                break;
            }
        }

        Ok(value_id)
    }

    pub fn emit_function<E: Extra>(
        &mut self,
        block_id: ValueId,
        def: Definition<E>,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<Option<ValueId>> {
        let scope_id = self.env.current_scope().unwrap();

        let params = def.params.iter().map(|p| p.ty.clone()).collect();
        let ty = AstType::Func(params, def.return_type.clone());

        if let Some(body) = def.body {
            let body_scope_id = self.env.new_scope(ScopeType::Function);

            // entry first
            let entry_id = self.push_label(def.name.into(), body_scope_id, &[], &def.params);

            // return block
            let name = b.s("ret");
            let return_type = *def.return_type;
            let args = match &return_type {
                AstType::Unit => vec![],
                _ => vec![return_type.clone()],
            };

            // return block follows entry
            let return_block = self.push_label::<E>(name.into(), body_scope_id, &args, &[]);
            let v_args = args
                .iter()
                .enumerate()
                .map(|(i, _arg)| {
                    let v_arg = self.push_code(
                        LCode::Arg(i as u8),
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
                    body_scope_id,
                    return_block,
                    return_type.clone(),
                    VarDefinitionSpace::Arg,
                );
            }

            self.push_code(
                LCode::Return(v_args.len() as u8),
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
                scope_id,
                block_id,
                ty.clone(),
                VarDefinitionSpace::Static,
                def.name,
            );

            self.env.enter_scope(body_scope_id);
            // next block in body scope
            self.env.push_next_block(return_block);
            self.add(entry_id, *body, b, d)?;
            self.env.pop_next_block().unwrap();
            self.env.exit_scope();
            self.env.add_succ_static(block_id, entry_id);
            Ok(Some(v_decl))
        } else {
            Ok(Some(self.push_code_with_name(
                LCode::DeclareFunction(None),
                scope_id,
                block_id,
                ty.clone(),
                VarDefinitionSpace::Static,
                def.name,
            )))
        }
    }

    pub fn error<E: Extra>(msg: &str, extra: &E, d: &mut Diagnostics) -> Result<Option<ValueId>> {
        d.push_diagnostic(error(msg, extra.get_span()));
        return Err(Error::new(ParseError::Invalid));
    }

    pub fn add_loop<E: Extra>(
        &mut self,
        block_id: ValueId,
        name: StringKey,
        body: AstNode<E>,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<Option<ValueId>> {
        let v_next = self.env.get_next_block().unwrap();

        let loop_scope_id = self.env.new_scope(ScopeType::Loop);
        let v_loop = self.push_label::<E>(name.into(), loop_scope_id, &[], &[]);
        self.env.push_loop_blocks(Some(name), v_next, v_loop);
        self.env.enter_scope(loop_scope_id);
        let _ = self.add_with_next(v_loop, body, v_next, b, d)?;
        self.env.exit_scope();

        // enter loop
        let code = LCode::Jump(v_loop, 0);
        let scope_id = self.env.current_scope().unwrap();
        let v = self.push_code(
            code,
            scope_id,
            block_id,
            AstType::Unit,
            VarDefinitionSpace::Reg,
        );

        Ok(Some(v))
    }

    pub fn add_with_next<E: Extra>(
        &mut self,
        block_id: ValueId,
        node: AstNode<E>,
        v_next: ValueId,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<Option<ValueId>> {
        self.env.push_next_block(v_next);
        let result = self.add(block_id, node, b, d)?.unwrap();
        self.env.pop_next_block();
        let last_block_id = self.get_block_id(result);
        let block = self.env.get_block(last_block_id);
        println!(
            "addnext: {:?}",
            (block_id, last_block_id, block.last_value, block.terminator)
        );
        if !block.has_term() {
            let scope_id = self.env.current_scope().unwrap();
            self.push_code(
                LCode::Jump(v_next, 0),
                scope_id,
                block_id,
                AstType::Unit,
                VarDefinitionSpace::Reg,
            );
        }

        Ok(Some(result))
    }

    pub fn add<E: Extra>(
        &mut self,
        block_id: ValueId,
        node: AstNode<E>,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<Option<ValueId>> {
        let scope_id = self.env.current_scope().unwrap();
        match node.node {
            Ast::Module(_, _) => {
                // nested modules are not yet implemented
                unimplemented!()
            }

            Ast::Sequence(ref _exprs) => self.emit_sequence(block_id, node, b, d),

            Ast::Definition(def) => self.emit_function(block_id, def, b, d),

            Ast::Call(expr, args, _ret_ty) => {
                let (v_func, ty, f_args, name) = match &expr.node {
                    Ast::Identifier(ident) => {
                        let name = b.resolve_label(ident.into());
                        if let Some(data) = self.env.resolve(*ident) {
                            if let AstType::Func(f_args, _) = data.ty.clone() {
                                (data.value_id, data.ty.clone(), f_args, name)
                            } else {
                                return Self::error(
                                    &format!("Type not function: {}, {:?}", name, data.ty),
                                    &node.extra,
                                    d,
                                );
                            }
                        } else {
                            return Self::error(
                                &format!("Call name not found: {}", name),
                                &node.extra,
                                d,
                            );
                        }
                    }
                    _ => {
                        unimplemented!("{:?}", expr.node);
                    }
                };

                if let AstType::Func(func_arg_types, ret) = &ty {
                    if f_args.len() != args.len() {
                        return Self::error(
                            &format!("Call arity mismatch: {}", name),
                            &node.extra,
                            d,
                        );
                    }

                    let args_size = args.len() as u8;
                    let mut values = vec![];
                    for (a, ty) in args.into_iter().zip(func_arg_types.iter()) {
                        match a {
                            Argument::Positional(expr) => {
                                let v = self.add(block_id, *expr, b, d)?.unwrap();
                                values.push((LCode::Value(v), ty.clone()));
                            }
                        }
                    }
                    for (code, ty) in values {
                        self.push_code(code, scope_id, block_id, ty, VarDefinitionSpace::Reg);
                    }
                    Ok(Some(self.push_code(
                        LCode::Call(v_func, args_size, 0),
                        scope_id,
                        block_id,
                        *ret.clone(),
                        VarDefinitionSpace::Reg,
                    )))
                } else {
                    unimplemented!("calling non function type: {:?}", ty);
                }
            }

            Ast::Label(name) => {
                // all blocks should have been forward declared in the sequence
                let value_id = self.env.resolve_block(name.into()).unwrap();

                let block = self.env.get_block(block_id);
                if let Some(last_value) = block.last_value {
                    // check to ensure that the previous block was terminated
                    let code = self.code.get(last_value.0 as usize).unwrap();
                    if !code.is_term() {
                        unreachable!();
                        /*
                        self.push_code(
                            LCode::Jump(value_id, 0),
                            scope_id,
                            block_id,
                            AstType::Unit,
                            VarDefinitionSpace::Reg,
                        );
                        */
                    }
                }

                Ok(Some(value_id))
            }

            Ast::Identifier(key) => {
                if let Some(data) = self.env.resolve(key) {
                    let ty = data.ty.clone();
                    let code = if let VarDefinitionSpace::Arg = data.mem {
                        LCode::Value(data.value_id)
                    } else {
                        LCode::Load(data.value_id)
                    };
                    Ok(Some(self.push_code(
                        code,
                        scope_id,
                        block_id,
                        ty,
                        data.mem.clone(),
                    )))
                } else {
                    d.push_diagnostic(error("Name not found", node.extra.get_span()));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            Ast::Assign(target, expr) => {
                let name = match target {
                    AssignTarget::Identifier(name) | AssignTarget::Alloca(name) => name,
                };

                //println!("assign: {}, {:?}", b.r(name), (block_id));

                let v_expr = self.add(block_id, *expr, b, d)?.unwrap();
                let expr_ty = self.get_type(v_expr);

                let v_decl = if let Some(data) = self.env.resolve(name) {
                    assert_eq!(data.ty, expr_ty);
                    data.value_id
                } else {
                    self.push_code_with_name(
                        LCode::Declare,
                        scope_id,
                        block_id,
                        expr_ty.clone(),
                        VarDefinitionSpace::Stack,
                        name,
                    )
                };

                let index = self.push_code(
                    LCode::Store(v_decl, v_expr),
                    scope_id,
                    block_id,
                    AstType::Unit,
                    VarDefinitionSpace::Stack,
                );
                Ok(Some(index))
            }

            Ast::Builtin(bi, mut args) => match bi {
                Builtin::Import => {
                    let arg = args.pop().unwrap();
                    if let Some(s) = arg.try_string() {
                        self.link.add_library(&s);
                    } else {
                        d.push_diagnostic(error("Expected string", node.extra.get_span()));
                    }
                    Ok(None)
                }
                _ => {
                    let _ty = bi.get_return_type();
                    let args_size = args.len();
                    assert_eq!(args_size, bi.arity());
                    let mut values = vec![];
                    for a in args.into_iter() {
                        let Argument::Positional(expr) = a;
                        let v = self.add(block_id, *expr, b, d)?.unwrap();
                        let ty = self.get_type(v);
                        values.push((v, ty));
                    }

                    for (v, ty) in values {
                        self.push_code(
                            LCode::Value(v),
                            scope_id,
                            block_id,
                            ty,
                            VarDefinitionSpace::Reg,
                        );
                    }

                    let ty = bi.get_return_type();
                    let value_id = self.push_code(
                        LCode::Builtin(bi, args_size as u8, 0),
                        scope_id,
                        block_id,
                        ty,
                        VarDefinitionSpace::Reg,
                    );
                    Ok(Some(value_id))
                }
            },

            Ast::Literal(lit) => {
                let ty: AstType = lit.clone().into();
                Ok(Some(self.push_code(
                    LCode::Const(lit),
                    scope_id,
                    block_id,
                    ty,
                    VarDefinitionSpace::Reg,
                )))
            }

            Ast::UnaryOp(op, x) => {
                let vx = self.add(block_id, *x, b, d)?.unwrap();
                let code = LCode::Op1(op, vx);
                Ok(Some(self.push_code(
                    code,
                    scope_id,
                    block_id,
                    self.get_type(vx),
                    VarDefinitionSpace::Reg,
                )))
            }

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
                let v_next = self.env.get_next_block().unwrap();

                let name = b.s("then");
                let then_scope_id = self.env.new_scope(ScopeType::Block);
                let v_then = self.push_label::<E>(name.into(), then_scope_id, &[], &[]);
                self.env.enter_scope(then_scope_id);
                let _ = self.add_with_next(v_then, *then_expr, v_next, b, d)?;
                self.env.exit_scope();
                //self.ensure_next_in_cfg(then_scope_id, v_then, v_next, b);

                let v_else = if let Some(else_expr) = maybe_else_expr {
                    let name = b.s("else");
                    let else_scope_id = self.env.new_scope(ScopeType::Block);
                    let v_else = self.push_label::<E>(name.into(), else_scope_id, &[], &[]);
                    self.env.enter_scope(else_scope_id);
                    let _v_else_result = self
                        .add_with_next(v_else, *else_expr, v_next, b, d)?
                        .unwrap();
                    self.env.exit_scope();
                    //self.ensure_next_in_cfg(else_scope_id, v_else, v_next, b);
                    v_else
                } else {
                    v_next
                };

                let v = self.add(block_id, *condition, b, d)?.unwrap();
                let code = LCode::Branch(v, v_then, v_else);
                self.push_code(
                    code,
                    scope_id,
                    block_id,
                    AstType::Unit,
                    VarDefinitionSpace::Reg,
                );
                self.env.add_succ_block(block_id, v_then);
                self.env.add_succ_block(block_id, v_else);

                Ok(Some(v))
            }

            Ast::Ternary(c, x, y) => {
                let v_c = self.add(block_id, *c, b, d)?.unwrap();

                let then_scope_id = self.env.new_scope(ScopeType::Block);
                let name = b.s("then");
                self.env.enter_scope(then_scope_id);
                let v_then = self.push_label::<E>(name.into(), then_scope_id, &[], &[]);
                let v_then_result = self.add(v_then, *x, b, d)?.unwrap();
                self.env.exit_scope();
                let then_ty = self.get_type(v_then_result);

                let else_scope_id = self.env.new_scope(ScopeType::Block);
                let name = b.s("else");
                self.env.enter_scope(else_scope_id);
                let v_else = self.push_label::<E>(name.into(), else_scope_id, &[], &[]);
                let v_else_result = self.add(v_else, *y, b, d)?.unwrap();
                self.env.exit_scope();
                let else_ty = self.get_type(v_else_result);
                assert_eq!(then_ty, else_ty);

                // TODO: we need to ensure that the cfg terminates with a yield

                let code = LCode::Ternary(v_c, v_then, v_else);

                Ok(Some(self.push_code(
                    code,
                    scope_id,
                    block_id,
                    then_ty,
                    VarDefinitionSpace::Reg,
                )))
            }

            Ast::BinaryOp(op, x, y) => {
                let vx = self.add(block_id, *x, b, d)?.unwrap();
                let vy = self.add(block_id, *y, b, d)?.unwrap();
                let code = LCode::Op2(op.node, vx, vy);
                let ty = self.get_type(vx);
                Ok(Some(self.push_code(
                    code,
                    scope_id,
                    block_id,
                    ty,
                    VarDefinitionSpace::Reg,
                )))
            }

            Ast::Goto(label) => {
                let code = if let Some(target_value_id) = self.env.resolve_block(label.into()) {
                    LCode::Jump(target_value_id, 0)
                } else {
                    d.push_diagnostic(error(
                        &format!("Block name not found: {}", b.r(label)),
                        node.extra.get_span(),
                    ));
                    LCode::Goto(label)
                };
                let jump_value = self.push_code(
                    code,
                    scope_id,
                    block_id,
                    AstType::Unit,
                    VarDefinitionSpace::Reg,
                );
                Ok(Some(jump_value))
            }

            Ast::Return(maybe_expr) => {
                if let Some(v_return) = self.env.resolve_return_block() {
                    let count = if maybe_expr.is_some() { 1 } else { 0 };

                    let maybe_ret_value = if let Some(expr) = maybe_expr {
                        let expr_value_id = self.add(block_id, *expr, b, d)?.unwrap();
                        Some(expr_value_id)
                    } else {
                        None
                    };

                    // args
                    if let Some(ret_value) = maybe_ret_value {
                        self.push_code(
                            LCode::Value(ret_value),
                            scope_id,
                            block_id,
                            self.get_type(ret_value),
                            VarDefinitionSpace::Reg,
                        );
                    }

                    let code = LCode::Jump(v_return, count);
                    let v = self.push_code(
                        code,
                        scope_id,
                        block_id,
                        AstType::Unit,
                        VarDefinitionSpace::Reg,
                    );
                    Ok(Some(v))
                } else {
                    d.push_diagnostic(error(
                        &format!("Return without function context"),
                        node.extra.get_span(),
                    ));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            Ast::Global(name, expr) => {
                if let Ast::Literal(lit) = expr.node {
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
                        scope_id,
                        block_id,
                        ast_ty,
                        VarDefinitionSpace::Static,
                        b.s(&global_name),
                    );
                    Ok(Some(v))
                } else {
                    unreachable!()
                }
            }

            Ast::Loop(name, body) => self.add_loop(block_id, name, *body, b, d),

            Ast::Break(maybe_name, args) => {
                // args not implemented yet
                assert_eq!(args.len(), 0);
                if let Some(v_next) = self.env.get_loop_next_block(maybe_name) {
                    let code = LCode::Jump(v_next, 0);
                    let v = self.push_code(
                        code,
                        scope_id,
                        block_id,
                        AstType::Unit,
                        VarDefinitionSpace::Reg,
                    );
                    Ok(Some(v))
                } else {
                    d.push_diagnostic(error(&format!("Break without loop"), node.extra.get_span()));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            Ast::Continue(maybe_name, args) => {
                // args not implemented yet
                assert_eq!(args.len(), 0);
                if let Some(v_start) = self.env.get_loop_start_block(maybe_name) {
                    let code = LCode::Jump(v_start, 0);
                    let v = self.push_code(
                        code,
                        scope_id,
                        block_id,
                        AstType::Unit,
                        VarDefinitionSpace::Reg,
                    );
                    Ok(Some(v))
                } else {
                    // mismatch name
                    d.push_diagnostic(error(
                        &format!("Continue without loop"),
                        node.extra.get_span(),
                    ));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            Ast::Error => {
                d.push_diagnostic(error(&format!("AST Error"), node.extra.get_span()));
                Err(Error::new(ParseError::Invalid))
            }

            _ => unimplemented!("{:?}", node.node),
        }
    }

    /*
    pub fn ensure_next_in_cfg<E: Extra>(
        &mut self,
        scope_id: ScopeId,
        v_block: ValueId,
        v_next: ValueId,
        b: &NodeBuilder<E>,
    ) {
        let leafs = self
            .get_graph(v_block, Some(Successor::BlockScope), b)
            .leafs(v_block);
        println!("leafs: {:?}", (v_block, v_next, &leafs));
        for block_id in leafs {
            let last_value = self.env.get_block(block_id).last_value.unwrap();
            let last_code = self.get_code(last_value);

            // TODO: this shouldn't happen
            if block_id == v_next {
                continue;
            }

            // TODO: This is terminating blocks that haven't been completed yet
            // because we are adding the successors in, it's following the loops
            // and trying to terminate the loop it's trying to generate.

            if !last_code.is_term() {
                //assert!(false);
                //println!("adding jump: {:?}", (block_id, v_next));
                self.push_code(
                    LCode::Jump(v_next, 0),
                    scope_id,
                    block_id,
                    AstType::Unit,
                    VarDefinitionSpace::Reg,
                );
            }
        }
    }
    */

    /*
    pub fn save_graph<E: Extra>(&self, filename: &str, b: &NodeBuilder<E>) {
        use petgraph::dot::{Config, Dot};
        #[derive(Debug)]
        enum Shape {
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
        struct Node {
            ty: Shape,
            name: String,
            block_id: ValueId,
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

        let mut g: DiGraph<Node, ()> = DiGraph::new();
        let mut ids = HashMap::new();
        let mut last = HashMap::new();
        for (offset, code) in self.code.iter().enumerate() {
            let go = match code {
                LCode::Jump(_, _) => true,
                LCode::Branch(_, _, _) => true,
                LCode::Ternary(_, _, _) => true,
                LCode::Label(_, _) => true,
                LCode::DeclareFunction(Some(_)) => true,
                LCode::Return(_) => true,
                _ => false,
            };

            if go {
                let v = ValueId(offset as u32);
                let name = self.code_to_string(v, b);
                let id = g.add_node(Node::new_block(name, v));
                ids.insert(v, id);
            }
        }

        for (offset, code) in self.code.iter().enumerate() {
            let v = ValueId(offset as u32);
            let v_block = self.entries[offset];
            match code {
                LCode::Label(_, _) => {
                    last.insert(v, v);
                }
                LCode::Return(_) => {
                    g.add_edge(*ids.get(&v_block).unwrap(), *ids.get(&v).unwrap(), ());
                }
                LCode::Jump(target_id, _) | LCode::DeclareFunction(Some(target_id)) => {
                    g.add_edge(*ids.get(&v_block).unwrap(), *ids.get(&v).unwrap(), ());
                    g.add_edge(*ids.get(&v).unwrap(), *ids.get(&target_id).unwrap(), ());
                }

                LCode::Branch(_, x, y) | LCode::Ternary(_, x, y) => {
                    g.add_edge(*ids.get(&v_block).unwrap(), *ids.get(&v).unwrap(), ());
                    g.add_edge(*ids.get(&v).unwrap(), *ids.get(&x).unwrap(), ());
                    g.add_edge(*ids.get(&v).unwrap(), *ids.get(&y).unwrap(), ());
                }
                _ => (),
            }
        }

        let s = format!(
            "{:?}",
            Dot::with_attr_getters(
                &g,
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
    */

    pub fn save_graph<E: Extra>(&self, filename: &str, b: &NodeBuilder<E>) {
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

pub struct LCodeIterator<'a> {
    blockify: &'a Blockify,
    blocks: Vec<ValueId>,
    values: VecDeque<ValueId>,
}

impl<'a> LCodeIterator<'a> {
    pub fn new(blockify: &'a Blockify) -> Self {
        let blocks = blockify.env.blocks.keys().rev().cloned().collect();
        Self {
            blockify,
            blocks,
            values: VecDeque::new(),
        }
    }
}

impl<'a> Iterator for LCodeIterator<'a> {
    type Item = ValueId;

    fn next(&mut self) -> Option<Self::Item> {
        if self.values.len() == 0 {
            if self.blocks.len() == 0 {
                return None;
            }

            let block_id = self.blocks.pop().unwrap();
            let mut current = block_id;
            self.values.push_back(block_id);
            loop {
                if let Some(next) = self.blockify.get_next(current) {
                    self.values.push_back(next);
                    current = next;
                } else {
                    break;
                }
            }
        }
        self.values.pop_front()
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

impl Blockify {
    pub fn get_cfg<E: Extra>(&self, block_id: ValueId, b: &NodeBuilder<E>) -> CFG {
        self.get_graph(block_id, Some(Successor::BlockScope), b)
    }

    pub fn get_graph<E: Extra>(
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
