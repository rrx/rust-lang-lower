use anyhow::Error;
use anyhow::Result;
use indexmap::IndexMap;
use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use std::collections::HashMap;
use tabled::{Table, Tabled};

use lower::{
    ast::AssignTarget,
    ast::Builtin,
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
    Literal,
    NodeBuilder,
    ParameterNode,
    ParseError,
    Span,
    StringKey,
    StringLabel,
    UnaryOperation,
    //Definition,
    //VarDefinitionSpace,
};

use crate::{BlockId, Environment, ScopeId, ValueId};

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
    Declare,
    DeclareFunction(Option<ValueId>), // optional entry block
    Value(ValueId),
    Arg(u8), // get the value of a positional arg
    NamedParameter(StringKey),
    Const(Literal),
    Op1(UnaryOperation, ValueId),
    Op2(BinaryOperation, ValueId, ValueId),
    Load(ValueId),
    Store(ValueId, ValueId),
    Return(u8), // return values
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

#[derive(Tabled)]
struct CodeRow<'a> {
    pos: usize,
    next: usize,
    prev: usize,
    value: String,
    ty: &'a AstType,
    name: String,
    scope_id: usize,
    block_id: usize,
    pred: String,
    succ: String,
    term: bool,
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
    NextReturn,           // next node is a return statement
    Other,                // all other options
}

impl NextSeqState {
    pub fn get<E: Extra>(next_node: Option<&AstNode<E>>) -> Self {
        if let Some(next_node) = next_node {
            match next_node.node {
                Ast::Return(_) => Self::NextReturn,
                Ast::Label(key) => Self::NextLabel(key),
                _ => Self::Other,
            }
        } else {
            Self::Empty
        }
    }
}

#[derive(Debug)]
pub struct Blockify {
    code: Vec<LCode>,
    types: Vec<AstType>,
    scopes: Vec<ScopeId>,
    next_pos: Vec<ValueId>,
    prev_pos: Vec<ValueId>,
    loop_stack: Vec<LoopLayer>,
    env: Environment,
    names: IndexMap<ValueId, StringLabel>,
    //block_id: Option<BlockId>,
    entries: Vec<ValueId>,
    blocks: Vec<BlockId>,
}

impl Blockify {
    pub fn new() -> Self {
        Self {
            code: vec![],
            types: vec![],
            scopes: vec![],
            names: IndexMap::new(),
            next_pos: vec![],
            prev_pos: vec![],
            loop_stack: vec![],
            env: Environment::new(),
            //block_id: None,
            entries: vec![],
            blocks: vec![],
        }
    }

    pub fn block_name(&mut self, scope_id: ScopeId, name: StringLabel, v: ValueId) {
        self.env.get_scope_mut(scope_id).labels.insert(name, v);
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

            LCode::NamedParameter(key) => {
                format!("namedparam({})", b.r(*key))
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

    pub fn dump_codes<E: Extra>(&self, b: &NodeBuilder<E>) {
        let mut pos = 0;
        let mut out = vec![];
        loop {
            let code = self.code.get(pos).unwrap();
            let ty = self.types.get(pos).unwrap();
            let next = self.next_pos[pos].0 as usize;
            let scope_id = self.scopes[pos];
            let block_id = self.scopes[pos];
            let v = ValueId(pos as u32);
            out.push(CodeRow {
                pos,
                next,
                prev: self.prev_pos[pos].0 as usize,
                value: self.code_to_string(v, b),
                ty,
                name: self
                    .names
                    .get(&v)
                    .map(|key| b.resolve_label(*key))
                    .unwrap_or("".to_string())
                    .to_string(),
                scope_id: scope_id.0 as usize,
                block_id: block_id.0 as usize,
                pred: format!("{:?}", self.env.scopes[scope_id.0 as usize].pred),
                succ: format!("{:?}", self.env.scopes[scope_id.0 as usize].succ),
                term: code.is_term(),
            });

            pos += 1;
            if pos == self.code.len() {
                break;
            }
        }
        use tabled::settings::Style;
        println!("{}", Table::new(out).with(Style::sharp()).to_string());
    }

    pub fn dump<E: Extra>(&self, b: &NodeBuilder<E>) {
        self.dump_codes(b);
        self.env.dump(b);
    }

    pub fn push_code_with_name(
        &mut self,
        code: LCode,
        scope_id: ScopeId,
        block_id: ValueId,
        ty: AstType,
        name: StringKey,
    ) -> ValueId {
        let value_id = self.push_code(code, scope_id, block_id, ty.clone());
        self.env.scope_define(scope_id, name, value_id, ty);
        self.names.insert(value_id, name.into());
        value_id
    }

    pub fn push_code(
        &mut self,
        code: LCode,
        scope_id: ScopeId,
        block_id: ValueId,
        ty: AstType,
    ) -> ValueId {
        let offset = self.code.len();
        let scope = self.env.get_scope_mut(scope_id);
        let v = ValueId(offset as u32);
        if let Some(last_value) = scope.last_value {
            self.prev_pos.push(last_value);
            self.next_pos[last_value.0 as usize] = v;
        } else {
            self.prev_pos.push(v);
        }
        self.next_pos.push(v);
        self.scopes.push(scope_id);
        self.entries.push(block_id);
        if block_id.0 as usize != offset {
            self.blocks.push(self.blocks[block_id.0 as usize]);
        } else {
            self.blocks.push(BlockId(0));
        }

        scope.last_value = Some(v);

        self.code.push(code);
        self.types.push(ty);
        v
    }

    pub fn get_block_id(&self, v: ValueId) -> BlockId {
        self.blocks[v.0 as usize]
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

    pub fn build_module<E: Extra>(
        &mut self,
        node: AstNode<E>,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<ValueId> {
        match node.node {
            Ast::Module(name, body) => {
                let static_scope = self.env.new_scope();
                let block_id = self.push_label::<E>(name.into(), static_scope, &[], &[]);
                self.env.enter_scope(static_scope);
                self.add(block_id, *body, b, d)?;
                self.env.exit_scope();
                self.build_edges(b, d)?;
                Ok(block_id)
            }
            _ => unreachable!(),
        }
    }

    pub fn build_edges<E: Extra>(
        &mut self,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        for (i, code) in self.code.iter().enumerate() {
            match code {
                LCode::Ternary(_, x, y) => {
                    let v = ValueId(i as u32);
                    let block_id = self.get_block_id(v);
                    self.env.add_succ(block_id, *x);
                    self.env.add_succ(block_id, *y);
                }

                LCode::Branch(_, x, y) => {
                    let v = ValueId(i as u32);
                    let block_id = self.get_block_id(v);
                    self.env.add_succ(block_id, *x);
                    self.env.add_succ(block_id, *y);

                    let block_id = self.get_block_id(*x);
                    //self.env.add_pred(block_id, v);
                    let block_id = self.get_block_id(*y);
                    //self.env.add_pred(block_id, v);
                }

                LCode::DeclareFunction(Some(entry_id)) => {
                    let v = ValueId(i as u32);
                    let decl_block_id = self.get_block_id(v);
                    let entry_block_id = self.get_block_id(*entry_id);
                    self.env.add_succ(decl_block_id, *entry_id);

                    //self.env.add_pred(entry_block_id, v);
                }

                LCode::Jump(target_id, _) => {
                    let v = ValueId(i as u32);
                    let block_id = self.get_block_id(v);
                    self.env.add_succ(block_id, *target_id);

                    let block_id = self.get_block_id(*target_id);
                    //self.env.add_pred(block_id, v);
                }

                LCode::Goto(key) => {
                    unreachable!();
                    /*
                    let scope_id = self.scopes.get(i).unwrap();
                    let scope = self.env.get_scope_mut(*scope_id);
                    if let Some(value_id) = scope.labels.get(key) {
                        let next_scope_id = self.scopes.get(value_id.0 as usize).unwrap();
                        //self.env.add_succ(*scope_id, *next_scope_id);
                        //self.env.add_pred(*next_scope_id, *scope_id);
                    } else {
                    }
                    */
                }
                _ => (),
            }
        }
        Ok(())
    }

    pub fn add_pred(&mut self, v: ValueId, pred: ValueId) {
        let block_id = self.get_block_id(v);
        self.env.get_block_mut(block_id).pred.insert(pred);
    }

    pub fn add_succ(&mut self, v: ValueId, succ: ValueId) {
        let block_id = self.get_block_id(v);
        self.env.get_block_mut(block_id).succ.insert(succ);
    }

    pub fn push_label<E: Extra>(
        &mut self,
        name: StringLabel,
        scope_id: ScopeId,
        args: &[AstType],
        kwargs: &[ParameterNode<E>],
    ) -> ValueId {
        let block_id = self.env.new_block();
        let label_id = self.push_code(
            LCode::Label(args.len() as u8, kwargs.len() as u8),
            scope_id,
            ValueId(0),
            AstType::Unit,
        );
        self.entries[label_id.0 as usize] = label_id;
        self.blocks[label_id.0 as usize] = block_id;
        self.names.insert(label_id, name);
        self.block_name(scope_id, name, label_id);
        for p in kwargs {
            let v = self.push_code(
                LCode::NamedParameter(p.name),
                scope_id,
                label_id,
                p.ty.clone(),
            );
            self.names.insert(v, p.name.into());
            self.env.define(p.name, v, p.ty.clone());
        }
        label_id
    }

    pub fn emit_sequence<E: Extra>(
        &mut self,
        block_id: ValueId,
        node: AstNode<E>,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<ValueId> {
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
        let mut current_block_id = block_id;
        let mut iter = exprs.into_iter().peekable();
        loop {
            if let Some(expr) = iter.next() {
                let next_state = NextSeqState::get(iter.peek());
                match next_state {
                    NextSeqState::NextLabel(key) => (),
                    NextSeqState::NextReturn => (),
                    NextSeqState::Empty => (),
                    NextSeqState::Other => (),
                }

                let v = self.add(current_block_id, expr, b, d)?;
                current_block_id = *self.entries.get(v.0 as usize).unwrap();
                value_id = Some(v);
            } else {
                break;
            }
        }

        Ok(value_id.unwrap())
    }

    pub fn emit_function<E: Extra>(
        &mut self,
        block_id: ValueId,
        def: Definition<E>,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<ValueId> {
        let scope_id = self.env.current_scope().unwrap();

        let params = def.params.iter().map(|p| p.ty.clone()).collect();
        let ty = AstType::Func(params, def.return_type.clone());

        if let Some(body) = def.body {
            let body_scope_id = self.env.new_scope();

            // return block
            let name = b.s("ret");
            let return_type = *def.return_type;
            let args = match &return_type {
                AstType::Unit => vec![],
                _ => vec![return_type.clone()],
            };

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
                );
            }

            self.push_code(
                LCode::Return(v_args.len() as u8),
                body_scope_id,
                return_block,
                AstType::Unit,
            );
            self.env.get_scope_mut(body_scope_id).return_block = Some(return_block);

            // handle body
            self.env.enter_scope(body_scope_id);
            let entry_id = self.push_label(def.name.into(), body_scope_id, &[], &def.params);
            let v_decl = self.push_code_with_name(
                LCode::DeclareFunction(Some(entry_id)),
                scope_id,
                block_id,
                ty.clone(),
                def.name,
            );

            self.add(entry_id, *body, b, d)?;
            self.env.exit_scope();

            // replace declaration with entry_id
            self.code[v_decl.0 as usize] = LCode::DeclareFunction(Some(entry_id));
            Ok(v_decl)
        } else {
            Ok(self.push_code_with_name(
                LCode::DeclareFunction(None),
                scope_id,
                block_id,
                ty.clone(),
                def.name,
            ))
        }
    }

    pub fn add<E: Extra>(
        &mut self,
        block_id: ValueId,
        node: AstNode<E>,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<ValueId> {
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
                                d.push_diagnostic(error(
                                    &format!("Type not function: {}, {:?}", name, data.ty),
                                    node.extra.get_span(),
                                ));
                                return Err(Error::new(ParseError::Invalid));
                            }
                        } else {
                            //self.env.dump(b);
                            d.push_diagnostic(error(
                                &format!("Call name not found: {}", name),
                                node.extra.get_span(),
                            ));
                            return Err(Error::new(ParseError::Invalid));
                        }
                    }
                    _ => {
                        unimplemented!("{:?}", expr.node);
                    }
                };

                if let AstType::Func(_func_arg_types, ret) = &ty {
                    if f_args.len() != args.len() {
                        d.push_diagnostic(error(
                            &format!("Call arity mismatch: {}", name),
                            node.extra.get_span(),
                        ));
                        return Err(Error::new(ParseError::Invalid));
                    }

                    let args_size = args.len() as u8;
                    for a in args {
                        match a {
                            Argument::Positional(expr) => {
                                let v = self.add(block_id, *expr, b, d)?;
                                self.push_code(LCode::Value(v), scope_id, block_id, ty.clone());
                            }
                        }
                    }
                    Ok(self.push_code(LCode::Call(v_func, args_size, 0), scope_id, block_id, ty))
                } else {
                    unimplemented!("calling non function type: {:?}", ty);
                }
            }

            Ast::Label(name) => {
                // all blocks should have been forward declared in the sequence
                let value_id = self.env.resolve_block(name.into()).unwrap();

                let scope = self.env.get_scope(scope_id);
                if let Some(last_value) = scope.last_value {
                    // check to ensure that the previous block was terminated

                    let code = self.code.get(last_value.0 as usize).unwrap();
                    if !code.is_term() {
                        //if params.len() > 0 {
                        // if this block requires parameters, then we have an error
                        //unreachable!()
                        //}

                        //println!("label: {}", b.r(name));
                        //println!("code: {:?}", self.code_to_string(last_value, b));
                        self.push_code(LCode::Jump(value_id, 0), scope_id, block_id, AstType::Unit);
                        //self.env.exit_scope();
                    }
                }

                Ok(value_id)
            }

            Ast::Identifier(key) => {
                let data = self.env.resolve(key).unwrap();
                let ty = data.ty.clone();
                let code = LCode::Load(data.value_id);
                Ok(self.push_code(code, scope_id, block_id, ty))
            }

            Ast::Assign(target, expr) => {
                let name = match target {
                    AssignTarget::Identifier(name) | AssignTarget::Alloca(name) => name,
                };

                //println!("expr: {:?}", expr);
                let v_expr = self.add(block_id, *expr, b, d)?;
                let ty = self.get_type(v_expr);
                let v_decl =
                    self.push_code_with_name(LCode::Declare, scope_id, block_id, ty.clone(), name);
                self.push_code(
                    LCode::Store(v_decl, v_expr),
                    scope_id,
                    block_id,
                    AstType::Unit,
                );
                Ok(v_decl)
            }

            Ast::Builtin(bi, args) => {
                let _ty = bi.get_return_type();
                let args_size = args.len();
                assert_eq!(args_size, bi.arity());
                let mut values = vec![];
                for a in args.into_iter() {
                    let Argument::Positional(expr) = a;
                    let v = self.add(block_id, *expr, b, d)?;
                    let ty = self.get_type(v);
                    values.push((v, ty));
                }

                for (v, ty) in values {
                    self.push_code(LCode::Value(v), scope_id, block_id, ty);
                }

                let ty = bi.get_return_type();
                let value_id = self.push_code(
                    LCode::Builtin(bi, args_size as u8, 0),
                    scope_id,
                    block_id,
                    ty,
                );
                Ok(value_id)
            }

            Ast::Literal(lit) => {
                let ty: AstType = lit.clone().into();
                Ok(self.push_code(LCode::Const(lit), scope_id, block_id, ty))
            }

            Ast::UnaryOp(op, x) => {
                let vx = self.add(block_id, *x, b, d)?;
                let code = LCode::Op1(op, vx);
                Ok(self.push_code(code, scope_id, block_id, self.get_type(vx)))
            }

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
                let next_scope_id = self.env.new_scope();
                //let next_block_id = self.env.new_block();
                let name = b.s("next");

                let v_next = self.push_label::<E>(name.into(), next_scope_id, &[], &[]);

                let then_scope_id = self.env.new_scope();
                //let then_block_id = self.env.new_block();
                let name = b.s("then");
                self.env.enter_scope(then_scope_id);
                let v_then = self.push_label::<E>(name.into(), then_scope_id, &[], &[]);
                let v_then_result = self.add(v_then, *then_expr, b, d)?;
                self.env.exit_scope();
                let then_ty = self.get_type(v_then_result);
                self.push_code(LCode::Jump(v_next, 0), then_scope_id, v_then, AstType::Unit);

                let v_else = if let Some(else_expr) = maybe_else_expr {
                    let else_scope_id = self.env.new_scope();
                    //let else_block_id = self.env.new_block();
                    let name = b.s("else");
                    self.env.enter_scope(else_scope_id);
                    let v_else = self.push_label::<E>(name.into(), else_scope_id, &[], &[]);
                    let v_else_result = self.add(v_else, *else_expr, b, d)?;
                    self.env.exit_scope();
                    let else_ty = self.get_type(v_else_result);
                    self.push_code(LCode::Jump(v_next, 0), else_scope_id, v_else, AstType::Unit);
                    v_else
                } else {
                    v_next
                };

                let v = self.add(block_id, *condition, b, d)?;
                let code = LCode::Branch(v, v_then, v_else);
                self.push_code(code, scope_id, block_id, AstType::Unit);
                Ok(v)
            }

            Ast::Ternary(c, x, y) => {
                let then_scope_id = self.env.new_scope();
                //let then_block_id = self.env.new_block();
                let name = b.s("then");
                self.env.enter_scope(then_scope_id);
                let v_then = self.push_label::<E>(name.into(), then_scope_id, &[], &[]);
                let v_then_result = self.add(v_then, *x, b, d)?;
                self.env.exit_scope();
                let then_ty = self.get_type(v_then_result);

                let else_scope_id = self.env.new_scope();
                //let else_block_id = self.env.new_block();
                let name = b.s("else");
                self.env.enter_scope(else_scope_id);
                let v_else = self.push_label::<E>(name.into(), else_scope_id, &[], &[]);
                let v_else_result = self.add(v_else, *y, b, d)?;
                self.env.exit_scope();
                let else_ty = self.get_type(v_else_result);
                assert_eq!(then_ty, else_ty);

                let v = self.add(block_id, *c, b, d)?;
                let code = LCode::Ternary(v, v_then, v_else);
                Ok(self.push_code(code, scope_id, block_id, then_ty))
            }

            Ast::BinaryOp(op, x, y) => {
                let vx = self.add(block_id, *x, b, d)?;
                let vy = self.add(block_id, *y, b, d)?;
                let code = LCode::Op2(op.node, vx, vy);
                let ty = self.get_type(vx);
                Ok(self.push_code(code, scope_id, block_id, ty))
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
                let jump_value = self.push_code(code, scope_id, block_id, AstType::Unit);
                Ok(jump_value)
            }

            Ast::Return(maybe_expr) => {
                if let Some(v_return) = self.env.resolve_return_block() {
                    let count = if maybe_expr.is_some() { 1 } else { 0 };

                    let maybe_ret_value = if let Some(expr) = maybe_expr {
                        let expr_value_id = self.add(block_id, *expr, b, d)?;
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
                        );
                    }

                    //let code = LCode::Return(count);
                    let code = LCode::Jump(v_return, count);
                    let v = self.push_code(code, scope_id, block_id, AstType::Unit);
                    //self.env.exit_scope();
                    Ok(v)
                } else {
                    d.push_diagnostic(error(
                        &format!("Return without function context"),
                        node.extra.get_span(),
                    ));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            _ => unimplemented!("{:?}", node.node),
        }
    }

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
            let v_block = self.entries[v.0 as usize];
            match code {
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

        /*
        let mut ids = HashMap::new();
        let mut values = vec![];
        for (offset, code) in self.code.iter().enumerate() {
            if let LCode::Label(_,_) = code {
                let v = ValueId(offset as u32);
                let name = self.names.get(&v).unwrap();
                let id = g.add_node(Node::new_block(b.r(*name).to_string(), v));
                ids.insert(v, id);
                values.push(v);
            }
        }

        for v in values {
            let block_id = self.get_block_id(v);
            let block = self.env.get_block(block_id);
            for succ in block.succ.iter() {
                g.add_edge(*ids.get(&v).unwrap(), *ids.get(succ).unwrap(), ());
            }

            for pred in block.pred.iter() {
                g.add_edge(*ids.get(pred).unwrap(), *ids.get(&v).unwrap(), ());
            }
        }
        */

        /*
        for (offset, code) in self.code.iter().enumerate() {
            if let LCode::Label(_,_) = code {
                let v = ValueId(offset as u32);
                let block_id = self.get_block_id(v);
                let block = self.env.get_block(block_id);
                for succ in block.succ.iter() {
                    g.add_edge(*ids.get(&v).unwrap(), *ids.get(succ).unwrap(), ());
                }

                for pred in block.pred.iter() {
                    g.add_edge(*ids.get(pred).unwrap(), *ids.get(&v).unwrap(), ());
                }
            }
        }

        for (offset, block) in self.env.blocks.iter().enumerate() {
            let block_id = BlockId(offset as u32);
            for succ in block.succ.iter() {
                g.add_edge(*ids.get(&block_id).unwrap(), *ids.get(&target_id).unwrap(), ());
            }
        }

        for (offset, code) in self.code.iter().enumerate() {
            match code {
                LCode::Jump(target_id,_) => {
                    //let value_id = ValueId(offset as u32);
                    let block_id = self.entries.get(offset).unwrap();
                    g.add_edge(*ids.get(&block_id).unwrap(), *ids.get(&target_id).unwrap(), ());
                }
                LCode::Branch(_, x, y) => {
                    let block_id = self.entries.get(offset).unwrap();
                    g.add_edge(*ids.get(&block_id).unwrap(), *ids.get(&x).unwrap(), ());
                    g.add_edge(*ids.get(&block_id).unwrap(), *ids.get(&y).unwrap(), ());
                }
                LCode::DeclareFunction(Some(entry_id)) => {
                    let block_id = self.entries.get(offset).unwrap();
                    g.add_edge(*ids.get(&block_id).unwrap(), *ids.get(&entry_id).unwrap(), ());
                }
                LCode::Ternary(_, x, y) => {
                    let block_id = self.entries.get(offset).unwrap();
                    g.add_edge(*ids.get(&block_id).unwrap(), *ids.get(&x).unwrap(), ());
                    g.add_edge(*ids.get(&block_id).unwrap(), *ids.get(&y).unwrap(), ());
                }
                LCode::Goto(_) => unreachable!(),
                _ => ()
            }
        }
        */

        /*
        for node_index in self.g.node_indices() {
            let _label = self.block_names_index.get(&node_index).unwrap();
            //let block_name = format!("b{}", label.offset());
            let block_name = b
                .resolve_block_label(*self.block_names_index.get(&node_index).unwrap())
                .clone();
            g_out.add_node(Node::new_block(block_name, node_index));
        }
        for block_node_index in self.g.node_indices() {
            let data = self.blocks.get(&block_node_index).unwrap();

            let mut x = HashMap::new();
            for (name, symbol_index) in data.symbols.iter() {
                let name = b.resolve_label(*name).clone();
                let name = match symbol_index {
                    SymIndex::Op(_, _) => {
                        format!("op:{}", name)
                    }
                    SymIndex::Arg(_, _) => {
                        format!("arg:{}", name)
                    }
                    SymIndex::Def(_, _) => {
                        format!("def:{}", name)
                    }
                };

                let symbol_node_index = g_out.add_node(Node::new_symbol(
                    name,
                    //b.strings.resolve(name).clone(),
                    //format!("{}{:?}", b.strings.resolve(name), symbol_index),
                    block_node_index,
                ));
                g_out.add_edge(block_node_index, symbol_node_index, ());
                x.insert(symbol_index, symbol_node_index);
            }

            for n in self
                .g
                .neighbors_directed(block_node_index, petgraph::Direction::Outgoing)
            {
                let block = self.blocks.get(&n).unwrap();
                if let Some(parent) = block.parent_symbol {
                    let symbol_node_index = x.get(&parent).unwrap();
                    g_out.add_edge(*symbol_node_index, n, ());
                } else {
                    g_out.add_edge(block_node_index, n, ());
                }
            }
        }

        */
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
        //let path = std::fs::canonicalize(filename).unwrap();
        println!("saved graph {:?}", filename);
        //println!("{}", path.clone().into_os_string().into_string().unwrap());
        println!("{}", s);
        std::fs::write(filename, s).unwrap();
    }
}
