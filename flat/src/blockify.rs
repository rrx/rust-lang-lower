use anyhow::Error;
use anyhow::Result;
//use codespan_reporting::diagnostic::{Diagnostic, Label};
use indexmap::IndexMap;
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
    //BlockId,
    Diagnostic,
    Diagnostics,
    Extra,
    //IRPlaceTable,
    Label,
    Literal,
    NodeBuilder,
    ParseError,
    //ParameterNode,
    //PlaceId,
    //PlaceNode, None,
    Span,
    StringKey,
    //StringLabel,
    UnaryOperation,
    //Definition,
    //VarDefinitionSpace,
};

use crate::{Environment, ScopeId, ValueId};

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
    Label(StringKey, u8, u8), // BlockId, number of positional arguments, number of named arguments
    Declare,
    DeclareFunction(Option<ValueId>), // optional entry block
    Value(ValueId),
    NamedArg(StringKey),
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
            Self::Label(_, _, _) => true,
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

    pub fn to_string<E: Extra>(&self, context: &Blockify, b: &NodeBuilder<E>) -> String {
        match self {
            Self::DeclareFunction(maybe_entry) => {
                format!("declare_function({:?})", maybe_entry) //.names.get(block_id).unwrap_or(format!("{:?}", block_id))) //b.resolve_block_label(*block_id))
            }
            Self::Label(block_id, args, kwargs) => {
                format!("label({}, {}, {})", b.r(*block_id), args, kwargs,)
            }
            Self::Goto(block_id) => {
                format!("goto({})", b.r(*block_id))
            }
            Self::Jump(value_id, args) => {
                format!("jump({:?}, {})", value_id, args,)
            }
            _ => {
                format!("{:?}", self)
            }
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
pub struct Blockify {
    code: Vec<LCode>,
    types: Vec<AstType>,
    scopes: Vec<ScopeId>,
    next_pos: Vec<ValueId>,
    prev_pos: Vec<ValueId>,
    loop_stack: Vec<LoopLayer>,
    env: Environment,
    names: IndexMap<ValueId, StringKey>,
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
        }
    }

    pub fn block_name(&mut self, scope_id: ScopeId, name: StringKey, v: ValueId) {
        self.env.get_scope_mut(scope_id).labels.insert(name, v);
    }

    pub fn dump_codes<E: Extra>(&self, b: &NodeBuilder<E>) {
        let mut pos = 0;
        //let depth = 0;
        let mut out = vec![];
        loop {
            let code = self.code.get(pos).unwrap();
            let ty = self.types.get(pos).unwrap();
            let next = self.next_pos[pos].0 as usize;
            let scope_id = self.scopes[pos];
            out.push(CodeRow {
                pos,
                next,
                prev: self.prev_pos[pos].0 as usize,
                value: code.to_string(&self, b),
                ty,
                name: self
                    .names
                    .get(&ValueId(pos as u32))
                    .map(|key| b.r(*key))
                    .unwrap_or("")
                    .to_string(),
                scope_id: scope_id.0 as usize,
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

    pub fn push_code(&mut self, code: LCode, scope_id: ScopeId, ty: AstType) -> ValueId {
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

        scope.last_value = Some(v);

        self.code.push(code);
        self.types.push(ty);
        v
    }

    pub fn resolve_block_label<E: Extra>(&self, k: ValueId, b: &NodeBuilder<E>) -> String {
        if let Some(key) = self.names.get(&k) {
            b.r(*key).to_string()
        } else {
            format!("b{}", k.0)
        }
    }

    pub fn get_type(&self, v: ValueId) -> AstType {
        self.types.get(v.0 as usize).unwrap().clone()
    }

    pub fn build<E: Extra>(
        &mut self,
        node: AstNode<E>,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        self.add(self.env.static_scope, node, b, d)?;
        self.build_edges(b, d)
    }

    pub fn build_edges<E: Extra>(
        &mut self,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        for (i, code) in self.code.iter().enumerate() {
            match code {
                LCode::Goto(key) => {
                    let scope_id = self.scopes.get(i).unwrap();
                    let scope = self.env.get_scope_mut(*scope_id);
                    if let Some(value_id) = scope.labels.get(key) {
                        let next_scope_id = self.scopes.get(value_id.0 as usize).unwrap();
                        self.env.add_succ(*scope_id, *next_scope_id);
                        self.env.add_pred(*next_scope_id, *scope_id);
                    } else {
                    }
                }
                _ => (),
            }
        }
        Ok(())
    }

    pub fn add<E: Extra>(
        &mut self,
        scope_id: ScopeId,
        node: AstNode<E>,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<ValueId> {
        match node.node {
            Ast::Module(name, body) => {
                let value_id = self.push_code(LCode::Label(name, 0, 0), scope_id, AstType::Unit);
                self.names.insert(value_id, name);
                self.add(scope_id, *body, b, d)?;
                Ok(value_id)
            }

            Ast::Sequence(exprs) => {
                let mut value_id = None;
                let mut current_scope_id = scope_id;
                for c in exprs.into_iter() {
                    let v = self.add(current_scope_id, c, b, d)?;
                    current_scope_id = *self.scopes.get(v.0 as usize).unwrap();
                    value_id = Some(v);
                }
                Ok(value_id.unwrap())
            }

            Ast::Definition(def) => {
                let params = def.params.iter().map(|p| p.ty.clone()).collect();
                let ty = AstType::Func(params, def.return_type);
                let v_decl = self.push_code(LCode::DeclareFunction(None), scope_id, ty.clone());
                self.env
                    .scope_define(self.env.static_scope, def.name, v_decl, ty.clone());
                self.names.insert(v_decl, def.name.into());

                let maybe_entry = if let Some(body) = def.body {
                    let body_scope_id = self.env.new_scope();
                    self.env.enter_scope(body_scope_id);
                    let entry_id = self.push_code(
                        LCode::Label(def.name, 0, def.params.len() as u8),
                        body_scope_id,
                        AstType::Unit,
                    );
                    self.block_name(body_scope_id, def.name, entry_id);
                    for p in def.params {
                        let v =
                            self.push_code(LCode::NamedArg(p.name), body_scope_id, p.ty.clone());
                        self.names.insert(v, p.name);
                        self.env.define(p.name, v, p.ty.clone());
                    }
                    self.add(body_scope_id, *body, b, d)?;

                    self.code[v_decl.0 as usize] = LCode::DeclareFunction(Some(entry_id));
                    Some(entry_id)
                } else {
                    None
                };
                let v = self.push_code(LCode::DeclareFunction(maybe_entry), scope_id, ty.clone());
                self.env
                    .scope_define(self.env.static_scope, def.name, v, ty.clone());
                self.names.insert(v, def.name.into());
                Ok(v)
            }

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
                            self.env.dump(b);
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
                                let v = self.add(scope_id, *expr, b, d)?;
                                self.push_code(LCode::Value(v), scope_id, ty.clone());
                            }
                        }
                    }
                    Ok(self.push_code(LCode::Call(v_func, args_size, 0), scope_id, ty))
                } else {
                    unimplemented!("calling non function type: {:?}", ty);
                }
            }

            Ast::Label(name, params) => {
                //assert!(self.env.prev.is_some());
                //assert!(self.env.current.is_none());

                let scope = self.env.get_scope(scope_id);
                if let Some(last_value) = scope.last_value {
                    // check to ensure that the previous block was terminated

                    let code = self.code.get(last_value.0 as usize).unwrap();
                    if !code.is_term() {
                        if params.len() > 0 {
                            // if this block requires parameters, then we have an error
                            unreachable!()
                        }

                        println!("label: {}", b.r(name));
                        println!("code: {:?}", code.to_string(self, b));
                        self.push_code(LCode::Goto(name), scope_id, AstType::Unit);
                        //self.env.exit_scope();
                    }
                }

                let new_scope_id = self.env.new_scope();
                self.env.enter_scope(new_scope_id);

                for p in &params {
                    let v =
                        self.push_code(LCode::NamedArg(p.name.into()), new_scope_id, p.ty.clone());
                    self.env.define(p.name, v, p.ty.clone());
                }

                let v = self.push_code(
                    LCode::Label(name, 0, params.len() as u8),
                    new_scope_id,
                    AstType::Unit,
                );
                self.block_name(new_scope_id, name, v);
                self.names.insert(v, name);
                Ok(v)
            }

            Ast::Identifier(key) => {
                println!("stack: {:?}", (b.r(key), &self.env.stack));
                self.env.dump(b);
                let data = self.env.resolve(key).unwrap();
                let ty = data.ty.clone();
                let code = LCode::Load(data.value_id);
                Ok(self.push_code(code, scope_id, ty))
            }

            Ast::Assign(target, expr) => {
                let name = match target {
                    AssignTarget::Identifier(name) | AssignTarget::Alloca(name) => name,
                };

                println!("expr: {:?}", expr);
                let v_expr = self.add(scope_id, *expr, b, d)?;
                let ty = self.get_type(v_expr);
                let v_decl = self.push_code(LCode::Declare, scope_id, ty.clone());
                self.env.define(name, v_decl, ty.clone());
                self.names.insert(v_decl, name);
                self.push_code(LCode::Store(v_decl, v_expr), scope_id, AstType::Unit);
                Ok(v_decl)
            }

            Ast::Builtin(bi, args) => {
                let _ty = bi.get_return_type();
                let args_size = args.len();
                assert_eq!(args_size, bi.arity());
                let mut values = vec![];
                for a in args.into_iter() {
                    let Argument::Positional(expr) = a;
                    let v = self.add(scope_id, *expr, b, d)?;
                    let ty = self.get_type(v);
                    values.push((v, ty));
                }

                for (v, ty) in values {
                    self.push_code(LCode::Value(v), scope_id, ty);
                }

                let ty = bi.get_return_type();
                let value_id = self.push_code(LCode::Builtin(bi, args_size as u8, 0), scope_id, ty);
                Ok(value_id)
            }

            Ast::Literal(lit) => {
                let ty: AstType = lit.clone().into();
                Ok(self.push_code(LCode::Const(lit), scope_id, ty))
            }

            //Ast::Identifier(label) => {
            //}
            Ast::UnaryOp(op, x) => {
                let vx = self.add(scope_id, *x, b, d)?;
                let code = LCode::Op1(op, vx);
                Ok(self.push_code(code, scope_id, self.get_type(vx)))
            }

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
                let next_scope_id = self.env.new_scope();
                let name = b.s("next");
                let v_next = self.push_code(LCode::Label(name, 0, 0), next_scope_id, AstType::Unit);

                let then_scope_id = self.env.new_scope();
                let name = b.s("then");
                let v_then = self.push_code(LCode::Label(name, 0, 0), then_scope_id, AstType::Unit);
                self.block_name(then_scope_id, name, v_then);
                let v_then_result = self.add(then_scope_id, *then_expr, b, d)?;
                let then_ty = self.get_type(v_then_result);
                self.push_code(LCode::Jump(v_next, 0), then_scope_id, AstType::Unit);

                let v_else = if let Some(else_expr) = maybe_else_expr {
                    let else_scope_id = self.env.new_scope();
                    let name = b.s("else");
                    let v_else =
                        self.push_code(LCode::Label(name, 0, 0), else_scope_id, AstType::Unit);
                    self.block_name(else_scope_id, name, v_else);
                    let v_else_result = self.add(else_scope_id, *else_expr, b, d)?;
                    let else_ty = self.get_type(v_else_result);
                    //assert_eq!(then_ty, else_ty);
                    self.push_code(LCode::Jump(v_next, 0), else_scope_id, AstType::Unit);
                    v_else
                } else {
                    v_next
                };

                let v = self.add(scope_id, *condition, b, d)?;
                let code = LCode::Branch(v, v_then, v_else);
                self.push_code(code, scope_id, AstType::Unit);
                //self.env.exit_scope();
                Ok(v)
            }

            Ast::Ternary(c, x, y) => {
                let then_scope_id = self.env.new_scope();
                let name = b.s("then");
                let v_then = self.push_code(LCode::Label(name, 0, 0), then_scope_id, AstType::Unit);
                self.block_name(then_scope_id, name, v_then);
                let v_then_result = self.add(then_scope_id, *x, b, d)?;
                let then_ty = self.get_type(v_then_result);

                let else_scope_id = self.env.new_scope();
                let name = b.s("else");
                let v_else = self.push_code(LCode::Label(name, 0, 0), else_scope_id, AstType::Unit);
                self.block_name(else_scope_id, name, v_else);
                let v_else_result = self.add(else_scope_id, *y, b, d)?;
                let else_ty = self.get_type(v_else_result);
                assert_eq!(then_ty, else_ty);

                let v = self.add(scope_id, *c, b, d)?;
                let code = LCode::Ternary(v, v_then, v_else);
                Ok(self.push_code(code, scope_id, then_ty))
            }

            Ast::BinaryOp(op, x, y) => {
                let vx = self.add(scope_id, *x, b, d)?;
                let vy = self.add(scope_id, *y, b, d)?;
                let code = LCode::Op2(op.node, vx, vy);
                let ty = self.get_type(vx);
                Ok(self.push_code(code, scope_id, ty))
            }

            Ast::Goto(label) => {
                let code = LCode::Goto(label);
                let jump_value = self.push_code(code, scope_id, AstType::Unit);
                //for a in args {
                //let v = self.add(scope_id, a, b, d)?;
                //self.push_code(LCode::Value(v), scope_id, self.get_type(v));
                //}
                //self.env.exit_scope();
                //self.env.prev = Some(scope_id);
                //self.env.current.take().unwrap();
                Ok(jump_value)
            }

            Ast::Return(maybe_expr) => {
                let count = if maybe_expr.is_some() { 1 } else { 0 };

                let maybe_ret_value = if let Some(expr) = maybe_expr {
                    let expr_value_id = self.add(scope_id, *expr, b, d)?;
                    Some(expr_value_id)
                } else {
                    None
                };

                // args
                if let Some(ret_value) = maybe_ret_value {
                    self.push_code(LCode::Value(ret_value), scope_id, self.get_type(ret_value));
                }

                let code = LCode::Return(count);
                let v = self.push_code(code, scope_id, AstType::Unit);
                //self.env.exit_scope();
                Ok(v)
            }

            _ => unimplemented!("{:?}", node.node),
        }
    }
}
