use anyhow::Result;
//use codespan_reporting::diagnostic::{Diagnostic, Label};
use indexmap::IndexMap;
use tabled::{Table, Tabled};

use lower::{
    ast::AssignTarget,
    ast::Builtin,
    Argument,
    Ast,
    AstNode,
    AstType,
    BinaryOperation,
    BlockId,
    Diagnostic,
    Diagnostics,
    Extra,
    //IRPlaceTable,
    Label,
    Literal,
    NodeBuilder,
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
    name: BlockId,
}

#[derive(Debug)]
pub struct LoopLayer {
    next: BlockId,
    restart: BlockId,
}

#[derive(Debug)]
pub enum LCode {
    Label(BlockId, u8, u8), // BlockId, number of positional arguments, number of named arguments
    Declare,
    DeclareFunction,
    Value(ValueId),
    NamedArg(StringKey),
    Const(Literal),
    Op1(UnaryOperation, ValueId),
    Op2(BinaryOperation, ValueId, ValueId),
    Load(ValueId),
    Store(ValueId, ValueId),
    Return(u8), // return values
    Jump(BlockId, u8),
    Branch(ValueId, BlockId, BlockId),
    Ternary(ValueId, ScopeId, ScopeId),
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
            Self::Branch(_, _, _) => true,
            _ => false,
        }
    }

    pub fn to_string<E: Extra>(&self, context: &Blockify, b: &NodeBuilder<E>) -> String {
        match self {
            Self::DeclareFunction => {
                format!("declare_function") //.names.get(block_id).unwrap_or(format!("{:?}", block_id))) //b.resolve_block_label(*block_id))
            }
            Self::Label(block_id, args, kwargs) => {
                format!(
                    "label({}, {}, {})",
                    b.resolve_block_label(*block_id),
                    args,
                    kwargs,
                )
            }
            Self::Jump(block_id, args) => {
                format!("jump({}, {})", b.resolve_block_label(*block_id), args,)
            }
            _ => {
                format!("{:?}", self)
            }
        }
    }

    /*
    pub fn dump<E: Extra>(
        &self,
        pos: usize,
        ty: &AstType,
        depth: usize,
        env: &Environment,
        b: &NodeBuilder<E>,
    ) {
        println!(
            "%{} = {:width$}{}: {:?}",
            pos,
            "",
            self.to_string(env, b),
            ty,
            width = depth * 2
        );
    }
    */
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

    /*
    pub fn dump_code<E: Extra>(
        &self,
        pos: ValueId,
        b: &NodeBuilder<E>,
    ) {
        println!(
            "%{} = {:width$}{}: {:?}",
            pos,
            "",
            self.to_string(env, b),
            ty,
            width = depth * 2
        );
    }
    */

    pub fn dump_codes<E: Extra>(&self, b: &NodeBuilder<E>) {
        let mut pos = 0;
        //let depth = 0;
        let mut out = vec![];
        loop {
            let code = self.code.get(pos).unwrap();
            let ty = self.types.get(pos).unwrap();
            //code.dump(pos, ty, depth, &self.env, b);
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
            });

            //pos = next;
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
        //env: &mut Environment,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        //let scope_id = self.env.enter_scope();
        self.add(self.env.static_scope, node, b, d)?;
        Ok(())
    }

    pub fn add<E: Extra>(
        &mut self,
        scope_id: ScopeId,
        node: AstNode<E>,
        //env: &mut Environment,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<ValueId> {
        match node.node {
            Ast::Module(block) => {
                let value_id =
                    self.push_code(LCode::Label(block.name, 0, 0), scope_id, AstType::Unit);
                if let BlockId::Name(key) = block.name {
                    self.names.insert(value_id, key);
                }

                for c in block.children.into_iter() {
                    self.add(scope_id, c, b, d)?;
                }
                Ok(value_id)
            }

            Ast::Sequence(exprs) => {
                let mut value_id = None;
                for c in exprs.into_iter() {
                    value_id = Some(self.add(scope_id, c, b, d)?);
                }
                Ok(value_id.unwrap())
            }

            Ast::Definition(def) => {
                let params = def.params.iter().map(|p| p.ty.clone()).collect();
                let ty = AstType::Func(params, def.return_type);
                self.env.define(self.env.static_scope, def.name, ty.clone());
                //let func_scope_id = self.env.dependent_scope(scope_id);

                if let Some(body) = def.body {
                    let body_scope_id = self.env.new_scope();
                    let seq = vec![
                        b.node(Ast::Label(def.name.into(), def.params.clone())),
                        *body,
                    ];
                    self.env.enter_scope(body_scope_id);
                    self.add(body_scope_id, b.seq(seq), b, d)?;
                    self.env.exit_scope();
                }
                let v = self.push_code(LCode::DeclareFunction, scope_id, ty);
                self.names.insert(v, def.name.into());
                Ok(v)
            }

            Ast::Label(block_id, params) => {
                //assert!(self.env.prev.is_some());
                //assert!(self.env.current.is_none());
                let v = self.push_code(
                    LCode::Label(block_id, 0, params.len() as u8),
                    scope_id,
                    AstType::Unit,
                );
                if let BlockId::Name(key) = block_id {
                    self.names.insert(v, key);
                }
                for p in params {
                    self.push_code(LCode::NamedArg(p.name.into()), scope_id, p.ty);
                }
                Ok(v)
            }

            Ast::Assign(target, expr) => {
                let name = match target {
                    AssignTarget::Identifier(name) | AssignTarget::Alloca(name) => name,
                };

                println!("expr: {:?}", expr);
                let v = self.add(scope_id, *expr, b, d)?;
                //let ty = self.get_place(v).ty.clone();
                //let p = PlaceNode::new_stack(name.into(), ty.clone());
                let ty = self.get_type(v);
                self.env
                    .define(self.env.current_scope().unwrap(), name, ty.clone());
                let v = self.push_code(LCode::Declare, scope_id, ty);
                self.names.insert(v, name);
                Ok(v)
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
                let ty = bi.get_return_type();
                let value_id = self.push_code(LCode::Builtin(bi, args_size as u8, 0), scope_id, ty);
                for (v, ty) in values {
                    self.push_code(LCode::Value(v), scope_id, ty);
                }
                Ok(value_id)
            }

            Ast::Literal(lit) => {
                let ty: AstType = lit.clone().into();
                //let name = b.labels.fresh_var_id();
                //let p = PlaceNode::new(name, ty.clone(), VarDefinitionSpace::Reg);
                Ok(self.push_code(LCode::Const(lit), scope_id, ty))
            }

            //Ast::Identifier(label) => {
            //}
            Ast::UnaryOp(op, x) => {
                let vx = self.add(scope_id, *x, b, d)?;
                let code = LCode::Op1(op, vx);
                Ok(self.push_code(code, scope_id, self.get_type(vx)))
            }

            Ast::Ternary(c, x, y) => {
                let then_scope_id = self.env.new_scope();
                let then_block_id = b.labels.fresh_block_id();
                let seq = vec![b.node(Ast::Label(then_block_id, vec![])), *x];
                let ty = AstType::unknown(0);
                let ast = b.seq(seq);
                self.add(then_scope_id, ast, b, d)?;
                //self.pending_blocks.push((then_scope_id, b.seq(seq)));
                //env.exit_scope();

                let else_scope_id = self.env.new_scope();
                let else_block_id = b.labels.fresh_block_id();
                let seq = vec![b.node(Ast::Label(else_block_id, vec![])), *y];
                //self.pending_blocks.push((else_scope_id, b.seq(seq)));
                let ty = AstType::unknown(0);
                let ast = b.seq(seq);
                self.add(else_scope_id, ast, b, d)?;
                //env.exit_scope();

                //let condition_scope_id = env.dependent_scope(then_scope_id);
                // condition
                //let p = PlaceNode::new(b.labels.fresh_var_id(), ty.clone(), VarDefinitionSpace::Reg);
                let v = self.add(scope_id, *c, b, d)?;
                let code = LCode::Ternary(v, then_scope_id, else_scope_id);
                Ok(self.push_code(code, scope_id, ty))
            }

            Ast::BinaryOp(op, x, y) => {
                let vx = self.add(scope_id, *x, b, d)?;
                let vy = self.add(scope_id, *y, b, d)?;
                let code = LCode::Op2(op.node, vx, vy);
                let ty = self.get_type(vx);
                Ok(self.push_code(code, scope_id, ty))
            }

            Ast::Goto(block_id, args) => {
                let code = LCode::Jump(block_id, args.len() as u8);
                let jump_value = self.push_code(code, scope_id, AstType::Unit);
                for a in args {
                    let v = self.add(scope_id, a, b, d)?;
                    self.push_code(LCode::Value(v), scope_id, self.get_type(v));
                }
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

                let code = LCode::Return(count);
                let v = self.push_code(code, scope_id, AstType::Unit);

                // args
                if let Some(ret_value) = maybe_ret_value {
                    self.push_code(LCode::Value(ret_value), scope_id, self.get_type(ret_value));
                }
                Ok(v)
            }

            _ => unimplemented!("{:?}", node.node),
        }
    }
}
