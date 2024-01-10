use anyhow::Result;
//use codespan_reporting::diagnostic::{Diagnostic, Label};
//use indexmap::IndexMap;
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
    VarDefinitionSpace,
};

use crate::{Environment, ScopeId};

#[derive(Debug)]
pub struct AstBlock {
    name: BlockId,
}

#[derive(Debug)]
pub struct LoopLayer {
    next: BlockId,
    restart: BlockId,
}

#[derive(Debug, Copy, Clone)]
pub struct ValueId(u32);

#[derive(Debug)]
pub enum LCode {
    Label(BlockId, u8, u8), // BlockId, number of positional arguments, number of named arguments
    Declare,
    DeclareFunction(BlockId), // block_id of entry point
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
    Ternary(ValueId, BlockId, BlockId),
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

    pub fn to_string<E: Extra>(&self, env: &Environment, b: &NodeBuilder<E>) -> String {
        match self {
            Self::DeclareFunction(block_id) => {
                format!("declare_function({})", b.resolve_block_label(*block_id))
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
}

#[derive(Tabled)]
struct CodeRow<'a> {
    pos: usize,
    value: String,
    ty: &'a AstType,
}

pub fn dump_codes<E: Extra>(
    codes: &[LCode],
    types: &[AstType],
    env: &Environment,
    b: &NodeBuilder<E>,
) {
    let mut pos = 0;
    let depth = 0;
    let mut out = vec![];
    loop {
        let code = codes.get(pos).unwrap();
        let ty = types.get(pos).unwrap();
        code.dump(pos, ty, depth, env, b);
        out.push(CodeRow {
            pos,
            value: code.to_string(env, b),
            ty,
        });
        pos += 1;
        if pos == codes.len() {
            break;
        }
    }
    use tabled::settings::Style;
    println!("{}", Table::new(out).with(Style::sharp()).to_string());
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
    next_pos: Vec<usize>,
    prev_pos: Vec<usize>,
    //place: Vec<Option<PlaceNode>>,
    loop_stack: Vec<LoopLayer>,
    env: Environment,
}

impl Blockify {
    pub fn new() -> Self {
        Self {
            code: vec![],
            types: vec![],
            next_pos: vec![],
            prev_pos: vec![],
            //place: vec![],
            loop_stack: vec![],
            env: Environment::new(),
        }
    }

    pub fn dump<E: Extra>(&self, b: &NodeBuilder<E>) {
        dump_codes(&self.code, &self.types, &self.env, b);
        self.env.dump(b);
    }

    pub fn push_code(&mut self, code: LCode, scope_id: ScopeId, ty: AstType) -> ValueId {
        let offset = self.code.len();
        self.code.push(code);
        self.types.push(ty);
        //self.place.push(place);
        ValueId(offset as u32)
    }

    pub fn get_type(&self, v: ValueId) -> AstType {
        self.types.get(v.0 as usize).unwrap().clone()
    }

    //pub fn get_place(&self, v: ValueId) -> &PlaceNode {
    //self.place.get(v.0 as usize).unwrap().as_ref().unwrap()
    //}

    pub fn build<E: Extra>(
        &mut self,
        node: AstNode<E>,
        //env: &mut Environment,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        let scope_id = self.env.enter_scope();
        self.add(scope_id, node, b, d)?;
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
                //let p = PlaceNode::new_static(def.name, ty.clone());
                //let place_id = self.place.push(p);
                self.env
                    .define(self.env.current_scope(), def.name, ty.clone());
                if let Some(body) = def.body {
                    let body_scope_id = self.env.dependent_scope(scope_id);
                    let seq = vec![
                        b.node(Ast::Label(def.name.into(), def.params.clone())),
                        *body,
                    ];
                    self.add(body_scope_id, b.seq(seq), b, d)?;
                    //self.pending_blocks.push((scope_id, b.seq(seq)));
                }
                Ok(self.push_code(LCode::DeclareFunction(def.name.into()), scope_id, ty))
            }

            Ast::Label(block_id, params) => {
                //env.enter_block(
                let v = self.push_code(
                    LCode::Label(block_id, 0, params.len() as u8),
                    scope_id,
                    AstType::Unit,
                );
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
                self.env.define(self.env.current_scope(), name, ty.clone());
                Ok(self.push_code(LCode::Declare, scope_id, ty))
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
                let name = b.labels.fresh_var_id();
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
                let then_scope_id = self.env.dependent_scope(scope_id);
                let then_block_id = b.labels.fresh_block_id();
                let seq = vec![b.node(Ast::Label(then_block_id, vec![])), *x];
                let ty = AstType::unknown(0);
                let ast = b.seq(seq);
                self.add(then_scope_id, ast, b, d)?;
                //self.pending_blocks.push((then_scope_id, b.seq(seq)));
                //env.exit_scope();

                let else_scope_id = self.env.dependent_scope(scope_id);
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
                let code = LCode::Ternary(v, then_block_id, else_block_id);
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
                Ok(jump_value)
            }

            Ast::Return(maybe_expr) => {
                let count = if maybe_expr.is_some() { 1 } else { 0 };
                let code = LCode::Return(count);
                let v = self.push_code(code, scope_id, AstType::Unit);
                if let Some(expr) = maybe_expr {
                    let expr_value_id = self.add(scope_id, *expr, b, d)?;
                    self.push_code(
                        LCode::Value(expr_value_id),
                        scope_id,
                        self.get_type(expr_value_id),
                    );
                }
                Ok(v)
            }

            _ => unimplemented!("{:?}", node.node),
        }
    }
}
