use anyhow::Result;
//use codespan_reporting::diagnostic::{Diagnostic, Label};
//use indexmap::IndexMap;

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
    ParameterNode,
    PlaceId,
    PlaceNode,
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

#[derive(Debug)]
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
    Load(PlaceId),
    Store(PlaceId, ValueId),
    Return(u8), // return values
    Jump(BlockId, u8),
    Branch(ValueId, BlockId, BlockId),
    Ternary(ValueId, BlockId, BlockId),
    Builtin(Builtin, u8, u8),
    Call(PlaceId, u8, u8),
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

    pub fn dump<E: Extra>(&self, pos: usize, depth: usize, env: &Environment, b: &NodeBuilder<E>) {
        match self {
            Self::DeclareFunction(block_id) => {
                println!(
                    "%{} = {:width$}declare_function({})",
                    pos,
                    "",
                    b.resolve_block_label(*block_id),
                    width = depth * 2
                );
            }
            Self::Label(block_id, args, kwargs) => {
                println!(
                    "%{} = {:width$}label({}, {}, {})",
                    pos,
                    "",
                    b.resolve_block_label(*block_id),
                    args,
                    kwargs,
                    width = depth * 2
                );
            }
            Self::Jump(block_id, args) => {
                println!(
                    "%{} = {:width$}jump({}, {})",
                    pos,
                    "",
                    b.resolve_block_label(*block_id),
                    args,
                    width = depth * 2
                );
            }
            //Self::Label(block_id, _args, _kwargs) => {
            //let index = env.blocks.lookup_block_label(*block_id).unwrap();
            //let _block = env.blocks.g.node_weight(index).unwrap();
            //env.blocks.dump_node(b, index, index, depth);
            //println!("{:width$}label({:?}", "", b.resolve_block_label(block.name.into()), width = depth * 2);
            //}
            _ => {
                println!("%{} = {:width$}{:?}", pos, "", self, width = depth * 2);
            }
        }
    }
}

pub fn dump_codes<E: Extra>(codes: &[LCode], env: &Environment, b: &NodeBuilder<E>) {
    let mut pos = 0;
    let depth = 0;
    loop {
        codes[pos].dump(pos, depth, env, b);
        pos += 1;
        if pos == codes.len() {
            break;
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
pub struct Blockify<E> {
    code: Vec<LCode>,
    place: Vec<Option<PlaceNode>>,
    pending_blocks: Vec<(ScopeId, AstNode<E>)>,
    loop_stack: Vec<LoopLayer>,
}

impl<E: Extra> Blockify<E> {
    pub fn new() -> Self {
        Self {
            code: vec![],
            place: vec![],
            pending_blocks: vec![],
            loop_stack: vec![],
        }
    }

    pub fn dump(&self, env: &Environment, b: &NodeBuilder<E>) {
        dump_codes(&self.code, env, b);
    }

    pub fn push_code(&mut self, code: LCode, place: Option<PlaceNode>) -> ValueId {
        let offset = self.code.len();
        self.code.push(code);
        self.place.push(place);
        ValueId(offset as u32)
    }

    pub fn get_place(&self, v: ValueId) -> &PlaceNode {
        self.place.get(v.0 as usize).unwrap().as_ref().unwrap()
    }

    pub fn build(
        &mut self,
        node: AstNode<E>,
        env: &mut Environment,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        let scope_id = env.enter_scope();
        self.add(scope_id, node, env, b, d)?;
        //env.exit_scope();
        let nodes = self.pending_blocks.drain(..).collect::<Vec<_>>();
        for (scope_id, ast) in nodes {
            self.add(scope_id, ast, env, b, d)?;
        }
        Ok(())
    }

    pub fn add(
        &mut self,
        scope_id: ScopeId,
        node: AstNode<E>,
        env: &mut Environment,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<ValueId> {
        match node.node {
            Ast::Module(block) => {
                let value_id = self.push_code(LCode::Label(block.name, 0, 0), None);

                for c in block.children.into_iter() {
                    self.add(scope_id, c, env, b, d)?;
                }
                Ok(value_id)
            }

            Ast::Sequence(exprs) => {
                let mut value_id = None;
                for c in exprs.into_iter() {
                    value_id = Some(self.add(scope_id, c, env, b, d)?);
                }
                Ok(value_id.unwrap())
            }

            Ast::Definition(def) => {
                let params = def.params.iter().map(|p| p.ty.clone()).collect();
                let ty = AstType::Func(params, def.return_type);
                let p = PlaceNode::new_static(def.name, ty.clone());
                //let place_id = self.place.push(p);
                env.define(env.current_scope(), def.name, ty);
                if let Some(body) = def.body {
                    let scope_id = env.dependent_scope(scope_id);
                    let seq = vec![
                        b.node(Ast::Label(def.name.into(), def.params.clone())),
                        *body,
                    ];
                    self.pending_blocks.push((scope_id, b.seq(seq)));
                    //env.exit_scope();
                }
                Ok(self.push_code(LCode::DeclareFunction(def.name.into()), Some(p)))
            }

            Ast::Label(block_id, params) => {
                //env.enter_block(
                let v = self.push_code(LCode::Label(block_id, 0, params.len() as u8), None);
                for p in params {
                    self.push_code(LCode::NamedArg(p.name.into()), None);
                }
                Ok(v)
            }

            Ast::Assign(target, expr) => {
                let name = match target {
                    AssignTarget::Identifier(name) | AssignTarget::Alloca(name) => name,
                };

                println!("expr: {:?}", expr);
                let v = self.add(scope_id, *expr, env, b, d)?;
                let ty = self.get_place(v).ty.clone();
                let p = PlaceNode::new_stack(name.into(), ty.clone());
                env.define(env.current_scope(), name, ty);
                Ok(self.push_code(LCode::Declare, Some(p)))
            }

            Ast::Builtin(bi, args) => {
                let _ty = bi.get_return_type();
                let args_size = args.len();
                assert_eq!(args_size, bi.arity());
                let mut values = vec![];
                for a in args.into_iter() {
                    let Argument::Positional(expr) = a;
                    let v = self.add(scope_id, *expr, env, b, d)?;
                    values.push(v);
                }
                let value_id = self.push_code(LCode::Builtin(bi, args_size as u8, 0), None);
                for v in values {
                    self.push_code(LCode::Value(v), None);
                }
                Ok(value_id)
            }

            Ast::Literal(lit) => {
                let ty: AstType = lit.clone().into();
                let name = b.labels.fresh_var_id();
                let p = PlaceNode::new(name, ty, VarDefinitionSpace::Reg);
                Ok(self.push_code(LCode::Const(lit), Some(p)))
            }

            //Ast::Identifier(label) => {
            //}
            Ast::UnaryOp(op, x) => {
                let vx = self.add(scope_id, *x, env, b, d)?;
                let code = LCode::Op1(op, vx);
                Ok(self.push_code(code, None))
            }

            Ast::Ternary(c, x, y) => {
                let then_scope_id = env.dependent_scope(scope_id);
                let then_block_id = b.labels.fresh_block_id();
                let seq = vec![b.node(Ast::Label(then_block_id, vec![])), *x];
                let ty = AstType::unknown(0);
                let ast = b.seq(seq);
                self.add(then_scope_id, ast, env, b, d)?;
                //self.pending_blocks.push((then_scope_id, b.seq(seq)));
                //env.exit_scope();

                let else_scope_id = env.dependent_scope(scope_id);
                let else_block_id = b.labels.fresh_block_id();
                let seq = vec![b.node(Ast::Label(else_block_id, vec![])), *y];
                //self.pending_blocks.push((else_scope_id, b.seq(seq)));
                let ty = AstType::unknown(0);
                let ast = b.seq(seq);
                self.add(else_scope_id, ast, env, b, d)?;
                //env.exit_scope();

                //let condition_scope_id = env.dependent_scope(then_scope_id);
                // condition
                let p = PlaceNode::new(b.labels.fresh_var_id(), ty, VarDefinitionSpace::Reg);
                let v = self.add(scope_id, *c, env, b, d)?;
                let code = LCode::Ternary(v, then_block_id, else_block_id);
                Ok(self.push_code(code, Some(p)))
            }

            Ast::BinaryOp(op, x, y) => {
                let vx = self.add(scope_id, *x, env, b, d)?;
                let vy = self.add(scope_id, *y, env, b, d)?;
                let code = LCode::Op2(op.node, vx, vy);
                Ok(self.push_code(code, None))
            }

            Ast::Goto(block_id, args) => {
                let code = LCode::Jump(block_id, args.len() as u8);
                let jump_value = self.push_code(code, None);
                for a in args {
                    let v = self.add(scope_id, a, env, b, d)?;
                    self.push_code(LCode::Value(v), None);
                }
                Ok(jump_value)
            }

            Ast::Return(maybe_expr) => {
                let count = if maybe_expr.is_some() { 1 } else { 0 };
                let code = LCode::Return(count);
                let v = self.push_code(code, None);
                if let Some(expr) = maybe_expr {
                    let expr_value_id = self.add(scope_id, *expr, env, b, d)?;
                    self.push_code(LCode::Value(expr_value_id), None);
                }
                Ok(v)
            }

            _ => unimplemented!("{:?}", node.node),
        }
    }

    /*
    pub fn build_block(
        &mut self,
        node: AstNode<E>,
        name: StringKey,
        params: Vec<ParameterNode<E>>,
        //places: &mut IRPlaceTable,
        env: &mut Environment,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        let seq = node.to_vec();
        if !seq.first().unwrap().node.is_label() {
            self.code
                .push(LCode::Label(name.into(), 0, params.len() as u8));
            for p in params {
                self.code.push(LCode::NamedArg(p.name));
            }
        }
        for n in seq {
            self.add(scope_id, n, env, b, d)?;
        }
        Ok(())
    }
    */
}
