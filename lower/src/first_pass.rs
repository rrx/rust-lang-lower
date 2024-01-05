use crate::{
    //Argument,
    Ast,
    AstNode,
    AstNodeBlock,
    AstType,
    BinaryOperation,
    Diagnostics,
    Extra,
    NodeBuilder,
    Span,
    //ParameterNode,
    StringKey,
    TypeUnify,
    UnaryOperation,
};
use anyhow::Result;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub enum DataType {
    Global,
    Local,
}

#[derive(Debug, Clone)]
pub struct Data {
    ty: AstType,
}

impl Data {
    pub fn new(ty: AstType) -> Self {
        Data { ty }
    }
}

#[derive(Debug)]
pub struct Layer {
    names: HashMap<StringKey, Data>,
}
impl Default for Layer {
    fn default() -> Self {
        Self {
            names: HashMap::new(),
        }
    }
}

#[derive(Debug)]
pub struct Environment {
    in_func: bool,
    layers: Vec<Layer>,
    unique: usize,
}

impl Environment {
    pub fn new() -> Self {
        let start = Layer::default();
        Self {
            in_func: false,
            layers: vec![start],
            unique: 0,
        }
    }

    pub fn gen_unique(&mut self) -> usize {
        let s = self.unique;
        self.unique += 1;
        s
    }

    pub fn enter_scope(&mut self) {
        self.layers.push(Layer::default());
    }

    pub fn exit_scope(&mut self) {
        self.layers.pop().unwrap();
    }

    pub fn define(&mut self, name: StringKey, ty: AstType) {
        let data = Data::new(ty);
        self.layers.last_mut().unwrap().names.insert(name, data);
    }

    pub fn resolve(&self, name: StringKey) -> Option<Data> {
        for layer in self.layers.iter().rev() {
            return layer.names.get(&name).cloned();
        }
        None
    }

    pub fn dump(&self) {
        println!("{:?}", self);
    }
}

impl<E: Extra> Ast<E> {
    pub fn terminator_types(&self, env: &Environment) -> Vec<AstType> {
        match self {
            Ast::Sequence(exprs) => exprs.last().unwrap().node.terminator_types(env),
            Ast::Block(block) => block.children.last().unwrap().node.terminator_types(env),
            Ast::Goto(_, args) => args.iter().map(|a| a.node.get_type(env)).collect(),
            _ => vec![],
        }
    }

    pub fn get_type(&self, env: &Environment) -> AstType {
        match self {
            Ast::Literal(lit) => lit.into(),
            Ast::BinaryOp(op, a, b) => match op.node {
                BinaryOperation::NE => AstType::Bool,
                BinaryOperation::EQ => AstType::Bool,
                BinaryOperation::GT => AstType::Bool,
                BinaryOperation::GTE => AstType::Bool,
                _ => a.node.get_type(env),
            },
            Ast::UnaryOp(op, a) => match op {
                UnaryOperation::Minus => a.node.get_type(env),
            },
            Ast::Call(_, _, ty) => ty.clone(),
            Ast::Identifier(key) => {
                if let Some(data) = env.resolve(*key) {
                    data.ty
                } else {
                    unreachable!()
                }
            }
            Ast::Sequence(exprs) => exprs.last().unwrap().node.get_type(env),
            Ast::Definition(def) => {
                let params = def.params.iter().map(|p| p.ty.clone()).collect();
                AstType::Func(params, def.return_type.clone())
            }
            Ast::Global(_, a) => a.node.get_type(env),
            Ast::Conditional(_, a, b) => {
                let a_ty = a.node.get_type(env);
                if let Some(b) = b {
                    let _b_ty = b.node.get_type(env);
                }
                a_ty
            }
            Ast::Block(block) => block.children.last().unwrap().node.get_type(env),
            Ast::Break(_, args) | Ast::Continue(_, args) | Ast::Goto(_, args) => {
                let mut types = args
                    .iter()
                    .map(|a| a.node.get_type(env))
                    .collect::<Vec<_>>();
                if types.len() == 0 {
                    AstType::Unit
                } else if types.len() == 1 {
                    types.pop().unwrap()
                } else {
                    AstType::Tuple(types)
                }
            }

            // return has the never type, because it never returns an expression, it returns before
            Ast::Return(_) => AstType::Never,

            _ => AstType::Unit,
        }
    }
}

pub fn unify(x: &AstType, y: &AstType, spans: &[Span], types: &mut TypeUnify, d: &mut Diagnostics) {
    use codespan_reporting::diagnostic::{Diagnostic, Label};
    if types.unify(x, y).is_err() {
        let labels = spans
            .iter()
            .map(|span| {
                let r = span.begin.pos as usize..span.end.pos as usize;
                Label::primary(span.file_id, r).with_message("Type mismatch")
            })
            .collect();
        let diagnostic = Diagnostic::error()
            .with_labels(labels)
            .with_message("error");
        d.push_diagnostic(diagnostic);
    }
}

impl<E: Extra> AstNode<E> {
    pub fn first_pass(self, b: &mut NodeBuilder<E>, d: &mut Diagnostics) -> Result<Self> {
        let mut env = Environment::new();
        let mut types = TypeUnify::new();
        self.run_first_pass(&mut env, &mut types, b, d)
    }

    fn run_first_pass(
        mut self,
        env: &mut Environment,
        types: &mut TypeUnify,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<Self> {
        match self.node {
            Ast::Module(mut block) => {
                let mut children = vec![];
                for c in block.children {
                    children.push(c.run_first_pass(env, types, b, d)?);
                }
                block.children = children;
                self.node = Ast::Module(block);
                Ok(self)
            }

            Ast::Definition(mut def) => {
                if let Some(body) = def.body.take() {
                    let body = body.run_first_pass(env, types, b, d)?;

                    let block = AstNodeBlock {
                        name: def.name,
                        params: def.params.clone(),
                        children: body.to_vec(),
                    };
                    let blocks = blockify(block, env, b, d)?
                        .into_iter()
                        .map(|block| b.node(Ast::Block(block)))
                        .collect::<Vec<_>>();
                    let seq = b.node(Ast::Sequence(blocks));
                    def.body = Some(seq.into());
                    Ok(b.node(Ast::Definition(def)))
                } else {
                    Ok(b.node(Ast::Definition(def)))
                }
                //self.node = Ast::Definition(def.normalize(b));
            }
            Ast::Sequence(exprs) => {
                let mut out = vec![];
                for expr in exprs {
                    out.extend(expr.run_first_pass(env, types, b, d)?.to_vec());
                }
                self.node = Ast::Sequence(out);
                Ok(self)
            }

            Ast::Conditional(ref condition, ref then_expr, ref maybe_else_expr) => {
                let ty = condition.node.get_type(env);

                unify(&ty, &AstType::Bool, &[condition.extra.get_span()], types, d);

                if let Some(else_expr) = maybe_else_expr {
                    let then_ty = then_expr.node.get_type(env);
                    let else_ty = else_expr.node.get_type(env);
                    unify(
                        &then_ty,
                        &else_ty,
                        &[then_expr.extra.get_span(), else_expr.extra.get_span()],
                        types,
                        d,
                    );
                }
                Ok(self)
            }
            _ => Ok(self),
        }
    }
}

fn terminate_seq<E: Extra>(
    mut exprs: Vec<AstNode<E>>,
    env: &mut Environment,
    b: &mut NodeBuilder<E>,
    d: &mut Diagnostics,
) -> Result<(Vec<AstNode<E>>, Vec<AstNode<E>>)> {
    // split the sequence on terminator, and return a tuple (terminated sequence, remainder)
    if let Some(index) = exprs.iter().position(|expr| expr.node.is_terminator()) {
        let rest = exprs.split_off(index + 1);
        return Ok((exprs, rest));
    }

    // if the sequence does not end in a terminator, then we have an implied return
    // if we end in an expression, we return the expression, otherwise we return None
    let last = exprs.last().unwrap();
    if last.node.is_expr() {
        let last = exprs.pop().unwrap();
        let extra = last.extra.clone();
        exprs.push(b.node(Ast::Return(Some(last.into()))).set_extra(extra));
    } else {
        exprs.push(b.ret(None));
    }
    Ok((exprs, vec![]))
}

pub fn ensure_terminate<E: Extra>(
    mut exprs: Vec<AstNode<E>>,
    next_key: StringKey,
    b: &mut NodeBuilder<E>,
) -> Vec<AstNode<E>> {
    // if the last node is not a terminator, then we add one
    let last = exprs.last().unwrap();
    if !last.node.is_terminator() {
        let last = exprs.pop().unwrap();
        let extra = last.extra.clone();
        exprs.push(b.node(Ast::Goto(next_key, vec![])).set_extra(extra));
    }
    exprs
}

pub fn blockify_cond<E: Extra>(
    condition: AstNode<E>,
    then_expr: AstNode<E>,
    maybe_else_expr: Option<AstNode<E>>,
    env: &mut Environment,
    next_key: StringKey,
    b: &mut NodeBuilder<E>,
    d: &mut Diagnostics,
) -> Result<(Vec<AstNode<E>>, Vec<AstNodeBlock<E>>)> {
    let mut seq = vec![];
    let mut blocks = vec![];

    let then_name = format!("then_block{}", env.gen_unique());
    let key = b.s(&then_name);
    let then_block_name = key;
    let then_block = AstNodeBlock {
        name: then_block_name,
        params: vec![],
        children: ensure_terminate(then_expr.to_vec(), next_key, b),
    };
    blocks.push(then_block);

    let else_block_name = if let Some(else_expr) = maybe_else_expr {
        let else_name = format!("else_block{}", env.gen_unique());
        let key = b.s(&else_name);
        let else_block = AstNodeBlock {
            name: key,
            params: vec![],
            children: ensure_terminate(else_expr.to_vec(), next_key, b),
        };
        blocks.push(else_block);
        key
    } else {
        next_key
    };

    seq.push(b.node(Ast::Branch(
        condition.into(),
        then_block_name,
        else_block_name,
    )));
    Ok((seq, blocks))
}

pub fn blockify<E: Extra>(
    mut block: AstNodeBlock<E>,
    env: &mut Environment,
    b: &mut NodeBuilder<E>,
    d: &mut Diagnostics,
) -> Result<Vec<AstNodeBlock<E>>> {
    let children = block.children;
    let mut out = vec![];
    let (seq, rest) = terminate_seq(children, env, b, d)?;
    //println!("seq {:?}", seq);
    //println!("rest {:?}", rest);

    let ty = seq.last().unwrap().node.get_type(env);
    let mut block_children = vec![];

    // if label is missing, add it
    if !seq.first().unwrap().node.is_label() {
        block_children.push(b.label(block.name, block.params.clone()));
    }

    block_children.extend(seq);

    let (next_key, next_blocks) = if rest.len() > 0 {
        let block_params = match ty {
            AstType::Unit => vec![],
            AstType::Tuple(types) => vec![],
            _ => unimplemented!(),
        };

        let block = if let Ast::Label(ref key, ref params) = rest.first().unwrap().node {
            AstNodeBlock {
                name: *key,
                params: params.clone(),
                children: rest,
            }
        } else {
            let name = format!("_block{}", env.gen_unique());
            let key = b.s(&name);
            AstNodeBlock {
                name: key,
                params: block_params,
                children: rest,
            }
        };

        let key = block.name;
        let next_blocks = blockify(block, env, b, d)?;
        (Some(key), next_blocks)
    } else {
        (None, vec![])
    };

    let last = block_children.pop().unwrap();
    match last.node {
        Ast::Conditional(condition, then_expr, maybe_else_expr) => {
            let (seq, seq_blocks) = blockify_cond(
                *condition,
                *then_expr,
                maybe_else_expr.map(|e| *e),
                env,
                next_key.unwrap(),
                b,
                d,
            )?;
            block_children.extend(seq);
            out.extend(seq_blocks);
        }
        _ => block_children.push(last),
    }
    block.children = block_children;
    out.push(block);
    out.extend(next_blocks);
    Ok(out)
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
}
