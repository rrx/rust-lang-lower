use crate::{
    Argument, Ast, AstNode, AstNodeBlock, AstType, BinaryOperation, Diagnostics, Extra,
    NodeBuilder, ParameterNode, StringKey, UnaryOperation,
};
use anyhow::Error;
use anyhow::Result;
use std::collections::{HashMap, HashSet};

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
}

impl Environment {
    pub fn new() -> Self {
        let start = Layer::default();
        Self {
            in_func: false,
            layers: vec![start],
        }
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
            _ => AstType::Unit,
        }
    }
}

impl<E: Extra> AstNode<E> {
    pub fn first_pass(mut self, b: &mut NodeBuilder<E>, d: &mut Diagnostics) -> Result<Self> {
        let mut env = Environment::new();
        self.run_first_pass(&mut env, b, d)
    }

    fn run_first_pass(
        mut self,
        env: &mut Environment,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<Self> {
        match self.node {
            Ast::Module(mut block) => {
                let mut children = vec![];
                for c in block.children {
                    children.push(c.run_first_pass(env, b, d)?);
                }
                block.children = children;
                self.node = Ast::Module(block);
                Ok(self)
            }

            Ast::Definition(def) => {
                //if let Some(body) = def.body {
                //blockify(body.to_vec(), def.name, def.params, b, d);
                //}
                self.node = Ast::Definition(def.normalize(b));
                Ok(self)
            }
            Ast::Sequence(exprs) => {
                let mut out = vec![];
                for expr in exprs {
                    out.extend(expr.run_first_pass(env, b, d)?.to_vec());
                }
                self.node = Ast::Sequence(out);
                Ok(self)
            }
            _ => Ok(self),
        }
    }
}

fn terminate_seq<E: Extra>(
    mut exprs: Vec<AstNode<E>>,
    b: &mut NodeBuilder<E>,
    d: &mut Diagnostics,
) -> Result<(Vec<AstNode<E>>, Vec<AstNode<E>>)> {
    // split the sequence on terminator, and return a tuple (terminated sequence, remainder)
    if let Some(index) = exprs.iter().position(|expr| expr.node.is_terminator()) {
        let rest = exprs.split_off(index);
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

/*
pub fn blockify<E: Extra>(mut block: AstNodeBlock<E>, b: &mut NodeBuilder<E>, d: &mut Diagnostics) -> Result<Vec<AstNodeBlock<E>>> {
    let mut children = block.children;
    let mut out = vec![];
    let (seq, rest) = terminate_seq(children, b, d)?;

    if rest.len() == 0 {
        let block = AstNodeBlock {
            name: block_name,
            params: block_params,
            children: seq,
        };
        return
    } else {
        // the previous block return arity, should match the new block arity
    }

    /*
    if let Some(index) = children.iter().position(|expr| expr.node.is_terminator()) {
        let rest = children.split_off(index);
        if rest.len() == 0 {
            // last element is a terminator
            return Ok(out);
        } else {
        }
    }
    */

    // implicit return, ensure it matches the function signature
    //children.push(b.ret(None));
    //block.children = children;
    //out.push(block);
    Ok(out)
}
*/

/*
pub fn blockify2<E: Extra>(exprs: Vec<AstNode<E>>, entry_name: StringKey, entry_params: Vec<ParameterNode<E>>, b: &mut NodeBuilder<E>, d: &mut Diagnostics) -> Result<Vec<AstNode<E>>> {
    let mut blocks = vec![];
    let mut current = exprs;
    let mut names = vec![];
    loop {
        if current.len() == 0 {
            break;
        }
        let index = current.iter().position(|expr| expr.node.is_terminator());
        let rest = if let Some(index) = index {
            let rest = current.split_off(index);
            rest
        } else {
            vec![]
        };

        let first = current.first().unwrap();

        let mut current_names = HashSet::new();
        let (block_name, block_params) = if let Ast::Label(key, first_params) = &first.node {
            current_names.insert(key);
            if blocks.len() == 0 {
                // on the first blocks
                //assert_eq!(first_params.len(), entry_params.len());
                current_names.insert(&entry_name);
            }
            (*key, first_params.clone())
        } else {
            if blocks.len() == 0 {
                (entry_name, entry_params.clone())
            } else {
                let name = format!("_block{}", blocks.len());
                let key = b.s(&name);
                (key, vec![])
            }
        };


        let block = AstNodeBlock {
            name: block_name,
            params: block_params,
            children: current,
        };
        blocks.push(b.node(Ast::Block(block)));
        names.push(current_names);

        current = rest;
    }
    Ok(blocks)
}
*/

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
}
