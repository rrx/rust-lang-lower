use anyhow::Error;
use anyhow::Result;

use crate::cfg::{CFGGraph, CFG};
use crate::{AstNode, AstType, Diagnostics, Extra, NodeBuilder, NodeID, ParseError, StringKey};
use melior::{ir::Location, Context};
use std::fmt::Debug;

use crate::ast::{
    Ast, BinaryOperation, Builtin, DerefTarget, Literal, Parameter, ParameterNode, UnaryOperation,
};

use crate::op;

use petgraph::graph::NodeIndex;
use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Debug)]
pub enum IRTypeSelect {
    // array offset
    Offset(usize),
    // attribute select on tuple
    Attr(usize),
    // byte level view (width, offset)
    Byte(u8, usize),
}

impl Default for IRTypeSelect {
    fn default() -> Self {
        Self::Offset(0)
    }
}
#[derive(Debug)]
pub struct IRArg {
    name: StringKey,
    ty: AstType,
}

#[derive(Debug)]
pub enum IRKind {
    Decl(StringKey, AstType),
    // set(variable, expr, type offset)
    Set(StringKey, Box<IRNode>, IRTypeSelect),
    // get(variable, type offset)
    Get(StringKey, IRTypeSelect),
    // ret(args)
    Ret(Vec<IRNode>),
    Cond(Box<IRNode>, Box<IRNode>, Option<Box<IRNode>>),
    Jump(StringKey, Vec<IRNode>),
    // call(variable, args), return type is inferred from variable
    Call(StringKey, Vec<IRNode>),
    // op(operation, args)
    Op1(UnaryOperation, Box<IRNode>),
    Op2(BinaryOperation, Box<IRNode>, Box<IRNode>),
    Block(StringKey, Vec<IRArg>, Vec<IRNode>),
    Seq(Vec<IRNode>),
    Noop,
}

#[derive(Debug)]
pub struct IRNode {
    kind: IRKind,
    loc: usize,
}

impl IRNode {
    pub fn new(kind: IRKind) -> Self {
        Self { kind, loc: 0 }
    }
    pub fn to_vec(self) -> Vec<Self> {
        if let IRKind::Seq(exprs) = self.kind {
            exprs
        } else {
            vec![self]
        }
    }
}

impl<E: Extra> AstNode<E> {
    pub fn lower_ir<'c>(
        self,
        context: &'c Context,
        d: &mut Diagnostics,
        cfg: &mut CFG<'c, E>,
        stack: &mut Vec<NodeIndex>,
        g: &mut CFGGraph<'c>,
        b: &mut NodeBuilder<E>,
    ) -> Result<IRNode> {
        if !self.node_id.is_valid() {
            d.push_diagnostic(self.extra.error(&format!("Invalid NodeID: {:#?}", self)));
            return Err(Error::new(ParseError::Invalid));
        }

        match self.node {
            Ast::Noop => Ok(b.ir_noop()),
            Ast::Sequence(exprs) => {
                let mut out = vec![];
                for expr in exprs {
                    out.extend(expr.lower_ir(context, d, cfg, stack, g, b)?.to_vec());
                }
                Ok(b.ir_seq(out))
            }
            _ => unimplemented!(),
        }
    }
}
