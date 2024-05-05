use compile_core::{Ast, StringKey};
use std::fmt::Debug;

#[derive(Debug)]
pub enum Terminator {
    Jump(StringKey),
    Branch(StringKey, StringKey),
    Return,
}

impl Terminator {
    pub fn from_ast(item: &Ast) -> Option<Self> {
        match item {
            Ast::Sequence(exprs) => Terminator::from_ast(&exprs.last().unwrap().node),
            //Self::Block(nb) => nb.children.last().unwrap().node.terminator(),
            Ast::Goto(key) => Some(Self::Jump(*key)),
            Ast::Return(_) => Some(Self::Return),
            _ => None,
        }
    }
}
