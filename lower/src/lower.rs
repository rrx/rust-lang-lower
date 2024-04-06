use crate::ast::*;
use crate::scope::{Layer, LayerIndex, LayerType};
use crate::{op, Environment, NodeBuilder};
use crate::{Diagnostics, ParseError};
use anyhow::Error;
use anyhow::Result;
use melior::{
    dialect::{arith, cf, func, llvm, memref, ods, scf},
    ir::{
        attribute::{
            //DenseElementsAttribute,
            FloatAttribute,
            IntegerAttribute,
            StringAttribute,
            TypeAttribute,
        },
        r#type::{
            FunctionType,
            IntegerType,
            MemRefType,
            //RankedTensorType
        },
        *,
    },
    Context,
};
use std::collections::HashSet;

#[derive(Debug, Clone)]
pub struct Data {
    ty: AstType,
    static_name: Option<String>,
}

impl Data {
    pub fn new_static(ty: AstType, name: &str) -> Self {
        Self {
            ty,
            static_name: Some(name.to_string()),
        }
    }

    pub fn new(ty: AstType) -> Self {
        Self {
            ty,
            static_name: None,
        }
    }
}

pub struct Lower<'c, E> {
    pub(crate) context: &'c Context,
    pub pass_manager: melior::pass::PassManager<'c>,
    pub shared: HashSet<String>,
    _e: std::marker::PhantomData<E>,
}

pub fn layer_in_scope<'c, E: Extra>(
    context: &'c Context,
    layer_type: LayerType,
    body: AstNode<E>,
    d: &mut Diagnostics,
    _b: &NodeBuilder<E>,
) -> Result<Layer<'c, E>> {
    let mut layer = Layer::new(layer_type);

    let blocks = if body.is_seq() {
        body.try_seq().unwrap()
    } else {
        vec![body]
    };

    // load nodes
    for expr in blocks.into_iter() {
        if let Ast::Block(nb) = expr.node {
            log::debug!("block node: {:?}", nb.body.node);
            log::debug!(
                "block terminator: {}: {:?}",
                nb.name,
                nb.body.node.terminator()
            );

            // ensure we have a terminator
            if nb.body.node.terminator().is_none() {
                d.push_diagnostic(nb.body.extra.error("Block does not terminate"));
                return Err(Error::new(ParseError::Invalid));
            }

            layer.push_block(context, &nb.name, nb.params, *nb.body, d);
        } else {
            unreachable!()
        }
    }
    Ok(layer)
}

pub fn new_block<'c, E: Extra>(
    context: &'c Context,
    arguments: &[ParameterNode<E>],
    d: &Diagnostics,
) -> Block<'c> {
    let block_args = arguments
        .iter()
        .map(|a| (from_type(context, &a.ty), a.extra.location(context, d)))
        .collect::<Vec<_>>();
    Block::new(&block_args)
}


#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::default_context;
    use crate::NodeBuilder;
    use test_log::test;

}
