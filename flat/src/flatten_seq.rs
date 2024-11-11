use anyhow::Error;
use anyhow::Result;
use compile_core::{Argument, Ast, AstNode, SpanId, StringKey};

use crate::{BlockifyError, NodeBuilder as NB};

pub fn resolve_attribute(
    ident: StringKey,
    attr: &AstNode,
    span_id: SpanId,
    args: Vec<Argument>,
    b: &mut NB,
) -> Result<AstNode> {
    let attr_name = b.labels.r(ident.into());
    // This is where we should check for comptime functions and resolve them
    // We are taking a shortcut for now.
    match &attr.node {
        Ast::Identifier(base) => {
            let name = b.labels.r(base.into());
            if &name == "q" {
                if let Some(ast) = b.build_builtin_from_name(&attr_name, args, span_id) {
                    Ok(ast)
                } else {
                    b.push_error_labels(vec![
                        b.primary_label(&format!("Builtin not found: {}", &name), attr.span_id)
                    ]);
                    Err(Error::new(BlockifyError::Invalid))
                }
            } else {
                unimplemented!("{}.{}", name, attr_name)
                //let ident_span_id = env.span_id(ident.span, b);
                //let ident = Ast::Identifier(key).node(ident_span_id);
                //let ast = Ast::Call(ident.into(), args).node(span_id.clone());
                //Ok(ast)
            }
        }
        _ => unimplemented!("{:?}", attr),
    }
}
