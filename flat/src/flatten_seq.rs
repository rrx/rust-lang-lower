use compile_core::{Argument, Ast, AstNode, SpanId, StringKey};

use crate::NodeBuilder as NB;

pub fn resolve_attribute(
    ident: StringKey,
    attr: &AstNode,
    span_id: SpanId,
    args: Vec<Argument>,
    b: &mut NB,
) -> Option<AstNode> {
    let attr_name = b.labels.r(ident.into());
    // This is where we should check for comptime functions and resolve them
    // We are taking a shortcut for now.
    match &attr.node {
        Ast::Identifier(base) => {
            let name = b.labels.r(base.into());
            if &name == "q" {
                if let Some(ast) = b.build_builtin_from_name(&attr_name, args, span_id) {
                    Some(ast)
                } else {
                    None
                }
            } else {
                unimplemented!("{}.{}", name, attr_name)
            }
        }
        _ => unimplemented!("{:?}", attr),
    }
}
