pub mod ast;
pub mod builder;
pub mod cfg;
pub mod compile;
pub mod diagnostics;
pub mod first_pass;
pub mod intern;
pub mod ir;
pub mod link;
pub mod mlir;
pub mod op;
pub mod place;
pub mod sort;
pub mod types;

pub use ast::{
    Argument, Ast, AstNode, AstNodeBlock, BinaryOperation, Definition, Extra, Literal,
    ParameterNode, SimpleExtra, Span, UnaryOperation, VarDefinitionSpace,
};
//pub use blockify::{BlockId, Blockify};
pub use builder::{BlockId, NodeBuilder, NodeID, StringLabel};
pub use cfg::{CFGBlocks, CFGGraph, SymIndex};
pub use compile::{default_context, default_pass_manager};
pub use diagnostics::{Diagnostics, FileDB, ParseError};
pub use intern::{InternKey, StringKey};
pub use ir::{IRArg, IRBlockGraph, IRControlBlock, IREnvironment};
pub use link::LinkOptions;
pub use place::{IRPlaceTable, PlaceId, PlaceNode};
pub use types::{AstType, TypeBuilder, TypeUnify};

// re-export codespan
pub use codespan_reporting::diagnostic::{Diagnostic, Label};

// re-export melior structs
pub use melior::{
    ir::operation::OperationPrintingFlags,
    ir::{Location, Module},
    Context,
};
pub use petgraph::graph::NodeIndex;

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    pub fn gen_test<'c, E: Extra>(b: &mut NodeBuilder<E>) -> AstNode<E> {
        let mut seq = vec![b.import_prelude()];
        let x = b.s("x").into();
        seq.push(b.main(b.seq(vec![
            b.assign(x, b.integer(123)),
            b.test(
                b.bool(false),
                b.seq(vec![
                    b.subtract(b.integer(2), b.integer(1)),
                    b.subtract(b.ident(x.into()), b.integer(1)),
                    b.index(1),
                ]),
            ),
            b.ret(Some(b.integer(0))),
        ])));

        b.seq(seq)
    }

    pub fn gen_block<'c, E: Extra>(b: &mut NodeBuilder<E>) -> AstNode<E> {
        // global variable x = 10
        //seq.push(b.global("z", b.integer(10)));
        let y = b.s("y").into();
        let yy = b.s("yy").into();
        let asdf = b.s("asdf");
        let asdf2 = b.s("asdf2").into();
        let entry = b.s("entry").into();
        let main = b.main(b.seq(vec![
            b.block(
                entry,
                &[],
                b.seq(vec![
                    b.label(entry, vec![]),
                    b.assign(yy, b.integer(1)),
                    b.alloca(y, b.integer(999)),
                    //b.mutate(b.ident("y"), b.integer(998)),
                    //b.ret(Some(b.integer(0))),
                    // branch to asdf
                    b.goto(asdf.into()),
                ]),
            ),
            b.block(
                asdf,
                &[],
                b.seq(vec![
                    b.label(asdf, vec![]),
                    //b.ident("y"),
                    //b.ident("z"),
                    b.assign(yy, b.integer(2)),
                    //b.mutate(b.ident("z"), b.integer(997)),
                    // entry dominates "asdf", so y should be visible
                    //b.mutate(b.ident("y"), b.integer(997)),
                    //b.mutate(b.ident("z_static"), b.integer(10)),
                    //b.subtract(b.deref_offset(b.ident("y"), 0), b.integer(1)),
                    b.goto(asdf2),
                    // branch to asdf2
                ]),
            ),
            // final block
            b.block(
                asdf2,
                &[],
                b.seq(vec![
                    b.label(asdf2, vec![]),
                    b.assign(yy, b.integer(3)),
                    //b.mutate(b.ident("y"), b.integer(996)),
                    b.ret(Some(b.integer(0))),
                ]),
            ),
        ]));
        b.seq(vec![b.import_prelude(), main])
    }

    pub fn gen_while<'c, E: Extra>(b: &mut NodeBuilder<E>) -> AstNode<E> {
        let mut seq = vec![b.import_prelude()];

        // global variable x = 10
        let x = b.s("x").into();
        let x2 = b.s("x2").into();
        let z = b.s("z").into();
        let y = b.s("y").into();
        let z_static = b.s("z_static");

        seq.push(b.global(z, b.integer(10)));
        seq.push(b.main(b.seq(vec![
            // define local var
            // allocate mutable var
            b.assign(x, b.integer(123)),
            b.alloca(x2, b.integer(10)),
            b.while_loop(
                b.ne(b.deref_offset(b.ident(x2.into()), 0), b.integer(0)),
                b.seq(vec![
                    // static variable with local scope
                    b.global(z_static, b.integer(10)),
                    b.mutate(b.ident(z_static.into()), b.integer(10)),
                    // mutate global variable
                    b.mutate(
                        b.ident(z.into()),
                        b.subtract(b.deref_offset(b.ident(z.into()), 0), b.integer(1)),
                    ),
                    // mutate scoped variable
                    b.mutate(
                        b.ident(x2.into()),
                        b.subtract(b.deref_offset(b.ident(x2.into()), 0), b.integer(1)),
                    ),
                    b.mutate(
                        b.ident(z_static.into()),
                        b.subtract(b.deref_offset(b.ident(z_static.into()), 0), b.integer(1)),
                    ),
                    // assign local
                    b.assign(
                        y,
                        b.subtract(
                            b.ident(x.into()),
                            b.deref_offset(b.ident(z_static.into()), 0),
                        ),
                    ),
                ]),
            ),
            b.ret(Some(b.ident(z.into()))),
        ])));

        b.seq(seq)
    }

    pub fn gen_function_call<'c, E: Extra>(b: &mut NodeBuilder<E>) -> AstNode<E> {
        let x = b.s("x").into();
        let x1 = b.s("x1").into();
        let z = b.s("z").into();
        let y = b.s("y").into();
        let arg0 = b.s("arg0").into();

        let mut seq = vec![b.import_prelude()];
        seq.push(b.global(z, b.integer(10)));

        seq.push(b.func(
            x1,
            &[(arg0, AstType::Int)],
            AstType::Int,
            b.seq(vec![
                // using an alloca
                b.alloca(y, b.ident(arg0.into())),
                b.cond(
                    b.ne(b.deref_offset(b.ident(y.into()), 0), b.integer(0)),
                    b.seq(vec![
                        b.mutate(
                            b.ident(y.into()),
                            b.subtract(b.deref_offset(b.ident(y.into()), 0), b.integer(1)),
                        ),
                        b.mutate(
                            b.ident(y.into()),
                            b.apply(
                                x1.into(),
                                vec![b.deref_offset(b.ident(y.into()), 0).into()],
                                AstType::Int,
                            ),
                        ),
                    ]),
                    None,
                ),
                // using args
                b.cond(
                    b.ne(b.ident(arg0.into()), b.integer(0)),
                    b.seq(vec![b.mutate(
                        b.ident(y.into()),
                        b.apply(
                            x1.into(),
                            vec![b.subtract(b.ident(arg0.into()), b.integer(1).into()).into()],
                            AstType::Int,
                        ),
                    )]),
                    None,
                ),
                b.ret(Some(b.deref_offset(b.ident(y.into()), 0))),
            ]),
        ));

        seq.push(b.main(b.seq(vec![
            b.assign(
                x,
                b.apply(x1.into(), vec![b.integer(10).into()], AstType::Int),
            ),
            b.assign(
                x,
                b.apply(x1.into(), vec![b.integer(0).into()], AstType::Int),
            ),
            b.ret(Some(b.ident(x.into()))),
        ])));
        b.seq(seq)
    }
}
