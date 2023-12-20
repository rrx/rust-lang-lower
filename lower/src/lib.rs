pub mod ast;
mod blocks;
pub mod builder;
pub mod cfg;
pub mod compile;
pub mod diagnostics;
pub mod env;
pub mod op;
pub mod types;

pub use ast::{AstNode, Extra, SimpleExtra};
pub use builder::NodeBuilder;
pub use compile::{default_context, default_pass_manager};
pub use diagnostics::{Diagnostics, FileDB, ParseError};
pub use types::{AstType, TypeUnify};

// re-export melior structs
pub use melior::{
    ir::{Location, Module},
    Context,
};

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    pub fn gen_test<'c, E: Extra>(b: &NodeBuilder<E>) -> AstNode<E> {
        let mut seq = vec![b.import_prelude()];
        seq.push(b.main(b.seq(vec![
            b.assign("x", b.integer(123)),
            b.test(
                b.bool(false),
                b.seq(vec![
                    b.subtract(b.integer(2), b.integer(1)),
                    b.subtract(b.ident("x"), b.integer(1)),
                    b.index(1),
                ]),
            ),
            b.ret(Some(b.integer(0))),
        ])));

        b.seq(seq)
    }

    pub fn gen_block<'c, E: Extra>(b: &NodeBuilder<E>) -> AstNode<E> {
        let mut seq = vec![b.import_prelude()];

        // global variable x = 10
        //seq.push(b.global("z", b.integer(10)));
        seq.push(b.main(b.seq(vec![
            b.block(
                "entry",
                &[],
                b.seq(vec![
                    b.assign("yy", b.integer(1)),
                    b.alloca("y", b.integer(999)),
                    //b.mutate(b.ident("y"), b.integer(998)),
                    //b.ret(Some(b.integer(0))),
                    // branch to asdf
                    b.goto("asdf"),
                ]),
            ),
            b.block(
                "asdf",
                &[],
                b.seq(vec![
                    //b.ident("y"),
                    //b.ident("z"),
                    b.assign("yy", b.integer(2)),
                    //b.mutate(b.ident("z"), b.integer(997)),
                    // entry dominates "asdf", so y should be visible
                    //b.mutate(b.ident("y"), b.integer(997)),
                    //b.mutate(b.ident("z_static"), b.integer(10)),
                    //b.subtract(b.deref_offset(b.ident("y"), 0), b.integer(1)),
                    b.goto("asdf2"),
                    // branch to asdf2
                ]),
            ),
            // final block
            b.block(
                "asdf2",
                &[],
                b.seq(vec![
                    b.assign("yy", b.integer(3)),
                    //b.mutate(b.ident("y"), b.integer(996)),
                    b.ret(Some(b.integer(0))),
                ]),
            ),
        ])));
        b.seq(seq)
    }

    pub fn gen_while<'c, E: Extra>(b: &NodeBuilder<E>) -> AstNode<E> {
        let mut seq = vec![b.import_prelude()];

        // global variable x = 10
        seq.push(b.global("z", b.integer(10)));
        seq.push(b.main(b.seq(vec![
            // define local var
            // allocate mutable var
            b.assign("x", b.integer(123)),
            b.alloca("x2", b.integer(10)),
            b.while_loop(
                b.ne(b.deref_offset(b.ident("x2"), 0), b.integer(0)),
                b.seq(vec![
                    // static variable with local scope
                    b.global("z_static", b.integer(10)),
                    b.mutate(b.ident("z_static"), b.integer(10)),
                    // mutate global variable
                    b.mutate(
                        b.ident("z"),
                        b.subtract(b.deref_offset(b.ident("z"), 0), b.integer(1)),
                    ),
                    // mutate scoped variable
                    b.mutate(
                        b.ident("x2"),
                        b.subtract(b.deref_offset(b.ident("x2"), 0), b.integer(1)),
                    ),
                    b.mutate(
                        b.ident("z_static"),
                        b.subtract(b.deref_offset(b.ident("z_static"), 0), b.integer(1)),
                    ),
                    // assign local
                    b.assign(
                        "y",
                        b.subtract(b.ident("x"), b.deref_offset(b.ident("z_static"), 0)),
                    ),
                ]),
            ),
            b.ret(Some(b.ident("z"))),
        ])));

        b.seq(seq)
    }

    pub fn gen_function_call<'c, E: Extra>(b: &NodeBuilder<E>) -> AstNode<E> {
        let mut seq = vec![b.import_prelude()];
        seq.push(b.global("z", b.integer(10)));

        seq.push(b.func(
            "x1",
            &[("arg0", AstType::Int)],
            AstType::Int,
            b.seq(vec![
                // using an alloca
                b.alloca("y", b.ident("arg0")),
                b.cond(
                    b.ne(b.deref_offset(b.ident("y"), 0), b.integer(0)),
                    b.seq(vec![
                        b.mutate(
                            b.ident("y"),
                            b.subtract(b.deref_offset(b.ident("y"), 0), b.integer(1)),
                        ),
                        b.mutate(
                            b.ident("y"),
                            b.apply(
                                "x1",
                                vec![b.deref_offset(b.ident("y"), 0).into()],
                                AstType::Int,
                            ),
                        ),
                    ]),
                    None,
                ),
                // using args
                b.cond(
                    b.ne(b.ident("arg0"), b.integer(0)),
                    b.seq(vec![b.mutate(
                        b.ident("y"),
                        b.apply(
                            "x1",
                            vec![b.subtract(b.ident("arg0"), b.integer(1).into()).into()],
                            AstType::Int,
                        ),
                    )]),
                    None,
                ),
                b.ret(Some(b.deref_offset(b.ident("y"), 0))),
            ]),
        ));

        seq.push(b.main(b.seq(vec![
            b.assign("x", b.apply("x1", vec![b.integer(10).into()], AstType::Int)),
            b.assign("x", b.apply("x1", vec![b.integer(0).into()], AstType::Int)),
            b.ret(Some(b.ident("x"))),
        ])));
        b.seq(seq)
    }
}
