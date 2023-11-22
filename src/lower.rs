use melior::{
    dialect::{arith, cf, func, memref, scf},
    ir,
    ir::{
        attribute::{StringAttribute, TypeAttribute},
        operation::OperationBuilder,
        r#type::{FunctionType, MemRefType},
        *,
    },
    Context,
};

use crate::ast::*;
use codespan_reporting::files::{Files, SimpleFiles};

/*
 * Environment
 * - is this in a function context?
 * - is this a scf.if region?  requiring a final yield
 * - how to we handle a return statement in an scf.if region?  return requires the function as the
 * parent. We need to maybe use cf directly instead.  Or transform it into something that removes
 * the return from within the scf.if.  We need to transform it to remove nested ifs.  We can
 * replace the return with a yield that returns 1+ values.  The first value being a boolean
 * determining if a return is requested, subsequent values could contain the return value, or the
 * value of a non-return yield from the scf.if.
 * - handle loops, scf.while doesn't handle deeply nested loops
 * - determine if a loop is affine, and then use affine, if not, then we need to use other looping
 * mechanisms.  Breaks preclude affine, and we use either scf, or cf
 * There's probably a default case that handles everything cleanly, and we can specialize from
 * there.  do everything with a set of while loops.  Each loop has an escape variable.  And the
 * outer loop escapes with a return statement which is the child of the func.func.  Every nested
 * loop needs to handle breakout.   Things like continue, break, return, as well as breaking out to
 * a specific labelled loop (as in rust, but not in python)
 * - buildins: assert, int, float
 * - keywords: continue, break, pass, return
 * - nested layers of loops, lambdas and conditionals, handling break, continue, pass and return
 * ra = loop a (depth=0):
 *   rb = loop b (depth=1):
 *     rc = loop c (depth=2):
 *       if False:
 *         return 1
 *       if False:
 *         break
 *       if False:
 *         continue
 *       if False:
 *         continue b
 *       if False
 *         break a
 *
 */

pub fn build_bool_op<'c>(
    context: &'c Context,
    value: bool,
    location: Location<'c>,
) -> Operation<'c> {
    let bool_type = melior::ir::r#type::IntegerType::new(context, 1);
    arith::constant(
        context,
        attribute::IntegerAttribute::new(if value { 1 } else { 0 }, bool_type.into()).into(),
        location,
    )
}

pub fn build_loop<'c, E: Extra>(
    context: &'c Context,
    files: &SimpleFiles<String, String>,
    condition: AstNode<E>,
    body: AstNode<E>,
    depth: usize,
) -> Vec<Operation<'c>> {
    let location = Location::unknown(context);
    let bool_type = melior::ir::r#type::IntegerType::new(context, 1);
    let b_true = build_bool_op(context, true, location);
    let b_false = build_bool_op(context, true, location);

    let before_region = Region::new();
    let before_block = Block::new(&[(bool_type.into(), location)]);
    let before_block_arg: Value = before_block.argument(0).unwrap().into();
    before_block.append_operation(scf::condition(before_block_arg, &[], location));
    before_region.append_block(before_block);

    let after_region = Region::new();
    let after_block = Block::new(&[]);
    after_block.append_operation(scf::r#yield(&[b_false.result(0).unwrap().into()], location));
    after_region.append_block(after_block);

    let ty = Type::index(context);
    let mut condition_ops = lower_expr(context, condition, files);
    let op = scf::r#while(
        &[b_true.result(0).unwrap().into()],
        &[ty],
        before_region,
        after_region,
        location,
    );

    //if depth == 0 {
    // function level, non-zero result means return immediately
    //} else {
    //}
    //let op = cf::cond_br(context
    vec![op]
}

pub fn lower_expr<'c, E: Extra>(
    context: &'c Context,
    expr: AstNode<E>,
    files: &SimpleFiles<String, String>,
) -> Vec<Operation<'c>> {
    let index_type = Type::index(context);
    let location = expr.extra.location(context, files);

    match expr.node {
        Ast::BinaryOp(op, a, b) => {
            let mut lhs_ops = lower_expr(context, *a, files);
            let mut rhs_ops = lower_expr(context, *b, files);
            let r_lhs = lhs_ops.last().unwrap().result(0).unwrap();
            let r_rhs = rhs_ops.last().unwrap().result(0).unwrap();

            // types must be the same for binary operation, no implicit casting yet
            assert!(r_lhs.r#type() == r_rhs.r#type());

            let ty = r_lhs.r#type();
            let float_type = Type::float64(context);

            let mut out = vec![];
            let binop = match op {
                BinaryOperation::Add => {
                    if ty == index_type {
                        arith::addi(r_lhs.into(), r_rhs.into(), location)
                    } else if ty == float_type {
                        arith::addf(r_lhs.into(), r_rhs.into(), location)
                    } else {
                        unimplemented!()
                    }
                }
                BinaryOperation::Subtract => {
                    if ty == index_type {
                        arith::subi(r_lhs.into(), r_rhs.into(), location)
                    } else if ty == float_type {
                        arith::subf(r_lhs.into(), r_rhs.into(), location)
                    } else {
                        unimplemented!()
                    }
                }
                BinaryOperation::Equal => {
                    if ty == index_type {
                        arith::cmpi(
                            context,
                            arith::CmpiPredicate::Eq,
                            r_lhs.into(),
                            r_rhs.into(),
                            location,
                        )
                    } else if ty == float_type {
                        // ordered comparison
                        arith::cmpf(
                            context,
                            arith::CmpfPredicate::Oeq,
                            r_lhs.into(),
                            r_rhs.into(),
                            location,
                        )
                    } else {
                        unimplemented!()
                    }
                }
                _ => {
                    println!("not implemented: {:?}", op);
                    unimplemented!();
                }
            };
            out.append(&mut lhs_ops);
            out.append(&mut rhs_ops);
            out.push(binop);
            out
        }

        Ast::Identifier(ident) => match ident.as_str() {
            "True" => {
                let bool_type = melior::ir::r#type::IntegerType::new(context, 1);
                vec![arith::constant(
                    context,
                    attribute::IntegerAttribute::new(1, bool_type.into()).into(),
                    location,
                )]
            }
            "False" => vec![],
            _ => unimplemented!("Ident({:?})", ident),
        },

        Ast::Call(expr, args) => {
            // function to call
            let f = match &expr.node {
                Ast::Identifier(ident) => attribute::FlatSymbolRefAttribute::new(context, ident),
                _ => {
                    println!("not implemented: {:?}", expr.node);
                    unimplemented!();
                }
            };

            // handle call arguments
            let mut ops: Vec<Operation> = vec![];
            let mut call_index: Vec<usize> = vec![];
            for a in args {
                match a {
                    Argument::Positional(arg) => {
                        println!("arg: {:?}", arg.node);
                        let mut arg_ops = lower_expr(context, *arg, files);
                        ops.append(&mut arg_ops);
                        call_index.push(ops.len() - 1);
                    }
                    _ => {
                        println!("not implemented: {:?}", a);
                        unimplemented!();
                    }
                };
            }

            let call_args: Vec<Value> = call_index
                .iter()
                .map(|index| {
                    let results = ops.get(*index).unwrap().results();
                    let results: Vec<Value> = results.map(|r| r.into()).collect();
                    results.last().unwrap().clone()
                })
                .collect::<Vec<Value>>();

            //println!("call_index: {:?}", call_index);
            //println!("call_args: {:?}", call_args);
            let op = func::call(context, f, call_args.as_slice(), &[index_type], location);
            ops.push(op);
            //println!("ops: {:?}", ops);
            ops
        }

        Ast::Literal(lit) => match lit {
            Literal::Float(f) => {
                let float_type = Type::float64(context);
                vec![arith::constant(
                    context,
                    attribute::FloatAttribute::new(context, f, float_type).into(),
                    location,
                )]
            }
            Literal::Int(x) => {
                vec![arith::constant(
                    context,
                    attribute::IntegerAttribute::new(x, index_type).into(),
                    location,
                )]
            }
            _ => {
                println!("not implemented: {:?}", lit);
                unimplemented!();
            }
        },

        Ast::Sequence(exprs) => {
            let mut out = vec![];
            for s in exprs {
                out.extend(lower_expr(context, s, files));
            }
            out
        }

        Ast::Definition(def) => {
            println!("name {:?}", def.name);
            let mut params = vec![];
            let index_type = Type::index(context);
            for p in def.params {
                match p.node {
                    Parameter::Normal(ident) => {
                        println!("params {:?}", ident);
                        let location = p.extra.location(context, files);
                        params.push((index_type, location));
                    }
                    _ => {
                        println!("not implemented: {:?}", p);
                        unimplemented!();
                    }
                }
            }

            let ops = lower_expr(context, *def.body, files);
            let index_type = Type::index(context);
            let location = expr.extra.location(context, files);

            let block = Block::new(params.as_slice());
            for op in ops {
                block.append_operation(op);
            }

            let region = Region::new();
            region.append_block(block);

            let types = params.iter().map(|x| x.0).collect::<Vec<Type>>();
            let ret_type = vec![index_type];
            let func_type = FunctionType::new(context, &types, &ret_type);

            let f = func::func(
                context,
                StringAttribute::new(context, &def.name),
                TypeAttribute::new(func_type.into()),
                region,
                &[(
                    Identifier::new(&context, "sym_visibility"),
                    StringAttribute::new(&context, "private").into(),
                )],
                location,
            );
            vec![f]
        }

        Ast::Return(maybe_expr) => match maybe_expr {
            Some(expr) => {
                let mut ops = lower_expr(context, *expr, files);
                let results: Vec<Value> = ops.last().unwrap().results().map(|r| r.into()).collect();
                let ret_op = func::r#return(results.as_slice(), location);
                ops.push(ret_op);
                ops
            }
            None => {
                vec![func::r#return(&[], location)]
            }
        },

        Ast::Conditional(condition, true_expr, maybe_false_expr) => {
            let mut condition_ops = lower_expr(context, *condition, files);
            let r_condition = condition_ops.last().unwrap().result(0).unwrap().into();
            let true_ops = lower_expr(context, *true_expr, files);

            let true_block = Block::new(&[]);
            for op in true_ops {
                true_block.append_operation(op);
            }
            true_block.append_operation(scf::r#yield(&[], location));

            let mut out = vec![];
            match maybe_false_expr {
                Some(false_expr) => {
                    let false_ops = lower_expr(context, *false_expr, files);
                    let false_block = Block::new(&[]);
                    for op in false_ops {
                        false_block.append_operation(op);
                    }
                    false_block.append_operation(scf::r#yield(&[], location));
                    let then_region = Region::new();
                    then_region.append_block(true_block);
                    let else_region = Region::new();
                    else_region.append_block(false_block);
                    let op = scf::r#if(r_condition, &[], then_region, else_region, location);

                    out.append(&mut condition_ops);
                    out.push(op);
                    out
                }
                None => {
                    let then_region = Region::new();
                    then_region.append_block(true_block);
                    let else_region = Region::new();
                    let op = scf::r#if(r_condition, &[], then_region, else_region, location);

                    out.append(&mut condition_ops);
                    out.push(op);
                    out
                }
            }
        }

        Ast::Assign(target, rhs) => {
            let mut out = vec![];
            match target {
                AssignTarget::Identifier(ident) => {
                    // TODO: handle global variables properly, currently assume function context
                    println!("assign ident {:?}", ident);
                    let ty = MemRefType::new(index_type, &[], None, None);
                    let op1 = memref::alloca(context, ty, &[], &[], None, location);
                    let x: Value = op1.result(0).unwrap().into();

                    let c = arith::constant(
                        context,
                        attribute::IntegerAttribute::new(10, index_type).into(),
                        location,
                    );

                    let op = memref::store(c.result(0).unwrap().into(), x, &[], location);
                    out.push(c);
                    out.push(op1);
                    out.push(op);
                }
                _ => {
                    unimplemented!("{:?}", target);
                }
            }

            out.extend(lower_expr(context, *rhs, files));
            out
        }

        _ => {
            unimplemented!("{:?}", expr.node);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    //use test_log::test;

    #[test]
    fn test_loop() {
        //let context = Context::new();
        //let ops = build_loop(context, condition, body, 0);

        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
