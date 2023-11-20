use melior::{
    dialect::{arith, cf, func, scf},
    ir::{
        attribute::{StringAttribute, TypeAttribute},
        operation::OperationBuilder,
        r#type::FunctionType,
        *,
    },
    Context,
};

use crate::ast::*;
use starlark_syntax::codemap::CodeMap;

pub fn lower_expr<'c, E: Extra>(
    context: &'c Context,
    codemap: &CodeMap,
    expr: AstNode<E>,
) -> Vec<Operation<'c>> {
    let index_type = Type::index(context);
    let location = expr.extra.location(context, codemap);
    //let location = Location::new(context, codemap.filename(), expr.begin.line, expr.begin.col);
    match expr.node {
        Ast::BinaryOp(op, a, b) => {
            let mut lhs_ops = lower_expr(context, codemap, *a);
            let mut rhs_ops = lower_expr(context, codemap, *b);
            let r_lhs = lhs_ops.last().unwrap().result(0).unwrap();
            let r_rhs = rhs_ops.last().unwrap().result(0).unwrap();
            //println!("lhs: {:?}", lhs_ops);
            //println!("rhs: {:?}", rhs_ops);
            //println!("lhs: {:?}", r_lhs.r#type());
            //println!("rhs: {:?}", r_rhs.r#type());

            // types must be the same for binary operation, no implicit casting
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
                        let mut arg_ops = lower_expr(context, codemap, *arg);
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
                out.extend(lower_expr(context, codemap, s));
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
                        let location = p.extra.location(context, codemap);
                        params.push((index_type, location));
                    }
                    _ => {
                        println!("not implemented: {:?}", p);
                        unimplemented!();
                    }
                }
            }

            let ops = lower_expr(context, codemap, *def.body);
            let index_type = Type::index(context);
            let location = expr.extra.location(context, codemap);

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
                let mut ops = lower_expr(context, codemap, *expr);
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
            let mut condition_ops = lower_expr(context, codemap, *condition);
            let r_condition = condition_ops.last().unwrap().result(0).unwrap().into();
            let true_ops = lower_expr(context, codemap, *true_expr);

            let true_block = Block::new(&[]);
            for op in true_ops {
                true_block.append_operation(op);
            }
            true_block.append_operation(scf::r#yield(&[], location));

            let mut out = vec![];
            match maybe_false_expr {
                Some(false_expr) => {
                    let false_ops = lower_expr(context, codemap, *false_expr);
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
            let ops = lower_expr(context, codemap, *rhs);
            match target {
                AssignTarget::Identifier(ident) => {
                    println!("assign ident {:?}", ident);
                }
                _ => {
                    unimplemented!("{:?}", target);
                }
            }
            ops
        }

        _ => {
            unimplemented!("{:?}", expr.node);
        }
    }
}
