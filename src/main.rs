use std::error::Error;
use std::fs::File;
use std::io::Write;
use std::path::Path;

use melior::{
    dialect::DialectRegistry,
    ir, pass,
    utility::{register_all_dialects, register_all_llvm_translations},
    Context,
};

use lower::starlark::parse;

/*
fn lower_expr<'c>(context: &'c Context, codemap: &CodeMap, expr: &syntax::ast::AstExpr) -> Vec<Operation<'c>> {
    use syntax::ast::ExprP;
    use syntax::ast::BinOp;
    use syntax::ast::AstLiteral;
    use syntax::ast::ArgumentP;
    use lexer::TokenInt;

    let index_type = Type::index(context);
    let r = codemap.resolve_span(expr.span);
    let location = Location::new(context, codemap.filename(), r.begin.line, r.begin.column);

    match &expr.node {
        ExprP::Op(a, op, b) =>  {
            let mut lhs_ops = lower_expr(context, codemap, a);
            let mut rhs_ops = lower_expr(context, codemap, b);
            let r_lhs = lhs_ops.last().unwrap().result(0).unwrap();
            let r_rhs = rhs_ops.last().unwrap().result(0).unwrap();
            println!("lhs: {:?}", lhs_ops);
            println!("rhs: {:?}", rhs_ops);
            println!("lhs: {:?}", r_lhs.r#type());
            println!("rhs: {:?}", r_rhs.r#type());

            // types must be the same for binary operation, no implicit casting
            assert!(r_lhs.r#type() == r_rhs.r#type());

            let ty = r_lhs.r#type();
            let float_type = Type::float64(context);

            let mut out = vec![];
            let binop = match op {
                BinOp::Add => {
                    if ty == index_type {
                        arith::addi(r_lhs.into(), r_rhs.into(), location)
                    } else if ty == float_type {
                        arith::addf(r_lhs.into(), r_rhs.into(), location)
                    } else {
                        unimplemented!()
                    }
                }
                BinOp::Subtract => {
                    if ty == index_type {
                        arith::subi(r_lhs.into(), r_rhs.into(), location)
                    } else if ty == float_type {
                        arith::subf(r_lhs.into(), r_rhs.into(), location)
                    } else {
                        unimplemented!()
                    }
                }
                BinOp::Equal => {
                    if ty == index_type {
                        arith::cmpi(context, arith::CmpiPredicate::Eq, r_lhs.into(), r_rhs.into(), location)
                    } else if ty == float_type {
                        // ordered comparison
                        arith::cmpf(context, arith::CmpfPredicate::Oeq, r_lhs.into(), r_rhs.into(), location)
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

        ExprP::Identifier(ident) => {
            let name = &ident.node.ident;
            println!("ident: {}", name);
            //vec![dummy]
            println!("not implemented: {:?}", ident);
            unimplemented!();
        }

        ExprP::Call(expr, args) => {
            // function to call
            let f = match &expr.node {
                ExprP::Identifier(ident) => {
                    let name = &ident.node.ident;
                    attribute::FlatSymbolRefAttribute::new(context, name)
                }
                _ => {
                    println!("not implemented: {:?}", expr.node);
                    unimplemented!();
                }
            };


            // handle call arguments
            let mut ops: Vec<Operation> = vec![];
            let mut call_index: Vec<usize> = vec![];
            for a in args {
                match &a.node {
                    ArgumentP::Positional(arg) => {
                        println!("arg: {:?}", arg.node);
                        let mut arg_ops = lower_expr(context, codemap, arg);
                        ops.append(&mut arg_ops);
                        call_index.push(ops.len()-1);
                    }
                    _ => {
                        println!("not implemented: {:?}", a.node);
                        unimplemented!();
                    }
                };

            }

            let call_args: Vec<Value> = call_index.iter().map(|index| {
                let results = ops.get(*index).unwrap().results();
                let results: Vec<Value> = results.map(|r| r.into()).collect();
                results.last().unwrap().clone()
            }).collect::<Vec<Value>>();

            println!("call_index: {:?}", call_index);
            println!("call_args: {:?}", call_args);
            let op = func::call(context, f, call_args.as_slice(), &[index_type], location);
            ops.push(op);
            println!("ops: {:?}", ops);
            ops
        }

        ExprP::Literal(lit) => {
            match lit {
                AstLiteral::Float(ast) => {
                    let f = ast.node;
                    let float_type = Type::float64(context);
                    vec![arith::constant(context, attribute::FloatAttribute::new(context, f, float_type).into(), location)]
                }
                AstLiteral::Int(ast) => {
                    match ast.node {
                        TokenInt::I32(x) => {
                            vec![arith::constant(context, attribute::IntegerAttribute::new(x as i64, index_type).into(), location)]
                        }
                        _ => {
                            println!("not implemented: {:?}", ast.node);
                            unimplemented!();
                        }
                    }
                }
                _ => {
                    println!("not implemented: {:?}", lit);
                    unimplemented!();
                }
            }
        }

        _ => {
            println!("not implemented: {:?}", expr.node);
            unimplemented!();
        }
    }
}

fn lower_stmt<'a>(context: &'a Context, codemap: &CodeMap, ast: &syntax::ast::AstStmt) -> Vec<Operation<'a>> {
    use syntax::ast::StmtP;
    use syntax::ast::ParameterP;
    match &ast.node {
        StmtP::Statements(stmts) => {
            let mut out = vec![];
            for s in stmts {
                out.extend(lower_stmt(context, codemap, s));
            }
            out
        }

        StmtP::Def(def) => {
            println!("name {:?}", def.name.ident);
            let mut params = vec![];
            let index_type = Type::index(context);
            for p in &def.params {
                match &p.node {
                    ParameterP::Normal(ident, maybe_ty) => {
                        println!("params {:?}", ident.node.ident);
                        let r = codemap.resolve_span(ident.span);
                        let location = Location::new(context, codemap.filename(), r.begin.line, r.begin.column);
                        params.push((index_type, location));
                    }
                    _ => {
                        println!("not implemented: {:?}", p);
                        unimplemented!();
                    }
                }
            }
            println!("ret {:?}", def.return_type);

            let ops = lower_stmt(context, codemap, &*def.body);
            let index_type = Type::index(context);
            let r = codemap.resolve_span(ast.span);
            let location = Location::new(context, codemap.filename(), r.begin.line, r.begin.column);


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
                StringAttribute::new(context, &def.name.ident),
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

        StmtP::IfElse(expr, options) => {
            println!("ifexpr {:?}", expr);
            lower_expr(context, codemap, expr);
            println!("if {:?}", options.0);
            lower_stmt(context, codemap, &options.0);
            println!("else {:?}", options.1);
            lower_stmt(context, codemap, &options.1);
            vec![]
        }

        StmtP::Return(maybe_expr) => {
            let r = codemap.resolve_span(ast.span);
            let location = Location::new(context, codemap.filename(), r.begin.line, r.begin.column);
            match maybe_expr {
                Some(expr) => {
                    let mut ops = lower_expr(context, codemap, expr);
                    let results: Vec<Value> = ops.last().unwrap().results().map(|r| r.into()).collect();
                    let ret_op = func::r#return( results.as_slice(), location);
                    ops.push(ret_op);
                    ops
                }
                None =>  {
                    vec![func::r#return( &[], location)]
                }
            }
        }

        StmtP::Assign(assign) => {
            let ops = lower_expr(context, codemap, &assign.rhs);
            match &*assign.lhs {
                syntax::ast::AssignTarget::Identifier(ident) => {
                    println!("assign ident {:?}", ident.node.ident);
                }
                _ => {
                    println!("not implemented: {:?}", assign.lhs);
                    unimplemented!();
                }
            }
            ops
            //vec![ops]
        }

        StmtP::Expression(expr) => {
            let ops = lower_expr(context, codemap, expr);
            println!("not implemented: {:?}", expr);
            unimplemented!();
            //vec![ops]
        }

        _ => {
            println!("not implemented: {:?}", ast.node);
            unimplemented!();
        }
    }
}

fn test(context: &Context) {
    let index_type = Type::index(context);
    let location = Location::unknown(context);
    let dummy = arith::constant(context, attribute::IntegerAttribute::new(1, index_type).into(), location);
    let op = func::r#return( &[dummy.result(0).unwrap().into()], location);

    let func_type = FunctionType::new(context, &[], &[index_type]);
    let block = Block::new(&[]);
    block.append_operation(dummy);
    block.append_operation(op);

    let region = Region::new();
    region.append_block(block);

    let f = func::func(
        context,
        StringAttribute::new(context, "test"),
        TypeAttribute::new(func_type.into()),
        region,
        &[(
            Identifier::new(&context, "sym_visibility"),
            StringAttribute::new(&context, "private").into(),
        )],
        location,
        );

    let module = Module::new(location);
    module.body().append_operation(f);

    module.as_operation().dump();
    assert!(module.as_operation().verify());
    module.as_operation().dump();
}
*/

fn main() -> Result<(), Box<dyn Error>> {
    let context = Context::new();

    let pass_manager = pass::PassManager::new(&context);
    pass_manager.enable_verifier(true);
    //pass_manager.enable_ir_printing();
    pass_manager.add_pass(pass::conversion::create_func_to_llvm());
    pass_manager.add_pass(pass::conversion::create_arith_to_llvm());
    //pass_manager.add_pass(pass::conversion::create_async_to_llvm());
    pass_manager.add_pass(pass::conversion::create_complex_to_llvm());
    pass_manager.add_pass(pass::conversion::create_math_to_llvm());

    context.attach_diagnostic_handler(|diagnostic| {
        eprintln!("E: {}", diagnostic);
        true
    });

    let registry = DialectRegistry::new();
    register_all_dialects(&registry);
    context.append_dialect_registry(&registry);
    context.load_all_available_dialects();
    register_all_llvm_translations(&context);

    let location = ir::Location::unknown(&context);
    let mut module = ir::Module::new(location);

    let ops = parse(&context, Path::new("examples/test_simple.py")).unwrap();
    for op in ops {
        module.body().append_operation(op);
    }
    module.as_operation().dump();
    assert!(module.as_operation().verify());
    let mut output = File::create("out.mlir")?;
    let s = module.as_operation().to_string();
    write!(output, "{}", s)?;

    pass_manager.run(&mut module)?;

    module.as_operation().dump();
    let mut output = File::create("out.ll")?;
    let s = module.as_operation().to_string();
    write!(output, "{}", s)?;

    Ok(())
}
