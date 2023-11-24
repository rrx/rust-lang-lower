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

pub type FileDB = SimpleFiles<String, String>;

pub struct Lower<'a> {
    context: &'a Context,
    files: &'a FileDB,
}

impl<'c> Lower<'c> {
    pub fn new(context: &'c Context, files: &'c FileDB) -> Self {
        Self { context, files }
    }

    pub fn type_from_expr<E: Extra>(&self, expr: &AstNode<E>) -> AstType {
        match &expr.node {
            Ast::Literal(x) => match x {
                Literal::Int(_) => AstType::Int,
                Literal::Float(_) => AstType::Float,
                Literal::Bool(_) => AstType::Bool,
            },

            _ => unreachable!("{:?}", expr),
        }
    }

    pub fn from_type(&self, ty: AstType) -> Type<'c> {
        match ty {
            AstType::Int => Type::index(self.context),
            AstType::Float => Type::float64(self.context),
            AstType::Bool => melior::ir::r#type::IntegerType::new(self.context, 1).into(),
        }
    }

    pub fn build_bool_op(&self, value: bool, location: Location<'c>) -> Operation<'c> {
        let bool_type = melior::ir::r#type::IntegerType::new(self.context, 1);
        arith::constant(
            self.context,
            attribute::IntegerAttribute::new(if value { 1 } else { 0 }, bool_type.into()).into(),
            location,
        )
    }

    pub fn build_int_op(&self, value: i64, location: Location<'c>) -> Operation<'c> {
        arith::constant(
            self.context,
            attribute::IntegerAttribute::new(value, Type::index(self.context)).into(),
            location,
        )
    }

    pub fn build_loop<E: Extra>(
        &self,
        init_args: &[Value<'c, '_>],
        condition: AstNode<E>,
        body: AstNode<E>,
        depth: usize,
    ) -> Vec<Operation<'c>> {
        let bool_type = melior::ir::r#type::IntegerType::new(self.context, 1).into();
        let float_type = Type::float64(self.context);
        let index_type = Type::index(self.context);
        let condition_location = self.location(&condition);
        let body_location = self.location(&body);

        //let init_args = &[(float_type, condition_location)];
        //let before_args = &[];//(bool_type, condition_location)];
        let before_args = init_args
            .iter()
            .map(|a| (a.r#type(), condition_location))
            .collect::<Vec<_>>();
        let after_args = &[(index_type, body_location)];

        let before_region = Region::new();
        let before_block = Block::new(&before_args);
        //let init_args = before_block.argument(0).unwrap().into();

        let mut out = vec![];
        let condition_ops = self.lower_expr(condition);
        //let r_condition = ops.last().unwrap().result(0).unwrap();
        //let op = self.build_int_op(2, body_location);
        let condition_op = condition_ops.last().unwrap();
        let condition_rs = condition_op
            .results()
            .map(|r| r.into())
            .collect::<Vec<Value>>();

        // should be bool type
        assert!(condition_rs[0].r#type() == bool_type);

        // to pass to after
        let op = self.build_int_op(2, body_location);
        let rs = op.results().map(|r| r.into()).collect::<Vec<Value>>();
        // check types
        rs.iter().for_each(|r| {
            assert!(r.r#type() == after_args[0].0);
        });

        // condition passes result to region 1 if true, or terminates with result
        let c = scf::condition(
            //init_arg,
            condition_rs[0].into(),
            &rs,
            condition_location,
        );
        before_block.append_operation(op);
        for op in condition_ops {
            before_block.append_operation(op);
        }
        before_block.append_operation(c);
        before_region.append_block(before_block);

        let after_region = Region::new();
        let after_block = Block::new(after_args);

        //let op = self.build_int_op(10, body_location);
        let body_ops = self.lower_expr(body);
        println!("ops: {:?}", body_ops);

        let op = self.build_bool_op(false, condition_location);
        //let op = ops.last().unwrap();
        let rs = op.results().map(|r| r.into()).collect::<Vec<Value>>();

        // check types
        rs.iter().for_each(|r| {
            println!("type: {:?}", r.r#type());
            println!("type: {:?}", before_args[0].0);
            assert!(r.r#type() == before_args[0].0);
        });
        //let rs = [];

        assert!(rs.len() == init_args.len());

        // yield passes result to region 0
        let y = scf::r#yield(&rs, body_location);
        after_block.append_operation(op);
        for op in body_ops {
            after_block.append_operation(op);
        }
        after_block.append_operation(y);

        after_region.append_block(after_block);

        //let init_op = self.build_bool_op(true, condition_location);
        //let rs = init_op.results().map(|r| r.into()).collect::<Vec<Value>>();
        let op = scf::r#while(
            //&rs,
            init_args,
            &after_args.iter().map(|x| x.0).collect::<Vec<Type<'_>>>(),
            before_region,
            after_region,
            body_location,
        );
        //out.push(init_op);
        out.push(op);

        //if depth == 0 {
        // function level, non-zero result means return immediately
        //} else {
        //}
        //let op = cf::cond_br(context
        //println!("op: {:?}", ops);
        out
    }

    pub fn location<E: Extra>(&self, expr: &AstNode<E>) -> Location<'c> {
        expr.extra.location(self.context, self.files)
    }

    pub fn lower_expr<E: Extra>(&self, expr: AstNode<E>) -> Vec<Operation<'c>> {
        let index_type = Type::index(self.context);
        let location = self.location(&expr);

        match expr.node {
            Ast::BinaryOp(op, a, b) => {
                let mut lhs_ops = self.lower_expr(*a);
                let mut rhs_ops = self.lower_expr(*b);
                let r_lhs = lhs_ops.last().unwrap().result(0).unwrap();
                let r_rhs = rhs_ops.last().unwrap().result(0).unwrap();

                // types must be the same for binary operation, no implicit casting yet
                assert!(r_lhs.r#type() == r_rhs.r#type());

                let ty = r_lhs.r#type();
                let float_type = Type::float64(self.context);

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
                                self.context,
                                arith::CmpiPredicate::Eq,
                                r_lhs.into(),
                                r_rhs.into(),
                                location,
                            )
                        } else if ty == float_type {
                            // ordered comparison
                            arith::cmpf(
                                self.context,
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
                "True" => vec![self.build_bool_op(true, location)],
                "False" => vec![self.build_bool_op(false, location)],
                _ => unimplemented!("Ident({:?})", ident),
            },

            Ast::Call(expr, args) => {
                // function to call
                let f = match &expr.node {
                    Ast::Identifier(ident) => {
                        attribute::FlatSymbolRefAttribute::new(self.context, ident)
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
                    match a {
                        Argument::Positional(arg) => {
                            println!("arg: {:?}", arg.node);
                            let mut arg_ops = self.lower_expr(*arg);
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
                let op = func::call(
                    self.context,
                    f,
                    call_args.as_slice(),
                    &[index_type],
                    location,
                );
                ops.push(op);
                //println!("ops: {:?}", ops);
                ops
            }

            Ast::Literal(lit) => match lit {
                Literal::Float(f) => {
                    let float_type = Type::float64(self.context);
                    vec![arith::constant(
                        self.context,
                        attribute::FloatAttribute::new(self.context, f, float_type).into(),
                        location,
                    )]
                }

                Literal::Int(x) => {
                    vec![arith::constant(
                        self.context,
                        attribute::IntegerAttribute::new(x, index_type).into(),
                        location,
                    )]
                }

                Literal::Bool(x) => {
                    vec![self.build_bool_op(x, location)]
                }

                _ => {
                    println!("not implemented: {:?}", lit);
                    unimplemented!();
                }
            },

            Ast::Sequence(exprs) => {
                let mut out = vec![];
                for s in exprs {
                    out.extend(self.lower_expr(s));
                }
                out
            }

            Ast::Definition(def) => {
                println!("name {:?}", def.name);
                let mut params = vec![];
                let index_type = Type::index(self.context);
                for p in def.params {
                    match p.node {
                        Parameter::Normal(ident, ty) => {
                            println!("params {:?}: {:?}", ident, ty);
                            let location = p.extra.location(self.context, self.files);
                            let ir_ty = self.from_type(ty);
                            params.push((ir_ty, location));
                        }
                        _ => {
                            println!("not implemented: {:?}", p);
                            unimplemented!();
                        }
                    }
                }

                let region = Region::new();
                if let Some(body) = def.body {
                    let ops = self.lower_expr(*body);
                    let index_type = Type::index(self.context);
                    let location = expr.extra.location(self.context, self.files);

                    let block = Block::new(params.as_slice());
                    for op in ops {
                        block.append_operation(op);
                    }

                    region.append_block(block);
                }

                let types = params.iter().map(|x| x.0).collect::<Vec<Type>>();
                let ret_type = vec![index_type];
                let func_type = FunctionType::new(self.context, &types, &ret_type);

                let f = func::func(
                    self.context,
                    StringAttribute::new(self.context, &def.name),
                    TypeAttribute::new(func_type.into()),
                    region,
                    &[(
                        Identifier::new(self.context, "sym_visibility"),
                        StringAttribute::new(self.context, "private").into(),
                    )],
                    location,
                );
                vec![f]
            }

            Ast::Return(maybe_expr) => match maybe_expr {
                Some(expr) => {
                    let mut ops = self.lower_expr(*expr);
                    let results: Vec<Value> =
                        ops.last().unwrap().results().map(|r| r.into()).collect();
                    let ret_op = func::r#return(results.as_slice(), location);
                    ops.push(ret_op);
                    ops
                }
                None => {
                    vec![func::r#return(&[], location)]
                }
            },

            Ast::Conditional(condition, true_expr, maybe_false_expr) => {
                let mut condition_ops = self.lower_expr(*condition);
                let r_condition = condition_ops.last().unwrap().result(0).unwrap().into();
                let true_ops = self.lower_expr(*true_expr);

                let true_block = Block::new(&[]);
                for op in true_ops {
                    true_block.append_operation(op);
                }
                true_block.append_operation(scf::r#yield(&[], location));

                let mut out = vec![];
                match maybe_false_expr {
                    Some(false_expr) => {
                        let false_ops = self.lower_expr(*false_expr);
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
                        let op1 = memref::alloca(self.context, ty, &[], &[], None, location);
                        let x: Value = op1.result(0).unwrap().into();

                        let c = arith::constant(
                            self.context,
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

                out.extend(self.lower_expr(*rhs));
                out
            }

            Ast::Test(condition, body) => {
                let mut out = vec![];
                let condition_location = self.location(&condition);
                let init_op = self.build_bool_op(true, condition_location);
                let rs = init_op.results().map(|r| r.into()).collect::<Vec<Value>>();
                let ops = self.build_loop(&rs, *condition, *body, 0);
                out.push(init_op);
                out.extend(ops);
                out
            }

            Ast::Builtin(b) => {
                match b {
                    Builtin::Assert(arg) => {
                        match *arg {
                            Argument::Positional(expr) => {
                                //let location = self.location(&expr);
                                let mut out = vec![];
                                println!("ops: {:?}", expr);
                                let ops = self.lower_expr(*expr);
                                println!("ops: {:?}", ops);
                                let op = ops.last().unwrap();
                                let r = op.result(0).unwrap().into();

                                let msg = format!("assert at {}", location);
                                let assert_op = cf::assert(self.context, r, &msg, location);
                                out.extend(ops);
                                out.push(assert_op);
                                out
                            }
                        }
                    }
                    Builtin::Print(arg) => match *arg {
                        Argument::Positional(expr) => {
                            println!("x: {:?}", expr);

                            let ast_ty = self.type_from_expr(&expr);

                            // eval expr
                            let mut ops = self.lower_expr(*expr);
                            let r = ops.last().unwrap().result(0).unwrap();
                            //let ty = r.r#type();

                            let ident = match &ast_ty {
                                AstType::Int => "print_index",
                                AstType::Float => "print_float",
                                _ => unimplemented!(),
                            };

                            //let ty = self.from_type(ast_ty);
                            //println!("ty: {:?}", ty);

                            //println!("ident: {:?}", ident);

                            let f = attribute::FlatSymbolRefAttribute::new(self.context, ident);
                            let op =
                                func::call(self.context, f, &[r.into()], &[index_type], location);

                            ops.push(op);
                            ops
                        }
                    },
                    _ => {
                        unimplemented!("{:?}", b);
                    }
                }
            }

            _ => {
                unimplemented!("{:?}", expr.node);
            }
        }
    }
}

pub fn node<E: Extra>(file_id: usize, ast: Ast<E>) -> AstNode<E> {
    let begin = CodeLocation { line: 0, col: 0 };
    let end = CodeLocation { line: 0, col: 0 };
    ast.node(file_id, begin, end)
}

pub fn prelude<E: Extra>(file_id: usize) -> Vec<AstNode<E>> {
    let ident = "fresh0".to_string();
    let begin = CodeLocation { line: 0, col: 0 };
    let end = CodeLocation { line: 0, col: 0 };
    vec![
        node(
            file_id,
            Ast::Definition(Definition {
                name: "print_index".to_string(),
                params: vec![ParameterNode {
                    node: Parameter::Normal(ident.clone(), AstType::Int),
                    extra: E::new(file_id, begin.clone(), end.clone()),
                }],
                body: None,
            }),
        ),
        node(
            file_id,
            Ast::Definition(Definition {
                name: "print_float".to_string(),
                params: vec![ParameterNode {
                    node: Parameter::Normal(ident, AstType::Float),
                    extra: E::new(file_id, begin, end),
                }],
                body: None,
            }),
        ),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    //use test_log::test;
    use melior::{
        dialect::DialectRegistry,
        utility::{register_all_dialects, register_all_llvm_translations},
        Context,
    };

    fn gen_test(file_id: usize) -> AstNode<SimpleExtra> {
        let mut seq = prelude(file_id);
        seq.push(node(
            file_id,
            Ast::Definition(Definition {
                name: "test".into(),
                params: vec![],
                body: Some(Box::new(node(
                    file_id,
                    Ast::Sequence(vec![
                        node(
                            file_id,
                            Ast::Test(
                                Box::new(node(file_id, Ast::Literal(Literal::Bool(true)))),
                                Box::new(node(file_id, Ast::Literal(Literal::Int(2)))),
                            ),
                        ),
                        node(
                            file_id,
                            Ast::Return(Some(Box::new(node(
                                file_id,
                                Ast::Literal(Literal::Int(1)),
                            )))),
                        ),
                    ]),
                ))),
            }),
        ));

        node(file_id, Ast::Sequence(seq))
    }

    fn test_context() -> Context {
        let context = Context::new();
        context.set_allow_unregistered_dialects(true);

        let registry = DialectRegistry::new();
        register_all_dialects(&registry);
        context.append_dialect_registry(&registry);
        context.load_all_available_dialects();
        register_all_llvm_translations(&context);
        context
    }

    #[test]
    fn test_loop() {
        let context = test_context();
        let mut files = FileDB::new();
        let file_id = files.add("test.py".into(), "test".into());
        let ast = gen_test(file_id);
        let lower = Lower::new(&context, &files);
        let ops = lower.lower_expr(ast);
        println!("{:?}", ops);
        let module = ir::Module::new(Location::unknown(&context));
        for op in ops {
            module.body().append_operation(op);
        }
        let s = module.as_operation().to_string();
        println!("{}", s);
        assert!(module.as_operation().verify());
    }
}
