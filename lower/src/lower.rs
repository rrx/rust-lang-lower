use melior::{
    dialect::{arith, cf, func, memref, scf},
    ir::{
        attribute::{StringAttribute, TypeAttribute},
        operation::{OperationRef, OperationResult},
        r#type::{FunctionType, MemRefType},
        *,
    },
    Context,
};
//use std::convert::From;
use std::collections::HashMap;

use crate::ast::*;
use crate::scope::{Layer, LayerType, OpIndex, ScopeStack};
use codespan_reporting::files::SimpleFiles;

type Environment<'c> = ScopeStack<'c>;

//pub struct Environment<'c, 'a> {
//h: HashMap<String, Value<'c, 'a>>,
//}
//impl<'c, 'a> Default for Environment<'c, 'a> {
//fn default() -> Self {
//Self { h: HashMap::new() }
//}
//}

//impl<'c, 'a> crate::env::LayerValue for Value<'c, 'a> {}
//impl<'c> crate::env::LayerValue for Layer<'c> {}
//pub type Environment<'c, 'a> = crate::env::EnvLayers<String, Value<'c, 'a>>;

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

/*
fn test(ops: Vec<ir::Operation<'_>>) -> (Vec<ir::operation::OperationResult<'_, '_>>, Vec<ir::Operation<'_>>) {
    let op = ops.last().unwrap();
    let r = op.results().collect::<Vec<_>>();
    (r, ops)
}

fn op2r<'c>(op: &'c ir::Operation<'c>) -> Vec<Value<'c, '_>> {
    op.results().map(|x| x.into()).collect::<Vec<_>>()
}

fn ops2r<'c>(ops: &'c Vec<ir::Operation<'c>>) -> Vec<Value<'c, '_>> {
    ops.last()
        .unwrap()
        .results()
        .map(|x| x.into())
        .collect::<Vec<_>>()
}
*/

pub type FileDB = SimpleFiles<String, String>;

pub struct Lower<'c> {
    pub(crate) context: &'c Context,
    files: &'c FileDB,
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
            Ast::Identifier(_) => AstType::Unknown,

            _ => unreachable!("{:?}", expr),
        }
    }

    pub fn from_type(&self, ty: AstType) -> Type<'c> {
        match ty {
            AstType::Int => Type::index(self.context),
            AstType::Float => Type::float64(self.context),
            AstType::Bool => melior::ir::r#type::IntegerType::new(self.context, 1).into(),
            AstType::Unknown => unreachable!(),
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

    pub fn build_float_op(&self, value: f64, location: Location<'c>) -> Operation<'c> {
        arith::constant(
            self.context,
            attribute::FloatAttribute::new(self.context, value, Type::float64(self.context)).into(),
            location,
        )
    }

    pub fn build_loop<'a, E: Extra>(
        &self,
        //init_args: &[Value<'c, 'a>],
        condition: AstNode<E>,
        body: AstNode<E>,
        env: &mut Environment<'c>,
        mut layer: Layer<'c>,
        h2: &mut HashMap<&str, Value<'c, 'a>>, //depth: usize,
    ) -> (Vec<Value<'c, '_>>, Vec<Operation<'c>>) {
        //let mut h = std::collections::HashMap::new();
        //env.enter(LayerType::Closed);
        let bool_type = melior::ir::r#type::IntegerType::new(self.context, 1).into();
        let index_type = Type::index(self.context);
        let condition_location = self.location(&condition);
        let body_location = self.location(&body);
        let x_op = self.build_int_op(1, condition_location);
        let r_op: Value<'c, '_> = x_op.result(0).unwrap().into();
        //layer.push(x_op);
        //out.push(op);
        //let r_op = layer.values(layer.last_index());
        //let r_op = out.last().unwrap().result(0).unwrap().into();
        //h.insert("test", r_op[0]);

        let init_op = self.build_bool_op(true, condition_location);
        let init_op2 = self.build_int_op(10, condition_location);
        let mut init_args = init_op.results().map(|r| r.into()).collect::<Vec<Value>>();
        //h.insert("init_op", init_args[0]);
        let rs2 = init_op2.results().map(|r| r.into()).collect::<Vec<Value>>();
        //h.insert("init_op2", rs2[0]);
        init_args.extend(rs2);

        //let init_args = &[(float_type, condition_location)];
        //let before_args = &[];//(bool_type, condition_location)];
        // before
        let before_args = init_args
            .iter()
            .map(|a| (a.r#type(), condition_location))
            .collect::<Vec<_>>();

        let before_region = Region::new();
        let before_block = Block::new(&before_args);

        // bool
        let _a: Value<'c, '_> = before_block.argument(0).unwrap().into();

        //index
        let b: Value<'c, '_> = before_block.argument(1).unwrap().into();

        //let r_op = h.get("test").unwrap().clone();
        //let op2 = arith::addi(b, r_op, condition_location);

        let (_, condition_ops) = self.lower_expr(condition, env);
        //let r_condition = ops.last().unwrap().result(0).unwrap();
        //let op = self.build_int_op(2, body_location);
        //let condition_op = condition_ops.last().unwrap();
        //
        let condition_rs = condition_ops
            .last()
            .unwrap()
            .results()
            .map(|r| r.into())
            .collect::<Vec<Value>>();

        // should be bool type
        assert!(condition_rs[0].r#type() == bool_type);

        // to pass to after

        //let op = self.build_int_op(2, body_location);
        //let rs = op.results().map(|r| r.into()).collect::<Vec<Value>>();
        // check types
        //rs.iter().for_each(|r| {
        //assert!(r.r#type() == after_args[0].0);
        //});

        // condition passes result to region 1 if true, or terminates with result
        let c = scf::condition(
            condition_rs[0].into(),
            //&rs,
            &[b],
            condition_location,
        );
        //before_block.append_operation(op2);
        //before_block.append_operation(op);
        for op in condition_ops {
            before_block.append_operation(op);
        }
        before_block.append_operation(c);
        before_region.append_block(before_block);

        // after
        let after_args = &[(index_type, body_location)];
        let after_region = Region::new();
        let after_block = Block::new(after_args);

        //let a: Value<'c, '_> = after_block.argument(0).unwrap().into();

        //let r_op = h.get("test").unwrap().clone();
        //let op = arith::addi(a, r_op, condition_location);
        //after_block.append_operation(op);

        //let op = self.build_int_op(10, body_location);
        let (_, body_ops) = self.lower_expr(body, env);
        println!("ops: {:?}", body_ops);

        let op = self.build_bool_op(false, condition_location);
        //let op = ops.last().unwrap();
        //let rs = op2r(&op);//op.results().map(|r| r.into()).collect::<Vec<Value>>();
        let mut rs = op.results().map(|r| r.into()).collect::<Vec<Value>>();
        //let op2 = self.build_int_op(0, condition_location);
        let rs2 = body_ops
            .last()
            .unwrap()
            .results()
            .map(|r| r.into())
            .collect::<Vec<Value>>();
        rs.extend(rs2);

        // check types
        rs.iter().for_each(|r| {
            println!("type: {:?}", r.r#type());
            println!("type: {:?}", before_args[0].0);
            //assert!(r.r#type() == before_args[0].0);
        });

        assert!(rs.len() == init_args.len());

        // yield passes result to region 0
        let y = scf::r#yield(&rs, body_location);
        after_block.append_operation(op);
        for op in body_ops {
            after_block.append_operation(op);
        }
        after_block.append_operation(y);

        after_region.append_block(after_block);

        let op = scf::r#while(
            &init_args,
            &after_args.iter().map(|x| x.0).collect::<Vec<Type<'_>>>(),
            before_region,
            after_region,
            body_location,
        );

        //env.push(op);
        //env.exit();
        //env.last_index()
        //let mut out = vec![];
        //out.push(init_op);
        //let r: Value<'c, '_> = op.result(0).unwrap().into();
        //let r: Vec<Value<'c, '_>> = op.results().map(|x| x.into()).collect::<Vec<_>>();
        //out.push(op);
        //let r = ops2r(&out);
        //let r = out.last().unwrap().results().map(|x| x.into()).collect::<Vec<_>>();

        //if depth == 0 {
        // function level, non-zero result means return immediately
        //} else {
        //}
        //let op = cf::cond_br(context
        //println!("op: {:?}", ops);
        //out.push(x_op);
        //for op in layer.ops.into_iter() {
        //out.push(op);
        //}

        (vec![], vec![init_op, init_op2, op]) //vec![op])
    }

    pub fn location<E: Extra>(&self, expr: &AstNode<E>) -> Location<'c> {
        expr.extra.location(self.context, self.files)
    }

    pub fn lower_expr<'a, E: Extra>(
        &self,
        expr: AstNode<E>,
        env: &mut Environment<'c>,
    ) -> (Vec<Value<'c, 'a>>, Vec<Operation<'c>>) {
        let index_type = Type::index(self.context);
        let location = self.location(&expr);

        match expr.node {
            Ast::BinaryOp(op, a, b) => {
                let (_, mut lhs_ops) = self.lower_expr(*a, env);
                let (_, mut rhs_ops) = self.lower_expr(*b, env);
                let r_lhs = lhs_ops.last().unwrap().result(0).unwrap();
                let r_rhs = rhs_ops.last().unwrap().result(0).unwrap();

                // types must be the same for binary operation, no implicit casting yet
                //assert!(r_lhs.len() == r_rhs.len());
                //std::iter::zip(r_lhs, r_rhs).for_each(|(a, b)| {
                //assert!(a.r#type() == b.r#type());
                //});

                //let r_lhs = r_lhs.pop().unwrap();
                //let r_rhs = r_rhs.pop().unwrap();//[0];

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
                    } //_ => unimplemented!("{:?}", op)
                };
                out.append(&mut lhs_ops);
                out.append(&mut rhs_ops);
                out.push(binop);
                //let r = out.last().unwrap().result(0).unwrap().into();
                //let r = binop.results().map(|x| x.into()).collect::<Vec<_>>();
                (vec![], out)
            }

            Ast::Identifier(ident) => {
                //let (r, ops)
                match ident.as_str() {
                    "True" => (vec![], vec![self.build_bool_op(true, location)]),
                    "False" => (vec![], vec![self.build_bool_op(false, location)]),
                    _ => {
                        //if let Some(r) = env.values.get(&ident) {
                        //println!("r: {:?}", r);
                        //}

                        //if let Some(r) = env.resolve(&ident) {
                        //r.r#type();
                        //let r = r.to_owned();

                        //(vec![r], vec![])
                        //(vec![], vec![])
                        //} else {
                        unimplemented!("Ident({:?})", ident)
                        //}
                    }
                }
                //(op2r(&op), vec![op])
                //(vec![], vec![op])
            }

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
                            let (_, mut arg_ops) = self.lower_expr(*arg, env);
                            ops.append(&mut arg_ops);
                            call_index.push(ops.len() - 1);
                        } //_ => unimplemented!("{:?}", a)
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
                //(ops2r(&ops), ops)
                ops.push(op);
                (vec![], ops)
                //let r = op2r(&op);
                //println!("ops: {:?}", ops);
                //(r, ops)
            }

            Ast::Literal(lit) => match lit {
                Literal::Float(f) => {
                    let op = self.build_float_op(f, location);
                    //(op2r(&op), vec![op])
                    (vec![], vec![op])
                }

                Literal::Int(x) => {
                    let op = self.build_int_op(x, location);
                    (vec![], vec![op])
                    //(op2r(&op), vec![op])
                }

                Literal::Bool(x) => {
                    let op = self.build_bool_op(x, location);
                    (vec![], vec![op])
                    //(op2r(&op), vec![op])
                } //_ => unimplemented!("{:?}", lit)
            },

            Ast::Sequence(exprs) => {
                let out = exprs
                    .into_iter()
                    .map(|expr| {
                        let (_, ops) = self.lower_expr(expr, env);
                        ops
                    })
                    .flatten()
                    .collect::<Vec<_>>();
                (vec![], out)
                //(ops2r(&out), out)
            }

            Ast::Variable(def) => {
                let mut out = vec![];
                let ident = def.name;
                // TODO: handle global variables properly, currently assume function context
                println!("variable ident {:?}", ident);
                let ty = MemRefType::new(index_type, &[], None, None);
                let op1 = memref::alloca(self.context, ty, &[], &[], None, location);
                let x: Value = op1.result(0).unwrap().into();

                let (_, ops) = self.lower_expr(*def.body.unwrap(), env);
                let r: Value<'c, '_> = ops.last().unwrap().result(0).unwrap().into();
                //env.values.insert(ident, r.clone());
                let op = memref::store(r, x, &[], location);
                out.push(op1);
                out.extend(ops);
                out.push(op);

                //out.extend(ops);
                (vec![], out)
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
                    let (_, ops) = self.lower_expr(*body, env);
                    //let index_type = Type::index(self.context);
                    //let location = expr.extra.location(self.context, self.files);

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
                //(op2r(&f), vec![f])
                (vec![], vec![f])
            }

            Ast::Return(maybe_expr) => match maybe_expr {
                Some(expr) => {
                    let (_, mut ops) = self.lower_expr(*expr, env);

                    //let results = env.last_values();
                    //let r = ops2r(&ops);
                    let results: Vec<Value> =
                        ops.last().unwrap().results().map(|r| r.into()).collect();
                    let ret_op = func::r#return(results.as_slice(), location);
                    ops.push(ret_op);
                    //(ops2r(&ops), ops)
                    (vec![], ops)
                }
                None => {
                    let op = func::r#return(&[], location);
                    //env.push(op);
                    //(op2r(&op), vec![op])
                    (vec![], vec![op])
                }
            },

            Ast::Conditional(condition, true_expr, maybe_false_expr) => {
                let (_, mut condition_ops) = self.lower_expr(*condition, env);
                //let index = env.last_index();
                //let r_conditions = env.values(index);//.last_values();
                let r_condition = condition_ops.last().unwrap().result(0).unwrap().into();
                let (_, true_ops) = self.lower_expr(*true_expr, env);

                //let mut s = Environment::default();
                let true_block = Block::new(&[]);
                for op in true_ops {
                    //for op in s.take_ops() {
                    true_block.append_operation(op);
                }
                true_block.append_operation(scf::r#yield(&[], location));

                let mut out = vec![];
                match maybe_false_expr {
                    Some(false_expr) => {
                        //let mut s = Environment::default();
                        let (_, false_ops) = self.lower_expr(*false_expr, env); //&mut s);
                        let false_block = Block::new(&[]);
                        for op in false_ops {
                            //for op in s.take_ops() {
                            false_block.append_operation(op);
                        }
                        false_block.append_operation(scf::r#yield(&[], location));
                        let then_region = Region::new();
                        then_region.append_block(true_block);
                        let else_region = Region::new();
                        else_region.append_block(false_block);
                        let if_op = scf::r#if(r_condition, &[], then_region, else_region, location);

                        out.append(&mut condition_ops);
                        //for op in condition_ops {
                        //out.push(op);
                        //}
                        out.push(if_op);
                        //(ops2r(&out), out)
                        (vec![], out)
                    }
                    None => {
                        let then_region = Region::new();
                        then_region.append_block(true_block);
                        let else_region = Region::new();
                        let if_op = scf::r#if(r_condition, &[], then_region, else_region, location);
                        //for op in condition_ops {
                        //out.push(op);
                        //}
                        out.append(&mut condition_ops);
                        out.push(if_op);
                        //out.push(op);
                        //(ops2r(&out), out)
                        (vec![], out) //vec![])
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
                        //let mut env = Environment::default();
                        let r: Value<'c, '_> = c.result(0).unwrap().into();
                        //env.values.insert(ident, r.clone());
                        let op = memref::store(r, x, &[], location);
                        //env.push(c);
                        //env.push(op1);
                        //env.push(op);
                        out.push(c);
                        out.push(op1);
                        out.push(op);
                    } //_ => unimplemented!("{:?}", target),
                }

                let (r, ops) = self.lower_expr(*rhs, env);
                out.extend(ops);
                (r, out)
                //(vec![], vec![])
            }

            Ast::Test(condition, body) => {
                let mut out = vec![];
                let condition_location = self.location(&condition);
                let mut h = std::collections::HashMap::new();
                let mut layer = Layer::new(LayerType::Static);
                let (_, ops) = self.build_loop(*condition, *body, env, layer, &mut h);
                //env.push(init_op);
                //env.push(init_op2);
                //out.push(init_op);
                //out.push(init_op2);
                out.extend(ops);
                (vec![], out) //vec![])
            }

            Ast::Builtin(b) => {
                match b {
                    Builtin::Assert(arg) => match *arg {
                        Argument::Positional(expr) => {
                            let mut out = vec![];
                            let (_, ops) = self.lower_expr(*expr, env);
                            let op = ops.last().unwrap();
                            let r = op.result(0).unwrap().into();
                            let msg = format!("assert at {}", location);
                            let assert_op = cf::assert(self.context, r, &msg, location);
                            out.extend(ops);
                            out.push(assert_op);
                            (vec![], out)
                        }
                    },
                    Builtin::Print(arg) => match *arg {
                        Argument::Positional(expr) => {
                            println!("x: {:?}", expr);

                            let ast_ty = self.type_from_expr(&expr);

                            // eval expr
                            let (_, mut ops) = self.lower_expr(*expr, env);
                            let r = ops.last().unwrap().result(0).unwrap();

                            let ident = match &ast_ty {
                                AstType::Int => "print_index",
                                AstType::Float => "print_float",
                                _ => unimplemented!(),
                            };

                            let f = attribute::FlatSymbolRefAttribute::new(self.context, ident);
                            let op =
                                func::call(self.context, f, &[r.into()], &[index_type], location);

                            ops.push(op);
                            (vec![], ops)
                        }
                    },
                    //_ => unimplemented!("{:?}", b),
                }
            } //_ => unimplemented!("{:?}", expr.node),
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
pub(crate) mod tests {
    use super::*;
    //use test_log::test;
    use melior::{
        dialect::DialectRegistry,
        ir,
        utility::{register_all_dialects, register_all_llvm_translations},
        Context,
    };

    pub fn gen_test(file_id: usize) -> AstNode<SimpleExtra> {
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
                            Ast::Assign(
                                AssignTarget::Identifier("x".to_string()),
                                Box::new(node(file_id, Ast::Literal(Literal::Int(123)))),
                            ),
                        ),
                        node(
                            file_id,
                            Ast::Test(
                                Box::new(node(file_id, Ast::Literal(Literal::Bool(true)))),
                                Box::new(node(
                                    file_id,
                                    Ast::Sequence(vec![
                                        node(
                                            file_id,
                                            Ast::BinaryOp(
                                                BinaryOperation::Subtract,
                                                node(file_id, Ast::Literal(Literal::Int(2))).into(),
                                                node(file_id, Ast::Literal(Literal::Int(1))).into(),
                                            ),
                                        ),
                                        node(
                                            file_id,
                                            Ast::Builtin(Builtin::Print(
                                                Argument::Positional(
                                                    node(file_id, Ast::Literal(Literal::Int(1)))
                                                        .into(), //node(file_id, Ast::Identifier("x".to_string())).into()
                                                )
                                                .into(),
                                            )),
                                        ),
                                        /*
                                        node(
                                            file_id,
                                            Ast::BinaryOp(
                                                BinaryOperation::Subtract,
                                                node(file_id, Ast::Identifier("x".to_string()))
                                                    .into(),
                                                node(file_id, Ast::Literal(Literal::Int(1))).into(),
                                            ),
                                        ),
                                        */
                                        //node(file_id, Ast::Identifier("x".to_string())),
                                        node(file_id, Ast::Literal(Literal::Int(1))),
                                    ]),
                                )),
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

    pub(crate) fn test_context() -> Context {
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
        let mut env = Environment::default();
        let (_, ops) = lower.lower_expr(ast, &mut env);
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
