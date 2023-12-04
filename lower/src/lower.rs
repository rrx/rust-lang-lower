use melior::{
    dialect::{arith, cf, func, llvm, memref, ods, scf},
    ir::{
        attribute::{StringAttribute, TypeAttribute},
        r#type::{FunctionType, MemRefType},
        *,
    },
    Context,
};

use crate::ast::*;
use crate::scope::{LayerIndex, LayerType, ScopeStack};
use codespan_reporting::files::SimpleFiles;

#[derive(Debug, Clone)]
pub struct Data {
    ty: AstType,
    is_static: bool,
}
impl Data {
    pub fn new(ty: AstType) -> Self {
        Self {
            ty,
            is_static: false,
        }
    }
}

pub type Environment<'c> = ScopeStack<'c, Data>;

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

pub struct Lower<'c> {
    pub(crate) context: &'c Context,
    files: &'c FileDB,
}

impl<'c> Lower<'c> {
    pub fn new(context: &'c Context, files: &'c FileDB) -> Self {
        Self { context, files }
    }

    pub fn type_from_expr<E: Extra>(&self, expr: &AstNode<E>, env: &Environment) -> AstType {
        match &expr.node {
            Ast::Literal(x) => match x {
                Literal::Int(_) => AstType::Int,
                Literal::Float(_) => AstType::Float,
                Literal::Bool(_) => AstType::Bool,
                Literal::Index(_) => AstType::Index,
            },
            Ast::Identifier(name) => {
                // infer type from the operation
                let r = env.value_from_name(name);
                let ty = r[0].r#type();
                if ty.is_index() {
                    AstType::Index
                } else if ty.is_integer() {
                    AstType::Int
                } else {
                    unreachable!("{:?}", ty);
                }
            }

            _ => unreachable!("{:?}", expr),
        }
    }

    pub fn from_type(&self, ty: &AstType) -> Type<'c> {
        match ty {
            AstType::Ptr => melior::ir::r#type::IntegerType::unsigned(self.context, 64).into(),
            AstType::Tuple(args) => {
                let types = args.iter().map(|a| self.from_type(a)).collect::<Vec<_>>();
                melior::ir::r#type::TupleType::new(self.context, &types).into()
            }
            AstType::Func(args, ret) => {
                let inputs = args.iter().map(|a| self.from_type(a)).collect::<Vec<_>>();
                let results = vec![self.from_type(ret)];
                melior::ir::r#type::FunctionType::new(self.context, &inputs, &results).into()
            }
            AstType::Int => melior::ir::r#type::IntegerType::new(self.context, 64).into(),
            AstType::Index => Type::index(self.context),
            AstType::Float => Type::float64(self.context),
            AstType::Bool => melior::ir::r#type::IntegerType::new(self.context, 1).into(),
            AstType::Unit => Type::none(self.context),
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
        let ty = melior::ir::r#type::IntegerType::new(self.context, 64);
        arith::constant(
            self.context,
            attribute::IntegerAttribute::new(value, ty.into()).into(),
            location,
        )
    }

    pub fn build_index_op(&self, value: i64, location: Location<'c>) -> Operation<'c> {
        let ty = Type::index(self.context);
        arith::constant(
            self.context,
            attribute::IntegerAttribute::new(value, ty.into()).into(),
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

    pub fn lower_static<E: Extra>(
        &self,
        expr: AstNode<E>,
        _env: &mut Environment<'c>,
    ) -> (AstType, Operation<'c>) {
        let location = self.location(&expr);
        match expr.node {
            Ast::Literal(Literal::Bool(x)) => (AstType::Bool, self.build_bool_op(x, location)),
            Ast::Literal(Literal::Int(x)) => (AstType::Int, self.build_int_op(x, location)),
            Ast::Literal(Literal::Float(x)) => (AstType::Float, self.build_float_op(x, location)),
            _ => unreachable!("{:?}", expr.node),
        }
    }

    pub fn build_while<'a, E: Extra>(
        &self,
        //init_args: &[Value<'c, 'a>],
        condition: AstNode<E>,
        body: AstNode<E>,
        env: &mut Environment<'c>,
    ) -> LayerIndex {
        let bool_type = self.from_type(&AstType::Bool);
        let condition_location = self.location(&condition);
        let body_location = self.location(&body);

        // before
        env.enter_block(&[]);
        self.lower_expr(condition, env);
        let condition_rs = env.last_values();
        // should be bool type
        assert!(condition_rs[0].r#type() == bool_type);
        let c = scf::condition(condition_rs[0].into(), &[], condition_location);

        // exit block
        let mut layer = env.exit();
        let before_block = layer.block.take().unwrap();
        let ops = layer.take_ops();
        for op in ops {
            before_block.append_operation(op);
        }
        before_block.append_operation(c);
        let before_region = Region::new();
        before_region.append_block(before_block);

        // after
        env.enter_block(&[]);
        let after_region = Region::new();
        self.lower_expr(body, env);
        // yield passes result to region 0
        let y = scf::r#yield(&[], body_location);
        env.push(y);

        let mut layer = env.exit();
        let after_block = layer.block.take().unwrap();
        let ops = layer.take_ops();
        for op in ops {
            after_block.append_operation(op);
        }
        after_region.append_block(after_block);

        // after complete

        env.push(scf::r#while(
            &[],
            &[],
            before_region,
            after_region,
            body_location,
        ));
        env.last_index().unwrap()
    }

    pub fn build_loop<'a, E: Extra>(
        &self,
        //init_args: &[Value<'c, 'a>],
        condition: AstNode<E>,
        body: AstNode<E>,
        env: &mut Environment<'c>,
    ) -> LayerIndex {
        /*
         * while condition_expr, body_expr, bool init_op, int init_op2 -> (bool, int) -> int:
         *   region0:
         *     block(bool arg0=init_op, int arg1=init_op2):
         *       bool result = condition_expr()
         *       # first param to continue is the condition
         *       # the following parameters are passed as arguments to region1 block
         *       # if condition is false, then arg1 is returned as result
         *       continue(result: bool) arg1: int
         *   region1:
         *     block(arg1: int):
         *       int result = body_expr()
         *       # yield arguments for block in region0
         *       yield true: bool, result: int
         *
         *    for a while Loop, we only need the condition and the body expressions
         *    we can ignore the return results
         *    we don't need to handle any free variables, since it has lexical scope with the
         *    function.
         *    yeild will have no args and continue will only have the condition which gets
         *    evaluated on each iteration.
         *    type is ()->()
         */
        let bool_type = self.from_type(&AstType::Bool);
        let index_type = self.from_type(&AstType::Index);
        let condition_location = self.location(&condition);
        let body_location = self.location(&body);

        //env.enter_closed();
        let x_op = self.build_index_op(1, condition_location);
        env.push_with_name(x_op, "test");

        // init args - bool, int
        let init_op = self.build_bool_op(true, condition_location);
        env.push_with_name(init_op, "init_op");
        let init_op2 = self.build_index_op(10, condition_location);
        env.push_with_name(init_op2, "init_op2");
        //env.dump();

        let init_args = vec![("arg0", "init_op"), ("arg1", "init_op2")];

        let before_args: Vec<(Type, Location, &str)> = init_args
            .into_iter()
            .map(|(arg_name, init_name)| {
                let r = env.value_from_name(init_name);
                println!("R: {:?}, {:?}", init_name, r);
                (r[0].r#type(), condition_location, arg_name)
            })
            .collect();

        env.enter_block(&before_args);
        println!("x: {:?}", env);

        self.lower_expr(condition, env);

        let condition_rs = env.last_values();
        // should be bool type
        assert!(condition_rs[0].r#type() == bool_type);

        // to pass to after

        // condition passes result to region 1 if true, or terminates with result
        let b_index = env.index_from_name("arg1").unwrap();
        println!("b: {:?}", b_index);
        let b = env.value_from_name("arg1");
        println!("b: {:?}", b);
        let b = env.values(b_index);
        println!("b: {:?}", b);

        println!("env: {:?}", env);
        let b: Value<'c, '_> = env.value_from_name("arg1")[0];
        let c = scf::condition(condition_rs[0].into(), &[b], condition_location);

        // exit block
        let mut layer = env.exit();
        let before_block = layer.block.take().unwrap();
        let ops = layer.take_ops();
        for op in ops {
            before_block.append_operation(op);
        }
        before_block.append_operation(c);
        let before_region = Region::new();
        before_region.append_block(before_block);

        // Before Complete

        // after
        let after_args = &[(index_type, body_location, "arg0")];
        env.enter_block(after_args);
        let after_region = Region::new();

        let op = arith::addi(
            env.value_from_name("arg0")[0],
            env.value_from_name("test")[0],
            condition_location,
        );
        env.push(op);

        let op = self.build_bool_op(false, condition_location);
        let index1 = env.push(op);

        self.lower_expr(body, env);
        let index2 = env.last_index().unwrap();

        let mut rs = env.values(index1);
        rs.extend(env.values(index2));

        // print types
        rs.iter().for_each(|r| {
            println!("type: {:?}", r.r#type());
            println!("type: {:?}", before_args[0].0);
        });

        // yield passes result to region 0
        let y = scf::r#yield(&rs, body_location);
        env.push(y);

        let mut layer = env.exit();
        let after_block = layer.block.take().unwrap();
        let ops = layer.take_ops();
        for op in ops {
            after_block.append_operation(op);
        }
        after_region.append_block(after_block);

        // after complete

        let init_args = vec![
            env.value_from_name("init_op")[0],
            env.value_from_name("init_op2")[0],
        ];
        env.push(scf::r#while(
            &init_args,
            &after_args.iter().map(|x| x.0).collect::<Vec<Type<'_>>>(),
            before_region,
            after_region,
            body_location,
        ));
        env.last_index().unwrap()

        //if depth == 0 {
        // function level, non-zero result means return immediately
        //} else {
        //}
    }

    pub fn location<E: Extra>(&self, expr: &AstNode<E>) -> Location<'c> {
        expr.extra.location(self.context, self.files)
    }

    pub fn lower_expr<'a, E: Extra>(
        &self,
        expr: AstNode<E>,
        env: &mut Environment<'c>,
    ) -> LayerIndex {
        //let index_type = Type::index(self.context);
        let location = self.location(&expr);

        match expr.node {
            Ast::Global(ident, expr) => {
                let block = Block::new(&[]);
                let (ast_ty, op1) = self.lower_static(*expr, env);
                let r = op1.result(0).unwrap().into();
                let op2 = llvm::r#return(Some(r), location);
                block.append_operation(op1);
                block.append_operation(op2);
                let region = Region::new();
                region.append_block(block);

                let i64_type = melior::ir::r#type::IntegerType::new(self.context, 64);
                let ty = TypeAttribute::new(i64_type.into());

                let name = StringAttribute::new(self.context, &ident);

                let linkage =
                    llvm::attributes::linkage(self.context, llvm::attributes::Linkage::External);
                let op = ods::llvm::mlir_global(self.context, region, ty, name, linkage, location);
                let index = env.push(op.into());

                //let index = LayerIndex::Static(env.fresh_index());
                let mut data = Data::new(ast_ty);
                data.is_static = true;

                env.name_index(index, &ident);
                env.index_data(index, data);
                //env.push_index(index);
                index
                //env.last_index().unwrap()
            }

            Ast::BinaryOp(op, a, b) => {
                println!("binop: {:?}, {:?}, {:?}", op, a, b);
                let index_lhs = self.lower_expr(*a, env);
                let index_rhs = self.lower_expr(*b, env);
                env.dump();
                println!("inx: {:?}, {:?}", index_lhs, index_rhs);
                let r_lhs = env.values(index_lhs)[0];
                let r_rhs = env.values(index_rhs)[0];
                println!("r: {:?}, {:?}", r_lhs, r_rhs);

                let data_lhs = env.data(&index_lhs).expect("LHS data missing");
                let data_rhs = env.data(&index_rhs).expect("RHS data missing");
                println!("ty: {:?}, {:?}", data_lhs.ty, data_lhs.ty);
                let ast_ty = data_lhs.ty.clone();

                assert_eq!(data_lhs.ty, data_rhs.ty);

                // types must be the same for binary operation, no implicit casting yet
                println!("bin: {:?}, {:?}", r_lhs.r#type(), r_rhs.r#type());
                assert!(r_lhs.r#type() == r_rhs.r#type());

                let ty = r_lhs.r#type();

                let binop = match op {
                    BinaryOperation::Add => {
                        if ty.is_index() || ty.is_integer() {
                            arith::addi(r_lhs.into(), r_rhs.into(), location)
                        } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                            arith::addf(r_lhs.into(), r_rhs.into(), location)
                        } else {
                            unimplemented!()
                        }
                    }
                    BinaryOperation::Subtract => {
                        if ty.is_index() || ty.is_integer() {
                            arith::subi(r_lhs.into(), r_rhs.into(), location)
                        } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                            arith::subf(r_lhs.into(), r_rhs.into(), location)
                        } else {
                            unimplemented!()
                        }
                    }
                    BinaryOperation::Equal => {
                        if ty.is_index() || ty.is_integer() {
                            arith::cmpi(
                                self.context,
                                arith::CmpiPredicate::Eq,
                                r_lhs.into(),
                                r_rhs.into(),
                                location,
                            )
                        } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
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

                let index = env.push(binop);
                let data = Data::new(ast_ty);
                env.index_data(index, data);
                index
                //env.last_index().unwrap()
            }

            Ast::Identifier(ident) => {
                match ident.as_str() {
                    "True" => {
                        let op = self.build_bool_op(true, location);
                        let index = env.push(op);
                        env.index_data(index, Data::new(AstType::Bool));
                        index
                        //env.last_index().unwrap()
                    }
                    "False" => {
                        let op = self.build_bool_op(false, location);
                        let index = env.push(op);
                        env.index_data(index, Data::new(AstType::Bool));
                        index
                        //env.last_index().unwrap()
                    }
                    _ => {
                        //println!("x: {:?}", ident);
                        //println!("env: {:?}", env);
                        let (index, data) = match env.index_from_name(ident.as_str()) {
                            Some(index) => {
                                let data = env.data(&index).unwrap().clone();
                                (index, data)
                            }
                            _ => unimplemented!("Ident({:?})", ident),
                        };

                        let is_static = match index {
                            LayerIndex::Op(_) => data.is_static,
                            LayerIndex::Static(_) => true,
                            _ => false,
                        };

                        if is_static {
                            println!("y: {:?}", index);
                            let source_data = env.data(&index).unwrap().clone();
                            // create a new type, drop other information (static)
                            let data = Data::new(source_data.ty);

                            let ty = self.from_type(&data.ty);

                            let opaque_ty = llvm::r#type::opaque_pointer(self.context);
                            let f = attribute::FlatSymbolRefAttribute::new(self.context, &ident);
                            // get global
                            let op1: Operation<'c> = ods::llvm::mlir_addressof(
                                self.context,
                                opaque_ty.into(),
                                f,
                                location,
                            )
                            .into();
                            let r = op1.result(0).unwrap().into();
                            let options = llvm::LoadStoreOptions::new();
                            let op2 = llvm::load(self.context, r, ty.into(), location, options);

                            // maybe cast?
                            //let op3 = arith::index_cast(r, Type::index(self.context), location);

                            env.push(op1);
                            let index = env.push(op2);
                            env.index_data(index, data);
                            //env.push(op3);
                            index
                        } else {
                            env.push_index(index);
                            index
                        }
                    }
                }
            }

            Ast::Call(expr, args) => {
                // function to call
                //env.dump();
                let (f, data) = match &expr.node {
                    Ast::Identifier(ident) => {
                        let index = env.index_from_name(ident).unwrap();
                        let data = env.data(&index).unwrap();
                        println!("data: {:?}, {:?}", data, index);

                        (
                            attribute::FlatSymbolRefAttribute::new(self.context, ident),
                            data,
                        )
                    }
                    _ => {
                        unimplemented!("not implemented: {:?}", expr.node);
                    }
                };

                println!("data: {:?}", data);
                if let AstType::Func(func_arg_types, ret) = &data.ty {
                    let data = Data::new(*ret.clone());
                    let ret_ty = self.from_type(ret);
                    // handle call arguments
                    let mut indices = vec![];
                    for a in args {
                        match a {
                            Argument::Positional(arg) => {
                                let index = self.lower_expr(*arg, env);
                                indices.push(index);
                            } //_ => unimplemented!("{:?}", a)
                        };
                    }

                    let call_args = indices
                        .into_iter()
                        .map(|index| env.values(index)[0])
                        .collect::<Vec<_>>();

                    let op = func::call(self.context, f, call_args.as_slice(), &[ret_ty], location);
                    let index = env.push(op);
                    env.index_data(index, data);

                    //env.last_index().unwrap()
                    index
                } else {
                    unimplemented!("calling non function type: {:?}", data);
                }
            }

            Ast::Literal(lit) => match lit {
                Literal::Float(f) => {
                    let op = self.build_float_op(f, location);
                    let index = env.push(op);
                    env.index_data(index, Data::new(AstType::Float));
                    index
                    //env.last_index().unwrap()
                }

                Literal::Int(x) => {
                    let op = self.build_int_op(x, location);
                    let index = env.push(op);
                    env.index_data(index, Data::new(AstType::Int));
                    index
                    //env.last_index().unwrap()
                }

                Literal::Index(x) => {
                    let op = self.build_index_op(x as i64, location);
                    let index = env.push(op);
                    env.index_data(index, Data::new(AstType::Index));
                    index
                    //env.last_index().unwrap()
                }

                Literal::Bool(x) => {
                    let op = self.build_bool_op(x, location);
                    let index = env.push(op);
                    env.index_data(index, Data::new(AstType::Bool));
                    index
                    //env.last_index().unwrap()
                } //_ => unimplemented!("{:?}", lit)
            },

            Ast::Sequence(exprs) => {
                exprs.into_iter().for_each(|expr| {
                    self.lower_expr(expr, env);
                });
                env.last_index().unwrap()
            }

            Ast::Variable(def) => {
                let ident = def.name;
                // TODO: handle global variables properly, currently assume function context
                println!("variable ident {:?}", ident);
                let index_type = Type::index(self.context);
                let ty = MemRefType::new(index_type, &[], None, None);
                let op1 = memref::alloca(self.context, ty, &[], &[], None, location);
                let x = env.push(op1);
                self.lower_expr(*def.body.unwrap(), env);
                let r = env.last_values();
                let op = memref::store(r[0], env.values(x)[0], &[], location);
                env.push_with_name(op, &ident);
                env.last_index().unwrap()
            }

            Ast::Definition(def) => {
                println!("name {:?}", def.name);
                let mut params = vec![];
                let ty = self.from_type(&*def.return_type);
                let mut ast_types = vec![];
                let ast_ret_type = def.return_type;

                for p in def.params {
                    match p.node {
                        Parameter::Normal(ident, ty) => {
                            println!("params {:?}: {:?}", ident, ty);
                            let location = p.extra.location(self.context, self.files);
                            let ir_ty = self.from_type(&ty);
                            params.push((ir_ty, location, "x"));
                            ast_types.push(ty);
                        }
                        _ => {
                            println!("not implemented: {:?}", p);
                            unimplemented!();
                        }
                    }
                }

                let region = Region::new();

                let mut attributes = vec![(
                    Identifier::new(self.context, "sym_visibility"),
                    StringAttribute::new(self.context, "private").into(),
                )];

                if let Some(body) = def.body {
                    env.enter_block(params.as_slice());
                    self.lower_expr(*body, env);
                    let mut layer = env.exit();
                    let block = layer.block.take().unwrap();
                    for op in layer.take_ops() {
                        block.append_operation(op);
                    }
                    region.append_block(block);

                    // declare as C interface only if body is defined
                    // function declarations represent functions that are already C interfaces
                    attributes.push((
                        Identifier::new(self.context, "llvm.emit_c_interface"),
                        Attribute::unit(self.context),
                    ));
                }

                let types = params.iter().map(|x| x.0).collect::<Vec<Type>>();

                let ret_type = if ty.is_none() { vec![] } else { vec![ty] };

                let func_type = FunctionType::new(self.context, &types, &ret_type);

                let f = func::func(
                    self.context,
                    StringAttribute::new(self.context, &def.name),
                    TypeAttribute::new(func_type.into()),
                    region,
                    &attributes,
                    location,
                );

                let index = env.push(f);
                env.name_index(index, &def.name);
                let f_type = AstType::Func(ast_types, ast_ret_type);
                let mut data = Data::new(f_type);
                data.is_static = true;
                env.index_data(index, data);
                env.last_index().unwrap()
            }

            Ast::Return(maybe_expr) => match maybe_expr {
                Some(expr) => {
                    let location = self.location(&expr);
                    self.lower_expr(*expr, env);
                    let ret_op = func::r#return(&env.last_values(), location);
                    env.push(ret_op);
                    env.last_index().unwrap()
                }
                None => {
                    let op = func::r#return(&[], location);
                    env.push(op);
                    env.last_index().unwrap()
                }
            },

            Ast::Conditional(condition, true_expr, maybe_false_expr) => {
                let index_conditions = self.lower_expr(*condition, env);
                env.enter_block(&[]);
                self.lower_expr(*true_expr, env);
                let mut layer = env.exit();
                let true_block = layer.block.take().unwrap();

                for op in layer.take_ops() {
                    true_block.append_operation(op);
                }
                true_block.append_operation(scf::r#yield(&[], location));

                match maybe_false_expr {
                    Some(false_expr) => {
                        env.enter_block(&[]);
                        self.lower_expr(*false_expr, env);
                        let mut layer = env.exit();
                        let false_block = layer.block.take().unwrap();
                        for op in layer.take_ops() {
                            false_block.append_operation(op);
                        }
                        false_block.append_operation(scf::r#yield(&[], location));
                        let then_region = Region::new();
                        then_region.append_block(true_block);
                        let else_region = Region::new();
                        else_region.append_block(false_block);
                        let if_op = scf::r#if(
                            env.values(index_conditions)[0],
                            &[],
                            then_region,
                            else_region,
                            location,
                        );
                        env.push(if_op);
                        env.last_index().unwrap()
                    }
                    None => {
                        let then_region = Region::new();
                        then_region.append_block(true_block);
                        let else_region = Region::new();
                        let if_op = scf::r#if(
                            env.values(index_conditions)[0],
                            &[],
                            then_region,
                            else_region,
                            location,
                        );
                        env.push(if_op);
                        env.last_index().unwrap()
                    }
                }
            }

            Ast::Assign(target, rhs) => {
                match target {
                    AssignTarget::Identifier(ident) => {
                        // TODO: handle global variables properly, currently assume function context
                        let ty = env.current_layer_type();
                        println!("assign ident {:?}, {:?}", ident, ty);
                        match ty {
                            LayerType::Static => {
                                unreachable!(
                                    "Assign not possible in global context, use Global instead"
                                );
                            }
                            _ => {
                                let index = self.lower_expr(*rhs, env);
                                //let index = env.last_index().unwrap();
                                env.name_index(index, &ident);
                                env.dump();
                                env.last_index().unwrap()
                            }
                        }
                    } //_ => unimplemented!("{:?}", target),
                }
            }

            Ast::While(condition, body) => {
                self.build_while(*condition, *body, env);
                env.last_index().unwrap()
            }

            Ast::Test(condition, body) => {
                self.build_loop(*condition, *body, env);
                env.last_index().unwrap()
            }

            Ast::Builtin(b, mut args) => {
                let arity = b.arity();
                assert_eq!(arity, args.len());
                match b {
                    Builtin::Assert => {
                        let arg = args.pop().unwrap();
                        match arg {
                            Argument::Positional(expr) => {
                                let index = self.lower_expr(*expr, env);
                                let msg = format!("assert at {}", location);
                                let assert_op =
                                    cf::assert(self.context, env.values(index)[0], &msg, location);
                                env.push(assert_op);
                                env.last_index().unwrap()
                            }
                        }
                    }
                    Builtin::Print => {
                        let arg = args.pop().unwrap();
                        match arg {
                            Argument::Positional(expr) => {
                                let ast_ty = self.type_from_expr(&expr, env);

                                // eval expr
                                let index = self.lower_expr(*expr, env);
                                let r = env.values(index);
                                let ty = r[0].r#type();

                                // Select the baked version based on parameters
                                // TODO: A more dynamic way of doing this
                                // TODO: We only want to import these if they are referenced
                                let ident = if ty.is_index() || ty.is_integer() {
                                    "print_index"
                                } else if ty.is_f64() {
                                    "print_float"
                                } else {
                                    unimplemented!("{:?}", &ast_ty)
                                };

                                let f = attribute::FlatSymbolRefAttribute::new(self.context, ident);
                                //let index_type = Type::index(self.context);
                                let op =
                                    func::call(self.context, f, &env.values(index), &[], location);

                                env.push(op);
                                env.last_index().unwrap()
                            }
                        }
                    } //_ => unimplemented!("{:?}", b),
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
                return_type: AstType::Unit.into(),
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
                return_type: AstType::Unit.into(),
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
                return_type: AstType::Int.into(),
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
                                            Ast::Builtin(
                                                Builtin::Print,
                                                vec![Argument::Positional(
                                                    node(file_id, Ast::Literal(Literal::Int(1)))
                                                        .into(),
                                                )],
                                            )
                                            .into(),
                                        ),
                                        node(
                                            file_id,
                                            Ast::BinaryOp(
                                                BinaryOperation::Subtract,
                                                node(file_id, Ast::Identifier("x".to_string()))
                                                    .into(),
                                                node(file_id, Ast::Literal(Literal::Int(1))).into(),
                                            ),
                                        ),
                                        node(file_id, Ast::Literal(Literal::Index(1))),
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

    pub fn gen_while(file_id: usize) -> AstNode<SimpleExtra> {
        let mut seq = prelude(file_id);
        // global variable
        seq.push(node(
            file_id,
            Ast::Global(
                "z".into(),
                Box::new(node(file_id, Ast::Literal(Literal::Int(122)))),
            ),
        ));
        seq.push(node(
            file_id,
            Ast::Definition(Definition {
                name: "test".into(),
                params: vec![],
                return_type: AstType::Int.into(),
                body: Some(Box::new(node(
                    file_id,
                    Ast::Sequence(vec![
                        // global variable x = 123
                        node(
                            file_id,
                            Ast::Assign(
                                AssignTarget::Identifier("x".to_string()),
                                Box::new(node(file_id, Ast::Literal(Literal::Int(123)))),
                            ),
                        ),
                        node(
                            file_id,
                            Ast::While(
                                // condition
                                Box::new(node(file_id, Ast::Literal(Literal::Bool(true)))),
                                // body
                                Box::new(node(
                                    file_id,
                                    Ast::Sequence(vec![
                                        node(
                                            file_id,
                                            Ast::Assign(
                                                AssignTarget::Identifier("y".to_string()),
                                                Box::new(node(
                                                    file_id,
                                                    Ast::Literal(Literal::Int(1234)),
                                                )),
                                            ),
                                        ),
                                        node(
                                            file_id,
                                            Ast::Assign(
                                                AssignTarget::Identifier("y".to_string()),
                                                Box::new(node(
                                                    file_id,
                                                    Ast::BinaryOp(
                                                        BinaryOperation::Subtract,
                                                        node(
                                                            file_id,
                                                            Ast::Identifier("x".to_string()),
                                                        )
                                                        .into(),
                                                        node(
                                                            file_id,
                                                            Ast::Identifier("x".to_string()),
                                                        )
                                                        .into(),
                                                    ),
                                                )),
                                            ),
                                        ),
                                        node(
                                            file_id,
                                            Ast::Builtin(
                                                Builtin::Print,
                                                vec![Argument::Positional(
                                                    node(file_id, Ast::Identifier("y".to_string()))
                                                        .into(),
                                                )],
                                            ),
                                        ),
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
    fn test_while() {
        let context = test_context();
        let mut files = FileDB::new();
        let file_id = files.add("test.py".into(), "test".into());
        let ast = gen_while(file_id);
        let lower = Lower::new(&context, &files);
        let mut env: Environment = Environment::default();
        lower.lower_expr(ast, &mut env);
        let module = ir::Module::new(Location::unknown(&context));
        for op in env.take_ops() {
            module.body().append_operation(op);
        }
        let s = module.as_operation().to_string();
        println!("{}", s);
        assert!(module.as_operation().verify());
    }

    #[test]
    fn test_loop() {
        let context = test_context();
        let mut files = FileDB::new();
        let file_id = files.add("test.py".into(), "test".into());
        let ast = gen_test(file_id);
        println!("ast: {:?}", ast);
        let lower = Lower::new(&context, &files);
        let mut env: Environment = Environment::default();
        lower.lower_expr(ast, &mut env);
        let module = ir::Module::new(Location::unknown(&context));
        for op in env.take_ops() {
            module.body().append_operation(op);
        }
        let s = module.as_operation().to_string();
        println!("{}", s);
        assert!(module.as_operation().verify());
    }
}
