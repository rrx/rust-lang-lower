use melior::{
    dialect::{arith, cf, func, llvm, memref, ods, scf},
    ir::{
        attribute::{
            DenseElementsAttribute, FloatAttribute, IntegerAttribute, StringAttribute,
            TypeAttribute,
        },
        r#type::{FunctionType, IntegerType, MemRefType, RankedTensorType},
        *,
    },
    Context,
};

use crate::ast::*;
use crate::scope::{Layer, LayerIndex, LayerType, ScopeStack};
use codespan_reporting::files::SimpleFiles;

#[derive(Debug, Clone)]
pub struct Data {
    ty: AstType,
    is_static: bool,
}
impl Data {
    pub fn new_static(ty: AstType) -> Self {
        Self {
            ty,
            is_static: true,
        }
    }

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
                let r = env.value0_from_name(name);
                let ty = r.r#type();
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
            AstType::Ptr(v) => Type::index(self.context),
            AstType::Tuple(args) => {
                let types = args.iter().map(|a| self.from_type(a)).collect::<Vec<_>>();
                melior::ir::r#type::TupleType::new(self.context, &types).into()
            }
            AstType::Func(args, ret) => {
                let inputs = args.iter().map(|a| self.from_type(a)).collect::<Vec<_>>();
                let results = vec![self.from_type(ret)];
                melior::ir::r#type::FunctionType::new(self.context, &inputs, &results).into()
            }
            AstType::Int => IntegerType::new(self.context, 64).into(),
            AstType::Index => Type::index(self.context),
            AstType::Float => Type::float64(self.context),
            AstType::Bool => IntegerType::new(self.context, 1).into(),
            AstType::Unit => Type::none(self.context),
        }
    }

    pub fn build_bool_op(&self, value: bool, location: Location<'c>) -> Operation<'c> {
        let bool_type = IntegerType::new(self.context, 1);
        arith::constant(
            self.context,
            attribute::IntegerAttribute::new(if value { 1 } else { 0 }, bool_type.into()).into(),
            location,
        )
    }

    pub fn build_int_op(&self, value: i64, location: Location<'c>) -> Operation<'c> {
        let ty = IntegerType::new(self.context, 64);
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
        let layer = self.build_block(&[], env);
        env.enter(layer);
        //env.enter_block(&[]);
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
        //env.enter_block(&[]);
        let layer = self.build_block(&[], env);
        env.enter(layer);
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
        //let index_type = self.from_type(&AstType::Index);
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

        let init_args = vec![
            (AstType::Bool, "arg0", "init_op"),
            (AstType::Index, "arg1", "init_op2"),
        ];

        let before_args: Vec<(AstType, Location, String)> = init_args
            .into_iter()
            .map(|(ast_ty, arg_name, init_name)| {
                let index = env.index_from_name(init_name).unwrap();
                let data = Data::new(ast_ty); //env.data(&index).unwrap();
                                              //let r = env.value0_from_name(init_name);
                                              //(r.r#type(), condition_location, arg_name.to_string())
                (data.ty.clone(), condition_location, arg_name.to_string())
            })
            .collect();

        //env.enter_block(&before_args);
        let layer = self.build_block(&before_args, env);
        env.enter(layer);

        self.lower_expr(condition, env);

        let condition_rs = env.last_values();
        // should be bool type
        assert!(condition_rs[0].r#type() == bool_type);

        // to pass to after

        // condition passes result to region 1 if true, or terminates with result
        let b = env.value0_from_name("arg1");
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
        let after_args = &[(AstType::Index, body_location, "arg0".to_string())];
        //env.enter_block(after_args);
        //env.enter(self.build_block(&before_args, env));
        let layer = self.build_block(after_args, env);
        env.enter(layer);

        let after_region = Region::new();

        let op = arith::addi(
            env.value0_from_name("arg0"),
            env.value0_from_name("test"),
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
            log::debug!("type: {:?}", r.r#type());
            log::debug!("type: {:?}", before_args[0].0);
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
            env.value0_from_name("init_op"),
            env.value0_from_name("init_op2"),
        ];
        env.push(scf::r#while(
            &init_args,
            &after_args
                .iter()
                .map(|x| self.from_type(&x.0))
                .collect::<Vec<Type<'_>>>(),
            before_region,
            after_region,
            body_location,
        ));
        env.last_index().unwrap()
    }

    pub fn location<E: Extra>(&self, expr: &AstNode<E>) -> Location<'c> {
        expr.extra.location(self.context, self.files)
    }

    pub fn build_static(
        &self,
        name: &str,
        ty: Type<'c>,
        value: Attribute<'c>,
        constant: bool,
        location: Location<'c>,
    ) -> Operation<'c> {
        let integer_type = IntegerType::new(self.context, 64).into();
        let attribute =
            DenseElementsAttribute::new(RankedTensorType::new(&[], ty, None).into(), &[value])
                .unwrap();
        let alignment = IntegerAttribute::new(8, integer_type);
        let memspace = IntegerAttribute::new(0, integer_type).into();

        memref::global(
            self.context,
            name,
            Some("private"),
            MemRefType::new(ty, &[], None, Some(memspace)),
            Some(attribute.into()),
            constant,
            Some(alignment),
            location,
        )
    }

    pub fn lower_llvm_global_int<E: Extra>(
        &self,
        name: &str,
        expr: AstNode<E>,
        env: &mut Environment<'c>,
    ) -> LayerIndex {
        let location = self.location(&expr);
        let block = Block::new(&[]);
        let (ast_ty, op1) = self.lower_static(expr, env);
        let r = op1.result(0).unwrap().into();
        let op2 = llvm::r#return(Some(r), location);
        block.append_operation(op1);
        block.append_operation(op2);
        let region = Region::new();
        region.append_block(block);

        let i64_type = IntegerType::new(self.context, 64);
        let ty = TypeAttribute::new(i64_type.into());

        let name_attr = StringAttribute::new(self.context, name);

        let linkage = llvm::attributes::linkage(self.context, llvm::attributes::Linkage::External);
        let op = ods::llvm::mlir_global(self.context, region, ty, name_attr, linkage, location);
        let index = env.push(op.into());

        env.name_index(index, name);
        env.index_data(index, Data::new_static(ast_ty));
        index
    }

    pub fn lower_llvm_load_global(
        &self,
        ident: &str,
        ty: Type<'c>,
        location: Location<'c>,
        env: &mut Environment<'c>,
    ) -> LayerIndex {
        // load global variable
        let opaque_ty = llvm::r#type::opaque_pointer(self.context);
        let f = attribute::FlatSymbolRefAttribute::new(self.context, ident);
        // get global
        let op1: Operation<'c> =
            ods::llvm::mlir_addressof(self.context, opaque_ty.into(), f, location).into();

        let r = op1.result(0).unwrap().into();
        let options = llvm::LoadStoreOptions::new();
        let op2 = llvm::load(self.context, r, ty, location, options);
        // maybe cast?
        //let op3 = arith::index_cast(r, Type::index(self.context), location);
        env.push(op1);
        env.push(op2)
    }

    pub fn lower_llvm_store<E: Extra>(
        &self,
        ident: &str,
        ast: AstNode<E>,
        env: &mut Environment<'c>,
    ) -> LayerIndex {
        let location = self.location(&ast);
        let value_index = self.lower_expr(ast, env);
        let opaque_ty = llvm::r#type::opaque_pointer(self.context);
        let f = attribute::FlatSymbolRefAttribute::new(self.context, ident);
        // get global address
        let op1: Operation<'c> =
            ods::llvm::mlir_addressof(self.context, opaque_ty.into(), f, location).into();

        let addr_index = env.push(op1);

        let r_value = env.value0(value_index);
        let r_addr = env.value0(addr_index);

        let options = llvm::LoadStoreOptions::new();
        env.push(llvm::store(
            self.context,
            r_value,
            r_addr,
            location,
            options,
        ))
    }

    pub fn build_block(
        &self,
        arguments: &[(AstType, Location<'c>, String)],
        env: &mut ScopeStack<'c, Data>,
    ) -> Layer<'c> {
        // create a new layer, adding arguments as scoped variables
        let mut layer = Layer::new(LayerType::Block);
        for (offset, a) in arguments.iter().enumerate() {
            let index = env.fresh_argument();
            layer.name_index(index, &a.2);
            let data = Data::new(a.0.clone());
            env.index_data(index, data);
            // record argument offset
            layer.index.insert(index, offset);
        }
        let block_args = arguments
            .iter()
            .map(|a| (self.from_type(&a.0), a.1))
            .collect::<Vec<_>>();
        let block = Block::new(&block_args);
        layer.block = Some(block);
        layer
    }

    pub fn lower_expr<'a, E: Extra>(
        &self,
        expr: AstNode<E>,
        env: &mut ScopeStack<'c, Data>,
    ) -> LayerIndex {
        let location = self.location(&expr);

        match expr.node {
            Ast::Global(ident, expr) => {
                let global_name = if env.current_layer_type() == LayerType::Static {
                    ident.clone()
                } else {
                    // we create a unique global name to prevent conflict
                    // and then we add ops to provide a local reference to the global name
                    let mut global_name = ident.clone();
                    global_name.push_str(&env.unique_static_name());
                    global_name
                };

                // evaluate expr at compile time
                let (ast_ty, op) = match expr.node {
                    Ast::Literal(Literal::Bool(x)) => {
                        let ast_ty = AstType::Bool;
                        let ty = self.from_type(&ast_ty);
                        let v = if x { 1 } else { 0 };
                        let value = IntegerAttribute::new(v, ty).into();
                        let op = self.build_static(&global_name, ty, value, false, location);
                        (ast_ty, op)
                    }

                    Ast::Literal(Literal::Int(x)) => {
                        let ast_ty = AstType::Int;
                        let ty = self.from_type(&ast_ty);
                        let value = IntegerAttribute::new(x, ty).into();
                        let op = self.build_static(&global_name, ty, value, false, location);
                        (ast_ty, op)
                    }

                    Ast::Literal(Literal::Index(x)) => {
                        let ast_ty = AstType::Int;
                        let ty = self.from_type(&ast_ty);
                        let value = IntegerAttribute::new(x as i64, ty).into();
                        let op = self.build_static(&global_name, ty, value, false, location);
                        (ast_ty, op)
                    }

                    Ast::Literal(Literal::Float(x)) => {
                        let ast_ty = AstType::Float;
                        let ty = self.from_type(&ast_ty);
                        let value = FloatAttribute::new(self.context, x, ty).into();
                        let op = self.build_static(&global_name, ty, value, false, location);
                        (ast_ty, op)
                    }

                    _ => unreachable!("{:?}", expr.node),
                };

                let ptr_data = Data::new_static(AstType::Ptr(ast_ty.clone().into()));
                if env.current_layer_type() == LayerType::Static {
                    // STATIC/GLOBAL VARIABLE
                    let index = env.push_with_name(op, &global_name);
                    env.index_data(index, ptr_data);
                    index
                } else {
                    // STATIC VARIABLE IN FUNCTION CONTEXT

                    // static operation
                    let index = env.push_static(op, &global_name);
                    env.index_data(index, ptr_data);

                    // emit load of static variable, and put the name in scope
                    // we don't actually need to do this unless the value is needed.
                    // TODO: move this to where the global variable is referenced.
                    // We can also check to see if the variable has been loaded already
                    // and we can skip a second load as long as the global var hasn't been
                    // modified.
                    let local_data = Data::new(ast_ty.clone());
                    let ty = self.from_type(&local_data.ty);

                    let ty = MemRefType::new(ty, &[], None, None);
                    // load using global name
                    let op1 = memref::get_global(self.context, &global_name, ty, location);

                    let r = op1.result(0).unwrap().into();
                    let op2 = memref::load(r, &[], location);

                    env.push(op1);
                    // name using locally scoped name
                    let index = env.push_with_name(op2, &ident);
                    env.index_data(index, local_data);
                    index
                }
            }

            Ast::UnaryOp(op, a) => {
                let index_rhs = self.lower_expr(*a, env);

                // get the type of the RHS
                let ty = env.value0(index_rhs).r#type();

                match op {
                    UnaryOperation::Minus => {
                        if ty.is_index() {
                            unreachable!("Unable to negate index type");
                        } else if ty.is_integer() {
                            // Multiply by -1
                            let int_op = self.build_int_op(-1, location);
                            let index_lhs = env.push(int_op);
                            let r = env.value0(index_lhs);
                            let r_rhs = env.value0(index_rhs);
                            env.push(arith::muli(r.into(), r_rhs.into(), location))
                        } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                            // arith has an op for negation
                            let r_rhs = env.value0(index_rhs);
                            env.push(arith::negf(r_rhs.into(), location))
                        } else {
                            unimplemented!()
                        }
                    }
                }
            }

            Ast::BinaryOp(op, a, b) => {
                log::debug!("binop: {:?}, {:?}, {:?}", op, a, b);
                let mut index_lhs = self.lower_expr(*a, env);
                let mut index_rhs = self.lower_expr(*b, env);

                let mut ty_lhs = env.data(&index_lhs).expect("LHS data missing").ty.clone();
                let mut ty_rhs = env.data(&index_rhs).expect("RHS data missing").ty.clone();
                log::debug!("ty: {:?}, {:?}", ty_lhs, ty_rhs);

                log::debug!("inx: {:?}, {:?}", index_lhs, index_rhs);
                {
                    if let AstType::Ptr(ty) = ty_lhs {
                        ty_lhs = *ty;
                    }

                    if let AstType::Ptr(ty) = ty_rhs {
                        ty_rhs = *ty;
                    }

                    let r_lhs = env.value0(index_lhs);
                    if r_lhs.r#type().is_mem_ref() {
                        // load
                        let op = memref::load(r_lhs, &[], location);
                        index_lhs = env.push(op);
                        env.index_data(index_lhs, Data::new(ty_lhs.clone()));
                    }

                    let r_rhs = env.value0(index_rhs);
                    if r_rhs.r#type().is_mem_ref() {
                        // load
                        let op = memref::load(r_rhs, &[], location);
                        index_rhs = env.push(op);
                        env.index_data(index_rhs, Data::new(ty_rhs.clone()));
                    }
                }

                let ast_ty = ty_lhs.clone();
                assert_eq!(ty_lhs, ty_rhs);

                // types must be the same for binary operation, no implicit casting yet
                let a = env.value0(index_lhs);
                let b = env.value0(index_rhs);
                //env.dump();
                log::debug!("bin: {:?}, {:?}", a, b);
                log::debug!("ty: {:?}, {:?}", a.r#type(), b.r#type());
                //assert!(a.r#type() == b.r#type());

                let a = env.value0(index_lhs);
                let ty = a.r#type();
                let a = env.value0(index_lhs);
                let b = env.value0(index_rhs);

                let binop = match op {
                    BinaryOperation::Divide => {
                        if ty.is_index() {
                            // index type is unsigned
                            arith::divui(a, b, location)
                        } else if ty.is_integer() {
                            // we assume all integers are signed for now
                            arith::divsi(a, b, location)
                        } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                            arith::divf(a, b, location)
                        } else {
                            unimplemented!()
                        }
                    }
                    BinaryOperation::Multiply => {
                        if ty.is_index() || ty.is_integer() {
                            arith::muli(a, b, location)
                        } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                            arith::mulf(a, b, location)
                        } else {
                            unimplemented!()
                        }
                    }
                    BinaryOperation::Add => {
                        if ty.is_index() || ty.is_integer() {
                            arith::addi(a, b, location)
                        } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                            arith::addf(a, b, location)
                        } else {
                            unimplemented!()
                        }
                    }
                    BinaryOperation::Subtract => {
                        if ty.is_index() || ty.is_integer() {
                            arith::subi(a, b, location)
                        } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                            arith::subf(a, b, location)
                        } else {
                            unimplemented!()
                        }
                    }
                    BinaryOperation::GTE => {
                        if ty.is_index() {
                            // unsigned
                            arith::cmpi(self.context, arith::CmpiPredicate::Uge, a, b, location)
                        } else if ty.is_integer() {
                            // signed
                            arith::cmpi(self.context, arith::CmpiPredicate::Sge, a, b, location)
                        } else {
                            unimplemented!();
                        }
                    }
                    BinaryOperation::GT => {
                        if ty.is_index() {
                            // unsigned
                            arith::cmpi(self.context, arith::CmpiPredicate::Ugt, a, b, location)
                        } else if ty.is_integer() {
                            // signed
                            arith::cmpi(self.context, arith::CmpiPredicate::Sgt, a, b, location)
                        } else {
                            unimplemented!();
                        }
                    }
                    BinaryOperation::NE => {
                        if ty.is_index() || ty.is_integer() {
                            arith::cmpi(self.context, arith::CmpiPredicate::Ne, a, b, location)
                        } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                            // ordered comparison
                            arith::cmpf(self.context, arith::CmpfPredicate::One, a, b, location)
                        } else {
                            unimplemented!()
                        }
                    }
                    BinaryOperation::EQ => {
                        if ty.is_index() || ty.is_integer() {
                            arith::cmpi(self.context, arith::CmpiPredicate::Eq, a, b, location)
                        } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                            // ordered comparison
                            arith::cmpf(self.context, arith::CmpfPredicate::Oeq, a, b, location)
                        } else {
                            unimplemented!()
                        }
                    } //_ => unimplemented!("{:?}", op)
                };

                let index = env.push(binop);
                let data = Data::new(ast_ty);
                env.index_data(index, data);
                index
            }

            Ast::Identifier(ident) => {
                match ident.as_str() {
                    "True" => {
                        let op = self.build_bool_op(true, location);
                        let index = env.push(op);
                        env.index_data(index, Data::new(AstType::Bool));
                        index
                    }
                    "False" => {
                        let op = self.build_bool_op(false, location);
                        let index = env.push(op);
                        env.index_data(index, Data::new(AstType::Bool));
                        index
                    }
                    _ => {
                        //env.dump();
                        let (index, data) = match env.index_from_name(ident.as_str()) {
                            Some(index) => {
                                let data = env.data(&index).unwrap().clone();
                                (index, data)
                            }
                            _ => unreachable!("Ident not found: {:?}", ident),
                        };

                        println!("data: {} - {:?}", ident, data);
                        let is_static = match index {
                            LayerIndex::Op(_) => data.is_static,
                            LayerIndex::Static(_) => true,
                            _ => false,
                        };

                        if is_static {
                            let source_data = env.data(&index).unwrap().clone();
                            // create a new type, drop other information (static)
                            let data = Data::new(source_data.ty);

                            // we should only be dealing with pointers in if we are static
                            if let AstType::Ptr(ty) = &data.ty {
                                let ty = self.from_type(ty);

                                let ty = MemRefType::new(ty, &[], None, None);
                                let op1 = memref::get_global(self.context, &ident, ty, location);

                                let r = op1.result(0).unwrap().into();
                                let op2 = memref::load(r, &[], location);

                                env.push(op1);
                                let index = env.push(op2);
                                env.index_data(index, data);
                                index
                            } else {
                                unreachable!();
                            }
                        } else {
                            env.push_index(index);
                            index
                        }
                    }
                }
            }

            Ast::Call(expr, args) => {
                // function to call
                let (f, data) = match &expr.node {
                    Ast::Identifier(ident) => {
                        let index = env.index_from_name(ident).unwrap();
                        let data = env.data(&index).unwrap();
                        (
                            attribute::FlatSymbolRefAttribute::new(self.context, ident),
                            data,
                        )
                    }
                    _ => {
                        unimplemented!("not implemented: {:?}", expr.node);
                    }
                };

                if let AstType::Func(_func_arg_types, ret) = &data.ty {
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
                        .map(|index| env.value0(index))
                        .collect::<Vec<_>>();

                    let op = func::call(self.context, f, call_args.as_slice(), &[ret_ty], location);
                    let index = env.push(op);
                    env.index_data(index, data);
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
                }

                Literal::Int(x) => {
                    let op = self.build_int_op(x, location);
                    let index = env.push(op);
                    env.index_data(index, Data::new(AstType::Int));
                    index
                }

                Literal::Index(x) => {
                    let op = self.build_index_op(x as i64, location);
                    let index = env.push(op);
                    env.index_data(index, Data::new(AstType::Index));
                    index
                }

                Literal::Bool(x) => {
                    let op = self.build_bool_op(x, location);
                    let index = env.push(op);
                    env.index_data(index, Data::new(AstType::Bool));
                    index
                } //_ => unimplemented!("{:?}", lit)
            },

            Ast::Sequence(exprs) => {
                exprs.into_iter().for_each(|expr| {
                    self.lower_expr(expr, env);
                });
                env.last_index().unwrap()
            }

            Ast::Variable(_def) => {
                unimplemented!();
                /*
                let ident = def.name;
                // TODO: handle global variables properly, currently assume function context
                log::debug!("variable ident {:?}", ident);
                let index_type = Type::index(self.context);
                let ty = MemRefType::new(index_type, &[], None, None);
                let op1 = memref::alloca(self.context, ty, &[], &[], None, location);
                let x = env.push(op1);
                self.lower_expr(*def.body.unwrap(), env);
                let r = env.last_values();
                let op = memref::store(r[0], env.values(x)[0], &[], location);
                env.push_with_name(op, &ident);
                env.last_index().unwrap()
                */
            }

            Ast::Definition(def) => {
                log::debug!("name {:?}", def.name);
                let mut params = vec![];
                let ty = self.from_type(&*def.return_type);
                let mut ast_types = vec![];
                let ast_ret_type = def.return_type;

                for p in def.params {
                    match p.node {
                        Parameter::Normal(ident, ast_ty) => {
                            log::debug!("params {:?}: {:?}", ident, ast_ty);
                            let location = p.extra.location(self.context, self.files);
                            //let ir_ty = self.from_type(&ast_ty);
                            params.push((ast_ty.clone(), location, ident));
                            ast_types.push(ast_ty);
                        }
                        _ => {
                            unimplemented!("{:?}", p);
                        }
                    }
                }

                let region = Region::new();

                let mut attributes = vec![(
                    Identifier::new(self.context, "sym_visibility"),
                    StringAttribute::new(self.context, "private").into(),
                )];

                if let Some(body) = def.body {
                    let layer = self.build_block(params.as_slice(), env);
                    env.enter(layer);
                    //env.enter_block(params.as_slice());
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

                let types = params
                    .iter()
                    .map(|x| self.from_type(&x.0))
                    .collect::<Vec<Type>>();

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
                    let mut index = self.lower_expr(*expr, env);

                    // TODO: this only handles a single return value
                    // Deref if necessary
                    let is_mem_ref = {
                        let r = env.value0(index);
                        r.r#type().is_mem_ref()
                    };

                    if is_mem_ref {
                        let r = env.value0(index);
                        let op = memref::load(r, &[], location);
                        index = env.push(op);
                    }

                    let rs = env.values(index);
                    let ret_op = func::r#return(&rs, location);

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
                //env.enter_block(&[]);
                let layer = self.build_block(&[], env);
                env.enter(layer);
                self.lower_expr(*true_expr, env);
                let mut layer = env.exit();
                let true_block = layer.block.take().unwrap();

                for op in layer.take_ops() {
                    true_block.append_operation(op);
                }
                true_block.append_operation(scf::r#yield(&[], location));

                match maybe_false_expr {
                    Some(false_expr) => {
                        //env.enter_block(&[]);
                        let layer = self.build_block(&[], env);
                        env.enter(layer);
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
                            env.value0(index_conditions),
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
                            env.value0(index_conditions),
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

            Ast::Replace(target, rhs) => {
                // mutate variable in place
                // This requires that the variable has a place either on the stack or in memory
                // global vars have a place, so start with those
                match target {
                    AssignTarget::Identifier(ident) => {
                        log::debug!("replace ident {:?}", ident);
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

                        // do we enforce types here? or do we just overwrite with what ever new
                        // type

                        let value_index = self.lower_expr(*rhs, env);
                        if is_static {
                            let ty = MemRefType::new(
                                IntegerType::new(self.context, 64).into(),
                                &[],
                                None,
                                None,
                            );
                            let op1 = memref::get_global(self.context, &ident, ty, location);

                            let addr_index = env.push(op1);

                            let r_value = env.value0(value_index);
                            let r_addr = env.value0(addr_index);

                            let op = memref::store(r_value, r_addr, &[], location);
                            env.push(op)
                        } else {
                            let r_value = env.value0(value_index);
                            let r_addr = env.value0(index);
                            let op = memref::store(r_value, r_addr, &[], location);
                            env.push(op)
                        }
                    }
                    _ => unimplemented!("{:?}", target),
                }
            }

            Ast::Assign(target, rhs) => {
                match target {
                    AssignTarget::Alloca(ident) => {
                        let ty = env.current_layer_type();
                        assert_ne!(ty, LayerType::Static);
                        let ty = IntegerType::new(self.context, 64);
                        let memref_ty = MemRefType::new(ty.into(), &[], None, None);
                        let op = memref::alloca(self.context, memref_ty, &[], &[], None, location);
                        let ptr_index = env.push(op);
                        env.name_index(ptr_index, &ident);
                        let rhs_index = self.lower_expr(*rhs, env);
                        let data = env.data(&rhs_index).unwrap();
                        env.index_data(ptr_index, Data::new(data.ty.clone()));
                        let r_value = env.value0(rhs_index);
                        let r_addr = env.value0(ptr_index);
                        let op = memref::store(r_value, r_addr, &[], location);
                        env.push(op)
                    }
                    AssignTarget::Identifier(ident) => {
                        let ty = env.current_layer_type();
                        log::debug!("assign ident {:?}, {:?}", ident, ty);
                        match ty {
                            LayerType::Static => {
                                unreachable!(
                                    "Assign not possible in global context, use Global instead"
                                );
                            }
                            _ => {
                                let index = self.lower_expr(*rhs, env);
                                env.name_index(index, &ident);
                                index
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
                                    cf::assert(self.context, env.value0(index), &msg, location);
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
                                let r = env.value0(index);
                                let ty = r.r#type();

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

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::compile::run_ast;
    use crate::NodeBuilder;
    use test_log::test;

    pub fn gen_test<'c, E: Extra>(file_id: usize, _env: &mut Environment<'c>) -> AstNode<E> {
        let mut b: NodeBuilder<E> = NodeBuilder::new();
        b.enter_file(file_id);
        let mut seq = vec![];
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

    pub fn gen_while<'c, E: Extra>(file_id: usize, _env: &mut Environment<'c>) -> AstNode<E> {
        let mut b: NodeBuilder<E> = NodeBuilder::new();
        b.enter_file(file_id);
        let mut seq = vec![];

        // global variable x = 10
        seq.push(b.global("z", b.integer(10)));
        seq.push(b.main(b.seq(vec![
            // define local var
            b.assign("x", b.integer(123)),
            // allocate mutable var
            b.alloca("x2", b.integer(10)),
            b.while_loop(
                b.ne(b.ident("x2"), b.integer(0)),
                b.seq(vec![
                    // static variable with local scope
                    b.global("z_static", b.integer(0)),
                    // mutate global variable
                    b.replace("z", b.subtract(b.ident("z"), b.integer(1))),
                    // mutate scoped variable
                    b.replace("x2", b.subtract(b.ident("x2"), b.integer(1))),
                    // assign local
                    b.assign("y", b.subtract(b.ident("x"), b.ident("z_static"))),
                ]),
            ),
            b.ret(Some(b.ident("x2"))),
        ])));

        b.seq(seq)
    }

    pub fn gen_function_call<'c, E: Extra>(
        file_id: usize,
        _env: &mut Environment<'c>,
    ) -> AstNode<E> {
        let mut b: NodeBuilder<E> = NodeBuilder::new();
        b.enter_file(file_id);
        let mut seq = vec![];

        seq.push(b.func(
            "x1",
            &[("arg0", AstType::Int)],
            AstType::Int,
            b.seq(vec![b.ret(Some(b.add(b.integer(0), b.ident("arg0"))))]),
        ));

        seq.push(b.main(b.seq(vec![
            b.assign("x", b.apply("x1", vec![b.integer(0)])),
            b.ret(Some(b.ident("x"))),
        ])));
        b.seq(seq)
    }

    pub fn gen_recursion<'c, E: Extra>(file_id: usize, _env: &mut Environment<'c>) -> AstNode<E> {
        let mut b: NodeBuilder<E> = NodeBuilder::new();
        b.enter_file(file_id);
        let seq = vec![];
        b.seq(seq)
    }

    #[test]
    fn test_gen() {
        let context = Context::new();
        let mut files = FileDB::new();
        let file_id = files.add("test.py".into(), "test".into());
        let mut env = Environment::default();
        let mut lower = Lower::new(&context, &files);
        let ast: AstNode<SimpleExtra> = gen_function_call(file_id, &mut env);
        run_ast(0, ast, &mut lower, &mut env);
    }

    #[test]
    fn test_while() {
        let context = Context::new();
        let mut files = FileDB::new();
        let file_id = files.add("test.py".into(), "test".into());
        let mut env = Environment::default();
        let mut lower = Lower::new(&context, &files);
        let ast: AstNode<SimpleExtra> = gen_while(file_id, &mut env);
        run_ast(0, ast, &mut lower, &mut env);
    }

    #[test]
    fn test_loop() {
        let context = Context::new();
        let mut files = FileDB::new();
        let file_id = files.add("test.py".into(), "test".into());
        let mut env = Environment::default();
        let mut lower = Lower::new(&context, &files);
        let ast: AstNode<SimpleExtra> = gen_test(file_id, &mut env);
        run_ast(0, ast, &mut lower, &mut env);
    }
}
