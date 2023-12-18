use crate::ast::*;
use crate::scope::{Layer, LayerIndex, LayerType};
use crate::{op, Environment, NodeBuilder};
use crate::{Diagnostics, ParseError};
use anyhow::Error;
use anyhow::Result;
use melior::{
    dialect::{arith, cf, func, llvm, memref, ods, scf},
    ir::{
        attribute::{
            //DenseElementsAttribute,
            FloatAttribute,
            IntegerAttribute,
            StringAttribute,
            TypeAttribute,
        },
        r#type::{
            FunctionType,
            IntegerType,
            MemRefType,
            //RankedTensorType
        },
        *,
    },
    Context,
};
use std::collections::HashSet;

#[derive(Debug, Clone)]
pub struct Data {
    ty: AstType,
    static_name: Option<String>,
}

impl Data {
    pub fn new_static(ty: AstType, name: &str) -> Self {
        Self {
            ty,
            static_name: Some(name.to_string()),
        }
    }

    pub fn new(ty: AstType) -> Self {
        Self {
            ty,
            static_name: None,
        }
    }
}

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

pub struct Lower<'c, E> {
    pub(crate) context: &'c Context,
    pub pass_manager: melior::pass::PassManager<'c>,
    pub shared: HashSet<String>,
    _e: std::marker::PhantomData<E>,
}

pub fn layer_in_scope<'c, E: Extra>(
    context: &'c Context,
    layer_type: LayerType,
    body: AstNode<E>,
    d: &mut Diagnostics,
    _b: &NodeBuilder<E>,
) -> Result<Layer<'c, E>> {
    let mut layer = Layer::new(layer_type);

    let blocks = if body.is_seq() {
        body.try_seq().unwrap()
    } else {
        vec![body]
    };

    // load nodes
    for expr in blocks.into_iter() {
        if let Ast::Block(nb) = expr.node {
            log::debug!("block node: {:?}", nb.body.node);
            log::debug!(
                "block terminator: {}: {:?}",
                nb.name,
                nb.body.node.terminator()
            );

            // ensure we have a terminator
            if nb.body.node.terminator().is_none() {
                d.push_diagnostic(nb.body.extra.error("Block does not terminate"));
                return Err(Error::new(ParseError::Invalid));
            }

            layer.push_block(context, &nb.name, nb.params, *nb.body, d);
        } else {
            unreachable!()
        }
    }
    Ok(layer)
}

pub fn new_block<'c, E: Extra>(
    context: &'c Context,
    arguments: &[ParameterNode<E>],
    d: &Diagnostics,
) -> Block<'c> {
    let block_args = arguments
        .iter()
        .map(|a| (from_type(context, &a.ty), a.extra.location(context, d)))
        .collect::<Vec<_>>();
    Block::new(&block_args)
}

/*
pub fn push_parameters<'c, E: Extra>(
    layer: &mut Layer<'c, E>,
    env: &mut Environment<'c, E>,
    arguments: &[ParameterNode<E>],
) {
    // create a new layer, adding arguments as scoped variables
    for (offset, a) in arguments.iter().enumerate() {
        let index = env.fresh_argument();
        layer.name_index(index.clone(), &a.name);
        //let data = Data::new(a.ty.clone());
        env.index_data(&index, a.ty.clone());
        // record argument offset
        layer.index.insert(index, offset);
    }
}
*/

pub fn from_type<'c>(context: &'c Context, ty: &AstType) -> Type<'c> {
    match ty {
        AstType::Ptr(_) => Type::index(context),
        AstType::Tuple(args) => {
            let types = args
                .iter()
                .map(|a| from_type(context, a))
                .collect::<Vec<_>>();
            melior::ir::r#type::TupleType::new(context, &types).into()
        }
        AstType::Func(args, ret) => {
            let inputs = args
                .iter()
                .map(|a| from_type(context, a))
                .collect::<Vec<_>>();
            let results = vec![from_type(context, ret)];
            melior::ir::r#type::FunctionType::new(context, &inputs, &results).into()
        }
        AstType::Int => IntegerType::new(context, 64).into(),
        AstType::Index => Type::index(context),
        AstType::Float => Type::float64(context),
        AstType::Bool => IntegerType::new(context, 1).into(),
        AstType::Unit => Type::none(context),
        //AstType::String => Type::none(self.context),
        _ => unimplemented!("{:?}", ty),
    }
}

/*
impl<'c, E: Extra> Lower<'c, E> {
    pub fn new(context: &'c Context) -> Self {
        Self {
            context,
            pass_manager: crate::compile::default_pass_manager(context),
            shared: HashSet::new(),
            _e: std::marker::PhantomData::default(),
        }
    }

    pub fn type_from_expr(&self, expr: &AstNode<E>, env: &Environment<'c, E>) -> AstType {
        match &expr.node {
            Ast::Literal(x) => x.into(),
            Ast::Identifier(name) => {
                // infer type from the operation
                let index = env.index_from_name(name).unwrap();
                env.data(&index).unwrap()
            }
            Ast::Call(_f, _args, ty) => ty.clone(),

            _ => unreachable!("{:?}", expr),
        }
    }

    pub fn build_bool_op(&self, value: bool, location: Location<'c>) -> Operation<'c> {
        op::build_bool_op(self.context, value, location)
    }

    pub fn build_int_op(&self, value: i64, location: Location<'c>) -> Operation<'c> {
        op::build_int_op(self.context, value, location)
    }

    pub fn build_index_op(&self, value: i64, location: Location<'c>) -> Operation<'c> {
        op::build_index_op(self.context, value, location)
    }

    pub fn build_float_op(&self, value: f64, location: Location<'c>) -> Operation<'c> {
        op::build_float_op(self.context, value, location)
    }

    pub fn lower_static(
        &self,
        expr: AstNode<E>,
        _env: &mut Environment<'c, E>,
        d: &mut Diagnostics,
    ) -> (AstType, Operation<'c>) {
        let location = self.location(&expr, d);
        match expr.node {
            Ast::Literal(Literal::Bool(x)) => (AstType::Bool, self.build_bool_op(x, location)),
            Ast::Literal(Literal::Int(x)) => (AstType::Int, self.build_int_op(x, location)),
            Ast::Literal(Literal::Float(x)) => (AstType::Float, self.build_float_op(x, location)),
            _ => unreachable!("{:?}", expr.node),
        }
    }

    /*
    pub fn build_block(
        &self,
        layer_type: LayerType,
        params: &[ParameterNode<E>],
        body: AstNode<E>,
        env: &mut Environment<'c, E>,
        d: &mut Diagnostics,
        b: &NodeBuilder<E>,
    ) -> Result<(LayerIndex, Block<'c>)> {
        let layer = Layer::new(layer_type);
        let block = Block::new(&[]);
        env.enter(layer);
        let index = self.lower_expr(body, env, d, b)?;
        let mut layer = env.exit();
        for op in layer.take_ops() {
            block.append_operation(op);
        }
        Ok((index, block))
    }
    */

    pub fn build_ops(
        &self,
        layer: Layer<'c, E>,
        env: &mut Environment<'c, E>,
        d: &mut Diagnostics,
        b: &NodeBuilder<E>,
    ) -> Result<Block<'c>> {
        use crate::blocks::Index;

        env.enter(layer);
        let mut items = env.build_layers();

        // take the nodes, and lower them
        let mut layers = vec![];
        let asts = env.last_mut().g.take_ast();
        // we should only have a single block
        assert_eq!(asts.len(), 1);
        for (offset, ast) in asts.into_iter().enumerate() {
            let layer = items.remove(&Index::new(offset)).unwrap();
            println!("layer {:?}", &layer);
            env.enter(layer);

            println!("enter {}", offset);
            //println!("ast {:?}", &ast);
            env.dump();
            self.lower_expr(ast, env, d, b)?;
            let layer = env.exit();
            layers.push(layer);
        }

        // exit func layer
        let mut layer = env.exit();

        // drop blocks
        let mut blocks = layer.g.take_blocks();
        assert_eq!(blocks.len(), 1);
        layer.append_ops(blocks.get(0).unwrap());
        Ok(blocks.pop().unwrap())
    }

    pub fn build_region(
        &self,
        layer: Layer<'c, E>,
        env: &mut Environment<'c, E>,
        d: &mut Diagnostics,
        b: &NodeBuilder<E>,
    ) -> Result<Region<'c>> {
        use crate::blocks::Index;

        env.enter(layer);
        let mut items = env.build_layers();

        // take the nodes, and lower them
        let region = Region::new();
        let mut layers = vec![];
        let asts = env.last_mut().g.take_ast();

        // TODO: we enter the layer, but layers don't know about other layers
        // we can look up block args, but not arguments that are defined in the layer
        // everything should be visible that is dominant
        for (offset, ast) in asts.into_iter().enumerate() {
            let index = Index::new(offset);
            let layer = items.remove(&index).unwrap();

            //println!("enter layer {:?}", &layer);
            println!("layer names {:?}", &layer.names);
            env.enter(layer);
            println!("enter {}", offset);
            //println!("ast {:?}", &ast);

            env.dump();
            self.lower_expr(ast, env, d, b)?;
            let layer = env.exit();
            layers.push(layer);
        }

        // exit func layer
        let mut layer = env.exit();

        // turn blocks into region
        let blocks = layer.g.take_blocks();
        for (mut layer, block) in layers.into_iter().zip(blocks) {
            layer.append_ops(&block);
            region.append_block(block);
        }

        Ok(region)
    }

    pub fn build_while<'a>(
        &self,
        //init_args: &[Value<'c, 'a>],
        condition: AstNode<E>,
        body: AstNode<E>,
        env: &mut Environment<'c, E>,
        d: &mut Diagnostics,
        b: &NodeBuilder<E>,
    ) -> Result<LayerIndex> {
        let bool_type = from_type(self.context, &AstType::Bool);
        let condition_location = self.location(&condition, d);
        let body_location = self.location(&body, d);

        // before

        let layer_type = LayerType::Block;
        let layer = Layer::new(layer_type);
        let block = Block::new(&[]);
        env.enter(layer);
        let _index = self.lower_expr(condition, env, d, b)?;
        let r: Value<'_, '_> = env.last_values()[0];
        // should be bool type
        assert!(r.r#type() == bool_type);
        let c = scf::condition(r, &[], condition_location);
        env.push(c);
        let mut layer = env.exit();
        layer.append_ops(&block);
        let before_region = Region::new();
        before_region.append_block(block);

        // after
        let layer_type = LayerType::Block;
        let layer = Layer::new(layer_type);
        let block = Block::new(&[]);
        env.enter(layer);
        let _index = self.lower_expr(body, env, d, b)?;
        let c = scf::r#yield(&[], body_location);
        env.push(c);
        let mut layer = env.exit();
        layer.append_ops(&block);
        let after_region = Region::new();
        after_region.append_block(block);

        // after complete

        Ok(env.push(scf::r#while(
            &[],
            &[],
            before_region,
            after_region,
            body_location,
        )))
    }

    pub fn build_loop<'a>(
        &self,
        //init_args: &[Value<'c, 'a>],
        condition: AstNode<E>,
        body: AstNode<E>,
        env: &mut Environment<'c, E>,
        d: &mut Diagnostics,
        b: &NodeBuilder<E>,
    ) -> Result<LayerIndex> {
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
        let bool_type = from_type(self.context, &AstType::Bool);
        let condition_location = self.location(&condition, d);
        let body_location = self.location(&body, d);

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

        /*
        let _block_args: Vec<(&str, AstType)> = init_args
            .iter()
            .map(|(ast_ty, arg_name, _)| (*arg_name, ast_ty.clone()))
            .collect();

        let before_args: Vec<ParameterNode<E>> = init_args
            .into_iter()
            .map(|(ast_ty, arg_name, init_name)| {
                // ensure the name exists
                let _index = env.index_from_name(init_name).unwrap();
                let data = Data::new(ast_ty);

                ParameterNode {
                    name: arg_name.to_string(),
                    ty: data.ty.clone(),
                    extra: condition.extra.clone(),
                    node: Parameter::Normal,
                }
            })
            .collect();

            */

        // condtion
        let block_args: Vec<(Type<'c>, Location<'c>)> = init_args
            .iter()
            .map(|(ast_ty, _arg_name, _)| {
                (
                    from_type(self.context, ast_ty),
                    self.location(&condition, d),
                )
            })
            .collect();

        /*
        for (offset, a) in arguments.iter().enumerate() {
            let index = env.fresh_argument();
            layer.name_index(index.clone(), &a.name);
            //let data = Data::new(a.ty.clone());
            env.index_data(&index, a.ty.clone());
            // record argument offset
            layer.index.insert(index, offset);
        }
        */

        let layer_type = LayerType::Block;
        let layer = Layer::new(layer_type);
        let block = Block::new(block_args.as_slice());
        env.enter(layer);
        let _index = self.lower_expr(condition, env, d, b)?;
        let r: Value<'_, '_> = env.last_values()[0];
        // should be bool type
        assert!(r.r#type() == bool_type);
        // return arg1
        let arg1 = block.argument(1).unwrap().into();
        let c = scf::condition(r, &[arg1], condition_location);
        env.push(c);
        let mut layer = env.exit();
        layer.append_ops(&block);
        let before_region = Region::new();
        before_region.append_block(block);

        // Before Complete

        // after
        let after_args = &[ParameterNode {
            name: "arg0".to_string(),
            ty: AstType::Index,
            extra: b.extra_unknown(),
            node: Parameter::Normal,
        }];

        // after
        let block_args = vec![(
            from_type(self.context, &AstType::Index),
            self.location(&body, d),
        )];
        let layer_type = LayerType::Block;
        let layer = Layer::new(layer_type);
        let block = Block::new(block_args.as_slice());
        env.enter(layer);

        let op = self.build_bool_op(false, condition_location);
        let index1 = env.push(op);

        let index2 = self.lower_expr(body, env, d, b)?;
        let mut rs = env.values(&index1);
        rs.extend(env.values(&index2));

        let c = scf::r#yield(&rs, body_location);
        env.push(c);
        let mut layer = env.exit();
        layer.append_ops(&block);
        let after_region = Region::new();
        after_region.append_block(block);

        // after complete

        let init_args = vec![
            env.value0_from_name("init_op"),
            env.value0_from_name("init_op2"),
        ];
        Ok(env.push(scf::r#while(
            &init_args,
            &after_args
                .iter()
                .map(|x| from_type(self.context, &x.ty))
                .collect::<Vec<Type<'_>>>(),
            before_region,
            after_region,
            body_location,
        )))
    }

    pub fn location(&self, expr: &AstNode<E>, d: &Diagnostics) -> Location<'c> {
        expr.extra.location(self.context, d)
    }

    pub fn lower_llvm_global_int(
        &self,
        name: &str,
        expr: AstNode<E>,
        env: &mut Environment<'c, E>,
        d: &mut Diagnostics,
    ) -> LayerIndex {
        let location = self.location(&expr, d);
        let block = Block::new(&[]);
        let (ast_ty, op1) = self.lower_static(expr, env, d);
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

        env.name_index(index.clone(), name);
        env.index_data(&index, Data::new_static(ast_ty, name).ty);
        index
    }

    pub fn lower_llvm_load_global(
        &self,
        ident: &str,
        ty: Type<'c>,
        location: Location<'c>,
        env: &mut Environment<'c, E>,
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
        env.push(op1);
        env.push(op2)
    }

    pub fn lower_llvm_store(
        &self,
        ident: &str,
        ast: AstNode<E>,
        env: &mut Environment<'c, E>,
        d: &mut Diagnostics,
        b: &NodeBuilder<E>,
    ) -> Result<LayerIndex> {
        let location = self.location(&ast, d);
        let value_index = self.lower_expr(ast, env, d, b)?;
        let opaque_ty = llvm::r#type::opaque_pointer(self.context);
        let f = attribute::FlatSymbolRefAttribute::new(self.context, ident);
        // get global address
        let op1: Operation<'c> =
            ods::llvm::mlir_addressof(self.context, opaque_ty.into(), f, location).into();

        let addr_index = env.push(op1);

        let r_value = env.value0(&value_index);
        let r_addr = env.value0(&addr_index);

        let options = llvm::LoadStoreOptions::new();
        Ok(env.push(llvm::store(
            self.context,
            r_value,
            r_addr,
            location,
            options,
        )))
    }

    pub fn emit_mutate(
        &self,
        ident: &str,
        rhs: AstNode<E>,
        env: &mut Environment<'c, E>,
        d: &mut Diagnostics,
        b: &NodeBuilder<E>,
    ) -> Result<LayerIndex> {
        let location = self.location(&rhs, d);
        let (index, _ty, _maybe_static_name) = match env.data_from_name(ident) {
            Some(index) => index,
            _ => unreachable!("Name not found: {}", ident),
        };
        let value_index = self.lower_expr(rhs, env, d, b)?;

        if let Some(static_name) = env.static_name(&index) {
            println!("static: {}", static_name);
            let ty = MemRefType::new(IntegerType::new(self.context, 64).into(), &[], None, None);
            let op1 = memref::get_global(self.context, &static_name, ty, location);

            let addr_index = env.push(op1);

            let r_value = env.value0(&value_index);
            let r_addr = env.value0(&addr_index);

            let op = memref::store(r_value, r_addr, &[], location);
            Ok(env.push(op))
        } else {
            let r_value = env.value0(&value_index);
            let r_addr = env.value0(&index);
            let op = memref::store(r_value, r_addr, &[], location);
            Ok(env.push(op))
        }
    }

    pub fn build_block(
        &self,
        layer: &mut Layer<'c, E>,
        name: &str,
        arguments: &[ParameterNode<E>],
        env: &mut Environment<'c, E>,
        d: &Diagnostics,
    ) {
        // create a new layer, adding arguments as scoped variables
        for (offset, a) in arguments.iter().enumerate() {
            let index = env.fresh_argument();
            layer.name_index(index.clone(), &a.name);
            //let data = Data::new(a.ty.clone());
            env.index_data(&index, a.ty.clone());
            // record argument offset
            layer.index.insert(index, offset);
        }

        let block = new_block(self.context, arguments, d);
        layer.enter_block(name, block);
    }
    */

/*
    pub fn lower_expr<'a>(
        &self,
        expr: AstNode<E>,
        env: &mut Environment<'c, E>,
        d: &mut Diagnostics,
        b: &NodeBuilder<E>,
    ) -> Result<LayerIndex> {
        let location = self.location(&expr, d);

        match expr.node {
            Ast::Error => unreachable!(),

            Ast::Loop(_name, _body) => {
                unimplemented!()
            }

            Ast::Block(_nb) => {
                unreachable!()
            }

            Ast::Break(_name) => {
                unimplemented!()
            }
            Ast::Continue(_name) => {
                unimplemented!()
            }
            Ast::Label(_) => unimplemented!(),
            Ast::Goto(name) => {
                env.dump();
                if let Some(block) = env.get_block_by_name(&name) {
                    Ok(env.push(cf::br(block, &[], location)))
                } else {
                    d.push_diagnostic(expr.extra.error(&format!("Missing block: {}", name)));
                    Err(Error::new(ParseError::Invalid))
                }
            }

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
                        let ty = from_type(self.context, &ast_ty);
                        let v = if x { 1 } else { 0 };
                        let value = IntegerAttribute::new(v, ty).into();
                        let op = op::build_static(
                            self.context,
                            &global_name,
                            ty,
                            value,
                            false,
                            location,
                        );
                        (ast_ty, op)
                    }

                    Ast::Literal(Literal::Int(x)) => {
                        let ast_ty = AstType::Int;
                        let ty = from_type(self.context, &ast_ty);
                        let value = IntegerAttribute::new(x, ty).into();
                        let op = op::build_static(
                            self.context,
                            &global_name,
                            ty,
                            value,
                            false,
                            location,
                        );
                        (ast_ty, op)
                    }

                    Ast::Literal(Literal::Index(x)) => {
                        let ast_ty = AstType::Int;
                        let ty = from_type(self.context, &ast_ty);
                        let value = IntegerAttribute::new(x as i64, ty).into();
                        let op = op::build_static(
                            self.context,
                            &global_name,
                            ty,
                            value,
                            false,
                            location,
                        );
                        (ast_ty, op)
                    }

                    Ast::Literal(Literal::Float(x)) => {
                        let ast_ty = AstType::Float;
                        let ty = from_type(self.context, &ast_ty);
                        let value = FloatAttribute::new(self.context, x, ty).into();
                        let op = op::build_static(
                            self.context,
                            &global_name,
                            ty,
                            value,
                            false,
                            location,
                        );
                        (ast_ty, op)
                    }

                    _ => unreachable!("{:?}", expr.node),
                };

                let ptr_ty = AstType::Ptr(ast_ty.clone().into());
                if env.current_layer_type() == LayerType::Static {
                    // STATIC/GLOBAL VARIABLE
                    let index = env.push_with_name(op, &global_name);
                    env.index_data(&index, ptr_ty);
                    env.index_static_name(&index, &global_name);
                    Ok(index)
                } else {
                    // STATIC VARIABLE IN FUNCTION CONTEXT

                    // push static operation
                    let index = env.push_static(op, &global_name);
                    env.index_data(&index, ptr_ty);

                    env.index_static_name(&index, &global_name);
                    env.name_index(index.clone(), &ident);

                    // push name into current context
                    env.name_index(index.clone(), &ident);
                    Ok(index)
                }
            }

            Ast::UnaryOp(op, a) => {
                let index_rhs = self.lower_expr(*a, env, d, b)?;

                // get the type of the RHS
                let ty = env.value0(&index_rhs).r#type();

                match op {
                    UnaryOperation::Minus => {
                        if ty.is_index() {
                            unreachable!("Unable to negate index type");
                        } else if ty.is_integer() {
                            // Multiply by -1
                            let int_op = self.build_int_op(-1, location);
                            let index_lhs = env.push(int_op);
                            let r = env.value0(&index_lhs);
                            let r_rhs = env.value0(&index_rhs);
                            Ok(env.push(arith::muli(r.into(), r_rhs.into(), location)))
                        } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                            // arith has an op for negation
                            let r_rhs = env.value0(&index_rhs);
                            Ok(env.push(arith::negf(r_rhs.into(), location)))
                        } else {
                            unimplemented!()
                        }
                    }
                }
            }

            Ast::BinaryOp(op, x, y) => {
                println!("x: {:?}", x);
                println!("y: {:?}", y);
                let x_extra = x.extra.clone();
                let y_extra = y.extra.clone();
                let index_lhs = self.lower_expr(*x, env, d, b)?;
                let index_rhs = self.lower_expr(*y, env, d, b)?;

                let ty_lhs = env.data(&index_lhs).expect("LHS data missing").clone();
                let ty_rhs = env.data(&index_rhs).expect("RHS data missing").clone();

                let (ty_lhs, index_lhs) = if let AstType::Ptr(ty) = ty_lhs {
                    let index =
                        self.emit_deref(index_lhs, x_extra.location(self.context, d), env, d, b)?;
                    (*ty, index)
                } else {
                    (ty_lhs, index_lhs)
                };

                let (ty_rhs, index_rhs) = if let AstType::Ptr(ty) = ty_rhs {
                    let index =
                        self.emit_deref(index_rhs, y_extra.location(self.context, d), env, d, b)?;
                    (*ty, index)
                } else {
                    (ty_rhs, index_rhs)
                };

                let ast_ty = ty_lhs.clone();
                assert_eq!(ty_lhs, ty_rhs);

                // types must be the same for binary operation, no implicit casting yet
                let a = env.value0(&index_lhs);
                let b = env.value0(&index_rhs);
                let (binop, ast_ty) =
                    op::build_binop(self.context, op, a, &x_extra, b, &y_extra, location, d)?;

                let index = env.push(binop);
                let data = Data::new(ast_ty);
                env.index_data(&index, data.ty);
                Ok(index)
            }

            Ast::Deref(expr, _target) => {
                let location = expr.location(self.context, d);
                // we are expecting a memref here
                let index = self.lower_expr(*expr, env, d, b)?;
                self.emit_deref(index, location, env, d, b)
            }

            Ast::Identifier(ident) => {
                match ident.as_str() {
                    "True" => {
                        let op = self.build_bool_op(true, location);
                        let index = env.push(op);
                        env.index_data(&index, Data::new(AstType::Bool).ty);
                        Ok(index)
                    }
                    "False" => {
                        let op = self.build_bool_op(false, location);
                        let index = env.push(op);
                        env.index_data(&index, Data::new(AstType::Bool).ty);
                        Ok(index)
                    }
                    _ => {
                        let (index, data) = match env.index_from_name(ident.as_str()) {
                            Some(index) => {
                                let data = env
                                    .data(&index)
                                    .expect(&format!("Missing data for {}", &ident))
                                    .clone();
                                (index, data)
                            }
                            _ => unreachable!("Ident not found: {:?}", ident),
                        };

                        if let Some(static_name) = &env.static_name(&index) {
                            // we should only be dealing with pointers in if we are static
                            if let AstType::Ptr(ty) = &data {
                                let ty = from_type(self.context, ty);

                                let ty = MemRefType::new(ty, &[], None, None);
                                let op =
                                    memref::get_global(self.context, &static_name, ty, location);

                                let index = env.push(op);
                                env.index_data(&index, data);
                                Ok(index)
                            } else {
                                unreachable!("Identifier of static variable must be pointer");
                            }
                        } else {
                            env.push_index(index.clone());
                            Ok(index)
                        }
                    }
                }
            }

            Ast::Call(expr, args, _ret_ty) => {
                // function to call
                let (f, ty) = match &expr.node {
                    Ast::Identifier(ident) => {
                        if let Some(index) = env.index_from_name(ident) {
                            let ty = env.data(&index).unwrap();
                            (
                                attribute::FlatSymbolRefAttribute::new(self.context, ident),
                                ty,
                            )
                        } else {
                            unreachable!("not found: {:?}", ident);
                        }
                    }
                    _ => {
                        unimplemented!("{:?}", expr.node);
                    }
                };

                if let AstType::Func(_func_arg_types, ret) = &ty {
                    let ret_ty = from_type(self.context, &ret);
                    // handle call arguments
                    let mut indices = vec![];
                    for a in args {
                        match a {
                            Argument::Positional(arg) => {
                                let index = self.lower_expr(*arg, env, d, b)?;
                                indices.push(index);
                            } //_ => unimplemented!("{:?}", a)
                        };
                    }

                    let call_args = indices
                        .into_iter()
                        .map(|index| env.value0(&index))
                        .collect::<Vec<_>>();

                    let op = func::call(
                        self.context,
                        f,
                        call_args.as_slice(),
                        &[ret_ty.clone()],
                        location,
                    );
                    let index = env.push(op);
                    env.index_data(&index, *ret.clone());
                    Ok(index)
                } else {
                    unimplemented!("calling non function type: {:?}", ty);
                }
            }

            Ast::Literal(lit) => match lit {
                Literal::Float(f) => {
                    let op = self.build_float_op(f, location);
                    let index = env.push(op);
                    env.index_data(&index, Data::new(AstType::Float).ty);
                    Ok(index)
                }

                Literal::Int(x) => {
                    let op = self.build_int_op(x, location);
                    let index = env.push(op);
                    env.index_data(&index, Data::new(AstType::Int).ty);
                    Ok(index)
                }

                Literal::Index(x) => {
                    let op = self.build_index_op(x as i64, location);
                    let index = env.push(op);
                    env.index_data(&index, Data::new(AstType::Index).ty);
                    Ok(index)
                }

                Literal::Bool(x) => {
                    let op = self.build_bool_op(x, location);
                    let index = env.push(op);
                    env.index_data(&index, AstType::Bool);
                    Ok(index)
                }
                _ => unimplemented!("{:?}", lit),
            },

            Ast::Sequence(exprs) => {
                for expr in exprs {
                    self.lower_expr(expr, env, d, b)?;
                }
                Ok(env.last_index().unwrap())
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
                // normalize def to ensure it's in the expected format
                let def = def.normalize();

                log::debug!("name {:?}", def.name);

                let ret_ty = from_type(self.context, &*def.return_type);
                let mut ast_types = vec![];
                let mut types = vec![];
                let ast_ret_type = def.return_type;

                for p in &def.params {
                    match p.node {
                        Parameter::Normal | Parameter::WithDefault(_) => {
                            //log::debug!("params {:?}: {:?}", p.name, p.ty);
                            types.push(from_type(self.context, &p.ty));
                            ast_types.push(p.ty.clone());
                        }
                        _ => unimplemented!("{:?}", p),
                    }
                }

                let mut attributes = vec![(
                    Identifier::new(self.context, "sym_visibility"),
                    StringAttribute::new(self.context, "private").into(),
                )];

                let ret_type = if ret_ty.is_none() {
                    vec![]
                } else {
                    vec![ret_ty]
                };

                let func_type = FunctionType::new(self.context, &types, &ret_type);
                let f_type = AstType::Func(ast_types, ast_ret_type);
                let data = Data::new_static(f_type, &def.name);

                // create a new index, but don't actually add it
                // we just associate the function signature with it, so it can
                // be called recursively
                let index = env.fresh_op();
                env.name_index(index.clone(), &def.name);
                env.index_data(&index, data.ty);

                let region = if let Some(body) = def.body {
                    let layer = layer_in_scope(self.context, LayerType::Function, *body, d, b)?;
                    let region = self.build_region(layer, env, d, b)?;

                    // declare as C interface only if body is defined
                    // function declarations represent functions that are already C interfaces
                    attributes.push((
                        Identifier::new(self.context, "llvm.emit_c_interface"),
                        Attribute::unit(self.context),
                    ));

                    region
                } else {
                    Region::new()
                };

                let f = func::func(
                    self.context,
                    StringAttribute::new(self.context, &def.name),
                    TypeAttribute::new(func_type.into()),
                    region,
                    &attributes,
                    location,
                );

                // save and return created index
                Ok(env.push_op_index(index.clone(), f))
            }

            Ast::Return(maybe_expr) => match maybe_expr {
                Some(expr) => {
                    let location = self.location(&expr, d);
                    let mut index = self.lower_expr(*expr, env, d, b)?;

                    // TODO: this only handles a single return value
                    // Deref if necessary
                    let is_mem_ref = {
                        let r = env.value0(&index);
                        r.r#type().is_mem_ref()
                    };

                    if is_mem_ref {
                        let r = env.value0(&index);
                        let op = memref::load(r, &[], location);
                        index = env.push(op);
                    }

                    let rs = env.values(&index);
                    let ret_op = func::r#return(&rs, location);

                    Ok(env.push(ret_op))
                }
                None => {
                    let op = func::r#return(&[], location);
                    Ok(env.push(op))
                }
            },

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
                let bool_type = from_type(self.context, &AstType::Bool);
                let then_location = self.location(&then_expr, d);

                // condition (outside of blocks)
                let index_conditions = self.lower_expr(*condition, env, d, b)?;
                let r: Value<'_, '_> = env.last_values()[0];
                // should be bool type
                assert!(r.r#type() == bool_type);

                // then block

                let layer_type = LayerType::Block;
                let layer = Layer::new(layer_type);
                let block = Block::new(&[]);
                env.enter(layer);
                let _index = self.lower_expr(*then_expr, env, d, b)?;
                env.push(scf::r#yield(&[], then_location));
                let mut layer = env.exit();
                layer.append_ops(&block);
                let then_region = Region::new();
                then_region.append_block(block);

                // else block

                let else_region = match maybe_else_expr {
                    Some(else_expr) => {
                        let else_location = self.location(&else_expr, d);

                        let layer_type = LayerType::Block;
                        let layer = Layer::new(layer_type);
                        let block = Block::new(&[]);
                        env.enter(layer);
                        let _index = self.lower_expr(*else_expr, env, d, b)?;
                        env.push(scf::r#yield(&[], else_location));
                        let mut layer = env.exit();
                        layer.append_ops(&block);
                        let else_region = Region::new();
                        else_region.append_block(block);
                        else_region
                    }
                    None => Region::new(),
                };
                let if_op = scf::r#if(
                    env.value0(&index_conditions),
                    &[],
                    then_region,
                    else_region,
                    location,
                );
                Ok(env.push(if_op))
            }

            Ast::Mutate(lhs, rhs) => match lhs.node {
                Ast::Identifier(ident) => self.emit_mutate(&ident, *rhs, env, d, b),
                _ => unimplemented!("{:?}", &lhs.node),
            },

            Ast::Replace(target, rhs) => {
                // mutate variable in place
                // This requires that the variable has a place either on the stack or in memory
                // global vars have a place, so start with those
                match target {
                    AssignTarget::Identifier(ident) => self.emit_mutate(&ident, *rhs, env, d, b),
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
                        env.name_index(ptr_index.clone(), &ident);
                        let rhs_index = self.lower_expr(*rhs, env, d, b)?;
                        let ty = env.data(&rhs_index).unwrap();
                        let data = Data::new(AstType::Ptr(ty.clone().into()));
                        env.index_data(&ptr_index, data.ty);
                        let r_value = env.value0(&rhs_index);
                        let r_addr = env.value0(&ptr_index);
                        let op = memref::store(r_value, r_addr, &[], location);
                        Ok(env.push(op))
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
                                let index = self.lower_expr(*rhs, env, d, b)?;
                                env.name_index(index.clone(), &ident);
                                Ok(index)
                            }
                        }
                    } //_ => unimplemented!("{:?}", target),
                }
            }

            Ast::While(condition, body) => self.build_while(*condition, *body, env, d, b),

            Ast::Test(condition, body) => self.build_loop(*condition, *body, env, d, b),

            Ast::Builtin(bi, mut args) => {
                let arity = bi.arity();
                assert_eq!(arity, args.len());
                match bi {
                    Builtin::Assert => {
                        let arg = args.pop().unwrap();
                        match arg {
                            Argument::Positional(expr) => {
                                let index = self.lower_expr(*expr, env, d, b)?;
                                let msg = format!("assert at {}", location);
                                let assert_op =
                                    cf::assert(self.context, env.value0(&index), &msg, location);
                                Ok(env.push(assert_op))
                            }
                        }
                    }
                    Builtin::Print => {
                        let arg = args.pop().unwrap();
                        match arg {
                            Argument::Positional(expr) => {
                                let ast_ty = self.type_from_expr(&expr, env);

                                // eval expr
                                let mut index = self.lower_expr(*expr, env, d, b)?;

                                // deref
                                if ast_ty.is_ptr() {
                                    index = self.emit_deref(index, location, env, d, b)?;
                                }

                                let r = env.value0(&index);
                                let ty = r.r#type();
                                //let ast_ty = env.data(&index).unwrap();

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
                                    func::call(self.context, f, &env.values(&index), &[], location);

                                Ok(env.push(op))
                            }
                        }
                    }
                    Builtin::Import => {
                        let arg = args.pop().unwrap();
                        log::debug!("import: {:?}", arg);
                        if let Argument::Positional(expr) = arg {
                            if let Some(s) = expr.try_string() {
                                env.add_shared(&s);
                            } else {
                                d.push_diagnostic(expr.extra.error("Expected string"));
                            }
                        } else {
                            unimplemented!()
                        }
                        // do nothing?
                        Ok(env.push_noop())
                    } //_ => unimplemented!("{:?}", b),
                }
            } //_ => unimplemented!("{:?}", expr.node),
        }
    }
    pub fn emit_deref(
        &self,
        index: LayerIndex,
        location: Location<'c>,
        env: &mut Environment<'c, E>,
        d: &mut Diagnostics,
        b: &NodeBuilder<E>,
    ) -> Result<LayerIndex> {
        let data = env.data(&index).unwrap();

        // ensure proper type
        if let AstType::Ptr(ast_ty) = &data {
            let r = env.value0(&index);
            let op = memref::load(r, &[], location);
            let index = env.push(op);
            env.index_data(&index, *ast_ty.clone());
            Ok(index)
        } else {
            unreachable!("Trying to dereference a non-pointer")
        }
    }
}
            */

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::default_context;
    use crate::NodeBuilder;
    use test_log::test;

    pub fn gen_test<'c, E: Extra>(_env: &mut Environment<'c, E>, b: &NodeBuilder<E>) -> AstNode<E> {
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

    pub fn gen_function_call<'c, E: Extra>(
        _env: &mut Environment<'c, E>,
        b: &NodeBuilder<E>,
    ) -> AstNode<E> {
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

    /*
    #[test]
    fn test_block() {
        let context = default_context();
        let mut lower = Lower::new(&context);
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let b = NodeBuilder::new(file_id, "type.py");
        let mut env = Environment::default();
        let ast: AstNode<SimpleExtra> = gen_block(&b);
        let r = lower
            .run_ast(ast, "../target/debug/", &mut env, &mut d, &b)
            .unwrap();
        assert_eq!(0, r);
    }

    #[test]
    fn test_gen() {
        let context = default_context();
        let mut lower: Lower<SimpleExtra> = Lower::new(&context);
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let b: NodeBuilder<SimpleExtra> = NodeBuilder::new(file_id, "type.py");
        let mut env = Environment::default();
        let ast: AstNode<SimpleExtra> = gen_function_call(&mut env, &b);
        let r = lower
            .run_ast(ast, "../target/debug/", &mut env, &mut d, &b)
            .unwrap();
        assert_eq!(0, r);
    }

    #[test]
    fn test_while() {
        let context = default_context();
        let mut lower = Lower::new(&context);
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let b = NodeBuilder::new(file_id, "type.py");
        let mut env = Environment::default();
        let ast: AstNode<SimpleExtra> = gen_while(&b);
        let r = lower
            .run_ast(ast, "../target/debug/", &mut env, &mut d, &b)
            .unwrap();
        assert_eq!(0, r);
    }

    #[test]
    fn test_loop() {
        let context = default_context();
        let mut d = Diagnostics::new();
        let mut lower = Lower::new(&context);
        let file_id = d.add_source("test.py".into(), "test".into());
        let b = NodeBuilder::new(file_id, "type.py");
        let mut env = Environment::default();
        let ast: AstNode<SimpleExtra> = gen_test(&mut env, &b);
        let r = lower
            .run_ast(ast, "../target/debug/", &mut env, &mut d, &b)
            .unwrap();
        assert_eq!(0, r);
    }
    */
}
