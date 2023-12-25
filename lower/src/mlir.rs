use crate::ast::{
    Argument, AssignTarget, Ast, AstNode, Builtin, DerefTarget, Literal, Parameter, ParameterNode,
    VarDefinitionSpace,
};
use crate::cfg::{values_in_scope, CFGGraph, SymIndex, CFG};
use crate::ir;
use crate::ir::{IRGraph, IRKind, IRNode};

use crate::op;
use crate::{AstType, Extra, NodeBuilder};
use crate::{Diagnostics, ParseError};
use anyhow::Error;
use anyhow::Result;
use melior::ir::Location;
use melior::{
    dialect::{
        arith,
        cf,
        func,
        //llvm,
        memref,
        //ods,
        //scf,
    },
    ir::{
        attribute::{
            DenseElementsAttribute,
            FlatSymbolRefAttribute,
            //FloatAttribute,
            IntegerAttribute,
            StringAttribute,
            TypeAttribute,
        },
        r#type::{FunctionType, IntegerType, MemRefType, RankedTensorType},
        Attribute, Identifier, Region, TypeLike, ValueLike,
    },
    Context,
};
use petgraph::graph::NodeIndex;

impl IRNode {
    pub fn location<'c>(&self, context: &'c Context, d: &Diagnostics) -> Location<'c> {
        d.location(context, &self.get_span())
    }

    pub fn lower_mlir<'c, E: Extra>(
        self,
        context: &'c Context,
        d: &mut Diagnostics,
        cfg: &mut CFG<'c, E>,
        stack: &mut Vec<NodeIndex>,
        g: &mut IRGraph,
        cfg_g: &mut CFGGraph<'c>,
        b: &mut NodeBuilder<E>,
    ) -> Result<SymIndex> {
        let location = self.location(context, d);
        match self.kind {
            IRKind::Noop => {
                let current_block = stack.last().unwrap().clone();
                op::emit_noop(context, location, current_block, cfg_g)
            }

            IRKind::Block(block) => {
                let current_block = stack.last().unwrap().clone();
                assert_eq!(cfg.root(), current_block);

                let mut out = vec![];
                for expr in block.children {
                    let index = expr.lower_mlir(context, d, cfg, stack, g, cfg_g, b)?;
                    out.push(index);
                }
                Ok(out.last().cloned().unwrap())
            }

            IRKind::Seq(exprs) => {
                let mut out = vec![];
                for expr in exprs {
                    let index = expr.lower_mlir(context, d, cfg, stack, g, cfg_g, b)?;
                    out.push(index);
                }
                Ok(out.last().cloned().unwrap())
            }

            IRKind::Ret(args) => {
                let current_block = stack.last().unwrap().clone();
                let mut rs = vec![];
                for expr in args {
                    let index = expr.lower_mlir(context, d, cfg, stack, g, cfg_g, b)?;
                    rs.push(index);
                }
                let current = cfg_g.node_weight_mut(current_block).unwrap();
                let rs = rs
                    .into_iter()
                    .map(|index| current.values(index))
                    .flatten()
                    .collect::<Vec<_>>();
                Ok(current.push(func::r#return(&rs, location)))
            }

            IRKind::Label(_label, _args) => {
                unreachable!()
            }

            IRKind::Jump(label, args) => {
                let current_block = stack.last().unwrap().clone();
                let span = self.span.clone();
                if let Some(index) = cfg.block_index(&label) {
                    let mut arg_index = vec![];
                    for expr in args {
                        let index = expr.lower_mlir(context, d, cfg, stack, g, cfg_g, b)?;
                        arg_index.push(index);
                    }

                    let current = cfg_g.node_weight(current_block).unwrap();

                    let arg_values = arg_index
                        .into_iter()
                        .map(|index| current.values(index))
                        .flatten()
                        .collect::<Vec<_>>();

                    let target_block = cfg_g.node_weight(index).unwrap().block.as_ref().unwrap();
                    //let block = target_block.block.as_ref().unwrap();

                    let op = cf::br(target_block, &arg_values, location);
                    g.add_edge(current_block, index, ());
                    let current = cfg_g.node_weight_mut(current_block).unwrap();
                    Ok(current.push(op))
                } else {
                    d.push_diagnostic(ir::error(
                        &format!("Missing block: {}", b.strings.resolve(&label)),
                        span,
                    ));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            IRKind::Get(name, select) => {
                let current_block = stack.last().unwrap().clone();
                let span = self.span.clone();
                let s = b.strings.resolve(&name);
                if let Some((op, ty)) = op::build_reserved(context, &s, location) {
                    let current = cfg_g.node_weight_mut(current_block).unwrap();
                    let index = current.push(op);
                    cfg.set_type(index, ty);
                    Ok(index)
                } else {
                    if let Some(sym_index) = cfg.name_in_scope(current_block, name, cfg_g) {
                        println!(
                            "lookup identifier: {}, {:?}",
                            b.strings.resolve(&name),
                            sym_index
                        );
                        if cfg.block_is_static(sym_index.block()) {
                            let ast_ty = cfg.lookup_type(sym_index).unwrap();
                            if let AstType::Ptr(ty) = &ast_ty {
                                let lower_ty = op::from_type(context, ty);
                                let memref_ty = MemRefType::new(lower_ty, &[], None, None);
                                let static_name = b.strings.resolve(
                                    &cfg.static_names.get(&sym_index).cloned().unwrap_or(name),
                                );
                                let op =
                                    memref::get_global(context, &static_name, memref_ty, location);
                                let current = cfg_g.node_weight_mut(current_block).unwrap();
                                let index = current.push(op);
                                cfg.set_type(index, ast_ty);
                                return Ok(index);
                            } else {
                                //unreachable!("Identifier of static variable must be pointer");
                                d.push_diagnostic(ir::error(
                                    &format!("Expected pointer: {:?}", &ast_ty),
                                    span,
                                ));
                                return Err(Error::new(ParseError::Invalid));
                            }
                        } else {
                            return Ok(sym_index);
                        }
                    }
                    d.push_diagnostic(ir::error(&format!("Name not found: {:?}", name), span));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            IRKind::Decl(key, ast_ty, mem) => {
                let current_block = stack.last().unwrap().clone();
                let is_current_static = current_block == cfg.root();
                match mem {
                    VarDefinitionSpace::Static => {
                        if is_current_static {
                            // STATIC/GLOBAL VARIABLE
                            match &ast_ty {
                                AstType::Func(params, ast_ret_type) => {
                                    //IRKind::Func(blocks, ast_ret_ty) => {
                                    //let first = blocks.first().unwrap();
                                    let mut types = vec![];
                                    let mut ast_types = vec![];
                                    //let ast_ret_type = def.return_type;

                                    let attributes = vec![(
                                        Identifier::new(context, "sym_visibility"),
                                        StringAttribute::new(context, "private").into(),
                                    )];

                                    for ty in params {
                                        types.push(op::from_type(context, &ty));
                                        ast_types.push(ty.clone());
                                    }

                                    let region = Region::new();

                                    let ret_type = if let AstType::Unit = **ast_ret_type {
                                        vec![]
                                    } else {
                                        vec![op::from_type(context, &ast_ret_type)]
                                    };

                                    let func_type = FunctionType::new(context, &types, &ret_type);
                                    let op = func::func(
                                        context,
                                        StringAttribute::new(context, b.strings.resolve(&key)),
                                        TypeAttribute::new(func_type.into()),
                                        region,
                                        &attributes,
                                        location,
                                    );

                                    let function_block =
                                        cfg_g.node_weight_mut(current_block).unwrap();
                                    let index = function_block.push(op);
                                    function_block.add_symbol(key, index);
                                    cfg.set_type(index, ast_ty);

                                    //if let Some(entry_block) = entry_block {
                                    //let data = g.node_weight_mut(entry_block).unwrap();
                                    //data.set_parent_symbol(func_index);
                                    //}

                                    Ok(index)
                                }
                                _ => op::emit_declare_static(
                                    context,
                                    key,
                                    ast_ty,
                                    location,
                                    current_block,
                                    cfg,
                                    cfg_g,
                                    b,
                                ),
                            }
                        } else {
                            // STATIC VARIABLE IN FUNCTION CONTEXT

                            // emitting in non-static context (local static var)
                            // we create a unique global name to prevent conflict
                            // and then we add ops to provide a local reference to the global name
                            let base = b.strings.resolve(&key).clone();
                            let name = b.unique_static_name();
                            let name = format!("{}{}", base, name).clone();
                            let global_name_key = b.strings.intern(name.clone());

                            let ty = IntegerType::new(context, 64);
                            let memref_ty = MemRefType::new(ty.into(), &[], None, None);
                            let op = memref::alloca(context, memref_ty, &[], &[], None, location);
                            let current = cfg_g.node_weight_mut(current_block).unwrap();
                            let index = current.push_with_name(op, key);
                            cfg.static_names.insert(index, global_name_key);
                            Ok(index)
                        }
                    }

                    VarDefinitionSpace::Default | VarDefinitionSpace::Stack => {
                        unimplemented!("{:?}", mem);
                        let ty = op::from_type(context, &ast_ty);
                        //let ty = IntegerType::new(context, 64);
                        let memref_ty = MemRefType::new(ty.into(), &[], None, None);
                        let op = memref::alloca(context, memref_ty, &[], &[], None, location);
                        let current = cfg_g.node_weight_mut(current_block).unwrap();
                        let index = current.push_with_name(op, key);
                        Ok(index)
                    }
                    _ => unimplemented!("{:?}", mem),
                }
            }

            IRKind::Set(name, expr, select) => {
                let current_block = stack.last().unwrap().clone();
                let span = self.span.clone();
                if let Some(sym_index) = cfg.name_in_scope(current_block, name, cfg_g) {
                    let is_symbol_static = sym_index.block() == cfg.root();
                    if is_symbol_static {
                        match expr.kind {
                            IRKind::Func(blocks, ast_ty) => {
                                let mut block_indicies = vec![];
                                for (_i, block) in blocks.into_iter().enumerate() {
                                    let block_index = cfg.add_block_ir(
                                        context,
                                        block.name,
                                        &block.params,
                                        d,
                                        cfg_g,
                                    );
                                    //let _data = g.node_weight_mut(block_index).unwrap();
                                    block_indicies.push(block_index);
                                    for c in block.children.into_iter() {
                                        stack.push(block_index);
                                        if let Ok(_index) =
                                            c.lower_mlir(context, d, cfg, stack, g, cfg_g, b)
                                        {
                                            stack.pop();
                                        } else {
                                            stack.pop();
                                            return Err(Error::new(ParseError::Invalid));
                                        }
                                    }
                                    //let region = Region::new();
                                }
                                for block_index in block_indicies {
                                    let block = cfg.take_block(block_index, cfg_g);
                                    let current = cfg_g.node_weight_mut(current_block).unwrap();
                                    let op = current.op_ref(sym_index);
                                    op.region(0).unwrap().append_block(block);
                                    //region.append_block(block);
                                }
                                Ok(sym_index)
                                /*
                                op::emit_set_function(
                                    context,
                                    sym_index,
                                    name,
                                    *expr,
                                    location,
                                    current_block,
                                    cfg,
                                    cfg_g,
                                    d,
                                    b,
                                    )
                                    */
                            }
                            _ => op::emit_set_static(
                                context,
                                sym_index,
                                name,
                                *expr,
                                location,
                                current_block,
                                cfg,
                                cfg_g,
                                d,
                                b,
                            ),
                        }
                    } else {
                        op::emit_set_alloca(
                            context,
                            sym_index,
                            name,
                            *expr,
                            location,
                            current_block,
                            cfg,
                            stack,
                            g,
                            cfg_g,
                            d,
                            b,
                        )
                    }
                } else {
                    d.push_diagnostic(ir::error(&format!("Name not found: {:?}", name), span));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            IRKind::Call(key, args) => {
                // function to call
                let current_block = stack.last().unwrap().clone();
                let name = b.strings.resolve(&key);
                let span = self.span.clone();
                let (f, ty) = if let Some(index) = cfg.name_in_scope(current_block, key, cfg_g) {
                    if let Some(ty) = cfg.lookup_type(index) {
                        (FlatSymbolRefAttribute::new(context, name), ty)
                    } else {
                        d.push_diagnostic(ir::error(
                            &format!("Type not found: {}, {:?}", name, index),
                            span,
                        ));
                        return Err(Error::new(ParseError::Invalid));
                    }
                } else {
                    d.push_diagnostic(ir::error(&format!("Name not found: {}", name), span));
                    return Err(Error::new(ParseError::Invalid));
                };

                if let AstType::Func(_func_arg_types, ret) = &ty {
                    let ret_type = op::from_type(context, &ret);
                    // handle call arguments
                    let mut indices = vec![];

                    // lower call args
                    for a in args {
                        let index = a.lower_mlir(context, d, cfg, stack, g, cfg_g, b)?;
                        indices.push(index);
                    }

                    let call_args = indices
                        .into_iter()
                        .map(|index| values_in_scope(cfg_g, index)[0])
                        .collect::<Vec<_>>();

                    let op = func::call(
                        context,
                        f,
                        call_args.as_slice(),
                        &[ret_type.clone()],
                        location,
                    );
                    let current = cfg_g.node_weight_mut(current_block).unwrap();

                    let index = current.push(op);
                    cfg.set_type(index, *ret.clone());
                    Ok(index)
                } else {
                    unimplemented!("calling non function type: {:?}", ty);
                }
            }

            IRKind::Func(blocks, ret_ty) => {
                let current_block = stack.last().unwrap().clone();

                assert!(cfg.block_is_static(current_block));

                let mut attributes = vec![(
                    Identifier::new(context, "sym_visibility"),
                    StringAttribute::new(context, "private").into(),
                )];

                let name = blocks.first().as_ref().unwrap().name;

                //let first = blocks.first();
                //let ast_types = first.as_ref().unwrap().params.iter().map(|p| p.ty.clone()).collect::<Vec<_>>();
                let types = blocks
                    .first()
                    .as_ref()
                    .unwrap()
                    .params
                    .iter()
                    .map(|p| op::from_type(context, &p.ty))
                    .collect::<Vec<_>>();
                //let f_type = AstType::Func(ast_types, ret_ty.into());

                let ret_ty = op::from_type(context, &ret_ty);
                //let mut types = vec![];

                let ret_type = if ret_ty.is_none() {
                    vec![]
                } else {
                    vec![ret_ty]
                };

                let func_type = FunctionType::new(context, &types, &ret_type);
                //let mut entry_block = None;

                let function_block = cfg_g.node_weight_mut(current_block).unwrap();
                let func_index = function_block.get_next_index();
                //function_block.add_symbol(def.name, func_index);
                //cfg.set_type(func_index, f_type);

                let region = Region::new();

                for (_i, block) in blocks.into_iter().enumerate() {
                    // connect the first block to the function
                    let index = cfg.block_index(&block.name).unwrap();
                    //cfg.dump_scope(index, g);
                    for expr in block.children {
                        stack.push(index);
                        if let Ok(_index) = expr.lower_mlir(context, d, cfg, stack, g, cfg_g, b) {
                            stack.pop();
                        } else {
                            stack.pop();
                            return Err(Error::new(ParseError::Invalid));
                        }
                    }
                    let block = cfg.take_block(index, cfg_g);
                    region.append_block(block);
                }

                // declare as C interface only if body is defined
                // function declarations represent functions that are already C interfaces
                attributes.push((
                    Identifier::new(context, "llvm.emit_c_interface"),
                    Attribute::unit(context),
                ));

                let op = func::func(
                    context,
                    StringAttribute::new(context, b.strings.resolve(&name)),
                    TypeAttribute::new(func_type.into()),
                    region,
                    &attributes,
                    location,
                );

                let function_block = cfg_g.node_weight_mut(current_block).unwrap();
                function_block.save_op(func_index, op);

                //if let Some(entry_block) = entry_block {
                //let data = g.node_weight_mut(entry_block).unwrap();
                //data.set_parent_symbol(func_index);
                //}

                Ok(func_index)
            }

            IRKind::Literal(lit) => {
                let current_block = stack.last().unwrap().clone();
                let current = cfg_g.node_weight_mut(current_block).unwrap();
                let (op, ast_ty) = match lit {
                    Literal::Float(f) => (op::build_float_op(context, f, location), AstType::Float),

                    Literal::Int(x) => (op::build_int_op(context, x, location), AstType::Int),

                    Literal::Index(x) => (
                        op::build_index_op(context, x as i64, location),
                        AstType::Index,
                    ),

                    Literal::Bool(x) => (op::build_bool_op(context, x, location), AstType::Bool),
                    _ => unimplemented!("{:?}", lit),
                };
                let index = current.push(op);
                cfg.set_type(index, ast_ty);
                Ok(index)
            }

            IRKind::Builtin(bi, mut args) => {
                let arity = bi.arity();
                assert_eq!(arity, args.len());
                let current_block = stack.last().unwrap().clone();
                match bi {
                    Builtin::Assert => {
                        let arg = args.pop().unwrap();
                        let index = arg.lower_mlir(context, d, cfg, stack, g, cfg_g, b)?;
                        let msg = format!("assert at {}", location);
                        let current = cfg_g.node_weight_mut(current_block).unwrap();
                        let r = current.value0(index).unwrap();
                        let op = cf::assert(context, r, &msg, location);
                        Ok(current.push(op))
                    }
                    Builtin::Print => {
                        let arg = args.pop().unwrap();
                        // eval expr
                        let mut index = arg.lower_mlir(context, d, cfg, stack, g, cfg_g, b)?;
                        let ast_ty = cfg.lookup_type(index).unwrap();

                        // deref
                        if ast_ty.is_ptr() {
                            let target = DerefTarget::Offset(0);
                            index = crate::cfg::emit_deref(
                                context, index, location, target, d, cfg, stack, cfg_g,
                            )?;
                        }

                        let current = cfg_g.node_weight_mut(current_block).unwrap();
                        let r = current.value0(index).unwrap();
                        let ty = r.r#type();

                        // Select the baked version based on parameters
                        // TODO: A more dynamic way of doing this
                        // TODO: We only want to import these if they are referenced
                        let ident = if ty.is_index() || ty.is_integer() {
                            "print_index"
                        } else if ty.is_f64() {
                            "print_float"
                        } else {
                            unimplemented!("{:?}", &ty)
                        };

                        let f = FlatSymbolRefAttribute::new(context, ident);
                        let op = func::call(context, f, &[r], &[], location);

                        Ok(current.push(op))
                    }
                    _ => unreachable!("{:?}", bi),
                }
            }

            IRKind::Branch(condition, then_key, else_key) => {
                let index = condition.lower_mlir(context, d, cfg, stack, g, cfg_g, b)?;
                let current_block = stack.last().unwrap().clone();

                let then_args = vec![];
                let then_block_index = cfg.block_index(&then_key).unwrap();

                let current = cfg_g.node_weight(current_block).unwrap();
                let r = current.value0(index).unwrap();

                let else_args = vec![];
                let else_block_index = cfg.block_index(&else_key).unwrap();
                let then_block = cfg_g
                    .node_weight(then_block_index)
                    .unwrap()
                    .block
                    .as_ref()
                    .unwrap();
                let else_block = cfg_g
                    .node_weight(else_block_index)
                    .unwrap()
                    .block
                    .as_ref()
                    .unwrap();
                let op = cf::cond_br(
                    context,
                    r,
                    &then_block,
                    &else_block,
                    &then_args,
                    &else_args,
                    location,
                );
                let current = cfg_g.node_weight_mut(current_block).unwrap();
                Ok(current.push(op))
            }

            IRKind::Op1(op, a) => {
                use crate::ast::UnaryOperation;
                let index = a.lower_mlir(context, d, cfg, stack, g, cfg_g, b)?;
                let current_block = stack.last().unwrap().clone();
                let current = cfg_g.node_weight_mut(current_block).unwrap();
                let ty = {
                    println!("{:?}", current);
                    // get the type of the RHS
                    let ty = current.value0(index).unwrap().r#type();
                    ty
                };

                match op {
                    UnaryOperation::Minus => {
                        if ty.is_index() {
                            unreachable!("Unable to negate index type");
                        } else if ty.is_integer() {
                            // Multiply by -1
                            let int_op = op::build_int_op(context, -1, location);
                            let index_lhs = current.push(int_op);
                            let r = current.value0(index_lhs).unwrap();
                            let r_rhs = current.value0(index).unwrap();
                            let index = current.push(arith::muli(r, r_rhs, location));
                            cfg.set_type(index, AstType::Int);
                            Ok(index)
                        } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                            // arith has an op for negation
                            let r_rhs = current.value0(index).unwrap();
                            let index = current.push(arith::negf(r_rhs, location));
                            cfg.set_type(index, AstType::Float);
                            Ok(index)
                        } else {
                            unimplemented!()
                        }
                    }
                }
            }

            IRKind::Op2(op, x, y) => {
                let fx = format!("x: {:?}", x);
                let fy = format!("y: {:?}", y);
                let x_extra = E::span(x.get_span());
                let y_extra = E::span(y.get_span());
                let x_location = x.location(context, d);
                let y_location = x.location(context, d);
                let index_x = x.lower_mlir(context, d, cfg, stack, g, cfg_g, b)?;
                let index_y = y.lower_mlir(context, d, cfg, stack, g, cfg_g, b)?;

                //cfg.save_graph("out.dot", g);
                println!("ix: {:?}, {}", index_x, fx);
                println!("iy: {:?}, {}", index_y, fy);
                let ty_x = cfg
                    .lookup_type(index_x)
                    .expect(&format!("missing type for {:?}, {}", index_x, fx));
                let ty_y = cfg
                    .lookup_type(index_y)
                    .expect(&format!("missing type for {:?}, {}", index_y, fy));
                let current_block = stack.last().unwrap().clone();
                let current = cfg_g.node_weight_mut(current_block).unwrap();
                println!("{:?}", current);

                let (_ty_x, index_x) = if let AstType::Ptr(ty) = ty_x {
                    let target = DerefTarget::Offset(0);
                    let index = crate::cfg::emit_deref(
                        context, index_x, x_location, target, d, cfg, stack, cfg_g,
                    )?;
                    (*ty, index)
                } else {
                    (ty_x, index_x)
                };

                let (_ty_y, index_y) = if let AstType::Ptr(ty) = ty_y {
                    let target = DerefTarget::Offset(0);
                    let index = crate::cfg::emit_deref(
                        context, index_y, y_location, target, d, cfg, stack, cfg_g,
                    )?;
                    (*ty, index)
                } else {
                    (ty_y, index_y)
                };

                // types must be the same for binary operation, no implicit casting yet
                let a = values_in_scope(cfg_g, index_x)[0];
                let b = values_in_scope(cfg_g, index_y)[0];
                let (op, ast_ty) =
                    op::build_binop(context, op, a, &x_extra, b, &y_extra, location, d)?;
                let current = cfg_g.node_weight_mut(current_block).unwrap();
                let index = current.push(op);
                cfg.set_type(index, ast_ty);
                Ok(index)
            }

            _ => {
                d.push_diagnostic(ir::error(
                    &format!("Unimplemented: {:?}", self.kind),
                    self.get_span(),
                ));
                Err(Error::new(ParseError::Invalid))
            }
        }
    }
}
