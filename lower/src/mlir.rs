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
            //DenseElementsAttribute,
            FlatSymbolRefAttribute,
            //FloatAttribute,
            //IntegerAttribute,
            StringAttribute,
            TypeAttribute,
        },
        r#type::{
            FunctionType,
            IntegerType,
            MemRefType,
            //RankedTensorType
        },
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
                // this is only used for the top level module?
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

            IRKind::Decl(key, ast_ty, mem) => {
                let current_block = stack.last().unwrap().clone();
                let is_current_static = current_block == cfg.root();
                match mem {
                    VarDefinitionSpace::Static => {
                        if is_current_static {
                            // STATIC/GLOBAL VARIABLE
                            match &ast_ty {
                                AstType::Func(_, _) => op::emit_declare_function(
                                    context,
                                    key,
                                    ast_ty,
                                    location,
                                    current_block,
                                    cfg,
                                    cfg_g,
                                    b,
                                ),
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
                            cfg.set_type(index, ast_ty, mem);
                            Ok(index)
                        }
                    }

                    VarDefinitionSpace::Default | VarDefinitionSpace::Stack => {
                        //unimplemented!("{:?}", mem);
                        let ty = op::from_type(context, &ast_ty);
                        let memref_ty = MemRefType::new(ty.into(), &[], None, None);
                        let op = memref::alloca(context, memref_ty, &[], &[], None, location);
                        let current = cfg_g.node_weight_mut(current_block).unwrap();
                        let index = current.push_with_name(op, key);
                        cfg.set_type(index, ast_ty, mem);
                        Ok(index)
                    }
                    _ => unimplemented!("{:?}", mem),
                }
            }

            IRKind::Set(name, expr, _select) => {
                let current_block = stack.last().unwrap().clone();
                let span = self.span.clone();
                if let Some(sym_index) = cfg.name_in_scope(current_block, name, cfg_g) {
                    let is_symbol_static = sym_index.block() == cfg.root();
                    if is_symbol_static {
                        match expr.kind {
                            IRKind::Func(_, _) => op::emit_set_function(
                                context,
                                sym_index,
                                *expr,
                                current_block,
                                cfg,
                                stack,
                                g,
                                cfg_g,
                                d,
                                b,
                            ),
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
                        let block = cfg_g.node_weight_mut(sym_index.block()).unwrap();
                        block.add_symbol(name, sym_index);
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

            IRKind::Branch(condition, then_key, else_key) => {
                let condition_index = condition.lower_mlir(context, d, cfg, stack, g, cfg_g, b)?;
                let current_block = stack.last().unwrap().clone();

                // look up defined blocks
                let then_block_index = cfg.block_index(&then_key).unwrap();
                let else_block_index = cfg.block_index(&else_key).unwrap();

                cfg_g.add_edge(current_block, then_block_index, ());
                cfg_g.add_edge(current_block, else_block_index, ());

                let current = cfg_g.node_weight(current_block).unwrap();
                let r = current.value0(condition_index).unwrap();

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
                    &[], //then_args,
                    &[], //else_args,
                    location,
                );
                let current = cfg_g.node_weight_mut(current_block).unwrap();
                Ok(current.push(op))
            }

            IRKind::Ret(mut args) => {
                let current_block = stack.last().unwrap().clone();

                if args.len() > 0 {
                    let expr = args.pop().unwrap();
                    let mut index = expr.lower_mlir(context, d, cfg, stack, g, cfg_g, b)?;
                    let (_ast_ty, mem) = cfg.lookup_type(index).unwrap();

                    if mem.requires_deref() {
                        // if it's in memory, we need to copy to return
                        let target = DerefTarget::Offset(0);
                        //unimplemented!();
                        index = crate::cfg::emit_deref(
                            context, index, location, target, d, cfg, stack, cfg_g,
                        )?;
                    }

                    let rs = values_in_scope(cfg_g, index).clone();
                    let op = func::r#return(&rs, location);
                    let current = cfg_g.node_weight_mut(current_block).unwrap();
                    Ok(current.push(op))
                } else {
                    let current = cfg_g.node_weight_mut(current_block).unwrap();
                    Ok(current.push(func::r#return(&[], location)))
                }

                //let mut rs = vec![];
                /*
                for expr in args {
                    let index = expr.lower_mlir(context, d, cfg, stack, g, cfg_g, b)?;
                    //let data = cfg_g.node_weight(index.block()).unwrap();
                    //let r = data.value0(index).unwrap().into();
                    //let r = values_in_scope(cfg_g, index)[0];
                    rs.push(index);
                }
                let rs = rs
                    .into_iter()
                    .map(|index| {
                        let data = cfg_g.node_weight(index.block()).unwrap();
                        //values_in_scope(cfg_g, index)[0]
                        //data.value0(index).unwrap().into()
                        (data, index)
                    })
                    //.flatten()
                    .collect::<Vec<_>>();
                let rs = rs.into_iter().map(|(data, index)| data.value0(index).unwrap()).collect::<Vec<_>>();
                let current = cfg_g.node_weight_mut(current_block).unwrap();
                Ok(current.push(func::r#return(&rs, location)))
                */
            }

            IRKind::Label(_label, _args) => {
                // this should have been removed by now, when converted to blocks
                unreachable!()
            }

            IRKind::Jump(label, args) => {
                let current_block = stack.last().unwrap().clone();
                let span = self.span.clone();
                if let Some(block_index) = cfg.block_index(&label) {
                    g.add_edge(current_block, block_index, ());

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

                    let target_block = cfg_g
                        .node_weight(block_index)
                        .unwrap()
                        .block
                        .as_ref()
                        .unwrap();
                    //let block = target_block.block.as_ref().unwrap();

                    let op = cf::br(target_block, &arg_values, location);
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
                //if let Some((op, ty)) = op::build_reserved(context, &s, location) {
                //let current = cfg_g.node_weight_mut(current_block).unwrap();
                //let index = current.push(op);
                //cfg.set_type(index, ty, VarDefinitionSpace::Reg);
                //Ok(index)
                //} else {
                println!("lookup: {}, {:?}", b.strings.resolve(&name), current_block);

                cfg.save_graph("out.dot", cfg_g, b);
                //cfg.dump_scope(current_block, cfg_g, b);

                if let Some(mut sym_index) = cfg.name_in_scope(current_block, name, cfg_g) {
                    println!(
                        "lookup identifier: {}, {:?}",
                        b.strings.resolve(&name),
                        sym_index
                    );
                    if cfg.block_is_static(sym_index.block()) {
                        let (ast_ty, mem) = cfg.lookup_type(sym_index).unwrap();

                        /*
                        if mem.requires_deref() {
                            let target = DerefTarget::Offset(0);
                            //unimplemented!();
                            sym_index = crate::cfg::emit_deref(
                                context, sym_index, location, target, d, cfg, stack, cfg_g,
                                )?;
                        }
                        */

                        if mem.requires_deref() {
                            //if let AstType::Ptr(ty) = &ast_ty {
                            let lower_ty = op::from_type(context, &ast_ty);
                            let memref_ty = MemRefType::new(lower_ty, &[], None, None);
                            let static_name = b.strings.resolve(
                                &cfg.static_names.get(&sym_index).cloned().unwrap_or(name),
                            );
                            let op = memref::get_global(context, &static_name, memref_ty, location);
                            let current = cfg_g.node_weight_mut(current_block).unwrap();
                            let addr_index = current.push(op);
                            let r_addr = current.value0(addr_index).unwrap();

                            let op = memref::load(r_addr, &[], location);
                            //let current = g.node_weight_mut(current_block).unwrap();
                            let value_index = current.push(op);
                            //cfg.set_type(index, ty, mem);
                            //Ok(index)

                            cfg.set_type(value_index, ast_ty, VarDefinitionSpace::Stack);
                            return Ok(value_index);
                            //} else {
                            //unreachable!("Identifier of static variable must be pointer");
                            //d.push_diagnostic(ir::error(
                            //&format!("mlir Expected pointer: {:?}", &ast_ty),
                            //span,
                            //));
                            //return Err(Error::new(ParseError::Invalid));
                        }
                    }
                    //} else {
                    return Ok(sym_index);
                    //}
                }
                d.push_diagnostic(ir::error(&format!("Name not found: {:?}", name), span));
                Err(Error::new(ParseError::Invalid))
                //}
            }

            IRKind::Call(key, args) => {
                // function to call
                let current_block = stack.last().unwrap().clone();
                let name = b.strings.resolve(&key);
                let span = self.span.clone();
                let (f, (ty, mem)) =
                    if let Some(index) = cfg.name_in_scope(current_block, key, cfg_g) {
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
                    cfg.set_type(index, *ret.clone(), VarDefinitionSpace::Reg);
                    Ok(index)
                } else {
                    unimplemented!("calling non function type: {:?}", ty);
                }
            }

            IRKind::Func(_blocks, _ret_ty) => {
                unreachable!();
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
                cfg.set_type(index, ast_ty, VarDefinitionSpace::Reg);
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
                        let (ast_ty, mem) = cfg.lookup_type(index).unwrap();

                        // deref
                        if mem.requires_deref() {
                            let target = DerefTarget::Offset(0);
                            //unimplemented!();
                            index = crate::cfg::emit_deref(
                                context, index, location, target, d, cfg, stack, cfg_g,
                            )?;
                        }
                        /*
                        if ast_ty.is_ptr() {
                            let target = DerefTarget::Offset(0);
                            unimplemented!();
                            index = crate::cfg::emit_deref(
                                context, index, location, target, d, cfg, stack, cfg_g,
                            )?;
                        }
                        */

                        let r = values_in_scope(cfg_g, index)[0];

                        //let r = current.value0(index).unwrap();
                        let ty = r.r#type();

                        // Select the baked version based on parameters
                        // TODO: A more dynamic way of doing this
                        // TODO: We only want to import these if they are referenced
                        let ident = if ty.is_index() || ty.is_integer() {
                            "print_index"
                        } else if ty.is_f64() {
                            "print_float"
                        } else {
                            unimplemented!("{:?}", (&ty, mem, ast_ty))
                        };

                        let f = FlatSymbolRefAttribute::new(context, ident);
                        let op = func::call(context, f, &[r], &[], location);

                        let current = cfg_g.node_weight_mut(current_block).unwrap();
                        Ok(current.push(op))
                    }
                    _ => unreachable!("{:?}", bi),
                }
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
                            cfg.set_type(index, AstType::Int, VarDefinitionSpace::Reg);
                            Ok(index)
                        } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                            // arith has an op for negation
                            let r_rhs = current.value0(index).unwrap();
                            let index = current.push(arith::negf(r_rhs, location));
                            cfg.set_type(index, AstType::Float, VarDefinitionSpace::Reg);
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

                let (ty_x, mem_x) = cfg
                    .lookup_type(index_x)
                    .expect(&format!("missing type for {:?}, {}", index_x, fx));

                let (ty_y, mem_y) = cfg
                    .lookup_type(index_y)
                    .expect(&format!("missing type for {:?}, {}", index_y, fy));

                println!("ty_x: {:?}", (ty_x, mem_x));
                println!("ty_y: {:?}", (ty_y, mem_y));
                let current_block = stack.last().unwrap().clone();
                let current = cfg_g.node_weight_mut(current_block).unwrap();
                println!("{:?}", current);

                let index_x = if mem_x.requires_deref() {
                    //let (_ty_x, index_x) = if let AstType::Ptr(ty) = ty_x {
                    let target = DerefTarget::Offset(0);
                    let index = crate::cfg::emit_deref(
                        context, index_x, x_location, target, d, cfg, stack, cfg_g,
                    )?;
                    index
                } else {
                    index_x
                };

                let index_y = if mem_y.requires_deref() {
                    //let (_ty_y, index_y) = if let AstType::Ptr(ty) = ty_y {
                    let target = DerefTarget::Offset(0);
                    let index = crate::cfg::emit_deref(
                        context, index_y, y_location, target, d, cfg, stack, cfg_g,
                    )?;
                    index
                } else {
                    index_y
                };

                // types must be the same for binary operation, no implicit casting yet
                let a = values_in_scope(cfg_g, index_x)[0];
                let b = values_in_scope(cfg_g, index_y)[0];
                let (op, ast_ty) =
                    op::build_binop(context, op, a, &x_extra, b, &y_extra, location, d)?;
                let current = cfg_g.node_weight_mut(current_block).unwrap();
                let index = current.push(op);
                cfg.set_type(index, ast_ty, VarDefinitionSpace::Reg);
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
