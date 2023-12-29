use crate::ast::{
    //Argument,
    //AssignTarget, Ast, AstNode,
    Builtin,
    DerefTarget,
    Literal,
    //Parameter, ParameterNode,
    VarDefinitionSpace,
};
use crate::ir;
use crate::ir::{
    //IRGraph,
    IRKind,
    IRNode,
};

use crate::op;
use crate::{
    AstType, CFGBlocks, Extra, IRPlaceTable, LinkOptions, NodeBuilder, SymIndex, TypeBuilder,
};
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
        attribute::FlatSymbolRefAttribute,
        r#type::MemRefType,
        //Attribute, Identifier, Region,
        TypeLike,
        ValueLike,
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
        place: &IRPlaceTable,
        d: &mut Diagnostics,
        types: &mut TypeBuilder,
        blocks: &mut CFGBlocks<'c>,
        stack: &mut Vec<NodeIndex>,
        b: &mut NodeBuilder<E>,
        link: &mut LinkOptions,
    ) -> Result<SymIndex> {
        let location = self.location(context, d);
        match self.kind {
            IRKind::Noop => {
                let current_block = stack.last().unwrap().clone();
                op::emit_noop(context, location, current_block, blocks)
            }

            IRKind::Block(block) | IRKind::Module(block) => {
                let current_block = stack.last().unwrap().clone();
                // this is only used for the top level module?
                assert_eq!(blocks.root(), current_block);
                let mut out = vec![];
                for expr in block.children {
                    let index =
                        expr.lower_mlir(context, place, d, types, blocks, stack, b, link)?;
                    out.push(index);
                }
                Ok(out.last().cloned().unwrap())
            }

            IRKind::Seq(exprs) => {
                let mut out = vec![];
                for expr in exprs {
                    let index =
                        expr.lower_mlir(context, place, d, types, blocks, stack, b, link)?;
                    out.push(index);
                }
                Ok(out.last().cloned().unwrap())
            }

            IRKind::Decl(place_id) => {
                //key, ast_ty, mem) => {
                let current_block = stack.last().unwrap().clone();
                let is_current_static = current_block == blocks.root();
                let p = place.get_place(place_id);
                match p.mem {
                    VarDefinitionSpace::Static => {
                        if is_current_static {
                            // STATIC/GLOBAL VARIABLE
                            match &p.ty {
                                AstType::Func(_, _) => op::emit_declare_function(
                                    context,
                                    place_id,
                                    p.name,
                                    p.ty.clone(),
                                    location,
                                    current_block,
                                    types,
                                    blocks,
                                    //cfg_g,
                                    b,
                                ),
                                _ => op::emit_declare_static(
                                    context,
                                    place_id,
                                    p.name,
                                    p.ty.clone(),
                                    location,
                                    current_block,
                                    types,
                                    blocks,
                                    //cfg_g,
                                    b,
                                ),
                            }
                        } else {
                            // STATIC VARIABLE IN FUNCTION CONTEXT

                            // emitting in non-static context (local static var)
                            // we create a unique global name to prevent conflict
                            // and then we add ops to provide a local reference to the global name
                            let base = b.strings.resolve(&p.name).clone();
                            let name = b.unique_static_name();
                            let name = format!("{}{}", base, name).clone();
                            let global_name_key = b.strings.intern(name.clone());

                            let ty = op::from_type(context, &p.ty);
                            let memref_ty = MemRefType::new(ty.into(), &[], None, None);
                            let op = memref::alloca(context, memref_ty, &[], &[], None, location);
                            let current = blocks.get_mut(&current_block).unwrap();
                            let index = current.push_with_place(op, place_id);
                            current.add_symbol(p.name, index);
                            // TODO: FIXME
                            //cfg.static_names.insert(index, global_name_key);
                            types.set_type(index, p.ty.clone(), p.mem);
                            Ok(index)
                        }
                    }

                    VarDefinitionSpace::Default | VarDefinitionSpace::Stack => {
                        let ty = op::from_type(context, &p.ty);
                        let memref_ty = MemRefType::new(ty.into(), &[], None, None);
                        let op = memref::alloca(context, memref_ty, &[], &[], None, location);
                        //let current = cfg_g.node_weight_mut(current_block).unwrap();
                        let current = blocks.get_mut(&current_block).unwrap();
                        let index = current.push_with_place(op, place_id);
                        current.add_symbol(p.name, index);
                        types.set_type(index, p.ty.clone(), p.mem);
                        Ok(index)
                    }
                    _ => unimplemented!("{:?}", p.mem),
                }
            }

            IRKind::Set(place_id, expr, _select) => {
                let current_block = stack.last().unwrap().clone();
                let span = self.span.clone();
                let is_current_static = current_block == blocks.root();
                let p = place.get_place(place_id);
                if let Some(sym_index) = blocks.place_in_scope(current_block, place_id) {
                    let is_symbol_static = sym_index.block() == blocks.root();
                    if is_symbol_static && is_current_static {
                        println!("expr: {:?}", expr);
                        expr.dump(place, b, 0);
                        match expr.kind {
                            IRKind::Func(_, _) => op::emit_set_function(
                                context,
                                place,
                                sym_index,
                                *expr,
                                current_block,
                                types,
                                blocks,
                                stack,
                                //cfg_g,
                                d,
                                b,
                                link,
                            ),
                            _ => op::emit_set_static(
                                context,
                                sym_index,
                                p.name,
                                *expr,
                                current_block,
                                blocks,
                                //cfg_g,
                                d,
                                b,
                            ),
                        }
                    } else {
                        op::emit_set_alloca(
                            context,
                            place,
                            sym_index,
                            p.name,
                            *expr,
                            location,
                            current_block,
                            types,
                            blocks,
                            stack,
                            //cfg_g,
                            d,
                            b,
                            link,
                        )
                    }
                } else {
                    d.push_diagnostic(ir::error(
                        &format!("Set name not found: {:?}", b.strings.resolve(&p.name)),
                        span,
                    ));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            IRKind::Branch(condition, then_key, else_key) => {
                let condition_index =
                    condition.lower_mlir(context, place, d, types, blocks, stack, b, link)?;
                let current_block = stack.last().unwrap().clone();

                // look up defined blocks
                let then_block_index = blocks.block_index(&then_key).unwrap();
                let else_block_index = blocks.block_index(&else_key).unwrap();

                //cfg_g.add_edge(current_block, then_block_index, ());
                //cfg_g.add_edge(current_block, else_block_index, ());

                //let current = cfg_g.node_weight(current_block).unwrap();
                let current = blocks.get(&current_block).unwrap();
                let r = current.value0(condition_index).unwrap();

                let then_block = blocks
                    .get(&then_block_index)
                    .unwrap()
                    .block
                    .as_ref()
                    .unwrap();
                //let then_block = cfg_g
                //.node_weight(then_block_index)
                //.unwrap()
                //.block
                //.as_ref()
                //.unwrap();
                let else_block = blocks
                    .get(&else_block_index)
                    .unwrap()
                    .block
                    .as_ref()
                    .unwrap();
                //let else_block = cfg_g
                //.node_weight(else_block_index)
                //.unwrap()
                //.block
                //.as_ref()
                //.unwrap();
                let op = cf::cond_br(
                    context,
                    r,
                    &then_block,
                    &else_block,
                    &[], //then_args,
                    &[], //else_args,
                    location,
                );
                //let current = cfg_g.node_weight_mut(current_block).unwrap();
                let current = blocks.get_mut(&current_block).unwrap();
                Ok(current.push(op))
            }

            IRKind::Ret(args) => {
                let current_block = stack.last().unwrap().clone();

                let mut rs = vec![];
                for expr in args {
                    let mut index =
                        expr.lower_mlir(context, place, d, types, blocks, stack, b, link)?;
                    let (_ast_ty, mem) = types.lookup_type(index).unwrap();
                    if mem.requires_deref() {
                        // if it's in memory, we need to copy to return
                        let target = DerefTarget::Offset(0);
                        index = op::emit_deref(index, location, target, d, types, blocks, stack)?;
                    }

                    rs.push(index);
                }
                let rs = rs
                    .into_iter()
                    .map(|index| blocks.values_in_scope(index)[0])
                    .collect::<Vec<_>>();
                let op = func::r#return(&rs, location);
                //let current = cfg_g.node_weight_mut(current_block).unwrap();
                let current = blocks.get_mut(&current_block).unwrap();
                return Ok(current.push(op));
            }

            IRKind::Label(_label, _index, _args) => {
                // this should have been removed by now, when converted to blocks
                unreachable!()
            }

            IRKind::Jump(label, args) => {
                let current_block = stack.last().unwrap().clone();
                let span = self.span.clone();
                if let Some(block_index) = blocks.block_index(&label) {
                    let mut arg_index = vec![];
                    for expr in args {
                        let index =
                            expr.lower_mlir(context, place, d, types, blocks, stack, b, link)?;
                        arg_index.push(index);
                    }

                    //let current = cfg_g.node_weight(current_block).unwrap();
                    let current = blocks.get(&current_block).unwrap();

                    let arg_values = arg_index
                        .into_iter()
                        .map(|index| current.values(index))
                        .flatten()
                        .collect::<Vec<_>>();

                    let target_block = blocks.get(&block_index).unwrap().block.as_ref().unwrap();
                    //let target_block = cfg_g
                    //.node_weight(block_index)
                    //.unwrap()
                    //.block
                    //.as_ref()
                    //.unwrap();

                    let op = cf::br(target_block, &arg_values, location);
                    //let current = cfg_g.node_weight_mut(current_block).unwrap();
                    let current = blocks.get_mut(&current_block).unwrap();
                    Ok(current.push(op))
                } else {
                    d.push_diagnostic(ir::error(
                        &format!(
                            "Missing block: {}",
                            //label.offset(),
                            b.strings.resolve(&label)
                        ),
                        span,
                    ));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            IRKind::Get(place_id, _select) => {
                let current_block = stack.last().unwrap().clone();
                let span = self.span.clone();
                let p = place.get_place(place_id);
                if let Some(sym_index) = blocks.name_in_scope(current_block, p.name) {
                    if blocks.block_is_static(sym_index.block()) {
                        let (ast_ty, mem) = types.lookup_type(sym_index).unwrap();

                        if mem.requires_deref() {
                            let lower_ty = op::from_type(context, &ast_ty);
                            let memref_ty = MemRefType::new(lower_ty, &[], None, None);
                            // TODO: FIXME
                            let static_name = b.strings.resolve(&p.name);
                            //let static_name = b.strings.resolve(
                            //&cfg.static_names.get(&sym_index).cloned().unwrap_or(name),
                            //);
                            let op = memref::get_global(context, &static_name, memref_ty, location);
                            //let current = cfg_g.node_weight_mut(current_block).unwrap();
                            let current = blocks.get_mut(&current_block).unwrap();
                            let addr_index = current.push(op);
                            let r_addr = current.value0(addr_index).unwrap();
                            let op = memref::load(r_addr, &[], location);
                            let value_index = current.push(op);
                            types.set_type(value_index, ast_ty, VarDefinitionSpace::Reg);
                            return Ok(value_index);
                        }
                    } else {
                        let (ast_ty, mem) = types.lookup_type(sym_index).unwrap();

                        if mem.requires_deref() {
                            let r_addr = blocks.values_in_scope(sym_index)[0];
                            let op = memref::load(r_addr, &[], location);
                            //let current = cfg_g.node_weight_mut(current_block).unwrap();
                            let current = blocks.get_mut(&current_block).unwrap();
                            let value_index = current.push(op);
                            types.set_type(value_index, ast_ty, VarDefinitionSpace::Reg);
                            return Ok(value_index);
                        }
                        return Ok(sym_index);
                    }
                }
                d.push_diagnostic(ir::error(
                    &format!("Get name not found: {:?}", p.name),
                    span,
                ));
                Err(Error::new(ParseError::Invalid))
            }

            IRKind::Call(key, args) => {
                // function to call
                let current_block = stack.last().unwrap().clone();
                let name = b.strings.resolve(&key);
                let span = self.span.clone();
                let (f, (ty, _mem)) = if let Some(index) = blocks.name_in_scope(current_block, key)
                {
                    if let Some(ty) = types.lookup_type(index) {
                        (FlatSymbolRefAttribute::new(context, name), ty)
                    } else {
                        d.push_diagnostic(ir::error(
                            &format!("Type not found: {}, {:?}", name, index),
                            span,
                        ));
                        return Err(Error::new(ParseError::Invalid));
                    }
                } else {
                    d.push_diagnostic(ir::error(
                        &format!("IR call name not found: {}", name),
                        span,
                    ));
                    return Err(Error::new(ParseError::Invalid));
                };

                if let AstType::Func(_func_arg_types, ret) = &ty {
                    let ret_type = op::from_type(context, &ret);
                    // handle call arguments
                    let mut indices = vec![];

                    // lower call args
                    for a in args {
                        let index =
                            a.lower_mlir(context, place, d, types, blocks, stack, b, link)?;
                        indices.push(index);
                    }

                    let call_args = indices
                        .into_iter()
                        .map(|index| blocks.values_in_scope(index)[0])
                        .collect::<Vec<_>>();

                    let op = func::call(
                        context,
                        f,
                        call_args.as_slice(),
                        &[ret_type.clone()],
                        location,
                    );
                    //let current = cfg_g.node_weight_mut(current_block).unwrap();
                    let current = blocks.get_mut(&current_block).unwrap();

                    let index = current.push(op);
                    types.set_type(index, *ret.clone(), VarDefinitionSpace::Reg);
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
                //let current = cfg_g.node_weight_mut(current_block).unwrap();
                let current = blocks.blocks.get_mut(&current_block).unwrap();
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
                types.set_type(index, ast_ty, VarDefinitionSpace::Reg);
                Ok(index)
            }

            IRKind::Builtin(bi, mut args) => {
                let arity = bi.arity();
                assert_eq!(arity, args.len());
                let current_block = stack.last().unwrap().clone();
                match bi {
                    Builtin::Import => {
                        let arg = args.pop().unwrap();
                        if let Some(s) = arg.try_string() {
                            link.add_library(&s);
                        } else {
                            d.push_diagnostic(ir::error("Expected string", self.span));
                        }
                        op::emit_noop(context, location, current_block, blocks)
                    }
                    Builtin::Assert => {
                        let arg = args.pop().unwrap();
                        let index =
                            arg.lower_mlir(context, place, d, types, blocks, stack, b, link)?;
                        let msg = "assert";
                        let msg = d.emit_string(ir::error(msg, self.span));
                        //let msg = format!("assert at {}", location.to_string());
                        //let current = cfg_g.node_weight_mut(current_block).unwrap();
                        let current = blocks.get_mut(&current_block).unwrap();
                        let r = current.value0(index).unwrap();
                        let op = cf::assert(context, r, &msg, location);
                        Ok(current.push(op))
                    }
                    Builtin::Print => {
                        let arg = args.pop().unwrap();
                        // eval expr
                        let mut index =
                            arg.lower_mlir(context, place, d, types, blocks, stack, b, link)?;
                        let (ast_ty, mem) = types.lookup_type(index).unwrap();

                        // deref
                        if mem.requires_deref() {
                            let target = DerefTarget::Offset(0);
                            index =
                                op::emit_deref(index, location, target, d, types, blocks, stack)?;
                        }

                        //let r = values_in_scope(blocks, cfg_g, index)[0];
                        let data = blocks.get(&index.block()).unwrap();
                        let r = data.value0(index).unwrap();
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

                        //let current = cfg_g.node_weight_mut(current_block).unwrap();
                        let current = blocks.get_mut(&current_block).unwrap();
                        Ok(current.push(op))
                    } //_ => unreachable!("{:?}", bi),
                }
            }

            IRKind::Op1(op, a) => {
                use crate::ast::UnaryOperation;
                let index = a.lower_mlir(context, place, d, types, blocks, stack, b, link)?;
                let current_block = stack.last().unwrap().clone();
                //let current = cfg_g.node_weight_mut(current_block).unwrap();
                let current = blocks.get_mut(&current_block).unwrap();
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
                            types.set_type(index, AstType::Int, VarDefinitionSpace::Reg);
                            Ok(index)
                        } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                            // arith has an op for negation
                            let r_rhs = current.value0(index).unwrap();
                            let index = current.push(arith::negf(r_rhs, location));
                            types.set_type(index, AstType::Float, VarDefinitionSpace::Reg);
                            Ok(index)
                        } else {
                            unimplemented!()
                        }
                    }
                }
            }

            IRKind::Op2(op, x, y) => op::emit_binop(
                context, place, op, *x, *y, location, d, types, blocks, stack, b, link,
            ),

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
