use crate::ast::{
    //BinOpNode,
    BinaryOperation,
    //Argument, AssignTarget, Ast, AstNode,
    //Literal,
    //Parameter, ParameterNode,
    DerefTarget,
    //Terminator,
    VarDefinitionSpace,
    //Builtin,
};
//use crate::cfg::{values_in_scope};
//use crate::ir;
use crate::ir::{
    //IRGraph,
    IRKind,
    IRNode,
};
use crate::{
    Ast, AstNode, AstType, CFGBlocks, Diagnostics, Extra, IRPlaceTable, LinkOptions, Literal,
    NodeBuilder, NodeIndex, ParseError, PlaceId, StringKey, SymIndex, TypeBuilder,
};

use anyhow::Error;
use anyhow::Result;
use codespan_reporting::diagnostic::Diagnostic;
use melior::ir::Location;
use melior::{
    dialect::{
        arith,
        //cf,
        func,
        //llvm,
        memref,
        //ods, scf,
    },
    ir::{
        attribute::{
            DenseElementsAttribute,
            //FlatSymbolRefAttribute,
            FloatAttribute,
            IntegerAttribute,
            StringAttribute,
            TypeAttribute,
        },
        r#type::{FunctionType, IntegerType, MemRefType, RankedTensorType},
        Attribute,
        //Block,
        Identifier,
        //Module,
        Operation,
        Region,
        Type,
        TypeLike,
        Value,
        ValueLike,
    },
    Context,
};

pub fn build_float_op<'c>(
    context: &'c Context,
    value: f64,
    location: Location<'c>,
) -> Operation<'c> {
    arith::constant(
        context,
        FloatAttribute::new(context, value, Type::float64(context)).into(),
        location,
    )
}

pub fn build_int_op<'c>(context: &'c Context, value: i64, location: Location<'c>) -> Operation<'c> {
    let ty = IntegerType::new(context, 64);
    arith::constant(
        context,
        IntegerAttribute::new(value, ty.into()).into(),
        location,
    )
}

pub fn build_index_op<'c>(
    context: &'c Context,
    value: i64,
    location: Location<'c>,
) -> Operation<'c> {
    let ty = Type::index(context);
    arith::constant(
        context,
        IntegerAttribute::new(value, ty.into()).into(),
        location,
    )
}

pub fn build_bool_op<'c>(
    context: &'c Context,
    value: bool,
    location: Location<'c>,
) -> Operation<'c> {
    let bool_type = IntegerType::new(context, 1);
    arith::constant(
        context,
        IntegerAttribute::new(if value { 1 } else { 0 }, bool_type.into()).into(),
        location,
    )
}

pub fn build_static<'c>(
    context: &'c Context,
    name: &str,
    ty: Type<'c>,
    value: Attribute<'c>,
    constant: bool,
    location: Location<'c>,
) -> Operation<'c> {
    let integer_type = IntegerType::new(context, 64).into();
    let attribute =
        DenseElementsAttribute::new(RankedTensorType::new(&[], ty, None).into(), &[value]).unwrap();
    let alignment = IntegerAttribute::new(8, integer_type);
    let memspace = IntegerAttribute::new(0, integer_type).into();

    memref::global(
        context,
        name,
        Some("private"),
        MemRefType::new(ty, &[], None, Some(memspace)),
        Some(attribute.into()),
        constant,
        Some(alignment),
        location,
    )
}

pub fn build_reserved<'c>(
    context: &'c Context,
    name: &str,
    location: Location<'c>,
) -> Option<(Operation<'c>, AstType)> {
    match name {
        "True" => {
            let op = build_bool_op(context, true, location);
            Some((op, AstType::Bool))
        }
        "False" => {
            let op = build_bool_op(context, false, location);
            Some((op, AstType::Bool))
        }
        _ => None,
    }
}

pub fn emit_binop<'c, E: Extra>(
    context: &'c Context,
    place: &IRPlaceTable,
    op: BinaryOperation,
    x: IRNode,
    y: IRNode,
    location: Location<'c>,
    d: &mut Diagnostics,
    types: &mut TypeBuilder,
    blocks: &mut CFGBlocks<'c>,
    stack: &mut Vec<NodeIndex>,
    //g: &mut IRGraph,
    //cfg_g: &mut CFGGraph<'c>,
    b: &mut NodeBuilder<E>,
    link: &mut LinkOptions,
) -> Result<SymIndex> {
    let fx = format!("x: {:?}", x);
    let fy = format!("y: {:?}", y);
    let x_extra = E::span(x.get_span());
    let y_extra = E::span(y.get_span());
    let x_location = x.location(context, d);
    let y_location = x.location(context, d);
    let index_x = x.lower_mlir(context, place, d, types, blocks, stack, b, link)?;
    let index_y = y.lower_mlir(context, place, d, types, blocks, stack, b, link)?;

    //cfg.save_graph("out.dot", g);
    //println!("ix: {:?}, {}", index_x, fx);
    //println!("iy: {:?}, {}", index_y, fy);

    let (_ty_x, mem_x) = types
        .lookup_type(index_x)
        .expect(&format!("missing type for {:?}, {}", index_x, fx));

    let (_ty_y, mem_y) = types
        .lookup_type(index_y)
        .expect(&format!("missing type for {:?}, {}", index_y, fy));

    //println!("ty_x: {:?}", (ty_x, mem_x));
    //println!("ty_y: {:?}", (ty_y, mem_y));

    let current_block = stack.last().unwrap().clone();
    //println!("{:?}", op);

    let index_x = if mem_x.requires_deref() {
        let target = DerefTarget::Offset(0);
        let index = emit_deref(index_x, x_location, target, d, types, blocks, stack)?;
        index
    } else {
        index_x
    };

    let index_y = if mem_y.requires_deref() {
        let target = DerefTarget::Offset(0);
        let index = emit_deref(index_y, y_location, target, d, types, blocks, stack)?;
        index
    } else {
        index_y
    };

    //let current = cfg_g.node_weight_mut(current_block).unwrap();
    //println!("{:?}", current);

    // types must be the same for binary operation, no implicit casting yet
    //let data = blocks.get(&index_x.block()).unwrap();
    //let a = data.values(index_x)[0];
    let a = blocks.values_in_scope(index_x)[0];
    let b = blocks.values_in_scope(index_y)[0];
    //let data = blocks.get(&index_y.block()).unwrap();
    //let b = data.values(index_y)[0];
    let (op, ast_ty) = build_binop(context, op, a, &x_extra, b, &y_extra, location, d)?;
    //let current = cfg_g.node_weight_mut(current_block).unwrap();
    let current = blocks.get_mut(&current_block).unwrap();
    let index = current.push(op);
    types.set_type(index, ast_ty, VarDefinitionSpace::Reg);
    Ok(index)
}

pub fn emit_deref<'c>(
    index: SymIndex,
    location: Location<'c>,
    _target: DerefTarget,
    _d: &mut Diagnostics,
    types: &mut TypeBuilder,
    blocks: &mut CFGBlocks<'c>,
    stack: &mut Vec<NodeIndex>,
    //cfg_g: &mut CFGGraph<'c>,
) -> Result<SymIndex> {
    // we are expecting a memref here
    let current_block = stack.last().unwrap().clone();
    let (ty, mem) = types.lookup_type(index).unwrap();

    // ensure proper type
    if mem.requires_deref() {
        //if let AstType::Ptr(ast_ty) = &ty {
        //let location = extra.location(context, d);
        //let r = values_in_scope(blocks, cfg_g, index)[0];
        let data = blocks.get(&index.block()).unwrap();
        let r = data.values(index)[0];
        let op = memref::load(r, &[], location);
        //let current = cfg_g.node_weight_mut(current_block).unwrap();
        let current = blocks.get_mut(&current_block).unwrap();
        let index = current.push(op);
        types.set_type(index, ty, mem);
        Ok(index)
    } else {
        Ok(index)
    }
    //} else {
    //d.push_diagnostic(extra.error(&format!("Trying to dereference a non-pointer: {:?}", ty)));
    //Err(Error::new(ParseError::Invalid))
    //}
}

pub fn emit_set_alloca<'c, E: Extra>(
    context: &'c Context,
    place: &IRPlaceTable,
    sym_index: SymIndex,
    name: StringKey,
    expr: IRNode,
    location: Location<'c>,
    block_index: NodeIndex,
    types: &mut TypeBuilder,
    blocks: &mut CFGBlocks<'c>,
    stack: &mut Vec<NodeIndex>,
    //g: &mut IRGraph,
    //cfg_g: &mut CFGGraph<'c>,
    d: &mut Diagnostics,
    b: &mut NodeBuilder<E>,
    link: &mut LinkOptions,
) -> Result<SymIndex> {
    log::debug!("assign alloca: {}", b.strings.resolve(&name));
    expr.dump(&place, b, 0);

    let rhs_index = expr.lower_mlir(context, place, d, types, blocks, stack, b, link)?;
    //let ty = IntegerType::new(context, 64);
    //let memref_ty = MemRefType::new(ty.into(), &[], None, None);
    //let op = memref::alloca(context, memref_ty, &[], &[], None, location);

    // name the pointer
    //let ptr_index = current.push_with_name(op, name);
    //let ast_ty = cfg.lookup_type(rhs_index).unwrap().to_ptr();
    //let ptr_ty = AstType::Ptr(ast_ty.into());
    //cfg.set_type(ptr_index, ast_ty);
    println!("ty_lhs: {:?}", types.lookup_type(sym_index));
    println!("ty_rhs: {:?}", types.lookup_type(rhs_index));
    println!("rhs: {:?}", (rhs_index));
    println!("lhs: {:?}", (sym_index));
    println!("rhs: {:?}", (rhs_index));
    blocks.dump_scope(block_index, b);
    //blocks.save_graph("out.dot", b);

    let is_symbol_static = sym_index.block() == blocks.root();

    let addr_index = if is_symbol_static {
        let (lhs_ty, _lhs_mem) = types.lookup_type(sym_index).unwrap();
        let (_rhs_ty, _rhs_mem) = types.lookup_type(rhs_index).unwrap();

        let lower_ty = from_type(context, &lhs_ty);
        let memref_ty = MemRefType::new(lower_ty, &[], None, None);
        let static_name = b.strings.resolve(&name);
        // TODO: FIXME
        //let static_name = b
        //.strings
        //.resolve(&cfg.static_names.get(&sym_index).cloned().unwrap_or(name));
        let op = memref::get_global(context, &static_name, memref_ty, location);
        let current = blocks.get_mut(&block_index).unwrap();
        let addr_index = current.push(op);
        addr_index
        //let r_addr = current.value0(addr_index).unwrap();
        //r_addr
    } else {
        sym_index
        //values_in_scope(cfg_g, sym_index)[0]
    };

    let r_value = blocks.values_in_scope(rhs_index)[0];
    let r_addr = blocks.values_in_scope(addr_index)[0];

    // emit store
    // store(value, memref)
    let op = memref::store(r_value, r_addr, &[], location);
    //let current = cfg_g.node_weight_mut(block_index).unwrap();
    let current = blocks.get_mut(&block_index).unwrap();
    let _index = current.push(op);
    println!("current: {:?}", current);
    Ok(sym_index)
}

pub fn emit_noop<'c>(
    context: &'c Context,
    location: Location<'c>,
    block_index: NodeIndex,
    blocks: &mut CFGBlocks<'c>,
) -> Result<SymIndex> {
    let op = build_bool_op(context, false, location);
    let current = blocks.blocks.get_mut(&block_index).unwrap();
    Ok(current.push(op))
}

pub fn emit_set_function<'c, E: Extra>(
    context: &'c Context,
    place: &IRPlaceTable,
    sym_index: SymIndex,
    expr: IRNode,
    current_block: NodeIndex,
    types: &mut TypeBuilder,
    blocks: &mut CFGBlocks<'c>,
    stack: &mut Vec<NodeIndex>,
    d: &mut Diagnostics,
    b: &mut NodeBuilder<E>,
    link: &mut LinkOptions,
) -> Result<SymIndex> {
    match expr.kind {
        IRKind::Func(func_blocks, _ast_ty) => {
            let mut block_seq = vec![];

            // create blocks, so they can be referenced when lowering
            for (i, block) in func_blocks.into_iter().enumerate() {
                let block_index = blocks.add_block_ir(
                    context,
                    block.index,
                    block.name,
                    &block.params,
                    types,
                    d,
                    //cfg_g,
                );
                if 0 == i {
                    //cfg_g.add_edge(current_block, block_index, ());
                }
                block_seq.push((block, block_index));
            }

            // lower to mlir
            let mut block_indicies = vec![];
            for (block, block_index) in block_seq.into_iter() {
                block_indicies.push(block_index);

                /*
                let term = block.terminator().unwrap();
                match term {
                    Terminator::Jump(label) => {
                        let target_block = blocks.block_index(&label).unwrap();
                    }
                    Terminator::Branch(a, b) => {
                        for key in &[a, b] {
                            let target_block = blocks.block_index(&key).unwrap();
                        }
                    }
                    Terminator::Return => (),
                }
                */

                for c in block.children.into_iter() {
                    stack.push(block_index);
                    if let Ok(_index) =
                        c.lower_mlir(context, place, d, types, blocks, stack, b, link)
                    {
                        stack.pop();
                    } else {
                        stack.pop();
                        return Err(Error::new(ParseError::Invalid));
                    }
                }
            }

            // build region and add it to the declared function
            for block_index in block_indicies {
                let block = blocks.take_block(block_index);
                let current = blocks.get_mut(&current_block).unwrap();
                let op = current.op_ref(sym_index);
                op.region(0).unwrap().append_block(block);
            }

            let current = blocks.get_mut(&current_block).unwrap();
            let op = current.op_ref(sym_index);
            op.set_attribute("llvm.emit_c_interface", &Attribute::unit(context));

            Ok(sym_index)
        }
        _ => unreachable!(),
    }
}

pub fn emit_set_static<'c, E: Extra>(
    context: &'c Context,
    sym_index: SymIndex,
    name: StringKey,
    expr: IRNode,
    //location: Location<'c>,
    block_index: NodeIndex,
    blocks: &mut CFGBlocks<'c>,
    //cfg_g: &mut CFGGraph<'c>,
    _d: &mut Diagnostics,
    b: &mut NodeBuilder<E>,
) -> Result<SymIndex> {
    let is_symbol_static = sym_index.block() == blocks.root();
    assert!(is_symbol_static);
    let is_current_static = block_index == blocks.root();
    // TODO: this needs to be cleaned up, only works for setting initial values on static variables
    assert!(is_current_static);

    // we can emit a static variable in either static context, or in a function
    // TODO: consider moving this logic into a transformation

    // symbol in static context
    let global_name = if is_current_static {
        // emitting in static context
        b.strings.resolve(&name).clone()
    } else {
        // emitting in non-static context (local static var)
        // we create a unique global name to prevent conflict
        // and then we add ops to provide a local reference to the global name
        let base = b.strings.resolve(&name).clone();
        let name = b.unique_static_name();
        let name = format!("{}{}", base, name).clone();
        name
    };

    // evaluate expr at compile time
    let (value, ast_ty) = build_static_attribute(context, expr);
    let ty = from_type(context, &ast_ty);
    let attribute =
        DenseElementsAttribute::new(RankedTensorType::new(&[], ty, None).into(), &[value]).unwrap();

    let current = blocks.blocks.get_mut(&block_index).unwrap();
    let op = current.op_ref(sym_index);
    op.set_attribute("initial_value", &attribute.into());
    if !is_current_static {
        // STATIC VARIABLE IN FUNCTION CONTEXT
        // TODO: FIXME
        //cfg.static_names
        //.insert(sym_index, b.strings.intern(global_name.clone()));
    }
    Ok(sym_index)
}

pub fn emit_declare_function<'c, E: Extra>(
    context: &'c Context,
    place_id: PlaceId,
    key: StringKey,
    ast_ty: AstType,
    location: Location<'c>,
    block_index: NodeIndex,
    types: &mut TypeBuilder,
    blocks: &mut CFGBlocks<'c>,
    //cfg_g: &mut CFGGraph<'c>,
    b: &NodeBuilder<E>,
) -> Result<SymIndex> {
    if let AstType::Func(params, ast_ret_type) = ast_ty.clone() {
        let mut type_list = vec![];
        let mut ast_types = vec![];
        //let ast_ret_type = def.return_type;

        let attributes = vec![(
            Identifier::new(context, "sym_visibility"),
            StringAttribute::new(context, "private").into(),
        )];

        for ty in params {
            type_list.push(from_type(context, &ty));
            ast_types.push(ty.clone());
        }

        let region = Region::new();

        let ret_type = if let AstType::Unit = *ast_ret_type {
            vec![]
        } else {
            vec![from_type(context, &ast_ret_type)]
        };

        let func_type = FunctionType::new(context, &type_list, &ret_type);
        let op = func::func(
            context,
            StringAttribute::new(context, b.strings.resolve(&key)),
            TypeAttribute::new(func_type.into()),
            region,
            &attributes,
            location,
        );

        let function_block = blocks.blocks.get_mut(&block_index).unwrap();
        let index = function_block.push_with_place(op, place_id);
        function_block.add_symbol(key, index);
        types.set_type(index, ast_ty, VarDefinitionSpace::Static);

        //if let Some(entry_block) = entry_block {
        //let data = g.node_weight_mut(entry_block).unwrap();
        //data.set_parent_symbol(func_index);
        //}

        Ok(index)
    } else {
        unreachable!()
    }
}

pub fn emit_declare_static<'c, E: Extra>(
    context: &'c Context,
    place_id: PlaceId,
    name: StringKey,
    ast_ty: AstType,
    location: Location<'c>,
    block_index: NodeIndex,
    types: &mut TypeBuilder,
    blocks: &mut CFGBlocks<'c>,
    //cfg_g: &mut CFGGraph<'c>,
    b: &NodeBuilder<E>,
) -> Result<SymIndex> {
    // STATIC/GLOBAL VARIABLE
    let integer_type = IntegerType::new(context, 64).into();
    let ty = from_type(context, &ast_ty);
    let alignment = IntegerAttribute::new(8, integer_type);
    let memspace = IntegerAttribute::new(0, integer_type).into();
    let constant = false;

    let op = memref::global(
        context,
        b.strings.resolve(&name),
        Some("private"),
        MemRefType::new(ty, &[], None, Some(memspace)),
        // initial value is not set
        None,
        constant,
        Some(alignment),
        location,
    );

    let current = blocks.blocks.get_mut(&block_index).unwrap();
    let index = current.push_with_place(op, place_id);
    current.add_symbol(name, index);
    types.set_type(index, ast_ty, VarDefinitionSpace::Static);
    Ok(index)
}

pub fn emit_static<'c, E: Extra>(
    context: &'c Context,
    global_name: String,
    expr: AstNode<E>,
    location: Location<'c>,
) -> (Operation<'c>, AstType) {
    // evaluate expr at compile time
    let (ast_ty, op) = match expr.node {
        Ast::Literal(Literal::Bool(x)) => {
            let ast_ty = AstType::Bool;
            let ty = from_type(context, &ast_ty);
            let v = if x { 1 } else { 0 };
            let value = IntegerAttribute::new(v, ty).into();
            let op = build_static(context, &global_name, ty, value, false, location);
            (ast_ty, op)
        }

        Ast::Literal(Literal::Int(x)) => {
            let ast_ty = AstType::Int;
            let ty = from_type(context, &ast_ty);
            let value = IntegerAttribute::new(x, ty).into();
            let op = build_static(context, &global_name, ty, value, false, location);
            (ast_ty, op)
        }

        Ast::Literal(Literal::Index(x)) => {
            let ast_ty = AstType::Int;
            let ty = from_type(context, &ast_ty);
            let value = IntegerAttribute::new(x as i64, ty).into();
            let op = build_static(context, &global_name, ty, value, false, location);
            (ast_ty, op)
        }

        Ast::Literal(Literal::Float(x)) => {
            let ast_ty = AstType::Float;
            let ty = from_type(context, &ast_ty);
            let value = FloatAttribute::new(context, x, ty).into();
            let op = build_static(context, &global_name, ty, value, false, location);
            (ast_ty, op)
        }

        _ => unreachable!("{:?}", expr.node),
    };
    (op, ast_ty)
}

pub fn build_static_attribute<'c>(context: &'c Context, expr: IRNode) -> (Attribute<'c>, AstType) {
    // evaluate expr at compile time
    match expr.kind {
        IRKind::Literal(Literal::Bool(x)) => {
            let ast_ty = AstType::Bool;
            let ty = from_type(context, &ast_ty);
            let v = if x { 1 } else { 0 };
            let value = IntegerAttribute::new(v, ty).into();
            (value, ast_ty)
        }

        IRKind::Literal(Literal::Int(x)) => {
            let ast_ty = AstType::Int;
            let ty = from_type(context, &ast_ty);
            let value = IntegerAttribute::new(x, ty).into();
            (value, ast_ty)
        }

        IRKind::Literal(Literal::Index(x)) => {
            let ast_ty = AstType::Int;
            let ty = from_type(context, &ast_ty);
            let value = IntegerAttribute::new(x as i64, ty).into();
            (value, ast_ty)
        }

        IRKind::Literal(Literal::Float(x)) => {
            let ast_ty = AstType::Float;
            let ty = from_type(context, &ast_ty);
            let value = FloatAttribute::new(context, x, ty).into();
            (value, ast_ty)
        }
        _ => unreachable!("{:?}", expr.kind),
    }
}

pub fn emit_static_ir<'c>(
    context: &'c Context,
    global_name: String,
    expr: IRNode,
    location: Location<'c>,
) -> (Operation<'c>, AstType) {
    // evaluate expr at compile time
    let (ast_ty, op) = match expr.kind {
        IRKind::Literal(Literal::Bool(x)) => {
            let ast_ty = AstType::Bool;
            let ty = from_type(context, &ast_ty);
            let v = if x { 1 } else { 0 };
            let value = IntegerAttribute::new(v, ty).into();
            let op = build_static(context, &global_name, ty, value, false, location);
            (ast_ty, op)
        }

        IRKind::Literal(Literal::Int(x)) => {
            let ast_ty = AstType::Int;
            let ty = from_type(context, &ast_ty);
            let value = IntegerAttribute::new(x, ty).into();
            let op = build_static(context, &global_name, ty, value, false, location);
            (ast_ty, op)
        }

        IRKind::Literal(Literal::Index(x)) => {
            let ast_ty = AstType::Int;
            let ty = from_type(context, &ast_ty);
            let value = IntegerAttribute::new(x as i64, ty).into();
            let op = build_static(context, &global_name, ty, value, false, location);
            (ast_ty, op)
        }

        IRKind::Literal(Literal::Float(x)) => {
            let ast_ty = AstType::Float;
            let ty = from_type(context, &ast_ty);
            let value = FloatAttribute::new(context, x, ty).into();
            let op = build_static(context, &global_name, ty, value, false, location);
            (ast_ty, op)
        }

        _ => unreachable!("{:?}", expr.kind),
    };
    (op, ast_ty)
}

pub fn build_binop<'c, E: Extra>(
    context: &'c Context,
    op: BinaryOperation,
    a: Value<'c, '_>,
    a_extra: &E,
    b: Value<'c, '_>,
    b_extra: &E,
    location: Location<'c>,
    d: &mut Diagnostics,
) -> Result<(Operation<'c>, AstType)> {
    let ty = a.r#type();
    assert_eq!(ty, b.r#type());

    let (op, ast_ty) = match op {
        BinaryOperation::Divide => {
            if ty.is_index() {
                // index type is unsigned
                (arith::divui(a, b, location), AstType::Index)
            } else if ty.is_integer() {
                // we assume all integers are signed for now
                (arith::divsi(a, b, location), AstType::Int)
            } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                (arith::divf(a, b, location), AstType::Float)
            } else {
                d.push_diagnostic(a_extra.error(&format!("Invalid Type")));
                return Err(Error::new(ParseError::Invalid));
            }
        }
        BinaryOperation::Multiply => {
            if ty.is_index() {
                (arith::muli(a, b, location), AstType::Index)
            } else if ty.is_integer() {
                (arith::muli(a, b, location), AstType::Int)
            } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                (arith::mulf(a, b, location), AstType::Float)
            } else {
                d.push_diagnostic(a_extra.error(&format!("Invalid Type")));
                return Err(Error::new(ParseError::Invalid));
            }
        }
        BinaryOperation::Add => {
            if ty.is_index() {
                (arith::addi(a, b, location), AstType::Index)
            } else if ty.is_integer() {
                (arith::addi(a, b, location), AstType::Int)
            } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                (arith::addf(a, b, location), AstType::Float)
            } else {
                d.push_diagnostic(a_extra.error(&format!("Invalid Type")));
                return Err(Error::new(ParseError::Invalid));
            }
        }
        BinaryOperation::Subtract => {
            if ty.is_index() {
                (arith::subi(a, b, location), AstType::Index)
            } else if ty.is_integer() {
                (arith::subi(a, b, location), AstType::Int)
            } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                (arith::subf(a, b, location), AstType::Float)
            } else {
                d.push_diagnostic(
                    Diagnostic::error()
                        .with_labels(vec![
                            a_extra.primary(&format!("Type {:?}", a.r#type())),
                            b_extra.secondary(&format!("Type: {:?}", b.r#type())),
                        ])
                        .with_message("Type Mispatch"),
                );

                return Err(Error::new(ParseError::Invalid));
            }
        }
        BinaryOperation::GTE => {
            if ty.is_index() {
                // unsigned
                (
                    arith::cmpi(context, arith::CmpiPredicate::Uge, a, b, location),
                    AstType::Bool,
                )
            } else if ty.is_integer() {
                // signed
                (
                    arith::cmpi(context, arith::CmpiPredicate::Sge, a, b, location),
                    AstType::Bool,
                )
            } else {
                d.push_diagnostic(a_extra.error(&format!("Invalid Type")));
                return Err(Error::new(ParseError::Invalid));
            }
        }
        BinaryOperation::GT => {
            if ty.is_index() {
                // unsigned
                (
                    arith::cmpi(context, arith::CmpiPredicate::Ugt, a, b, location),
                    AstType::Bool,
                )
            } else if ty.is_integer() {
                // signed
                (
                    arith::cmpi(context, arith::CmpiPredicate::Sgt, a, b, location),
                    AstType::Bool,
                )
            } else {
                d.push_diagnostic(a_extra.error(&format!("Invalid Type")));
                return Err(Error::new(ParseError::Invalid));
            }
        }
        BinaryOperation::NE => {
            if ty.is_index() || ty.is_integer() {
                (
                    arith::cmpi(context, arith::CmpiPredicate::Ne, a, b, location),
                    AstType::Bool,
                )
            } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                // ordered comparison
                (
                    arith::cmpf(context, arith::CmpfPredicate::One, a, b, location),
                    AstType::Bool,
                )
            } else {
                d.push_diagnostic(a_extra.error(&format!("Invalid Type")));
                return Err(Error::new(ParseError::Invalid));
            }
        }
        BinaryOperation::EQ => {
            if ty.is_index() || ty.is_integer() {
                (
                    arith::cmpi(context, arith::CmpiPredicate::Eq, a, b, location),
                    AstType::Bool,
                )
            } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                // ordered comparison
                (
                    arith::cmpf(context, arith::CmpfPredicate::Oeq, a, b, location),
                    AstType::Bool,
                )
            } else {
                d.push_diagnostic(a_extra.error(&format!("Invalid Type")));
                return Err(Error::new(ParseError::Invalid));
            }
        } //_ => unimplemented!("{:?}", op)
    };

    Ok((op, ast_ty))
}

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
