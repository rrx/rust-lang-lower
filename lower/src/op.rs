use crate::ast::{
    //Argument, AssignTarget, Ast, AstNode,
    //Literal,
    //Parameter, ParameterNode,
    BinOpNode,
    BinaryOperation,
    //Builtin,
};
use crate::cfg::{CFGGraph, SymIndex, CFG};
use crate::ir;
use crate::ir::{IRGraph, IRKind, IRNode};
use crate::{
    Ast, AstNode, AstType, Diagnostics, Extra, Literal, NodeBuilder, NodeIndex, ParseError,
    StringKey,
};

use anyhow::Error;
use anyhow::Result;
use codespan_reporting::diagnostic::Diagnostic;
use melior::ir::Location;
use melior::{
    dialect::{
        arith,
        //cf,
        //func,
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
            //StringAttribute, TypeAttribute,
        },
        r#type::{
            //FunctionType,
            IntegerType,
            MemRefType,
            RankedTensorType,
        },
        Attribute,
        //Block, Identifier, Module,
        Operation,
        //Region,
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

pub fn emit_set_alloca<'c, E: Extra>(
    context: &'c Context,
    sym_index: SymIndex,
    name: StringKey,
    expr: IRNode,
    location: Location<'c>,
    block_index: NodeIndex,
    cfg: &mut CFG<'c, E>,
    stack: &mut Vec<NodeIndex>,
    g: &mut IRGraph,
    cfg_g: &mut CFGGraph<'c>,
    d: &mut Diagnostics,
    b: &mut NodeBuilder<E>,
) -> Result<SymIndex> {
    //log::debug!("assign alloca: {}", name);
    let rhs_index = expr.lower_mlir(context, d, cfg, stack, g, cfg_g, b)?;
    //let ty = IntegerType::new(context, 64);
    //let memref_ty = MemRefType::new(ty.into(), &[], None, None);
    //let op = memref::alloca(context, memref_ty, &[], &[], None, location);
    let current = cfg_g.node_weight_mut(block_index).unwrap();

    // name the pointer
    //let ptr_index = current.push_with_name(op, name);
    let ast_ty = cfg.lookup_type(rhs_index).unwrap().to_ptr();
    //let ptr_ty = AstType::Ptr(ast_ty.into());
    //cfg.set_type(ptr_index, ast_ty);

    let r_value = current.value0(rhs_index).unwrap();
    let r_addr = current.value0(sym_index).unwrap();

    // emit store
    let op = memref::store(r_value, r_addr, &[], location);
    let _index = current.push(op);
    Ok(sym_index)
}

pub fn emit_set_static<'c, E: Extra>(
    context: &'c Context,
    sym_index: SymIndex,
    name: StringKey,
    expr: IRNode,
    location: Location<'c>,
    block_index: NodeIndex,
    cfg: &mut CFG<'c, E>,
    cfg_g: &mut CFGGraph<'c>,
    d: &mut Diagnostics,
    b: &mut NodeBuilder<E>,
) -> Result<SymIndex> {
    let is_symbol_static = sym_index.block() == cfg.root();
    assert!(is_symbol_static);
    let is_current_static = block_index == cfg.root();

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

    match expr.kind {
        IRKind::Func(blocks, ast_ty) => {
            unimplemented!();
        }
        _ => {
            // evaluate expr at compile time
            let (value, ast_ty) =
                build_static_attribute(context, global_name.clone(), expr, location);
            let ty = from_type(context, &ast_ty);
            let attribute =
                DenseElementsAttribute::new(RankedTensorType::new(&[], ty, None).into(), &[value])
                    .unwrap();

            let current = cfg_g.node_weight_mut(block_index).unwrap();
            let op = current.op_ref(sym_index);
            op.set_attribute("initial_value", &attribute.into());
            if !is_current_static {
                // STATIC VARIABLE IN FUNCTION CONTEXT
                cfg.static_names
                    .insert(sym_index, b.strings.intern(global_name.clone()));
            }
            Ok(sym_index)
        }
    }
}

pub fn emit_declare_static<'c, E: Extra>(
    context: &'c Context,
    name: StringKey,
    ast_ty: AstType,
    location: Location<'c>,
    block_index: NodeIndex,
    cfg: &mut CFG<'c, E>,
    cfg_g: &mut CFGGraph<'c>,
    b: &NodeBuilder<E>,
) -> Result<SymIndex> {
    // STATIC/GLOBAL VARIABLE
    let integer_type = IntegerType::new(context, 64).into();
    let ty = from_type(context, &ast_ty);
    //let attribute =
    //DenseElementsAttribute::new(RankedTensorType::new(&[], ty, None).into(), &[value]).unwrap();
    let alignment = IntegerAttribute::new(8, integer_type);
    let memspace = IntegerAttribute::new(0, integer_type).into();
    let constant = false;

    let op = memref::global(
        context,
        b.strings.resolve(&name),
        Some("private"),
        MemRefType::new(ty, &[], None, Some(memspace)),
        // initial value is not set
        None, //Some(attribute.into()),
        constant,
        Some(alignment),
        location,
    );

    let current = cfg_g.node_weight_mut(block_index).unwrap();
    let index = current.push_with_name(op, name);
    cfg.set_type(index, ast_ty);
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

pub fn build_static_attribute<'c>(
    context: &'c Context,
    global_name: String,
    expr: IRNode,
    location: Location<'c>,
) -> (Attribute<'c>, AstType) {
    // evaluate expr at compile time
    match expr.kind {
        IRKind::Literal(Literal::Bool(x)) => {
            let ast_ty = AstType::Bool;
            let ty = from_type(context, &ast_ty);
            let v = if x { 1 } else { 0 };
            let value = IntegerAttribute::new(v, ty).into();

            //let op = build_static(context, &global_name, ty, value, false, location);
            (value, ast_ty)
        }

        IRKind::Literal(Literal::Int(x)) => {
            let ast_ty = AstType::Int;
            let ty = from_type(context, &ast_ty);
            let value = IntegerAttribute::new(x, ty).into();
            let op = build_static(context, &global_name, ty, value, false, location);
            (value, ast_ty)
            //(ast_ty, op)
        }

        IRKind::Literal(Literal::Index(x)) => {
            let ast_ty = AstType::Int;
            let ty = from_type(context, &ast_ty);
            let value = IntegerAttribute::new(x as i64, ty).into();
            let op = build_static(context, &global_name, ty, value, false, location);
            (value, ast_ty)
            //(ast_ty, op)
        }

        IRKind::Literal(Literal::Float(x)) => {
            let ast_ty = AstType::Float;
            let ty = from_type(context, &ast_ty);
            let value = FloatAttribute::new(context, x, ty).into();
            let op = build_static(context, &global_name, ty, value, false, location);
            (value, ast_ty)
            //(ast_ty, op)
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
