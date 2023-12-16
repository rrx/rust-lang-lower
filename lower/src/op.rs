use crate::ast::{
    Argument, AssignTarget, Ast, AstNode, AstType, BinaryOperation, Builtin, Extra, Literal,
    Parameter, ParameterNode,
};
use crate::lower::from_type;
use melior::ir::operation::OperationPrintingFlags;
//use crate::scope::LayerIndex;
use crate::default_pass_manager;

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
        //ods, scf,
    },
    ir::{
        attribute::{
            DenseElementsAttribute, FlatSymbolRefAttribute, FloatAttribute, IntegerAttribute,
            StringAttribute, TypeAttribute,
        },
        r#type::{FunctionType, IntegerType, MemRefType, RankedTensorType},
        Attribute, Block, Identifier, Module, Operation, Region, Type, TypeLike, Value, ValueLike,
    },
    Context, ExecutionEngine,
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

pub fn build_binop<'c>(
    context: &'c Context,
    op: BinaryOperation,
    a: Value<'c, '_>,
    b: Value<'c, '_>,
    location: Location<'c>,
) -> Operation<'c> {
    let ty = a.r#type();
    assert_eq!(ty, b.r#type());

    match op {
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
                arith::cmpi(context, arith::CmpiPredicate::Uge, a, b, location)
            } else if ty.is_integer() {
                // signed
                arith::cmpi(context, arith::CmpiPredicate::Sge, a, b, location)
            } else {
                unimplemented!();
            }
        }
        BinaryOperation::GT => {
            if ty.is_index() {
                // unsigned
                arith::cmpi(context, arith::CmpiPredicate::Ugt, a, b, location)
            } else if ty.is_integer() {
                // signed
                arith::cmpi(context, arith::CmpiPredicate::Sgt, a, b, location)
            } else {
                unimplemented!();
            }
        }
        BinaryOperation::NE => {
            if ty.is_index() || ty.is_integer() {
                arith::cmpi(context, arith::CmpiPredicate::Ne, a, b, location)
            } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                // ordered comparison
                arith::cmpf(context, arith::CmpfPredicate::One, a, b, location)
            } else {
                unimplemented!()
            }
        }
        BinaryOperation::EQ => {
            if ty.is_index() || ty.is_integer() {
                arith::cmpi(context, arith::CmpiPredicate::Eq, a, b, location)
            } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                // ordered comparison
                arith::cmpf(context, arith::CmpfPredicate::Oeq, a, b, location)
            } else {
                unimplemented!()
            }
        } //_ => unimplemented!("{:?}", op)
    }
}
