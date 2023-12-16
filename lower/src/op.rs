use crate::ast::{
    Argument, AssignTarget, Ast, AstNode, AstType, Builtin, Extra, Literal, Parameter,
    ParameterNode,
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
            //DenseElementsAttribute,
            FlatSymbolRefAttribute,
            FloatAttribute,
            IntegerAttribute,
            StringAttribute,
            TypeAttribute,
        },
        r#type::{
            FunctionType,
            IntegerType,
            MemRefType,
            //RankedTensorType,
        },
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
