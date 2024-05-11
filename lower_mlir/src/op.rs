use compile_core::BinaryOperation;
use compile_core::{primary_label, secondary_label, Ast, AstNode, AstType, Literal, Span};
use thiserror::Error;

use anyhow::Error;
use anyhow::Result;
use compile_core::Diagnostic;
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
            //StringAttribute,
            //TypeAttribute,
        },
        r#type::{
            //FunctionType,
            IntegerType,
            MemRefType,
            RankedTensorType,
        },
        Attribute,
        //Block,
        //Identifier,
        //Module,
        Operation,
        //Region,
        Type,
        TypeLike,
        Value,
        ValueLike,
    },
    Context,
};

#[derive(Error, Debug)]
pub enum LowerError {
    #[error("LowerError")]
    Invalid,
}

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

pub fn emit_literal_const<'c>(
    context: &'c Context,
    lit: &Literal,
    location: Location<'c>,
) -> (Operation<'c>, AstType) {
    match lit {
        Literal::Float(f) => (build_float_op(context, *f, location), AstType::Float),

        Literal::Int(x) => (build_int_op(context, *x, location), AstType::Int),

        Literal::Index(x) => (build_index_op(context, *x as i64, location), AstType::Index),

        Literal::Bool(x) => (build_bool_op(context, *x, location), AstType::Bool),
        _ => unimplemented!("{:?}", lit),
    }
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
