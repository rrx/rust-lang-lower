use crate::ast::BinaryOperation;
use crate::{Ast, AstNode, AstType, Diagnostics, Extra, Literal, ParseError, Span};

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

pub fn build_static_attribute<'c>(context: &'c Context, lit: &Literal) -> (Attribute<'c>, AstType) {
    // evaluate expr at compile time
    match lit {
        Literal::Bool(x) => {
            let ast_ty = AstType::Bool;
            let ty = from_type(context, &ast_ty);
            let v = if *x { 1 } else { 0 };
            let value = IntegerAttribute::new(v, ty).into();
            (value, ast_ty)
        }

        Literal::Int(x) => {
            let ast_ty = AstType::Int;
            let ty = from_type(context, &ast_ty);
            let value = IntegerAttribute::new(*x, ty).into();
            (value, ast_ty)
        }

        Literal::Index(x) => {
            let ast_ty = AstType::Int;
            let ty = from_type(context, &ast_ty);
            let value = IntegerAttribute::new(*x as i64, ty).into();
            (value, ast_ty)
        }

        Literal::Float(x) => {
            let ast_ty = AstType::Float;
            let ty = from_type(context, &ast_ty);
            let value = FloatAttribute::new(context, *x, ty).into();
            (value, ast_ty)
        }
        _ => unreachable!("{:?}", lit),
    }
}

pub fn build_binop<'c>(
    context: &'c Context,
    op: BinaryOperation,
    a: Value<'c, '_>,
    a_span: &Span,
    b: Value<'c, '_>,
    b_span: &Span,
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
                d.error(&format!("Invalid Type"), a_span);
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
                d.error(&format!("Invalid Type"), a_span);
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
                d.error(&format!("Invalid Type"), a_span);
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
                            d.primary(&format!("Type {:?}", a.r#type()), a_span),
                            d.secondary(&format!("Type: {:?}", b.r#type()), b_span),
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
                d.error(&format!("Invalid Type"), a_span);
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
                d.error(&format!("Invalid Type"), a_span);
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
                d.error(&format!("Invalid Type"), a_span);
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
                d.error(&format!("Invalid Type"), a_span);
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
