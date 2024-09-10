use crate::Lower;
use anyhow::Error;
use anyhow::Result;
use compile_core::Diagnostic;
use compile_core::{Ast, AstNode, AstType, BinaryOperation, Literal, SpanId};
use melior::ir::Location;
use melior::{
    dialect::{
        arith,
        //cf,
        //func,
        llvm,
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
use thiserror::Error;

#[derive(Error, Debug)]
pub enum LowerError {
    #[error("LowerError")]
    Invalid,
    #[error("op")]
    Op(String, SpanId),
    #[error("diagnostic")]
    Diagnostic(Diagnostic<usize>),
}

impl<'c> Lower<'c> {
    pub fn from_type(&self, ty: &AstType) -> (Type<'c>, Vec<u64>) {
        match ty {
            AstType::Ptr(_) => (Type::index(self.context), vec![]),
            AstType::Struct(args) => {
                let types = args
                    .iter()
                    .map(|(_, a)| self.from_type(a).0)
                    .collect::<Vec<_>>();
                let tuple_type = llvm::r#type::r#struct(self.context, &types, true);
                let ptr_type = llvm::r#type::pointer(tuple_type, 0);
                (
                    ptr_type,
                    //melior::ir::r#type::TupleType::new(self.context, &types).into(),
                    vec![],
                )
            }
            AstType::Union(args) => {
                //let byte_ty - IntegerType::width(8);
                //let memref = MemRefType::new(byte_type, &[size], None, None);
                // get the sizes and just create a type that has the max size of all fields
                let types = args
                    .iter()
                    .map(|(_, a)| self.from_type(a).0)
                    .collect::<Vec<_>>();
                (
                    melior::ir::r#type::TupleType::new(self.context, &types).into(),
                    vec![],
                )
            }
            AstType::Func(args, ret) => {
                let inputs = args
                    .fields()
                    .iter()
                    .map(|(_, a)| self.from_type(a).0)
                    .collect::<Vec<_>>();
                let results = vec![self.from_type(ret).0];
                (
                    melior::ir::r#type::FunctionType::new(self.context, &inputs, &results).into(),
                    vec![],
                )
            }
            AstType::Array(ast_ty, dims) => {
                let ty = self.from_type(ast_ty).0;
                (ty, dims.clone())
            }
            AstType::Args => {
                // TODO: hardwired for now
                //let ty = Type::index(self.context);
                let dummy = vec![self.from_type(&AstType::Int).0];
                let tuple_type = llvm::r#type::r#struct(self.context, &dummy, true);
                let ptr_type = llvm::r#type::pointer(tuple_type, 0);
                (ptr_type.into(), vec![])

                //let ty = TupleType::new(self.context, &[self.from_type(&AstType::Int, b).0]);
                //let mty = MemRefType::new(ty.into(), &[], None, None);
                //let ty = IntegerType::new(self.context, 64).into();
                //(mty.into(), vec![])
            }
            AstType::KwArgs => {
                // TODO: hardwired for now
                //let ty = Type::index(self.context);
                let ty = IntegerType::new(self.context, 64).into();
                (ty, vec![])
            }
            AstType::Int => (IntegerType::new(self.context, 64).into(), vec![]),
            AstType::Index => (Type::index(self.context), vec![]),
            AstType::Float => (Type::float64(self.context), vec![]),
            AstType::Bool => (IntegerType::new(self.context, 1).into(), vec![]),
            AstType::Unit => (Type::none(self.context), vec![]),

            // Resolve Variable
            AstType::Variable(x) => {
                unimplemented!("Missing type information: {:?}", x);
                //let ty = b.types.resolve_type(ty).unwrap();
                //self.from_type(&ty, b)
            }
            //AstType::String => Type::none(self.context),
            _ => unimplemented!("{:?}", ty),
        }
    }

    pub fn emit_static(
        &self,
        global_name: String,
        expr: AstNode,
        location: Location<'c>,
    ) -> (Operation<'c>, AstType) {
        // evaluate expr at compile time
        let (ast_ty, op) = match expr.node {
            Ast::Literal(Literal::Bool(x)) => {
                let ast_ty = AstType::Bool;
                let ty = self.from_type(&ast_ty).0;
                let v = if x { 1 } else { 0 };
                let value = IntegerAttribute::new(v, ty).into();
                let op = build_static(self.context, &global_name, ty, value, false, location);
                (ast_ty, op)
            }

            Ast::Literal(Literal::Int(x)) => {
                let ast_ty = AstType::Int;
                let ty = self.from_type(&ast_ty).0;
                let value = IntegerAttribute::new(x, ty).into();
                let op = build_static(self.context, &global_name, ty, value, false, location);
                (ast_ty, op)
            }

            Ast::Literal(Literal::Index(x)) => {
                let ast_ty = AstType::Int;
                let ty = self.from_type(&ast_ty).0;
                let value = IntegerAttribute::new(x as i64, ty).into();
                let op = build_static(self.context, &global_name, ty, value, false, location);
                (ast_ty, op)
            }

            Ast::Literal(Literal::Float(x)) => {
                let ast_ty = AstType::Float;
                let ty = self.from_type(&ast_ty).0;
                let value = FloatAttribute::new(self.context, x, ty).into();
                let op = build_static(self.context, &global_name, ty, value, false, location);
                (ast_ty, op)
            }

            _ => unreachable!("{:?}", expr.node),
        };
        (op, ast_ty)
    }

    pub fn build_static_attribute(&self, lit: &Literal) -> (Attribute<'c>, AstType) {
        // evaluate expr at compile time
        match lit {
            Literal::Bool(x) => {
                let ast_ty = AstType::Bool;
                let ty = self.from_type(&ast_ty).0;
                let v = if *x { 1 } else { 0 };
                let value = IntegerAttribute::new(v, ty).into();
                (value, ast_ty)
            }

            Literal::Int(x) => {
                let ast_ty = AstType::Int;
                let ty = self.from_type(&ast_ty).0;
                let value = IntegerAttribute::new(*x, ty).into();
                (value, ast_ty)
            }

            Literal::Index(x) => {
                let ast_ty = AstType::Int;
                let ty = self.from_type(&ast_ty).0;
                let value = IntegerAttribute::new(*x as i64, ty).into();
                (value, ast_ty)
            }

            Literal::Float(x) => {
                let ast_ty = AstType::Float;
                let ty = self.from_type(&ast_ty).0;
                let value = FloatAttribute::new(self.context, *x, ty).into();
                (value, ast_ty)
            }
            _ => unreachable!("{:?}", lit),
        }
    }
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
    a_span: &SpanId,
    b: Value<'c, '_>,
    _b_span: &SpanId,
    location: Location<'c>,
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
                return Err(Error::new(LowerError::Op(format!("Invalid Type"), *a_span)));
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
                return Err(Error::new(LowerError::Op(format!("Invalid Type"), *a_span)));
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
                return Err(Error::new(LowerError::Op(format!("Invalid Type"), *a_span)));
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
                return Err(Error::new(LowerError::Op(format!("Invalid Type"), *a_span)));
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
                return Err(Error::new(LowerError::Op(format!("Invalid Type"), *a_span)));
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
                return Err(Error::new(LowerError::Op(format!("Invalid Type"), *a_span)));
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
                return Err(Error::new(LowerError::Op(format!("Invalid Type"), *a_span)));
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
                return Err(Error::new(LowerError::Op(format!("Invalid Type"), *a_span)));
            }
        } //_ => unimplemented!("{:?}", op)
    };

    Ok((op, ast_ty))
}
