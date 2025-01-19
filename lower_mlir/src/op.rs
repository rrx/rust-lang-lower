use crate::MLIRGenerator;
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

impl<'c> MLIRGenerator<'c> {
    pub fn from_type(&self, ty: &AstType) -> (Type<'c>, Vec<i64>) {
        match ty {
            AstType::Ptr(_) => (Type::index(self.context), vec![]),
            AstType::Tuple(args) => {
                let types = args
                    .iter()
                    .map(|ast_ty| {
                        let (ty, _dims) = self.from_type(ast_ty);
                        ty
                    })
                    .collect::<Vec<_>>();
                (
                    IntegerType::new(self.context, 64).into(),
                    vec![types.len() as i64],
                )
            }

            //AstType::TargetUnion(_, _) => (IntegerType::new(self.context, 64).into(), vec![]),
            AstType::JumpTarget => (IntegerType::new(self.context, 64).into(), vec![]),
            AstType::Func(_) => (IntegerType::new(self.context, 64).into(), vec![]),
            AstType::Struct(_args) => {
                /*
                let types = args
                    .iter()
                    .map(|(_, ast_ty)| {
                        let (ty, _dims) = self.from_type(ast_ty);
                        ty
                    })
                .collect::<Vec<_>>();
                (IntegerType::new(self.context, 64).into(), vec![types.len() as i64])
                */

                /*
                let tuple_type = llvm::r#type::r#struct(self.context, &types, true);
                let ptr_type = llvm::r#type::pointer(self.context, 0);
                //(ptr_type, tuple_type)
                (tuple_type, vec![])
                    */

                /*
                //let types = args
                //.iter()
                //.map(|(_, a)| self.from_type(a).0)
                //.collect::<Vec<_>>();
                //let tuple_type = llvm::r#type::r#struct(self.context, &types, true);
                let b_ty = IntegerType::new(self.context, 64);
                let size = args.len();
                let memref_ty = MemRefType::new(b_ty.into(), &[size as i64], None, None);
                (
                    memref_ty.into(),
                    vec![args.len() as i64]
                )
                    */

                //
                let ptr_type = llvm::r#type::pointer(self.context, 0);
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
            /*
            AstType::Func(args, ret) => {
                let inputs = args
                    .fields()
                    .iter()
                    .map(|(_, a)| self.from_type(a).0)
                    .collect::<Vec<_>>();

                let results = match ret.as_ref() {
                    ReturnType::Never => vec![],
                    ReturnType::Single(ret) => {
                        vec![self.from_type(ret).0]
                    }
                    ReturnType::Multi(_ret) => {
                        unimplemented!()
                    }
                };
                (
                    melior::ir::r#type::FunctionType::new(self.context, &inputs, &results).into(),
                    vec![],
                )
            }
            */
            AstType::Array(ast_ty, dims) => {
                let ty = self.from_type(ast_ty).0;
                (ty, dims.iter().map(|i| *i as i64).collect())
            }
            AstType::Args(ty) => {
                // TODO: hardwired for now
                //let ty = Type::index(self.context);
                //let dummy = vec![self.from_type(&AstType::Int).0];
                println!("args_ty: {}", ty);
                //let fields = ty
                //.fields()
                //.iter()
                //.map(|(_, f)| self.from_type(f).0)
                //.collect::<Vec<_>>();
                //let tuple_type = llvm::r#type::r#struct(self.context, &fields, true);
                let ptr_type = llvm::r#type::pointer(self.context, 0);
                (ptr_type.into(), vec![])

                //let ty = TupleType::new(self.context, &[self.from_type(&AstType::Int, b).0]);
                //let mty = MemRefType::new(ty.into(), &[], None, None);
                //let ty = IntegerType::new(self.context, 64).into();
                //(mty.into(), vec![])
            }
            AstType::KwArgs(_) => {
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
                let value = IntegerAttribute::new(ty, v).into();
                let op = self.build_static(&global_name, ty, value, false, location);
                (ast_ty, op)
            }

            Ast::Literal(Literal::Int(x)) => {
                let ast_ty = AstType::Int;
                let ty = self.from_type(&ast_ty).0;
                let value = IntegerAttribute::new(ty, x).into();
                let op = self.build_static(&global_name, ty, value, false, location);
                (ast_ty, op)
            }

            Ast::Literal(Literal::Index(x)) => {
                let ast_ty = AstType::Int;
                let ty = self.from_type(&ast_ty).0;
                let value = IntegerAttribute::new(ty, x as i64).into();
                let op = self.build_static(&global_name, ty, value, false, location);
                (ast_ty, op)
            }

            Ast::Literal(Literal::Float(x)) => {
                let ast_ty = AstType::Float;
                let ty = self.from_type(&ast_ty).0;
                let value = FloatAttribute::new(self.context, ty, x).into();
                let op = self.build_static(&global_name, ty, value, false, location);
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
                let value = IntegerAttribute::new(ty, v).into();
                (value, ast_ty)
            }

            Literal::Int(x) => {
                let ast_ty = AstType::Int;
                let ty = self.from_type(&ast_ty).0;
                let value = IntegerAttribute::new(ty, *x).into();
                (value, ast_ty)
            }

            Literal::Index(x) => {
                let ast_ty = AstType::Int;
                let ty = self.from_type(&ast_ty).0;
                let value = IntegerAttribute::new(ty, *x as i64).into();
                (value, ast_ty)
            }

            Literal::Float(x) => {
                let ast_ty = AstType::Float;
                let ty = self.from_type(&ast_ty).0;
                let value = FloatAttribute::new(self.context, ty, *x).into();
                (value, ast_ty)
            }
            _ => unreachable!("{:?}", lit),
        }
    }

    pub fn build_float_op(&self, value: f64, location: Location<'c>) -> Operation<'c> {
        arith::constant(
            self.context,
            FloatAttribute::new(self.context, Type::float64(self.context), value).into(),
            location,
        )
    }

    pub fn build_int_op(&self, value: i64, location: Location<'c>) -> Operation<'c> {
        let ty = IntegerType::new(self.context, 64);
        arith::constant(
            self.context,
            IntegerAttribute::new(ty.into(), value).into(),
            location,
        )
    }

    pub fn build_index_op(&self, value: i64, location: Location<'c>) -> Operation<'c> {
        let ty = Type::index(self.context);
        arith::constant(
            self.context,
            IntegerAttribute::new(ty.into(), value).into(),
            location,
        )
    }

    pub fn build_bool_op(&self, value: bool, location: Location<'c>) -> Operation<'c> {
        let bool_type = IntegerType::new(self.context, 1);
        arith::constant(
            self.context,
            IntegerAttribute::new(bool_type.into(), if value { 1 } else { 0 }).into(),
            location,
        )
    }

    pub fn emit_literal_const(&self, lit: &Literal, location: Location<'c>) -> Operation<'c> {
        match lit {
            Literal::Float(f) => self.build_float_op(*f, location),

            Literal::Int(x) => self.build_int_op(*x, location),

            Literal::Index(x) => self.build_index_op(*x as i64, location),

            Literal::Bool(x) => self.build_bool_op(*x, location),
            Literal::String(_) => {
                // TODO, replace with dummy value
                self.build_int_op(0, location)
            }

            /*
                Literal::Block(block_id) => {
                    // this is a variable passed into a jump statement
                    // We are keeping this very simple and just passing the block_id index
                    // as the argument.  This is unique in the module.  It's not dense, but it's
                    // much easier to debug.
                    let index = block_id.index() as i64;
                    self.build_int_op(index as i64, location)
                    /*
                    let ty = llvm::r#type::pointer(self.context, 0);
                    arith::constant(
                        self.context,
                        IntegerAttribute::new(ty, block_id.index() as i64).into(),
                        location,
                    )
                    */
                }
            */
            _ => unimplemented!("{:?}", lit),
        }
    }

    pub fn build_reserved(
        &self,
        name: &str,
        location: Location<'c>,
    ) -> Option<(Operation<'c>, AstType)> {
        match name {
            "True" => {
                let op = self.build_bool_op(true, location);
                Some((op, AstType::Bool))
            }
            "False" => {
                let op = self.build_bool_op(false, location);
                Some((op, AstType::Bool))
            }
            _ => None,
        }
    }

    pub fn build_static(
        &self,
        name: &str,
        ty: Type<'c>,
        value: Attribute<'c>,
        constant: bool,
        location: Location<'c>,
    ) -> Operation<'c> {
        let integer_type = IntegerType::new(self.context, 64).into();
        let attribute =
            DenseElementsAttribute::new(RankedTensorType::new(&[], ty, None).into(), &[value])
                .unwrap();
        let alignment = IntegerAttribute::new(integer_type, 8);
        let memspace = IntegerAttribute::new(integer_type, 0).into();

        memref::global(
            self.context,
            name,
            Some("private"),
            MemRefType::new(ty, &[], None, Some(memspace)),
            Some(attribute.into()),
            constant,
            Some(alignment),
            location,
        )
    }

    pub fn build_binop(
        &self,
        op: BinaryOperation,
        a: Value<'c, '_>,
        a_span: &SpanId,
        b: Value<'c, '_>,
        _b_span: &SpanId,
        location: Location<'c>,
    ) -> Result<(Operation<'c>, AstType)> {
        let ty = a.r#type();
        assert_eq!(ty, b.r#type());

        let is_float = ty.is_f64() || ty.is_f32() || ty.is_f16();

        let (op, ast_ty) = match op {
            BinaryOperation::Divide => {
                if ty.is_index() {
                    // index type is unsigned
                    (arith::divui(a, b, location), AstType::Index)
                } else if ty.is_integer() {
                    // we assume all integers are signed for now
                    (arith::divsi(a, b, location), AstType::Int)
                } else if is_float {
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
                } else if is_float {
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
                } else if is_float {
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
                } else if is_float {
                    (arith::subf(a, b, location), AstType::Float)
                } else {
                    return Err(Error::new(LowerError::Op(format!("Invalid Type"), *a_span)));
                }
            }
            BinaryOperation::GTE => {
                if ty.is_index() {
                    // unsigned
                    (
                        arith::cmpi(self.context, arith::CmpiPredicate::Uge, a, b, location),
                        AstType::Bool,
                    )
                } else if ty.is_integer() {
                    // signed
                    (
                        arith::cmpi(self.context, arith::CmpiPredicate::Sge, a, b, location),
                        AstType::Bool,
                    )
                } else if is_float {
                    (
                        arith::cmpf(self.context, arith::CmpfPredicate::Oge, a, b, location),
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
                        arith::cmpi(self.context, arith::CmpiPredicate::Ugt, a, b, location),
                        AstType::Bool,
                    )
                } else if ty.is_integer() {
                    // signed
                    (
                        arith::cmpi(self.context, arith::CmpiPredicate::Sgt, a, b, location),
                        AstType::Bool,
                    )
                } else if is_float {
                    (
                        arith::cmpf(self.context, arith::CmpfPredicate::Ogt, a, b, location),
                        AstType::Bool,
                    )
                } else {
                    return Err(Error::new(LowerError::Op(format!("Invalid Type"), *a_span)));
                }
            }
            BinaryOperation::NE => {
                if ty.is_index() || ty.is_integer() {
                    (
                        arith::cmpi(self.context, arith::CmpiPredicate::Ne, a, b, location),
                        AstType::Bool,
                    )
                } else if is_float {
                    // ordered comparison
                    (
                        arith::cmpf(self.context, arith::CmpfPredicate::One, a, b, location),
                        AstType::Bool,
                    )
                } else {
                    return Err(Error::new(LowerError::Op(format!("Invalid Type"), *a_span)));
                }
            }
            BinaryOperation::EQ => {
                if ty.is_index() || ty.is_integer() {
                    (
                        arith::cmpi(self.context, arith::CmpiPredicate::Eq, a, b, location),
                        AstType::Bool,
                    )
                } else if is_float {
                    // ordered comparison
                    (
                        arith::cmpf(self.context, arith::CmpfPredicate::Oeq, a, b, location),
                        AstType::Bool,
                    )
                } else {
                    return Err(Error::new(LowerError::Op(format!("Invalid Type"), *a_span)));
                }
            } //_ => unimplemented!("{:?}", op)
        };

        Ok((op, ast_ty))
    }
}
