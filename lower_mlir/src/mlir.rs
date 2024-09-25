use anyhow::Result;
use flat::{Builtin, CodeOffset, ICodeModule, LCode, NodeBuilder, StringLabel, ValueId};
use indexmap::IndexMap;
use melior::ir::Location;
use melior::{
    dialect::{
        arith,
        cf,
        func,
        llvm,
        memref,
        //ods,
        scf,
    },
    ir::{
        self,
        attribute::FlatSymbolRefAttribute,
        attribute::{
            DenseElementsAttribute,
            //FlatSymbolRefAttribute,
            //FloatAttribute,
            IntegerAttribute,
            StringAttribute,
            TypeAttribute,
        },
        r#type::{FunctionType, IntegerType, MemRefType, RankedTensorType, TupleType},
        Attribute, Block, Identifier, Operation, Region, Type, TypeLike, Value, ValueLike,
    },
    Context,
};
use std::collections::VecDeque;

use compile_core::{AstType, Literal, NaryOperation, ReturnType, Span, UnaryOperation};

use std::collections::HashMap;

pub trait LowerIR<'c> {
    fn lower_literal(&mut self, v: ValueId, lit: &compile_core::Literal);
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum SymIndex {
    Op(ValueId, usize),
    Arg(ValueId, usize),
    Def(ValueId, usize),
}

impl SymIndex {
    pub fn block(&self) -> ValueId {
        match self {
            SymIndex::Op(block_index, _)
            | SymIndex::Arg(block_index, _)
            | SymIndex::Def(block_index, _) => *block_index,
        }
    }

    pub fn offset(&self) -> usize {
        match self {
            SymIndex::Op(_, offset) | SymIndex::Arg(_, offset) | SymIndex::Def(_, offset) => {
                *offset
            }
        }
    }

    pub fn is_op(&self) -> bool {
        if let SymIndex::Op(_, _) = self {
            true
        } else {
            false
        }
    }

    pub fn is_arg(&self) -> bool {
        if let SymIndex::Arg(_, _) = self {
            true
        } else {
            false
        }
    }
}

#[derive(Debug)]
pub struct OpCollection<'c> {
    block_id: ValueId,
    op_count: usize,
    //arg_count: usize,
    block: Option<Block<'c>>,
    ops: Vec<Operation<'c>>,
    complete: bool,
}

impl<'c> OpCollection<'c> {
    pub fn new(block_id: ValueId, block: Block<'c>) -> Self {
        Self {
            block_id,
            op_count: 0,
            //arg_count: 0,
            block: Some(block),
            ops: vec![],
            complete: false,
        }
    }

    pub fn is_complete(&self) -> bool {
        self.complete
    }

    pub fn push(&mut self, op: Operation<'c>) -> SymIndex {
        let offset = self.op_count;
        self.ops.push(op);
        self.op_count += 1;
        SymIndex::Op(self.block_id, offset)
    }

    pub fn take_ops(&mut self) -> Vec<Operation<'c>> {
        assert_eq!(self.op_count, self.ops.len());
        self.ops.drain(..).collect()
    }

    pub fn take_block(&mut self) -> Block<'c> {
        let ops = self.take_ops();
        let block = self.block.take().unwrap();
        for op in ops {
            block.append_operation(op);
        }
        block
    }

    pub fn op_ref(&mut self, index: SymIndex) -> &mut Operation<'c> {
        match index {
            SymIndex::Op(block_id, offset) => {
                assert_eq!(block_id, self.block_id);
                assert!(offset < self.ops.len());
                self.ops.get_mut(offset).expect("Op missing")
            }
            SymIndex::Arg(_, _) => {
                unreachable!()
            }
            _ => unimplemented!(),
        }
    }

    pub fn values(&self, values: Vec<SymIndex>) -> Vec<Value<'c, '_>> {
        let mut rs = vec![];
        for index in values {
            let op = self.ops.get(index.offset()).expect("Op missing");
            let r = op.result(0).unwrap();
            rs.push(r.into());
        }
        rs
    }
}

pub struct MLIRGenerator<'c> {
    pub(crate) context: &'c Context,
    blockify: &'c dyn ICodeModule,
    index: IndexMap<ValueId, SymIndex>,
    module_block_id: ValueId,
    blocks: HashMap<ValueId, OpCollection<'c>>,
    b: &'c NodeBuilder,
}

impl<'c> MLIRGenerator<'c> {
    pub fn new(
        context: &'c Context,
        blockify: &'c dyn ICodeModule,
        module_block_id: ValueId,
        b: &'c NodeBuilder,
    ) -> Self {
        Self {
            context,
            blockify,
            index: IndexMap::new(),
            module_block_id,
            blocks: HashMap::new(),
            b,
        }
    }
}

impl<'c> MLIRGenerator<'c> {
    pub fn take_block(&mut self, block_id: ValueId) -> Block<'c> {
        self.blocks.get_mut(&block_id).unwrap().take_block()
    }

    pub fn op_ref(&mut self, index: SymIndex) -> &mut Operation<'c> {
        let c = self.blocks.get_mut(&index.block()).unwrap();
        let op = c.op_ref(index);
        op
    }

    pub fn append_op(&mut self, index: SymIndex, block_id: ValueId, region_index: usize) {
        let block = self.blocks.get_mut(&block_id).unwrap().take_block();
        let op = self.blocks.get_mut(&index.block()).unwrap().op_ref(index);
        op.region(region_index).unwrap().append_block(block);
    }

    pub fn value0(&self, index: SymIndex) -> Value<'c, '_> {
        let c = self.blocks.get(&index.block()).unwrap();
        match index {
            SymIndex::Op(_, pos) => {
                let op = c.ops.get(pos).expect("Op missing");
                op.result(0).unwrap().into()
            }
            SymIndex::Arg(_, pos) => c.block.as_ref().unwrap().argument(pos).unwrap().into(),
            _ => unimplemented!(),
        }
    }

    pub fn values(&self, values: Vec<SymIndex>) -> Vec<Value<'c, '_>> {
        let mut rs = vec![];
        for index in values {
            let r = self.value0(index);
            rs.push(r);
        }
        rs
    }
}

impl<'c> LowerIR<'c> for MLIRGenerator<'c> {
    fn lower_literal(&mut self, v: ValueId, lit: &Literal) {
        let block_id = self.blockify.get_entry_id(v);
        let location = self.get_location(v);

        if self.blockify.is_in_static_scope(v.into()) {
            let (value, ast_ty) = self.build_static_attribute(lit);

            let name = self.blockify.get_name(v.into()).unwrap();

            // declare
            let integer_type = IntegerType::new(self.context, 64).into();
            let (ty, dims) = self.from_type(&ast_ty);
            assert_eq!(dims.len(), 0);
            let alignment = IntegerAttribute::new(integer_type, 8);
            let memspace = IntegerAttribute::new(integer_type, 0).into();
            let constant = false;

            let mut op = memref::global(
                self.context,
                &self.b.labels.r(name),
                Some("private"),
                MemRefType::new(ty, &[], None, Some(memspace)),
                // initial value is not set
                None,
                constant,
                Some(alignment),
                location,
            );

            //let ty = self.from_type(&ast_ty, b);
            let attribute =
                DenseElementsAttribute::new(RankedTensorType::new(&[], ty, None).into(), &[value])
                    .unwrap();

            let c = self.blocks.get_mut(&block_id).unwrap();
            //let index = lower.index.get(&v).unwrap();
            //let op = c.op_ref(index);
            //let current = blocks.blocks.get_mut(&block_index).unwrap();
            //let op = current.op_ref(sym_index);
            op.set_attribute("initial_value", attribute.into());
            let index = c.push(op);
            //if !is_current_static {
            // STATIC VARIABLE IN FUNCTION CONTEXT
            // TODO: FIXME
            //cfg.static_names
            //.insert(sym_index, b.strings.intern(global_name.clone()));
            //}
            //Ok(index)
            self.index.insert(v, index);
        } else {
            let op = self.emit_literal_const(lit, location);
            let c = self.blocks.get_mut(&block_id).unwrap();
            let index = c.push(op);
            self.index.insert(v, index);
        }
    }
}

impl<'c> MLIRGenerator<'c> {
    pub fn get_location(&self, value_id: ValueId) -> Location<'c> {
        let span_id = self.blockify.get_span_id(value_id);
        let span = self.b.spans.lookup(span_id);
        let location = self.diagnostics_location(&span);
        location
    }

    fn diagnostics_location(&self, span: &Span) -> ir::Location<'c> {
        if let Ok(name) = self.b.spans.get_filename(span) {
            let loc = self.b.spans.get_location(span).unwrap();
            ir::Location::new(self.context, &name, loc.line_number, loc.column_number)
        } else {
            ir::Location::unknown(self.context)
        }
    }

    pub fn resolve_value(&self, offset: CodeOffset) -> Option<SymIndex> {
        if let Some(offset_decl) = self.blockify.resolve_declaration(offset) {
            let mut current = offset_decl;
            loop {
                let v_decl = self.blockify.resolve_code_offset(current);
                let code = self.blockify.get_code(v_decl);
                if let LCode::Value(next_value_id) = code {
                    current = (*next_value_id).into();
                    continue;
                }

                if let LCode::CallValue(next_value_id) = code {
                    current = (*next_value_id).into();
                    continue;
                }

                if let LCode::ValueIndex(link_id, index) = code {
                    let v = self.blockify.resolve_code_offset(link_id.into());
                    let index = (*index) as usize;
                    /*
                    let c = self
                        .blocks
                        .get(&v)
                        .expect(&format!("missing block at {}", v));

                    let block = c.block.as_ref().unwrap();
                    let arg_count = block.argument_count();
                    assert!(index < arg_count, "mismatch arity on index");
                    block.argument(index).unwrap();
                    */

                    return Some(SymIndex::Arg(v, index));
                }
                break;
            }
            let v = self.blockify.resolve_code_offset(current);
            self.index.get(&v).cloned()
        } else {
            None
        }
    }

    pub fn get_label_args(&self, v: ValueId) -> Vec<(Type<'c>, Location<'c>)> {
        let types = self.blockify.get_label_args(v);
        if types == vec![AstType::Unit] {
            vec![]
        } else {
            let location = self.get_location(v);
            types
                .into_iter()
                .map(|ty| {
                    let (ty, dims) = self.from_type(&ty);
                    assert_eq!(dims.len(), 0);
                    (ty, location)
                })
                .collect()
        }
        /*
        let mut out = vec![];
        let mut current = v;
        loop {
            current = self.blockify.get_next(current).unwrap();
            let code = self.blockify.get_code(current);
            if let LCode::Arg(_) = code {
                let location = self.get_location(current);
                let ty = self.blockify.get_type(current.into());
                //assert!(ty != AstType::Unit);
                //if ty == AstType::Unit {
                //}
                let (ty, dims) = self.from_type(&ty);
                assert_eq!(dims.len(), 0);
                out.push((ty, location));
            } else {
                break;
            }
        }
        out
        */
    }

    pub fn create_block(&mut self, entry_id: ValueId) {
        //println!("create block: {}", entry_id);
        let code = self.blockify.get_code(entry_id);
        if let LCode::Label = code {
            let args = self.get_label_args(entry_id);
            let block = Block::new(&args);
            let c = OpCollection::new(entry_id, block);
            self.blocks.insert(entry_id, c);
        } else {
            unreachable!("{:?}", code)
        }
    }

    pub fn lower_jump(&mut self, v: ValueId, target_value_id: ValueId) -> Result<()> {
        let block_id = self.blockify.get_entry_id(v);
        let values = self.blockify.get_previous_values(v);
        let indicies = values
            .iter()
            .map(|value_id| self.resolve_value(*value_id).unwrap())
            .collect();
        let rs = self.values(indicies);

        let c = self
            .blocks
            .get(&target_value_id)
            .expect(&format!("missing block at {}", target_value_id));
        let arg_count = c.block.as_ref().unwrap().argument_count();
        assert_eq!(arg_count, values.len(), "mismatch arity on jump");

        let location = self.get_location(v);
        let op = cf::br(&c.block.as_ref().unwrap(), &rs, location);
        let c = self.blocks.get_mut(&block_id).unwrap();

        let index = c.push(op);
        self.index.insert(v, index);
        Ok(())
    }

    pub fn lower_code(&mut self, v: ValueId) -> Result<()> {
        let code = self.blockify.get_code(v);
        let location = self.get_location(v);

        match code {
            LCode::Label => {
                // should already exist
                assert!(self.blocks.get(&v).is_some());
            }

            LCode::Arg(pos) => {
                let block_id = self.blockify.get_entry_id(v);
                let index = SymIndex::Arg(block_id, *pos as usize);
                self.index.insert(v, index);
            }

            LCode::Jump(target) => {
                let target_value_id = self.blockify.resolve_code_offset(*target);
                self.lower_jump(v, target_value_id)?;
            }

            LCode::Const(lit) => {
                self.lower_literal(v, lit);
            }

            LCode::Return => {
                let values = self.blockify.get_previous_values(v);
                let indicies = values
                    .iter()
                    .map(|value_id| self.resolve_value(*value_id).unwrap())
                    .collect();
                let rs = self.values(indicies);
                let op = func::r#return(&rs, location);
                let block_id = self.blockify.get_entry_id(v);
                let c = self.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                self.index.insert(v, index);
            }

            LCode::DeclareFunction(maybe_block_id) => {
                let static_block_id = self.module_block_id;
                //let _block_id = self.blockify.get_entry_id(v);
                let key = self.blockify.get_name(v.into()).unwrap();
                let ty = self.blockify.get_type(v.into());

                //if static_block_id == block_id {
                // global context
                let visibility = if maybe_block_id.is_some() {
                    "private"
                } else {
                    "private"
                };

                let op = self.build_declare_function(key, ty, location, visibility)?;
                let c = self.blocks.get_mut(&static_block_id).unwrap();
                let index = c.push(op);
                self.index.insert(v, index);

                if let Some(block_id) = maybe_block_id.clone() {
                    let attribute = Attribute::unit(self.context);
                    let op = self.op_ref(index);
                    op.set_attribute("llvm.emit_c_interface", attribute);
                    let offset = block_id.clone().into();
                    let entry_id = self.blockify.resolve_code_offset(offset);
                    let block_ids = self.blockify.blocks(block_id, entry_id, self.b);

                    // create blocks
                    for block_id in block_ids.iter() {
                        let entry_id = self.blockify.resolve_code_offset(*block_id);
                        self.create_block(entry_id);
                    }

                    // lower
                    for block_id in block_ids.iter() {
                        let entry_id = self.blockify.resolve_code_offset(*block_id);
                        self.lower_block(entry_id)?;
                    }

                    // append blocks to region
                    for block_id in block_ids.iter() {
                        let entry_id = self.blockify.resolve_code_offset(*block_id);
                        self.append_op(index, entry_id, 0);
                    }
                }

                //} else {
                // local context
                // nothing to do?
                //let entry_id = maybe_entry_id.unwrap();
                //let index = lower.index.get(&entry_id).unwrap();
                //let code = LCode::Value(entry_id);
                //self.push_code(code, scope_id, block_id, ty, VarDefinitionSpace::Reg);
                //lower.index.insert(v, index);
                //}
            }

            LCode::Call(v_f) => {
                // TODO: ensure calling static

                // function to call
                let key = self.blockify.get_name((*v_f).into()).unwrap();
                let name = self.b.labels.r(key);
                let ty = self.blockify.get_type((*v_f).into());
                let f = FlatSymbolRefAttribute::new(self.context, &name);

                if let AstType::Func(_func_arg_types, ret) = &ty {
                    let ret_ty = match ret.as_ref() {
                        ReturnType::Single(ty) => ty,
                        ReturnType::Multi(_) => {
                            /*
                            let fields = ret.fields();
                            let ret_types = fields.into_iter().map(|(_, ty)| ty.clone()).collect::<Vec<_>>();
                            let ret_ty = if ret_types.is_empty() {
                                AstType::Unit
                            } else {
                                ret_types.get(0).unwrap().clone()
                            };
                            */
                            unimplemented!()
                        }
                    };

                    let (ret_type, dims) = self.from_type(&ret_ty);
                    assert_eq!(dims.len(), 0);
                    // handle call arguments

                    let values = self.blockify.get_previous_values(v);
                    let indicies = values
                        .iter()
                        .map(|value_id| self.resolve_value(*value_id).unwrap())
                        .collect();
                    let rs = self.values(indicies);

                    let ret = if ret_type.is_none() {
                        vec![]
                    } else {
                        vec![ret_type.clone()]
                    };

                    let op = func::call(self.context, f, &rs, &ret, location);

                    let block_id = self.blockify.get_entry_id(v);
                    let c = self.blocks.get_mut(&block_id).unwrap();
                    let index = c.push(op);
                    self.index.insert(v, index);
                } else {
                    unimplemented!("calling non function type: {:?}", ty);
                }
            }

            LCode::Declare => {
                //if let Some(name) = self.blockify.get_name(v.into()) {
                //let s = self.b.labels.r(name);
                //println!("declare: {:?}", (s));
                //}
                let block_id = self.blockify.get_entry_id(v);
                let ast_ty = self.blockify.get_type(v.into());
                let (ty, dims) = self.from_type(&ast_ty);
                let memref_ty = MemRefType::new(ty.into(), &dims, None, None);
                //println!("declare: {:?}", (ty, dims, memref_ty));
                let op = memref::alloca(self.context, memref_ty, &[], &[], None, location);

                /*
                if false {
                    let tuple_type = llvm::r#type::r#struct(self.context, &types, true);
                    let ptr_type = llvm::r#type::pointer(tuple_type, 0);
                    let (op, _ast_ty) = crate::op::emit_literal_const(
                        self.context,
                        &Literal::Int(1),
                        location,
                    );
                    let c = blocks.blocks.get_mut(&block_id).unwrap();
                    let size_sym = c.push(op);
                    let r_size = blocks.value0(size_sym);
                    let options = melior::dialect::llvm::AllocaOptions::new();
                    let op =
                        llvm::alloca(self.context, r_size, ptr_type, location, options);
                    let c = blocks.blocks.get_mut(&block_id).unwrap();
                    let index = c.push(op);
                    self.index.insert(v, index);

                }
                */

                /*
                let options = melior::dialect::llvm::AllocaOptions::new();
                let ptr_type = memref_ty.into();

                let (op, _ast_ty) = crate::op::emit_literal_const(self.context, &Literal::Int(1), location);
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let size_sym = c.push(op);
                let r_size = blocks.value0(size_sym);
                let op = llvm::alloca(self.context, r_size, ptr_type, location, options);
                */
                let c = self.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                self.index.insert(v, index);
            }

            LCode::Store(v_decl, v_value) => {
                let block_id = self.blockify.get_entry_id(v);
                let decl_is_static = self.blockify.is_in_static_scope(v_decl.into());

                let addr_index = if decl_is_static {
                    let name = self.blockify.get_name(v_decl.into()).unwrap();
                    let lhs_ty = self.blockify.get_type(v_decl.into());
                    let rhs_ty = self.blockify.get_type(v_value.into());
                    assert_eq!(lhs_ty, rhs_ty);

                    let (lower_ty, dims) = self.from_type(&lhs_ty);
                    assert_eq!(dims.len(), 0);
                    let memref_ty = MemRefType::new(lower_ty, &[], None, None);
                    let static_name = self.b.labels.r(name);
                    // TODO: FIXME
                    //let static_name = b
                    //.strings
                    //.resolve(&cfg.static_names.get(&sym_index).cloned().unwrap_or(name));
                    let op = memref::get_global(self.context, &static_name, memref_ty, location);
                    //let current = blocks.get_mut(&block_index).unwrap();
                    //let addr_index = current.push(op);
                    //addr_index
                    let c = self.blocks.get_mut(&block_id).unwrap();
                    let index = c.push(op);
                    self.index.insert(v, index);
                    index
                } else {
                    let decl_index = self.resolve_value(v_decl.into()).unwrap();
                    decl_index
                };

                let value_index = self.resolve_value(v_value.into()).unwrap();
                let r_addr = self.value0(addr_index);
                let r_value = self.value0(value_index);

                // emit store
                // store(value, memref)
                let op = memref::store(r_value, r_addr, &[], location);

                let c = self.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                self.index.insert(v, index);
            }

            LCode::Load(v_decl) => {
                let block_id = self.blockify.get_entry_id(v);
                let v_decl = self.blockify.resolve_declaration(v_decl.into()).unwrap();
                if self.blockify.is_in_static_scope(v_decl) {
                    let ast_ty = self.blockify.get_type(v.into());
                    let (lower_ty, dims) = self.from_type(&ast_ty);
                    assert_eq!(dims.len(), 0);
                    let memref_ty = MemRefType::new(lower_ty, &[], None, None);
                    // TODO: FIXME
                    let decl_name = self.blockify.get_name(v_decl).unwrap();
                    let static_name = self.b.labels.r(decl_name);
                    let op = memref::get_global(self.context, &static_name, memref_ty, location);
                    let c = self.blocks.get_mut(&block_id).unwrap();
                    let addr_index = c.push(op);
                    let r_addr = self.value0(addr_index);
                    let op = memref::load(r_addr, &[], location);
                    let c = self.blocks.get_mut(&block_id).unwrap();
                    let index = c.push(op);
                    self.index.insert(v, index);
                } else {
                    let decl_index = self.resolve_value(v_decl).expect(&format!(
                        "Unable to resolve declaration {} for load {}",
                        v_decl, v
                    ));
                    let r_addr = self.value0(decl_index);
                    let op = memref::load(r_addr, &[], location);
                    let c = self.blocks.get_mut(&block_id).unwrap();
                    let index = c.push(op);
                    self.index.insert(v, index);
                }
            }

            LCode::Op1(op) => {
                let x = self.blockify.get_prev(v).unwrap().into();

                let block_id = self.blockify.get_entry_id(v);
                let x_index = self.resolve_value(x).unwrap();
                let ast_ty = self.blockify.get_type(x);
                let (ty, dims) = self.from_type(&ast_ty);
                assert_eq!(dims.len(), 0);

                match op {
                    UnaryOperation::Minus => {
                        if ty.is_index() {
                            unreachable!("Unable to negate index type");
                        } else if ty.is_integer() {
                            // Multiply by -1
                            let int_op = self.build_int_op(-1, location);
                            let c = self.blocks.get_mut(&block_id).unwrap();
                            let index = c.push(int_op);
                            let r = self.value0(index);
                            let r_x = self.value0(x_index);
                            let op = arith::muli(r, r_x, location);
                            let c = self.blocks.get_mut(&block_id).unwrap();
                            let index = c.push(op);
                            self.index.insert(v, index);
                        } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                            // arith has an op for negation
                            let r_x = self.value0(x_index);
                            let op = arith::negf(r_x, location);
                            let c = self.blocks.get_mut(&block_id).unwrap();
                            let index = c.push(op);
                            self.index.insert(v, index);
                        } else {
                            unimplemented!()
                        }
                    }
                }
            }

            LCode::Op2(op) => {
                let y = self.blockify.get_prev(v).unwrap();
                let x = self.blockify.get_prev(y).unwrap();

                let vx = self.blockify.resolve_code_offset(x.into());
                let vy = self.blockify.resolve_code_offset(y.into());
                let block_id = self.blockify.get_entry_id(v);
                let x_span_id = self.blockify.get_span_id(vx);
                let y_span_id = self.blockify.get_span_id(vy);
                //let x_span = b.spans.lookup(x_span_id);
                //let y_span = b.spans.lookup(y_span_id);
                let x_index = self.resolve_value(vx.into()).unwrap();
                let r_x = self.value0(x_index);
                let y_index = self.resolve_value(vy.into()).unwrap();
                let r_y = self.value0(y_index);

                let (op, _ast_ty) =
                    self.build_binop(op.clone(), r_x, &x_span_id, r_y, &y_span_id, location)?;
                let c = self.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                self.index.insert(v, index);
            }

            LCode::NaryOp(op) => {
                let values = self.blockify.get_previous_values(v);
                let types = values
                    .iter()
                    .map(|v| {
                        let ast_ty = self.blockify.get_type(v.into());
                        let (ty, _dims) = self.from_type(&ast_ty);
                        ty
                    })
                    .collect::<Vec<_>>();
                match op {
                    NaryOperation::Struct => {
                        // construct a sized struct memref and store it somewhere
                        let block_id = self.blockify.get_entry_id(v);

                        //let op = memref::alloca(self.context, memref_ty, &[], &[], None, location);
                        if true {
                            let tuple_type = llvm::r#type::r#struct(self.context, &types, true);
                            /*
                            let ptr_type = llvm::r#type::pointer(tuple_type, 0);
                            let (op, _ast_ty) = crate::op::emit_literal_const(
                            self.context,
                            &Literal::Int(1),
                            location,
                            );
                            let c = blocks.blocks.get_mut(&block_id).unwrap();
                            let size_sym = c.push(op);
                            let r_size = blocks.value0(size_sym);
                            let options = melior::dialect::llvm::AllocaOptions::new();
                            let op =
                            llvm::alloca(self.context, r_size, ptr_type, location, options);
                            let c = blocks.blocks.get_mut(&block_id).unwrap();
                            let index = c.push(op);
                            self.index.insert(v, index);

                            }
                            */

                            let ptr_type = llvm::r#type::pointer(self.context, 0);
                            let op = self.build_int_op(1, location);
                            let c = self.blocks.get_mut(&block_id).unwrap();
                            let size_sym = c.push(op);
                            let r_size = self.value0(size_sym);
                            let options = melior::dialect::llvm::AllocaOptions::new();
                            let type_attr = TypeAttribute::new(tuple_type);
                            let options = options.elem_type(Some(type_attr));
                            let op =
                                llvm::alloca(self.context, r_size, ptr_type, location, options);
                            let c = self.blocks.get_mut(&block_id).unwrap();
                            let index = c.push(op);
                            self.index.insert(v, index);
                        }

                        if false {
                            let ty = TupleType::new(self.context, &types);
                            //let ty = IntegerType::new(self.context, 8);
                            let memref_ty = MemRefType::new(ty.into(), &[], None, None);
                            //println!("struct: {:?}", (block_id, ty, memref_ty));
                            let options = melior::dialect::llvm::AllocaOptions::new();
                            let ptr_type = memref_ty.into();

                            let op = self.build_int_op(1, location);
                            //let (op, _ast_ty) = self.emit_literal_const(&Literal::Int(1), location);
                            let c = self.blocks.get_mut(&block_id).unwrap();
                            let size_sym = c.push(op);
                            let r_size = self.value0(size_sym);
                            let op =
                                llvm::alloca(self.context, r_size, ptr_type, location, options);
                            let c = self.blocks.get_mut(&block_id).unwrap();
                            let index = c.push(op);
                            self.index.insert(v, index);
                        }

                        if false {
                            let ty = TupleType::new(self.context, &types);
                            //let ty = IntegerType::new(self.context, 8);
                            let memref_ty = MemRefType::new(ty.into(), &[], None, None);
                            //println!("struct: {:?}", (block_id, ty, memref_ty));

                            let op =
                                memref::alloca(self.context, memref_ty, &[], &[], None, location);
                            let c = self.blocks.get_mut(&block_id).unwrap();
                            let index = c.push(op);
                            self.index.insert(v, index);
                        }
                    }
                }
            }

            LCode::Branch(condition, then_block_id, else_block_id) => {
                let v_then = self.blockify.resolve_code_offset((*then_block_id).into());
                let v_else = self.blockify.resolve_code_offset((*else_block_id).into());

                let c_index = self.resolve_value((*condition).into()).unwrap();
                let r_c = self.value0(c_index);

                let c = self.blocks.get(&v_then).unwrap();
                let then_block = c.block.as_ref().unwrap();

                let c = self
                    .blocks
                    .get(&v_else)
                    .expect(&format!("missing else block in branch: {}", v_else));
                let else_block = c.block.as_ref().unwrap();

                let op = cf::cond_br(
                    self.context,
                    r_c,
                    &then_block,
                    &else_block,
                    &[], //then_args,
                    &[], //else_args,
                    location,
                );
                let block_id = self.blockify.get_entry_id(v);
                let c = self.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                self.index.insert(v, index);
            }

            LCode::Ternary(condition, then_block_id, else_block_id) => {
                // THEN
                //let then_block_id = blockify.get_entry_id(*v_then);
                //let then_block_id = blockify.resolve_code_offset(v_then);
                let then_block_id = *then_block_id;
                let v_then = self.blockify.resolve_code_offset(then_block_id.into());
                let then_block_ids = self.blockify.blocks(then_block_id, v_then, self.b);

                for block_id in then_block_ids.iter() {
                    let entry_id = self.blockify.resolve_code_offset(*block_id);
                    self.create_block(entry_id);
                }
                for block_id in then_block_ids.iter() {
                    let entry_id = self.blockify.resolve_code_offset(*block_id);
                    self.lower_block(entry_id)?;
                }

                // yield the last value
                let c = self.blocks.get_mut(&v_then).unwrap();
                let r2: Value<'c, '_> = c.ops.last().unwrap().operand(0).unwrap().into();
                let then_ty = r2.r#type();

                // ELSE
                //let else_block_id = blockify.get_entry_id(*v_else);
                //let else_block_id = blockify.resolve_code_offset(*v_else);
                let else_block_id = *else_block_id;
                let v_else = self.blockify.resolve_code_offset(else_block_id.into());
                let else_block_ids = self.blockify.blocks(else_block_id, v_else, self.b);

                for block_id in else_block_ids.iter() {
                    let entry_id = self.blockify.resolve_code_offset(*block_id);
                    self.create_block(entry_id);
                }
                for block_id in else_block_ids.iter() {
                    let entry_id = self.blockify.resolve_code_offset(*block_id);
                    self.lower_block(entry_id)?;
                }

                // yield the last value
                let c = self.blocks.get_mut(&v_else).unwrap();
                let r: Value<'c, '_> = c.ops.last().unwrap().operand(0).unwrap().into();
                let else_ty = r.r#type();

                let then_region = Region::new();
                for block_id in then_block_ids.iter() {
                    let entry_id = self.blockify.resolve_code_offset(*block_id);
                    let block = self.take_block(entry_id);
                    then_region.append_block(block);
                }

                let else_region = Region::new();
                for block_id in else_block_ids.iter() {
                    let entry_id = self.blockify.resolve_code_offset(*block_id);
                    let block = self.take_block(entry_id);
                    else_region.append_block(block);
                }

                let c_index = self.resolve_value((*condition).into()).unwrap();
                let r_c = self.value0(c_index);

                assert_eq!(then_ty, else_ty);
                let r_types = &[then_ty];

                let op = scf::r#if(r_c, r_types, then_region, else_region, location);
                let block_id = self.blockify.get_entry_id(v);
                let c = self.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                self.index.insert(v, index);
            }

            LCode::Yield => {
                let block_id = self.blockify.get_entry_id(v);
                let values = self.blockify.get_previous_values(v);
                let indicies = values
                    .iter()
                    .map(|value_id| self.resolve_value(*value_id).unwrap())
                    .collect();
                let rs = self.values(indicies);
                let r = rs[0];
                let op = scf::r#yield(&[r], location);
                let c = self.blocks.get_mut(&block_id).unwrap();
                c.push(op);
            }

            LCode::Value(_) => (),
            LCode::ValueIndex(_, _) => (),
            LCode::CallValue(_) => (),
            LCode::Noop => (),
            LCode::Extern => (),

            LCode::Builtin(id) => {
                let bi = self.b.builtins.get_enum(*id);
                match bi {
                    Builtin::Import => {
                        unreachable!()
                    }
                    Builtin::Assert => {
                        let values = self.blockify.get_previous_values(v);
                        let indicies = values
                            .iter()
                            .map(|value_id| self.resolve_value(*value_id).unwrap())
                            .collect();
                        let rs = self.values(indicies);

                        let msg = "assert";
                        //let msg = d.emit_string(error(msg, self.span));
                        let op = cf::assert(self.context, rs[0], &msg, location);
                        let block_id = self.blockify.get_entry_id(v);
                        let c = self.blocks.get_mut(&block_id).unwrap();
                        let index = c.push(op);
                        self.index.insert(v, index);
                    }
                    Builtin::Print => {
                        let values = self.blockify.get_previous_values(v);
                        let indicies = values
                            .iter()
                            .map(|value_id| self.resolve_value(*value_id).unwrap())
                            .collect();
                        let rs = self.values(indicies);
                        let r = rs[0];
                        let ty = r.r#type();

                        // Select the baked version based on parameters
                        // TODO: A more dynamic way of doing this
                        // TODO: We only want to import these if they are referenced
                        let ident = if ty.is_index() || ty.is_integer() {
                            let it = IntegerType::try_from(ty)?;
                            if it.width() == 1 {
                                "print_bool"
                            } else {
                                "print_index"
                            }
                        } else if ty.is_f64() {
                            "print_float"
                        } else {
                            unimplemented!("{:?}", (&ty, ty))
                        };

                        let f = FlatSymbolRefAttribute::new(self.context, ident);
                        let op = func::call(self.context, f, &[r], &[], location);
                        let block_id = self.blockify.get_entry_id(v);
                        let c = self.blocks.get_mut(&block_id).unwrap();
                        let index = c.push(op);
                        self.index.insert(v, index);
                    } //_ => unreachable!("{:?}", bi),
                }
            } //_ => unimplemented!("{:?}", (v, code)),
            LCode::DeclareTemplate(_) => (),
        }
        Ok(())
    }

    pub fn lower_block(&mut self, entry_id: ValueId) -> Result<()> {
        //println!("lower block: {}", entry_id);
        let mut current = entry_id;
        loop {
            self.lower_code(current)?;
            if let Some(next) = self.blockify.get_next(current) {
                current = next;
            } else {
                break;
            }
        }
        self.blocks.get_mut(&entry_id).unwrap().complete = true;
        Ok(())
    }

    pub fn lower_static_block(&mut self, module_block_id: ValueId) -> Result<()> {
        // reorder things, so we lower declarations last
        let mut current = module_block_id;
        let mut values = VecDeque::new();

        loop {
            let code = self.blockify.get_code(current);
            if let LCode::DeclareFunction(Some(_)) = code {
                values.push_back(current);
            } else {
                values.push_front(current);
            }
            if let Some(next) = self.blockify.get_next(current) {
                current = next;
            } else {
                break;
            }
        }

        for current in values {
            self.lower_code(current)?;
        }

        self.blocks.get_mut(&module_block_id).unwrap().complete = true;
        Ok(())
    }

    pub fn lower_module(&mut self, module: &mut melior::ir::Module) -> Result<()> {
        let module_block_id = self.module_block_id;
        self.create_block(module_block_id);
        self.lower_static_block(module_block_id)?;
        let block = self.blocks.get_mut(&module_block_id).unwrap();
        for op in block.take_ops() {
            module.body().append_operation(op);
        }
        Ok(())
    }
}

impl<'c> MLIRGenerator<'c> {
    pub fn build_declare_function(
        &self,
        key: StringLabel,
        ast_ty: AstType,
        location: Location<'c>,
        visibility: &str,
    ) -> Result<Operation<'c>> {
        if let AstType::Func(params, ast_ret_type) = ast_ty.clone() {
            let mut type_list = vec![];
            let mut ast_types = vec![];

            let attributes = vec![(
                Identifier::new(self.context, "sym_visibility"),
                StringAttribute::new(self.context, visibility).into(),
            )];

            for (_, ty) in params.fields() {
                let (p_ty, dims) = self.from_type(&ty);
                assert_eq!(dims.len(), 0);
                type_list.push(p_ty);
                ast_types.push(ty.clone());
            }

            let region = Region::new();

            let ret_type = match ast_ret_type.as_ref() {
                ReturnType::Single(ty) => {
                    let ret_type = if let AstType::Unit = ty {
                        vec![]
                        /*
                        } else if ty.is_composite() {
                            let fields = ty.fields().into_iter().map(|(_, ty)| {
                                let (ty, _dims) = self.from_type(&ty);
                                ty
                            }).collect::<Vec<_>>();
                            assert!(fields.len() <= 1);
                            if fields.len() == 0 {
                                vec![]
                            } else {
                                //let (ty, _) = kself.from_type(&fields.get(1).unwrap());
                                vec![*fields.get(0).unwrap()]
                            }
                            */
                    } else {
                        let (ty, dims) = self.from_type(&ty);
                        assert_eq!(dims.len(), 0);
                        vec![ty]
                    };
                    ret_type
                }
                ReturnType::Multi(_) => {
                    unimplemented!()
                }
            };

            let func_type = FunctionType::new(self.context, &type_list, &ret_type);
            let func_name_attr = StringAttribute::new(self.context, &self.b.labels.r(key));
            let func_ty_attr = TypeAttribute::new(func_type.into());

            let op = func::func(
                self.context,
                func_name_attr,
                func_ty_attr,
                region,
                &attributes,
                location,
            );
            Ok(op)
        } else {
            unreachable!()
        }
    }
}
