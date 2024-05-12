use anyhow::Result;
use flat::{Blockify, Builtin, CodeOffset, LCode, NodeBuilder, StringLabel, ValueId};
use indexmap::IndexMap;
use melior::ir::Location;
use melior::{
    dialect::{
        arith,
        cf,
        func,
        //llvm,
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
        r#type::{FunctionType, IntegerType, MemRefType, RankedTensorType},
        Attribute, Block, Identifier, Operation, Region, Type, TypeLike, Value, ValueLike,
    },
    Context,
};
use std::collections::VecDeque;

use compile_core::{AstType, Span, UnaryOperation, VarDefinitionSpace};

use std::collections::HashMap;

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

pub struct LowerBlocks<'c> {
    blocks: HashMap<ValueId, OpCollection<'c>>,
}
impl<'c> LowerBlocks<'c> {
    pub fn new() -> Self {
        Self {
            blocks: HashMap::new(),
        }
    }

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

pub struct Lower<'c> {
    context: &'c Context,
    index: IndexMap<ValueId, SymIndex>,
    module_block_id: ValueId,
}

impl<'c> Lower<'c> {
    pub fn new(context: &'c Context, module_block_id: ValueId) -> Self {
        Self {
            context,
            index: IndexMap::new(),
            module_block_id,
        }
    }
}

#[derive(Debug)]
pub struct OpCollection<'c> {
    block_id: ValueId,
    op_count: usize,
    arg_count: usize,
    block: Option<Block<'c>>,
    ops: Vec<Operation<'c>>,
    complete: bool,
}

impl<'c> OpCollection<'c> {
    pub fn new(block_id: ValueId, block: Block<'c>) -> Self {
        Self {
            block_id,
            op_count: 0,
            arg_count: 0,
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

impl<'c> Lower<'c> {
    pub fn get_location(
        blockify: &Blockify,
        value_id: ValueId,
        context: &'c Context,
        b: &NodeBuilder,
    ) -> Location<'c> {
        let span_id = blockify.get_span_id(value_id);
        let span = b.spans.lookup(span_id);
        let location = diagnostics_location(b, context, &span);
        location
    }

    pub fn resolve_value(&self, blockify: &Blockify, value_id: ValueId) -> Option<SymIndex> {
        if let Some(v_decl) = blockify.resolve_declaration(value_id) {
            let mut current = v_decl;
            loop {
                let code = blockify.get_code(current);
                if let LCode::Value(next_value_id) = code {
                    current = *next_value_id;
                    continue;
                } else {
                    break;
                }
            }
            self.index.get(&current).cloned()
        } else {
            None
        }
    }

    pub fn get_label_args(
        &self,
        blockify: &Blockify,
        context: &'c Context,
        v: ValueId,
        num_args: usize,
        num_kwargs: usize,
        b: &NodeBuilder,
    ) -> Vec<(Type<'c>, Location<'c>)> {
        let mut current = v;
        let mut out = vec![];
        for _ in 0..num_args {
            let location = Lower::get_location(blockify, current, context, b);

            let next = blockify.get_next(current).unwrap();
            let ty = crate::op::from_type(context, &blockify.get_type(next), b);
            current = next;
            out.push((ty, location));
        }
        for _ in 0..num_kwargs {
            let location = Lower::get_location(blockify, current, context, b);
            let next = blockify.get_next(current).unwrap();
            let ty = crate::op::from_type(context, &blockify.get_type(next), b);
            current = next;
            out.push((ty, location));
        }
        out
    }

    pub fn create_block(
        &self,
        blockify: &Blockify,
        blocks: &mut LowerBlocks<'c>,
        entry_id: ValueId,
        b: &NodeBuilder,
    ) {
        let code = blockify.get_code(entry_id);
        if let LCode::Label(num_args, num_kwargs) = code {
            let args = self.get_label_args(
                blockify,
                self.context,
                entry_id,
                *num_args as usize,
                *num_kwargs as usize,
                b,
            );
            let block = Block::new(&args);
            let c = OpCollection::new(entry_id, block);
            blocks.blocks.insert(entry_id, c);
        } else {
            unreachable!()
        }
    }

    pub fn lower_jump(
        &mut self,
        blockify: &Blockify,
        blocks: &mut LowerBlocks<'c>,
        v: ValueId,
        target_value_id: ValueId,
        num_args: u8,
        b: &NodeBuilder,
    ) -> Result<()> {
        let block_id = blockify.get_entry_id(v);
        let values = blockify.get_previous_values(v, num_args as usize);
        let indicies = values
            .iter()
            .map(|value_id| self.resolve_value(blockify, *value_id).unwrap())
            .collect();
        let rs = blocks.values(indicies);

        let c = blocks.blocks.get(&target_value_id).unwrap();
        let arg_count = c.block.as_ref().unwrap().argument_count();
        assert_eq!(arg_count, num_args as usize);

        let location = Lower::get_location(blockify, v, self.context, b);
        let op = cf::br(&c.block.as_ref().unwrap(), &rs, location);
        let c = blocks.blocks.get_mut(&block_id).unwrap();

        let index = c.push(op);
        self.index.insert(v, index);
        Ok(())
    }

    pub fn lower_code(
        &mut self,
        blockify: &Blockify,
        blocks: &mut LowerBlocks<'c>,
        v: ValueId,
        stack: &mut Vec<ValueId>,
        b: &mut NodeBuilder,
    ) -> Result<()> {
        let code = blockify.get_code(v);
        let location = Lower::get_location(blockify, v, self.context, b);

        println!("lower_code: {}", blockify.code_to_string(v, b));

        match code {
            LCode::Label(_num_args, _num_kwargs) => {
                // should already exist
                assert!(blocks.blocks.get(&v).is_some());
            }

            LCode::Arg(pos) => {
                //| LCode::NamedParameter(pos) => {
                let block_id = blockify.get_entry_id(v);
                let index = SymIndex::Arg(block_id, *pos as usize);
                self.index.insert(v, index);
            }

            LCode::Jump(target, num_args) => match target {
                CodeOffset::Value(target_value_id) => {
                    self.lower_jump(blockify, blocks, v, *target_value_id, *num_args, b)?;
                }
                CodeOffset::Block(target_block_id) => {
                    let target_entry_id = blockify
                        .env
                        .get_block_by_block_id(*target_block_id)
                        .entry_id
                        .unwrap();
                    self.lower_jump(blockify, blocks, v, target_entry_id, *num_args, b)?;
                }
            },

            LCode::Const(lit) => {
                let block_id = blockify.get_entry_id(v);

                if blockify.is_in_static_scope(v) {
                    let (value, ast_ty) = crate::op::build_static_attribute(self.context, lit, b);

                    let name = blockify.get_name(v).unwrap();

                    // declare
                    let integer_type = IntegerType::new(self.context, 64).into();
                    let ty = crate::op::from_type(self.context, &ast_ty, b);
                    let alignment = IntegerAttribute::new(8, integer_type);
                    let memspace = IntegerAttribute::new(0, integer_type).into();
                    let constant = false;

                    let mut op = memref::global(
                        self.context,
                        &b.labels.r(name),
                        Some("private"),
                        MemRefType::new(ty, &[], None, Some(memspace)),
                        // initial value is not set
                        None,
                        constant,
                        Some(alignment),
                        location,
                    );

                    let ty = crate::op::from_type(self.context, &ast_ty, b);
                    let attribute = DenseElementsAttribute::new(
                        RankedTensorType::new(&[], ty, None).into(),
                        &[value],
                    )
                    .unwrap();

                    let c = blocks.blocks.get_mut(&block_id).unwrap();
                    //let index = lower.index.get(&v).unwrap();
                    //let op = c.op_ref(index);
                    //let current = blocks.blocks.get_mut(&block_index).unwrap();
                    //let op = current.op_ref(sym_index);
                    op.set_attribute("initial_value", &attribute.into());
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
                    let (op, _ast_ty) = crate::op::emit_literal_const(self.context, lit, location);
                    let c = blocks.blocks.get_mut(&block_id).unwrap();
                    let index = c.push(op);
                    self.index.insert(v, index);
                }
            }

            LCode::Return(num_args) => {
                //let num = *num_args as usize;
                let values = blockify.get_previous_values(v, *num_args as usize);
                let indicies = values
                    .iter()
                    .map(|value_id| self.resolve_value(blockify, *value_id).unwrap())
                    .collect();
                let rs = blocks.values(indicies);
                let op = func::r#return(&rs, location);
                let block_id = blockify.get_entry_id(v);
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                self.index.insert(v, index);
            }

            LCode::DeclareFunction(maybe_entry_id) => {
                let static_block_id = self.module_block_id;
                let _block_id = blockify.get_entry_id(v);
                let key = blockify.get_name(v).unwrap();
                let ty = blockify.get_type(v);

                //if static_block_id == block_id {
                // global context
                let op = build_declare_function(self.context, key, ty, location, b)?;
                let c = blocks.blocks.get_mut(&static_block_id).unwrap();
                let index = c.push(op);
                self.index.insert(v, index);
                if let Some(entry_id) = maybe_entry_id {
                    let op = blocks.op_ref(index);
                    op.set_attribute("llvm.emit_c_interface", &Attribute::unit(self.context));

                    let cfg = blockify.get_cfg(*entry_id, b);
                    let offset = entry_id.clone().into();
                    let entry_id = blockify.env.resolve_code_offset(offset);
                    let block_ids = cfg.blocks(entry_id);

                    // create blocks
                    for block_id in block_ids.iter() {
                        let entry_id = blockify.env.resolve_code_offset(*block_id);
                        self.create_block(blockify, blocks, entry_id, b);
                    }

                    // lower
                    for block_id in block_ids.iter() {
                        let entry_id = blockify.env.resolve_code_offset(*block_id);
                        self.lower_block(blockify, entry_id, blocks, stack, b)?;
                    }

                    // append blocks to region
                    for block_id in block_ids.iter() {
                        let entry_id = blockify.env.resolve_code_offset(*block_id);
                        blocks.append_op(index, entry_id, 0);
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

            LCode::Call(v_f, args, _kwargs) => {
                // ensure calling static
                if let VarDefinitionSpace::Static = blockify.get_mem(*v_f) {
                } else {
                    // not supported
                    unreachable!()
                }

                // function to call
                let key = blockify.get_name(*v_f).unwrap();
                let name = b.labels.r(key);
                let ty = blockify.get_type(*v_f);
                let f = FlatSymbolRefAttribute::new(self.context, &name);

                if let AstType::Func(_func_arg_types, ret) = &ty {
                    let ret_type = crate::op::from_type(self.context, &ret, b);
                    // handle call arguments

                    let values = blockify.get_previous_values(v, *args as usize);
                    let indicies = values
                        .iter()
                        .map(|value_id| self.resolve_value(blockify, *value_id).unwrap())
                        .collect();
                    let rs = blocks.values(indicies);

                    let ret = if ret_type.is_none() {
                        vec![]
                    } else {
                        vec![ret_type.clone()]
                    };

                    let op = func::call(self.context, f, &rs, &ret, location);

                    let block_id = blockify.get_entry_id(v);
                    let c = blocks.blocks.get_mut(&block_id).unwrap();
                    let index = c.push(op);
                    self.index.insert(v, index);
                } else {
                    unimplemented!("calling non function type: {:?}", ty);
                }
            }

            LCode::Declare => {
                let block_id = blockify.get_entry_id(v);
                let ast_ty = blockify.get_type(v);
                let ty = crate::op::from_type(self.context, &ast_ty, b);
                let memref_ty = MemRefType::new(ty.into(), &[], None, None);
                let op = memref::alloca(self.context, memref_ty, &[], &[], None, location);
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                self.index.insert(v, index);
            }

            LCode::Store(v_decl, v_value) => {
                let block_id = blockify.get_entry_id(v);
                let decl_is_static = blockify.is_in_static_scope(*v_decl);

                let addr_index = if decl_is_static {
                    let name = blockify.get_name(*v_decl).unwrap();
                    let lhs_ty = blockify.get_type(*v_decl);
                    let rhs_ty = blockify.get_type(*v_value);
                    assert_eq!(lhs_ty, rhs_ty);

                    let lower_ty = crate::op::from_type(self.context, &lhs_ty, b);
                    let memref_ty = MemRefType::new(lower_ty, &[], None, None);
                    let static_name = b.labels.r(name);
                    // TODO: FIXME
                    //let static_name = b
                    //.strings
                    //.resolve(&cfg.static_names.get(&sym_index).cloned().unwrap_or(name));
                    let op = memref::get_global(self.context, &static_name, memref_ty, location);
                    //let current = blocks.get_mut(&block_index).unwrap();
                    //let addr_index = current.push(op);
                    //addr_index
                    let c = blocks.blocks.get_mut(&block_id).unwrap();
                    let index = c.push(op);
                    self.index.insert(v, index);
                    index
                } else {
                    let decl_index = self.resolve_value(blockify, *v_decl).unwrap();
                    decl_index
                };

                let value_index = self.resolve_value(blockify, *v_value).unwrap();
                let r_addr = blocks.value0(addr_index);
                let r_value = blocks.value0(value_index);

                // emit store
                // store(value, memref)
                let op = memref::store(r_value, r_addr, &[], location);

                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                self.index.insert(v, index);
            }

            LCode::Load(v_decl) => {
                let block_id = blockify.get_entry_id(v);
                let v_decl = blockify.resolve_declaration(*v_decl).unwrap();
                if blockify.is_in_static_scope(v_decl) {
                    let ast_ty = blockify.get_type(v);
                    let lower_ty = crate::op::from_type(self.context, &ast_ty, b);
                    let memref_ty = MemRefType::new(lower_ty, &[], None, None);
                    // TODO: FIXME
                    let decl_name = blockify.get_name(v_decl).unwrap();
                    let static_name = b.labels.r(decl_name);
                    let op = memref::get_global(self.context, &static_name, memref_ty, location);
                    let c = blocks.blocks.get_mut(&block_id).unwrap();
                    let addr_index = c.push(op);
                    let r_addr = blocks.value0(addr_index);
                    let op = memref::load(r_addr, &[], location);
                    let c = blocks.blocks.get_mut(&block_id).unwrap();
                    let index = c.push(op);
                    self.index.insert(v, index);
                } else {
                    let decl_index = self.resolve_value(blockify, v_decl).unwrap();
                    let r_addr = blocks.value0(decl_index);
                    let op = memref::load(r_addr, &[], location);
                    let c = blocks.blocks.get_mut(&block_id).unwrap();
                    let index = c.push(op);
                    self.index.insert(v, index);
                }
            }

            LCode::Op1(op, x) => {
                let block_id = blockify.get_entry_id(v);
                let x_index = self.resolve_value(blockify, *x).unwrap();
                let ast_ty = blockify.get_type(*x);
                let ty = crate::op::from_type(self.context, &ast_ty, b);

                match op {
                    UnaryOperation::Minus => {
                        if ty.is_index() {
                            unreachable!("Unable to negate index type");
                        } else if ty.is_integer() {
                            // Multiply by -1
                            let int_op = crate::op::build_int_op(self.context, -1, location);
                            let c = blocks.blocks.get_mut(&block_id).unwrap();
                            let index = c.push(int_op);
                            let r = blocks.value0(index);
                            let r_x = blocks.value0(x_index);
                            let op = arith::muli(r, r_x, location);
                            let c = blocks.blocks.get_mut(&block_id).unwrap();
                            let index = c.push(op);
                            self.index.insert(v, index);
                        } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                            // arith has an op for negation
                            let r_x = blocks.value0(x_index);
                            let op = arith::negf(r_x, location);
                            let c = blocks.blocks.get_mut(&block_id).unwrap();
                            let index = c.push(op);
                            self.index.insert(v, index);
                        } else {
                            unimplemented!()
                        }
                    }
                }
            }

            LCode::Op2(op, x, y) => {
                let block_id = blockify.get_entry_id(v);
                let x_span_id = blockify.get_span_id(*x);
                let y_span_id = blockify.get_span_id(*y);
                //let x_span = b.spans.lookup(x_span_id);
                //let y_span = b.spans.lookup(y_span_id);
                let x_index = self.resolve_value(blockify, *x).unwrap();
                let r_x = blocks.value0(x_index);
                let y_index = self.resolve_value(blockify, *y).unwrap();
                let r_y = blocks.value0(y_index);
                let (op, _ast_ty) = crate::op::build_binop(
                    self.context,
                    op.clone(),
                    r_x,
                    &x_span_id,
                    r_y,
                    &y_span_id,
                    location,
                )?;
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                self.index.insert(v, index);
            }

            LCode::Branch(condition, v_then, v_else) => {
                let then_block_id = blockify.env.resolve_code_offset(*v_then);
                let else_block_id = blockify.env.resolve_code_offset(*v_else);

                let c_index = self.resolve_value(blockify, *condition).unwrap();
                let r_c = blocks.value0(c_index);

                let c = blocks.blocks.get(&then_block_id).unwrap();
                let then_block = c.block.as_ref().unwrap();

                let c = blocks.blocks.get(&else_block_id).unwrap();
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
                let block_id = blockify.get_entry_id(v);
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                self.index.insert(v, index);
            }

            LCode::Ternary(condition, then_block_id, else_block_id) => {
                // THEN
                //let then_block_id = blockify.get_entry_id(*v_then);
                //let then_block_id = blockify.env.resolve_code_offset(v_then);
                let then_block_id = *then_block_id;
                let v_then = blockify.env.resolve_code_offset(then_block_id.into());
                let cfg = blockify.get_cfg(then_block_id.into(), b);
                let then_block_ids = cfg.blocks(v_then);

                for block_id in then_block_ids.iter() {
                    let entry_id = blockify.env.resolve_code_offset(*block_id);
                    self.create_block(blockify, blocks, entry_id, b);
                }
                for block_id in then_block_ids.iter() {
                    let entry_id = blockify.env.resolve_code_offset(*block_id);
                    self.lower_block(blockify, entry_id, blocks, stack, b)?;
                }

                // yield the last value
                let c = blocks.blocks.get_mut(&v_then).unwrap();
                let r2: Value<'c, '_> = c.ops.last().unwrap().operand(0).unwrap().into();
                let then_ty = r2.r#type();

                // ELSE
                //let else_block_id = blockify.get_entry_id(*v_else);
                //let else_block_id = blockify.env.resolve_code_offset(*v_else);
                let else_block_id = *else_block_id;
                let v_else = blockify.env.resolve_code_offset(else_block_id.into());
                let cfg = blockify.get_cfg(else_block_id.into(), b);
                let else_block_ids = cfg.blocks(v_else);

                for block_id in else_block_ids.iter() {
                    let entry_id = blockify.env.resolve_code_offset(*block_id);
                    self.create_block(blockify, blocks, entry_id, b);
                }
                for block_id in else_block_ids.iter() {
                    let entry_id = blockify.env.resolve_code_offset(*block_id);
                    self.lower_block(blockify, entry_id, blocks, stack, b)?;
                }

                // yield the last value
                let c = blocks.blocks.get_mut(&v_else).unwrap();
                let r: Value<'c, '_> = c.ops.last().unwrap().operand(0).unwrap().into();
                let else_ty = r.r#type();

                let then_region = Region::new();
                for block_id in then_block_ids.iter() {
                    let entry_id = blockify.env.resolve_code_offset(*block_id);
                    let block = blocks.take_block(entry_id);
                    then_region.append_block(block);
                }

                let else_region = Region::new();
                for block_id in else_block_ids.iter() {
                    let entry_id = blockify.env.resolve_code_offset(*block_id);
                    let block = blocks.take_block(entry_id);
                    else_region.append_block(block);
                }

                let c_index = self.resolve_value(blockify, *condition).unwrap();
                let r_c = blocks.value0(c_index);

                assert_eq!(then_ty, else_ty);
                let r_types = &[then_ty];

                let op = scf::r#if(r_c, r_types, then_region, else_region, location);
                let block_id = blockify.get_entry_id(v);
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                self.index.insert(v, index);
            }

            LCode::Yield(n_args) => {
                let block_id = blockify.get_entry_id(v);
                let values = blockify.get_previous_values(v, *n_args as usize);
                let indicies = values
                    .iter()
                    .map(|value_id| self.resolve_value(blockify, *value_id).unwrap())
                    .collect();
                let rs = blocks.values(indicies);
                let r = rs[0];
                let op = scf::r#yield(&[r], location);
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                c.push(op);
            }

            LCode::Value(_) => (),
            LCode::Noop => (),

            LCode::Builtin(id, num_args, _num_kwargs) => {
                let bi = b.builtins.get_enum(*id);
                let arity = bi.arity();
                assert_eq!(arity, *num_args as usize);

                match bi {
                    Builtin::Import => {
                        unreachable!()
                    }
                    Builtin::Assert => {
                        let values = blockify.get_previous_values(v, *num_args as usize);
                        let indicies = values
                            .iter()
                            .map(|value_id| self.resolve_value(blockify, *value_id).unwrap())
                            .collect();
                        let rs = blocks.values(indicies);

                        let msg = "assert";
                        //let msg = d.emit_string(error(msg, self.span));
                        let op = cf::assert(self.context, rs[0], &msg, location);
                        let block_id = blockify.get_entry_id(v);
                        let c = blocks.blocks.get_mut(&block_id).unwrap();
                        let index = c.push(op);
                        self.index.insert(v, index);
                    }
                    Builtin::Print => {
                        let values = blockify.get_previous_values(v, *num_args as usize);
                        let indicies = values
                            .iter()
                            .map(|value_id| self.resolve_value(blockify, *value_id).unwrap())
                            .collect();
                        let rs = blocks.values(indicies);
                        let r = rs[0];
                        let ty = r.r#type();

                        // Select the baked version based on parameters
                        // TODO: A more dynamic way of doing this
                        // TODO: We only want to import these if they are referenced
                        let ident = if ty.is_index() || ty.is_integer() {
                            "print_index"
                        } else if ty.is_f64() {
                            "print_float"
                        } else {
                            unimplemented!("{:?}", (&ty, ty))
                        };

                        let f = FlatSymbolRefAttribute::new(self.context, ident);
                        let op = func::call(self.context, f, &[r], &[], location);
                        let block_id = blockify.get_entry_id(v);
                        let c = blocks.blocks.get_mut(&block_id).unwrap();
                        let index = c.push(op);
                        self.index.insert(v, index);
                    } //_ => unreachable!("{:?}", bi),
                }
            } //_ => unimplemented!("{:?}", (v, code)),
        }
        Ok(())
    }

    pub fn lower_block(
        &mut self,
        blockify: &Blockify,
        block_id: ValueId,
        blocks: &mut LowerBlocks<'c>,
        stack: &mut Vec<ValueId>,
        b: &mut NodeBuilder,
    ) -> Result<()> {
        let mut current = block_id;
        stack.push(block_id);
        loop {
            self.lower_code(blockify, blocks, current, stack, b)?;
            if let Some(next) = blockify.get_next(current) {
                current = next;
            } else {
                break;
            }
        }
        blocks.blocks.get_mut(&block_id).unwrap().complete = true;
        stack.pop();
        Ok(())
    }

    pub fn lower_static_block(
        &mut self,
        blockify: &Blockify,
        module_block_id: ValueId,
        blocks: &mut LowerBlocks<'c>,
        stack: &mut Vec<ValueId>,
        b: &mut NodeBuilder,
    ) -> Result<()> {
        // reorder things, so we lower declarations last
        let mut current = module_block_id;
        stack.push(module_block_id);
        let mut values = VecDeque::new();

        loop {
            let code = blockify.get_code(current);
            if let LCode::DeclareFunction(Some(_)) = code {
                values.push_back(current);
            } else {
                values.push_front(current);
            }
            if let Some(next) = blockify.get_next(current) {
                current = next;
            } else {
                break;
            }
        }

        for current in values {
            self.lower_code(blockify, blocks, current, stack, b)?;
        }

        blocks.blocks.get_mut(&module_block_id).unwrap().complete = true;
        stack.pop();
        Ok(())
    }

    pub fn lower_module(
        &mut self,
        blockify: &Blockify,
        blocks: &mut LowerBlocks<'c>,
        module: &mut melior::ir::Module,
        b: &mut NodeBuilder,
    ) -> Result<()> {
        let module_block_id = self.module_block_id;
        let mut stack = vec![];
        self.create_block(blockify, blocks, module_block_id, b);
        self.lower_static_block(blockify, module_block_id, blocks, &mut stack, b)?;
        let block = blocks.blocks.get_mut(&module_block_id).unwrap();
        for op in block.take_ops() {
            module.body().append_operation(op);
        }
        Ok(())
    }
}

pub fn build_declare_function<'c>(
    context: &'c Context,
    key: StringLabel,
    ast_ty: AstType,
    location: Location<'c>,
    b: &NodeBuilder,
) -> Result<Operation<'c>> {
    if let AstType::Func(params, ast_ret_type) = ast_ty.clone() {
        let mut type_list = vec![];
        let mut ast_types = vec![];

        let attributes = vec![(
            Identifier::new(context, "sym_visibility"),
            StringAttribute::new(context, "private").into(),
        )];

        for ty in params {
            type_list.push(crate::op::from_type(context, &ty, b));
            ast_types.push(ty.clone());
        }

        let region = Region::new();

        let ret_type = if let AstType::Unit = *ast_ret_type {
            vec![]
        } else {
            vec![crate::op::from_type(context, &ast_ret_type, b)]
        };

        let func_type = FunctionType::new(context, &type_list, &ret_type);
        let func_name_attr = StringAttribute::new(context, &b.labels.r(key));
        let func_ty_attr = TypeAttribute::new(func_type.into());

        let op = func::func(
            context,
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

pub fn diagnostics_location<'c>(
    b: &NodeBuilder,
    context: &'c Context,
    span: &Span,
) -> ir::Location<'c> {
    if let Ok(name) = b.spans.get_filename(span) {
        let loc = b.spans.get_location(span).unwrap();
        ir::Location::new(context, &name, loc.line_number, loc.column_number)
    } else {
        ir::Location::unknown(context)
    }
}
