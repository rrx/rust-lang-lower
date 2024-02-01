use crate::{Blockify, LCode, ValueId};
use anyhow::Result;
use indexmap::IndexMap;
use lower::melior::ir::Location;
use lower::melior::{
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

use lower::{
    op,
    AstType,
    Builtin,
    Diagnostics,
    Extra,
    NodeBuilder,
    //StringKey,
    StringLabel,
    UnaryOperation,
    VarDefinitionSpace,
};

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

impl<E: Extra> Blockify<E> {
    pub fn resolve_declaration<'c>(&self, value_id: ValueId) -> Option<ValueId> {
        let mut current = value_id;
        loop {
            let code = self.get_code(current);
            if let LCode::Value(next_value_id) = code {
                current = *next_value_id;
            } else {
                return Some(current);
            }
        }
    }

    pub fn resolve_value<'c>(&self, lower: &Lower<'c>, value_id: ValueId) -> Option<SymIndex> {
        if let Some(v_decl) = self.resolve_declaration(value_id) {
            //println!("resolve: {:?}", value_id);
            let mut current = v_decl;
            loop {
                let code = self.get_code(current);
                if let LCode::Value(next_value_id) = code {
                    //println!("resolve: {:?}", next_value_id);
                    current = *next_value_id;
                    continue;
                } else {
                    break;
                }
            }
            //println!(":{:?}", lower.index);
            lower.index.get(&current).cloned()
        } else {
            None
        }
    }

    pub fn get_location<'c>(
        &self,
        value_id: ValueId,
        context: &'c Context,
        d: &Diagnostics,
    ) -> Location<'c> {
        let span_id = self.get_span_id(value_id);
        let span = d.lookup(span_id);
        let location = d.location(context, &span);
        location
    }

    pub fn get_label_args<'c>(
        &self,
        context: &'c Context,
        v: ValueId,
        num_args: usize,
        num_kwargs: usize,
        d: &Diagnostics,
    ) -> Vec<(Type<'c>, Location<'c>)> {
        let mut current = v;
        let mut out = vec![];
        for _ in 0..num_args {
            let location = self.get_location(current, context, d);

            let next = self.get_next(current).unwrap();
            let ty = op::from_type(context, &self.get_type(next));
            current = next;
            out.push((ty, location));
        }
        for _ in 0..num_kwargs {
            let location = self.get_location(current, context, d);
            let next = self.get_next(current).unwrap();
            let ty = op::from_type(context, &self.get_type(next));
            current = next;
            out.push((ty, location));
        }
        out
    }

    pub fn get_previous_values(&self, v: ValueId, num: usize) -> Vec<ValueId> {
        let mut values = vec![];
        for i in 0..num {
            let v = ValueId((v.0 as usize - num + i) as u32);
            let code = self.get_code(v);
            if let LCode::Value(value_id) = code {
                values.push(*value_id);
            }
        }
        values
    }

    pub fn create_block<'c>(
        &self,
        lower: &mut Lower<'c>,
        blocks: &mut LowerBlocks<'c>,
        block_id: ValueId,
        d: &Diagnostics,
    ) {
        let code = self.get_code(block_id);
        if let LCode::Label(num_args, num_kwargs) = code {
            let args = self.get_label_args(
                lower.context,
                block_id,
                *num_args as usize,
                *num_kwargs as usize,
                d,
            );
            let block = Block::new(&args);
            let c = OpCollection::new(block_id, block);
            blocks.blocks.insert(block_id, c);
        } else {
            unreachable!()
        }
    }

    pub fn lower_code<'c>(
        &self,
        lower: &mut Lower<'c>,
        blocks: &mut LowerBlocks<'c>,
        v: ValueId,
        stack: &mut Vec<ValueId>,
        b: &NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        let code = self.get_code(v);
        let location = self.get_location(v, lower.context, d);

        match code {
            LCode::Label(_num_args, _num_kwargs) => {
                // should already exist
                assert!(blocks.blocks.get(&v).is_some());
            }

            LCode::Arg(pos) => {
                //| LCode::NamedParameter(pos) => {
                let block_id = self.get_block_id(v);
                let index = SymIndex::Arg(block_id, *pos as usize);
                lower.index.insert(v, index);
            }

            LCode::Jump(target, num_args) => {
                //println!("jump: {:?}", (target, num_args));
                let block_id = self.get_block_id(v);
                let values = self.get_previous_values(v, *num_args as usize);
                let indicies = values
                    .iter()
                    .map(|value_id| self.resolve_value(lower, *value_id).unwrap())
                    .collect();
                let rs = blocks.values(indicies);

                let c = blocks.blocks.get(&target).unwrap();
                let arg_count = c.block.as_ref().unwrap().argument_count();
                assert_eq!(arg_count, *num_args as usize);

                let op = cf::br(&c.block.as_ref().unwrap(), &rs, location);
                let c = blocks.blocks.get_mut(&block_id).unwrap();

                let index = c.push(op);
                lower.index.insert(v, index);
            }

            LCode::Const(lit) => {
                let block_id = self.get_block_id(v);

                if self.is_in_static_scope(v) {
                    let (value, ast_ty) = op::build_static_attribute(lower.context, lit);

                    let name = self.get_name(v).unwrap();

                    // declare
                    let integer_type = IntegerType::new(lower.context, 64).into();
                    let ty = op::from_type(lower.context, &ast_ty);
                    let alignment = IntegerAttribute::new(8, integer_type);
                    let memspace = IntegerAttribute::new(0, integer_type).into();
                    let constant = false;

                    let mut op = memref::global(
                        lower.context,
                        &b.resolve_label(name),
                        Some("private"),
                        MemRefType::new(ty, &[], None, Some(memspace)),
                        // initial value is not set
                        None,
                        constant,
                        Some(alignment),
                        location,
                    );

                    let ty = op::from_type(lower.context, &ast_ty);
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
                    lower.index.insert(v, index);
                } else {
                    let (op, _ast_ty) = op::emit_literal_const(lower.context, lit, location);
                    let c = blocks.blocks.get_mut(&block_id).unwrap();
                    let index = c.push(op);
                    lower.index.insert(v, index);
                }
            }

            LCode::Return(num_args) => {
                //let num = *num_args as usize;
                let values = self.get_previous_values(v, *num_args as usize);
                let indicies = values
                    .iter()
                    .map(|value_id| self.resolve_value(lower, *value_id).unwrap())
                    .collect();
                let rs = blocks.values(indicies);
                let op = func::r#return(&rs, location);
                let block_id = self.get_block_id(v);
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                lower.index.insert(v, index);
            }

            LCode::DeclareFunction(maybe_entry_id) => {
                let static_block_id = lower.module_block_id;
                let _block_id = self.get_block_id(v);
                let key = self.get_name(v).unwrap();
                let ty = self.get_type(v);

                //if static_block_id == block_id {
                // global context
                let op = build_declare_function(lower.context, key, ty, location, b)?;
                let c = blocks.blocks.get_mut(&static_block_id).unwrap();
                let index = c.push(op);
                lower.index.insert(v, index);
                if let Some(entry_id) = maybe_entry_id {
                    let op = blocks.op_ref(index);
                    op.set_attribute("llvm.emit_c_interface", &Attribute::unit(lower.context));

                    let cfg = self.get_cfg(*entry_id, b);
                    let block_ids = cfg.blocks(*entry_id);

                    // create blocks
                    for block_id in block_ids.iter() {
                        self.create_block(lower, blocks, *block_id, d);
                    }

                    // lower
                    for block_id in block_ids.iter() {
                        self.lower_block(*block_id, lower, blocks, stack, b, d)?;
                    }

                    // append blocks to region
                    for block_id in block_ids.iter() {
                        blocks.append_op(index, *block_id, 0);
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
                if let VarDefinitionSpace::Static = self.get_mem(*v_f) {
                } else {
                    // not supported
                    unreachable!()
                }

                // function to call
                let key = self.get_name(*v_f).unwrap();
                let name = b.resolve_label(key);
                let ty = self.get_type(*v_f);
                let f = FlatSymbolRefAttribute::new(lower.context, &name);

                if let AstType::Func(_func_arg_types, ret) = &ty {
                    let ret_type = op::from_type(lower.context, &ret);
                    // handle call arguments

                    let values = self.get_previous_values(v, *args as usize);
                    let indicies = values
                        .iter()
                        .map(|value_id| self.resolve_value(lower, *value_id).unwrap())
                        .collect();
                    let rs = blocks.values(indicies);

                    let ret = if ret_type.is_none() {
                        vec![]
                    } else {
                        vec![ret_type.clone()]
                    };

                    let op = func::call(lower.context, f, &rs, &ret, location);

                    let block_id = self.get_block_id(v);
                    let c = blocks.blocks.get_mut(&block_id).unwrap();
                    let index = c.push(op);
                    lower.index.insert(v, index);
                } else {
                    unimplemented!("calling non function type: {:?}", ty);
                }
            }

            LCode::Declare => {
                let block_id = self.get_block_id(v);
                let ast_ty = self.get_type(v);
                let ty = op::from_type(lower.context, &ast_ty);
                let memref_ty = MemRefType::new(ty.into(), &[], None, None);
                let op = memref::alloca(lower.context, memref_ty, &[], &[], None, location);
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                lower.index.insert(v, index);
            }

            LCode::Store(v_decl, v_value) => {
                let block_id = self.get_block_id(v);
                let decl_is_static = self.is_in_static_scope(*v_decl);

                let addr_index = if decl_is_static {
                    let name = self.get_name(*v_decl).unwrap();
                    let lhs_ty = self.get_type(*v_decl);
                    let rhs_ty = self.get_type(*v_value);
                    assert_eq!(lhs_ty, rhs_ty);

                    let lower_ty = op::from_type(lower.context, &lhs_ty);
                    let memref_ty = MemRefType::new(lower_ty, &[], None, None);
                    let static_name = b.resolve_label(name);
                    // TODO: FIXME
                    //let static_name = b
                    //.strings
                    //.resolve(&cfg.static_names.get(&sym_index).cloned().unwrap_or(name));
                    let op = memref::get_global(lower.context, &static_name, memref_ty, location);
                    //let current = blocks.get_mut(&block_index).unwrap();
                    //let addr_index = current.push(op);
                    //addr_index
                    let c = blocks.blocks.get_mut(&block_id).unwrap();
                    let index = c.push(op);
                    lower.index.insert(v, index);
                    index
                } else {
                    let decl_index = self.resolve_value(lower, *v_decl).unwrap();
                    decl_index
                };

                let value_index = self.resolve_value(lower, *v_value).unwrap();
                let r_addr = blocks.value0(addr_index);
                let r_value = blocks.value0(value_index);

                // emit store
                // store(value, memref)
                let op = memref::store(r_value, r_addr, &[], location);

                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                lower.index.insert(v, index);
            }

            LCode::Load(v_decl) => {
                let block_id = self.get_block_id(v);
                let v_decl = self.resolve_declaration(*v_decl).unwrap();
                if self.is_in_static_scope(v_decl) {
                    let ast_ty = self.get_type(v);
                    let lower_ty = op::from_type(lower.context, &ast_ty);
                    let memref_ty = MemRefType::new(lower_ty, &[], None, None);
                    // TODO: FIXME
                    let decl_name = self.get_name(v_decl).unwrap();
                    let static_name = b.resolve_label(decl_name);
                    let op = memref::get_global(lower.context, &static_name, memref_ty, location);
                    let c = blocks.blocks.get_mut(&block_id).unwrap();
                    let addr_index = c.push(op);
                    let r_addr = blocks.value0(addr_index);
                    let op = memref::load(r_addr, &[], location);
                    let c = blocks.blocks.get_mut(&block_id).unwrap();
                    let index = c.push(op);
                    lower.index.insert(v, index);
                } else {
                    let decl_index = self.resolve_value(lower, v_decl).unwrap();
                    let r_addr = blocks.value0(decl_index);
                    let op = memref::load(r_addr, &[], location);
                    let c = blocks.blocks.get_mut(&block_id).unwrap();
                    let index = c.push(op);
                    lower.index.insert(v, index);
                }
            }

            LCode::Op1(op, x) => {
                let block_id = self.get_block_id(v);
                let x_index = self.resolve_value(lower, *x).unwrap();
                let ast_ty = self.get_type(*x);
                let ty = op::from_type(lower.context, &ast_ty);

                match op {
                    UnaryOperation::Minus => {
                        if ty.is_index() {
                            unreachable!("Unable to negate index type");
                        } else if ty.is_integer() {
                            // Multiply by -1
                            let int_op = op::build_int_op(lower.context, -1, location);
                            let c = blocks.blocks.get_mut(&block_id).unwrap();
                            let index = c.push(int_op);
                            let r = blocks.value0(index);
                            let r_x = blocks.value0(x_index);
                            let op = arith::muli(r, r_x, location);
                            let c = blocks.blocks.get_mut(&block_id).unwrap();
                            let index = c.push(op);
                            lower.index.insert(v, index);
                        } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                            // arith has an op for negation
                            let r_x = blocks.value0(x_index);
                            let op = arith::negf(r_x, location);
                            let c = blocks.blocks.get_mut(&block_id).unwrap();
                            let index = c.push(op);
                            lower.index.insert(v, index);
                        } else {
                            unimplemented!()
                        }
                    }
                }
            }

            LCode::Op2(op, x, y) => {
                let block_id = self.get_block_id(v);
                let x_span_id = self.get_span_id(*x);
                let y_span_id = self.get_span_id(*y);
                let x_span = d.lookup(x_span_id);
                let y_span = d.lookup(y_span_id);
                let x_index = self.resolve_value(lower, *x).unwrap();
                let r_x = blocks.value0(x_index);
                let y_index = self.resolve_value(lower, *y).unwrap();
                let r_y = blocks.value0(y_index);
                let (op, _ast_ty) = op::build_binop(
                    lower.context,
                    op.clone(),
                    r_x,
                    &x_span,
                    r_y,
                    &y_span,
                    location,
                    d,
                )?;
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                lower.index.insert(v, index);
            }

            LCode::Branch(condition, v_then, v_else) => {
                let then_block_id = self.get_block_id(*v_then);
                let else_block_id = self.get_block_id(*v_else);

                let c_index = self.resolve_value(lower, *condition).unwrap();
                let r_c = blocks.value0(c_index);

                let c = blocks.blocks.get(&then_block_id).unwrap();
                let then_block = c.block.as_ref().unwrap();

                let c = blocks.blocks.get(&else_block_id).unwrap();
                let else_block = c.block.as_ref().unwrap();

                let op = cf::cond_br(
                    lower.context,
                    r_c,
                    &then_block,
                    &else_block,
                    &[], //then_args,
                    &[], //else_args,
                    location,
                );
                //println!("op: {:?}", (op));
                let block_id = self.get_block_id(v);
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                lower.index.insert(v, index);
            }

            LCode::Ternary(condition, v_then, v_else) => {
                // THEN
                let then_block_id = self.get_block_id(*v_then);

                let cfg = self.get_cfg(then_block_id, b);
                let then_block_ids = cfg.blocks(then_block_id);

                for block_id in then_block_ids.iter() {
                    self.create_block(lower, blocks, *block_id, d);
                }
                for block_id in then_block_ids.iter() {
                    self.lower_block(*block_id, lower, blocks, stack, b, d)?;
                }

                let c = blocks.blocks.get_mut(&then_block_id).unwrap();
                let r: Value<'c, '_> = c.ops.last().unwrap().result(0).unwrap().into();
                let then_ty = r.r#type();
                let op = scf::r#yield(&[r], location);
                let c = blocks.blocks.get_mut(&then_block_id).unwrap();
                c.push(op);

                // ELSE
                let else_block_id = self.get_block_id(*v_else);

                let cfg = self.get_cfg(else_block_id, b);
                let else_block_ids = cfg.blocks(else_block_id);

                for block_id in else_block_ids.iter() {
                    self.create_block(lower, blocks, *block_id, d);
                }
                for block_id in else_block_ids.iter() {
                    self.lower_block(*block_id, lower, blocks, stack, b, d)?;
                }

                let c = blocks.blocks.get_mut(&else_block_id).unwrap();
                let r: Value<'c, '_> = c.ops.last().unwrap().result(0).unwrap().into();
                let else_ty = r.r#type();
                let op = scf::r#yield(&[r], location);
                let c = blocks.blocks.get_mut(&else_block_id).unwrap();
                c.push(op);

                let then_region = Region::new();
                for block_id in then_block_ids.iter() {
                    let block = blocks.take_block(*block_id);
                    then_region.append_block(block);
                }

                let else_region = Region::new();
                for block_id in else_block_ids.iter() {
                    let block = blocks.take_block(*block_id);
                    else_region.append_block(block);
                }

                let c_index = self.resolve_value(lower, *condition).unwrap();
                let r_c = blocks.value0(c_index);

                assert_eq!(then_ty, else_ty);
                let r_types = &[then_ty];

                let op = scf::r#if(r_c, r_types, then_region, else_region, location);
                let block_id = self.get_block_id(v);
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                lower.index.insert(v, index);
            }

            LCode::Value(_) => (),
            LCode::Noop => (),

            LCode::Builtin(bi, num_args, _num_kwargs) => {
                let arity = bi.arity();
                assert_eq!(arity, *num_args as usize);
                match bi {
                    Builtin::Import => {
                        unreachable!()
                    }
                    Builtin::Assert => {
                        let values = self.get_previous_values(v, *num_args as usize);
                        let indicies = values
                            .iter()
                            .map(|value_id| self.resolve_value(lower, *value_id).unwrap())
                            .collect();
                        let rs = blocks.values(indicies);

                        let msg = "assert";
                        //let msg = d.emit_string(error(msg, self.span));
                        let op = cf::assert(lower.context, rs[0], &msg, location);
                        let block_id = self.get_block_id(v);
                        let c = blocks.blocks.get_mut(&block_id).unwrap();
                        let index = c.push(op);
                        lower.index.insert(v, index);
                    }
                    Builtin::Print => {
                        let values = self.get_previous_values(v, *num_args as usize);
                        let indicies = values
                            .iter()
                            .map(|value_id| self.resolve_value(lower, *value_id).unwrap())
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

                        let f = FlatSymbolRefAttribute::new(lower.context, ident);
                        let op = func::call(lower.context, f, &[r], &[], location);
                        let block_id = self.get_block_id(v);
                        let c = blocks.blocks.get_mut(&block_id).unwrap();
                        let index = c.push(op);
                        lower.index.insert(v, index);
                    } //_ => unreachable!("{:?}", bi),
                }
            }

            _ => unimplemented!("{:?}", (v, code)),
        }
        Ok(())
    }

    pub fn lower_block<'c>(
        &self,
        block_id: ValueId,
        lower: &mut Lower<'c>,
        blocks: &mut LowerBlocks<'c>,
        stack: &mut Vec<ValueId>,
        b: &NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        let mut current = block_id;
        stack.push(block_id);
        loop {
            self.lower_code(lower, blocks, current, stack, b, d)?;
            if let Some(next) = self.get_next(current) {
                current = next;
            } else {
                break;
            }
        }
        blocks.blocks.get_mut(&block_id).unwrap().complete = true;
        stack.pop();
        Ok(())
    }

    pub fn lower_static_block<'c>(
        &self,
        module_block_id: ValueId,
        lower: &mut Lower<'c>,
        blocks: &mut LowerBlocks<'c>,
        stack: &mut Vec<ValueId>,
        b: &NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        // reorder things, so we lower declarations last
        let mut current = module_block_id;
        stack.push(module_block_id);
        let mut values = VecDeque::new();

        loop {
            let code = self.get_code(current);
            if let LCode::DeclareFunction(Some(_)) = code {
                values.push_back(current);
            } else {
                values.push_front(current);
            }
            if let Some(next) = self.get_next(current) {
                current = next;
            } else {
                break;
            }
        }

        for current in values {
            self.lower_code(lower, blocks, current, stack, b, d)?;
        }

        blocks.blocks.get_mut(&module_block_id).unwrap().complete = true;
        stack.pop();
        Ok(())
    }

    pub fn lower_module<'c>(
        &self,
        lower: &mut Lower<'c>,
        blocks: &mut LowerBlocks<'c>,
        module: &mut lower::Module,
        b: &NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        let module_block_id = lower.module_block_id;
        let mut stack = vec![];
        self.create_block(lower, blocks, module_block_id, d);
        self.lower_static_block(module_block_id, lower, blocks, &mut stack, b, d)?;
        let block = blocks.blocks.get_mut(&module_block_id).unwrap();
        for op in block.take_ops() {
            module.body().append_operation(op);
        }
        Ok(())
    }
}

pub fn build_declare_function<'c, E: Extra>(
    context: &'c Context,
    key: StringLabel,
    ast_ty: AstType,
    location: Location<'c>,
    b: &NodeBuilder<E>,
) -> Result<Operation<'c>> {
    if let AstType::Func(params, ast_ret_type) = ast_ty.clone() {
        let mut type_list = vec![];
        let mut ast_types = vec![];

        let attributes = vec![(
            Identifier::new(context, "sym_visibility"),
            StringAttribute::new(context, "private").into(),
        )];

        for ty in params {
            type_list.push(op::from_type(context, &ty));
            ast_types.push(ty.clone());
        }

        let region = Region::new();

        let ret_type = if let AstType::Unit = *ast_ret_type {
            vec![]
        } else {
            vec![op::from_type(context, &ast_ret_type)]
        };

        let func_type = FunctionType::new(context, &type_list, &ret_type);
        let func_name_attr = StringAttribute::new(context, &b.resolve_label(key));
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
