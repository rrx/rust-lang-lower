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
            FloatAttribute,
            IntegerAttribute,
            StringAttribute,
            TypeAttribute,
        },
        r#type::{FunctionType, IntegerType, MemRefType, RankedTensorType},
        Attribute, Block, Identifier, Operation, Region, Type, TypeLike, Value, ValueLike,
    },
    Context,
};
use lower::{op, AstType, Diagnostics, Extra, NodeBuilder, StringKey, StringLabel};
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
        //println!("b:{:?}", block_id);
        //println!("x:{:?}", op);
    }

    pub fn value0(&self, index: SymIndex) -> Value<'c, '_> {
        //println!("value0: {:?}", index);
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
            /*
            let c = self.blocks.get(&index.block()).unwrap();
            let r: Value<'c, '_> = match index {
                SymIndex::Op(_, pos) => {
                    let op = c.ops.get(pos).expect("Op missing");
                    op.result(0).unwrap().into()
                }
                SymIndex::Arg(_, pos) => c.block.as_ref().unwrap().argument(pos).unwrap().into(),
                _ => unimplemented!(),
            };
            */
            rs.push(r);
        }
        rs
    }
}

pub struct Lower<'c> {
    context: &'c Context,
    index: IndexMap<ValueId, SymIndex>,
}

impl<'c> Lower<'c> {
    pub fn new(context: &'c Context) -> Self {
        Self {
            context,
            index: IndexMap::new(),
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
        //self.symbols.clear();
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

impl Blockify {
    pub fn resolve_value<'c>(&self, lower: &Lower<'c>, value_id: ValueId) -> Option<SymIndex> {
        let mut current = value_id;
        loop {
            let code = self.get_code(current);
            if let LCode::Value(next_value_id) = code {
                current = *next_value_id;
                continue;
            } else {
                break;
            }
        }
        lower.index.get(&current).cloned()
    }

    pub fn get_label_args<'c>(
        &self,
        context: &'c Context,
        v: ValueId,
        num_args: usize,
        num_kwargs: usize,
    ) -> Vec<(Type<'c>, Location<'c>)> {
        let mut current = v;
        let mut out = vec![];
        for i in 0..num_args {
            let next = self.get_next(current).unwrap();
            let ty = op::from_type(context, &self.get_type(next));
            current = next;
            out.push((ty, Location::unknown(context)));
        }
        for i in 0..num_kwargs {
            let next = self.get_next(current).unwrap();
            let ty = op::from_type(context, &self.get_type(next));
            current = next;
            out.push((ty, Location::unknown(context)));
        }
        out
    }

    pub fn get_previous_values(&self, v: ValueId, num: usize) -> Vec<ValueId> {
        let mut values = vec![];
        for i in 0..num {
            let v = ValueId((v.0 as usize - num + i) as u32);
            let code = self.get_code(v);
            //println!("code: {:?}", (code, self.names.get(&v)));
            //blocks.blocks.get(
            if let LCode::Value(value_id) = code {
                values.push(*value_id);
            }
        }
        values
    }

    pub fn get_or_lower_block<'c, E: Extra>(
        &self,
        lower: &mut Lower<'c>,
        blocks: &mut LowerBlocks<'c>,
        v: ValueId,
        block_id: ValueId,
        stack: &mut Vec<ValueId>,
        b: &NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        assert!(blocks.blocks.contains_key(&block_id));
        let from_block_id = self.get_block_id(v);

        if stack.contains(&block_id) {
            return Ok(());
        }

        if !blocks.blocks.get(&block_id).unwrap().is_complete() {
            self.lower_block(block_id, lower, blocks, stack, b, d)?;
        }
        Ok(())
    }

    pub fn create_block<'c>(
        &self,
        lower: &mut Lower<'c>,
        blocks: &mut LowerBlocks<'c>,
        block_id: ValueId,
    ) {
        let code = self.get_code(block_id);
        if let LCode::Label(num_args, num_kwargs) = code {
            let args = self.get_label_args(
                lower.context,
                block_id,
                *num_args as usize,
                *num_kwargs as usize,
            );
            let block = Block::new(&args);
            let c = OpCollection::new(block_id, block);
            blocks.blocks.insert(block_id, c);
        } else {
            unreachable!()
        }
    }

    pub fn lower_code<'c, E: Extra>(
        &self,
        lower: &mut Lower<'c>,
        blocks: &mut LowerBlocks<'c>,
        v: ValueId,
        stack: &mut Vec<ValueId>,
        b: &NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        let code = self.get_code(v);
        let location = Location::unknown(lower.context);
        //println!("lower: {:?}", (v, self.code_to_string(v, b)));

        match code {
            LCode::Label(_num_args, _num_kwargs) => {
                assert!(blocks.blocks.get(&v).is_some());
                //let args =
                //self.get_label_args(lower.context, v, *num_args as usize, *num_kwargs as usize);
                //let block = Block::new(&args);
                //let c = OpCollection::new(v, block);
                //blocks.blocks.insert(v, c);
                //block_list.push(v);
            }

            LCode::Arg(pos) | LCode::NamedParameter(pos) => {
                let block_id = self.get_block_id(v);
                let index = SymIndex::Arg(block_id, *pos as usize);
                lower.index.insert(v, index);
            }

            LCode::Jump(target, num_args) => {
                let block_id = self.get_block_id(v);
                self.get_or_lower_block(lower, blocks, v, *target, stack, b, d)?;
                let values = self.get_previous_values(v, *num_args as usize);
                //println!("jump: {:?}", (values));
                let indicies = values
                    .iter()
                    .map(|value_id| self.resolve_value(lower, *value_id).unwrap())
                    .collect();
                let rs = blocks.values(indicies);

                let c = blocks.blocks.get(&target).unwrap();
                let arg_count = c.block.as_ref().unwrap().argument_count();
                assert_eq!(arg_count, *num_args as usize);

                //println!("jump: {:?}", (&c.block.as_ref().unwrap(), &rs));
                let op = cf::br(&c.block.as_ref().unwrap(), &rs, location);
                //println!("jump: {:?}", op);
                let c = blocks.blocks.get_mut(&block_id).unwrap();

                let index = c.push(op);
                lower.index.insert(v, index);
            }

            LCode::Const(lit) => {
                let block_id = self.get_block_id(v);
                let (op, ast_ty) = op::emit_literal_const(lower.context, lit, location);
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                lower.index.insert(v, index);
            }

            LCode::Return(num_args) => {
                //let op = func::r#return(&[], location);
                //let block_id = self.get_block_id(v);
                //let c = blocks.blocks.get_mut(&block_id).unwrap();
                //let index = c.push(op);
                //lower.index.insert(v, index);
                //return Ok(());
                let num = *num_args as usize;
                let values = self.get_previous_values(v, *num_args as usize);
                //println!("code: {:?}", (values));
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
                let block_id = self.get_block_id(v);
                let key = self.names.get(&v).unwrap();
                let ty = self.get_type(v);

                //println!("declare");
                let op = build_declare_function(lower.context, *key, ty, location, b)?;
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                lower.index.insert(v, index);

                if let Some(entry_id) = maybe_entry_id {
                    let scope_id = self.get_scope_id(*entry_id);
                    let scope = self.env.get_scope(scope_id);
                    // create blocks
                    //println!("body");
                    for block_id in scope.blocks.iter() {
                        self.create_block(lower, blocks, *block_id);
                    }

                    for block_id in scope.blocks.iter() {
                        self.get_or_lower_block(lower, blocks, v, *block_id, stack, b, d)?;
                    }
                    let op = blocks.op_ref(index);
                    op.set_attribute("llvm.emit_c_interface", &Attribute::unit(lower.context));

                    //println!("body:{:?}", op);

                    for block_id in scope.blocks.iter() {
                        blocks.append_op(index, *block_id, 0);
                    }
                }
            }

            LCode::Call(v_f, args, _kwargs) => {
                // function to call
                let key = self.get_name(*v_f);
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

                    let op = func::call(lower.context, f, &rs, &[ret_type.clone()], location);

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
                /*
                let block_id = self.get_block_id(*v_decl);
                self.get_or_lower_block(lower, blocks, block_list, block_id, b)?;
                let block_id = self.get_block_id(*v_value);
                self.get_or_lower_block(lower, blocks, block_list, block_id, b)?;
                */

                //let lhs_ty = self.get_type(*v_decl);
                //let rhs_ty = self.get_type(*v_value);
                let decl_index = self.resolve_value(lower, *v_decl).unwrap();
                let value_index = self.resolve_value(lower, *v_value).unwrap();
                let r_addr = blocks.value0(decl_index);
                let r_value = blocks.value0(value_index);

                // emit store
                // store(value, memref)
                let op = memref::store(r_value, r_addr, &[], location);

                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                lower.index.insert(v, index);
            }

            LCode::Load(v_decl) => {
                let block_id = self.get_block_id(*v_decl);
                self.get_or_lower_block(lower, blocks, v, block_id, stack, b, d)?;

                let block_id = self.get_block_id(v);
                let ast_ty = self.get_type(v);
                let ty = op::from_type(lower.context, &ast_ty);

                let decl_index = self.resolve_value(lower, *v_decl).unwrap();
                let r_addr = blocks.value0(decl_index);
                //println!("load: {:?}", (v_decl, decl_index, r_addr));
                let op = memref::load(r_addr, &[], location);
                //println!("loadop: {:?}", (op));
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                lower.index.insert(v, index);
            }

            LCode::Op2(op, x, y) => {
                let block_id = self.get_block_id(v);
                let x_extra = b.extra();
                let y_extra = b.extra();
                let x_index = self.resolve_value(lower, *x).unwrap();
                let r_x = blocks.value0(x_index);
                let y_index = self.resolve_value(lower, *y).unwrap();
                let r_y = blocks.value0(y_index);
                let (op, ast_ty) = op::build_binop(
                    lower.context,
                    op.clone(),
                    r_x,
                    &x_extra,
                    r_y,
                    &y_extra,
                    location,
                    d,
                )?;
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                lower.index.insert(v, index);
            }

            LCode::Branch(condition, v_then, v_else) => {
                let then_block_id = self.get_block_id(*v_then);
                self.get_or_lower_block(lower, blocks, v, then_block_id, stack, b, d)?;

                let else_block_id = self.get_block_id(*v_else);
                self.get_or_lower_block(lower, blocks, v, else_block_id, stack, b, d)?;

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
                let block_id = self.get_block_id(v);
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                lower.index.insert(v, index);
            }

            LCode::Ternary(condition, v_then, v_else) => {
                let then_block_id = self.get_block_id(*v_then);
                let scope_id = self.get_scope_id(*v_then);
                let then_scope = self.env.get_scope(scope_id);
                for block_id in then_scope.blocks.iter() {
                    self.create_block(lower, blocks, *block_id);
                }
                for block_id in then_scope.blocks.iter() {
                    self.get_or_lower_block(lower, blocks, v, *block_id, stack, b, d)?;
                }

                let c = blocks.blocks.get_mut(&then_block_id).unwrap();
                let r: Value<'c, '_> = c.ops.last().unwrap().result(0).unwrap().into();
                let then_ty = r.r#type();
                let op = scf::r#yield(&[r], location);
                let c = blocks.blocks.get_mut(&then_block_id).unwrap();
                c.push(op);

                let else_block_id = self.get_block_id(*v_else);
                let scope_id = self.get_scope_id(*v_else);
                let else_scope = self.env.get_scope(scope_id);
                for block_id in else_scope.blocks.iter() {
                    self.create_block(lower, blocks, *block_id);
                }
                for block_id in else_scope.blocks.iter() {
                    self.get_or_lower_block(lower, blocks, v, *block_id, stack, b, d)?;
                }
                let c = blocks.blocks.get_mut(&else_block_id).unwrap();
                let r: Value<'c, '_> = c.ops.last().unwrap().result(0).unwrap().into();
                let else_ty = r.r#type();
                let op = scf::r#yield(&[r], location);
                let c = blocks.blocks.get_mut(&else_block_id).unwrap();
                c.push(op);

                let then_region = Region::new();
                for block_id in then_scope.blocks.iter() {
                    let block = blocks.take_block(*block_id);
                    then_region.append_block(block);
                }

                let else_region = Region::new();
                for block_id in else_scope.blocks.iter() {
                    let block = blocks.take_block(*block_id);
                    else_region.append_block(block);
                }

                let c_index = self.resolve_value(lower, *condition).unwrap();
                let r_c = blocks.value0(c_index);

                assert_eq!(then_ty, else_ty);
                let r_types = &[then_ty];

                //println!("res: {:?}", (r_types, v_then));
                let op = scf::r#if(r_c, r_types, then_region, else_region, location);
                let block_id = self.get_block_id(v);
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                lower.index.insert(v, index);
            }

            LCode::Value(_) => (),

            _ => unimplemented!("{:?}", (v, code)),
        }
        //println!("f: {:?}", (v, code));
        Ok(())
    }

    pub fn lower_block<'c, E: Extra>(
        &self,
        block_id: ValueId,
        lower: &mut Lower<'c>,
        blocks: &mut LowerBlocks<'c>,
        stack: &mut Vec<ValueId>,
        b: &NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        //println!("lowering block {:?}", block_id);
        let mut current = block_id;
        stack.push(block_id);
        loop {
            self.lower_code(lower, blocks, current, stack, b, d)?;
            //let code = self.get_code(current);
            //println!("X: {:?}", (current, code));
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

    pub fn lower_module<'c, E: Extra>(
        &self,
        lower: &mut Lower<'c>,
        blocks: &mut LowerBlocks<'c>,
        module: &mut lower::Module,
        b: &NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        let block_id = ValueId(0);
        let mut stack = vec![];
        self.create_block(lower, blocks, block_id);
        self.lower_block(block_id, lower, blocks, &mut stack, b, d)?;
        //println!("finished lower module");
        let block = blocks.blocks.get_mut(&block_id).unwrap();
        for op in block.take_ops() {
            //println!("op: {:?}", op);
            module.body().append_operation(op);
        }
        //println!("finished lower module:{:?}", module);
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

        //println!(
        //"func: {:?}",
        //(func_name_attr, func_ty_attr, &region, &attributes)
        //);
        let op = func::func(
            context,
            func_name_attr,
            func_ty_attr,
            region,
            &attributes,
            location,
        );
        //println!("func: {:?}", op);
        Ok(op)
    } else {
        unreachable!()
    }
}

/*
pub fn emit_set_function<'c, E: Extra>(
    context: &'c Context,
    //place: &mut IRPlaceTable,
    sym_index: SymIndex,
    expr: IRNode,
    //current_block: NodeIndex,
    //types: &mut TypeBuilder,
    //blocks: &mut CFGBlocks<'c>,
    //stack: &mut Vec<NodeIndex>,
    //d: &mut Diagnostics,
    b: &mut NodeBuilder<E>,
    //link: &mut LinkOptions,
) -> Result<SymIndex> {
    match expr.kind {
        IRKind::Func(func_blocks, _ast_ty) => {
            let mut block_seq = vec![];

            // create blocks, so they can be referenced when lowering
            for (i, block) in func_blocks.into_iter().enumerate() {
                let block_index = blocks.update_block_ir(
                    context,
                    block.index,
                    block.label,
                    &block.params,
                    types,
                    d,
                    //cfg_g,
                );
                if 0 == i {
                    //cfg_g.add_edge(current_block, block_index, ());
                }
                block_seq.push((block, block_index));
            }

            // lower to mlir
            let mut block_indicies = vec![];
            for (block, block_index) in block_seq.into_iter() {
                block_indicies.push(block_index);

                for c in block.children.into_iter() {
                    stack.push(block_index);
                    if let Ok(_index) =
                        c.lower_mlir(context, place, d, types, blocks, stack, b, link)
                    {
                        stack.pop();
                    } else {
                        stack.pop();
                        return Err(Error::new(ParseError::Invalid));
                    }
                }
            }

            // build region and add it to the declared function
            for block_index in block_indicies {
                let block = blocks.take_block(block_index);
                let current = blocks.get_mut(&current_block).unwrap();
                let op = current.op_ref(sym_index);
                op.region(0).unwrap().append_block(block);
            }

            let current = blocks.get_mut(&current_block).unwrap();
            let op = current.op_ref(sym_index);
            op.set_attribute("llvm.emit_c_interface", &Attribute::unit(context));

            Ok(sym_index)
        }
        _ => unreachable!(),
    }
}

*/
