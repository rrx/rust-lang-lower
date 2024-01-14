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
        //let block = c.take_block();
        //let op = c.op_ref(index);
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
}

impl<'c> OpCollection<'c> {
    pub fn new(block_id: ValueId, block: Block<'c>) -> Self {
        Self {
            block_id,
            op_count: 0,
            arg_count: 0,
            block: Some(block),
            ops: vec![],
        }
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
            //let index = lower.index.get(&value_id).unwrap();
            let op = self.ops.get(index.offset()).expect("Op missing");
            let r = op.result(0).unwrap();
            //let block_id = self.get_block_id(value_id);
            //let c = blocks.blocks.get_mut(&block_id).unwrap();
            //let index = c.push(op);
            rs.push(r.into());
        }
        rs
    }
}

impl Blockify {
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
            println!("code: {:?}", (code, self.names.get(&v)));
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
        block_list: &mut Vec<ValueId>,
        block_id: ValueId,
        b: &NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        if !blocks.blocks.contains_key(&block_id) {
            self.lower_block(block_id, lower, blocks, block_list, b, d)?;
        }
        Ok(())
    }

    pub fn lower_code<'c, E: Extra>(
        &self,
        lower: &mut Lower<'c>,
        blocks: &mut LowerBlocks<'c>,
        block_list: &mut Vec<ValueId>,
        v: ValueId,
        b: &NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        let code = self.get_code(v);
        let location = Location::unknown(lower.context);

        match code {
            LCode::Label(num_args, num_kwargs) => {
                let args =
                    self.get_label_args(lower.context, v, *num_args as usize, *num_kwargs as usize);
                let block = Block::new(&args);
                let c = OpCollection::new(v, block);
                blocks.blocks.insert(v, c);
                block_list.push(v);
            }

            LCode::Arg(pos) => {
                let block_id = self.get_block_id(v);
                let index = SymIndex::Arg(block_id, *pos as usize);
                lower.index.insert(v, index);
            }

            LCode::NamedParameter(pos) => {
                let block_id = self.get_block_id(v);
                let index = SymIndex::Arg(block_id, *pos as usize);
                lower.index.insert(v, index);
            }

            LCode::Jump(target, num_args) => {
                let block_id = self.get_block_id(v);
                self.get_or_lower_block(lower, blocks, block_list, *target, b, d)?;
                let values = self.get_previous_values(v, *num_args as usize);
                let indicies = values
                    .iter()
                    .map(|value_id| lower.index.get(value_id).unwrap())
                    .cloned()
                    .collect();
                let rs = blocks.values(indicies);
                let c = blocks.blocks.get(&target).unwrap();
                let op = cf::br(&c.block.as_ref().unwrap(), &rs, location);
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
                let num = *num_args as usize;
                let values = self.get_previous_values(v, *num_args as usize);
                println!("code: {:?}", (values));
                let indicies = values
                    .iter()
                    .map(|value_id| lower.index.get(value_id).unwrap())
                    .cloned()
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
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = emit_declare_function(lower.context, c, *key, ty, location, b)?;
                lower.index.insert(v, index);
                if let Some(entry_id) = maybe_entry_id {
                    let op = blocks.op_ref(index);
                    op.set_attribute("llvm.emit_c_interface", &Attribute::unit(lower.context));
                    let mut block_list = vec![];
                    self.lower_block(*entry_id, lower, blocks, &mut block_list, b, d)?;
                    for block_id in block_list {
                        blocks.append_op(index, block_id, 0);
                    }
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
                let decl_index = lower.index.get(v_decl).unwrap();
                let value_index = lower.index.get(v_value).unwrap();
                let r_addr = blocks.value0(*decl_index);
                let r_value = blocks.value0(*value_index);

                // emit store
                // store(value, memref)
                let op = memref::store(r_value, r_addr, &[], location);

                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                lower.index.insert(v, index);
            }

            LCode::Load(v_decl) => {
                let block_id = self.get_block_id(*v_decl);
                self.get_or_lower_block(lower, blocks, block_list, block_id, b, d)?;

                let block_id = self.get_block_id(v);
                let ast_ty = self.get_type(v);
                let ty = op::from_type(lower.context, &ast_ty);

                println!("load: {:?}", (v_decl));
                let decl_index = lower.index.get(v_decl).unwrap();
                let r_addr = blocks.value0(*decl_index);
                let op = memref::load(r_addr, &[], location);
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                lower.index.insert(v, index);

                //let r_addr = blocks.values_in_scope(sym_index)[0];
                //let op = memref::load(r_addr, &[], location);
                //let current = cfg_g.node_weight_mut(current_block).unwrap();
                //let current = blocks.get_mut(&current_block).unwrap();
                //let value_index = current.push(op);
                //types.set_type(value_index, ast_ty, VarDefinitionSpace::Reg);
                //return Ok(value_index);
                //}
                //return Ok(sym_index);
            }

            LCode::Op2(op, x, y) => {
                let block_id = self.get_block_id(v);
                let x_extra = b.extra();
                let y_extra = b.extra();
                let x_index = lower.index.get(x).unwrap();
                let r_x = blocks.value0(*x_index);
                let y_index = lower.index.get(x).unwrap();
                let r_y = blocks.value0(*y_index);
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

            LCode::Ternary(condition, v_then, v_else) => {
                let then_block_id = self.get_block_id(*v_then);
                let mut then_block_list = vec![];
                self.get_or_lower_block(lower, blocks, &mut then_block_list, then_block_id, b, d)?;
                let c = blocks.blocks.get_mut(&then_block_id).unwrap();
                let r: Value<'c, '_> = c.ops.last().unwrap().result(0).unwrap().into();
                let then_ty = r.r#type();
                let op = scf::r#yield(&[r], location);
                let c = blocks.blocks.get_mut(&then_block_id).unwrap();
                c.push(op);

                let mut else_block_list = vec![];
                let else_block_id = self.get_block_id(*v_else);
                self.get_or_lower_block(lower, blocks, &mut else_block_list, else_block_id, b, d)?;
                let c = blocks.blocks.get_mut(&else_block_id).unwrap();
                let r: Value<'c, '_> = c.ops.last().unwrap().result(0).unwrap().into();
                let else_ty = r.r#type();
                let op = scf::r#yield(&[r], location);
                let c = blocks.blocks.get_mut(&else_block_id).unwrap();
                c.push(op);

                let then_region = Region::new();
                for block_id in then_block_list {
                    let block = blocks.take_block(block_id);
                    then_region.append_block(block);
                }

                let else_region = Region::new();
                for block_id in else_block_list {
                    let block = blocks.take_block(block_id);
                    else_region.append_block(block);
                }

                let c_index = lower.index.get(condition).unwrap();
                let r_c = blocks.value0(*c_index);

                //let then_ty = self.get_type(*v_then);
                //let else_ty = self.get_type(*v_else);
                assert_eq!(then_ty, else_ty);
                //let lower_ty = op::from_type(lower.context, &then_ty);
                let r_types = &[then_ty];

                println!("res: {:?}", (r_types, v_then));
                let op = scf::r#if(r_c, r_types, then_region, else_region, location);
                let block_id = self.get_block_id(v);
                let c = blocks.blocks.get_mut(&block_id).unwrap();
                let index = c.push(op);
                lower.index.insert(v, index);
            }

            LCode::Value(_) => (),

            _ => unimplemented!("{:?}", (v, code)),
        }
        Ok(())
    }

    pub fn lower_block<'c, E: Extra>(
        &self,
        block_id: ValueId,
        lower: &mut Lower<'c>,
        blocks: &mut LowerBlocks<'c>,
        block_list: &mut Vec<ValueId>,
        b: &NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        let mut current = block_id;
        loop {
            self.lower_code(lower, blocks, block_list, current, b, d)?;
            let code = self.get_code(current);
            println!("X: {:?}", (current, code));
            if let Some(next) = self.get_next(current) {
                current = next;
            } else {
                break;
            }
        }
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
        let mut block_list = vec![];
        self.lower_block(block_id, lower, blocks, &mut block_list, b, d)?;
        let block = blocks.blocks.get_mut(&block_id).unwrap();
        for op in block.take_ops() {
            module.body().append_operation(op);
        }
        Ok(())
    }
}

impl LCode {
    pub fn lower(&self) {
        //match self {
        //Self::
        //}
    }
}

pub fn emit_declare_function<'c, E: Extra>(
    context: &'c Context,
    c: &mut OpCollection<'c>,
    key: StringLabel,
    ast_ty: AstType,
    location: Location<'c>,
    b: &NodeBuilder<E>,
) -> Result<SymIndex> {
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
        let op = func::func(
            context,
            StringAttribute::new(context, &b.resolve_label(key)),
            TypeAttribute::new(func_type.into()),
            region,
            &attributes,
            location,
        );
        let index = c.push(op);
        Ok(index)
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
