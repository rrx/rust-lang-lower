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
use lower::{op, AstType, Extra, NodeBuilder, StringKey, StringLabel};
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

    pub fn values(&self, values: Vec<SymIndex>) -> Vec<Value<'c, '_>> {
        let mut rs = vec![];
        for index in values {
            let c = self.blocks.get(&index.block()).unwrap();
            let r: Value<'c, '_> = match index {
                SymIndex::Op(_, pos) => {
                    let op = c.ops.get(pos).expect("Op missing");
                    op.result(0).unwrap().into()
                }
                SymIndex::Arg(_, pos) => c.block.as_ref().unwrap().argument(pos).unwrap().into(),
                _ => unimplemented!(),
            };
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
    ) -> Result<()> {
        if !blocks.blocks.contains_key(&block_id) {
            self.lower_block(block_id, lower, blocks, block_list, b)?;
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

            LCode::Jump(target, num_args) => {
                let block_id = self.get_block_id(v);
                self.get_or_lower_block(lower, blocks, block_list, *target, b)?;
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
                    self.lower_block(*entry_id, lower, blocks, &mut block_list, b)?;
                    for block_id in block_list {
                        blocks.append_op(index, block_id, 0);
                    }
                }
            }
            _ => (),
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
    ) -> Result<()> {
        let mut current = block_id;
        loop {
            self.lower_code(lower, blocks, block_list, current, b)?;
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
    ) -> Result<()> {
        let block_id = ValueId(0);
        let mut block_list = vec![];
        self.lower_block(block_id, lower, blocks, &mut block_list, b)?;
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
