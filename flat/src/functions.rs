use crate::{ArgVec, BlockId, LinkId, NodeBuilder, StringLabel, ValueId};
use compile_core::{AbstractionId, Argument, AstType, Lambda, SpanId, StringKey};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct VariantId(u32);
impl std::fmt::Display for VariantId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "V{}", self.0)
    }
}

impl VariantId {
    pub fn new(index: usize) -> Self {
        Self(index as u32)
    }
    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone)]
pub struct Caller {
    pub block_id: BlockId,
    pub link_id: LinkId,
    pub args: Vec<LinkId>,
}

#[derive(Debug)]
pub struct FunctionVariant {
    pub ty: AstType,
    pub link_id: LinkId,
    pub block_id: BlockId,
    pub name: StringKey,
    pub caller_blocks: HashMap<BlockId, Caller>,
}

impl FunctionVariant {
    pub fn block_index(&self, block_id: &BlockId) -> i64 {
        let mut blocks = self
            .caller_blocks
            .clone()
            .into_iter()
            .map(|(block_id, _)| block_id)
            .collect::<Vec<_>>();
        blocks.sort();
        let index = blocks.iter().position(|&x| x == *block_id).unwrap();
        index as i64
    }
}

#[derive(Debug)]
pub struct VariantIterator {
    index: usize,
    len: usize,
}

impl VariantIterator {
    pub fn new(len: usize) -> Self {
        Self { index: 0, len }
    }
}

impl Iterator for VariantIterator {
    type Item = VariantId;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.len {
            let index = self.index;
            self.index += 1;
            Some(VariantId::new(index))
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct FunctionVariantBuilder {
    pub variants: Vec<FunctionVariant>,
    pub block_lookup: HashMap<BlockId, VariantId>,
}

impl FunctionVariantBuilder {
    pub fn new() -> Self {
        Self {
            variants: vec![],
            block_lookup: HashMap::new(),
        }
    }

    pub fn iter(&self) -> VariantIterator {
        VariantIterator::new(self.variants.len())
    }

    pub fn get_by_block(&self, block_id: BlockId) -> Option<VariantId> {
        if let Some(variant_id) = self.block_lookup.get(&block_id) {
            Some(*variant_id)
        } else {
            None
        }
    }

    pub fn get(&self, variant_id: VariantId) -> &FunctionVariant {
        self.variants.get(variant_id.index()).unwrap()
    }

    pub fn get_mut(&mut self, variant_id: VariantId) -> &mut FunctionVariant {
        self.variants.get_mut(variant_id.index()).unwrap()
    }

    pub fn add_caller(
        &mut self,
        variant_id: VariantId,
        block_id: BlockId,
        goto_link_id: LinkId,
        args: Vec<LinkId>,
    ) {
        let v = self.get_mut(variant_id);
        v.caller_blocks.insert(
            block_id,
            Caller {
                block_id,
                link_id: goto_link_id,
                args,
            },
        );
    }

    pub fn add(
        &mut self,
        ty: AstType,
        link_id: LinkId,
        block_id: BlockId,
        name: StringKey,
    ) -> VariantId {
        let index = self.variants.len();
        self.variants.push(FunctionVariant {
            ty,
            link_id,
            block_id,
            name,
            caller_blocks: HashMap::new(),
        });
        let variant_id = VariantId(index as u32);
        self.block_lookup.insert(block_id, variant_id);
        variant_id
    }

    pub fn update_type(&mut self, variant_id: VariantId, ty: AstType) {
        let v = self.variants.get_mut(variant_id.index()).unwrap();
        v.ty = ty;
    }

    pub fn update(
        &mut self,
        variant_id: VariantId,
        ty: AstType,
        link_id: LinkId,
        caller_blocks: HashMap<BlockId, Caller>,
    ) {
        let v = self.variants.get_mut(variant_id.index()).unwrap();
        v.ty = ty;
        v.link_id = link_id;
        v.caller_blocks = caller_blocks;
    }
}

#[derive(Debug)]
pub struct Abstraction {
    pub def: Lambda,
    pub def_span_id: SpanId,
    pub caller_blocks: HashSet<BlockId>,
}

#[derive(Debug)]
pub struct AbstractionsBuilder(Vec<Abstraction>);

impl AbstractionsBuilder {
    pub fn new() -> Self {
        Self(vec![])
    }

    pub fn get(&self, abstraction_id: AbstractionId) -> &Abstraction {
        self.0.get(abstraction_id.index()).unwrap()
    }

    pub fn get_mut(&mut self, abstraction_id: AbstractionId) -> &mut Abstraction {
        self.0.get_mut(abstraction_id.index()).unwrap()
    }

    pub fn add(&mut self, def: Lambda, def_span_id: SpanId) -> AbstractionId {
        let index = self.0.len();
        self.0.push(Abstraction {
            def,
            def_span_id,
            caller_blocks: HashSet::new(),
        });
        AbstractionId::new(index)
    }
}
