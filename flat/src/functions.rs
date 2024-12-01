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

#[derive(Debug)]
pub struct FunctionVariant {
    pub ty: AstType,
    pub link_id: LinkId,
    pub block_id: BlockId,
    pub caller_blocks: HashSet<BlockId>,
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

    pub fn get(&self, variant_id: VariantId) -> &FunctionVariant {
        self.variants.get(variant_id.index()).unwrap()
    }

    pub fn get_mut(&mut self, variant_id: VariantId) -> &mut FunctionVariant {
        self.variants.get_mut(variant_id.index()).unwrap()
    }

    pub fn add(&mut self, ty: AstType, link_id: LinkId, block_id: BlockId) -> VariantId {
        let index = self.variants.len();
        self.variants.push(FunctionVariant {
            ty,
            link_id,
            block_id,
            caller_blocks: HashSet::new(),
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
        caller_blocks: HashSet<BlockId>,
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
