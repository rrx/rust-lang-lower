use crate::{BlockId, LinkId, NodeBuilder};
use compile_core::{AstType, StringKey};

use std::collections::HashMap;

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
    pub name: StringKey,
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
        });
        let variant_id = VariantId(index as u32);
        self.block_lookup.insert(block_id, variant_id);
        variant_id
    }

    pub fn dump_variants(&self, b: &NodeBuilder) {
        for (index, v) in self.variants.iter().enumerate() {
            let variant_id = VariantId::new(index);
            let name = b.labels.r(v.name.into());
            println!("[{}] Variant: {:?}", variant_id, (name, v));
        }
    }
}
