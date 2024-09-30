use std::collections::HashMap;

use crate::{BlockId, LinkId, NodeBuilder, StringLabel, ValueId};
use compile_core::{AstType, StringKey};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Successor {
    BlockScope,
    Operation,
    Jump,
    FunctionDeclaration,
    TemplateDeclaration,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ScopeType {
    Static,
    Function,
    Template,
    Block,
    Region,
    Loop,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct ScopeId(pub(crate) u32);
impl std::fmt::Display for ScopeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl ScopeId {
    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy)]
pub struct LoopScope {
    pub(crate) name: Option<StringKey>,
    pub(crate) next_block: BlockId,
    pub(crate) start_block: BlockId,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct TemplateId(pub(crate) u32);
impl TemplateId {
    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct VariantId(pub(crate) u32);
impl std::fmt::Display for VariantId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "V{}", self.0)
    }
}

impl VariantId {
    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug)]
pub struct FunctionVariant {
    pub ty: AstType,
    pub link_id: LinkId,
}

#[derive(Debug)]
pub struct FunctionVariantBuilder {
    pub variants: Vec<FunctionVariant>,
}

impl FunctionVariantBuilder {
    pub fn new() -> Self {
        Self { variants: vec![] }
    }

    pub fn add(&mut self, ty: AstType, link_id: LinkId) -> VariantId {
        let index = self.variants.len();
        self.variants.push(FunctionVariant { ty, link_id });
        VariantId(index as u32)
    }

    pub fn update_type(&mut self, variant_id: VariantId, ty: AstType) {
        let v = self.variants.get_mut(variant_id.index()).unwrap();
        v.ty = ty;
    }

    pub fn update(&mut self, variant_id: VariantId, ty: AstType, link_id: LinkId) {
        let v = self.variants.get_mut(variant_id.index()).unwrap();
        v.ty = ty;
        v.link_id = link_id;
    }
}

#[derive(Debug)]
pub struct ScopeLayer {
    pub names: HashMap<StringKey, LinkId>,
    pub entries: HashMap<StringKey, FunctionVariantBuilder>,
    pub declarations: HashMap<StringKey, LinkId>,
    pub labels: HashMap<StringLabel, ValueId>,
    pub(crate) block_labels: HashMap<StringLabel, BlockId>,
    pub blocks: Vec<ValueId>,
    pub entry_block: Option<BlockId>,
    pub return_block: Option<BlockId>,
    pub next_block: Vec<ValueId>,
    pub(crate) loop_block: Option<LoopScope>,
    pub scope_type: ScopeType,
    pub lambdas: HashMap<StringLabel, TemplateId>,
    pub templates: HashMap<StringKey, LinkId>,
}

impl ScopeLayer {
    pub fn new(scope_type: ScopeType) -> Self {
        Self {
            labels: HashMap::new(),
            block_labels: HashMap::new(),
            blocks: vec![],
            names: HashMap::new(),
            entries: HashMap::new(),
            declarations: HashMap::new(),
            entry_block: None,
            return_block: None,
            next_block: vec![],
            loop_block: None,
            scope_type,
            lambdas: HashMap::new(),
            templates: HashMap::new(),
        }
    }

    pub fn variant_add(&mut self, name: StringKey, ty: AstType, link_id: LinkId) -> VariantId {
        if !self.entries.contains_key(&name) {
            self.entries.insert(name, FunctionVariantBuilder::new());
        }
        let v = self.entries.get_mut(&name).unwrap();
        v.add(ty, link_id)
    }

    pub fn variant_update(
        &mut self,
        name: StringKey,
        variant_id: VariantId,
        ty: AstType,
        link_id: LinkId,
    ) {
        let v = self.entries.get_mut(&name).unwrap();
        v.update(variant_id, ty, link_id)
    }

    pub fn lookup(&self, name: StringKey) -> Option<LinkId> {
        self.names.get(&name).cloned()
    }

    pub fn dump(&self, b: &NodeBuilder) {
        println!("Scope: {:?}", self.scope_type);
        for (k, v) in self.labels.iter() {
            let s = b.labels.r(*k);
            println!("Label: {}:{:?}", s, v);
        }
        for (k, v) in self.entries.iter() {
            let name = b.labels.r((*k).into());
            for v in v.variants.iter() {
                println!("Entry: {}:{}:{}", name, v.ty, v.link_id);
            }
        }
    }
}
