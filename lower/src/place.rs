use crate::{AstType, NodeIndex, StringKey, SymIndex, VarDefinitionSpace};
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct PlaceId(u32);

#[derive(Debug)]
pub struct PlaceNode {
    //pub(crate) block_index: NodeIndex,
    //pub(crate) index: SymIndex,
    pub(crate) name: StringKey,
    pub(crate) static_name: Option<StringKey>,
    pub(crate) mem: VarDefinitionSpace,
    pub(crate) ty: AstType,
}

impl PlaceNode {
    pub fn new(name: StringKey, ty: AstType, mem: VarDefinitionSpace) -> Self {
        Self {
            name,
            static_name: None,
            mem,
            ty,
        }
    }

    pub fn new_static(name: StringKey, ty: AstType) -> Self {
        Self::new(name, ty, VarDefinitionSpace::Static)
    }

    pub fn new_stack(name: StringKey, ty: AstType) -> Self {
        Self::new(name, ty, VarDefinitionSpace::Stack)
    }

    pub fn new_arg(name: StringKey, ty: AstType) -> Self {
        Self::new(name, ty, VarDefinitionSpace::Arg)
    }
}

#[derive(Default)]
pub struct IRPlaceTable {
    places: Vec<PlaceNode>,
}

impl IRPlaceTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(&mut self, place: PlaceNode) -> PlaceId {
        let offset = self.places.len();
        self.places.push(place);
        PlaceId(offset as u32)
    }

    pub fn get(&self, place_id: PlaceId) -> &PlaceNode {
        self.places.get(place_id.0 as usize).unwrap()
    }
}
