use crate::{
    AstType, IRBlockGraph, IRControlBlock, NodeIndex, StringKey, StringLabel, SymIndex,
    VarDefinitionSpace,
};
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct PlaceId(u32);

#[derive(Debug)]
pub struct PlaceNode {
    //pub(crate) block_index: NodeIndex,
    //pub(crate) index: SymIndex,
    pub(crate) name: StringLabel,
    pub(crate) static_name: Option<StringKey>,
    pub(crate) mem: VarDefinitionSpace,
    pub(crate) ty: AstType,
}

impl PlaceNode {
    pub fn new(name: StringLabel, ty: AstType, mem: VarDefinitionSpace) -> Self {
        Self {
            name,
            static_name: None,
            mem,
            ty,
        }
    }

    pub fn new_static(name: StringKey, ty: AstType) -> Self {
        Self::new(StringLabel::Intern(name), ty, VarDefinitionSpace::Static)
    }

    pub fn new_stack(name: StringLabel, ty: AstType) -> Self {
        Self::new(name, ty, VarDefinitionSpace::Stack)
    }

    pub fn new_arg(name: StringLabel, ty: AstType) -> Self {
        Self::new(name, ty, VarDefinitionSpace::Arg)
    }
}

#[derive(Debug)]
pub struct BlockNode {}

#[derive(Default)]
pub struct IRPlaceTable {
    places: Vec<PlaceNode>,
    //blocks: Vec<BlockNode>,
    //g: IRBlockGraph,
}

impl IRPlaceTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_place(&mut self, place: PlaceNode) -> PlaceId {
        let offset = self.places.len();
        self.places.push(place);
        PlaceId(offset as u32)
    }

    pub fn get_place(&self, place_id: PlaceId) -> &PlaceNode {
        self.places.get(place_id.0 as usize).unwrap()
    }

    /*
    pub fn connect_block(&mut self, source: NodeIndex, target: NodeIndex) {
        self.g.add_edge(source, target, ());
    }

    pub fn get_block(&self, block_id: NodeIndex) -> &IRControlBlock {
        self.g.node_weight(block_id).unwrap()
    }

    pub fn get_block_mut(&self, block_id: NodeIndex) -> &mut IRControlBlock {
        self.g.node_weight_mut(block_id).unwrap()
    }

    pub fn add_definition(
        &mut self,
        block_index: NodeIndex,
        place_id: PlaceId,
        name: StringKey,
    ) -> SymIndex {
        let data = self.g.node_weight_mut(block_index).unwrap();
        let index = data.add_definition(place_id);
        data.alloca_add(place_id, name, index);
        self.places.insert(place_id, index);
        //data.add_symbol(name, index);
        index
    }
    */
}
