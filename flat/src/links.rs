use crate::{BlockId, CodeEntry};
use serde::Serialize;

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct ValueId(pub(crate) u32);

impl ValueId {
    pub fn new(index: u32) -> Self {
        Self(index)
    }
    pub fn index(&self) -> usize {
        self.0 as usize
    }
    pub fn succ(&self) -> ValueId {
        Self::new(self.index() as u32 + 1)
    }
}

impl std::fmt::Display for ValueId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "V{}", self.index())
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Serialize)]
pub struct LinkId(pub(crate) u32);

impl LinkId {
    fn new(index: usize) -> Self {
        Self(index as u32)
    }
    fn index(&self) -> usize {
        self.0 as usize
    }
}

impl std::fmt::Display for LinkId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "L{}", self.index())
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub enum CodeOffset {
    Value(ValueId),
    Link(LinkId),
    Block(BlockId),
}

impl std::fmt::Display for CodeOffset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Value(x) => write!(f, "{}", x),
            Self::Link(x) => write!(f, "{}", x),
            Self::Block(x) => write!(f, "{}", x),
        }
    }
}

impl From<&CodeOffset> for CodeOffset {
    fn from(item: &CodeOffset) -> Self {
        *item
    }
}
impl From<&LinkId> for CodeOffset {
    fn from(item: &LinkId) -> Self {
        Self::Link(*item)
    }
}

impl From<LinkId> for CodeOffset {
    fn from(item: LinkId) -> Self {
        Self::Link(item)
    }
}

impl From<ValueId> for CodeOffset {
    fn from(item: ValueId) -> Self {
        Self::Value(item)
    }
}

impl From<BlockId> for CodeOffset {
    fn from(item: BlockId) -> Self {
        Self::Block(item)
    }
}

impl From<&BlockId> for CodeOffset {
    fn from(item: &BlockId) -> Self {
        Self::Block(*item)
    }
}

pub struct Links {
    links: Vec<CodeEntry>,
}

impl Links {
    pub fn new() -> Self {
        Self { links: Vec::new() }
    }

    pub fn get(&self, link_id: LinkId) -> &CodeEntry {
        self.links.get(link_id.index()).unwrap()
    }

    pub fn get_mut(&mut self, link_id: LinkId) -> &mut CodeEntry {
        self.links.get_mut(link_id.index()).unwrap()
    }

    pub fn iter(&self) -> impl Iterator<Item = LinkId> + '_ {
        self.links.iter().map(|entry| entry.link.unwrap())
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut CodeEntry> + '_ {
        self.links.iter_mut()
    }

    pub fn insert(&mut self, mut entry: CodeEntry) -> LinkId {
        let index = self.links.len();
        let link_id = LinkId(index as u32);
        entry.link = Some(link_id);
        self.links.push(entry);
        link_id
    }
}
