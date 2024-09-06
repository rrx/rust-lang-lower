#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct ValueId(pub(crate) u32);

impl ValueId {
    pub fn new(index: u32) -> Self {
        Self(index)
    }
    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

impl std::fmt::Display for ValueId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "V{}", self.index())
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct BlockId(pub(crate) u32);

impl BlockId {
    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

impl std::fmt::Display for BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "B{}", self.index())
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct LinkId(pub(crate) u32);

impl LinkId {
    pub fn index(&self) -> usize {
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

