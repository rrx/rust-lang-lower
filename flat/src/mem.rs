use crate::LinkId;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum VarDefinitionSpace {
    Arg,
    Reg,
    Static,
    Stack(LinkId),
    Heap,
    Default,
}

impl Default for VarDefinitionSpace {
    fn default() -> Self {
        Self::Default
    }
}

impl VarDefinitionSpace {
    pub fn is_static(&self) -> bool {
        match self {
            Self::Static => true,
            _ => false,
        }
    }

    pub fn requires_deref(&self) -> bool {
        match self {
            Self::Static | Self::Stack(_) | Self::Heap => true,
            _ => false,
        }
    }
}

impl std::fmt::Display for VarDefinitionSpace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VarDefinitionSpace::Arg => write!(f, "Marg"),
            VarDefinitionSpace::Reg => write!(f, "Mreg"),
            VarDefinitionSpace::Static => write!(f, "Mstatic"),
            VarDefinitionSpace::Stack(x) => write!(f, "Mstack(L{})", x.index()),
            VarDefinitionSpace::Heap => write!(f, "Mheap"),
            VarDefinitionSpace::Default => write!(f, "Mdef"),
        }
    }
}
