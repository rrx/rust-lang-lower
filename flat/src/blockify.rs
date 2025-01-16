use crate::{CodeOffset, LinkId};
use compile_core::StringKey;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum BlockifyError {
    #[error("BlockifyError: Unimplemented")]
    Unimplemented,
    #[error("BlockifyError: Invalid")]
    Invalid,
    #[error("BlockifyError: Incomplete")]
    Incomplete,
    #[error("BlockifyError: NotFound")]
    NotFound(String),
    #[error("BlockifyError: Template Not Found")]
    TemplateNotFound(String),
    #[error("BlockifyError: Unwind scopes: path not found")]
    UnwindNotFound(String),
}

#[derive(Debug, Clone)]
pub enum UseIndex {
    Attr(StringKey),
    Pos(usize),
    Use(CodeOffset),
}

impl UseIndex {
    pub fn offset(self) -> CodeOffset {
        match self {
            Self::Use(offset) => offset,
            _ => unimplemented!(),
        }
    }
}

impl From<LinkId> for UseIndex {
    fn from(item: LinkId) -> Self {
        Self::Use(item.into())
    }
}

impl From<&LinkId> for UseIndex {
    fn from(item: &LinkId) -> Self {
        Self::Use(item.into())
    }
}

#[derive(Debug, Clone)]
pub struct UseIndexList(Vec<UseIndex>);
impl UseIndexList {
    pub fn new(elements: Vec<UseIndex>) -> Self {
        Self(elements)
    }
    pub fn offset(self) -> CodeOffset {
        self.0.get(0).unwrap().clone().offset()
    }
}

impl From<LinkId> for UseIndexList {
    fn from(item: LinkId) -> Self {
        Self(vec![item.into()])
    }
}

impl From<&LinkId> for UseIndexList {
    fn from(item: &LinkId) -> Self {
        Self(vec![item.into()])
    }
}
