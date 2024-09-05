use crate::{InternKey, InternPool, InternValue, StringKey};
use serde::Serialize;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct TypeId(u32);

impl InternValue for AstType {}

impl InternKey for TypeId {
    fn index(&self) -> usize {
        self.0 as usize
    }
    fn new(index: usize) -> Self {
        Self(index as u32)
    }
}

pub type TypePool = InternPool<TypeId, AstType>;

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum AstType {
    //Number,
    Int,
    Index,
    String,
    Float,
    Bool,
    Unit,
    Never,
    Type,
    Array(Box<AstType>, Vec<u64>),
    Sum(Vec<AstType>),
    Ptr(Box<AstType>),
    Tuple(Vec<AstType>),
    NamedTuple(Vec<(StringKey, AstType)>),
    // Func(parameters, return type)
    Func(Vec<AstType>, Box<AstType>),
    Variable(u32),
}

impl std::fmt::Display for AstType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl AstType {
    pub fn unknown(id: u32) -> Self {
        Self::Variable(id)
    }

    pub fn is_unknown(&self) -> bool {
        match self {
            Self::Ptr(ty) => ty.is_unknown(),
            Self::Tuple(values) => {
                for a in values {
                    if a.is_unknown() {
                        return true;
                    }
                }
                false
            }
            Self::Func(args, ret) => {
                if ret.is_unknown() {
                    return true;
                }

                for a in args {
                    if a.is_unknown() {
                        return true;
                    }
                }
                false
            }
            Self::Variable(_) => true,
            _ => false,
        }
    }

    pub fn to_ptr(self) -> Self {
        Self::Ptr(self.into())
    }

    pub fn is_ptr(&self) -> bool {
        if let Self::Ptr(_) = self {
            true
        } else {
            false
        }
    }

    pub fn try_unknown(&self) -> Option<u32> {
        if let Self::Variable(s) = self {
            Some(*s)
        } else {
            None
        }
    }

    fn children(&self) -> Vec<&AstType> {
        match self {
            Self::Ptr(v) => vec![v],
            _ => unimplemented!(),
        }
    }
}
