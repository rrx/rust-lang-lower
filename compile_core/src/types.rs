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
    JumpTarget,
    Args,   // *args type
    KwArgs, // **kwargs type
    Array(Box<AstType>, Vec<u64>),

    // T(a:int, b:float), T(int, float), defaults are handled as part of implementation
    // Tuples and NamedTuples are just Stucts
    Struct(Vec<(Option<StringKey>, AstType)>),
    // Unions are similar to structs, but the values hold the same space
    // Naked unions, and tagged unions are implemented as part of layout and implementation
    Union(Vec<(Option<StringKey>, AstType)>),
    Ptr(Box<AstType>),
    // Func(parameters, return type)
    Func(Box<AstType>, Box<AstType>),
    Variable(u32),
}

impl std::fmt::Display for AstType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl AstType {
    pub fn tuple(fields: Vec<Self>) -> Self {
        Self::Struct(fields.into_iter().map(|f| (None, f)).collect())
    }

    pub fn func(args: Vec<Self>, ret_type: Self) -> Self {
        let t = Self::tuple(args);
        AstType::Func(t.into(), ret_type.into())
    }

    pub fn from_str(s: &str) -> Option<AstType> {
        match s {
            "int" => Some(AstType::Int),
            _ => None,
        }
    }

    pub fn unknown(id: u32) -> Self {
        Self::Variable(id)
    }

    pub fn fields(&self) -> Vec<(Option<StringKey>, AstType)> {
        match self {
            Self::Struct(fields) => fields.clone(),
            _ => vec![],
        }
    }

    pub fn is_unknown(&self) -> bool {
        match self {
            Self::Ptr(ty) => ty.is_unknown(),
            Self::Struct(fields) | Self::Union(fields) => {
                for (_, a) in fields {
                    if a.is_unknown() {
                        return true;
                    }
                }
                false
            }
            Self::Array(element, _) => element.is_unknown(),
            Self::Func(args, ret) => {
                if ret.is_unknown() {
                    return true;
                }

                if args.is_unknown() {
                    return true;
                }
                /*
                for a in args {
                    if a.is_unknown() {
                        return true;
                    }
                }
                */
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
