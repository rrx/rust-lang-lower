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
pub enum ReturnType {
    Single(AstType),
    Multi(Vec<AstType>),
}

impl std::fmt::Display for ReturnType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Single(ty) => {
                write!(f, "S({})", ty)
            }
            Self::Multi(fields) => {
                let mut t = f.debug_tuple("M");
                for ty in fields.iter() {
                    t.field(&format!("{}", ty));
                }
                t.finish()
            }
        }
    }
}

impl ReturnType {
    pub fn is_unknown(&self) -> bool {
        match self {
            ReturnType::Single(ty) => {
                if ty.is_unknown() {
                    return true;
                }
            }
            ReturnType::Multi(types) => {
                for ty in types {
                    if ty.is_unknown() {
                        return true;
                    }
                }
            }
        }
        false
    }
}

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
    Error,
    Type,
    JumpTarget,
    Args(Box<AstType>),   // *args type
    KwArgs(Box<AstType>), // **kwargs type
    Array(Box<AstType>, Vec<usize>),

    // T(a:int, b:float), T(int, float), defaults are handled as part of implementation
    // Tuples and NamedTuples are just Stucts
    Struct(Vec<(Option<StringKey>, AstType)>),
    Tuple(Vec<AstType>),
    // Unions are similar to structs, but the values hold the same space
    // Naked unions, and tagged unions are implemented as part of layout and implementation
    Union(Vec<(Option<StringKey>, AstType)>),
    Ptr(Box<AstType>),
    // Func(parameters, return type)
    Func(Box<AstType>, Box<ReturnType>),
    TypeArg(u32),
    Variable(u32),
}

impl std::fmt::Display for AstType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Func(arg_ty, ret_ty) => {
                assert!(arg_ty.is_composite());
                write!(f, "fn({})->{}", arg_ty, ret_ty)
            }
            Self::Struct(fields) => {
                //let mut t = f.debug_struct("Struct");
                let mut t = f.debug_tuple("Struct");
                for (_index, (key, ty)) in fields.iter().enumerate() {
                    t.field(&format!("{}:{}", key.map(|k| k.index()).unwrap_or(0), ty));
                }
                t.finish()
            }
            Self::Args(ty) => {
                let mut t = f.debug_tuple("Args");
                for (_, ty) in ty.fields().iter() {
                    t.field(ty);
                }
                t.finish()
            }
            _ => write!(f, "{:?}", self),
        }
    }
}

impl AstType {
    pub fn build_struct(fields: Vec<Self>) -> Self {
        Self::Struct(fields.into_iter().map(|f| (None, f)).collect())
    }

    pub fn build_tuple(fields: Vec<Self>) -> Self {
        Self::Tuple(fields.into_iter().map(|f| f).collect())
    }

    pub fn func(args: Vec<Self>, ret_type: Self) -> Self {
        let t = Self::build_struct(args);
        AstType::Func(t.into(), ReturnType::Single(ret_type).into())
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
            Self::Args(ty) => ty.fields(),
            Self::Struct(fields) => fields.clone(),
            Self::Tuple(fields) => fields.iter().map(|f| (None, f.clone())).collect(),
            _ => vec![],
        }
    }

    pub fn is_composite(&self) -> bool {
        match self {
            Self::Union(_) => true,
            Self::Struct(_) => true,
            Self::Tuple(_) => true,
            _ => false,
        }
    }

    pub fn is_unknown(&self) -> bool {
        match self {
            Self::Ptr(ty) | Self::Args(ty) | Self::KwArgs(ty) => ty.is_unknown(),
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

    /*
    fn children(&self) -> Vec<&AstType> {
        match self {
            Self::Ptr(v) => vec![v],
            _ => unimplemented!(),
        }
    }
    */
}
