#[derive(Debug, PartialEq, Clone)]
pub enum AstType {
    Int,
    Index,
    String,
    Float,
    Bool,
    Unit,
    Ptr(Box<AstType>),
    Tuple(Vec<AstType>),
    // Func(parameters, return type)
    Func(Vec<AstType>, Box<AstType>),
    //Unknown,
}

impl AstType {
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
}
