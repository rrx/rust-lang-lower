use compile_core::{SpanId, Spanned};

#[derive(Debug, Clone)]
pub enum Literal {
    Bool,
    Float,
    Int,
    Null,
    Str,
}

#[derive(Debug, Clone)]
pub enum Op {
    Add,
    Sub,
    Mult,
    Div,
    Rem,

    Lt,
    Lte,
    Gt,
    Gte,

    Eq,
    Neq,
}

#[derive(Debug, Clone)]
pub enum OpType {
    IntOp,
    FloatOp,
    StrOp,

    IntOrFloatCmp,
    AnyCmp,
}

type VarDefinition = (String, Box<Expr>);

#[derive(Debug, Clone)]
pub enum LetPattern {
    Var(String),
    Record(Vec<(Spanned<String>, Box<LetPattern>)>),
}

#[derive(Debug, Clone)]
pub enum MatchPattern {
    Case(String, String),
    Wildcard(String),
}

#[derive(Debug, Clone)]
pub enum Expr {
    BinOp(Spanned<Box<Expr>>, Spanned<Box<Expr>>, OpType, Op, SpanId),
    Call(Box<Expr>, Box<Expr>, SpanId),
    Case(Spanned<String>, Box<Expr>),
    FieldAccess(Box<Expr>, String, SpanId),
    FuncDef(Spanned<(LetPattern, Box<Expr>)>),
    If(Spanned<Box<Expr>>, Box<Expr>, Box<Expr>),
    Let(VarDefinition, Box<Expr>),
    LetRec(Vec<VarDefinition>, Box<Expr>),
    Literal(Literal, Spanned<String>),
    Match(Box<Expr>, Vec<(Spanned<MatchPattern>, Box<Expr>)>, SpanId),
    NewRef(Box<Expr>, SpanId),
    Record(Option<Box<Expr>>, Vec<(Spanned<String>, Box<Expr>)>, SpanId),
    RefGet(Spanned<Box<Expr>>),
    RefSet(Spanned<Box<Expr>>, Box<Expr>),
    Typed(Box<Expr>, TypeExpr),
    Variable(Spanned<String>),
}

#[derive(Debug, Clone)]
pub enum TopLevel {
    Expr(Expr),
    LetDef(VarDefinition),
    LetRecDef(Vec<VarDefinition>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Readability {
    ReadWrite,
    ReadOnly,
    WriteOnly,
}

#[derive(Debug, Clone)]
pub enum TypeExpr {
    Alias(Box<TypeExpr>, Spanned<String>),
    Case(
        Option<Box<TypeExpr>>,
        Vec<(Spanned<String>, Box<TypeExpr>)>,
        SpanId,
    ),
    Func(Spanned<(Box<TypeExpr>, Box<TypeExpr>)>),
    Ident(Spanned<String>),
    Nullable(Box<TypeExpr>, SpanId),
    Record(
        Option<Box<TypeExpr>>,
        Vec<(Spanned<String>, Box<TypeExpr>)>,
        SpanId,
    ),
    Ref(Box<TypeExpr>, Spanned<Readability>),
    TypeVar(Spanned<String>),
}
