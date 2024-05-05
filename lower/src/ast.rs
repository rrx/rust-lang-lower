use crate::Diagnostics;
use crate::{AstType, CodeLocation, NodeBuilder, Span, SpanId, StringKey};
use codespan_reporting::diagnostic::{Diagnostic, Label};
use melior::{ir::Location, Context};
use std::fmt::Debug;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum VarDefinitionSpace {
    Arg,
    Reg,
    Static,
    Stack,
    Heap,
    Default,
}

impl Default for VarDefinitionSpace {
    fn default() -> Self {
        Self::Default
    }
}

impl VarDefinitionSpace {
    pub fn requires_deref(&self) -> bool {
        match self {
            Self::Static | Self::Stack | Self::Heap => true,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct VarDefinition {
    ty: AstType,
    space: VarDefinitionSpace,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum DefinitionId {
    Var(u32),
    Arg(u32),
}

#[derive(Debug, Clone)]
pub enum Literal {
    Int(i64),
    Index(usize),
    Float(f64),
    String(String),
    Bool(bool),
    Type(AstType),
}

impl From<Literal> for AstType {
    fn from(item: Literal) -> Self {
        From::from(&item)
    }
}

impl From<&Literal> for AstType {
    fn from(item: &Literal) -> Self {
        match item {
            Literal::Int(_) => AstType::Int,
            Literal::Float(_) => AstType::Float,
            Literal::Bool(_) => AstType::Bool,
            Literal::Index(_) => AstType::Index,
            Literal::String(_) => AstType::String,
            Literal::Type(_) => AstType::Type,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum UnaryOperation {
    Minus,
}

#[derive(Debug, Clone, Copy)]
pub enum BinaryOperation {
    Add,
    Subtract,
    Multiply,
    Divide,
    NE,
    EQ,
    GT,
    GTE,
}

#[derive(Debug, Clone)]
pub struct BinOpNode {
    pub node: BinaryOperation,
    span_id: SpanId,
}

impl BinOpNode {
    pub fn new(node: BinaryOperation, span_id: SpanId) -> Self {
        Self { node, span_id }
    }
}

#[derive(Debug, Clone)]
pub enum Argument {
    Positional(Box<AstNode>),
}

impl From<AstNode> for Argument {
    fn from(item: AstNode) -> Self {
        Argument::Positional(item.into())
    }
}

impl Argument {
    pub fn try_string(self) -> Option<String> {
        let Self::Positional(node) = self;
        (*node).try_string()
    }
}

#[derive(Debug, Clone)]
pub enum Parameter {
    Normal,
    //WithDefault(AstNode),
    //Dummy<std::marker::PhantomData//(AstNode),
}

#[derive(Debug, Clone)]
pub struct ParameterNode {
    pub name: StringKey,
    pub ty: AstType,
    pub node: Parameter,
    pub span_id: SpanId,
}

#[derive(Debug, Clone)]
pub struct Definition {
    pub params: Vec<ParameterNode>,
    pub return_type: Box<AstType>,
    pub body: Option<Box<AstNode>>,
}

#[derive(Debug, Clone)]
pub enum Builtin {
    Assert,
    Print,
    Import,
}

impl Builtin {
    pub fn from_name(name: &str) -> Option<Builtin> {
        if name == "check" {
            Some(Builtin::Assert)
        } else if name == "print" {
            Some(Builtin::Print)
        } else if name == "use" {
            Some(Builtin::Import)
        } else {
            None
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            Self::Assert => 1,
            Self::Print => 1,
            Self::Import => 1,
        }
    }

    pub fn get_return_type(&self) -> AstType {
        AstType::Unit
    }
}

#[derive(Debug, Clone)]
pub enum DerefTarget {
    Offset(usize),
    Field(String),
}

#[derive(Debug)]
pub enum Terminator {
    Jump(StringKey),
    Branch(StringKey, StringKey),
    Return,
}

#[derive(Debug, Clone)]
pub enum Ast {
    BinaryOp(BinOpNode, Box<AstNode>, Box<AstNode>),
    UnaryOp(UnaryOperation, Box<AstNode>),
    Call(Box<AstNode>, Vec<Argument>, AstType),
    Identifier(StringKey),
    Literal(Literal),
    Sequence(Vec<AstNode>),
    Definition(Definition),
    Global(StringKey, Box<AstNode>),
    Assign(AssignTarget, Box<AstNode>),
    Branch(Box<AstNode>, StringKey, StringKey),
    Conditional(Box<AstNode>, Box<AstNode>, Option<Box<AstNode>>),
    Ternary(Box<AstNode>, Box<AstNode>, Box<AstNode>),
    Return(Option<Box<AstNode>>),
    While(Box<AstNode>, Box<AstNode>),
    Builtin(Builtin, Vec<Argument>),
    Module(StringKey, Box<AstNode>),
    Loop(StringKey, Box<AstNode>),
    Break(Option<StringKey>, Vec<AstNode>),
    Continue(Option<StringKey>, Vec<AstNode>),
    Goto(StringKey),
    BlockStart(StringKey, Vec<ParameterNode>),
    Noop,
    Error,
}

impl Ast {
    pub fn global(name: StringKey, node: AstNode) -> Self {
        Ast::Global(name, Box::new(node))
    }

    pub fn assign(target: AssignTarget, node: AstNode) -> Self {
        Ast::Assign(target, Box::new(node))
    }

    pub fn bool(x: bool) -> Self {
        Ast::Literal(Literal::Bool(x))
    }

    pub fn is_label(&self) -> bool {
        if let Ast::BlockStart(_, _) = self {
            true
        } else {
            false
        }
    }

    pub fn get_label(&self) -> Option<StringKey> {
        if let Ast::BlockStart(key, _) = self {
            Some(*key)
        } else {
            None
        }
    }

    pub fn is_expr(&self) -> bool {
        match self {
            Self::BinaryOp(_, _, _) => true,
            Self::UnaryOp(_, _) => true,
            Self::Call(_, _, _) => true,
            Self::Identifier(_) => true,
            Self::Literal(_) => true,
            //Self::Conditional(_, _, _) => true,
            Self::While(_, _) => true,
            _ => false,
        }
    }

    pub fn is_terminator(&self) -> bool {
        match self {
            Self::Sequence(exprs) => exprs.last().unwrap().node.is_terminator(),
            //Self::Block(_) => true,
            Self::Goto(_) => true,
            Self::Return(_) => true,
            //Self::Conditional(_, _, _) => true,
            Self::Break(_, _) => true,
            Self::Continue(_, _) => true,
            Self::While(_, _) => true,
            //Self::Test(_, _) => true,
            _ => false,
        }
    }

    pub fn terminator(&self) -> Option<Terminator> {
        match self {
            Self::Sequence(exprs) => exprs.last().unwrap().node.terminator(),
            //Self::Block(nb) => nb.children.last().unwrap().node.terminator(),
            Self::Goto(key) => Some(Terminator::Jump(*key)),
            Self::Return(_) => Some(Terminator::Return),
            _ => None,
        }
    }

    pub fn from_name(
        name: &str,
        mut args: Vec<Argument>,
        b: &mut NodeBuilder,
    ) -> Option<Self> {
        if name == "goto" {
            let rest = args
                .split_off(1)
                .into_iter()
                .map(|a| {
                    let Argument::Positional(expr) = a;
                    *expr
                })
                .collect::<Vec<_>>();
            assert_eq!(rest.len(), 0);
            let s = args.pop().unwrap().try_string().unwrap();
            let key = b.s(&s);
            Some(Self::Goto(key.into()))
        } else if name == "static" {
            println!("args: {:?}", args);
            let Argument::Positional(value) = args.pop().unwrap();
            let Argument::Positional(name_node) = args.pop().unwrap();
            let name = b.s(&name_node.try_string().unwrap());
            Some(Self::global(name, *value))
        } else if name == "label" {
            let rest = args.split_off(1);
            let s = args.pop().unwrap().try_string().unwrap();
            let key = b.s(&s);

            let mut params = vec![];
            for arg in rest {
                let Argument::Positional(node) = arg;
                let name = node.try_string().unwrap();
                let key = b.s(&name);
                params.push(ParameterNode {
                    name: key,
                    ty: AstType::Unit,
                    node: Parameter::Normal,
                    span_id: b.span_id.clone(),
                });
            }
            Some(Self::BlockStart(key.into(), vec![]))
        } else if name == "ternary" {
            let Argument::Positional(else_expr) = args.pop().unwrap();
            let Argument::Positional(then_expr) = args.pop().unwrap();
            let Argument::Positional(condition) = args.pop().unwrap();
            Some(Self::Ternary(
                condition.into(),
                then_expr.into(),
                else_expr.into(),
            ))
        } else {
            None
        }
    }
}

#[derive(Clone)]
pub struct SimpleExtra {
    span: Span,
}

impl std::fmt::Debug for SimpleExtra {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.span.begin.pos == 0 && self.span.end.pos == 0 {
            f.write_str("extra")
        } else {
            f.debug_struct("span")
                .field("begin", &self.span.begin.pos)
                .field("end", &self.span.end.pos)
                .finish()
        }
    }
}

impl Extra for SimpleExtra {
    fn new(span_id: SpanId, file_id: usize, begin: CodeLocation, end: CodeLocation) -> Self {
        Self {
            span: Span {
                span_id,
                file_id,
                begin,
                end,
            },
        }
    }
    fn get_span(&self) -> Span {
        self.span.clone()
    }

    fn span(span: Span) -> Self {
        Self { span }
    }
    fn location<'c>(&self, context: &'c Context, d: &Diagnostics) -> Location<'c> {
        d.location(context, &self.span)
    }

    fn error(&self, msg: &str) -> Diagnostic<usize> {
        let r = self.span.begin.pos as usize..self.span.end.pos as usize;
        Diagnostic::error()
            .with_labels(vec![Label::primary(self.span.file_id, r).with_message(msg)])
            .with_message("error")
    }

    fn range(&self) -> std::ops::Range<usize> {
        self.span.begin.pos as usize..self.span.end.pos as usize
    }

    fn primary(&self, msg: &str) -> Label<usize> {
        let r = self.span.begin.pos as usize..self.span.end.pos as usize;
        Label::primary(self.span.file_id, r).with_message(msg)
    }

    fn secondary(&self, msg: &str) -> Label<usize> {
        let r = self.span.begin.pos as usize..self.span.end.pos as usize;
        Label::secondary(self.span.file_id, r).with_message(msg)
    }
}

pub trait Extra: Debug + Clone {
    fn new(span_id: SpanId, file_id: usize, begin: CodeLocation, end: CodeLocation) -> Self;
    fn get_span(&self) -> Span;
    fn span(span: Span) -> Self;
    fn location<'c>(&self, context: &'c Context, d: &Diagnostics) -> Location<'c>;
    fn error(&self, msg: &str) -> Diagnostic<usize>;
    fn range(&self) -> std::ops::Range<usize>;
    fn primary(&self, msg: &str) -> Label<usize>;
    fn secondary(&self, msg: &str) -> Label<usize>;
}

#[derive(Debug, Clone)]
pub struct AstNode {
    pub node: Ast,
    pub span_id: SpanId,
    //pub(crate) _e: std::marker::PhantomData<E>,
}

impl AstNode {
    pub fn location<'c>(&self, context: &'c Context, d: &Diagnostics) -> Location<'c> {
        let span = d.lookup(self.span_id);
        d.location(context, &span)
    }

    pub fn try_string(&self) -> Option<String> {
        if let Ast::Literal(Literal::String(s)) = &self.node {
            Some(s.clone())
        } else {
            None
        }
    }

    /*
    pub fn is_block(&self) -> bool {
        if let Ast::Block(_nb) = &self.node {
            true
        } else {
            false
        }
    }

    pub fn try_block(self) -> Option<Vec<AstNode<E>>> {
        if let Ast::Block(nb) = self.node {
            Some(nb.children)
        } else {
            None
        }
    }
    */

    pub fn is_seq(&self) -> bool {
        if let Ast::Sequence(_) = self.node {
            true
        } else {
            false
        }
    }

    pub fn try_seq(self) -> Option<Vec<AstNode>> {
        if let Ast::Sequence(seq) = self.node {
            Some(seq)
        } else {
            None
        }
    }

    pub fn to_vec(self) -> Vec<AstNode> {
        match self.node {
            Ast::Sequence(exprs) => exprs
                .into_iter()
                .map(|expr| expr.to_vec())
                .flatten()
                .collect(),
            _ => vec![self],
        }
    }

    pub fn to_vec_ref(&self) -> Vec<&AstNode> {
        match self.node {
            Ast::Sequence(ref exprs) => exprs
                .iter()
                .map(|expr| expr.to_vec_ref())
                .flatten()
                .collect(),
            _ => vec![self],
        }
    }

    pub fn children_mut<'a>(&'a mut self) -> AstNodeIterator<'a> {
        let mut values = vec![];
        match &mut self.node {
            Ast::Sequence(ref mut exprs) => {
                for e in exprs.iter_mut() {
                    values.push(e);
                }
            }
            Ast::Definition(def) => {
                if let Some(ref mut body) = def.body {
                    values.push(body);
                }
            }
            Ast::BinaryOp(_, a, b)
                //| Ast::Mutate(a, b) 
                //| Ast::Test(a, b)
                | Ast::While(a, b) => {
                values.push(a);
                values.push(b);
            }
            Ast::UnaryOp(_, a)
            | Ast::Assign(_, a)
            //| Ast::Replace(_, a)
            //| Ast::Deref(a, _)
            | Ast::Loop(_, a) => {
                values.push(a);
            }
            Ast::Call(f, args, _ty) => {
                values.push(f);
                for a in args {
                    let Argument::Positional(expr) = a;
                    values.push(expr);
                }
            }
            Ast::Global(_, body) => {
                values.push(body);
            }
            Ast::Conditional(a, b, c) => {
                values.push(a);
                values.push(b);
                if let Some(c) = c {
                    values.push(c);
                }
            }
            Ast::Return(a) => {
                if let Some(a) = a {
                    values.push(a);
                }
            }
            /*
            Ast::Block(ref mut nb) => {
                values.extend(&mut nb.children);
            }
            */
            Ast::Module(_name, ref mut body) => {
                values.push(body);
                //values.extend(&mut body.to_vec());
            }
            Ast::Builtin(_, args) => {
                for a in args {
                    let Argument::Positional(expr) = a;
                    values.push(expr);
                }
            }
            _ => (),
        }
        AstNodeIterator { values }
    }
}

/*
impl<E: Extra> AstNode<E> {
    pub fn normalize<'c>(mut self, d: &mut Diagnostics, b: &mut NodeBuilder<E>) -> Self {
        self.preprocess(d, b);
        self.analyze(b);
        self
    }

    pub fn preprocess<'c>(&mut self, d: &mut Diagnostics, b: &mut NodeBuilder<E>) {
        match &mut self.node {
            _ => (),
        }
        for child in self.children_mut() {
            child.preprocess(d, b);
        }
    }

    pub fn analyze<'c>(&mut self, b: &mut NodeBuilder<E>) {
        //b.identify_node(self);
        for child in self.children_mut() {
            child.analyze(b);
        }
    }
}
*/

pub struct AstNodeIterator<'a> {
    values: Vec<&'a mut AstNode>,
}

impl<'a> Iterator for AstNodeIterator<'a> {
    type Item = &'a mut AstNode;
    fn next(&mut self) -> Option<Self::Item> {
        self.values.pop()
    }
}

impl From<Argument> for AstNode {
    fn from(item: Argument) -> Self {
        match item {
            Argument::Positional(x) => *x,
        }
    }
}

#[derive(Debug, Clone)]
pub enum AssignTarget {
    Identifier(StringKey),
    Alloca(StringKey),
}
