use crate::Diagnostics;
use crate::{AstType, BlockId, NodeBuilder, NodeID, StringKey};
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

#[derive(Debug)]
pub enum UnaryOperation {
    Minus,
}

#[derive(Debug)]
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

#[derive(Debug)]
pub struct BinOpNode<E> {
    pub node: BinaryOperation,
    extra: E,
}
impl<E> BinOpNode<E> {
    pub fn new(node: BinaryOperation, extra: E) -> Self {
        Self { node, extra }
    }
}

#[derive(Debug)]
pub enum Argument<E> {
    Positional(Box<AstNode<E>>),
}

impl<E> From<AstNode<E>> for Argument<E> {
    fn from(item: AstNode<E>) -> Self {
        Argument::Positional(item.into())
    }
}

impl<E: Extra> Argument<E> {
    pub fn try_string(self) -> Option<String> {
        let Self::Positional(node) = self;
        (*node).try_string()
    }
}

#[derive(Debug, Clone)]
pub enum Parameter {
    Normal,
    //WithDefault(AstNode<E>),
    //Dummy<std::marker::PhantomData<E>//(AstNode<E>),
}

#[derive(Debug, Clone)]
pub struct ParameterNode<E> {
    pub name: StringKey,
    pub ty: AstType,
    pub node: Parameter,
    pub extra: E,
}

#[derive(Debug)]
pub struct Definition<E> {
    pub name: StringKey,
    pub params: Vec<ParameterNode<E>>,
    pub return_type: Box<AstType>,
    pub body: Option<Box<AstNode<E>>>,
    //pub payload: P::DefPayload,
}

#[derive(Debug)]
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

#[derive(Debug)]
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

#[derive(Debug)]
pub struct AstNodeBlock<E> {
    pub name: BlockId,
    //pub(crate) label: BlockLabel,
    pub params: Vec<ParameterNode<E>>,
    pub children: Vec<AstNode<E>>,
}

#[derive(Debug)]
pub enum Ast<E> {
    BinaryOp(BinOpNode<E>, Box<AstNode<E>>, Box<AstNode<E>>),
    UnaryOp(UnaryOperation, Box<AstNode<E>>),
    Call(Box<AstNode<E>>, Vec<Argument<E>>, AstType),
    Identifier(StringKey),
    Literal(Literal),
    Sequence(Vec<AstNode<E>>),
    Definition(Definition<E>),
    //Variable(Definition<E>),
    Global(StringKey, Box<AstNode<E>>),
    Assign(AssignTarget, Box<AstNode<E>>),
    Replace(AssignTarget, Box<AstNode<E>>),
    Mutate(Box<AstNode<E>>, Box<AstNode<E>>),
    Branch(Box<AstNode<E>>, StringKey, StringKey),
    Conditional(Box<AstNode<E>>, Box<AstNode<E>>, Option<Box<AstNode<E>>>),
    Ternary(Box<AstNode<E>>, Box<AstNode<E>>, Box<AstNode<E>>),
    Return(Option<Box<AstNode<E>>>),
    Test(Box<AstNode<E>>, Box<AstNode<E>>),
    While(Box<AstNode<E>>, Box<AstNode<E>>),
    Builtin(Builtin, Vec<Argument<E>>),
    Deref(Box<AstNode<E>>, DerefTarget),
    Block(AstNodeBlock<E>),
    Module(StringKey, Box<AstNode<E>>),
    Loop(StringKey, Box<AstNode<E>>),
    Break(Option<StringKey>, Vec<AstNode<E>>),
    Continue(Option<StringKey>, Vec<AstNode<E>>),
    Goto(StringKey),
    Label(StringKey, Vec<ParameterNode<E>>),
    Noop,
    Error,
}

impl<E: Extra> Ast<E> {
    pub fn global(name: StringKey, node: AstNode<E>) -> Self {
        Ast::Global(name, Box::new(node))
    }

    pub fn assign(target: AssignTarget, node: AstNode<E>) -> Self {
        Ast::Assign(target, Box::new(node))
    }

    pub fn bool(x: bool) -> Self {
        Ast::Literal(Literal::Bool(x))
    }

    pub fn is_label(&self) -> bool {
        if let Ast::Label(_, _) = self {
            true
        } else {
            false
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
            Self::Block(_) => true,
            Self::Goto(_) => true,
            Self::Return(_) => true,
            //Self::Conditional(_, _, _) => true,
            Self::Break(_, _) => true,
            Self::Continue(_, _) => true,
            Self::While(_, _) => true,
            Self::Test(_, _) => true,
            _ => false,
        }
    }

    pub fn terminator(&self) -> Option<Terminator> {
        match self {
            Self::Sequence(exprs) => exprs.last().unwrap().node.terminator(),
            Self::Block(nb) => nb.children.last().unwrap().node.terminator(),
            Self::Goto(key) => Some(Terminator::Jump(*key)),
            Self::Return(_) => Some(Terminator::Return),
            _ => None,
        }
    }

    pub fn from_name(
        name: &str,
        mut args: Vec<Argument<E>>,
        b: &mut NodeBuilder<E>,
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
                    extra: node.extra,
                });
            }
            Some(Self::Label(key.into(), params))
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

#[derive(Debug, Clone, Default)]
pub struct CodeLocation {
    pub pos: u32,
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
    fn new(file_id: usize, begin: CodeLocation, end: CodeLocation) -> Self {
        Self {
            span: Span {
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
    fn new(file_id: usize, begin: CodeLocation, end: CodeLocation) -> Self;
    fn get_span(&self) -> Span;
    fn span(span: Span) -> Self;
    fn location<'c>(&self, context: &'c Context, d: &Diagnostics) -> Location<'c>;
    fn error(&self, msg: &str) -> Diagnostic<usize>;
    fn range(&self) -> std::ops::Range<usize>;
    fn primary(&self, msg: &str) -> Label<usize>;
    fn secondary(&self, msg: &str) -> Label<usize>;
}

#[derive(Debug, Clone)]
pub struct Span {
    pub file_id: usize,
    pub begin: CodeLocation,
    pub end: CodeLocation,
}

#[derive(Debug)]
pub struct AstNode<E> {
    pub node_id: NodeID,
    pub node: Ast<E>,
    pub extra: E,
}

impl<E: Extra> AstNode<E> {
    pub fn set_extra(mut self, extra: E) -> Self {
        self.extra = extra;
        self
    }

    pub fn location<'c>(&self, context: &'c Context, d: &Diagnostics) -> Location<'c> {
        self.extra.location(context, d)
    }

    //pub fn new(node: Ast<E>, extra: E) -> Self {
    //Self { node, extra }
    //}

    pub fn try_string(&self) -> Option<String> {
        if let Ast::Literal(Literal::String(s)) = &self.node {
            Some(s.clone())
        } else {
            None
        }
    }

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

    pub fn is_seq(&self) -> bool {
        if let Ast::Sequence(_) = self.node {
            true
        } else {
            false
        }
    }

    pub fn try_seq(self) -> Option<Vec<AstNode<E>>> {
        if let Ast::Sequence(seq) = self.node {
            Some(seq)
        } else {
            None
        }
    }

    pub fn to_vec(self) -> Vec<AstNode<E>> {
        match self.node {
            Ast::Sequence(exprs) => exprs
                .into_iter()
                .map(|expr| expr.to_vec())
                .flatten()
                .collect(),
            _ => vec![self],
        }
    }

    /*
    pub fn to_blocks(self) -> Vec<NodeBlock<E>> {
        //let mut out = vec![];
        for expr in self.to_vec() {
            match &expr.node {
                // should be flattened already
                Ast::Sequence(_) => unreachable!(),
                Ast::Goto(_, _) => (),
                Ast::Label(_, _) => (),
                _ => unimplemented!(),
            }
        }
        //let mut out = vec![];
        //match self.node {
        //Ast::Sequence(_exprs) => {
        //}
        //_ => ()
        //}

        //out
        vec![]
    }
    */

    pub fn children_mut<'a>(&'a mut self) -> AstNodeIterator<'a, E> {
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
            Ast::BinaryOp(_, a, b) | Ast::Mutate(a, b) | Ast::Test(a, b) | Ast::While(a, b) => {
                values.push(a);
                values.push(b);
            }
            Ast::UnaryOp(_, a)
            | Ast::Assign(_, a)
            | Ast::Replace(_, a)
            | Ast::Deref(a, _)
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
            Ast::Block(ref mut nb) => {
                values.extend(&mut nb.children);
            }
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

    pub fn dump(&self, b: &NodeBuilder<E>, mut depth: usize) {
        match &self.node {
            Ast::Module(name, body) => {
                println!("{:width$}module({}):", "", b.r(*name), width = depth * 2);
                depth += 1;
                body.dump(b, depth);
                //for c in body.to_vec() {
                //c.dump(b, depth);
                //}
            }
            Ast::Sequence(exprs) => {
                for expr in exprs {
                    expr.dump(b, depth);
                }
            }
            Ast::Return(maybe_result) => {
                println!("{:width$}ret:", "", width = depth * 2);
                if let Some(result) = maybe_result {
                    result.dump(b, depth + 1);
                }
            }
            Ast::Builtin(bi, args) => {
                println!("{:width$}builtin({:?})", "", bi, width = depth * 2);
                for a in args {
                    let Argument::Positional(expr) = a;
                    expr.dump(b, depth + 1);
                }
            }
            Ast::Literal(lit) => {
                println!("{:width$}{:?}", "", lit, width = depth * 2);
            }

            Ast::Label(name, args) => {
                println!(
                    "{:width$}label: {}",
                    "",
                    //name.0,
                    b.r(*name),
                    width = depth * 2
                );
                for e in args {
                    println!(
                        "{:width$}arg: {}, {:?}",
                        "",
                        b.resolve_label(e.name.into()),
                        e.ty,
                        width = (depth + 1) * 2
                    );
                }
            }

            Ast::Goto(key) => {
                println!(
                    "{:width$}goto: {}",
                    "",
                    //key.0,
                    b.r(*key),
                    width = depth * 2
                );
            }
            Ast::Definition(def) => {
                println!("{:width$}func({}):", "", b.r(def.name), width = depth * 2);
                depth += 1;

                for a in &def.params {
                    println!(
                        "{:width$}arg: {}: {:?}",
                        "",
                        b.resolve_label(a.name.into()),
                        a.ty,
                        width = depth * 2
                    );
                }
                if let Some(ref body) = def.body {
                    body.dump(b, depth);
                }
            }

            Ast::Block(block) => {
                println!(
                    "{:width$}block({})",
                    "",
                    //block.label.0,
                    b.resolve_block_label(block.name),
                    width = depth * 2
                );
                for a in &block.params {
                    println!(
                        "{:width$}arg: {}: {:?}",
                        "",
                        b.resolve_label(a.name.into()),
                        a.ty,
                        width = (depth + 1) * 2
                    );
                }
                for a in &block.children {
                    a.dump(b, depth + 1);
                }
            }

            Ast::Global(key, value) => {
                println!("{:width$}global: {}", "", b.r(*key), width = depth * 2);
                value.dump(b, depth + 1);
            }

            Ast::Assign(target, value) => {
                println!("{:width$}assign", "", width = depth * 2);
                depth += 1;
                match target {
                    AssignTarget::Identifier(key) => {
                        println!(
                            "{:width$}target identifier: {}",
                            "",
                            b.resolve_label(key.into()),
                            width = depth * 2
                        );
                    }
                    AssignTarget::Alloca(key) => {
                        println!(
                            "{:width$}target alloca: {}",
                            "",
                            b.resolve_label(key.into()),
                            width = depth * 2
                        );
                    }
                }
                value.dump(b, depth);
            }

            Ast::BinaryOp(op, x, y) => {
                println!("{:width$}binop: {:?}", "", op, width = depth * 2);
                x.dump(b, depth + 1);
                y.dump(b, depth + 1);
            }

            Ast::UnaryOp(op, expr) => {
                println!("{:width$}unary: {:?}", "", op, width = depth * 2);
                expr.dump(b, depth + 1);
            }

            Ast::Identifier(key) => {
                println!(
                    "{:width$}ident: {}",
                    "",
                    b.resolve_label(key.into()),
                    width = depth * 2
                );
            }

            Ast::Conditional(c, a, mb) => {
                println!("{:width$}cond:", "", width = depth * 2);
                depth += 1;
                c.dump(b, depth);
                println!("{:width$}then:", "", width = depth * 2);
                a.dump(b, depth + 1);
                if let Some(else_expr) = mb {
                    println!("{:width$}else:", "", width = depth * 2);
                    else_expr.dump(b, depth + 1);
                }
            }

            Ast::Ternary(c, then_expr, else_expr) => {
                println!("{:width$}ternary:", "", width = depth * 2);
                depth += 1;
                c.dump(b, depth);
                println!("{:width$}then:", "", width = depth * 2);
                then_expr.dump(b, depth + 1);
                println!("{:width$}else:", "", width = depth * 2);
                else_expr.dump(b, depth + 1);
            }

            Ast::Branch(c, then_key, else_key) => {
                println!(
                    "{:width$}branch: {}, {}",
                    "",
                    b.r(*then_key),
                    b.r(*else_key),
                    width = depth * 2
                );
                c.dump(b, depth + 1);
            }

            Ast::Call(f, args, ret_ty) => {
                println!("{:width$}call: {:?}", "", ret_ty, width = depth * 2);
                f.dump(b, depth + 1);
                if args.len() > 0 {
                    for a in args {
                        let Argument::Positional(expr) = a;
                        expr.dump(b, depth + 1);
                    }
                }
            }

            Ast::Deref(a, _) => a.dump(b, depth),
            Ast::Mutate(lhs, rhs) => {
                println!("{:width$}mutate", "", width = depth * 2);
                lhs.dump(b, depth + 1);
                rhs.dump(b, depth + 1);
            }

            _ => unimplemented!("{:?}", self),
        }
    }
}

pub struct AstNodeIterator<'a, E> {
    values: Vec<&'a mut AstNode<E>>,
}

impl<'a, E> Iterator for AstNodeIterator<'a, E> {
    type Item = &'a mut AstNode<E>;
    fn next(&mut self) -> Option<Self::Item> {
        self.values.pop()
    }
}

impl<E> From<Argument<E>> for AstNode<E> {
    fn from(item: Argument<E>) -> Self {
        match item {
            Argument::Positional(x) => *x,
        }
    }
}

#[derive(Debug)]
pub enum AssignTarget {
    Identifier(StringKey),
    Alloca(StringKey),
}
