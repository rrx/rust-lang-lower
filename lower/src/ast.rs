use crate::Diagnostics;
use crate::{
    AstType,
    BlockId,
    CodeLocation,
    NodeBuilder,
    Span,
    SpanId,
    //NodeID,
    StringKey,
};
use anyhow::Result;
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
pub struct BinOpNode<E> {
    pub node: BinaryOperation,
    extra: E,
}
impl<E> BinOpNode<E> {
    pub fn new(node: BinaryOperation, extra: E) -> Self {
        Self { node, extra }
    }
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub struct Definition<E> {
    pub name: StringKey,
    pub params: Vec<ParameterNode<E>>,
    pub return_type: Box<AstType>,
    pub body: Option<Box<AstNode<E>>>,
    pub lambda: bool,
    //pub payload: P::DefPayload,
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
pub struct AstNodeBlock<E> {
    pub name: BlockId,
    //pub(crate) label: BlockLabel,
    pub params: Vec<ParameterNode<E>>,
    pub children: Vec<AstNode<E>>,
}

#[derive(Debug, Clone)]
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
    BlockStart(StringKey, Vec<ParameterNode<E>>),
    Label(StringKey),
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
        if let Ast::Label(_) = self {
            true
        } else {
            false
        }
    }

    pub fn get_label(&self) -> Option<StringKey> {
        if let Ast::Label(key) = self {
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
                    extra: node.extra,
                });
            }
            Some(Self::Label(key.into()))
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
pub struct AstNode<E> {
    //pub node_id: NodeID,
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

    pub fn to_vec_ref(&self) -> Vec<&AstNode<E>> {
        match self.node {
            Ast::Sequence(ref exprs) => exprs
                .iter()
                .map(|expr| expr.to_vec_ref())
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

    pub fn dump(&self, b: &NodeBuilder<E>) {
        let mut out = vec![];
        self.dump_strings(b, &mut out, 0);
        for (depth, s, _span) in out {
            print_with_indent(&s, depth);
        }
    }

    pub fn dump_html(&self, b: &NodeBuilder<E>) -> Result<()> {
        let mut file = std::fs::File::create("out.html")?;
        use std::io::prelude::*;
        let mut out = vec![];
        self.dump_strings(b, &mut out, 0);
        file.write_all(b"<pre>\n")?;
        for (depth, s, _span) in out {
            file.write_fmt(format_args!(
                "{:width$}<span id=\"0\">{}</span>\n",
                "",
                s,
                width = depth * 2
            ))?;
        }
        file.write_all(b"</pre>\n")?;
        Ok(())
    }

    pub fn dump_strings(
        &self,
        b: &NodeBuilder<E>,
        out: &mut Vec<(usize, String, Span)>,
        mut depth: usize,
    ) {
        match &self.node {
            Ast::Module(name, body) => {
                let s = format!("module({})", b.r(*name));
                out.push((depth, s, self.extra.get_span()));
                depth += 1;
                body.dump_strings(b, out, depth);
            }

            Ast::Sequence(exprs) => {
                for expr in exprs {
                    expr.dump_strings(b, out, depth);
                }
            }

            Ast::Return(maybe_result) => {
                let s = format!("ret:");
                out.push((depth, s, self.extra.get_span()));
                if let Some(result) = maybe_result {
                    result.dump_strings(b, out, depth + 1);
                }
            }

            Ast::Builtin(bi, args) => {
                let s = format!("builtin({:?})", bi);
                out.push((depth, s, self.extra.get_span()));
                for a in args {
                    let Argument::Positional(expr) = a;
                    expr.dump_strings(b, out, depth + 1);
                }
            }

            Ast::Literal(lit) => {
                let s = format!("{:?}", lit);
                out.push((depth, s, self.extra.get_span()));
            }

            Ast::BlockStart(name, params) => {
                let s = format!("block_start: {}", b.r(*name),);
                out.push((depth, s, self.extra.get_span()));
                for e in params {
                    let s = format!("arg: {}, {:?}", b.resolve_label(e.name.into()), e.ty,);
                    out.push((depth, s, self.extra.get_span()));
                }
            }

            Ast::Label(name) => {
                let s = format!("label: {}", b.r(*name));
                out.push((depth, s, self.extra.get_span()));
            }

            Ast::Goto(key) => {
                let s = format!("goto: {}", b.r(*key),);
                out.push((depth, s, self.extra.get_span()));
            }

            Ast::Definition(def) => {
                let s = format!("func({}):", b.r(def.name));
                out.push((depth, s, self.extra.get_span()));
                depth += 1;

                for a in &def.params {
                    let s = format!("arg: {}: {:?}", b.resolve_label(a.name.into()), a.ty,);
                    out.push((depth, s, self.extra.get_span()));
                }
                if let Some(ref body) = def.body {
                    body.dump_strings(b, out, depth);
                }
            }

            Ast::Block(block) => {
                let s = format!("block({})", b.resolve_block_label(block.name),);
                out.push((depth, s, self.extra.get_span()));
                depth += 1;
                for a in &block.params {
                    let s = format!("arg: {}: {:?}", b.resolve_label(a.name.into()), a.ty,);
                    out.push((depth, s, self.extra.get_span()));
                }
                for a in &block.children {
                    a.dump_strings(b, out, depth);
                }
            }

            Ast::Global(key, value) => {
                let s = format!("global: {}", b.r(*key));
                out.push((depth, s, self.extra.get_span()));
                value.dump_strings(b, out, depth + 1);
            }

            Ast::Assign(target, value) => {
                let s = format!("assign");
                out.push((depth, s, self.extra.get_span()));
                depth += 1;
                match target {
                    AssignTarget::Identifier(key) => {
                        let s = format!("target identifier: {}", b.resolve_label(key.into()),);
                        out.push((depth, s, self.extra.get_span()));
                    }
                    AssignTarget::Alloca(key) => {
                        let s = format!("target alloca: {}", b.resolve_label(key.into()),);
                        out.push((depth, s, self.extra.get_span()));
                    }
                }
                value.dump_strings(b, out, depth);
            }

            Ast::BinaryOp(op, x, y) => {
                let s = format!("binop: {:?}", op);
                out.push((depth, s, self.extra.get_span()));
                x.dump_strings(b, out, depth + 1);
                y.dump_strings(b, out, depth + 1);
            }

            Ast::UnaryOp(op, expr) => {
                let s = format!("unary: {:?}", op);
                out.push((depth, s, self.extra.get_span()));
                expr.dump_strings(b, out, depth + 1);
            }

            Ast::Identifier(key) => {
                let s = format!("ident: {}", b.resolve_label(key.into()),);
                out.push((depth, s, self.extra.get_span()));
            }

            Ast::Conditional(c, a, mb) => {
                let s = format!("cond:");
                out.push((depth, s, self.extra.get_span()));
                depth += 1;
                c.dump_strings(b, out, depth);
                let s = format!("then:");
                out.push((depth, s, self.extra.get_span()));
                a.dump_strings(b, out, depth + 1);
                if let Some(else_expr) = mb {
                    let s = format!("else:");
                    out.push((depth, s, self.extra.get_span()));
                    else_expr.dump_strings(b, out, depth + 1);
                }
            }

            Ast::Ternary(c, then_expr, else_expr) => {
                let s = format!("ternary:");
                out.push((depth, s, self.extra.get_span()));
                depth += 1;
                c.dump_strings(b, out, depth);
                let s = format!("then:");
                out.push((depth, s, self.extra.get_span()));
                then_expr.dump_strings(b, out, depth + 1);
                let s = format!("else:");
                out.push((depth, s, self.extra.get_span()));
                else_expr.dump_strings(b, out, depth + 1);
            }

            Ast::Branch(c, then_key, else_key) => {
                let s = format!("branch: {}, {}", b.r(*then_key), b.r(*else_key),);
                out.push((depth, s, self.extra.get_span()));
                c.dump_strings(b, out, depth + 1);
            }

            Ast::Call(f, args, ret_ty) => {
                let s = format!("call: {:?}", ret_ty);
                out.push((depth, s, self.extra.get_span()));
                f.dump_strings(b, out, depth + 1);
                if args.len() > 0 {
                    for a in args {
                        let Argument::Positional(expr) = a;
                        expr.dump_strings(b, out, depth + 1);
                    }
                }
            }

            Ast::Deref(a, _) => a.dump_strings(b, out, depth),

            Ast::Mutate(lhs, rhs) => {
                let s = format!("mutate");
                out.push((depth, s, self.extra.get_span()));
                lhs.dump_strings(b, out, depth + 1);
                rhs.dump_strings(b, out, depth + 1);
            }

            Ast::Loop(key, body) => {
                let s = format!("loop({})", b.r(*key));
                out.push((depth, s, self.extra.get_span()));
                body.dump_strings(b, out, depth + 1);
            }

            Ast::Break(maybe_key, args) => {
                let s = format!(
                    "break({})",
                    maybe_key.map(|key| b.r(key)).or(Some("")).unwrap()
                );
                out.push((depth, s, self.extra.get_span()));
                for expr in args {
                    expr.dump_strings(b, out, depth + 1);
                }
            }

            Ast::Continue(maybe_key, args) => {
                let s = format!(
                    "continue({})",
                    maybe_key.map(|key| b.r(key)).or(Some("")).unwrap()
                );
                out.push((depth, s, self.extra.get_span()));
                for expr in args {
                    expr.dump_strings(b, out, depth + 1);
                }
            }

            _ => unimplemented!("{:?}", self),
        }
    }
}

pub fn print_html(s: &str, depth: usize, span: &Span) {
    println!(
        "{:width$}<span id=\"0\">{}</span>",
        "",
        s,
        width = depth * 2
    );
}

pub fn print_with_indent(s: &str, depth: usize) {
    println!("{:width$}{}", "", s, width = depth * 2);
}

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

#[derive(Debug, Clone)]
pub enum AssignTarget {
    Identifier(StringKey),
    Alloca(StringKey),
}
