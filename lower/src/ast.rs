use compile_core::Ast;
use compile_core::Diagnostics;
use compile_core::{
    CodeLocation,
    //NodeBuilder,
    Span,
    SpanId,
    StringKey,
};
use compile_core::{Diagnostic, Label};
use melior::{ir::Location, Context};
use std::fmt::Debug;

#[derive(Debug)]
pub enum Terminator {
    Jump(StringKey),
    Branch(StringKey, StringKey),
    Return,
}

impl Terminator {
    pub fn from_ast(item: &Ast) -> Option<Self> {
        match item {
            Ast::Sequence(exprs) => Terminator::from_ast(&exprs.last().unwrap().node),
            //Self::Block(nb) => nb.children.last().unwrap().node.terminator(),
            Ast::Goto(key) => Some(Self::Jump(*key)),
            Ast::Return(_) => Some(Self::Return),
            _ => None,
        }
    }
}

/*
pub fn node_terminator(node: &AstNode) -> Option<Terminator> {
    match self {
        Ast::Sequence(exprs) => exprs.last().unwrap().node.terminator(),
        //Self::Block(nb) => nb.children.last().unwrap().node.terminator(),
        Self::Goto(key) => Some(Terminator::Jump(*key)),
        Self::Return(_) => Some(Terminator::Return),
        _ => None,
    }
}
*/

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

    fn location<'c>(&self, context: &'c Context, _d: &Diagnostics) -> Location<'c> {
        Location::unknown(context)
        //flat::mlir::diagnostics_location(self, context, &self.span)
        //d.location(context, &self.span)
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
