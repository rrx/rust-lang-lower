use crate::{InternKey, InternPool, InternValue};
use std::error;
use std::fmt;

#[derive(Debug, Clone, Copy)]
pub struct SpanId(u32);
impl SpanId {
    pub fn new(v: u32) -> Self {
        Self(v)
    }

    pub fn unknown() -> Self {
        Self(0)
    }

    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Default, Copy, Hash, Eq, PartialEq)]
pub struct CodeLocation {
    pub pos: u32,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct SpanInner {
    pub file_id: usize,
    pub begin: CodeLocation,
    pub end: CodeLocation,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Span {
    Unknown,
    Loc(SpanInner),
}

impl Span {
    pub fn new(file_id: usize, begin: CodeLocation, end: CodeLocation) -> Self {
        Self::Loc(SpanInner {
            file_id,
            begin,
            end,
        })
    }
    pub fn unknown() -> Self {
        Self::Unknown
    }
    pub fn to_string(&self) -> String {
        format!("{:?}", self)
    }
}

impl InternValue for Span {}

impl InternKey for SpanId {
    fn index(&self) -> usize {
        self.0 as usize
    }
    fn new(index: usize) -> Self {
        Self(index as u32)
    }
}

pub type SpanPool = InternPool<SpanId, Span>;

pub struct SpanBuilder {
    pool: SpanPool,
}

impl SpanBuilder {
    pub fn new() -> Self {
        Self {
            pool: SpanPool::new(),
        }
    }

    /*
    pub fn get_filename(&self, span: &Span) -> Result<String, codespan_reporting::files::Error> {
        if let Span::Loc(span) = span {
            self.files.name(span.file_id)
        } else {
            Ok("unknown".into())
        }
    }


    pub fn get_location(
        &self,
        span: &Span,
    ) -> Result<codespan_reporting::files::Location, codespan_reporting::files::Error> {
        if let Span::Loc(span) = span {
            self.files.location(span.file_id, span.begin.pos as usize)
        } else {
            self.files.location(0, 0)
        }
    }

    */
    pub fn get_span_unknown(&mut self) -> SpanId {
        self.get_span(0, CodeLocation::default(), CodeLocation::default())
    }

    pub fn lookup(&self, span_id: SpanId) -> Span {
        self.pool.resolve(&span_id).clone()
    }

    pub fn get_span(&mut self, file_id: usize, begin: CodeLocation, end: CodeLocation) -> SpanId {
        let v = Span::new(file_id, begin, end);
        self.pool.intern(v)
    }
}

pub type Spanned<T> = (T, SpanId);

#[derive(Debug)]
pub struct SpannedError {
    pairs: Vec<(String, SpanId)>,
}

impl SpannedError {
    pub fn new1(s1: impl Into<String>, s2: SpanId) -> Self {
        let p1 = (s1.into(), s2);
        SpannedError { pairs: vec![p1] }
    }

    pub fn new2(s1: impl Into<String>, s2: SpanId, s3: impl Into<String>, s4: SpanId) -> Self {
        let p1 = (s1.into(), s2);
        let p2 = (s3.into(), s4);
        SpannedError {
            pairs: vec![p1, p2],
        }
    }

    /*
    pub fn print(&self, sm: &SpanManager) -> String {
        let mut out = String::new();
        for (msg, span) in self.pairs.iter() {
            out += &msg;
            out += "\n";
            out += &sm.print(*span);
        }
        out
    }
    */
}
impl fmt::Display for SpannedError {
    fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result {
        Ok(())
    }
}
impl error::Error for SpannedError {}
