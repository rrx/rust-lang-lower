use std::error;
use std::fmt;

#[derive(Debug, Clone, Copy)]
pub struct SpanId(u32);
impl SpanId {
    pub fn new(v: u32) -> Self {
        Self(v)
    }

    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Default, Copy, Hash, Eq, PartialEq)]
pub struct CodeLocation {
    pub pos: u32,
}

#[derive(Debug, Clone)]
pub struct Span {
    pub span_id: SpanId,
    pub file_id: usize,
    pub begin: CodeLocation,
    pub end: CodeLocation,
}

impl Span {
    pub fn new(span_id: SpanId, file_id: usize, begin: CodeLocation, end: CodeLocation) -> Self {
        Self {
            span_id,
            file_id,
            begin,
            end,
        }
    }
    pub fn to_string(&self) -> String {
        format!("{:?}", self)
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
