use crate::{InternKey, InternPool, InternValue};
use std::error;
use std::fmt;

use codespan_reporting::diagnostic::{Diagnostic, Label, Severity};
use codespan_reporting::files::Files;
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{BufferWriter, ColorChoice, StandardStream};

pub type FileDB = SimpleFiles<String, String>;

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
    files: crate::FileDB,
    pub diagnostics: Vec<Diagnostic<usize>>,
    pub has_errors: bool,
}

pub fn primary_label(msg: &str, span: &Span) -> Label<usize> {
    if let Span::Loc(span) = span {
        let r = span.begin.pos as usize..span.end.pos as usize;
        Label::primary(span.file_id, r).with_message(msg)
    } else {
        Label::primary(0, 0..0)
    }
}

pub fn secondary_label(msg: &str, span: &Span) -> Label<usize> {
    if let Span::Loc(span) = span {
        let r = span.begin.pos as usize..span.end.pos as usize;
        Label::secondary(span.file_id, r).with_message(msg)
    } else {
        Label::secondary(0, 0..0)
    }
}

pub fn diagnostic_error(msg: &str, span: Span) -> Diagnostic<usize> {
    let mut labels = vec![];
    if let Span::Loc(span) = span {
        let r = span.begin.pos as usize..span.end.pos as usize;
        labels = vec![Label::primary(span.file_id, r).with_message(msg)];
    }

    let error = Diagnostic::error().with_labels(labels).with_message(msg);
    error
}

impl SpanBuilder {
    pub fn new() -> Self {
        let s = Self {
            pool: SpanPool::new(),
            files: crate::FileDB::new(),
            diagnostics: vec![],
            has_errors: false,
        };
        s.init()
    }

    pub fn init(mut self) -> Self {
        // make sure the first span is unknown
        self.get_span_unknown();
        self
    }

    pub fn push_diagnostic(&mut self, d: Diagnostic<usize>) {
        if d.severity > Severity::Warning {
            self.has_errors = true;
        }
        self.diagnostics.push(d);
    }

    pub fn reset_diagnostics(&mut self) {
        self.has_errors = false;
        self.diagnostics.clear();
    }

    pub fn diagnostics_emit_string(&self, d: Diagnostic<usize>) -> String {
        let config = codespan_reporting::term::Config::default();
        let writer = BufferWriter::stdout(ColorChoice::Always);
        let mut buffer = writer.buffer();
        term::emit(&mut buffer, &config, &self.files, &d).unwrap();
        String::from_utf8_lossy(buffer.as_slice()).to_string()
    }

    pub fn diagnostics_dump(&mut self) {
        let writer = StandardStream::stderr(ColorChoice::Always);
        let config = codespan_reporting::term::Config::default();
        for d in self.diagnostics.drain(..) {
            term::emit(&mut writer.lock(), &config, &self.files, &d).unwrap();
        }
    }

    pub fn add_source(&mut self, filename: String, content: String) -> usize {
        self.files.add(filename, content)
    }

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

    pub fn s(&mut self, span: Span) -> SpanId {
        self.pool.intern(span)
    }

    pub fn error(&self, msg: &str, span: &Span) -> Diagnostic<usize> {
        let mut labels = vec![];
        if let Span::Loc(span) = span {
            let r = span.begin.pos as usize..span.end.pos as usize;
            labels = vec![Label::primary(span.file_id, r).with_message(msg)];
        }
        Diagnostic::error()
            .with_labels(labels)
            .with_message("error")
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
