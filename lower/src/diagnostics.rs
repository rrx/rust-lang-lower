use codespan_reporting::diagnostic::{Diagnostic, Severity};
use codespan_reporting::files::Files;
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{BufferWriter, ColorChoice, StandardStream};
use indexmap::IndexSet;
use melior::ir;
use melior::Context;
use thiserror::Error;

pub type FileDB = SimpleFiles<String, String>;

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("Invalid")]
    Invalid,
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

#[derive(Debug, Clone)]
pub struct SpanId(u32);
impl SpanId {
    pub fn index(&self) -> usize {
        self.0 as usize
    }
}

pub struct Diagnostics {
    pub files: FileDB,
    diagnostics: Vec<Diagnostic<usize>>,
    stack: Vec<Span>,
    pub has_errors: bool,
    spans: IndexSet<(usize, CodeLocation, CodeLocation)>,
}

impl Diagnostics {
    pub fn new() -> Self {
        Self {
            files: FileDB::new(),
            diagnostics: vec![],
            stack: vec![],
            has_errors: false,
            spans: IndexSet::new(),
        }
    }

    pub fn get_span_unknown(&mut self) -> Span {
        self.get_span(0, CodeLocation::default(), CodeLocation::default())
    }

    pub fn lookup(&self, span_id: SpanId) -> Span {
        let (file_id, begin, end) = self.spans.get_index(span_id.0 as usize).unwrap();
        Span::new(span_id, *file_id, *begin, *end)
    }

    pub fn get_span(&mut self, file_id: usize, begin: CodeLocation, end: CodeLocation) -> Span {
        let v = (file_id, begin, end);
        let (index, x) = self.spans.insert_full(v);
        let span_id = SpanId(index as u32);
        Span::new(span_id, file_id, begin, end)
    }

    pub fn add_source(&mut self, filename: String, content: String) -> usize {
        self.files.add(filename, content)
    }

    pub fn push_diagnostic(&mut self, d: Diagnostic<usize>) {
        if d.severity > Severity::Warning {
            self.has_errors = true;
        }
        self.diagnostics.push(d);
    }

    pub fn enter(&mut self, span: Span) {
        self.stack.push(span);
    }

    pub fn exit(&mut self) {
        self.stack.pop();
    }

    pub fn emit_string(&self, d: Diagnostic<usize>) -> String {
        let config = codespan_reporting::term::Config::default();
        let writer = BufferWriter::stdout(ColorChoice::Always);
        let mut buffer = writer.buffer();
        term::emit(&mut buffer, &config, &self.files, &d).unwrap();
        String::from_utf8_lossy(buffer.as_slice()).to_string()
    }

    pub fn dump(&mut self) {
        let writer = StandardStream::stderr(ColorChoice::Always);
        let config = codespan_reporting::term::Config::default();
        for d in self.diagnostics.drain(..) {
            term::emit(&mut writer.lock(), &config, &self.files, &d).unwrap();
        }
    }

    pub fn location<'c>(&self, context: &'c Context, span: &Span) -> ir::Location<'c> {
        if let Ok(name) = self.files.name(span.file_id) {
            let loc = self
                .files
                .location(span.file_id, span.begin.pos as usize)
                .unwrap();
            ir::Location::new(context, &name, loc.line_number, loc.column_number)
        } else {
            ir::Location::unknown(context)
        }
    }
}
