use codespan_reporting::diagnostic::{Diagnostic, Label, Severity};
use codespan_reporting::files::Files;
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{BufferWriter, ColorChoice, StandardStream};

use indexmap::IndexSet;
use thiserror::Error;

use crate::{CodeLocation, Span, SpanId};

pub type FileDB = SimpleFiles<String, String>;

#[derive(Error, Debug)]
pub enum ParseError {
    #[error("Invalid")]
    Invalid,
}

pub struct Diagnostics {
    pub files: FileDB,
    diagnostics: Vec<Diagnostic<usize>>,
    stack: Vec<Span>,
    pub has_errors: bool,
    spans: IndexSet<Span>,
}

impl Diagnostics {
    pub fn new() -> Self {
        let s = Self {
            files: FileDB::new(),
            diagnostics: vec![],
            stack: vec![],
            has_errors: false,
            spans: IndexSet::new(),
        };
        s.init()
    }

    pub fn init(mut self) -> Self {
        // make sure the first span is unknown
        self.get_span_unknown();
        self
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
        //if let Some(span_id) = span_id {
        self.spans.get_index(span_id.index()).unwrap().clone()
        //Some(Span::new(*file_id, *begin, *end))
        //} else {
        //Span::Unknown
        //}
    }

    pub fn get_span(&mut self, file_id: usize, begin: CodeLocation, end: CodeLocation) -> SpanId {
        let v = Span::new(file_id, begin, end);
        let (index, _) = self.spans.insert_full(v);
        let span_id = SpanId::new(index as u32);
        span_id
        //Span::new(file_id, begin, end)
    }

    pub fn add_source(&mut self, filename: String, content: String) -> usize {
        self.files.add(filename, content)
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

    pub fn primary(&self, msg: &str, span: &Span) -> Label<usize> {
        if let Span::Loc(span) = span {
            let r = span.begin.pos as usize..span.end.pos as usize;
            Label::primary(span.file_id, r).with_message(msg)
        } else {
            Label::primary(0, 0..0)
        }
    }

    pub fn secondary(&self, msg: &str, span: &Span) -> Label<usize> {
        if let Span::Loc(span) = span {
            let r = span.begin.pos as usize..span.end.pos as usize;
            Label::secondary(span.file_id, r).with_message(msg)
        } else {
            Label::secondary(0, 0..0)
        }
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
}
