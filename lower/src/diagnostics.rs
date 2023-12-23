use crate::ast::Span;
use codespan_reporting::diagnostic::{Diagnostic, Severity};
use codespan_reporting::files::Files;
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use melior::ir;
use melior::Context;
use thiserror::Error;

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
}
impl Diagnostics {
    pub fn new() -> Self {
        Self {
            files: FileDB::new(),
            diagnostics: vec![],
            stack: vec![],
            has_errors: false,
        }
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
