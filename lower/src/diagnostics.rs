use crate::ast::Span;
use crate::lower::FileDB;
use codespan_reporting::diagnostic::{Diagnostic, Severity};
use codespan_reporting::files::Files;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use melior::ir;
use melior::Context;

pub struct Diagnostics {
    pub files: FileDB,
    diagnostics: Vec<Diagnostic<usize>>,
    pub has_errors: bool,
}
impl Diagnostics {
    pub fn new() -> Self {
        Self {
            files: FileDB::new(),
            diagnostics: vec![],
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

    pub fn dump(&self) {
        let writer = StandardStream::stderr(ColorChoice::Always);
        let config = codespan_reporting::term::Config::default();
        for d in self.diagnostics.iter() {
            term::emit(&mut writer.lock(), &config, &self.files, &d).unwrap();
        }
    }

    pub fn location<'c>(&self, context: &'c Context, span: &Span) -> ir::Location<'c> {
        if let Ok(name) = self.files.name(span.file_id) {
            ir::Location::new(context, &name, span.begin.line + 1, span.begin.col + 1)
        } else {
            ir::Location::unknown(context)
        }
    }
}
