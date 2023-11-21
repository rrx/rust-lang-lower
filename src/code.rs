//use miette::{Diagnostic, IntoDiagnostic, Report, SourceSpan, WrapErr};
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use thiserror::Error;

/*
#[derive(Debug)]
pub struct CodeStore {
    pub data: im::HashMap<String, String>
}
impl CodeStore {
    pub fn new() -> Self {
        Self { data: im::HashMap::new() }
    }

    pub fn insert(self, k: String, v: String) -> Self {
        Self { data: self.data.update(k, v) }
    }

}


#[derive(Diagnostic, Debug, Error)]
#[error("oops")]
#[diagnostic()]
pub struct CodeError {
    //#[source_code]
    //code:
    #[label]
    span: SourceSpan
}

*/

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_loop() {
        /*
        let store = CodeStore::new();
        let store = store.insert("asdf.py".to_string(), "asdf".to_string());
        let err = CodeError { span: (2..3).into() };
        println!("{}", err.into_diagnostic());//.with_source_code(store.data.get("asdf.py").unwrap()));
        */

        let mut files = SimpleFiles::new();
        let file_id = files.add("asdf.py", "asdf");
        let diagnostic: Diagnostic<usize> = Diagnostic::error()
            .with_labels(vec![Label::primary(file_id, 2..3).with_message("something")])
            .with_message("error");
        let writer = StandardStream::stderr(ColorChoice::Always);
        let config = codespan_reporting::term::Config::default();
        term::emit(&mut writer.lock(), &config, &files, &diagnostic).unwrap();
    }
}
