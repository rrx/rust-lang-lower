#[cfg(test)]
mod tests {
    //use super::*;
    use codespan_reporting::diagnostic::{Diagnostic, Label};
    use codespan_reporting::files::SimpleFiles;
    use codespan_reporting::term;
    use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
    //use thiserror::Error;

    #[test]
    fn test_loop() {
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
