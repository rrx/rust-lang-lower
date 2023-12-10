use std::error::Error;
use std::fs::File;
use std::io::Write;
use std::path::Path;

use argh::FromArgs;
use melior::{ir, ExecutionEngine};
use simple_logger::{set_up_color_terminal, SimpleLogger};

use lower::ast::{AstNode, SimpleExtra};
use lower::compile::default_context;
use lower::{Diagnostics, Lower};
use parse::starlark::Parser;

#[derive(FromArgs, Debug)]
/// Compile Stuff
struct Config {
    /// compile flag
    #[argh(switch, short = 'c')]
    compile: bool,

    /// lower flag
    #[argh(switch, short = 'l')]
    lower: bool,

    /// exec flag
    #[argh(switch, short = 'x')]
    exec: bool,

    /// verbose flag
    #[argh(switch, short = 'v')]
    verbose: bool,

    /// output file
    #[argh(option, short = 'o')]
    output: Option<String>,

    /// compile file
    #[argh(positional)]
    inputs: Vec<String>,
}

fn main() -> Result<(), Box<dyn Error>> {
    set_up_color_terminal();
    SimpleLogger::new().init().unwrap();
    let config: Config = argh::from_env();

    if config.verbose {
        log::set_max_level(log::LevelFilter::Trace);
    } else {
        log::set_max_level(log::LevelFilter::Warn);
    }

    log::debug!("config: {:?}", config);
    let context = default_context();

    let location = ir::Location::unknown(&context);
    let mut module = ir::Module::new(location);
    let mut parser = Parser::new();
    let mut d = Diagnostics::new();
    let mut lower = Lower::new(&context);

    for path in config.inputs {
        let mut env: lower::scope::ScopeStack<lower::lower::Data> =
            lower::scope::ScopeStack::default();
        env.enter_static();
        let path = Path::new(&path);
        log::debug!("parsing: {}", path.to_str().unwrap());

        let file_id = d.add_source(
            path.to_str().unwrap().to_string(),
            std::fs::read_to_string(path)?,
        );

        let result = parser.parse(&path, None, file_id, &mut d);
        if config.verbose {
            d.dump();
        }
        if d.has_errors {
            std::process::exit(1);
        }
        let ast: AstNode<SimpleExtra> = result?;

        assert_eq!(1, env.layer_count());
        lower.module_lower(&mut module, ast, env, &mut d);
        //env.exit();
    }

    if config.verbose {
        module.as_operation().dump();
    }
    assert!(module.as_operation().verify());

    if config.lower {
        lower.module_passes(&mut module);
        if config.verbose {
            module.as_operation().dump();
        }
    }

    if let Some(out_filename) = config.output {
        let mut output = File::create(out_filename)?;
        let s = module.as_operation().to_string();
        write!(output, "{}", s)?;
    }

    if config.exec {
        let mut path = "./target/debug/prelude.so".to_string();
        path.push('\0');
        let engine = ExecutionEngine::new(&module, 0, &[&path], true);
        let mut result: i32 = -1;
        unsafe {
            engine
                .invoke_packed("main", &mut [&mut result as *mut i32 as *mut ()])
                .unwrap();
            println!("exec: {}", result);
            std::process::exit(result);
        }
    }

    Ok(())
}
