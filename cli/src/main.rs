use std::error::Error;
use std::fs::File;
use std::io::Write;
use std::path::Path;

use argh::FromArgs;
use melior::ir;
use simple_logger::{set_up_color_terminal, SimpleLogger};

use lower::ast::SimpleExtra;
use lower::cfg::{CFGGraph, CFG};
use lower::compile::default_context;
use lower::{Diagnostics, NodeBuilder};
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
    let mut parser: Parser<SimpleExtra> = Parser::new();
    let mut d = Diagnostics::new();
    let mut g = CFGGraph::new();
    //let mut lower = Lower::new(&context);
    let mut cfg: CFG<SimpleExtra> = CFG::new(&context, "module", &d, &mut g);

    for path in config.inputs {
        //let mut env: lower::Environment<SimpleExtra> = lower::Environment::default();
        let path = Path::new(&path);
        log::debug!("parsing: {}", path.to_str().unwrap());

        let filename = path.to_str().unwrap().to_string();
        let file_id = d.add_source(filename.clone(), std::fs::read_to_string(path)?);

        let mut b: NodeBuilder<SimpleExtra> = NodeBuilder::new();
        b.enter(file_id, &filename);

        let result = parser.parse(&path, None, file_id, &mut d);
        if config.verbose {
            d.dump();
        }
        if d.has_errors {
            println!("Errors in parsing");
            std::process::exit(1);
        }
        let ast = result?;

        let mut stack = vec![cfg.root()];
        let r = ast.lower(&context, &mut d, &mut cfg, &mut stack, &mut g, &mut b);
        assert_eq!(1, stack.len());
        if config.verbose {
            d.dump();
        }
        r?;
    }
    cfg.save_graph("out.dot", &g);
    if d.has_errors {
        std::process::exit(1);
    }

    if config.verbose {
        module.as_operation().dump();
    }
    assert!(module.as_operation().verify());

    if config.lower {
        cfg.module(&context, &mut module, &mut g);
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
        let exit_code = cfg.exec_main(&module, "target/debug/");
        std::process::exit(exit_code);
    }

    Ok(())
}
