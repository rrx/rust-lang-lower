use std::error::Error;
use std::fs::File;
use std::io::Write;
use std::path::Path;

use argh::FromArgs;
//use melior::ir;
use simple_logger::{set_up_color_terminal, SimpleLogger};

use lower::{
    default_context, CFGGraph, Diagnostics, Extra, IREnvironment, IRGraph, NodeBuilder,
    SimpleExtra, CFG,
};
use parse::starlark::Parser;
use parse::starlark::StarlarkParser;

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

    let location = lower::Location::unknown(&context);
    let mut module = lower::Module::new(location);
    //let mut parser: Parser<SimpleExtra> = Parser::new();
    let mut p: StarlarkParser<SimpleExtra> = StarlarkParser::new();
    let mut d = Diagnostics::new();
    //let mut cfg_g = CFGGraph::new();
    let mut b: NodeBuilder<SimpleExtra> = NodeBuilder::new();
    //let mut cfg: CFG<SimpleExtra> = CFG::new(&context, b.s("module"), &d, &mut cfg_g);

    for filename in config.inputs {
        p.parse_module(
            &filename,
            &context,
            &mut module,
            &mut b,
            &mut d,
            config.verbose,
        )?;
    }

    if config.verbose {
        module.as_operation().dump();
    }

    assert!(module.as_operation().verify());

    /*
    if config.lower {
        cfg.module(&context, &mut module, &mut cfg_g);
        if config.verbose {
            module.as_operation().dump();
        }
    }

    */
    if let Some(out_filename) = config.output {
        let mut output = File::create(out_filename)?;
        let s = module.as_operation().to_string();
        write!(output, "{}", s)?;
    }

    if config.exec {
        let exit_code = p.exec_main(&module, "target/debug");
        std::process::exit(exit_code);
    }

    Ok(())
}
