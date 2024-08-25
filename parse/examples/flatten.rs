use argh::FromArgs;
use simple_logger::{set_up_color_terminal, SimpleLogger};
use std::error::Error;
use std::fs::File;
use std::io::Write;

use lower_mlir::default_context;

use flat::{Flatten, FlattenEnvironment, ICodeModule, NodeBuilder, ValueId};
use parse::starlark::StarlarkParser;

#[derive(FromArgs, Debug)]
/// Compile Stuff
struct Config {
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
    let mut p: StarlarkParser = StarlarkParser::new();
    let mut b: NodeBuilder = NodeBuilder::new();
    let context = default_context();
    let location = lower_mlir::Location::unknown(&context);
    let mut module = lower_mlir::Module::new(location);

    for filename in config.inputs {
        let result = p.parse(&filename, &mut b, true);
        b.spans.diagnostics_dump();
        let ast = result?;

        let mut fenv = FlattenEnvironment::new();
        let r = Flatten::flatten_module(ast, &mut fenv, &mut b);
        b.spans.diagnostics_dump();
        let mut f = r?;
        let r = f.run_loop(&mut fenv, &mut b);
        f.dump_ast(&b);
        b.spans.diagnostics_dump();
        let _ = r?;
        let m = f.module(&mut fenv, &b);
        m.dump(&b);

        let r = p.lower(&m, ValueId::new(0), &context, &mut module, &mut b);
        b.spans.diagnostics_dump();
        r?;
    }

    if config.verbose {
        module.as_operation().dump();
    }

    assert!(module.as_operation().verify());

    if let Some(out_filename) = config.output {
        let mut output = File::create(out_filename)?;
        let s = module.as_operation().to_string();
        write!(output, "{}", s)?;
    }

    if config.exec {
        let exit_code = p.exec_main(&context, &mut module, "target/debug", config.verbose);
        println!("Exit: {}", exit_code);
        std::process::exit(exit_code);
    }

    Ok(())
}
