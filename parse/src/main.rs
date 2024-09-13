use argh::FromArgs;
use simple_logger::{set_up_color_terminal, SimpleLogger};
use std::error::Error;
use std::fs::File;
use std::io::Write;

use lower_mlir::default_context;

use flat::{
    BlockifyError, Flatten, FlattenEnvironment, FlattenModule, ICodeModule, NodeBuilder, ValueId,
};
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

    /// verbose flag
    #[argh(switch, short = 'O')]
    optimize: bool,

    /// pass flag
    #[argh(switch, short = 'p', long = "enabled-passes")]
    enablepasses: bool,

    /// output file
    #[argh(option, short = 'o')]
    output: Option<String>,

    /// output file
    #[argh(option, long = "mlir-output")]
    mliroutput: Option<String>,

    /// compile file
    #[argh(option, short = 'i')]
    input: String,
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

    let location = lower_mlir::Location::unknown(&context);
    let mut module = lower_mlir::Module::new(location);
    let mut p: StarlarkParser = StarlarkParser::new();
    let mut b: NodeBuilder = NodeBuilder::new();

    let result = p.parse(&config.input, &mut b, config.verbose);
    if result.is_err() {
        b.spans.diagnostics_dump();
    }
    let ast = result?;

    let mut fenv = FlattenEnvironment::new();
    let r = Flatten::flatten_module(ast, &mut fenv, &mut b);
    if r.is_err() {
        b.spans.diagnostics_dump();
    }
    let f = r?;
    let m = FlattenModule::from_builder(f, &mut fenv, &mut b);
    m.dump(&mut b);
    m.block_graph("blocks.dot", &b);

    flat::flatten::scope_graph("scopes.dot", &fenv);

    b.spans.diagnostics_dump();
    if b.spans.has_errors {
        return Err(anyhow::Error::new(BlockifyError::Invalid).into());
    }

    let r = p.codegen(&m, ValueId::new(0), &context, &mut module, &mut b);
    m.block_graph2("cfg.mmd", &b)?;
    b.spans.diagnostics_dump();
    r?;

    b.types.dump();
    if config.verbose {
        module.as_operation().dump();
    }
    assert!(module.as_operation().verify());

    // run passes
    let pass_manager = lower_mlir::default_pass_manager(&context, config.optimize);
    pass_manager.run(&mut module).unwrap();
    if config.verbose {
        module.as_operation().dump();
    }
    assert!(module.as_operation().verify());

    let path = if let Some(out_filename) = config.output {
        out_filename
    } else {
        config.input
    };

    let mut path = std::path::PathBuf::from(path);
    if config.compile {
        path.set_extension("o");
        lower_mlir::save_object_file(&module, &path.to_str().unwrap());
        println!("Wrote: {:?}", &path.as_os_str());
    } else if config.exec {
        let exit_code = p.exec_main(&mut module, "target/debug");
        std::process::exit(exit_code);
    } else {
        path.set_extension("mlir");
        let s = module.as_operation().to_string();
        let mut output = File::create(path.clone())?;
        write!(output, "{}", s)?;
        println!("Wrote: {:?}", &path.as_os_str());
    }

    Ok(())
}
