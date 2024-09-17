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
use std::path::PathBuf;

#[derive(FromArgs, Debug)]
/// Compile Stuff
struct Config {
    /// compile flag
    #[argh(switch, short = 'c')]
    compile: bool,

    /// template
    #[argh(switch, short = 't')]
    template: bool,

    /// exec flag
    #[argh(switch, short = 'x')]
    exec: bool,

    /// verbose flag
    #[argh(switch, short = 'v')]
    verbose: bool,

    /// verbose flag
    #[argh(switch, short = 'O')]
    optimize: bool,

    /// output file
    #[argh(option, short = 'o')]
    output: Option<String>,

    /// compile file
    #[argh(option, short = 'i')]
    input: String,
}

fn make_path<'a>(path: &'a str, extension: &str) -> String {
    let mut path = PathBuf::from(&path);
    path.set_extension(extension);
    path.to_str().unwrap().to_string()
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

    let output_filename;
    let path = if let Some(out_filename) = &config.output {
        output_filename = out_filename;
        std::path::PathBuf::from(out_filename)
    } else {
        output_filename = &config.input;
        let mut path = PathBuf::from(&config.input);
        path.set_extension("");
        path
    };

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
    let mut f = r?;

    if config.template {
    } else {
        let r = f.push_bake_main(&mut fenv, &mut b);
        if r.is_err() {
            b.spans.diagnostics_dump();
        }
        r?;
    }

    //f.dump_blocks();

    let m = FlattenModule::from_builder(f, &mut fenv, &mut b);
    //b.labels.pool.dump();
    m.dump(&fenv, &b);

    let out_graph_path = make_path(&output_filename, "graph.dot");
    m.dump_graph(&out_graph_path, &mut b);

    let mut blocks_path = path.clone();
    blocks_path.set_extension("blocks.dot");
    m.block_graph(blocks_path.clone().to_str().unwrap(), &b);

    let mut scopes_path = path.clone();
    scopes_path.set_extension("scopes.dot");
    flat::flatten::scope_graph(scopes_path.clone().to_str().unwrap(), &fenv);

    let table_path = make_path(&output_filename, "table.txt");
    m.dump_code_table(&table_path, &mut b);

    let mut cfg_path = path.clone();
    cfg_path.set_extension("cfg.mmd");
    m.block_graph2(cfg_path.clone().to_str().unwrap(), &b)?;
    flat::flatten::scope_graph(path.clone().to_str().unwrap(), &fenv);

    if b.spans.has_errors {
        b.spans.diagnostics_dump();
        return Err(anyhow::Error::new(BlockifyError::Invalid).into());
    }

    if config.template {
    } else {
        let r = p.codegen(&m, ValueId::new(0), &context, &mut module, &mut b);
        b.spans.diagnostics_dump();
        r?;

        //b.types.dump();
        if config.verbose {
            //module.as_operation().dump();
        }
        assert!(module.as_operation().verify());

        // run passes
        let pass_manager = lower_mlir::default_pass_manager(&context, config.optimize);
        pass_manager.run(&mut module).unwrap();
        if config.verbose {
            //module.as_operation().dump();
        }
        assert!(module.as_operation().verify());
    }

    if config.compile {
        let mut path = path.clone();
        path.set_extension("o");
        lower_mlir::save_object_file(&module, &path.to_str().unwrap());
        println!("Wrote: {:?}", &path.as_os_str());
    } else if config.exec {
        let exit_code = p.exec_main(&mut module, "target/debug");
        std::process::exit(exit_code);
    } else {
        let mut path = path.clone();
        path.set_extension("mlir");
        let s = module.as_operation().to_string();
        let mut output = File::create(path.clone())?;
        write!(output, "{}", s)?;
        println!("Wrote: {:?}", &path.as_os_str());
    }

    Ok(())
}
