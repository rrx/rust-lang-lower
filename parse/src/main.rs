use argh::FromArgs;
use simple_logger::{set_up_color_terminal, SimpleLogger};
use std::error::Error;
use std::fs::File;
use std::io::Write;

use lower_mlir::default_context;

use flat::{BlockifyError, Flatten, FlattenMode, FlattenModule, ICodeModule, NodeBuilder, ValueId};
use parse::starlark::StarlarkParser;
use std::path::PathBuf;

#[derive(FromArgs, Debug)]
/// Compile Stuff
struct Config {
    /// compile flag
    #[argh(switch, short = 'c')]
    compile: bool,

    /// interp flag
    #[argh(switch)]
    interp: bool,

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
    let mut b: NodeBuilder = NodeBuilder::new();
    let r = run(&config, &mut b);
    b.spans.diagnostics_dump();
    let exit_code = r?;
    std::process::exit(exit_code);
}

fn run(config: &Config, b: &mut NodeBuilder) -> Result<i32, Box<dyn Error>> {
    if config.verbose {
        log::set_max_level(log::LevelFilter::Warn);
    } else {
        log::set_max_level(log::LevelFilter::Info);
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

    let ast = p.parse(&config.input, b, config.verbose)?;

    let mut f = Flatten::flatten_module(ast, b)?;

    f.push_bake_main(b)?;

    let m = FlattenModule::build(f, b)?;

    let directory = std::path::Path::new(output_filename)
        .parent()
        .map(|dir| dir.to_string_lossy().into_owned())
        .unwrap();
    std::fs::create_dir_all(directory).unwrap();

    let pre_graph_path = make_path(&output_filename, "graph.dot");
    m.save_graph(&pre_graph_path, &b);

    let mut blocks_path = path.clone();
    blocks_path.set_extension("blocks.dot");
    m.block_graph(blocks_path.clone().to_str().unwrap(), &b);

    let mut scopes_path = path.clone();
    scopes_path.set_extension("scopes.dot");
    m.scopes.scope_graph(scopes_path.clone().to_str().unwrap());

    let mut cont_path = path.clone();
    cont_path.set_extension("cont.dot");
    m.cont_graph(cont_path.clone().to_str().unwrap(), b);

    let mut cfg_path = path.clone();
    cfg_path.set_extension("cfg.mmd");
    m.flow_graph(cfg_path.clone().to_str().unwrap(), &b)?;

    let table_path = make_path(&output_filename, "table.txt");
    m.dump_code_table(&table_path, b);
    m.dump_scopes();
    m.dump_variants(b);

    if b.spans.has_errors {
        return Err(anyhow::Error::new(BlockifyError::Invalid).into());
    }

    p.codegen(&m, ValueId::new(0), &context, &mut module, b)?;

    //b.types.dump();
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

    if config.compile {
        let mut path = path.clone();
        path.set_extension("o");
        lower_mlir::save_object_file(&module, &path.to_str().unwrap());
        println!("Wrote: {:?}", &path.as_os_str());

        let mut path = path.clone();
        path.set_extension("mlir");
        let s = module.as_operation().to_string();
        let mut output = File::create(path.clone())?;
        write!(output, "{}", s)?;
        println!("Wrote: {:?}", &path.as_os_str());
    }

    let exit_code = if config.interp {
        //let exit_code = p.interp(&m, "target/debug", b);
        let exit_code = flat::interp::interp(&m.shared_libraries(), &m, "target/debug", b);
        exit_code
    } else if config.exec {
        println!("exec");
        let exit_code =
            lower_mlir::compile::exec_main(&m.shared_libraries(), &module, "target/debug");
        //let exit_code = p.exec_main(&mut module, "target/debug");
        exit_code
    } else {
        let mut path = path.clone();
        path.set_extension("mlir");
        let s = module.as_operation().to_string();
        let mut output = File::create(path.clone())?;
        write!(output, "{}", s)?;
        println!("Wrote: {:?}", &path.as_os_str());
        0
    };
    Ok(exit_code)
}
