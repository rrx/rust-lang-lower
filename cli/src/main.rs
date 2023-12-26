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
use lower::{Diagnostics, Extra, IREnvironment, IRGraph, NodeBuilder};
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
    let mut parser: Parser<SimpleExtra> = Parser::new();
    let mut d = Diagnostics::new();
    let mut cfg_g = CFGGraph::new();
    let mut b: NodeBuilder<SimpleExtra> = NodeBuilder::new();
    let mut cfg: CFG<SimpleExtra> = CFG::new(&context, b.s("module"), &d, &mut cfg_g);

    for path in config.inputs {
        //let mut env: lower::Environment<SimpleExtra> = lower::Environment::default();
        let path = Path::new(&path);
        log::debug!("parsing: {}", path.to_str().unwrap());

        let filename = path.to_str().unwrap().to_string();
        let file_id = d.add_source(filename.clone(), std::fs::read_to_string(path)?);

        b.enter(file_id, &filename);

        let result = parser.parse(&path, None, file_id, &mut d, &mut b);
        if config.verbose {
            d.dump();
        }
        if d.has_errors {
            println!("Errors in parsing");
            std::process::exit(1);
        }

        let ast = result?.normalize(&mut cfg, &mut d, &mut b);

        //let mut stack = vec![cfg.root()];
        /*
        let r = ast.lower(&context, &mut d, &mut cfg, &mut stack, &mut g, &mut b);
        assert_eq!(1, stack.len());
        if config.verbose {
            d.dump();
        }
        r?;
        */

        // lower ast to ir
        let mut env = IREnvironment::new();
        let mut g = IRGraph::new();
        let index = env.add_block(b.s("module"), vec![], &d, &mut g);
        env.enter_block(index, ast.extra.get_span());
        let r = ast.lower_ir_expr(&mut d, &mut env, &mut g, &mut b);
        if config.verbose {
            d.dump();
        }
        //assert!(!d.has_errors);
        let (ir, _ty) = r.unwrap();
        ir.dump(&b, 0);
        assert_eq!(1, env.stack_size());

        // lower to mlir
        let mut stack = vec![cfg.root()];
        let r = ir.lower_mlir(
            &context, &mut d, &mut cfg, &mut stack, &mut g, &mut cfg_g, &mut b,
        );
        d.dump();
        r.unwrap();
        env.save_graph("out.dot", &g, &b);
    }
    cfg.save_graph("out.dot", &cfg_g, &b);
    if d.has_errors {
        std::process::exit(1);
    }

    let mut module = ir::Module::new(location);
    if config.verbose {
        module.as_operation().dump();
    }
    assert!(module.as_operation().verify());

    if config.lower {
        cfg.module(&context, &mut module, &mut cfg_g);
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
