use std::error::Error;
use std::fs::File;
use std::io::Write;
use std::path::Path;

use melior::{
    dialect::DialectRegistry,
    ir,
    pass,
    utility::{register_all_dialects, register_all_llvm_translations},
    Context,
    ExecutionEngine,
};

use codespan_reporting::files::SimpleFiles;
use lower::ast::{AstNode, SimpleExtra};
use lower::lower::Lower;
use parse::starlark::Parser;

use argh::FromArgs;

#[derive(FromArgs, Debug)]
/// Compile Stuff
struct Config {
    /// compile flag
    #[argh(switch, short='l')]
    lower: bool,

    /// output file
    #[argh(option, short='o')]
    output: Option<String>,

    /// compile file
    #[argh(positional)]
    inputs: Vec<String>,
}

fn main() -> Result<(), Box<dyn Error>> {
    //let args: Vec<String> = std::env::args().skip(1).collect();
    let config: Config = argh::from_env();
    println!("config: {:?}", config);
    let context = Context::new();
    context.set_allow_unregistered_dialects(true);
    context.enable_multi_threading(true);

    let pass_manager = pass::PassManager::new(&context);
    pass_manager.enable_verifier(true);
    //pass_manager.enable_ir_printing();

    // lower to llvm
    pass_manager.add_pass(pass::conversion::create_scf_to_control_flow());
    pass_manager.add_pass(pass::conversion::create_control_flow_to_llvm());
    pass_manager.add_pass(pass::conversion::create_index_to_llvm());
    pass_manager.add_pass(pass::conversion::create_math_to_llvm());
    pass_manager.add_pass(pass::conversion::create_func_to_llvm());
    pass_manager.add_pass(pass::conversion::create_arith_to_llvm());
    //pass_manager.add_pass(pass::conversion::create_async_to_llvm());
    pass_manager.add_pass(pass::conversion::create_complex_to_llvm());
    pass_manager.add_pass(pass::conversion::create_math_to_llvm());
    pass_manager.add_pass(pass::conversion::create_finalize_mem_ref_to_llvm());
    pass_manager.add_pass(pass::conversion::create_reconcile_unrealized_casts());

    // some optimization passes
    //pass_manager.add_pass(pass::transform::create_inliner());
    pass_manager.add_pass(pass::transform::create_canonicalizer());
    pass_manager.add_pass(pass::transform::create_cse());
    pass_manager.add_pass(pass::transform::create_sccp());
    pass_manager.add_pass(pass::transform::create_control_flow_sink());
    pass_manager.add_pass(pass::transform::create_symbol_privatize());

    context.attach_diagnostic_handler(|diagnostic| {
        let location = diagnostic.location();
        eprintln!("E: {}: {}", diagnostic, location);
        true
    });

    let registry = DialectRegistry::new();
    register_all_dialects(&registry);
    context.append_dialect_registry(&registry);
    context.load_all_available_dialects();
    register_all_llvm_translations(&context);

    let location = ir::Location::unknown(&context);
    let mut module = ir::Module::new(location);

    let mut files = SimpleFiles::new();
    let mut parser = Parser::new();

    let default_out = "out.mlir".to_string();
    let out_filename = config.output.as_ref().unwrap_or(&default_out);
    let mut output = File::create(out_filename)?;

    for path in config.inputs {
        let path = Path::new(&path);
        println!("path: {:?}", path);
        let result = parser.parse(&path, &mut files);
        parser.dump(&files);
        let ast: AstNode<SimpleExtra> = result?;

        let lower = Lower::new(&context, &files);
        let mut env: lower::scope::ScopeStack<lower::lower::Data> =
            lower::scope::ScopeStack::default();
        lower.lower_expr(ast, &mut env);
        for op in env.take_ops() {
            module.body().append_operation(op);
        }

    }

    module.as_operation().dump();
    assert!(module.as_operation().verify());

    let default_out = "out.mlir".to_string();
    let out_filename = config.output.as_ref().unwrap_or(&default_out);
    let mut output = File::create(out_filename)?;
    if config.lower {
        pass_manager.run(&mut module)?;
        module.as_operation().dump();
    }

    let s = module.as_operation().to_string();
    write!(output, "{}", s)?;
    //let engine = ExecutionEngine::new(&module, 0, &[], true);
    //engine.dump_to_object_file("out.o");

    Ok(())
}
