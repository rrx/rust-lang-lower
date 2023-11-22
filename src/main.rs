use std::error::Error;
use std::fs::File;
use std::io::Read;
use std::io::Write;
use std::path::Path;

use melior::{
    dialect::DialectRegistry,
    ir, pass,
    utility::{register_all_dialects, register_all_llvm_translations},
    Context, ExecutionEngine,
};

use lower::ast::{AstNode, SimpleExtra};
use lower::lower::lower_expr;
use lower::starlark::Parser;

fn main() -> Result<(), Box<dyn Error>> {
    let context = Context::new();
    context.set_allow_unregistered_dialects(true);
    context.enable_multi_threading(true);

    let pass_manager = pass::PassManager::new(&context);
    pass_manager.enable_verifier(true);
    //pass_manager.enable_ir_printing();

    // lower to llvm
    /*
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
    */

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
    let module = ir::Module::new(location);

    let mut parser = Parser::new();
    let path = Path::new("examples/test_simple.py");
    let ast: AstNode<SimpleExtra> = parser.parse(&context, &path)?;
    parser.dump();
    let ops = lower_expr(&context, ast, &parser.files);
    for op in ops {
        module.body().append_operation(op);
    }

    module.as_operation().dump();
    assert!(module.as_operation().verify());
    let mut output = File::create("out.mlir")?;
    let s = module.as_operation().to_string();
    write!(output, "{}", s)?;

    /*
    pass_manager.run(&mut module)?;

    module.as_operation().dump();
    let mut output = File::create("out.ll")?;
    let s = module.as_operation().to_string();
    write!(output, "{}", s)?;

    let engine = ExecutionEngine::new(&module, 0, &[], true);
    engine.dump_to_object_file("out.o");
    */
    Ok(())
}
