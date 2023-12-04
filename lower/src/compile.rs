use crate::ast;
use crate::lower;
use crate::scope;
use melior::ir::operation::OperationPrintingFlags;
use melior::ExecutionEngine;
use melior::{
    dialect::DialectRegistry,
    ir, pass,
    utility::{register_all_dialects, register_all_llvm_translations},
    Context,
};

pub fn run_test_content<E: ast::Extra>(expected: i64, files: &lower::FileDB, ast: ast::AstNode<E>) {
    let context = Context::new();
    context.set_allow_unregistered_dialects(true);

    // passes
    let pass_manager = pass::PassManager::new(&context);
    pass_manager.enable_verifier(true);
    // lower to llvm
    pass_manager.add_pass(pass::conversion::create_scf_to_control_flow());
    pass_manager.add_pass(pass::conversion::create_control_flow_to_llvm());
    pass_manager.add_pass(pass::conversion::create_index_to_llvm());
    pass_manager.add_pass(pass::conversion::create_math_to_llvm());
    pass_manager.add_pass(pass::conversion::create_func_to_llvm());
    pass_manager.add_pass(pass::conversion::create_arith_to_llvm());
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
        log::error!("E: {}: {}", diagnostic, location);
        true
    });

    // registry
    let registry = DialectRegistry::new();
    register_all_dialects(&registry);
    context.append_dialect_registry(&registry);
    context.load_all_available_dialects();
    register_all_llvm_translations(&context);

    let location = ir::Location::unknown(&context);
    let mut module = ir::Module::new(location);

    let lower = lower::Lower::new(&context, &files);
    let mut env: crate::scope::ScopeStack<lower::Data> = scope::ScopeStack::default();
    lower.lower_expr(ast, &mut env);
    for op in env.take_ops() {
        module.body().append_operation(op);
    }

    log::debug!(
        "before {}",
        module
            .as_operation()
            .to_string_with_flags(OperationPrintingFlags::new())
            .unwrap()
    );
    pass_manager.run(&mut module).unwrap();
    assert!(module.as_operation().verify());
    log::debug!(
        "after pass {}",
        module
            .as_operation()
            .to_string_with_flags(OperationPrintingFlags::new())
            .unwrap()
    );
    let engine = ExecutionEngine::new(&module, 0, &[], true);
    let mut result: i64 = -1;
    unsafe {
        engine
            .invoke_packed("main", &mut [&mut result as *mut i64 as *mut ()])
            .unwrap();
        assert_eq!(result, expected);
    }
}
