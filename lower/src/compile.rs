use crate::ast;
use crate::lower;
use crate::scope;
use melior::ir::operation::OperationPrintingFlags;
use melior::ExecutionEngine;
use melior::{
    dialect::DialectRegistry,
    ir, pass,
    utility::{register_all_dialects, register_all_llvm_translations},
};

impl<'c, E: ast::Extra> lower::Lower<'c, E> {
    pub fn run_ast(
        &mut self,
        ast: ast::AstNode<E>,
        env: &mut scope::ScopeStack<'c, lower::Data>,
    ) -> i32 {
        run_ast(ast, self, env)
    }
}

pub fn run_ast<'c, E: ast::Extra>(
    ast: ast::AstNode<E>,
    lower: &mut lower::Lower<'c, E>,
    env: &mut scope::ScopeStack<'c, lower::Data>,
) -> i32 {
    //let context = Context::new();
    //let c = &context;
    lower.context.set_allow_unregistered_dialects(true);

    // passes
    let pass_manager = pass::PassManager::new(lower.context);
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
    pass_manager.add_pass(pass::conversion::create_bufferization_to_mem_ref());
    //pass_manager.add_pass(pass::conversion::create_map_mem_ref_storage_class());
    pass_manager.add_pass(pass::conversion::create_finalize_mem_ref_to_llvm());
    pass_manager.add_pass(pass::conversion::create_reconcile_unrealized_casts());

    // some optimization passes
    //pass_manager.add_pass(pass::transform::create_inliner());
    pass_manager.add_pass(pass::transform::create_canonicalizer());
    pass_manager.add_pass(pass::transform::create_cse());
    pass_manager.add_pass(pass::transform::create_sccp());
    pass_manager.add_pass(pass::transform::create_control_flow_sink());
    pass_manager.add_pass(pass::transform::create_symbol_privatize());

    lower.context.attach_diagnostic_handler(|diagnostic| {
        let location = diagnostic.location();
        log::error!("E: {}: {}", diagnostic, location);
        true
    });

    // registry
    let registry = DialectRegistry::new();
    register_all_dialects(&registry);
    lower.context.append_dialect_registry(&registry);
    lower.context.load_all_available_dialects();
    register_all_llvm_translations(lower.context);

    let location = ir::Location::unknown(lower.context);
    let mut module = ir::Module::new(location);

    //let lower = lower::Lower::new(c, &files);
    lower.lower_expr(ast, env);
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
    let mut result: i32 = -1;
    unsafe {
        engine
            .invoke_packed("main", &mut [&mut result as *mut i32 as *mut ()])
            .unwrap();
        result
    }
}
