use melior::ExecutionEngine;
use melior::{
    dialect::DialectRegistry,
    ir, pass,
    utility::{register_all_dialects, register_all_llvm_translations},
    Context,
};

pub fn save_object_file<'c>(module: &ir::Module<'c>, filename: &str) {
    let engine = ExecutionEngine::new(module, 0, &[], true);
    engine.dump_to_object_file(filename);
}

pub fn exec_main<'c>(shared: &[String], module: &ir::Module<'c>, libpath: &str) -> i32 {
    let paths = shared
        .iter()
        .map(|s| {
            let mut path = format!("{}/{}.so", libpath, s);
            path.push('\0');
            path
        })
        .collect::<Vec<_>>();
    let shared = paths.iter().map(|p| p.as_str()).collect::<Vec<_>>();

    let engine = ExecutionEngine::new(&module, 0, &shared, false);
    let mut result: i32 = -1;
    unsafe {
        engine
            .invoke_packed("main", &mut [&mut result as *mut i32 as *mut ()])
            .unwrap();
        println!("exec: {}", result);
        result
    }
}

pub fn default_context() -> Context {
    let context = Context::new();
    context.set_allow_unregistered_dialects(true);
    context.enable_multi_threading(true);

    context.attach_diagnostic_handler(|diagnostic| {
        let location = diagnostic.location();
        log::error!("E: {}: {}", diagnostic, location);
        true
    });

    let registry = DialectRegistry::new();
    register_all_dialects(&registry);
    context.append_dialect_registry(&registry);
    context.load_all_available_dialects();
    register_all_llvm_translations(&context);

    context
}

pub fn default_pass_manager<'c>(context: &Context, optimize: bool) -> pass::PassManager<'c> {
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

    if optimize {
        // some optimization passes
        //pass_manager.add_pass(pass::transform::create_inliner());
        pass_manager.add_pass(pass::transform::create_canonicalizer());
        pass_manager.add_pass(pass::transform::create_cse());
        pass_manager.add_pass(pass::transform::create_sccp());
        pass_manager.add_pass(pass::transform::create_control_flow_sink());
        pass_manager.add_pass(pass::transform::create_symbol_privatize());
    }

    pass_manager
}
