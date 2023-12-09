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

impl<'c, E: ast::Extra> lower::Lower<'c, E> {
    pub fn run_ast(
        &mut self,
        ast: ast::AstNode<E>,
        env: &mut scope::ScopeStack<'c, lower::Data>,
    ) -> i32 {
        run_ast(ast, self, env)
    }
}

pub struct CompilerContext<'c, E> {
    context: melior::Context,
    pub env: scope::ScopeStack<'c, lower::Data>,
    pass_manager: pass::PassManager<'c>,
    _e: std::marker::PhantomData<E>,
}

impl<'c, E: ast::Extra> CompilerContext<'c, E> {
    pub fn new() -> Self {
        let context = melior::Context::new();
        context.attach_diagnostic_handler(|diagnostic| {
            let location = diagnostic.location();
            log::error!("E: {}: {}", diagnostic, location);
            true
        });
        let env = scope::ScopeStack::default();

        // registry
        let registry = DialectRegistry::new();
        register_all_dialects(&registry);
        context.append_dialect_registry(&registry);
        context.load_all_available_dialects();
        register_all_llvm_translations(&context);

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
        Self {
            context,
            env,
            pass_manager,
            _e: std::marker::PhantomData::default(),
        }
    }

    pub fn module(&self) -> ir::Module<'c> {
        let location = ir::Location::unknown(&self.context);
        let module = ir::Module::new(location);
        module
    }

    pub fn compiler(&'c self) -> Compiler<'c, E> {
        let module = self.module();
        let lower = lower::Lower::new(&self.context);
        Compiler {
            module,
            lower,
            _e: std::marker::PhantomData::default(),
        }
    }

    pub fn merge(&mut self, module: &ir::Module<'c>, ast: ast::AstNode<E>) {
        //let lower = lower::Lower::new(&self.context, &self.files);
        //lower.lower_expr(ast, &mut self.env);
        for op in self.env.take_ops() {
            module.body().append_operation(op);
        }
    }
}

pub struct Compiler<'c, E> {
    module: ir::Module<'c>,
    lower: lower::Lower<'c, E>,
    _e: std::marker::PhantomData<E>,
}

impl<'c, E: ast::Extra> Compiler<'c, E> {
    /*
    pub fn new(context: &'c mut CompilerContext<'c, E>) -> Self {
        let module = context.module();
        let lower = lower::Lower::new(&context.context, &context.files);
        Self { module, lower, _e: std::marker::PhantomData::default() }
    }
    */

    pub fn module(&mut self, context: &'c mut CompilerContext<'c, E>, ast: ast::AstNode<E>) {
        //let lower = lower::Lower::new(&context.context, &context.files);
        self.lower.lower_expr(ast, &mut context.env);
        for op in context.env.take_ops() {
            self.module.body().append_operation(op);
        }
    }

    pub fn run(&mut self, context: &mut CompilerContext<'c, E>) -> i32 {
        log::debug!(
            "before {}",
            self.module
                .as_operation()
                .to_string_with_flags(OperationPrintingFlags::new())
                .unwrap()
        );
        context.pass_manager.run(&mut self.module).unwrap();
        assert!(self.module.as_operation().verify());
        log::debug!(
            "after pass {}",
            self.module
                .as_operation()
                .to_string_with_flags(OperationPrintingFlags::new())
                .unwrap()
        );

        let mut path = "../target/debug/prelude.so".to_string();
        path.push('\0');
        let engine = ExecutionEngine::new(&self.module, 0, &[&path], true);
        let mut result: i32 = -1;
        unsafe {
            engine
                .invoke_packed("main", &mut [&mut result as *mut i32 as *mut ()])
                .unwrap();
            result
        }
    }
}

pub fn run_ast<'c, E: ast::Extra>(
    ast: ast::AstNode<E>,
    lower: &mut lower::Lower<'c, E>,
    env: &mut scope::ScopeStack<'c, lower::Data>,
) -> i32 {
    // passes
    let pass_manager = default_pass_manager(lower.context);

    let location = ir::Location::unknown(lower.context);
    let mut module = ir::Module::new(location);

    lower.module(&mut module, ast, env);

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

    let mut path = "../target/debug/prelude.so".to_string();
    path.push('\0');
    let engine = ExecutionEngine::new(&module, 0, &[&path], true);
    let mut result: i32 = -1;
    unsafe {
        engine
            .invoke_packed("main", &mut [&mut result as *mut i32 as *mut ()])
            .unwrap();
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

pub fn default_pass_manager(context: &Context) -> pass::PassManager {
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
    pass_manager
}
