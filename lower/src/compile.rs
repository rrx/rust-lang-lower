use crate::ast;
use crate::lower;
//use crate::scope;
use crate::{Diagnostics, Environment, NodeBuilder};
use anyhow::Result;
use melior::ir::operation::OperationPrintingFlags;
use melior::ExecutionEngine;
use melior::{
    dialect::DialectRegistry,
    ir, pass,
    utility::{register_all_dialects, register_all_llvm_translations},
    Context,
};

impl<'c, E: ast::Extra> lower::Lower<'c, E> {
    pub fn add_shared(&mut self, s: &str) {
        self.shared.insert(s.to_string());
    }

    pub fn module_lower(
        &mut self,
        module: &mut ir::Module<'c>,
        expr: ast::AstNode<E>,
        env: &mut Environment<'c, E>,
        d: &mut Diagnostics,
        b: &NodeBuilder<E>,
    ) -> Result<()> {
        assert_eq!(0, env.layer_count());
        env.enter_static();
        self.lower_expr(expr, env, d, b)?;
        env.dump();
        let mut layer = env.exit();
        assert_eq!(0, env.layer_count());
        for op in layer.take_ops() {
            module.body().append_operation(op);
        }

        for s in &env.shared {
            self.shared.insert(s.clone());
        }

        log::debug!(
            "lowered {}",
            module
                .as_operation()
                .to_string_with_flags(OperationPrintingFlags::new())
                .unwrap()
        );
        Ok(())
    }

    pub fn module_passes(&mut self, module: &mut ir::Module<'c>) {
        self.pass_manager.run(module).unwrap();
        assert!(module.as_operation().verify());
        log::debug!(
            "after pass {}",
            module
                .as_operation()
                .to_string_with_flags(OperationPrintingFlags::new())
                .unwrap()
        );
    }

    pub fn run_ast(
        &mut self,
        ast: ast::AstNode<E>,
        libpath: &str,
        env: &mut Environment<'c, E>,
        d: &mut Diagnostics,
        b: &NodeBuilder<E>,
    ) -> Result<i32> {
        let location = ir::Location::unknown(self.context);
        let mut module = ir::Module::new(location);
        let r = self.module_lower(&mut module, ast, env, d, b);
        d.dump();
        assert!(!d.has_errors);
        r.unwrap();
        self.module_passes(&mut module);
        Ok(self.exec_main(&module, libpath))
    }

    pub fn exec_main(&self, module: &ir::Module<'c>, libpath: &str) -> i32 {
        let paths = self
            .shared
            .iter()
            .map(|s| {
                let mut path = format!("{}/{}.so", libpath, s);
                path.push('\0');
                path
            })
            .collect::<Vec<_>>();
        let shared = paths.iter().map(|p| p.as_str()).collect::<Vec<_>>();

        let engine = ExecutionEngine::new(&module, 0, &shared, true);
        let mut result: i32 = -1;
        unsafe {
            engine
                .invoke_packed("main", &mut [&mut result as *mut i32 as *mut ()])
                .unwrap();
            println!("exec: {}", result);
            result
        }
    }
}
/*
pub struct CompilerContext<'c, E> {
    context: melior::Context,
    pub env: Environment<'c, E>,
    pass_manager: pass::PassManager<'c>,
    _e: std::marker::PhantomData<E>,
}

impl<'c, E: ast::Extra> CompilerContext<'c, E> {
    pub fn new() -> Self {
        let context = default_context();
        let pass_manager = default_pass_manager(&context);
        let env = scope::ScopeStack::default();
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
*/
/*
pub fn merge(&mut self, module: &ir::Module<'c>, _ast: ast::AstNode<E>) {
    //let lower = lower::Lower::new(&self.context, &self.files);
    //lower.lower_expr(ast, &mut self.env);
    for op in self.env.take_ops() {
        module.body().append_operation(op);
    }
}
*/
//}

pub struct Compiler<'c, E> {
    module: ir::Module<'c>,
    lower: lower::Lower<'c, E>,
    _e: std::marker::PhantomData<E>,
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

pub fn default_pass_manager<'c>(context: &Context) -> pass::PassManager<'c> {
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
