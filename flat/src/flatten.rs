use anyhow::Error;
use anyhow::Result;
use compile_core::{
    Argument, AssignTarget, Ast, AstNode, AstType, BinaryOperation, BuiltinId, ControlFlowMarker,
    Lambda, LinkOptions, Literal, ParameterNode, SpanId, StringKey, UnaryOperation,
    VarDefinitionSpace,
};
use indexmap::IndexMap;
use std::collections::HashMap;

use crate::{
    BlockId,
    BlockifyError,
    Builtin,
    LCode,
    LinkId,
    NodeBuilder,
    ScopeId,
    ScopeLayer,
    //NodeBuilder as NB,
    ScopeType,
    TemplateId,
};

pub struct FlattenEnvironment {
    current_block: Option<BlockId>,
    static_block: Option<BlockId>,
    static_scope: Option<ScopeId>,
    stack: Vec<ScopeId>,
    scopes: Vec<ScopeLayer>,
}

impl FlattenEnvironment {
    pub fn new() -> Self {
        Self {
            current_block: None,
            static_block: None,
            static_scope: None,
            stack: vec![],
            scopes: vec![],
        }
    }

    pub fn static_scope_id(&self) -> ScopeId {
        self.static_scope.unwrap()
    }

    pub fn static_block_id(&self) -> BlockId {
        self.static_block.unwrap()
    }

    pub fn new_scope(&mut self, scope_type: ScopeType) -> ScopeId {
        let offset = self.scopes.len();
        let scope = ScopeLayer::new(scope_type);
        self.scopes.push(scope);
        ScopeId(offset as u32)
    }

    pub fn current_scope(&self) -> Option<ScopeId> {
        self.stack.last().cloned()
    }

    pub fn enter_scope(&mut self, scope_id: ScopeId) {
        self.stack.push(scope_id);
    }

    pub fn exit_scope(&mut self) {
        self.stack.pop().unwrap();
    }

    pub fn get_scope(&self, scope_id: ScopeId) -> &ScopeLayer {
        self.scopes.get(scope_id.0 as usize).unwrap()
    }

    pub fn get_scope_mut(&mut self, scope_id: ScopeId) -> &mut ScopeLayer {
        self.scopes.get_mut(scope_id.0 as usize).unwrap()
    }

    pub fn push_block(&mut self, block_id: BlockId) {
        self.current_block = Some(block_id);
    }

    pub fn current_block(&mut self) -> BlockId {
        self.current_block.unwrap().clone()
    }

    pub fn pop_block(&mut self) -> BlockId {
        self.current_block.take().unwrap()
    }
}

pub struct CodeEntry {
    code: LCode,
    name: Option<StringKey>,
    link: Option<LinkId>,
    ty: Option<AstType>,
}

impl CodeEntry {
    pub fn new(code: LCode, name: Option<StringKey>) -> Self {
        Self {
            code,
            name,
            link: None,
            ty: None,
        }
    }

    pub fn add_type(mut self, ty: AstType) -> Self {
        self.ty = Some(ty);
        self
    }
}

pub struct IRBlock {
    block_id: BlockId,
    stack: Vec<ScopeId>,
    ast: Option<AstNode>,
    next: Option<BlockId>,
    ret: Option<BlockId>,
    links: Vec<LinkId>,
}

impl IRBlock {
    pub fn new(block_id: BlockId, stack: Vec<ScopeId>, ast: Option<AstNode>) -> Self {
        Self {
            block_id,
            stack,
            ast,
            links: vec![],
            ret: None,
            next: None,
        }
    }

    pub fn push(&mut self, link_id: LinkId) {
        self.links.push(link_id);
    }

    pub fn add_next(&mut self, block_id: BlockId) {
        self.next = Some(block_id);
    }

    pub fn add_ret(&mut self, block_id: BlockId) {
        self.ret = Some(block_id);
    }
}

pub struct FlattenResult {
    link_id: Option<LinkId>,
    block_id: BlockId,
}

impl FlattenResult {
    pub fn new(block_id: BlockId, link_id: Option<LinkId>) -> Self {
        Self { block_id, link_id }
    }
}

pub struct Flatten {
    module_key: Option<StringKey>,
    ast_blocks: Vec<BlockId>,
    ir_blocks: Vec<BlockId>,
    link: LinkOptions,
    entries: Vec<CodeEntry>,
    blocks: Vec<IRBlock>,
}

impl Flatten {
    pub fn new() -> Self {
        Self {
            module_key: None,
            ast_blocks: vec![],
            ir_blocks: vec![],
            entries: vec![],
            blocks: vec![],
            link: LinkOptions::new(),
        }
    }

    pub fn flatten_module(node: AstNode, fenv: &mut FlattenEnvironment) -> Result<Self> {
        let mut f = Self::new();
        if let Ast::Module(key, body) = node.node {
            f.module_key = Some(key);
            let static_scope = fenv.new_scope(ScopeType::Static);
            let stack = vec![static_scope];
            let block_id = f.new_ast_block(Some(*body), stack);
            let code = LCode::Label(0, 0);
            let entry = CodeEntry::new(code, Some(key));
            f.push_entry_with_link(block_id, entry);
            fenv.static_block = Some(block_id);
            fenv.static_scope = Some(static_scope);
            f.ast_blocks.push(block_id);
            Ok(f)
        } else {
            unreachable!()
        }
    }

    pub fn step(&mut self, fenv: &mut FlattenEnvironment, b: &mut NodeBuilder) -> Result<bool> {
        if let Some(block_id) = self.ast_blocks.pop() {
            let block = self.get_block_mut(block_id);
            let ast = block.ast.take().unwrap();
            self.flatten(block_id, ast, fenv, b)?;
        }
        Ok(self.ast_blocks.is_empty())
    }

    pub fn run_loop(&mut self, fenv: &mut FlattenEnvironment, b: &mut NodeBuilder) -> Result<()> {
        loop {
            if !self.step(fenv, b)? {
                break;
            }
        }
        Ok(())
    }

    pub fn push(&mut self, mut entry: CodeEntry) -> LinkId {
        let index = self.entries.len();
        let link_id = LinkId(index as u32);
        entry.link = Some(link_id);
        self.entries.push(entry);
        link_id
    }

    pub fn push_link(&mut self, block_id: BlockId, link_id: LinkId) {
        self.get_block_mut(block_id).push(link_id);
    }

    pub fn push_entry_with_link(&mut self, block_id: BlockId, entry: CodeEntry) -> LinkId {
        let link_id = self.push(entry);
        self.get_block_mut(block_id).push(link_id);
        link_id
    }

    pub fn new_ast_block(&mut self, ast: Option<AstNode>, stack: Vec<ScopeId>) -> BlockId {
        let index = self.blocks.len();
        let block_id = BlockId(index as u32);
        let ir_block = IRBlock::new(block_id, stack, ast);
        self.blocks.push(ir_block);
        block_id
    }

    pub fn get_block(&self, block_id: BlockId) -> &IRBlock {
        self.blocks.get(block_id.index()).unwrap()
    }

    pub fn get_block_mut(&mut self, block_id: BlockId) -> &mut IRBlock {
        self.blocks.get_mut(block_id.index()).unwrap()
    }

    pub fn get_entry(&self, link_id: LinkId) -> &CodeEntry {
        self.entries.get(link_id.index()).unwrap()
    }

    pub fn get_entry_mut(&mut self, link_id: LinkId) -> &mut CodeEntry {
        self.entries.get_mut(link_id.index()).unwrap()
    }

    fn flatten_sequence(
        &mut self,
        block_id: BlockId,
        mut seq: Vec<AstNode>,
        fenv: &mut FlattenEnvironment,
        b: &mut NodeBuilder,
    ) -> Result<FlattenResult> {
        let block = self.get_block_mut(block_id);
        let is_static = block.stack.len() == 1;
        let r = if seq.is_empty() {
            if is_static {
                // don't do anything, static block is already present
            } else {
                self.ir_blocks.push(block_id);
            }
            FlattenResult::new(block_id, None)
        } else {
            let rem = seq.split_off(1);
            let node = seq.pop().unwrap();
            //let stack = block.stack.clone();
            //self.new_ast_block(Some(node), stack);
            let r = self.flatten(block_id, node, fenv, b)?;
            if r.block_id != block_id {
                self.ir_blocks.push(block_id);
            }

            let block = self.get_block_mut(r.block_id);
            block.ast = Some(Ast::Sequence(rem).into());
            self.ast_blocks.push(r.block_id);
            r
        };
        Ok(r)
    }

    pub fn flatten(
        &mut self,
        block_id: BlockId,
        node: AstNode,
        fenv: &mut FlattenEnvironment,
        b: &mut NodeBuilder,
    ) -> Result<FlattenResult> {
        let block = self.get_block_mut(block_id);
        let span_id = node.span_id;
        let ast = node.node;

        match ast {
            Ast::Module(_, _) => {
                unimplemented!("No nested modules yet")
            }

            Ast::Sequence(exprs) => self.flatten_sequence(block_id, exprs, fenv, b),

            Ast::Global(name, expr) => {
                match expr.node {
                    Ast::Lambda(def) => {
                        let r = if let Some(body) = def.body {
                            let fun_scope_id = fenv.new_scope(ScopeType::Function);
                            let mut stack = block.stack.clone();
                            stack.push(fun_scope_id);
                            let fun_block_id = self.new_ast_block(Some(*body), stack);
                            self.ast_blocks.push(fun_block_id);

                            // push declaration into static block
                            let code = LCode::DeclareFunction(Some(fun_block_id));
                            let link_id =
                                self.push_entry_with_link(block_id, CodeEntry::new(code, None));
                            FlattenResult::new(block_id, Some(link_id))
                        } else {
                            let code = LCode::DeclareFunction(None);
                            let link_id =
                                self.push_entry_with_link(block_id, CodeEntry::new(code, None));
                            FlattenResult::new(block_id, Some(link_id))
                        };
                        Ok(r)
                    }

                    Ast::Literal(lit) => {
                        let scope_id = block.stack.last().unwrap();
                        let scope = fenv.get_scope(*scope_id);
                        let global_name = if let ScopeType::Static = scope.scope_type {
                            b.labels.r(name.into()).to_string()
                        } else {
                            // static var with local name
                            let unique_name = b.unique_static_name();
                            let base = b.labels.r(name.into());
                            format!("{}{}", base, unique_name).clone()
                        };

                        let ast_ty: AstType = lit.clone().into();
                        let code = LCode::Const(lit);
                        let global_name_key = b.labels.s(&global_name);

                        let entry = CodeEntry::new(code, Some(global_name_key)).add_type(ast_ty);
                        let link_id = self.push_entry_with_link(block_id, entry);
                        let code = LCode::Link(link_id);
                        let entry = CodeEntry::new(code, Some(name));
                        let link_id = self.push_entry_with_link(block_id, entry);
                        Ok(FlattenResult::new(block_id, Some(link_id)))
                    }
                    _ => unreachable!(),
                }
            }

            Ast::Builtin(id, mut args) => {
                let bi = b.builtins.get_enum(id);
                match bi {
                    Builtin::Import => {
                        let arg = args.pop().unwrap();
                        if let Some(s) = arg.try_string() {
                            self.link.add_library(&s);
                        } else {
                            b.push_error("Expected string", span_id);
                        }
                        Ok(FlattenResult::new(block_id, None))
                    }
                    _ => {
                        let _ty = bi.get_return_type();
                        let args_size = args.len();
                        assert_eq!(args_size, bi.arity());
                        let mut values = vec![];
                        for a in args.into_iter() {
                            let Argument::Positional(expr) = a;
                            let r = self.flatten(block_id, *expr, fenv, b)?;
                            let link_id = r.link_id.unwrap();
                            let entry = self.get_entry(link_id);
                            values.push((link_id, entry.ty.clone()));
                        }

                        for (link_id, ty) in values {
                            let code = LCode::Link(link_id);
                            let mut entry = CodeEntry::new(code, None);
                            if let Some(ty) = ty {
                                entry = entry.add_type(ty);
                            }
                            self.push_entry_with_link(block_id, entry);
                        }

                        let ty = bi.get_return_type();
                        let code = LCode::Builtin(id, args_size as u8, 0);
                        let entry = CodeEntry::new(code, None).add_type(ty);
                        let link_id = self.push_entry_with_link(block_id, entry);
                        Ok(FlattenResult::new(block_id, Some(link_id)))
                    }
                }
            }

            /*
            Ast::Lambda(_def) => {
            }

            Ast::Call(expr, args, _ret_ty) => {
            },

            Ast::ControlFlowMarker(ControlFlowMarker::BlockStart(name, args)) => {
            }

            Ast::ControlFlowMarker(ControlFlowMarker::Goto(label)) => {
            }

            Ast::Identifier(key) => {
            }

            Ast::Assign(target, expr) => {
            }

            Ast::Literal(lit) => {
            }

            Ast::UnaryOp(op, x) => {
            }

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
            }

            Ast::Ternary(c, x, y) => {
            }

            Ast::BinaryOp(op, x, y) => {
            }

            Ast::Return(maybe_expr) => {
            }

            Ast::Yield(maybe_expr) => {
            }


            Ast::Loop(name, body) => {
            }

            Ast::Block(name, args, body) => {
            }

            Ast::CloseBlock => {
            }

            Ast::Break(maybe_name, args) => {
            }

            Ast::Continue(maybe_name, args) => {
            }
            */
            Ast::Error => {
                b.push_error(&format!("AST Error"), node.span_id);
                Err(Error::new(BlockifyError::Invalid))
            }

            _ => unimplemented!("{:?}", ast),
        }
    }
}
