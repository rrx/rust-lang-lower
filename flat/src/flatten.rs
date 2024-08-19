use indexmap::IndexMap;
use anyhow::Error;
use anyhow::Result;
use compile_core::{
    Argument, AssignTarget, Ast, AstNode, AstType, BinaryOperation, BuiltinId, ControlFlowMarker,
    Lambda, LinkOptions, Literal, ParameterNode, SpanId, StringKey, UnaryOperation,
    VarDefinitionSpace,
};
use std::collections::HashMap;

use crate::{
    BlockId,
    Builtin,
    ScopeId,
    ScopeLayer,
    LCode,
    BlockifyError,
    CodeOffset,
    NodeBuilder,
    //NodeBuilder as NB,
    ScopeType,
    StringLabel,
    TemplateId,
    ValueId,
};

pub struct FlattenEnvironment {
    current_block: Option<BlockId>,
    stack: Vec<ScopeId>,
    scopes: Vec<ScopeLayer>,
    block_map: HashMap<BlockId, IRBlock>,
    block_count: u32,
}

impl FlattenEnvironment {
    pub fn new() -> Self {
        Self {
            current_block: None,
            stack: vec![],
            scopes: vec![],
            block_map: HashMap::new(),
            block_count: 0,
        }
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

    pub fn push_block(&mut self) -> BlockId {
        let block_id = self.new_ir_block();
        self.current_block = Some(block_id);
        block_id
    }

    pub fn current_block(&mut self) -> BlockId {
        self.current_block.unwrap().clone()
    }

    pub fn push_code(&mut self, code: LCode) {
        let block_id = self.current_block();
        self.get_block_mut(block_id).push(code)
    }

    pub fn pop_block(&mut self) -> BlockId {
        self.current_block.take().unwrap()
    }

    pub fn fresh_block_id(&mut self) -> BlockId {
        let b = BlockId(self.block_count);
        self.block_count += 1;
        b
    }

    pub fn new_ast_block(&mut self, ast: AstNode) -> AstBlock {
        let block_id = self.fresh_block_id();
        AstBlock::new(block_id, ast)
    }

    pub fn new_ir_block(&mut self) -> BlockId {
        let block_id = self.fresh_block_id();
        let ir_block = IRBlock::new(block_id);
        self.block_map.insert(block_id, ir_block);
        block_id
    }

    pub fn get_block(&self, block_id: BlockId) -> &IRBlock {
        self.block_map.get(&block_id).unwrap()
    }

    pub fn get_block_mut(&mut self, block_id: BlockId) -> &mut IRBlock {
        self.block_map.get_mut(&block_id).unwrap()
    }


}

pub struct AstBlock {
    block_id: BlockId,
    ast: AstNode
}

impl AstBlock {
    pub fn new(block_id: BlockId, ast: AstNode) -> Self {
        Self { block_id, ast }
    }
}

pub struct IRBlock {
    block_id: BlockId,
    codes: Vec<LCode>
}

impl IRBlock {
    pub fn new(block_id: BlockId) -> Self {
        Self { block_id, codes: vec![] }
    }

    pub fn push(&mut self, code: LCode) {
        self.codes.push(code);
    }
}

pub struct Flatten {
    module_key: Option<StringKey>,
    ast_blocks: Vec<AstBlock>,
    ir_blocks: Vec<BlockId>,
}

impl Flatten {
    pub fn new() -> Self {
        Self {
            module_key: None,
            ast_blocks: vec![],
            ir_blocks: vec![],
        }
    }

    pub fn flatten(
        &mut self,
        node: AstNode,
        fenv: &mut FlattenEnvironment,
        b: &mut NodeBuilder,
    ) -> Result<()> {
        match node.node {
            Ast::Module(key, body) => {
                self.module_key = Some(key);
                let static_scope = fenv.new_scope(ScopeType::Static);
                fenv.enter_scope(static_scope);
                let block_id = fenv.push_block();
                self.ir_blocks.push(block_id);
                self.flatten(*body, fenv, b);
                let block_id = fenv.pop_block();
                Ok(())
            }

            Ast::Sequence(ref exprs) => {
                for expr in exprs.to_vec() {
                    self.flatten(expr, fenv, b)?
                }
                Ok(())
            }

            Ast::Global(name, expr) => {
                let scope_id = fenv.current_scope().unwrap();
                let scope = fenv.get_scope(scope_id);
                match expr.node {
                    Ast::Lambda(def) => {
                        if let Some(body) = def.body {
                            let ast_block = fenv.new_ast_block(*body);
                            fenv.push_code(LCode::DeclareFunction(Some(ast_block.block_id)));
                        } else {
                            fenv.push_code(LCode::DeclareFunction(None));
                        }
                        Ok(())
                    }
                    Ast::Literal(lit) => {
                        let global_name = if let ScopeType::Static = scope.scope_type {
                            b.labels.r(name.into()).to_string()
                        } else {
                            let unique_name = b.unique_static_name();
                            let base = b.labels.r(name.into());
                            format!("{}{}", base, unique_name).clone()
                        };

                        let ast_ty: AstType = lit.clone().into();

                        let code = LCode::Const(lit);
                        fenv.push_code(code);
                        Ok(())
                    }
                    _ => unreachable!(),
                }
            },

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

            Ast::Builtin(id, mut args) => {
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

            _ => unimplemented!("{:?}", node.node),
        }
    }

}

