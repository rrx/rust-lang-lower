use anyhow::Result;

use compile_core::{
    Ast, AstNode, AstType, Lambda, ParameterNode, SpanId, StringKey, VarDefinitionSpace,
};

use crate::{
    blockify::AddResult,
    BlockId,
    Blockify,
    ICodeModule,
    //CodeOffset,
    //Environment,
    LCode,
    NodeBuilder,
    NodeBuilder as NB,
    ScopeId,
    ScopeType,
};

enum BlockType {
    Normal,
    Module,
    Loop,
}

pub struct SequenceBlock {
    block_type: BlockType,
    start: BlockId,
    next: BlockId,
    scope_id: ScopeId,
}

impl SequenceBlock {
    fn loop_block(start: BlockId, next: BlockId, scope_id: ScopeId) -> Self {
        Self {
            block_type: BlockType::Loop,
            start,
            next,
            scope_id,
        }
    }

    fn normal(start: BlockId, next: BlockId, scope_id: ScopeId) -> Self {
        Self {
            block_type: BlockType::Normal,
            start,
            next,
            scope_id,
        }
    }

    fn module(start: BlockId, scope_id: ScopeId) -> Self {
        Self {
            block_type: BlockType::Module,
            start: start,
            next: start,
            scope_id,
        }
    }
}

struct SequenceReader {
    //result: Vec<AstNode>,
    current: Vec<AstNode>,
    current_label: Option<StringKey>,
    current_block: Option<BlockId>,
}

impl SequenceReader {
    fn new() -> Self {
        Self {
            //result: vec![],
            current: vec![],
            current_label: None,
            current_block: None,
        }
    }

    fn add(&mut self, blockify: &mut Blockify, ast: AstNode, b: &mut NodeBuilder) {
        blockify.test_add(self.current_block.unwrap(), ast, b);
        //blockify.add_block_with_expr(
        //blockify.test_add(entry_id,
        //self.result.push(block.into());
    }

    fn close_block(&mut self, blockify: &mut Blockify, b: &mut NodeBuilder) {
        let block = Ast::Block(
            self.current_label.unwrap(),
            vec![],
            Box::new(Ast::Sequence(self.current.drain(..).collect()).into()),
        );
        self.current_label = None;
        self.add(blockify, block.into(), b);
    }

    fn push(&mut self, ast: AstNode, blockify: &mut Blockify, b: &mut NodeBuilder) {
        let this_is_term = ast.node.is_term();
        let this_label = ast.node.get_label();

        if let Some(this_label) = this_label {
            // we have a block
            if let Some(_) = self.current_label {
                // a block is open
                // close it by jumping to this
                self.current.push(NB::goto(this_label));
                self.close_block(blockify, b);
                self.add(blockify, ast, b);
            } else {
                // block is not open, just push this block
                //self.result.push(ast);
                self.add(blockify, ast, b);
            }
        } else if this_is_term {
            // this is not a block, but it is a terminal
            if let Some(_) = self.current_label {
                // block is open
                // close it with the terminal
                self.current.push(ast);
                self.close_block(blockify, b);
            } else {
                // current is not yet open, this is not a block, but it's a terminal
                // open a new block, and push the terminal, then close the block
                self.current_label = Some(b.fresh_block_name());
                self.current.push(ast);
                self.close_block(blockify, b);
            }
        } else {
            // not a block and not a terminal
            if let Some(_) = self.current_label {
                // current is open, just push the non-terminal
                self.current.push(ast);
            } else {
                // current is not yet open
                // open current then push the non terminal
                self.current_label = Some(b.fresh_block_name());
                self.current.push(ast);
            }
        }
    }

    fn build(
        exprs: Vec<AstNode>,
        //span_id: SpanId,
        //env: &mut Environment,
        //next_block: Option<BlockId>,
        blockify: &mut Blockify,
        b: &mut NodeBuilder,
    ) {
        let mut reader = Self::new();
        for expr in exprs {
            reader.push(expr, blockify, b);
        }

        // end of the sequence
        if let Some(_) = reader.current_label {
            // we have an open current
            // close it with next
            //env
            //reader.current.push(NB::goto(next_block.unwrap()));
            // it needs to be a yield or a return
            reader.push(Ast::CloseBlock.into(), blockify, b);
        }
        //reader.result
        //Ok(NB::seq(reader.result.drain(..).collect(), span_id))
    }
}

impl Blockify {
    pub fn add_sequence_inner(
        &mut self,
        entry_id: BlockId,
        maybe_next: Option<BlockId>,
        node: AstNode,
        b: &mut NodeBuilder,
    ) -> Result<AddResult> {
        // iterate through and merge things together so we have a sequence of terminals

        //let scope_id = self.env.current_scope().unwrap();
        let entry_id = self.env.resolve_code_offset(entry_id.into());
        //let mut current_entry_id = Some(entry_id.into());
        // flatten
        let exprs = node.to_vec();

        let mut value_id = None;
        let mut current_entry_id = Some(entry_id.into());
        let mut current_is_term = false;
        let mut iter = exprs.into_iter().peekable();
        loop {
            if let Some(expr) = iter.next() {
                let this_is_term = expr.node.is_term();
                let this_label = expr.node.get_label();

                if let Some(next) = iter.peek() {
                    let next_is_term = next.node.is_term();
                    let next_label = expr.node.get_label();
                    if next_is_term {
                        // just add with next
                    } else {
                    }
                } else {
                    // end of the line
                }
                println!("a: {:?}", (&expr.node, maybe_next, entry_id));

                if let Ast::ControlFlowMarker(_) = expr.node {
                    unreachable!()
                }
                let r = self.add(
                    current_entry_id.unwrap(),
                    None,
                    //Some(target_block_id),
                    expr,
                    b,
                )?;
                if let Some(v) = r.value_id {
                    //let v = r.value_id.unwrap();
                    current_is_term = r.is_term;
                    //assert_eq!(current_is_term, is_term);
                    //current_entry_id = Some(*self.entries.get(v.0 as usize).unwrap());
                    current_entry_id = Some(r.entry_id.into());
                    //assert_eq!(current_block_id.unwrap(), r.block_id);
                    value_id = Some(v);
                }
            } else {
                break;
            }
        }
        Ok(AddResult::new(
            value_id,
            current_is_term,
            current_entry_id.unwrap(),
        ))
    }

    fn open_module(&mut self, name: StringKey, b: &mut NodeBuilder) -> (BlockId, ScopeId) {
        let static_scope = self.env.new_scope(ScopeType::Static);
        let block_id = self.env.new_block();
        self.env.enter_scope(static_scope, block_id);
        let span_id = b.spans.get_span_unknown();
        let entry_id =
            self.push_label_with_block(name.into(), span_id, static_scope, block_id, &[], &[], b);
        (block_id, static_scope)
    }

    fn close_module(&mut self) {
        self.env.exit_scope();
    }

    fn open_function(
        &mut self,
        scope_id: ScopeId,
        block_id: BlockId,
        name: StringKey,
        lambda: &Lambda,
        b: &mut NodeBuilder,
    ) -> SequenceBlock {
        let body_scope_id = self.env.new_scope(ScopeType::Function);

        let new_block_id = self.env.new_block();
        let span_id = b.spans.get_span_unknown();
        let ty = b.types.get_type(&lambda);
        // declare function before adding the body, for recursion
        let v_decl = self.push_code_with_name(
            LCode::DeclareFunction(Some(new_block_id)),
            span_id,
            scope_id,
            block_id,
            ty.clone(),
            VarDefinitionSpace::Static,
            name,
        );

        // entry
        let new_entry_id = self.push_label_with_block(
            name.into(),
            span_id,
            body_scope_id,
            new_block_id,
            &[],
            &lambda.params,
            b,
        );

        let ret_block_id = self.env.new_block();

        let block = SequenceBlock::normal(new_block_id, ret_block_id, body_scope_id);
        block
    }

    fn close_function(
        &mut self,
        block: &SequenceBlock,
        lambda: &Lambda,
        span_id: SpanId,
        b: &mut NodeBuilder,
    ) {
        let return_type = b.types.r(lambda.return_type).clone();
        self.add_return_block(block.scope_id, block.next, span_id, return_type, b);
    }

    pub fn test_add_module(
        &mut self,
        block_id: BlockId,
        name: StringKey,
        body: AstNode,
        b: &mut NodeBuilder,
    ) -> Result<SequenceBlock> {
        assert_eq!(self.env.stack.len(), 0);
        let static_scope = self.env.new_scope(ScopeType::Static);
        let entry_id = self.push_label_with_block(
            name.into(),
            body.span_id,
            static_scope,
            block_id,
            &[],
            &[],
            b,
        );
        self.env.enter_scope(static_scope, block_id);
        for expr in body.to_vec() {
            self.test_add(block_id, expr, b)?;
        }
        self.env.exit_scope();
        let block = SequenceBlock::module(block_id, static_scope);
        Ok(block)
    }

    pub fn test_add_function(
        &mut self,
        scope_id: ScopeId,
        block_id: BlockId,
        name: StringKey,
        lambda: Lambda,
        span_id: SpanId,
        b: &mut NodeBuilder,
    ) -> Result<SequenceBlock> {
        let block = self.open_function(scope_id, block_id, name, &lambda, b);
        self.test_add(block.start, *lambda.body.unwrap(), b)?;
        let return_type = b.types.r(lambda.return_type).clone();
        self.add_return_block(block.scope_id, block.next, span_id, return_type, b);
        let block = SequenceBlock::normal(block_id, block_id, scope_id);
        Ok(block)
    }

    pub fn test_add_return(
        &mut self,
        scope_id: ScopeId,
        block_id: BlockId,
        span_id: SpanId,
        arg: Option<AstNode>,
        //return_type: AstType,
        b: &mut NodeBuilder,
    ) -> Result<AddResult> {
        let mut block_id = block_id.into();
        let v_args = if let Some(arg) = arg {
            let r = self.add(block_id, None, arg, b)?;
            let ty = self.get_type(r.value_id.unwrap());

            block_id = r.entry_id;
            self.push_code(
                LCode::Value(r.value_id.unwrap()),
                span_id,
                scope_id,
                block_id,
                ty,
                VarDefinitionSpace::Arg,
            );
            1
        } else {
            0
        };
        let v = self.push_code(
            LCode::Return(v_args),
            span_id,
            scope_id,
            block_id.into(),
            AstType::Unit,
            VarDefinitionSpace::Reg,
        );
        Ok(AddResult::new(Some(v), false, block_id))
    }

    pub fn test_add(
        &mut self,
        entry_id: BlockId,
        //maybe_next: Option<BlockId>,
        node: AstNode,
        b: &mut NodeBuilder,
    ) -> Result<SequenceBlock> {
        println!("ADD");
        b.dump_ast(&node);
        match node.node {
            Ast::Module(name, body) => self.test_add_module(entry_id, name, *body, b),

            Ast::Lambda(_def) => {
                unimplemented!();
            }

            Ast::Global(name, expr) => match expr.node {
                Ast::Lambda(lambda) => {
                    let scope_id = self.env.current_scope().unwrap();
                    let block_id = self.resolve_block_id(self.env.static_entry_id());
                    self.test_add_function(scope_id, block_id, name, lambda, node.span_id, b)
                }
                _ => unimplemented!(),
            },

            Ast::Sequence(exprs) => {
                let mut block = None;
                for expr in exprs {
                    block = Some(self.test_add(entry_id, expr, b)?);
                }

                Ok(block.unwrap())
                /*
                let mut reader = SequenceReader::new();
                for expr in exprs {
                    reader.push(expr, self, b);
                }

                // end of the sequence
                if let Some(_) = reader.current_label {
                    // we have an open current
                    // close it with next
                    //env
                    //reader.current.push(NB::goto(next_block.unwrap()));
                    // it needs to be a yield or a return
                    reader.push(Ast::CloseBlock.into(), self, b);
                }

                //SequenceReader::build(exprs, self, b);
                Ok(())
                */
            }

            Ast::Return(maybe_body) => {
                let scope_id = self.env.current_scope().unwrap();
                let r = self.test_add_return(
                    scope_id,
                    entry_id,
                    node.span_id,
                    maybe_body.map(|body| *body),
                    b,
                )?;
                let block = SequenceBlock::normal(entry_id, entry_id, scope_id);
                Ok(block)
            }

            Ast::Literal(lit) => {
                let scope_id = self.env.current_scope().unwrap();
                let r = self.add_literal_expr(entry_id.into(), lit, node.span_id)?;
                let block = SequenceBlock::normal(entry_id, entry_id, scope_id);
                Ok(block)
            }

            Ast::Block(name, args, body) => {
                let scope_id = self.env.new_scope(ScopeType::Block);
                let block_id = self.env.new_block();
                self.env.enter_scope(scope_id, block_id);
                self.test_add(entry_id, *body, b)?;
                self.env.exit_scope();
                let block = SequenceBlock::normal(entry_id, entry_id, scope_id);
                Ok(block)
            }

            Ast::Builtin(_, _) => {
                let scope_id = self.env.new_scope(ScopeType::Block);
                let block = SequenceBlock::normal(entry_id, entry_id, scope_id);
                Ok(block)
            }
            _ => {
                unreachable!();
                //let r = self._add(entry_id, maybe_next, node, b)?;
                //let block = SequenceBlock::normal(entry_id, entry_id, scope_id);
                //Ok(block)
            }
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    //use test_log::test;

    #[test]
    fn test_seq() {
        let mut b = NodeBuilder::new();
        let ast = crate::builder::tests::gen_block(&mut b);
        let module: AstNode = Ast::Module(b.labels.s("module"), ast.into()).into();
        let mut blockify = Blockify::new();
        let block_id = blockify.env.new_block();
        blockify.test_add(block_id, module, &mut b).unwrap();
        blockify.dump(&b);
    }
}
