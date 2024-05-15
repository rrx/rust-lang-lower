use anyhow::Result;

use compile_core::{
    Ast, AstNode, AstType, Lambda, ParameterNode, SpanId, StringKey, VarDefinitionSpace,
};

use crate::{
    blockify::AddResult, BlockId, Blockify, Environment, LCode, NodeBuilder, NodeBuilder as NB,
    ScopeId, ScopeType,
};

enum BlockType {
    Normal,
    Loop,
}

struct SequenceBlock {
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
}

struct SequenceReader {
    result: Vec<AstNode>,
    current: Vec<AstNode>,
    current_label: Option<StringKey>,
}

impl SequenceReader {
    fn new() -> Self {
        Self {
            result: vec![],
            current: vec![],
            current_label: None,
        }
    }

    fn close_block(&mut self) {
        let block = Ast::Block(
            self.current_label.unwrap(),
            vec![],
            Box::new(Ast::Sequence(self.current.drain(..).collect()).into()),
        );
        self.current_label = None;
        self.result.push(block.into());
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
                self.close_block();
                self.result.push(ast);
            } else {
                // block is not open, just push this block
                self.result.push(ast);
            }
        } else if this_is_term {
            // this is not a block, but it is a terminal
            if let Some(_) = self.current_label {
                // block is open
                // close it with the terminal
                self.current.push(ast);
                self.close_block();
            } else {
                // current is not yet open, this is not a block, but it's a terminal
                // open a new block, and push the terminal, then close the block
                self.current_label = Some(b.fresh_block_name());
                self.current.push(ast);
                self.close_block();
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
    ) -> Vec<AstNode> {
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
        reader.result
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
        let span_id = b.spans.get_span_unknown();
        let entry_id =
            self.push_label_with_block(name.into(), span_id, static_scope, block_id, &[], &[], b);
        (block_id, static_scope)
    }

    fn open_function(
        &mut self,
        name: StringKey,
        block_id: BlockId,
        scope_id: ScopeId,
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
        lambda: Lambda,
        span_id: SpanId,
        b: &mut NodeBuilder,
    ) {
        let return_type = b.types.r(lambda.return_type).clone();
        self.add_return_block(block.scope_id, block.next, span_id, return_type, b);
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::{SequenceReader as R, *};
    //use test_log::test;

    #[test]
    fn test_seq() {
        let mut b = NodeBuilder::new();
        let ast = crate::builder::tests::gen_block(&mut b);
        let span_id = ast.span_id;

        let mut blockify = Blockify::new();
        let (block_id, scope_id) = blockify.open_module(b.labels.s("module"), &mut b);
        let lambda = Lambda {
            params: vec![],
            return_type: b.types.s(&AstType::Unit),
            body: None,
        };

        let block = blockify.open_function(b.labels.s("main"), block_id, scope_id, &lambda, &mut b);
        let r = R::build(vec![Ast::bool(true).into()], &mut blockify, &mut b);
        for expr in r {
            println!("{:?}", expr);
        }
        blockify.close_function(&block, lambda, span_id, &mut b);
    }
}
/*
 *
    let scope = self.env.get_scope_mut(body_scope_id);
    scope.return_block = Some(ret_block_id);
    scope.entry_block = Some(new_block_id);

    self.env.enter_scope(body_scope_id);
    // next block in body scope
    self.add_with_next(new_entry_id.into(), *body, ret_block_id.into(), b)?;
    self.env.exit_scope();
    self.env.add_succ_static(current_block_id, new_entry_id);

    Ok(AddResult::new(Some(v_decl), false, current_entry_id))

    body_scope_id
}
*/
/*
        let ret_block_id = self.env.new_block();
        let scope = self.env.get_scope_mut(body_scope_id);
        scope.return_block = Some(ret_block_id);
        scope.entry_block = Some(new_block_id);

        self.env.enter_scope(body_scope_id);
        // next block in body scope
        self.add_with_next(new_entry_id.into(), *body, ret_block_id.into(), b)?;
        self.env.exit_scope();
        self.env.add_succ_static(current_block_id, new_entry_id);

        let _ = self.add_return_block(body_scope_id, ret_block_id, span_id, return_type, b)?;
        Ok(AddResult::new(Some(v_decl), false, current_entry_id))
    }
}
        self.env.enter_scope(static_scope);
        self.add(entry_id.into(), None, *body, b)?;
        self.env.exit_scope();
        Ok(entry_id)
        */
