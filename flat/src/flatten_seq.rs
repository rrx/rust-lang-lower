use compile_core::{Ast, AstNode, ControlFlowMarker, SpanId, StringKey, AstType};

use crate::{NodeBuilder as NB};

#[derive(Debug)]
pub struct SequenceReader {
    loop_names: Vec<StringKey>,
    block_names: Vec<StringKey>,
    stack: Vec<(StackType, Vec<AstNode>)>,
    spans: Vec<SpanId>,
    seq: Vec<AstNode>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum StackType {
    Loop,
    Block,
}

impl SequenceReader {
    pub fn new() -> Self {
        Self {
            loop_names: vec![],
            block_names: vec![],
            stack: vec![],
            spans: vec![],
            seq: vec![],
        }
    }

    fn start_loop(&mut self, key: StringKey, span_id: SpanId) {
        self.loop_names.push(key);
        self.stack.push((StackType::Loop, vec![]));
        self.spans.push(span_id)
    }

    fn end_loop(&mut self) -> AstNode {
        let (stack_type, seq) = self.stack.pop().unwrap();
        assert_eq!(stack_type, StackType::Loop);
        let span_id = self.spans.pop().unwrap();
        let key = self.loop_names.pop().unwrap();
        Ast::Loop(key, NB::seq(seq, span_id).into()).into()
    }

    fn start_block(&mut self, maybe_key: Option<StringKey>, span_id: SpanId) {
        if let Some(key) = maybe_key {
            self.block_names.push(key);
        }
        self.stack.push((StackType::Block, vec![]));
        self.spans.push(span_id)
    }

    fn end_block(&mut self) -> AstNode {
        let (stack_type, seq) = self.stack.pop().unwrap();
        assert_eq!(stack_type, StackType::Block);
        let span_id = self.spans.pop().unwrap();
        let key = self.block_names.pop().unwrap();
        Ast::Block(key, vec![], NB::seq(seq, span_id).into()).into()

        /*
        let mut new_seq = vec![];
        new_seq.push(Ast::ControlFlowMarker(ControlFlowMarker::BlockStart(Some(key), vec![])).into());
        new_seq.extend(seq);
        new_seq.push(Ast::ControlFlowMarker(ControlFlowMarker::BlockEnd).into());
        //new_seq.push(Ast::CloseBlock.into());
        NB::seq(new_seq, span_id).into()
           */
    }

    fn is_type(&self, t: StackType) -> bool {
        self.stack
            .last()
            .as_ref()
            .map(|v| v.0 == t)
            .unwrap_or(false)
    }

    fn is_block(&self) -> bool {
        self.is_type(StackType::Block)
    }

    fn is_loop(&self) -> bool {
        self.is_type(StackType::Loop)
    }

    fn push_stack(&mut self, ast: AstNode) {
        if self.stack.len() == 0 {
            self.seq.push(ast);
        } else {
            self.stack.last_mut().unwrap().1.push(ast);
        }
    }

    fn push_node(&mut self, node: AstNode, b: &mut NB) {
        let span_id = node.span_id;
        match &node.node {
            Ast::ControlFlowMarker(ControlFlowMarker::LoopStart(maybe_key)) => {
                let key = if let Some(key) = maybe_key {
                    key.clone()
                } else {
                    b.fresh_loop_name()
                };
                self.start_loop(key, span_id);
            }
            Ast::ControlFlowMarker(ControlFlowMarker::LoopBreak(maybe_key)) => {
                self.push_stack(NB::loop_break(maybe_key.clone()));
            }
            Ast::ControlFlowMarker(ControlFlowMarker::LoopContinue(maybe_key)) => {
                self.push_stack(NB::loop_continue(maybe_key.clone()));
            }

            Ast::ControlFlowMarker(ControlFlowMarker::BlockEnd) => {
                self.close();
            }

            Ast::ControlFlowMarker(ControlFlowMarker::BlockStart(maybe_key, params)) => {
                assert_eq!(params.len(), 0);
                self.start_block(maybe_key.clone(), span_id);
            }
            Ast::ControlFlowMarker(ControlFlowMarker::Goto(key)) => {
                if self.is_block() {
                    let ast = self.end_block();
                    self.push_stack(ast);
                } else {
                    self.push_stack(NB::goto(key.clone()));
                }
            }
            Ast::Block(_key, _params, _body) => {
                self.close_block();
                self.push_stack(node);
            }
            _ => {
                self.push_stack(node);
            }
        }
    }

    pub fn close_block(&mut self) {
        assert!(self.stack.len() > 0);
        let (stack_type, _) = self.stack.last().unwrap();
        assert_eq!(stack_type, &StackType::Block);
        let ast = self.end_block();
        self.push_stack(ast);
    }

    pub fn close(&mut self) {
        if self.stack.len() > 0 {
            let (stack_type, _) = self.stack.last().unwrap();
            match stack_type {
                StackType::Block => {
                    let ast = self.end_block();
                    self.push_stack(ast);
                }
                StackType::Loop => {
                    let ast = self.end_loop();
                    self.push_stack(ast);
                }
            }
        }
    }

    pub fn build(&mut self, exprs: Vec<AstNode>, b: &mut NB) -> Vec<AstNode> {
        for expr in exprs {
            self.push_node(expr, b);
        }

        self.close();
        self.seq.drain(..).collect()
    }
}

/*
impl Flatten {
    pub fn flatten_sequence_step(
        &mut self,
        block_id: BlockId,
        mut seq: Vec<AstNode>,
        fenv: &mut FlattenEnvironment,
        b: &mut NB,
    ) -> Result<(Vec<AstNode>, FlattenResult)> {
        let mut current_block_id = block_id;
        let mut ty = AstType::Unit;
        let mut link_id = None;
        let mut is_term = false;
        let mut span_id = b.spans.get_span_unknown();
        let block = self.get_block(block_id);
        let scope_id = block.scope_id;

        Ok(FlattenResult::new(current_block_id, link_id, ty, is_term))
    }
}
*/

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Flatten, FlattenEnvironment, NodeBuilder as NB, ScopeType, ICodeModule};
    use anyhow::Result;
    use test_log::test;

    fn builder() -> NB {
        let mut b = NB::new();
        let _file_id = b.spans.add_source("test".to_string(), "".to_string());
        b
    }

    fn build_module(seq: Vec<AstNode>, b: &mut NB) -> AstNode {
        let name = b.labels.s("func");
        let module_name = b.labels.s("module");
        let span_id = b.spans.get_span_unknown();
        let f = b.func(name, &[], AstType::Unit, NB::seq(seq, span_id));
        NB::module(module_name, f)
    }

    fn run(seq: Vec<AstNode>, b: &mut NB) -> Result<()> {
        let mut fenv = FlattenEnvironment::new();
        let module = build_module(seq, b);
        b.dump_ast(&module);
        let r = Flatten::flatten_module(module, &mut fenv, b);
        b.spans.diagnostics_dump();
        let mut f = r?;
        let r = f.run_loop(&mut fenv, b);
        f.dump_ast(&b);
        b.spans.diagnostics_dump();
        let _ = r?;
        let m = f.module(&mut fenv, &b);
        m.dump(&b);
        m.block_graph("blocks.dot", &b);
        
        Ok(())
    }

    #[test]
    fn test_seq1() {
        let mut b = builder();
        let a = b.labels.s("a");
        let seq = vec![
            NB::goto(a).into(),
            NB::label(a).into(),
            NB::index(0).into()
        ];
        let _ = run(seq, &mut b).unwrap();
        b.spans.diagnostics_dump();
    }

    #[test]
    fn test_seq2() {
        let mut b = builder();
        let a = b.labels.s("a");
        let seq = vec![
            NB::label(a).into(),
        ];
        let _ = run(seq, &mut b).unwrap();
        b.spans.diagnostics_dump();
    }
}
