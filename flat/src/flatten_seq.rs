use compile_core::{Ast, AstNode, ControlFlowMarker, SpanId, StringKey};

use crate::NodeBuilder as NB;

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
                //let x = self.stack.last().unwrap();
                //println!("x: {:?}", x);
                //let ast = self.end_loop();
                //self.push_stack(ast);
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
            _ => {
                self.push_stack(node);
            }
        }
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
