use crate::ast::*;
use crate::intern::{StringKey, StringPool};
use crate::AstType;
use crate::Diagnostics;
use melior::ir;
use melior::Context;
use std::collections::VecDeque;

#[derive(Debug, Clone, Copy)]
pub struct NodeID(Option<u32>);
impl NodeID {
    pub fn is_valid(&self) -> bool {
        self.0.is_some()
    }
}

pub struct NodeBuilder<E> {
    span: Option<Span>,
    filename: String,
    current_node_id: u32,
    current_def_id: u32,
    static_count: usize,
    pub strings: StringPool,
    _e: std::marker::PhantomData<E>,
}

impl<E: Extra> NodeBuilder<E> {
    pub fn new() -> Self {
        let filename = "";
        Self {
            span: None,
            filename: filename.to_string(),
            current_node_id: 0,
            current_def_id: 0,
            static_count: 0,
            strings: StringPool::new(),
            _e: std::marker::PhantomData::default(),
        }
    }

    pub fn s(&mut self, s: &str) -> StringKey {
        self.strings.intern(s.into())
    }

    fn fresh_def_arg(&mut self) -> DefinitionId {
        let def_id = DefinitionId::Arg(self.current_def_id);
        self.current_def_id += 1;
        def_id
    }

    fn fresh_def_var(&mut self) -> DefinitionId {
        let def_id = DefinitionId::Var(self.current_def_id);
        self.current_def_id += 1;
        def_id
    }

    pub fn unique_static_name(&mut self) -> String {
        let s = format!("__static_x{}", self.static_count);
        self.static_count += 1;
        s
    }

    pub fn identify_node(&mut self, ast: &mut AstNode<E>) {
        if let NodeID(Some(_)) = ast.node_id {
        } else {
            ast.node_id = self.fresh_node_id();
        }
    }

    fn fresh_node_id(&mut self) -> NodeID {
        let node_id = NodeID(Some(self.current_node_id));
        self.current_node_id += 1;
        node_id
    }

    pub fn enter(&mut self, file_id: usize, filename: &str) {
        let begin = CodeLocation {
            pos: 0,
            //line: 0,
            //col: 0,
        };
        let end = CodeLocation {
            pos: 0,
            //line: 0,
            //col: 0,
        };
        let span = Span {
            file_id,
            begin,
            end,
        };
        self.span = Some(span);
        self.filename = filename.to_string();
    }

    pub fn with_loc(&mut self, span: Span) {
        self.span = Some(span);
    }

    pub fn current_file_id(&self) -> usize {
        self.span.as_ref().map(|s| s.file_id).unwrap_or(0)
    }

    pub fn get_location<'c>(&self, context: &'c Context, d: &Diagnostics) -> ir::Location<'c> {
        if let Some(span) = self.span.as_ref() {
            d.location(context, span)
        } else {
            ir::Location::unknown(context)
        }
    }

    pub fn extra(&self) -> E {
        if let Some(span) = self.span.as_ref() {
            //E::span(span.clone())
            E::new(0, CodeLocation::default(), CodeLocation::default())
        } else {
            E::new(0, CodeLocation::default(), CodeLocation::default())
        }
    }

    pub fn build(&self, node: Ast<E>, extra: E) -> AstNode<E> {
        AstNode {
            node,
            extra,
            node_id: NodeID(None),
        }
    }

    pub fn node(&self, ast: Ast<E>) -> AstNode<E> {
        self.build(ast, self.extra())
    }

    pub fn extra_unknown(&self) -> E {
        let begin = CodeLocation {
            pos: 0,
            //line: 0,
            //col: 0,
        };
        let end = CodeLocation {
            pos: 0,
            //line: 0,
            //col: 0,
        };
        E::new(self.current_file_id(), begin, end)
    }

    pub fn error(&self) -> AstNode<E> {
        self.node(Ast::Error)
    }

    pub fn definition(
        &self,
        name: StringKey,
        params: &[(StringKey, AstType)],
        return_type: AstType,
        body: Option<AstNode<E>>,
    ) -> AstNode<E> {
        let params = params
            .into_iter()
            .map(|(name, ty)| ParameterNode {
                name: *name,
                ty: ty.clone(),
                node: Parameter::Normal,
                extra: self.extra_unknown(),
            })
            .collect();
        self.node(Ast::Definition(Definition {
            name, //: self.strings.intern(name.to_string()),
            params,
            return_type: return_type.into(),
            body: body.map(|b| b.into()),
        }))
    }

    pub fn import_prelude(&self) -> AstNode<E> {
        let s = self.string("prelude");
        let arg = self.arg(s);
        self.node(Ast::Builtin(Builtin::Import, vec![arg]))
    }

    pub fn prelude(&mut self) -> Vec<AstNode<E>> {
        let a = self.strings.intern("a".into());
        let print_index = self.strings.intern("print_index".into());
        let print_float = self.strings.intern("print_float".into());
        vec![
            self.definition(print_index, &[(a, AstType::Int)], AstType::Unit, None),
            self.definition(print_float, &[(a, AstType::Float)], AstType::Unit, None),
        ]
    }

    pub fn string(&self, s: &str) -> AstNode<E> {
        self.node(Ast::Literal(Literal::String(s.to_string())))
    }

    pub fn integer(&self, x: i64) -> AstNode<E> {
        self.node(Ast::Literal(Literal::Int(x)))
    }

    pub fn index(&self, x: i64) -> AstNode<E> {
        self.node(Ast::Literal(Literal::Index(x as usize)))
    }

    pub fn bool(&self, x: bool) -> AstNode<E> {
        self.node(Ast::Literal(Literal::Bool(x)))
    }

    pub fn binop(&self, op: BinaryOperation, a: AstNode<E>, b: AstNode<E>) -> AstNode<E> {
        let op_node = BinOpNode::new(op, self.extra());
        let ast = Ast::BinaryOp(op_node, a.into(), b.into());
        self.node(ast)
    }

    pub fn subtract(&self, a: AstNode<E>, b: AstNode<E>) -> AstNode<E> {
        self.binop(BinaryOperation::Subtract, a, b)
    }

    pub fn add(&self, a: AstNode<E>, b: AstNode<E>) -> AstNode<E> {
        self.binop(BinaryOperation::Add, a, b)
    }

    pub fn multiply(&self, a: AstNode<E>, b: AstNode<E>) -> AstNode<E> {
        self.binop(BinaryOperation::Multiply, a, b)
    }

    pub fn ne(&self, a: AstNode<E>, b: AstNode<E>) -> AstNode<E> {
        self.binop(BinaryOperation::NE, a, b)
    }

    pub fn eq(&self, a: AstNode<E>, b: AstNode<E>) -> AstNode<E> {
        self.binop(BinaryOperation::EQ, a, b)
    }

    pub fn seq(&self, nodes: Vec<AstNode<E>>) -> AstNode<E> {
        // flatten nodes
        let nodes = nodes
            .into_iter()
            .map(|expr| expr.to_vec())
            .flatten()
            .collect();
        self.node(Ast::Sequence(nodes))
    }

    pub fn v(&self, name: StringKey) -> AstNode<E> {
        self.ident(name)
    }

    pub fn ident(&self, name: StringKey) -> AstNode<E> {
        self.build(Ast::Identifier(name), self.extra_unknown())
    }

    pub fn deref_offset(&self, value: AstNode<E>, offset: usize) -> AstNode<E> {
        self.node(Ast::Deref(value.into(), DerefTarget::Offset(offset)))
    }

    pub fn global(&self, name: StringKey, value: AstNode<E>) -> AstNode<E> {
        let extra = value.extra.clone();
        self.build(Ast::Global(name, value.into()), extra)
    }

    pub fn test(&self, condition: AstNode<E>, body: AstNode<E>) -> AstNode<E> {
        let extra = body.extra.clone();
        self.build(Ast::Test(condition.into(), body.into()), extra)
    }

    pub fn while_loop(&self, condition: AstNode<E>, body: AstNode<E>) -> AstNode<E> {
        self.node(Ast::While(condition.into(), body.into()))
    }

    pub fn func(
        &self,
        name: StringKey,
        params: &[(StringKey, AstType)],
        return_type: AstType,
        body: AstNode<E>,
    ) -> AstNode<E> {
        self.definition(name, params, return_type, Some(body))
    }

    pub fn ret(&self, node: Option<AstNode<E>>) -> AstNode<E> {
        self.build(Ast::Return(node.map(|n| n.into())), self.extra_unknown())
    }

    pub fn arg(&self, node: AstNode<E>) -> Argument<E> {
        node.into()
    }

    pub fn apply(&self, name: StringKey, args: Vec<Argument<E>>, ty: AstType) -> AstNode<E> {
        let ident = self.ident(name);
        self.build(Ast::Call(ident.into(), args, ty), self.extra_unknown())
    }

    pub fn call(&self, f: AstNode<E>, args: Vec<Argument<E>>, ty: AstType) -> AstNode<E> {
        let extra = f.extra.clone();
        self.build(Ast::Call(f.into(), args, ty), extra)
    }

    pub fn main(&mut self, body: AstNode<E>) -> AstNode<E> {
        let key = self.strings.intern("main".into());
        self.func(key, &[], AstType::Int, body)
    }

    pub fn mutate(&self, lhs: AstNode<E>, rhs: AstNode<E>) -> AstNode<E> {
        let extra = lhs.extra.clone();
        self.build(Ast::Mutate(lhs.into(), rhs.into()), extra)
    }

    pub fn assign(&self, name: StringKey, rhs: AstNode<E>) -> AstNode<E> {
        self.node(Ast::Assign(AssignTarget::Identifier(name), rhs.into()))
    }

    pub fn alloca(&self, name: StringKey, rhs: AstNode<E>) -> AstNode<E> {
        self.node(Ast::Assign(AssignTarget::Alloca(name), rhs.into()))
    }

    pub fn cond(
        &self,
        condition: AstNode<E>,
        then: AstNode<E>,
        else_block: Option<AstNode<E>>,
    ) -> AstNode<E> {
        self.node(Ast::Conditional(
            condition.into(),
            then.into(),
            else_block.map(|x| x.into()),
        ))
    }

    pub fn goto(&self, name: StringKey) -> AstNode<E> {
        self.build(Ast::Goto(name), self.extra_unknown())
    }

    pub fn param(&self, name: StringKey, ty: AstType) -> ParameterNode<E> {
        ParameterNode {
            name,
            ty: ty.clone(),
            node: Parameter::Normal,
            extra: self.extra_unknown(),
        }
    }

    pub fn module(&self, name: StringKey, body: AstNode<E>) -> AstNode<E> {
        self.block(name, &[], body)
    }

    pub fn block(
        &self,
        name: StringKey,
        params: &[(StringKey, AstType)],
        body: AstNode<E>,
    ) -> AstNode<E> {
        let extra = body.extra.clone();
        let params = params
            .iter()
            .map(|(name, ty)| ParameterNode {
                name: *name,
                ty: ty.clone(),
                node: Parameter::Normal,
                extra: self.extra_unknown(),
            })
            .collect();
        let nb = NodeBlock {
            name,
            params,
            body: body.into(),
        };
        self.build(Ast::Block(nb), extra)
    }
}

pub struct AstBlockSorter<E> {
    pub stack: Vec<AstNode<E>>,
    pub blocks: Vec<AstNode<E>>,
}
impl<E: Extra> AstBlockSorter<E> {
    pub fn new() -> Self {
        Self {
            stack: vec![],
            blocks: vec![],
        }
    }
    pub fn sort_children(
        &mut self,
        ast: AstNode<E>,
        entry_params: &[ParameterNode<E>],
        b: &mut NodeBuilder<E>,
    ) {
        match ast.node {
            Ast::Sequence(exprs) => {
                for e in exprs {
                    if self.blocks.len() == 0 {
                        self.sort_children(e, entry_params, b);
                    } else {
                        self.sort_children(e, &[], b);
                    }
                }
            }
            Ast::Block(ref nb) => {
                // check params match
                if self.blocks.len() == 0 {
                    assert_eq!(nb.params.len(), entry_params.len());
                }
                self.blocks.push(ast);
            }
            Ast::Goto(_) => {
                self.stack.push(ast);
                self.close_block(b);
            }
            Ast::Label(_) => {
                self.close_block(b);
                self.stack.push(ast);
            }
            _ => {
                self.stack.push(ast);
            }
        }
    }

    fn close_block(&mut self, b: &mut NodeBuilder<E>) {
        if self.stack.len() == 0 {
            return;
        }

        let extra = self.stack.first().unwrap().extra.clone();
        // end of block
        let offset = self.blocks.len();

        let name = b.strings.intern(format!("_block{}", offset));
        let seq = b
            .seq(self.stack.drain(..).collect())
            .set_extra(extra.clone());
        let nb = NodeBlock {
            name,
            params: vec![],
            body: seq.into(),
        };
        let ast = b.build(Ast::Block(nb), extra.clone());
        self.blocks.push(ast);
    }
}

impl<'c, E: Extra> Definition<E> {
    pub fn normalize(mut self, b: &mut NodeBuilder<E>) -> Self {
        // ensure that the function body is a sequence of named blocks
        if let Some(body) = self.body {
            let extra = body.extra.clone();
            // sort body
            let mut s = crate::builder::AstBlockSorter::new();
            s.sort_children(*body, &self.params, b);

            let mut blocks = VecDeque::new();

            // initial nodes form the entry block
            if s.stack.len() > 0 {
                let seq = b.seq(s.stack).set_extra(extra.clone());
                // TODO: check that function args match the first block args
                let params = self
                    .params
                    .iter()
                    .map(|p| {
                        if let Parameter::Normal = p.node {
                            ParameterNode {
                                name: p.name.clone(),
                                ty: p.ty.clone(),
                                node: Parameter::Normal,
                                extra: p.extra.clone(),
                            }
                        } else {
                            unreachable!()
                        }
                    })
                    .collect::<Vec<_>>();
                let nb = NodeBlock {
                    name: b.strings.intern("entry".to_string()),
                    params,
                    body: seq.into(),
                };
                let node = b.build(Ast::Block(nb), extra.clone());
                blocks.push_back(node.into());
            }

            blocks.extend(s.blocks.into_iter().map(|b| b.into()));

            let mut body = b.seq(blocks.into_iter().collect()).set_extra(extra.clone());
            body.analyze(b);
            self.body = Some(body.into());
        }
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_log::test;

    #[test]
    fn test_builder() {}
}
