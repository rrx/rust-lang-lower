use crate::ast::*;
use crate::intern::StringPool;
use crate::Diagnostics;
use crate::{
    //ir::{IRArg, IRBlock, IRKind, IRNode, IRTypeSelect},
    AstType,
    Span,
    SpanId,
    //CodeLocation,
    //NodeIndex, PlaceId,
    StringKey,
};
use melior::{ir::Location, Context};

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum BlockId {
    Name(StringKey),
    // unique
    U(usize),
}

impl From<StringKey> for BlockId {
    fn from(item: StringKey) -> BlockId {
        BlockId::Name(item)
    }
}

impl From<&StringKey> for BlockId {
    fn from(item: &StringKey) -> BlockId {
        BlockId::Name(*item)
    }
}

impl BlockId {
    pub fn to_string<E: Extra>(self, b: &NodeBuilder<E>) -> String {
        match self {
            Self::Name(key) => b.r(key).to_string(),
            Self::U(i) => format!("b{}", i),
        }
    }
}

/*
#[derive(Debug, Clone, Copy)]
pub struct NodeID(Option<u32>);
impl NodeID {
    pub fn is_valid(&self) -> bool {
        self.0.is_some()
    }
}
*/

#[derive(Debug, Eq, PartialEq, Hash, Clone, Copy)]
pub enum StringLabel {
    Intern(StringKey),
    Variable(usize),
}

impl From<StringKey> for StringLabel {
    fn from(item: StringKey) -> Self {
        Self::Intern(item)
    }
}

impl From<&StringKey> for StringLabel {
    fn from(item: &StringKey) -> Self {
        Self::Intern(*item)
    }
}

pub struct LabelBuilder {
    unique_count: usize,
    strings: StringPool,
}

impl LabelBuilder {
    pub fn new() -> Self {
        Self {
            unique_count: 0,
            strings: StringPool::new(),
        }
    }

    pub fn fresh_block_id(&mut self) -> BlockId {
        let offset = self.unique_count;
        self.unique_count += 1;
        BlockId::U(offset)
    }

    pub fn fresh_var_id(&mut self) -> StringLabel {
        let offset = self.unique_count;
        self.unique_count += 1;
        StringLabel::Variable(offset)
    }
}

pub struct NodeBuilder<E> {
    span: Option<Span>,
    filename: String,
    current_node_id: u32,
    current_def_id: u32,
    static_count: usize,
    loop_count: usize,
    pub extra_unknown: E,
    pub span_id: SpanId,
    pub labels: LabelBuilder,
    _e: std::marker::PhantomData<E>,
}

impl<E: Extra> NodeBuilder<E> {
    pub fn new(d: &mut Diagnostics) -> Self {
        let filename = "";
        let span_unknown = d.get_span_unknown();
        Self {
            span: None,
            filename: filename.to_string(),
            current_node_id: 0,
            current_def_id: 0,
            static_count: 0,
            loop_count: 0,
            labels: LabelBuilder::new(),
            span_id: span_unknown.span_id.clone(),
            extra_unknown: E::span(span_unknown),
            _e: std::marker::PhantomData::default(),
        }
    }

    pub fn r(&self, key: StringKey) -> &str {
        self.labels.strings.resolve(&key)
    }

    pub fn s(&mut self, s: &str) -> StringKey {
        self.labels.strings.intern(s.into())
    }

    pub fn resolve_block_label(&self, k: BlockId) -> String {
        match k {
            BlockId::Name(key) => self.labels.strings.resolve(&key).clone(),
            BlockId::U(offset) => format!("b{}", offset),
        }
    }

    pub fn resolve_label(&self, k: StringLabel) -> String {
        match k {
            StringLabel::Intern(key) => self.labels.strings.resolve(&key).clone(),
            StringLabel::Variable(offset) => format!("v{}", offset),
        }
    }

    pub fn build_literal_from_identifier(&self, name: &str) -> Option<AstNode<E>> {
        match name {
            "True" => Some(self.bool(true)),
            "False" => Some(self.bool(false)),
            _ => None,
        }
    }

    pub fn build_builtin_from_name(
        &mut self,
        name: &str,
        args: Vec<Argument<E>>,
    ) -> Option<AstNode<E>> {
        if let Some(b) = Builtin::from_name(name) {
            assert_eq!(b.arity(), args.len());
            Some(self.node(Ast::Builtin(b, args)))
        } else if let Some(ast) = Ast::from_name(name, args, self) {
            Some(self.node(ast))
        } else {
            None
        }
    }

    pub fn fresh_loop_name(&mut self) -> StringKey {
        let unique = self.loop_count;
        self.loop_count += 1;
        let s = format!("_loop{}", unique);
        let key = self.s(&s);
        key
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

    /*
    pub fn enter(&mut self, file_id: usize, filename: &str) {
        let begin = CodeLocation { pos: 0 };
        let end = CodeLocation { pos: 0 };
        let span = Span {
            file_id,
            begin,
            end,
        };
        self.span = Some(span);
        self.filename = filename.to_string();
    }
    */

    pub fn with_loc(&mut self, span: Span) {
        self.span = Some(span);
    }

    pub fn current_file_id(&self) -> usize {
        self.span.as_ref().map(|s| s.file_id).unwrap_or(0)
    }

    pub fn get_location<'c>(&self, context: &'c Context, d: &Diagnostics) -> Location<'c> {
        if let Some(span) = self.span.as_ref() {
            d.location(context, span)
        } else {
            Location::unknown(context)
        }
    }

    /*
    pub fn extra(&self) -> E {
        if let Some(span) = self.span.as_ref() {
            E::span(span.clone())
            //E::new(0, CodeLocation::default(), CodeLocation::default())
        } else {
            E::new(0, CodeLocation::default(), CodeLocation::default())
        }
    }
    */

    pub fn build(&self, node: Ast<E>, span_id: SpanId) -> AstNode<E> {
        AstNode {
            node,
            span_id, //: E::get_span(&extra).span_id,
            extra: self.extra_unknown.clone(),
            //node_id: NodeID(None),
        }
    }

    pub fn node(&self, ast: Ast<E>) -> AstNode<E> {
        self.build(ast, self.span_id.clone()) //self.extra_unknown.clone())
    }

    /*
    pub fn extra_unknown(&self) -> E {
        let begin = CodeLocation { pos: 0 };
        let end = CodeLocation { pos: 0 };
        E::new(self.current_file_id(), begin, end)
    }
    */

    pub fn error(&self, extra: E) -> AstNode<E> {
        self.node(Ast::Error)
    }

    pub fn definition(
        &self,
        name: StringKey,
        params: &[(StringKey, AstType)],
        return_type: AstType,
        body: Option<AstNode<E>>,
        lambda: bool,
    ) -> AstNode<E> {
        let params = params
            .into_iter()
            .map(|(name, ty)| ParameterNode {
                name: *name,
                ty: ty.clone(),
                node: Parameter::Normal,
                span_id: self.span_id.clone(),
                //extra: self.extra_unknown.clone(),
            })
            .collect();
        self.node(Ast::Definition(Definition {
            name,
            params,
            lambda,
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
        let a = self.s("a".into());
        let print_index = self.s("print_index".into());
        let print_float = self.s("print_float".into());
        vec![
            self.definition(
                print_index,
                &[(a, AstType::Int)],
                AstType::Unit,
                None,
                false,
            ),
            self.definition(
                print_float,
                &[(a, AstType::Float)],
                AstType::Unit,
                None,
                false,
            ),
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
        let op_node = BinOpNode::new(op, self.span_id.clone());
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
        self.build(Ast::Identifier(name), self.span_id.clone()) //self.extra_unknown.clone())
    }

    pub fn deref_offset(&self, value: AstNode<E>, offset: usize) -> AstNode<E> {
        self.node(Ast::Deref(value.into(), DerefTarget::Offset(offset)))
    }

    pub fn global(&self, name: StringKey, value: AstNode<E>) -> AstNode<E> {
        //let extra = value.extra.clone();
        self.build(Ast::Global(name, value.into()), self.span_id.clone()) //extra)
    }

    pub fn test(&self, condition: AstNode<E>, body: AstNode<E>) -> AstNode<E> {
        //let extra = body.extra.clone();
        self.build(
            Ast::Test(condition.into(), body.into()),
            self.span_id.clone(),
        ) //extra)
    }

    pub fn while_loop(&self, condition: AstNode<E>, body: AstNode<E>) -> AstNode<E> {
        self.node(Ast::While(condition.into(), body.into()))
    }

    pub fn loop_break(&self, key: Option<StringKey>) -> AstNode<E> {
        self.node(Ast::Break(key, vec![]))
    }

    pub fn loop_continue(&self, key: Option<StringKey>) -> AstNode<E> {
        self.node(Ast::Continue(key, vec![]))
    }

    pub fn func(
        &self,
        name: StringKey,
        params: &[(StringKey, AstType)],
        return_type: AstType,
        body: AstNode<E>,
    ) -> AstNode<E> {
        self.definition(name, params, return_type, Some(body), false)
    }

    pub fn ret(&self, node: Option<AstNode<E>>) -> AstNode<E> {
        self.build(
            Ast::Return(node.map(|n| n.into())),
            self.span_id.clone(), //self.extra_unknown.clone(),
        )
    }

    pub fn arg(&self, node: AstNode<E>) -> Argument<E> {
        node.into()
    }

    pub fn apply(&self, name: StringKey, args: Vec<Argument<E>>, ty: AstType) -> AstNode<E> {
        let ident = self.ident(name);
        self.build(
            Ast::Call(ident.into(), args, ty),
            //self.extra_unknown.clone(),
            self.span_id.clone(),
        )
    }

    pub fn call(&self, f: AstNode<E>, args: Vec<Argument<E>>, ty: AstType) -> AstNode<E> {
        let extra = f.extra.clone();
        self.build(Ast::Call(f.into(), args, ty), self.span_id.clone()) //extra)
    }

    pub fn main(&mut self, body: AstNode<E>) -> AstNode<E> {
        let key = self.s("main".into());
        self.func(key, &[], AstType::Int, body)
    }

    pub fn mutate(&self, lhs: AstNode<E>, rhs: AstNode<E>) -> AstNode<E> {
        let extra = lhs.extra.clone();
        self.build(Ast::Mutate(lhs.into(), rhs.into()), self.span_id.clone()) //extra)
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

    pub fn label(&self, name: StringKey) -> AstNode<E> {
        self.build(Ast::Label(name), self.span_id.clone()) //self.extra_unknown.clone())
    }

    pub fn block_start(&self, name: StringKey, params: Vec<ParameterNode>) -> AstNode<E> {
        self.build(Ast::BlockStart(name, params), self.span_id.clone()) //self.extra_unknown.clone())
    }

    pub fn goto(&self, name: StringKey) -> AstNode<E> {
        self.build(Ast::Goto(name), self.span_id.clone()) //self.extra_unknown.clone())
    }

    pub fn param(&self, name: StringKey, ty: AstType) -> ParameterNode {
        ParameterNode {
            name,
            ty: ty.clone(),
            node: Parameter::Normal,
            //extra: self.extra_unknown.clone(),
            span_id: self.span_id.clone(),
        }
    }

    pub fn module(&self, name: StringKey, body: AstNode<E>) -> AstNode<E> {
        let extra = body.extra.clone();
        self.build(Ast::Module(name, body.into()), self.span_id.clone()) //extra)
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
                //extra: self.extra_unknown.clone(),
                span_id: self.span_id.clone(),
            })
            .collect();
        let nb = AstNodeBlock {
            name: name.into(),
            params,
            children: vec![body],
        };
        self.build(Ast::Block(nb), self.span_id.clone()) //extra)
    }

    /*
    pub fn ir_module(&self, label: BlockId, index: NodeIndex, seq: Vec<IRNode>) -> IRNode {
        IRNode::new(
            IRKind::Module(IRBlock::new(index, label, vec![], seq)),
            self.span.clone().unwrap(),
        )
    }

    pub fn ir_noop(&self) -> IRNode {
        IRNode::new(IRKind::Noop, self.span.clone().unwrap())
    }

    pub fn ir_seq(&self, seq: Vec<IRNode>) -> IRNode {
        IRNode::new(IRKind::Seq(seq), self.span.clone().unwrap())
    }

    pub fn ir_ret(&self, seq: Vec<IRNode>) -> IRNode {
        IRNode::new(IRKind::Ret(seq), self.span.clone().unwrap())
    }

    pub fn ir_block(
        &self,
        label: BlockId,
        block_index: NodeIndex,
        args: Vec<IRArg>,
        seq: Vec<IRNode>,
    ) -> IRNode {
        IRNode::new(
            IRKind::Block(IRBlock::new(block_index, label, args, seq)),
            self.span.clone().unwrap(),
        )
    }

    pub fn ir_label(&self, label: BlockId, block_index: NodeIndex, args: Vec<IRArg>) -> IRNode {
        IRNode::new(
            IRKind::Label(label, block_index, args),
            self.span.clone().unwrap(),
        )
    }

    pub fn ir_jump(&self, label: BlockId, args: Vec<IRNode>) -> IRNode {
        IRNode::new(IRKind::Jump(label, args), self.span.clone().unwrap())
    }

    pub fn ir_get(&self, place_id: PlaceId, select: IRTypeSelect) -> IRNode {
        IRNode::new(IRKind::Get(place_id, select), self.span.clone().unwrap())
    }

    pub fn ir_set(&self, place_id: PlaceId, expr: IRNode, select: IRTypeSelect) -> IRNode {
        IRNode::new(
            IRKind::Set(place_id, expr.into(), select),
            self.span.clone().unwrap(),
        )
    }

    pub fn ir_decl(&self, place_id: PlaceId) -> IRNode {
        IRNode::new(IRKind::Decl(place_id), self.span.clone().unwrap())
    }

    pub fn ir_call(&self, key: StringLabel, args: Vec<IRNode>) -> IRNode {
        IRNode::new(IRKind::Call(key, args), self.span.clone().unwrap())
    }

    pub fn ir_float(&self, f: f64) -> IRNode {
        IRNode::new(
            IRKind::Literal(Literal::Float(f)),
            self.span.clone().unwrap(),
        )
    }

    pub fn ir_integer(&self, f: i64) -> IRNode {
        IRNode::new(IRKind::Literal(Literal::Int(f)), self.span.clone().unwrap())
    }

    pub fn ir_index(&self, f: usize) -> IRNode {
        IRNode::new(
            IRKind::Literal(Literal::Index(f)),
            self.span.clone().unwrap(),
        )
    }

    pub fn ir_bool(&self, f: bool) -> IRNode {
        IRNode::new(
            IRKind::Literal(Literal::Bool(f)),
            self.span.clone().unwrap(),
        )
    }

    pub fn ir_string(&self, f: String) -> IRNode {
        IRNode::new(
            IRKind::Literal(Literal::String(f)),
            self.span.clone().unwrap(),
        )
    }

    pub fn ir_op1(&self, op: UnaryOperation, v: IRNode) -> IRNode {
        IRNode::new(IRKind::Op1(op, v.into()), self.span.clone().unwrap())
    }

    pub fn ir_op2(&self, op: BinaryOperation, a: IRNode, b: IRNode) -> IRNode {
        IRNode::new(
            IRKind::Op2(op, a.into(), b.into()),
            self.span.clone().unwrap(),
        )
    }

    pub fn ir_ternary(&self, condition: IRNode, a: IRNode, b: IRNode) -> IRNode {
        IRNode::new(
            IRKind::Ternary(condition.into(), a.into(), b.into()),
            self.span.clone().unwrap(),
        )
    }

    pub fn ir_branch(&self, condition: IRNode, then_br: BlockId, else_br: BlockId) -> IRNode {
        IRNode::new(
            IRKind::Branch(condition.into(), then_br, else_br),
            self.span.clone().unwrap(),
        )
    }

    pub fn ir_cond(
        &self,
        condition: IRNode,
        then_expr: IRNode,
        maybe_else_expr: Option<IRNode>,
    ) -> IRNode {
        IRNode::new(
            IRKind::Cond(
                condition.into(),
                then_expr.into(),
                maybe_else_expr.map(|e| e.into()),
            ),
            self.span.clone().unwrap(),
        )
    }
    */
}

/*
impl<'c, E: Extra> Definition<E> {
    pub fn normalize2(mut self, b: &mut NodeBuilder<E>) -> Self {
        // ensure that the function body is a sequence of named blocks
        if let Some(body) = self.body {
            let extra = body.extra.clone();
            // sort body
            let mut s = crate::sort::AstBlockSorter::new();

            // push label that matches the function signature
            s.stack.push(b.label(self.name.into(), self.params.clone()));
            s.sort_children(*body, &self.params, b);

            let mut blocks = vec![];

            // initial nodes form the entry block
            if s.stack.len() > 0 {
                // ensure a well formed block
                // must start with a label and end with a terminator
                // statements in between should be neither
                for (i, v) in s.stack.iter().enumerate() {
                    if i == 0 {
                        // first
                        assert!(v.node.is_label());
                    } else if i + 1 == s.stack.len() {
                        //last
                        assert!(v.node.terminator().is_some());
                    } else {
                        assert!(v.node.terminator().is_none());
                        assert_eq!(false, v.node.is_label());
                    }
                }

                //let children = s.stack.into_iter().skip(1).collect::<Vec<_>>().drain(..).collect();
                let children = s.stack;
                //let seq = b.seq(s.stack).set_extra(extra.clone());

                // TODO: check that function args match the first block args
                let params = self
                    .params
                    .iter()
                    .map(|p| {
                        //if let Parameter::Normal = p.node {
                        ParameterNode {
                            name: p.name.clone(),
                            ty: p.ty.clone(),
                            node: Parameter::Normal,
                            extra: p.extra.clone(),
                        }
                        //} else {
                        //unreachable!()
                        //}
                    })
                    .collect::<Vec<_>>();
                let nb = AstNodeBlock {
                    name: self.name.into(), //StringLabel::Intern(self.name), //b.strings.intern("entry".to_string()),
                    params,
                    children,
                };
                let node = b.build(Ast::Block(nb), extra.clone());
                blocks.push(node.into());
            }

            blocks.extend(s.blocks.into_iter().map(|b| b.into()));

            let mut body = b.seq(blocks.into_iter().collect()).set_extra(extra.clone());
            body.analyze(b);
            self.body = Some(body.into());
        }
        self
    }
}
*/

#[cfg(test)]
mod tests {
    //use super::*;
    use test_log::test;

    #[test]
    fn test_builder() {}
}
