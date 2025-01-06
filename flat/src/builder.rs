use compile_core::ast::*;
use compile_core::{
    Argument, Ast, AstFuncType, AstNode, AstType, Lambda, Literal, Parameter, ParameterNode,
    ReturnType, Span, SpanBuilder, SpanId, StringKey, StringPool, TypeId, TypePool,
};
use hmunify::TypeUnify;

use std::collections::HashMap;

use crate::BuiltinBuilder;

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
    pub pool: StringPool,
}

impl LabelBuilder {
    pub fn new() -> Self {
        Self {
            unique_count: 0,
            pool: StringPool::new(),
        }
    }

    pub fn fresh_key(&mut self, prefix: &str) -> StringKey {
        let offset = self.unique_count;
        self.unique_count += 1;
        self.s(&format!(".{}.{}", prefix, offset))
    }

    pub fn fresh_var_id(&mut self) -> StringLabel {
        let offset = self.unique_count;
        self.unique_count += 1;
        StringLabel::Variable(offset)
    }

    pub fn r(&self, k: StringLabel) -> String {
        match k {
            StringLabel::Intern(key) => self.pool.resolve(&key).clone(),
            StringLabel::Variable(offset) => format!("v{}", offset),
        }
    }

    pub fn s(&mut self, s: &str) -> StringKey {
        self.pool.intern(s.into())
    }
}

pub struct TypeBuilder {
    pool: TypePool,
    //unknown_count: u32,
    pub u: TypeUnify,
}

impl TypeBuilder {
    pub fn new() -> Self {
        Self {
            pool: TypePool::new(),
            u: TypeUnify::new(),
        }
    }

    pub fn fresh_unknown(&mut self) -> AstType {
        self.u.fresh_unknown().into()
    }

    pub fn fresh_type_arg(&mut self) -> AstType {
        self.u.fresh_type_arg().into()
    }

    pub fn fresh_args(&mut self) -> AstType {
        let t = self.fresh_unknown();
        AstType::Args(t.into())
    }

    pub fn fresh_kwargs(&mut self) -> AstType {
        let t = self.fresh_unknown();
        AstType::KwArgs(t.into())
    }

    pub(super) fn refresh_func_type(&mut self, def_func_type: &AstFuncType) -> AstFuncType {
        // refresh variables
        match &def_func_type.ret {
            ReturnType::Single(ret_ty) => AstFuncType::new(
                self.refresh(def_func_type.args.clone()),
                ReturnType::Single(self.refresh(ret_ty.clone())),
            ),
            ReturnType::Never => {
                AstFuncType::new(self.refresh(def_func_type.args.clone()), ReturnType::Never)
            }
            _ => unreachable!(),
        }
    }

    pub fn refresh(&mut self, ty: AstType) -> AstType {
        match ty {
            AstType::Variable(_) => self.fresh_unknown(),
            AstType::Func(f) => self.refresh_func_type(&f).into(),
            AstType::Struct(fields) => {
                let fields = fields
                    .into_iter()
                    .map(|(key, f)| (key, self.refresh(f)))
                    .collect();
                AstType::Struct(fields)
            }
            AstType::Args(ty) => AstType::Args(self.refresh(*ty).into()),
            _ => {
                if ty.is_unknown() {
                    unreachable!("{}", ty)
                } else {
                    ty
                }
            }
        }
    }
    pub fn dump(&mut self) {
        self.u.dump();
    }

    pub fn s(&mut self, t: &AstType) -> TypeId {
        self.pool.intern(t.clone())
    }

    pub fn r(&self, id: TypeId) -> &AstType {
        self.pool.resolve(&id)
    }
}

pub struct NodeBuilder {
    static_count: usize,
    loop_count: usize,
    pub labels: LabelBuilder,
    pub types: TypeBuilder,
    pub builtins: BuiltinBuilder,
    pub spans: SpanBuilder,
}

impl NodeBuilder {
    pub fn new() -> Self {
        Self {
            static_count: 0,
            loop_count: 0,
            labels: LabelBuilder::new(),
            types: TypeBuilder::new(),
            builtins: BuiltinBuilder::new(),
            spans: SpanBuilder::new(),
        }
    }

    pub fn ensure_seq(ast: AstNode) -> AstNode {
        let span_id = ast.span_id;
        Self::seq(ast.to_vec(), span_id)
    }

    pub fn build_literal_from_identifier(&self, name: &str) -> Option<AstNode> {
        match name {
            "True" => Some(true.into()),
            "False" => Some(false.into()),
            _ => None,
        }
    }

    pub fn build_builtin_from_name(
        &mut self,
        name: &str,
        args: Vec<Argument>,
        span_id: SpanId,
    ) -> Option<AstNode> {
        if let Some(node) = crate::builtin_from_name(name, args, span_id, self) {
            Some(node)
        } else {
            None
        }
    }

    pub fn fresh_loop_name(&mut self) -> StringKey {
        let unique = self.loop_count;
        self.loop_count += 1;
        let s = format!("_loop{}", unique);
        let key = self.labels.s(&s);
        key
    }

    pub fn fresh_block_name(&mut self) -> StringKey {
        let unique = self.loop_count;
        self.loop_count += 1;
        let s = format!("_block{}", unique);
        let key = self.labels.s(&s);
        key
    }

    pub fn unique_static_name(&mut self) -> String {
        let s = format!("__static_x{}", self.static_count);
        self.static_count += 1;
        s
    }

    pub fn definition(
        &mut self,
        name: StringKey,
        def_params: &[(StringKey, AstType)],
        return_type: AstType,
        body: Option<AstNode>,
    ) -> AstNode {
        let arg_type = AstType::Struct(
            def_params
                .into_iter()
                .map(|(key, ty)| (Some(*key), ty.clone()))
                .collect::<Vec<_>>(),
        );
        let fun_type = AstFuncType::new(arg_type, ReturnType::Single(return_type.clone()));
        Self::global(
            name,
            Ast::Lambda(Lambda {
                func_type: fun_type.clone(),
                body: body.map(|b| b.into()),
                defaults: HashMap::new(),
            })
            .into(),
        )
    }

    pub fn import_prelude(&self) -> AstNode {
        let id = self.builtins.get_id(crate::Builtin::Import);
        Ast::Builtin(id, vec![Argument::Positional(Box::new("prelude".into()))]).into()
    }

    pub fn prelude(&mut self) -> Vec<AstNode> {
        let a = self.labels.s("a".into());
        let print_index = self.labels.s("print_index".into());
        let print_float = self.labels.s("print_float".into());
        let print_bool = self.labels.s("print_bool".into());
        vec![
            self.definition(print_index, &[(a, AstType::Int)], AstType::Unit, None),
            self.definition(print_float, &[(a, AstType::Float)], AstType::Unit, None),
            self.definition(print_bool, &[(a, AstType::Bool)], AstType::Unit, None),
        ]
    }

    pub fn index(x: i64) -> AstNode {
        Ast::Literal(Literal::Index(x as usize)).into()
    }

    pub fn binop(op: BinaryOperation, a: AstNode, b: AstNode) -> AstNode {
        let op_node = BinOpNode::new(op, SpanId::unknown());
        Ast::BinaryOp(op_node, a.into(), b.into()).into()
    }

    pub fn subtract(a: AstNode, b: AstNode) -> AstNode {
        Self::binop(BinaryOperation::Subtract, a, b)
    }

    pub fn add(a: AstNode, b: AstNode) -> AstNode {
        Self::binop(BinaryOperation::Add, a, b)
    }

    pub fn multiply(a: AstNode, b: AstNode) -> AstNode {
        Self::binop(BinaryOperation::Multiply, a, b)
    }

    pub fn ne(a: AstNode, b: AstNode) -> AstNode {
        Self::binop(BinaryOperation::NE, a, b)
    }

    pub fn eq(a: AstNode, b: AstNode) -> AstNode {
        Self::binop(BinaryOperation::EQ, a, b)
    }

    pub fn seq(nodes: Vec<AstNode>, span_id: SpanId) -> AstNode {
        // flatten nodes
        let nodes = nodes
            .into_iter()
            .map(|expr| expr.to_vec())
            .flatten()
            .collect();
        Ast::Sequence(nodes).node(span_id)
    }

    pub fn ident(name: StringKey) -> AstNode {
        Ast::Identifier(name).into()
    }

    pub fn global(name: StringKey, value: AstNode) -> AstNode {
        let span_id = value.span_id;
        Ast::Global(name, value.into()).node(span_id)
    }

    pub fn while_loop(condition: AstNode, body: AstNode) -> AstNode {
        Ast::While(condition.into(), body.into()).into()
    }

    pub fn loop_break(key: Option<StringKey>) -> Ast {
        Ast::Break(key, vec![])
    }

    pub fn loop_continue(key: Option<StringKey>) -> Ast {
        Ast::Continue(key, vec![])
    }

    pub fn func(
        &mut self,
        name: StringKey,
        params: &[(StringKey, AstType)],
        return_type: AstType,
        body: AstNode,
    ) -> AstNode {
        self.definition(name, params, return_type, Some(body))
    }

    pub fn ret(node: Option<AstNode>) -> AstNode {
        Ast::Return(node.map(|n| n.into())).into()
    }

    pub fn apply(name: StringKey, args: Vec<Argument>) -> AstNode {
        let ident = Self::ident(name);
        Ast::Call(ident.into(), args).into()
    }

    pub fn call(f: AstNode, args: Vec<Argument>) -> AstNode {
        Ast::Call(f.into(), args).into()
    }

    pub fn main(&mut self, body: AstNode) -> AstNode {
        let key = self.labels.s("main".into());
        self.func(key, &[], AstType::Int, body)
    }

    pub fn assign(name: StringKey, rhs: AstNode) -> AstNode {
        Ast::Assign(AssignTarget::Identifier(name), rhs.into()).into()
    }

    pub fn alloca(name: StringKey, rhs: AstNode) -> AstNode {
        Ast::Assign(AssignTarget::Alloca(name), rhs.into()).into()
    }

    pub fn cond(condition: AstNode, then: AstNode, else_block: Option<AstNode>) -> AstNode {
        Ast::Conditional(condition.into(), then.into(), else_block.map(|x| x.into())).into()
    }

    pub fn label(name: StringKey) -> AstNode {
        ControlFlowMarker::BlockStart(Some(name), vec![]).into()
    }

    pub fn block_start(name: StringKey, params: Vec<ParameterNode>) -> AstNode {
        ControlFlowMarker::BlockStart(Some(name), params).into()
    }

    pub fn goto(name: StringKey, args: Vec<Argument>) -> Ast {
        ControlFlowMarker::Goto(name, args).into()
    }

    pub fn param(&mut self, name: StringKey, ty: AstType) -> ParameterNode {
        let ty = self.types.s(&ty);
        ParameterNode {
            name,
            ty: ty.clone(),
            node: Parameter::Normal,
            span_id: SpanId::unknown(),
            //default: None,
        }
    }

    pub fn module(name: StringKey, body: AstNode) -> AstNode {
        let span_id = body.span_id;
        AstNode {
            node: Ast::Module(name, body.into()),
            span_id,
        }
    }

    pub fn push_error_span(&mut self, msg: &str, span: Span) {
        self.spans
            .push_diagnostic(compile_core::diagnostic_error(msg, span));
    }

    pub fn push_error(&mut self, msg: &str, span_id: SpanId) {
        let span = self.spans.lookup(span_id);
        self.spans
            .push_diagnostic(compile_core::diagnostic_error(msg, span));
    }

    pub fn primary_label(&self, msg: &str, span_id: SpanId) -> compile_core::Label<usize> {
        let span = self.spans.lookup(span_id);
        compile_core::primary_label(msg, &span)
    }

    pub fn secondary_label(&self, msg: &str, span_id: SpanId) -> compile_core::Label<usize> {
        let span = self.spans.lookup(span_id);
        compile_core::secondary_label(msg, &span)
    }

    pub fn push_error_labels(&mut self, labels: Vec<compile_core::Label<usize>>) {
        self.spans
            .push_diagnostic(compile_core::diagnostic_error_labels(labels));
    }

    pub fn push_warning(&mut self, msg: &str, span_id: SpanId) {
        let span = self.spans.lookup(span_id);
        self.spans
            .push_diagnostic(compile_core::diagnostic_warning(msg, span));
    }

    pub fn unify(&mut self, a: &AstType, a_span_id: SpanId, b: &AstType, b_span_id: SpanId) {
        if self.types.u.unify(a, b).is_err() {
            let ty1 = self.types.u.resolve(a).unwrap_or(a.clone());
            let ty2 = self.types.u.resolve(b).unwrap_or(b.clone());
            self.push_error_labels(vec![
                self.primary_label(&format!("Type Mismatch: {}", &ty1), a_span_id),
                self.secondary_label(&format!("reference: {}", &ty2), b_span_id),
            ]);
            println!("Type Mismatch: {} reference: {}", &ty1, &ty2);
            //assert!(false);
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    /*
    use super::NodeBuilder as NB;
    use super::*;


    pub fn gen_block<'c>(b: &mut NodeBuilder) -> AstNode {
        // global variable x = 10
        //seq.push(b.global("z", b.integer(10)));
        let y = b.labels.s("y").into();
        let yy = b.labels.s("yy").into();
        let asdf = b.labels.s("asdf");
        let asdf2 = b.labels.s("asdf2").into();
        let entry = b.labels.s("entry").into();
        let span_id = b.spans.get_span_unknown();
        let main = b.main(NB::seq(
            vec![
                // entry
                NB::label(entry),
                NB::assign(yy, 1.into()),
                NB::alloca(y, 999.into()),
                NB::goto(asdf.into()).into(),
                // asdf
                NB::label(asdf),
                NB::assign(yy, 2.into()),
                NB::goto(asdf2).into(),
                // asdf2
                NB::label(asdf2),
                NB::assign(yy, 3.into()),
                NB::ret(Some(0.into())),
            ],
            span_id,
        ));
        NB::seq(vec![b.import_prelude(), main], span_id)
    }

    pub fn gen_while<'c>(b: &mut NodeBuilder) -> AstNode {
        let mut seq = vec![b.import_prelude()];

        // global variable x = 10
        let x = b.labels.s("x").into();
        let x2 = b.labels.s("x2").into();
        let z = b.labels.s("z").into();
        let y = b.labels.s("y").into();
        let z_static = b.labels.s("z_static");
        let span_id = b.spans.get_span_unknown();

        seq.push(NB::global(z, 10.into()));
        seq.push(b.main(NB::seq(
            vec![
                // define local var
                // allocate mutable var
                NB::assign(x, 123.into()),
                NB::alloca(x2, 10.into()),
                NB::while_loop(
                    NB::ne(NB::ident(x2.into()), 0.into()),
                    NB::seq(
                        vec![
                            // static variable with local scope
                            NB::global(z_static, 10.into()),
                            NB::assign(z_static, 10.into()),
                            // mutate global variable
                            NB::assign(z, NB::subtract(NB::ident(z.into()), 1.into())),
                            // mutate scoped variable
                            NB::assign(x2, NB::subtract(NB::ident(x2.into()), 1.into())),
                            NB::assign(
                                z_static,
                                NB::subtract(NB::ident(z_static.into()), 1.into()),
                            ),
                            // assign local
                            NB::assign(
                                y,
                                NB::subtract(NB::ident(x.into()), NB::ident(z_static.into())),
                            ),
                        ],
                        span_id,
                    ),
                ),
                NB::ret(Some(NB::ident(z.into()))),
            ],
            span_id,
        )));

        NB::seq(seq, span_id)
    }

    pub fn gen_function_call<'c>(b: &mut NodeBuilder) -> AstNode {
        let x = b.labels.s("x").into();
        let x1 = b.labels.s("x1").into();
        let z = b.labels.s("z").into();
        let y = b.labels.s("y").into();
        let arg0 = b.labels.s("arg0").into();
        //let t_int = b.types.s(&AstType::Int);
        let span_id = b.spans.get_span_unknown();

        let mut seq = vec![b.import_prelude()];
        seq.push(NB::global(z, 10.into()));

        seq.push(b.func(
            x1,
            &[(arg0, AstType::Int)],
            AstType::Int,
            NB::seq(
                vec![
                    // using an alloca
                    NB::alloca(y, NB::ident(arg0.into())),
                    NB::cond(
                        NB::ne(NB::ident(y.into()), 0.into()),
                        NB::seq(
                            vec![
                                NB::assign(y, NB::subtract(NB::ident(y.into()), 1.into())),
                                NB::assign(
                                    y,
                                    NB::apply(x1.into(), vec![NB::ident(y.into()).into()]),
                                ),
                            ],
                            span_id,
                        ),
                        None,
                    ),
                    // using args
                    NB::cond(
                        NB::ne(NB::ident(arg0.into()), 0.into()),
                        NB::seq(
                            vec![NB::assign(
                                y,
                                NB::apply(
                                    x1.into(),
                                    vec![NB::subtract(NB::ident(arg0.into()), 1.into()).into()],
                                ),
                            )],
                            span_id,
                        ),
                        None,
                    ),
                    NB::ret(Some(NB::ident(y.into()))),
                ],
                span_id,
            ),
        ));

        seq.push(b.main(NB::seq(
            vec![
                NB::assign(x, NB::apply(x1.into(), vec![AstNode::from(10).into()])),
                NB::assign(x, NB::apply(x1.into(), vec![AstNode::from(0).into()])),
                NB::ret(Some(NB::ident(x.into()))),
            ],
            span_id,
        )));
        NB::seq(seq, span_id)
    }
    */
}
