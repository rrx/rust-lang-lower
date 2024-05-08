use compile_core::ast::*;
use compile_core::{
    Argument, Ast, AstNode, AstType, Definition, DefinitionId, Literal, Parameter, ParameterNode,
    SpanBuilder, SpanId, StringKey, StringPool, TypeId, TypePool,
};

use crate::BuiltinBuilder;

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
    pub fn to_string(self, b: &NodeBuilder) -> String {
        match self {
            Self::Name(key) => b.r(key).to_string(),
            Self::U(i) => format!("b{}", i),
        }
    }
}

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

pub struct TypeBuilder {
    pool: TypePool,
}

impl TypeBuilder {
    pub fn new() -> Self {
        Self {
            pool: TypePool::new(),
        }
    }
}

pub struct NodeBuilder {
    filename: String,
    current_node_id: u32,
    current_def_id: u32,
    static_count: usize,
    loop_count: usize,
    pub labels: LabelBuilder,
    pub types: TypeBuilder,
    pub builtins: BuiltinBuilder,
    pub spans: SpanBuilder,
}

impl NodeBuilder {
    pub fn new() -> Self {
        let filename = "";
        let mut s = Self {
            filename: filename.to_string(),
            current_node_id: 0,
            current_def_id: 0,
            static_count: 0,
            loop_count: 0,
            labels: LabelBuilder::new(),
            types: TypeBuilder::new(),
            builtins: BuiltinBuilder::new(),
            spans: SpanBuilder::new(),
        };
        s.init();
        s
    }

    fn init(&mut self) {
        let ty = AstType::Func(vec![AstType::Bool], AstType::Unit.into());
        let ty = self.t(&ty);
        let b = compile_core::Builtin::new("check".into(), ty);
        self.builtins.insert(b);

        let ty = AstType::Func(vec![AstType::String], AstType::Unit.into());
        let ty = self.t(&ty);
        let b = compile_core::Builtin::new("use".into(), ty);
        self.builtins.insert(b);

        let ty = AstType::Func(
            vec![AstType::Sum(vec![AstType::Int, AstType::Float])],
            AstType::Unit.into(),
        );
        let ty = self.t(&ty);
        let b = compile_core::Builtin::new("print".into(), ty);
        self.builtins.insert(b);
    }

    pub fn r(&self, key: StringKey) -> &str {
        self.labels.strings.resolve(&key)
    }

    pub fn s(&mut self, s: &str) -> StringKey {
        self.labels.strings.intern(s.into())
    }

    pub fn t(&mut self, t: &AstType) -> TypeId {
        self.types.pool.intern(t.clone())
    }

    pub fn rt(&mut self, id: TypeId) -> &AstType {
        self.types.pool.resolve(&id)
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

    pub fn build_literal_from_identifier(&self, name: &str) -> Option<AstNode> {
        match name {
            "True" => Some(self.bool(true)),
            "False" => Some(self.bool(false)),
            _ => None,
        }
    }

    pub fn build_builtin_from_name(
        &mut self,
        name: &str,
        args: Vec<Argument>,
        span_id: SpanId,
    ) -> Option<AstNode> {
        if let Some(b) = crate::builtin_from_name(name) {
            assert_eq!(b.arity(), args.len());
            let id = self.builtins.get_id(b);
            Some(self.build(Ast::Builtin(id, args), span_id))
        } else if let Some(ast) = ast_from_name(name, args, self) {
            Some(self.build(ast, span_id))
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

    pub fn build(&self, node: Ast, span_id: SpanId) -> AstNode {
        AstNode { node, span_id }
    }

    pub fn node(&self, ast: Ast) -> AstNode {
        AstNode {
            node: ast,
            span_id: SpanId::unknown(),
        }
    }

    pub fn error(&self, span_id: SpanId) -> AstNode {
        self.build(Ast::Error, span_id)
    }

    pub fn definition(
        &mut self,
        name: StringKey,
        params: &[(StringKey, AstType)],
        return_type: AstType,
        body: Option<AstNode>,
    ) -> AstNode {
        let params = params
            .into_iter()
            .map(|(name, ty)| {
                let ty = self.t(ty);
                ParameterNode {
                    name: *name,
                    ty,
                    node: Parameter::Normal,
                    span_id: SpanId::unknown(),
                }
            })
            .collect();

        let return_type = self.t(&return_type);
        self.global(
            name,
            self.node(Ast::Definition(Definition {
                params,
                return_type,
                body: body.map(|b| b.into()),
            })),
        )
    }

    pub fn import_prelude(&self) -> AstNode {
        let s = self.string("prelude");
        let arg = self.arg(s);
        let id = self.builtins.get_id(crate::Builtin::Import);
        self.node(Ast::Builtin(id, vec![arg]))
    }

    pub fn prelude(&mut self) -> Vec<AstNode> {
        let a = self.s("a".into());
        let print_index = self.s("print_index".into());
        let print_float = self.s("print_float".into());
        vec![
            self.definition(print_index, &[(a, AstType::Int)], AstType::Unit, None),
            self.definition(print_float, &[(a, AstType::Float)], AstType::Unit, None),
        ]
    }

    pub fn string(&self, s: &str) -> AstNode {
        self.node(Ast::Literal(Literal::String(s.to_string())))
    }

    pub fn integer(&self, x: i64) -> AstNode {
        self.node(Ast::Literal(Literal::Int(x)))
    }

    pub fn index(&self, x: i64) -> AstNode {
        self.node(Ast::Literal(Literal::Index(x as usize)))
    }

    pub fn bool(&self, x: bool) -> AstNode {
        self.node(Ast::Literal(Literal::Bool(x)))
    }

    pub fn binop(&self, op: BinaryOperation, a: AstNode, b: AstNode) -> AstNode {
        let op_node = BinOpNode::new(op, SpanId::unknown());
        let ast = Ast::BinaryOp(op_node, a.into(), b.into());
        self.node(ast)
    }

    pub fn subtract(&self, a: AstNode, b: AstNode) -> AstNode {
        self.binop(BinaryOperation::Subtract, a, b)
    }

    pub fn add(&self, a: AstNode, b: AstNode) -> AstNode {
        self.binop(BinaryOperation::Add, a, b)
    }

    pub fn multiply(&self, a: AstNode, b: AstNode) -> AstNode {
        self.binop(BinaryOperation::Multiply, a, b)
    }

    pub fn ne(&self, a: AstNode, b: AstNode) -> AstNode {
        self.binop(BinaryOperation::NE, a, b)
    }

    pub fn eq(&self, a: AstNode, b: AstNode) -> AstNode {
        self.binop(BinaryOperation::EQ, a, b)
    }

    pub fn seq(&self, nodes: Vec<AstNode>) -> AstNode {
        // flatten nodes
        let nodes = nodes
            .into_iter()
            .map(|expr| expr.to_vec())
            .flatten()
            .collect();
        self.node(Ast::Sequence(nodes))
    }

    pub fn v(&self, name: StringKey) -> AstNode {
        self.ident(name)
    }

    pub fn ident(&self, name: StringKey) -> AstNode {
        self.node(Ast::Identifier(name))
    }

    pub fn global(&self, name: StringKey, value: AstNode) -> AstNode {
        self.node(Ast::Global(name, value.into()))
    }

    pub fn while_loop(&self, condition: AstNode, body: AstNode) -> AstNode {
        self.node(Ast::While(condition.into(), body.into()))
    }

    pub fn loop_break(&self, key: Option<StringKey>) -> AstNode {
        self.node(Ast::Break(key, vec![]))
    }

    pub fn loop_continue(&self, key: Option<StringKey>) -> AstNode {
        self.node(Ast::Continue(key, vec![]))
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

    pub fn ret(&self, node: Option<AstNode>) -> AstNode {
        self.node(Ast::Return(node.map(|n| n.into())))
    }

    pub fn arg(&self, node: AstNode) -> Argument {
        node.into()
    }

    pub fn apply(&self, name: StringKey, args: Vec<Argument>, ty: TypeId) -> AstNode {
        let ident = self.ident(name);
        self.node(Ast::Call(ident.into(), args, ty))
    }

    pub fn call(&self, f: AstNode, args: Vec<Argument>, ty: TypeId) -> AstNode {
        self.node(Ast::Call(f.into(), args, ty))
    }

    pub fn main(&mut self, body: AstNode) -> AstNode {
        let key = self.s("main".into());
        self.func(key, &[], AstType::Int, body)
    }

    pub fn assign(&self, name: StringKey, rhs: AstNode) -> AstNode {
        self.node(Ast::Assign(AssignTarget::Identifier(name), rhs.into()))
    }

    pub fn alloca(&self, name: StringKey, rhs: AstNode) -> AstNode {
        self.node(Ast::Assign(AssignTarget::Alloca(name), rhs.into()))
    }

    pub fn cond(&self, condition: AstNode, then: AstNode, else_block: Option<AstNode>) -> AstNode {
        self.node(Ast::Conditional(
            condition.into(),
            then.into(),
            else_block.map(|x| x.into()),
        ))
    }

    pub fn label(&self, name: StringKey) -> AstNode {
        self.node(Ast::BlockStart(name, vec![]))
    }

    pub fn block_start(&self, name: StringKey, params: Vec<ParameterNode>) -> AstNode {
        self.node(Ast::BlockStart(name, params))
    }

    pub fn goto(&self, name: StringKey) -> AstNode {
        self.node(Ast::Goto(name))
    }

    pub fn param(&mut self, name: StringKey, ty: AstType) -> ParameterNode {
        let ty = self.t(&ty);
        ParameterNode {
            name,
            ty: ty.clone(),
            node: Parameter::Normal,
            span_id: SpanId::unknown(),
        }
    }

    pub fn module(&self, name: StringKey, body: AstNode) -> AstNode {
        let span_id = body.span_id;
        AstNode {
            node: Ast::Module(name, body.into()),
            span_id,
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    pub fn gen_block<'c>(b: &mut NodeBuilder) -> AstNode {
        // global variable x = 10
        //seq.push(b.global("z", b.integer(10)));
        let y = b.s("y").into();
        let yy = b.s("yy").into();
        let asdf = b.s("asdf");
        let asdf2 = b.s("asdf2").into();
        let entry = b.s("entry").into();
        let main = b.main(b.seq(vec![
            // entry
            b.label(entry),
            b.assign(yy, b.integer(1)),
            b.alloca(y, b.integer(999)),
            b.goto(asdf.into()),
            // asdf
            b.label(asdf),
            b.assign(yy, b.integer(2)),
            b.goto(asdf2),
            // asdf2
            b.label(asdf2),
            b.assign(yy, b.integer(3)),
            b.ret(Some(b.integer(0))),
        ]));
        b.seq(vec![b.import_prelude(), main])
    }

    pub fn gen_while<'c>(b: &mut NodeBuilder) -> AstNode {
        let mut seq = vec![b.import_prelude()];

        // global variable x = 10
        let x = b.s("x").into();
        let x2 = b.s("x2").into();
        let z = b.s("z").into();
        let y = b.s("y").into();
        let z_static = b.s("z_static");

        seq.push(b.global(z, b.integer(10)));
        seq.push(b.main(b.seq(vec![
            // define local var
            // allocate mutable var
            b.assign(x, b.integer(123)),
            b.alloca(x2, b.integer(10)),
            b.while_loop(
                b.ne(b.ident(x2.into()), b.integer(0)),
                b.seq(vec![
                    // static variable with local scope
                    b.global(z_static, b.integer(10)),
                    b.assign(z_static, b.integer(10)),
                    // mutate global variable
                    b.assign(z, b.subtract(b.ident(z.into()), b.integer(1))),
                    // mutate scoped variable
                    b.assign(x2, b.subtract(b.ident(x2.into()), b.integer(1))),
                    b.assign(z_static, b.subtract(b.ident(z_static.into()), b.integer(1))),
                    // assign local
                    b.assign(y, b.subtract(b.ident(x.into()), b.ident(z_static.into()))),
                ]),
            ),
            b.ret(Some(b.ident(z.into()))),
        ])));

        b.seq(seq)
    }

    pub fn gen_function_call<'c>(b: &mut NodeBuilder) -> AstNode {
        let x = b.s("x").into();
        let x1 = b.s("x1").into();
        let z = b.s("z").into();
        let y = b.s("y").into();
        let arg0 = b.s("arg0").into();
        let t_int = b.t(&AstType::Int);

        let mut seq = vec![b.import_prelude()];
        seq.push(b.global(z, b.integer(10)));

        seq.push(b.func(
            x1,
            &[(arg0, AstType::Int)],
            AstType::Int,
            b.seq(vec![
                // using an alloca
                b.alloca(y, b.ident(arg0.into())),
                b.cond(
                    b.ne(b.ident(y.into()), b.integer(0)),
                    b.seq(vec![
                        b.assign(y, b.subtract(b.ident(y.into()), b.integer(1))),
                        b.assign(y, b.apply(x1.into(), vec![b.ident(y.into()).into()], t_int)),
                    ]),
                    None,
                ),
                // using args
                b.cond(
                    b.ne(b.ident(arg0.into()), b.integer(0)),
                    b.seq(vec![b.assign(
                        y,
                        b.apply(
                            x1.into(),
                            vec![b.subtract(b.ident(arg0.into()), b.integer(1).into()).into()],
                            t_int,
                        ),
                    )]),
                    None,
                ),
                b.ret(Some(b.ident(y.into()))),
            ]),
        ));

        seq.push(b.main(b.seq(vec![
            b.assign(x, b.apply(x1.into(), vec![b.integer(10).into()], t_int)),
            b.assign(x, b.apply(x1.into(), vec![b.integer(0).into()], t_int)),
            b.ret(Some(b.ident(x.into()))),
        ])));
        b.seq(seq)
    }
}

pub fn ast_from_name(name: &str, mut args: Vec<Argument>, b: &mut NodeBuilder) -> Option<Ast> {
    if name == "goto" {
        let rest = args
            .split_off(1)
            .into_iter()
            .map(|a| {
                let Argument::Positional(expr) = a;
                *expr
            })
            .collect::<Vec<_>>();
        assert_eq!(rest.len(), 0);
        let s = args.pop().unwrap().try_string().unwrap();
        let key = b.s(&s);
        Some(Ast::Goto(key.into()))
    } else if name == "static" {
        println!("args: {:?}", args);
        let Argument::Positional(value) = args.pop().unwrap();
        let Argument::Positional(name_node) = args.pop().unwrap();
        let name = b.s(&name_node.try_string().unwrap());
        Some(Ast::global(name, *value))
    } else if name == "label" {
        let rest = args.split_off(1);
        let s = args.pop().unwrap().try_string().unwrap();
        let key = b.s(&s);

        let mut params = vec![];
        for arg in rest {
            let Argument::Positional(node) = arg;
            let name = node.try_string().unwrap();
            let key = b.s(&name);
            let ty = b.t(&AstType::Unit);
            params.push(ParameterNode {
                name: key,
                ty,
                node: Parameter::Normal,
                span_id: SpanId::unknown(),
            });
        }
        Some(Ast::BlockStart(key.into(), vec![]))
    } else if name == "ternary" {
        let Argument::Positional(else_expr) = args.pop().unwrap();
        let Argument::Positional(then_expr) = args.pop().unwrap();
        let Argument::Positional(condition) = args.pop().unwrap();
        Some(Ast::Ternary(
            condition.into(),
            then_expr.into(),
            else_expr.into(),
        ))
    } else {
        None
    }
}
