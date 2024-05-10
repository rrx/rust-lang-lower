use compile_core::ast::*;
use compile_core::{
    Argument, Ast, AstNode, AstType, Definition, Literal, Parameter, ParameterNode, SpanBuilder,
    SpanId, StringKey, StringPool, TypeId, TypePool,
};

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
    pool: StringPool,
}

impl LabelBuilder {
    pub fn new() -> Self {
        Self {
            unique_count: 0,
            pool: StringPool::new(),
        }
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
}

impl TypeBuilder {
    pub fn new() -> Self {
        Self {
            pool: TypePool::new(),
        }
    }

    pub fn s(&mut self, t: &AstType) -> TypeId {
        self.pool.intern(t.clone())
    }

    pub fn r(&mut self, id: TypeId) -> &AstType {
        self.pool.resolve(&id)
    }
}

pub struct NodeBuilder {
    filename: String,
    current_node_id: u32,
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
        let ty = self.types.s(&ty);
        let b = compile_core::Builtin::new("check".into(), ty);
        self.builtins.insert(b);

        let ty = AstType::Func(vec![AstType::String], AstType::Unit.into());
        let ty = self.types.s(&ty);
        let b = compile_core::Builtin::new("use".into(), ty);
        self.builtins.insert(b);

        let ty = AstType::Func(
            vec![AstType::Sum(vec![AstType::Int, AstType::Float])],
            AstType::Unit.into(),
        );
        let ty = self.types.s(&ty);
        let b = compile_core::Builtin::new("print".into(), ty);
        self.builtins.insert(b);
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
        if let Some(b) = crate::builtin_from_name(name) {
            assert_eq!(b.arity(), args.len());
            let id = self.builtins.get_id(b);
            Some(Ast::Builtin(id, args).node(span_id))
        } else if let Some(ast) = ast_from_name(name, args, self) {
            Some(ast.node(span_id))
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

    pub fn unique_static_name(&mut self) -> String {
        let s = format!("__static_x{}", self.static_count);
        self.static_count += 1;
        s
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
                let ty = self.types.s(ty);
                ParameterNode {
                    name: *name,
                    ty,
                    node: Parameter::Normal,
                    span_id: SpanId::unknown(),
                }
            })
            .collect();

        let return_type = self.types.s(&return_type);
        Self::global(
            name,
            Ast::Definition(Definition {
                params,
                return_type,
                body: body.map(|b| b.into()),
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
        vec![
            self.definition(print_index, &[(a, AstType::Int)], AstType::Unit, None),
            self.definition(print_float, &[(a, AstType::Float)], AstType::Unit, None),
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

    pub fn seq(nodes: Vec<AstNode>) -> AstNode {
        // flatten nodes
        let nodes = nodes
            .into_iter()
            .map(|expr| expr.to_vec())
            .flatten()
            .collect();
        Ast::Sequence(nodes).into()
    }

    pub fn ident(name: StringKey) -> AstNode {
        Ast::Identifier(name).into()
    }

    pub fn global(name: StringKey, value: AstNode) -> AstNode {
        Ast::Global(name, value.into()).into()
    }

    pub fn while_loop(condition: AstNode, body: AstNode) -> AstNode {
        Ast::While(condition.into(), body.into()).into()
    }

    pub fn loop_break(key: Option<StringKey>) -> AstNode {
        Ast::Break(key, vec![]).into()
    }

    pub fn loop_continue(key: Option<StringKey>) -> AstNode {
        Ast::Continue(key, vec![]).into()
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

    pub fn apply(name: StringKey, args: Vec<Argument>, ty: TypeId) -> AstNode {
        let ident = Self::ident(name);
        Ast::Call(ident.into(), args, ty).into()
    }

    pub fn call(f: AstNode, args: Vec<Argument>, ty: TypeId) -> AstNode {
        Ast::Call(f.into(), args, ty).into()
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
        Ast::BlockStart(name, vec![]).into()
    }

    pub fn block_start(name: StringKey, params: Vec<ParameterNode>) -> AstNode {
        Ast::BlockStart(name, params).into()
    }

    pub fn goto(name: StringKey) -> AstNode {
        Ast::Goto(name).into()
    }

    pub fn param(&mut self, name: StringKey, ty: AstType) -> ParameterNode {
        let ty = self.types.s(&ty);
        ParameterNode {
            name,
            ty: ty.clone(),
            node: Parameter::Normal,
            span_id: SpanId::unknown(),
        }
    }

    pub fn module(name: StringKey, body: AstNode) -> AstNode {
        let span_id = body.span_id;
        AstNode {
            node: Ast::Module(name, body.into()),
            span_id,
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
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
        let main = b.main(NB::seq(vec![
            // entry
            NB::label(entry),
            NB::assign(yy, 1.into()),
            NB::alloca(y, 999.into()),
            NB::goto(asdf.into()),
            // asdf
            NB::label(asdf),
            NB::assign(yy, 2.into()),
            NB::goto(asdf2),
            // asdf2
            NB::label(asdf2),
            NB::assign(yy, 3.into()),
            NB::ret(Some(0.into())),
        ]));
        NB::seq(vec![b.import_prelude(), main])
    }

    pub fn gen_while<'c>(b: &mut NodeBuilder) -> AstNode {
        let mut seq = vec![b.import_prelude()];

        // global variable x = 10
        let x = b.labels.s("x").into();
        let x2 = b.labels.s("x2").into();
        let z = b.labels.s("z").into();
        let y = b.labels.s("y").into();
        let z_static = b.labels.s("z_static");

        seq.push(NB::global(z, 10.into()));
        seq.push(b.main(NB::seq(vec![
            // define local var
            // allocate mutable var
            NB::assign(x, 123.into()),
            NB::alloca(x2, 10.into()),
            NB::while_loop(
                NB::ne(NB::ident(x2.into()), 0.into()),
                NB::seq(vec![
                    // static variable with local scope
                    NB::global(z_static, 10.into()),
                    NB::assign(z_static, 10.into()),
                    // mutate global variable
                    NB::assign(z, NB::subtract(NB::ident(z.into()), 1.into())),
                    // mutate scoped variable
                    NB::assign(x2, NB::subtract(NB::ident(x2.into()), 1.into())),
                    NB::assign(z_static, NB::subtract(NB::ident(z_static.into()), 1.into())),
                    // assign local
                    NB::assign(
                        y,
                        NB::subtract(NB::ident(x.into()), NB::ident(z_static.into())),
                    ),
                ]),
            ),
            NB::ret(Some(NB::ident(z.into()))),
        ])));

        NB::seq(seq)
    }

    pub fn gen_function_call<'c>(b: &mut NodeBuilder) -> AstNode {
        let x = b.labels.s("x").into();
        let x1 = b.labels.s("x1").into();
        let z = b.labels.s("z").into();
        let y = b.labels.s("y").into();
        let arg0 = b.labels.s("arg0").into();
        let t_int = b.types.s(&AstType::Int);

        let mut seq = vec![b.import_prelude()];
        seq.push(NB::global(z, 10.into()));

        seq.push(b.func(
            x1,
            &[(arg0, AstType::Int)],
            AstType::Int,
            NB::seq(vec![
                // using an alloca
                NB::alloca(y, NB::ident(arg0.into())),
                NB::cond(
                    NB::ne(NB::ident(y.into()), 0.into()),
                    NB::seq(vec![
                        NB::assign(y, NB::subtract(NB::ident(y.into()), 1.into())),
                        NB::assign(
                            y,
                            NB::apply(x1.into(), vec![NB::ident(y.into()).into()], t_int),
                        ),
                    ]),
                    None,
                ),
                // using args
                NB::cond(
                    NB::ne(NB::ident(arg0.into()), 0.into()),
                    NB::seq(vec![NB::assign(
                        y,
                        NB::apply(
                            x1.into(),
                            vec![NB::subtract(NB::ident(arg0.into()), 1.into()).into()],
                            t_int,
                        ),
                    )]),
                    None,
                ),
                NB::ret(Some(NB::ident(y.into()))),
            ]),
        ));

        seq.push(b.main(NB::seq(vec![
            NB::assign(
                x,
                NB::apply(x1.into(), vec![AstNode::from(10).into()], t_int),
            ),
            NB::assign(
                x,
                NB::apply(x1.into(), vec![AstNode::from(0).into()], t_int),
            ),
            NB::ret(Some(NB::ident(x.into()))),
        ])));
        NB::seq(seq)
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
        let key = b.labels.s(&s);
        Some(Ast::Goto(key.into()))
    } else if name == "static" {
        println!("args: {:?}", args);
        let Argument::Positional(value) = args.pop().unwrap();
        let Argument::Positional(name_node) = args.pop().unwrap();
        let name = b.labels.s(&name_node.try_string().unwrap());
        Some(Ast::global(name, *value))
    } else if name == "label" {
        let rest = args.split_off(1);
        let s = args.pop().unwrap().try_string().unwrap();
        let key = b.labels.s(&s);

        let mut params = vec![];
        for arg in rest {
            let Argument::Positional(node) = arg;
            let name = node.try_string().unwrap();
            let key = b.labels.s(&name);
            let ty = b.types.s(&AstType::Unit);
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
