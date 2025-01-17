use crate::{Abstraction, AbstractionId, NodeBuilder};
use compile_core::{
    Argument, Ast, AstFuncType, AstNode, AstType, ControlFlowMarker, InternKey, InternPool,
    InternValue, Lambda, Literal, ReturnType, SpanId, StringKey,
};
use std::collections::{HashMap, VecDeque};
#[derive(Debug, Clone, Copy)]
pub struct BuiltinId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Builtin {
    Assert,
    Print,
    Import,
}

impl Builtin {
    pub fn lookup(name: &str) -> Option<Self> {
        match name {
            "check" => Some(Builtin::Assert),
            "print" => Some(Builtin::Print),
            "use" => Some(Builtin::Import),
            _ => None,
        }
    }
}

impl InternValue for Builtin {}

impl InternKey for BuiltinId {
    fn index(&self) -> usize {
        self.0 as usize
    }
    fn new(index: usize) -> Self {
        Self(index as u32)
    }
}

pub type BuiltinPool = InternPool<BuiltinId, Builtin>;

fn get_string_arg(args: &[Argument], b: &mut NodeBuilder) -> Option<StringKey> {
    if args.len() == 0 {
        None
    } else {
        let arg = args.get(0).unwrap().get_expr();
        match &arg.node {
            Ast::Literal(Literal::String(s)) => Some(b.labels.s(&s)),
            Ast::Identifier(key) => Some(*key),
            _ => unimplemented!(),
        }
    }
}

pub fn builtin_from_name(
    name: &str,
    mut args: Vec<Argument>,
    span_id: SpanId,
    b: &mut NodeBuilder,
) -> Option<AstNode> {
    match name {
        "loop" => Some(ControlFlowMarker::LoopStart(get_string_arg(&args, b)).node(span_id)),
        "loop_break" => Some(ControlFlowMarker::LoopBreak(get_string_arg(&args, b)).node(span_id)),
        "loop_continue" => {
            Some(ControlFlowMarker::LoopContinue(get_string_arg(&args, b)).node(span_id))
        }
        "end" => {
            assert_eq!(args.len(), 0);
            Some(Ast::CloseBlock.node(span_id))
        }
        "goto" => {
            let rem = args.split_off(1);
            Some(ControlFlowMarker::Goto(get_string_arg(&args, b).unwrap(), rem).node(span_id))
        }
        "goto_chain" => Some(ControlFlowMarker::GotoChain(args).node(span_id)),
        "label" => {
            let _rem = args.split_off(1);
            Some(ControlFlowMarker::BlockStart(get_string_arg(&args, b), vec![]).node(span_id))
        }

        "resolve_label" => {
            let node = args.pop().unwrap().expr();
            Some(ControlFlowMarker::BlockReference(node.into()).node(span_id))
        }

        "array" => {
            let mut args = args.iter().collect::<VecDeque<_>>();
            let ty_node = args.pop_front().unwrap().get_expr();
            b.dump_ast(ty_node);
            let type_id = match &ty_node.node {
                Ast::Type(type_id) => *type_id,
                Ast::Identifier(key) => {
                    let s = b.labels.r(key.into());
                    if let Some(ty) = AstType::from_str(&s) {
                        b.types.s(&ty)
                    } else {
                        unimplemented!("{}", &s)
                    }
                }
                _ => unimplemented!("{:?}", ty_node),
            };
            let dims = args
                .into_iter()
                .map(|arg| {
                    let value = arg.get_expr();
                    let i = match &value.node {
                        Ast::Literal(Literal::Int(x)) => *x as u64,
                        Ast::Literal(Literal::Index(x)) => *x as u64,
                        _ => unimplemented!(),
                    };
                    Ast::Literal(Literal::Index(i as usize)).node(value.span_id)
                })
                .collect::<Vec<_>>();
            Some(Ast::Array(type_id, dims).into())
        }
        "static" => {
            println!("args: {:?}", args);
            let name_node = args.get(0).unwrap().get_expr();
            let value = args.get(1).unwrap().get_expr().clone();
            let name = b.labels.s(&name_node.try_string().unwrap());
            Some(Ast::global(name, value).node(span_id))
        }
        "ternary" => {
            let condition = args.get(0).unwrap().get_expr();
            let then_expr = args.get(1).unwrap().get_expr();
            let else_expr = args.get(2).unwrap().get_expr();
            Some(
                Ast::Ternary(
                    condition.clone().into(),
                    then_expr.clone().into(),
                    else_expr.clone().into(),
                )
                .node(span_id),
            )
        }

        "defer" => {
            let expr = args.pop().unwrap().expr();
            Some(Ast::Defer(expr.clone().into()).node(span_id))
        }

        "check" | "print" | "use" => {
            let bb = match name {
                "check" => Builtin::Assert,
                "print" => Builtin::Print,
                "use" => Builtin::Import,
                _ => unimplemented!("builtin not found: {}", name),
            };
            let key = b.labels.s(name);
            let arity = bb.arity();
            if arity != args.len() {
                b.push_error(
                    &format!("Builtin Call arity mismatch: {}<=>{}", arity, args.len()),
                    span_id,
                );
            }
            Some(Ast::Builtin(key, args.to_vec()).node(span_id))
        }
        _ => None,
    }
}

impl Builtin {
    pub fn arity(&self) -> usize {
        match self {
            Self::Assert => 1,
            Self::Print => 1,
            Self::Import => 1,
        }
    }

    pub fn name(&self) -> String {
        match self {
            Self::Assert => "check".into(),
            Self::Print => "print".into(),
            Self::Import => "use".into(),
        }
    }

    pub fn get_return_type(&self) -> AstType {
        AstType::Unit
    }

    pub fn get_lambda(&self, b: &mut NodeBuilder) -> Lambda {
        let key = b.labels.s("a");
        let unknown = b.types.fresh_unknown();
        let arg_type = AstType::Struct(vec![(Some(key), unknown)]);
        let func_ty =
            AstFuncType::new(arg_type.clone(), ReturnType::Single(self.get_return_type()));
        let def = Lambda {
            func_type: func_ty.clone(),
            body: None,
            defaults: HashMap::new(),
        };
        def
    }

    pub fn make_abstraction(&self, b: &mut NodeBuilder) -> Abstraction {
        let name = b.labels.s(&self.name());
        Abstraction {
            def: self.get_lambda(b),
            def_span_id: b.spans.get_span_unknown(),
            name,
        }
    }
}

pub struct BuiltinBuilder {
    pub pool: BuiltinPool,
    lookup: HashMap<String, BuiltinId>,
    abstractions: HashMap<Builtin, AbstractionId>,
}

impl BuiltinBuilder {
    pub fn new() -> Self {
        Self {
            pool: BuiltinPool::new(),
            lookup: HashMap::new(),
            abstractions: HashMap::new(),
        }
    }

    pub fn add_abstraction(&mut self, b: Builtin, abstraction_id: AbstractionId) {
        self.abstractions.insert(b, abstraction_id);
    }

    pub fn get_abstraction(&self, b: Builtin) -> AbstractionId {
        *self.abstractions.get(&b).unwrap()
    }

    pub fn get_id(&self, b: Builtin) -> BuiltinId {
        let name = match b {
            Builtin::Assert => "check",
            Builtin::Print => "print",
            Builtin::Import => "use",
        };
        self.lookup.get(name).unwrap().clone()
    }
}
