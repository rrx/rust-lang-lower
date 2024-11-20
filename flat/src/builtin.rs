use crate::NodeBuilder;
use compile_core::{
    Argument, Ast, AstNode, AstType, BuiltinId, BuiltinPool, ControlFlowMarker, Lambda, Literal,
    ReturnType, SpanId, StringKey,
};
use std::collections::{HashMap, VecDeque};

#[derive(Debug, Clone)]
pub enum Builtin {
    Assert,
    Print,
    Import,
}

fn get_string_arg(args: &[Argument], b: &mut NodeBuilder) -> Option<StringKey> {
    if args.len() == 0 {
        None
    } else if args.len() == 1 {
        let arg = args.get(0).unwrap().get_expr();
        match &arg.node {
            Ast::Literal(Literal::String(s)) => Some(b.labels.s(&s)),
            Ast::Identifier(key) => Some(*key),
            _ => unimplemented!(),
        }
    } else {
        unreachable!()
    }
}

pub fn builtin_from_name(
    name: &str,
    args: &[Argument],
    span_id: SpanId,
    b: &mut NodeBuilder,
) -> Option<AstNode> {
    match name {
        "loop" => Some(ControlFlowMarker::LoopStart(get_string_arg(args, b)).node(span_id)),
        "loop_break" => Some(ControlFlowMarker::LoopBreak(get_string_arg(args, b)).node(span_id)),
        "loop_continue" => {
            Some(ControlFlowMarker::LoopContinue(get_string_arg(args, b)).node(span_id))
        }
        "end" => {
            assert_eq!(args.len(), 0);
            Some(Ast::CloseBlock.node(span_id))
        }
        "goto" => Some(ControlFlowMarker::Goto(get_string_arg(args, b).unwrap()).node(span_id)),
        "label" => {
            Some(ControlFlowMarker::BlockStart(get_string_arg(args, b), vec![]).node(span_id))
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

        "check" | "print" | "use" => {
            let bb = match name {
                "check" => Builtin::Assert,
                "print" => Builtin::Print,
                "use" => Builtin::Import,
                _ => unimplemented!("builtin not found: {}", name),
            };
            let arity = bb.arity();
            if arity != args.len() {
                b.push_error(
                    &format!("Builtin Call arity mismatch: {}<=>{}", arity, args.len()),
                    span_id,
                );
            }
            Some(Ast::Builtin(b.builtins.get_id(bb), args.to_vec()).node(span_id))
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

    pub fn get_return_type(&self) -> AstType {
        AstType::Unit
        //AstType::Struct(vec![])
    }

    pub fn get_lambda(&self, b: &mut NodeBuilder) -> Lambda {
        let ret_type_id = b.types.s(&self.get_return_type());
        let key = b.labels.s("a");
        let unknown = b.types.fresh_unknown();
        let arg_type = AstType::Struct(vec![(Some(key), unknown)]);
        let func_ty = AstType::Func(
            arg_type.clone().into(),
            ReturnType::Single(self.get_return_type()).into(),
        );
        let def = Lambda {
            fun_type: b.types.s(&func_ty),
            arg_type: b.types.s(&arg_type),
            return_type: ret_type_id,
            body: None,
            defaults: HashMap::new(),
        };
        def
    }
}

pub struct BuiltinBuilder {
    pub pool: BuiltinPool,
    lookup: HashMap<String, BuiltinId>,
}

impl BuiltinBuilder {
    pub fn new() -> Self {
        let mut s = Self {
            pool: BuiltinPool::new(),
            lookup: HashMap::new(),
        };
        let b = compile_core::Builtin::new("check".into());
        s.insert(b);
        let b = compile_core::Builtin::new("use".into());
        s.insert(b);
        let b = compile_core::Builtin::new("print".into());
        s.insert(b);
        s
    }

    pub fn insert(&mut self, bi: compile_core::Builtin) {
        let name = bi.name.clone();
        let id = self.pool.intern(bi);
        self.lookup.insert(name, id);
    }

    pub fn get_enum(&self, id: BuiltinId) -> Builtin {
        let b = self.pool.resolve(&id);
        match b.name.as_str() {
            "check" => Builtin::Assert,
            "print" => Builtin::Print,
            "use" => Builtin::Import,
            _ => unimplemented!("{}", &b.name),
        }
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
