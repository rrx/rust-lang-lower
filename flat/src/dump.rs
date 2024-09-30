use crate::NodeBuilder;
use compile_core::{Argument, AssignTarget, Ast, AstNode, ControlFlowMarker, Literal, SpanId};

pub fn print_with_indent(s: &str, span_id: SpanId, depth: usize) {
    println!("{:width$}{}, {}", "", s, span_id, width = depth * 2);
}

impl NodeBuilder {
    pub fn dump_ast(&self, node: &AstNode) {
        let mut out = vec![];
        self.dump_strings(node, &mut out, 0);
        for (depth, s, span_id) in out {
            print_with_indent(&s, span_id, depth);
        }
    }

    /*
    pub fn format_type(&self, ty: &AstType) -> String {
        if match
        let mut out = vec![];
        self.dump_strings(node, &mut out, 0);
        for (depth, s, span_id) in out {
            print_with_indent(&s, span_id, depth);
        }
    }
    */

    pub fn dump_argument(
        &self,
        index: usize,
        a: &Argument,
        out: &mut Vec<(usize, String, SpanId)>,
        depth: usize,
    ) {
        let (s, expr, span_id) = match a {
            Argument::Positional(expr) => {
                (format!("arg({})", index), vec![*expr.clone()], expr.span_id)
            }
            Argument::Named(key, expr) => {
                let name = self.labels.r((*key).into());
                (
                    format!("arg({},{})", index, name),
                    vec![*expr.clone()],
                    expr.span_id,
                )
            }
            Argument::Args(key, seq) => {
                let name = self.labels.r((*key).into());
                let span_id = if seq.len() == 0 {
                    SpanId::new(0)
                } else {
                    seq.first().unwrap().span_id
                };
                (
                    format!("*args({},{})", index, name),
                    (*seq).clone(),
                    span_id,
                ) //Box::new(Ast::Sequence(seq.clone()).into()))
            }
            Argument::KwArgs(key, seq) => {
                let name = self.labels.r((*key).into());
                let seq = seq.values().cloned().collect::<Vec<_>>();
                let span_id = if seq.len() == 0 {
                    SpanId::new(0)
                } else {
                    seq.first().unwrap().span_id
                };
                (format!("**kwargs({},{})", index, name), seq, span_id)
            }
        };
        out.push((depth, s, span_id));
        for x in expr {
            self.dump_strings(&x, out, depth + 1);
        }
    }

    fn dump_strings(&self, node: &AstNode, out: &mut Vec<(usize, String, SpanId)>, depth: usize) {
        let span_id = node.span_id;
        match &node.node {
            Ast::Module(name, body) => {
                let s = format!("module({},{})", self.labels.r((*name).into()), span_id);
                out.push((depth, s, node.span_id));
                self.dump_strings(body, out, depth + 1);
            }

            Ast::Block(name, _args, body) => {
                let s = format!("block({},{})", self.labels.r((*name).into()), span_id);
                out.push((depth, s, node.span_id));
                self.dump_strings(body, out, depth + 1);
            }

            Ast::Sequence(exprs) => {
                let _s = format!("sequence({})", span_id);
                for expr in exprs {
                    self.dump_strings(expr, out, depth + 1);
                }
            }

            Ast::Return(maybe_result) => {
                let s = format!("ret({}):", span_id);
                out.push((depth, s, node.span_id));
                if let Some(result) = maybe_result {
                    self.dump_strings(result, out, depth + 1);
                }
            }

            Ast::Builtin(bi, args) => {
                let bb = self.builtins.pool.resolve(bi);
                let s = format!("builtin({})", bb.name);
                out.push((depth, s, node.span_id));
                for (index, a) in args.iter().enumerate() {
                    self.dump_argument(index, a, out, depth + 1);
                }
            }

            Ast::Literal(Literal::String(s)) => {
                let s = format!("{}", s);
                out.push((depth, s, node.span_id));
            }

            Ast::Literal(lit) => {
                let s = format!("({:?})", lit);
                out.push((depth, s, node.span_id));
            }

            Ast::ControlFlowMarker(ControlFlowMarker::LoopStart(name)) => {
                let s = if let Some(name) = name {
                    format!("loop_start({},{}):", self.labels.r((*name).into()), span_id)
                } else {
                    "loop_start".into()
                };
                out.push((depth, s, node.span_id));
            }

            Ast::ControlFlowMarker(ControlFlowMarker::BlockStart(name, params)) => {
                let s = if let Some(name) = name {
                    format!(
                        "block_start({},{}):",
                        self.labels.r((*name).into()),
                        span_id
                    )
                } else {
                    format!("block_start({}):", span_id)
                };
                out.push((depth, s, node.span_id));
                for e in params {
                    let s = format!("arg: {}, {:?}", self.labels.r(e.name.into()), e.ty,);
                    out.push((depth, s, node.span_id));
                }
            }

            Ast::ControlFlowMarker(ControlFlowMarker::Goto(key)) => {
                let s = format!("goto: {}", self.labels.r(key.into()),);
                out.push((depth, s, node.span_id));
            }

            Ast::ControlFlowMarker(ControlFlowMarker::BlockEnd) => {
                let s = format!("end({})", node.span_id);
                out.push((depth, s, node.span_id));
            }

            Ast::Lambda(def) => {
                //let s = format!("func({}):", b.r(def.name));
                let s = format!("func:");
                out.push((depth, s.into(), node.span_id));

                let arg_type = self.types.r(def.arg_type);
                for (i, (maybe_key, ty)) in arg_type.fields().iter().enumerate() {
                    let name = if let Some(key) = maybe_key {
                        self.labels.r(key.into())
                    } else {
                        format!("{}", i)
                    };

                    let s = format!("arg: {}: {:?}", name, ty);
                    out.push((depth + 2, s, node.span_id));
                }
                if let Some(ref body) = def.body {
                    self.dump_strings(body, out, depth + 1);
                }
            }

            Ast::Global(key, value) => {
                let s = format!("global: {}, {}", self.labels.r(key.into()), node.span_id);
                out.push((depth, s, node.span_id));
                self.dump_strings(value, out, depth + 1);
            }

            Ast::Assign(target, value) => {
                let s = format!("assign:");
                out.push((depth, s, node.span_id));
                match target {
                    AssignTarget::Identifier(key) => {
                        let s = format!("target identifier: {}", self.labels.r(key.into()),);
                        out.push((depth + 1, s, node.span_id));
                    }
                    AssignTarget::Alloca(key) => {
                        let s = format!("target alloca: {}", self.labels.r(key.into()),);
                        out.push((depth + 1, s, node.span_id));
                    }
                }
                self.dump_strings(value, out, depth + 1);
            }

            Ast::BinaryOp(op, x, y) => {
                let s = format!("binop: {:?}", op);
                out.push((depth, s, node.span_id));
                self.dump_strings(x, out, depth + 1);
                self.dump_strings(y, out, depth + 1);
            }

            Ast::UnaryOp(op, expr) => {
                let s = format!("unary: {:?}", op);
                out.push((depth, s, node.span_id));
                self.dump_strings(expr, out, depth + 1);
            }

            Ast::Identifier(key) => {
                let s = format!("ident: {}", self.labels.r(key.into()));
                out.push((depth, s, node.span_id));
            }

            Ast::Conditional(c, a, mb) => {
                let s = format!("cond({}):", node.span_id);
                out.push((depth, s, node.span_id));
                self.dump_strings(c, out, depth + 1);
                let s = format!("then:");
                out.push((depth + 1, s, node.span_id));
                self.dump_strings(a, out, depth + 2);
                if let Some(else_expr) = mb {
                    let s = format!("else:");
                    out.push((depth, s, node.span_id));
                    self.dump_strings(else_expr, out, depth + 2);
                }
            }

            Ast::Ternary(c, then_expr, else_expr) => {
                let s = format!("ternary({}):", node.span_id);
                out.push((depth, s, node.span_id));
                self.dump_strings(c, out, depth + 1);
                let s = format!("then:");
                out.push((depth + 1, s, node.span_id));
                self.dump_strings(then_expr, out, depth + 2);
                let s = format!("else:");
                out.push((depth + 1, s, node.span_id));
                self.dump_strings(else_expr, out, depth + 2);
            }

            Ast::Branch(c, then_key, else_key) => {
                let s = format!(
                    "branch({},{},{})",
                    self.labels.r(then_key.into()),
                    self.labels.r(else_key.into()),
                    node.span_id
                );
                out.push((depth, s, node.span_id));
                self.dump_strings(c, out, depth + 1);
            }

            Ast::Call(f, args) => {
                let s = format!("call:");
                out.push((depth, s, node.span_id));
                self.dump_strings(f, out, depth + 1);
                if args.len() > 0 {
                    for (pos, a) in args.iter().enumerate() {
                        self.dump_argument(pos, a, out, depth + 2);
                    }
                }
            }

            Ast::Loop(key, body) => {
                let s = format!("loop({},{})", self.labels.r(key.into()), node.span_id);
                out.push((depth, s, node.span_id));
                self.dump_strings(body, out, depth + 1);
            }

            Ast::ControlFlowMarker(ControlFlowMarker::LoopBreak(maybe_key)) => {
                let s = format!(
                    "loop_break({},{})",
                    maybe_key
                        .map(|key| self.labels.r(key.into()))
                        .or(Some("".into()))
                        .unwrap(),
                    node.span_id,
                );
                out.push((depth, s, node.span_id));
            }

            Ast::ControlFlowMarker(ControlFlowMarker::LoopContinue(maybe_key)) => {
                let s = format!(
                    "loop_continue({},{})",
                    maybe_key
                        .map(|key| self.labels.r(key.into()))
                        .or(Some("".into()))
                        .unwrap(),
                    node.span_id,
                );
                out.push((depth, s, node.span_id));
            }
            Ast::Break(maybe_key, args) => {
                let s = format!(
                    "break({},{})",
                    maybe_key
                        .map(|key| self.labels.r(key.into()))
                        .or(Some("".into()))
                        .unwrap(),
                    node.span_id,
                );
                out.push((depth, s, node.span_id));
                for expr in args {
                    self.dump_strings(expr, out, depth + 1);
                }
            }

            Ast::Continue(maybe_key, args) => {
                let s = format!(
                    "continue({},{})",
                    maybe_key
                        .map(|key| self.labels.r(key.into()))
                        .or(Some("".into()))
                        .unwrap(),
                    node.span_id
                );
                out.push((depth, s, node.span_id));
                for expr in args {
                    self.dump_strings(expr, out, depth + 1);
                }
            }

            Ast::CloseBlock => {
                let s = format!("close_block({})", node.span_id);
                out.push((depth, s.into(), node.span_id));
            }

            Ast::Yield(body) => {
                let s = format!("yield({})", node.span_id);
                out.push((depth, s, node.span_id));
                if let Some(result) = body {
                    self.dump_strings(result, out, depth + 1);
                }
            }

            Ast::Error => {
                let s = format!("error");
                out.push((depth, s.into(), node.span_id));
            }

            Ast::Array(type_id, dims) => {
                let ty = self.types.r(*type_id);
                let s = format!("array({}, {:?})", ty, dims);
                out.push((depth, s, node.span_id));
            }

            Ast::Tuple(exprs) => {
                let s = format!("tuple:");
                out.push((depth, s, node.span_id));
                for e in exprs {
                    self.dump_strings(e, out, depth + 1);
                }
            }

            Ast::Attribute(key, body) => {
                let s = self.labels.r(key.into());
                let s = format!("attr({})", s);
                out.push((depth, s, node.span_id));
                self.dump_strings(body, out, depth + 1);
            }

            Ast::Index(body, index) => {
                let s = format!("index");
                out.push((depth, s, node.span_id));
                self.dump_strings(body, out, depth + 1);
                self.dump_strings(index, out, depth + 1);
            }

            Ast::Import(module_name, mapping) => {
                let name = self.labels.r(module_name.into());
                let s = format!("import({})", name);
                out.push((depth, s, node.span_id));
                for (k, v) in mapping.iter() {
                    let k = self.labels.r(k.into());
                    let v = self.labels.r(v.into());
                    let s = format!("{}=>{}", k, v);
                    out.push((depth + 1, s, node.span_id));
                }
            }

            _ => unimplemented!("{:?}", node),
        }
    }
}
