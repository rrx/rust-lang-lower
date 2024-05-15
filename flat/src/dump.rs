use crate::NodeBuilder;
use compile_core::{Argument, AssignTarget, Ast, AstNode, ControlFlowMarker, SpanId};

pub fn print_with_indent(s: &str, depth: usize) {
    println!("{:width$}{}", "", s, width = depth * 2);
}

impl NodeBuilder {
    pub fn dump_ast(&self, node: &AstNode) {
        let mut out = vec![];
        self.dump_strings(node, &mut out, 0);
        for (depth, s, _span) in out {
            print_with_indent(&s, depth);
        }
    }

    pub fn dump_strings(
        &self,
        node: &AstNode,
        out: &mut Vec<(usize, String, SpanId)>,
        mut depth: usize,
    ) {
        match &node.node {
            Ast::Module(name, body) => {
                let s = format!("module({})", self.labels.r((*name).into()));
                out.push((depth, s, node.span_id));
                depth += 1;
                self.dump_strings(body, out, depth);
            }

            Ast::Block(name, _args, body) => {
                let s = format!("block({})", self.labels.r((*name).into()));
                out.push((depth, s, node.span_id));
                depth += 1;
                self.dump_strings(body, out, depth);
            }

            Ast::Sequence(exprs) => {
                for expr in exprs {
                    self.dump_strings(expr, out, depth);
                }
            }

            Ast::Return(maybe_result) => {
                let s = format!("ret:");
                out.push((depth, s, node.span_id));
                if let Some(result) = maybe_result {
                    self.dump_strings(result, out, depth + 1);
                }
            }

            Ast::Builtin(bi, args) => {
                let s = format!("builtin({:?})", bi);
                out.push((depth, s, node.span_id));
                for a in args {
                    let Argument::Positional(expr) = a;
                    self.dump_strings(expr, out, depth + 1);
                }
            }

            Ast::Literal(lit) => {
                let s = format!("{:?}", lit);
                out.push((depth, s, node.span_id));
            }

            Ast::ControlFlowMarker(ControlFlowMarker::BlockStart(name, params)) => {
                let s = format!("block_start: {}", self.labels.r((*name).into()),);
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

            Ast::Lambda(def) => {
                //let s = format!("func({}):", b.r(def.name));
                let s = "func:";
                out.push((depth, s.into(), node.span_id));
                depth += 1;

                for a in &def.params {
                    let s = format!("arg: {}: {:?}", self.labels.r(a.name.into()), a.ty,);
                    out.push((depth, s, node.span_id));
                }
                if let Some(ref body) = def.body {
                    self.dump_strings(body, out, depth);
                }
            }

            Ast::Global(key, value) => {
                let s = format!("global: {}", self.labels.r(key.into()));
                out.push((depth, s, node.span_id));
                self.dump_strings(value, out, depth + 1);
            }

            Ast::Assign(target, value) => {
                let s = format!("assign");
                out.push((depth, s, node.span_id));
                depth += 1;
                match target {
                    AssignTarget::Identifier(key) => {
                        let s = format!("target identifier: {}", self.labels.r(key.into()),);
                        out.push((depth, s, node.span_id));
                    }
                    AssignTarget::Alloca(key) => {
                        let s = format!("target alloca: {}", self.labels.r(key.into()),);
                        out.push((depth, s, node.span_id));
                    }
                }
                self.dump_strings(value, out, depth);
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
                let s = format!("ident: {}", self.labels.r(key.into()),);
                out.push((depth, s, node.span_id));
            }

            Ast::Conditional(c, a, mb) => {
                let s = format!("cond:");
                out.push((depth, s, node.span_id));
                depth += 1;
                self.dump_strings(c, out, depth);
                let s = format!("then:");
                out.push((depth, s, node.span_id));
                self.dump_strings(a, out, depth + 1);
                if let Some(else_expr) = mb {
                    let s = format!("else:");
                    out.push((depth, s, node.span_id));
                    self.dump_strings(else_expr, out, depth + 1);
                }
            }

            Ast::Ternary(c, then_expr, else_expr) => {
                let s = format!("ternary:");
                out.push((depth, s, node.span_id));
                depth += 1;
                self.dump_strings(c, out, depth);
                let s = format!("then:");
                out.push((depth, s, node.span_id));
                self.dump_strings(then_expr, out, depth + 1);
                let s = format!("else:");
                out.push((depth, s, node.span_id));
                self.dump_strings(else_expr, out, depth + 1);
            }

            Ast::Branch(c, then_key, else_key) => {
                let s = format!(
                    "branch: {}, {}",
                    self.labels.r(then_key.into()),
                    self.labels.r(else_key.into()),
                );
                out.push((depth, s, node.span_id));
                self.dump_strings(c, out, depth + 1);
            }

            Ast::Call(f, args, ret_ty) => {
                let s = format!("call: {:?}", ret_ty);
                out.push((depth, s, node.span_id));
                self.dump_strings(f, out, depth + 1);
                if args.len() > 0 {
                    for a in args {
                        let Argument::Positional(expr) = a;
                        self.dump_strings(expr, out, depth + 1);
                    }
                }
            }

            Ast::Loop(key, body) => {
                let s = format!("loop({})", self.labels.r(key.into()));
                out.push((depth, s, node.span_id));
                self.dump_strings(body, out, depth + 1);
            }

            Ast::Break(maybe_key, args) => {
                let s = format!(
                    "break({})",
                    maybe_key
                        .map(|key| self.labels.r(key.into()))
                        .or(Some("".into()))
                        .unwrap()
                );
                out.push((depth, s, node.span_id));
                for expr in args {
                    self.dump_strings(expr, out, depth + 1);
                }
            }

            Ast::Continue(maybe_key, args) => {
                let s = format!(
                    "continue({})",
                    maybe_key
                        .map(|key| self.labels.r(key.into()))
                        .or(Some("".into()))
                        .unwrap()
                );
                out.push((depth, s, node.span_id));
                for expr in args {
                    self.dump_strings(expr, out, depth + 1);
                }
            }

            _ => unimplemented!("{:?}", node),
        }
    }
}
