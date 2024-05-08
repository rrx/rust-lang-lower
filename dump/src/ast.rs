use compile_core::{Argument, AssignTarget, Ast, AstNode, Span, SpanId};

use flat::NodeBuilder;

pub fn dump(node: &AstNode, b: &NodeBuilder) {
    let mut out = vec![];
    dump_strings(node, b, &mut out, 0);
    for (depth, s, _span) in out {
        print_with_indent(&s, depth);
    }
}

pub fn print_with_indent(s: &str, depth: usize) {
    println!("{:width$}{}", "", s, width = depth * 2);
}

pub fn dump_html(node: &AstNode, b: &NodeBuilder) -> String {
    let mut out = vec![];
    dump_strings(node, b, &mut out, 0);
    let mut s = String::new();
    s.push_str("<pre>\n");
    for (depth, content, span_id) in out {
        let span = b.spans.lookup(span_id);
        if let Span::Loc(span) = span {
            s.push_str(&format!(
                "{:width$}<span span_id=\"{}\" class=\"s{}\" begin=\"{}\" end=\"{}\">{}</span>\n",
                "",
                span_id.index(),
                span_id.index(),
                span.begin.pos,
                span.end.pos,
                content,
                width = depth * 2
            ));
        } else {
            s.push_str(&format!(
                "{:width$}<span span_id=\"{}\" class=\"s{}\" begin=\"{}\" end=\"{}\">{}</span>\n",
                "",
                span_id.index(),
                span_id.index(),
                0,
                0,
                content,
                width = depth * 2
            ));
        }
    }
    s.push_str("</pre>\n");
    s
}

pub fn dump_strings(
    node: &AstNode,
    b: &NodeBuilder,
    out: &mut Vec<(usize, String, SpanId)>,
    mut depth: usize,
) {
    match &node.node {
        Ast::Module(name, body) => {
            let s = format!("module({})", b.r(*name));
            out.push((depth, s, node.span_id));
            depth += 1;
            dump_strings(body, b, out, depth);
        }

        Ast::Sequence(exprs) => {
            for expr in exprs {
                dump_strings(expr, b, out, depth);
            }
        }

        Ast::Return(maybe_result) => {
            let s = format!("ret:");
            out.push((depth, s, node.span_id));
            if let Some(result) = maybe_result {
                dump_strings(result, b, out, depth + 1);
            }
        }

        Ast::Builtin(bi, args) => {
            let s = format!("builtin({:?})", bi);
            out.push((depth, s, node.span_id));
            for a in args {
                let Argument::Positional(expr) = a;
                dump_strings(expr, b, out, depth + 1);
            }
        }

        Ast::Literal(lit) => {
            let s = format!("{:?}", lit);
            out.push((depth, s, node.span_id));
        }

        Ast::BlockStart(name, params) => {
            let s = format!("block_start: {}", b.r(*name),);
            out.push((depth, s, node.span_id));
            for e in params {
                let s = format!("arg: {}, {:?}", b.resolve_label(e.name.into()), e.ty,);
                out.push((depth, s, node.span_id));
            }
        }

        //Ast::Label(name) => {
        //let s = format!("label: {}", b.r(*name));
        //out.push((depth, s, self.span_id));
        //}
        Ast::Goto(key) => {
            let s = format!("goto: {}", b.r(*key),);
            out.push((depth, s, node.span_id));
        }

        Ast::Definition(def) => {
            //let s = format!("func({}):", b.r(def.name));
            let s = "func:";
            out.push((depth, s.into(), node.span_id));
            depth += 1;

            for a in &def.params {
                let s = format!("arg: {}: {:?}", b.resolve_label(a.name.into()), a.ty,);
                out.push((depth, s, node.span_id));
            }
            if let Some(ref body) = def.body {
                dump_strings(body, b, out, depth);
            }
        }

        /*
        Ast::Block(block) => {
            let s = format!("block({})", b.resolve_block_label(block.name),);
            out.push((depth, s, self.span_id));
            depth += 1;
            for a in &block.params {
                let s = format!("arg: {}: {:?}", b.resolve_label(a.name.into()), a.ty,);
                out.push((depth, s, self.span_id));
            }
            for a in &block.children {
                a.dump_strings(b, out, depth);
            }
        }
        */
        Ast::Global(key, value) => {
            let s = format!("global: {}", b.r(*key));
            out.push((depth, s, node.span_id));
            dump_strings(value, b, out, depth + 1);
        }

        Ast::Assign(target, value) => {
            let s = format!("assign");
            out.push((depth, s, node.span_id));
            depth += 1;
            match target {
                AssignTarget::Identifier(key) => {
                    let s = format!("target identifier: {}", b.resolve_label(key.into()),);
                    out.push((depth, s, node.span_id));
                }
                AssignTarget::Alloca(key) => {
                    let s = format!("target alloca: {}", b.resolve_label(key.into()),);
                    out.push((depth, s, node.span_id));
                }
            }
            dump_strings(value, b, out, depth);
        }

        Ast::BinaryOp(op, x, y) => {
            let s = format!("binop: {:?}", op);
            out.push((depth, s, node.span_id));
            dump_strings(x, b, out, depth + 1);
            dump_strings(y, b, out, depth + 1);
        }

        Ast::UnaryOp(op, expr) => {
            let s = format!("unary: {:?}", op);
            out.push((depth, s, node.span_id));
            dump_strings(expr, b, out, depth + 1);
        }

        Ast::Identifier(key) => {
            let s = format!("ident: {}", b.resolve_label(key.into()),);
            out.push((depth, s, node.span_id));
        }

        Ast::Conditional(c, a, mb) => {
            let s = format!("cond:");
            out.push((depth, s, node.span_id));
            depth += 1;
            dump_strings(c, b, out, depth);
            let s = format!("then:");
            out.push((depth, s, node.span_id));
            dump_strings(a, b, out, depth + 1);
            if let Some(else_expr) = mb {
                let s = format!("else:");
                out.push((depth, s, node.span_id));
                dump_strings(else_expr, b, out, depth + 1);
            }
        }

        Ast::Ternary(c, then_expr, else_expr) => {
            let s = format!("ternary:");
            out.push((depth, s, node.span_id));
            depth += 1;
            dump_strings(c, b, out, depth);
            let s = format!("then:");
            out.push((depth, s, node.span_id));
            dump_strings(then_expr, b, out, depth + 1);
            let s = format!("else:");
            out.push((depth, s, node.span_id));
            dump_strings(else_expr, b, out, depth + 1);
        }

        Ast::Branch(c, then_key, else_key) => {
            let s = format!("branch: {}, {}", b.r(*then_key), b.r(*else_key),);
            out.push((depth, s, node.span_id));
            dump_strings(c, b, out, depth + 1);
        }

        Ast::Call(f, args, ret_ty) => {
            let s = format!("call: {:?}", ret_ty);
            out.push((depth, s, node.span_id));
            dump_strings(f, b, out, depth + 1);
            if args.len() > 0 {
                for a in args {
                    let Argument::Positional(expr) = a;
                    dump_strings(expr, b, out, depth + 1);
                }
            }
        }

        //Ast::Deref(a, _) => a.dump_strings(b, out, depth),
        /*
        Ast::Mutate(lhs, rhs) => {
            let s = format!("mutate");
            out.push((depth, s, self.span_id));
            lhs.dump_strings(b, out, depth + 1);
            rhs.dump_strings(b, out, depth + 1);
        }
        */
        Ast::Loop(key, body) => {
            let s = format!("loop({})", b.r(*key));
            out.push((depth, s, node.span_id));
            dump_strings(body, b, out, depth + 1);
        }

        Ast::Break(maybe_key, args) => {
            let s = format!(
                "break({})",
                maybe_key.map(|key| b.r(key)).or(Some("")).unwrap()
            );
            out.push((depth, s, node.span_id));
            for expr in args {
                dump_strings(expr, b, out, depth + 1);
            }
        }

        Ast::Continue(maybe_key, args) => {
            let s = format!(
                "continue({})",
                maybe_key.map(|key| b.r(key)).or(Some("")).unwrap()
            );
            out.push((depth, s, node.span_id));
            for expr in args {
                dump_strings(expr, b, out, depth + 1);
            }
        }

        _ => unimplemented!("{:?}", node),
    }
}

/*
pub fn print_html(s: &str, depth: usize, span: &Span) {
    println!(
        "{:width$}<span class=\"span{}\">{}</span>",
        "",
        span.span_id.index(),
        s,
        width = depth * 2
    );
}
*/
