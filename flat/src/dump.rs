use crate::{block_format::LCodeIterator, Blockify, Environment, ICodeModule, NodeBuilder};
use compile_core::{Argument, AssignTarget, Ast, AstNode, ControlFlowMarker, SpanId};

use tabled::{
    settings::{object::Rows, Border, Style},
    Table,
};

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

    fn dump_strings(
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
                let _s = format!("sequence:");
                depth += 1;
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

            Ast::CloseBlock => {
                let s = "close_block";
                out.push((depth, s.into(), node.span_id));
            }

            _ => unimplemented!("{:?}", node),
        }
    }

    pub fn dump_env(&self, env: &Environment) {
        println!("current scope: {:?}", env.current_scope());
        //println!("static block: {:?}", self.static_block_id());
        //println!("static scope: {:?}", self.static_scope_id());
        for block in env.blocks.iter() {
            //let block_id = BlockId(offset as u32);
            println!("block({:?}, {:?})", block.entry_id, block);
        }

        for (index, layer) in env.scopes.iter().enumerate() {
            println!("scope({},{:?})", index, layer.scope_type);
            for (key, data) in layer.names.iter() {
                println!("  name  {} = {:?}", self.labels.r((*key).into()), data);
            }
            for (key, data) in layer.labels.iter() {
                println!("  label {} = {:?}", self.labels.r(*key), data);
            }
            for next_id in layer.next_block.iter() {
                println!("  next  {:?}", next_id);
            }
            for block_id in layer.blocks.iter() {
                println!("  block {:?}", block_id);
            }
            for (name, def) in layer.lambdas.iter() {
                println!("  def {:?}", (self.labels.r(*name), def));
            }
        }
    }

    pub fn dump_blockify(&self, blockify: &Blockify) {
        //self.dump_codes(b, None);
        self.dump_env(&blockify.env);

        for block in blockify.env.blocks.iter() {
            println!("block({:?}, {:?})", block.entry_id, block);
            let rows = blockify.dump_codes_filter(self, block.entry_id.unwrap().into());
            let s = Table::new(rows).with(Style::sharp()).to_string();
            println!("{}", s);
        }
        /*
        let rows = self.get_code_rows(b);

        if false {
        use minijinja::{context, Environment};
        use std::io::prelude::*;
        let mut env = Environment::new();
        env.add_template("template", include_str!("template.html"))
        .unwrap();
        let tmpl = env.get_template("template").unwrap();
        let html = tmpl
        .render(context!(header => CodeRow::header(), rows => rows))
        .unwrap();
        let mut file = std::fs::File::create("blocks.html").unwrap();
        file.write_all(html.as_bytes()).unwrap();
        println!(
        "{}",
        tmpl.render(context!(header => CodeRow::header(), rows => rows))
        .unwrap()
        );
        }
        */
    }

    pub fn dump_codes(&self, blockify: &Blockify) -> String {
        let mut out = vec![];
        let mut labels = vec![];
        let iter = LCodeIterator::new(blockify);
        for (i, v) in iter.enumerate() {
            let row = blockify.get_code_row(v, self);
            let code = blockify.get_code(v);

            if code.is_start() {
                labels.push(i + 1);
            }

            out.push(row);
        }

        let mut t = Table::new(out);

        t.with(Style::sharp());

        for i in labels {
            let rows = Rows::single(i);
            t.modify(rows, Border::new().set_top('-'));
        }
        let s = t.to_string();
        println!("{}", s);
        s
    }
}
