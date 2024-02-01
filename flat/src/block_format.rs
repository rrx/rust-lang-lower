use serde::Serialize;
use std::collections::VecDeque;

use tabled::{
    settings::{object::Rows, Border, Style},
    Table, Tabled,
};

use lower::{AstType, Extra, Literal, NodeBuilder};

use crate::{Blockify, LCode, ValueId};

#[derive(Tabled, Serialize)]
pub struct CodeRow {
    pos: usize,
    next: usize,
    prev: usize,
    value: String,
    ty: AstType,
    mem: String,
    name: String,
    span_id: usize,
    scope_id: usize,
    block_id: usize,
    term: bool,
}

impl CodeRow {
    pub fn header() -> Vec<&'static str> {
        vec![
            "pos", "next", "prev", "value", "ty", "mem", "name", "span_id", "scope_id", "block_id",
            "term",
        ]
    }

    fn format_html_header() -> String {
        let mut s = String::new();
        s.push_str("<thead><tr>");
        for row in Self::header() {
            s.push_str(&format!("<td>{}</td>", row));
        }
        s
    }

    fn format_html_row(&self) -> String {
        let mut s = String::new();
        s.push_str(&format!("<tr class=\"s{}\">", self.span_id));
        s.push_str(&format!("<td>{}</td>", self.pos));
        s.push_str(&format!("<td>{}</td>", self.next));
        s.push_str(&format!("<td>{}</td>", self.prev));
        s.push_str(&format!("<td>{}</td>", self.value));
        s.push_str(&format!("<td>{}</td>", self.ty));
        s.push_str(&format!("<td>{}</td>", self.mem));
        s.push_str(&format!("<td>{}</td>", self.name));
        s.push_str(&format!("<td>{}</td>", self.span_id));
        s.push_str(&format!("<td>{}</td>", self.scope_id));
        s.push_str(&format!("<td>{}</td>", self.block_id));
        s.push_str(&format!("<td>{}</td>", self.term));
        s.push_str("</tr>");
        s
    }
}

impl<E: Extra> Blockify<E> {
    pub fn code_to_string(&self, v: ValueId, b: &NodeBuilder<E>) -> String {
        let code = self.get_code(v);
        match code {
            LCode::Declare => {
                let code_str = b.resolve_label(self.get_name(v).unwrap());
                format!("declare {}: {:?}", code_str, self.get_type(v))
            }

            LCode::DeclareFunction(maybe_entry) => {
                let code_str = b.resolve_label(self.get_name(v).unwrap());
                if let Some(entry_id) = maybe_entry {
                    format!("declare_function({},{})", code_str, entry_id.0)
                } else {
                    format!("declare_function({})", code_str)
                }
            }

            LCode::Label(args, kwargs) => {
                if let Some(key) = self.get_name(v) {
                    format!("label({}, {}, {})", b.resolve_label(key), args, kwargs,)
                } else {
                    format!("label(-, {}, {})", args, kwargs,)
                }
            }

            LCode::Goto(block_id) => {
                format!("goto({})", b.r(*block_id))
            }

            LCode::Jump(value_id, args) => {
                format!("jump({}, {})", value_id.0, args,)
            }

            LCode::Const(Literal::String(s)) => {
                format!("String({})", s)
            }

            LCode::Ternary(c, x, y) => {
                format!("Ternary({},{},{})", c.0, x.0, y.0)
            }

            LCode::Branch(c, x, y) => {
                format!("Branch({},{},{})", c.0, x.0, y.0)
            }

            _ => {
                format!("{:?}", code)
            }
        }
    }

    fn get_code_row(&self, v: ValueId, b: &NodeBuilder<E>) -> CodeRow {
        let code = self.get_code(v);
        let ty = self.get_type(v);
        let mem = self.get_mem(v);
        let next = self.get_next(v).unwrap_or(v).index();
        let prev = self.get_prev(v).unwrap_or(v).index();
        let scope_id = self.get_scope_id(v);
        let block_id = self.get_block_id(v);

        CodeRow {
            pos: v.index(),
            next,
            prev,
            value: self.code_to_string(v, b),
            ty,
            mem: format!("{:?}", mem),
            name: self
                .get_name(v)
                .map(|key| b.resolve_label(key))
                .unwrap_or("".to_string())
                .to_string(),
            span_id: self.get_span_id(v).index(),
            scope_id: scope_id.0 as usize,
            block_id: block_id.0 as usize,
            term: code.is_term(),
        }
    }

    pub fn dump_codes_filter(&self, b: &NodeBuilder<E>, filter_block_id: ValueId) -> Vec<CodeRow> {
        let mut pos = 0;
        let mut out = vec![];
        loop {
            let v = ValueId(pos as u32);
            let row = self.get_code_row(v, b);
            let block_id = self.get_block_id(v);

            let mut display = true;
            if filter_block_id != block_id {
                display = false;
            }

            if display {
                out.push(row);
            }

            pos += 1;
            if pos == self.code_count() {
                break;
            }
        }
        out
    }

    pub fn get_code_rows(&self, b: &NodeBuilder<E>) -> Vec<CodeRow> {
        let mut out = vec![];
        let iter = LCodeIterator::new(self);
        for (i, v) in iter.enumerate() {
            let row = self.get_code_row(v, b);
            let code = self.get_code(v);
            out.push(row);
        }
        out
    }

    pub fn dump_codes(&self, b: &NodeBuilder<E>) -> String {
        let mut out = vec![];
        let mut labels = vec![];
        let iter = LCodeIterator::new(self);
        for (i, v) in iter.enumerate() {
            let row = self.get_code_row(v, b);
            let code = self.get_code(v);

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

    pub fn dump(&self, b: &NodeBuilder<E>) {
        //self.dump_codes(b, None);
        self.env.dump(b);

        for (block_id, block) in self.env.blocks.iter() {
            println!("block({:?}, {:?})", block_id, block);
            let rows = self.dump_codes_filter(b, *block_id);
            let s = Table::new(rows).with(Style::sharp()).to_string();
            println!("{}", s);
        }

        use minijinja::{context, Environment};
        use std::io::prelude::*;
        let mut env = Environment::new();
        env.add_template("template", include_str!("template.html"))
            .unwrap();
        let tmpl = env.get_template("template").unwrap();
        let rows = self.get_code_rows(b);
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
}

pub struct LCodeIterator<'a, E> {
    blockify: &'a Blockify<E>,
    blocks: Vec<ValueId>,
    values: VecDeque<ValueId>,
}

impl<'a, E> LCodeIterator<'a, E> {
    pub fn new(blockify: &'a Blockify<E>) -> Self {
        let blocks = blockify.env.blocks.keys().rev().cloned().collect();
        Self {
            blockify,
            blocks,
            values: VecDeque::new(),
        }
    }
}

impl<'a, E: Extra> Iterator for LCodeIterator<'a, E> {
    type Item = ValueId;

    fn next(&mut self) -> Option<Self::Item> {
        if self.values.len() == 0 {
            if self.blocks.len() == 0 {
                return None;
            }

            let block_id = self.blocks.pop().unwrap();
            let mut current = block_id;
            self.values.push_back(block_id);
            loop {
                if let Some(next) = self.blockify.get_next(current) {
                    self.values.push_back(next);
                    current = next;
                } else {
                    break;
                }
            }
        }
        self.values.pop_front()
    }
}
