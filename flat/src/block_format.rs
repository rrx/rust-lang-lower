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
    pub pos: usize,
    pub next: usize,
    pub prev: usize,
    pub value: String,
    pub ty: AstType,
    pub mem: String,
    pub name: String,
    pub span_id: usize,
    pub scope_id: usize,
    pub block_id: usize,
    pub entry_id: usize,
    pub term: bool,
}

impl CodeRow {
    pub fn header() -> Vec<&'static str> {
        vec![
            "pos", "next", "prev", "value", "ty", "mem", "name", "span_id", "scope_id", "block_id",
            "term",
        ]
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
                format!("jump({:?}, {})", value_id, args,)
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
}
/*
    fn get_code_row(&self, v: ValueId, b: &NodeBuilder<E>) -> CodeRow {
        let code = self.get_code(v);
        let ty = self.get_type(v);
        let mem = self.get_mem(v);
        let next = self.get_next(v).unwrap_or(v).index();
        let prev = self.get_prev(v).unwrap_or(v).index();
        let scope_id = self.get_scope_id(v);
        let entry_id = self.get_entry_id(v);
        let block_id = self.env.block_map.get(&entry_id).unwrap();

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
            entry_id: entry_id.index(),
            block_id: block_id.index(),
            term: code.is_term(),
        }
    }

    pub fn dump_codes_filter(&self, b: &NodeBuilder<E>, filter_entry_id: ValueId) -> Vec<CodeRow> {
        let mut pos = 0;
        let mut out = vec![];
        loop {
            let v = ValueId(pos as u32);
            let row = self.get_code_row(v, b);
            let entry_id = self.get_entry_id(v);

            let mut display = true;
            if filter_entry_id != entry_id {
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
        for (_i, v) in iter.enumerate() {
            let row = self.get_code_row(v, b);
            let _code = self.get_code(v);
            out.push(row);
        }
        out
    }

    pub fn get_json(&self, b: &NodeBuilder<E>) -> String {
        let out = self.get_code_rows(b);
        serde_json::to_string(&out).unwrap()
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
}
*/

pub struct LCodeIterator<'a, E> {
    blockify: &'a Blockify<E>,
    blocks: Vec<ValueId>,
    values: VecDeque<ValueId>,
}

impl<'a, E> LCodeIterator<'a, E> {
    pub fn new(blockify: &'a Blockify<E>) -> Self {
        let blocks = blockify
            .env
            .blocks
            .iter()
            .rev()
            .map(|block| block.entry_id.unwrap())
            .collect();
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
