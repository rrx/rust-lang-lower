use std::collections::VecDeque;

use compile_core::AstType;

use crate::{Blockify, ICodeModule, NodeBuilder, ValueId};
use serde::Serialize;
use tabled::{
    settings::{
        //object::Rows,
        //Border,
        Style,
    },
    Table, Tabled,
};

#[derive(Tabled, Serialize)]
pub struct CodeRow {
    pub pos: usize,
    pub link: usize,
    //pub next: usize,
    //pub prev: usize,
    pub value: String,
    pub ty: AstType,
    pub mem: String,
    pub name: String,
    pub span_id: usize,
    pub scope_id: usize,
    pub block_id: usize,
    pub entry_id: usize,
    pub term: bool,
    pub dead: bool,
}

impl CodeRow {
    pub fn header() -> Vec<&'static str> {
        vec![
            "pos", "link", "next", "prev", "value", "ty", "mem", "name", "span_id", "scope_id",
            "block_id", "term", "dead",
        ]
    }
}

impl Blockify {
    pub fn dump(&self, b: &NodeBuilder) {
        //self.dump_codes(b, None);
        b.dump_env(&self.env);

        for block in self.env.blocks.iter() {
            println!("block({:?}, {:?})", block.entry_id, block);
            let rows = self.dump_codes_filter(b, block.entry_id.unwrap());
            let s = Table::new(rows).with(Style::sharp()).to_string();
            println!("{}", s);
        }
    }

    pub fn dump_codes_filter(&self, b: &NodeBuilder, filter_entry_id: ValueId) -> Vec<CodeRow> {
        let mut pos = 0;
        let mut out = vec![];
        loop {
            let v = ValueId::new(pos as u32);
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

    pub fn get_code_row(&self, v: ValueId, b: &NodeBuilder) -> CodeRow {
        let code = self.get_code(v);
        let ty = self.get_type(v.into());
        let mem = self.get_mem(v.into());
        //let next = self.get_next(v).unwrap_or(v).index();
        //let prev = self.get_prev(v).unwrap_or(v).index();
        let scope_id = self.get_scope_id(v);
        let entry_id = self.get_entry_id(v);
        let block_id = self.env.block_map.get(&entry_id).unwrap();

        CodeRow {
            pos: v.index(),
            link: 0,
            //next,
            //prev,
            value: self.code_to_string(v, b),
            ty,
            mem: format!("{:?}", mem),
            name: self
                .get_name(v.into())
                .map(|key| b.labels.r(key))
                .unwrap_or("".to_string())
                .to_string(),
            span_id: self.get_span_id(v).index(),
            scope_id: scope_id.index(),
            entry_id: entry_id.index(),
            block_id: block_id.index(),
            term: code.is_term(),
            dead: false,
        }
    }
}

pub struct LCodeIterator<'a> {
    blockify: &'a Blockify,
    blocks: Vec<ValueId>,
    values: VecDeque<ValueId>,
}

impl<'a> LCodeIterator<'a> {
    pub fn new(blockify: &'a Blockify) -> Self {
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

impl<'a> Iterator for LCodeIterator<'a> {
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
