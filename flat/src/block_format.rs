use std::collections::VecDeque;

use compile_core::Literal;

use crate::{Blockify, LCode, NodeBuilder, ValueId};

impl Blockify {
    pub fn code_to_string(&self, v: ValueId, b: &NodeBuilder) -> String {
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
