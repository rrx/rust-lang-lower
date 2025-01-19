use compile_core::{AstType, Literal};
use petgraph::graph::NodeIndex;

use std::convert::Into;

use crate::{
    BlockId, CodeOffset, CodeRow, Flatten, LCode, LinkId, Module, NodeBuilder as NB, StringLabel,
    Successor, ValueId, VarDefinitionSpace,
};

use tabled::{settings::Style, Table};

impl Flatten<Module> {
    pub fn shared_libraries(&self) -> Vec<String> {
        self.link.shared_libraries()
    }

    pub fn get_block_successors(&self, block_id: BlockId) -> Vec<(Successor, BlockId)> {
        self.blocks.get_block_successors(block_id)
    }

    pub fn get_type(&self, v: CodeOffset) -> AstType {
        let value_id = self.value(v);
        let link_id = self.link(value_id);
        let entry = self.get_entry(link_id);
        entry.clone().ty
    }

    pub fn get_block_id<T: Copy + Into<CodeOffset>>(&self, offset: T) -> BlockId {
        let entry = self.get_entry(offset);
        entry.block_id.clone()
    }

    pub fn get_entry_id<T: Copy + Into<CodeOffset>>(&self, offset: T) -> Option<ValueId> {
        let link_id = self.link(offset);
        let block_id = self.get_entry(link_id).block_id;
        self.blocks.maybe_value(block_id)
    }

    pub fn maybe_link<T: Copy + Into<CodeOffset>>(&self, code_offset: T) -> Option<LinkId> {
        match code_offset.into() {
            CodeOffset::Value(v) => Some(self.state.values.get(v)),
            CodeOffset::Link(link_id) => Some(link_id),
            CodeOffset::Block(block_id) => {
                if let Some(link_id) = self.blocks.maybe_link(block_id) {
                    Some(link_id)
                } else {
                    None
                }
            }
        }
    }

    pub fn is_in_static_scope(&self, offset: CodeOffset) -> bool {
        let value_id = self.value(offset);
        let link_id = self.link(value_id);
        let entry = self.get_entry(link_id);
        let block = self.blocks.get_block(entry.block_id);
        let scope = self.blocks.get_scope(block.scope());
        scope.is_static()
    }

    pub fn value<T: Copy + Into<CodeOffset>>(&self, offset: T) -> ValueId {
        self.blocks.value(offset)
    }

    pub fn link<T: Copy + Into<CodeOffset>>(&self, offset: T) -> LinkId {
        self.state.values.get(self.value(offset))
    }

    pub fn get_code<T: Copy + Into<CodeOffset>>(&self, offset: T) -> &LCode {
        let link_id = self.link(offset);
        &self.get_entry(link_id).code
    }

    pub fn get_name(&self, offset: CodeOffset) -> Option<StringLabel> {
        if let Some(value_id) = self.blocks.maybe_value(offset) {
            let link_id = self.state.values.get(value_id);
            self.get_entry(link_id).name.map(|n| n.into())
        } else {
            None
        }
    }

    pub fn get_code_row(&self, v: ValueId, b: &mut NB) -> Option<CodeRow> {
        let link_id = self.link(v);
        let entry = self.get_entry(link_id);
        let block = self
            .blocks
            .block_graph()
            .node_weight(NodeIndex::new(entry.block_id.index()))
            .unwrap();
        let entry_id = self.get_entry_id(v).map(|v| format!("{}", v));

        let r_ty = if let Some(r_ty) = b.types.u.resolve(&entry.ty) {
            r_ty
        } else {
            entry.ty.clone()
        };

        let is_unknown = r_ty.is_unknown();
        let s_ty = format!("{}", &r_ty);

        let scope_id = block.scope();
        let link_id = entry.link.unwrap();

        Some(CodeRow {
            pos: v,
            link: link_id,
            value: self.code_to_string(link_id, b),
            ty: s_ty,
            mem: format!("{:?}", entry.mem),
            name: self
                .get_name(v.into())
                .map(|key| b.labels.r(key))
                .unwrap_or("".to_string())
                .to_string(),
            span_id: entry.span_id.index(),
            scope_id: scope_id.index(),
            entry_id: entry_id.map(|v| v).unwrap_or("".to_string()),
            block_id: entry.block_id.index(),
            term: entry.code.is_term(),
            dead: block.is_dead(),
            unknown: is_unknown,
        })
    }

    pub fn dump_code_table(&self, filename: &str, b: &mut NB) -> String {
        let mut rows = vec![];
        for value_id in self.state.values.iter() {
            if let Some(row) = self.get_code_row(value_id, b) {
                rows.push(row);
            } else {
                println!("Unable to load entry: {}", value_id);
            }
        }
        let s = Table::new(rows).with(Style::sharp()).to_string();
        println!("saved table {:?}", filename);
        std::fs::write(filename, s.clone()).unwrap();
        s
    }

    pub fn resolve_declaration<'c>(&self, offset: CodeOffset) -> Option<CodeOffset> {
        let mut current = offset;
        loop {
            let value_id = self.value(current);
            let code = self.get_code(value_id);
            if let LCode::CallValue(base) = code {
                //current = inds.clone().offset();
                current = *base;
                continue;
            }

            if let LCode::Use(base, _inds) = code {
                current = *base;
                continue;

                /*
                if _inds.len() == 0 {
                    current = *base;
                    continue;
                }

                assert_eq!(_inds.len(), 1);

                //let value_id = self.resolve_code_offset(*base);
                //let code = self.get_code(value_id);
                let ty = self.get_type(*base);
                assert!(ty.is_composite());
                let index = _inds.get(0).unwrap().clone();
                //let (_, field_type) = ty.fields().get(inds.get(0).unwrap()));
                current = match index {
                    UseIndex::Use(offset) => {
                        let v = self.resolve_code_offset(offset);
                        let code = self.get_code(v);
                        let pos = match code {
                            LCode::Val(Literal::Int(i)) => *i as usize,
                            _ => unimplemented!(),
                        };
                        let (_, _field_type) = ty.fields().get(pos).unwrap().clone();
                        v.into()
                    }
                    _ => unimplemented!(),
                };
                //let base = self.resolve_declaration(base).unwrap();
                //current = *base;
                return Some(current);
                */
            }

            return Some(current);
        }
    }

    pub fn get_label_args(&self, link_id: LinkId) -> Vec<AstType> {
        let entry = self.get_entry(link_id);
        let block_id = entry.block_id;
        let block = self.blocks.get_block(block_id);
        let args: Vec<_> = block.iter_args().collect();
        let mut out = vec![];
        for current in args {
            let entry = self.get_entry(current);
            if let LCode::Arg(_) = &entry.code {
                out.push(entry.ty.clone());
            } else {
                unreachable!()
            }
        }
        out
    }

    pub fn code_to_string(&self, link_id: LinkId, b: &NB) -> String {
        let entry = self.get_entry(link_id);
        match &entry.code {
            LCode::Declare => {
                let code_str = b.labels.r(entry.name.unwrap().into());
                format!("declare {}", code_str)
            }

            LCode::DeclareFunction(maybe_entry) => {
                let code_str = b.labels.r(entry.name.unwrap().into());
                if let Some(entry_id) = maybe_entry {
                    format!("declare_function({},{})", code_str, entry_id)
                } else {
                    format!("declare_function({})", code_str)
                }
            }

            LCode::Label => {
                let args = self.get_label_args(link_id);
                if let Some(key) = entry.name {
                    format!("label({},{})", b.labels.r(key.into()), args.len())
                } else {
                    format!("label(_,{})", args.len())
                }
            }

            LCode::Jump(value_id) => {
                format!("jump({})", value_id)
            }

            LCode::Val(Literal::String(s)) => {
                format!("String({})", s)
            }

            LCode::Ternary(c, x, y) => {
                format!("Ternary({:?},{},{})", c, x, y)
            }

            LCode::Branch(c, x, y) => {
                format!("Branch({:?},{},{})", c, x, y)
            }

            LCode::Switch(link_id, m) => {
                let mut s = vec![];
                for (k, v) in m {
                    s.push(format!("{}->{}", k, v));
                }
                format!("switch({},{})", link_id, s.join(","))
            }

            _ => {
                format!("{:?}", entry.code)
            }
        }
    }

    pub fn mem_to_string(&self, mem: VarDefinitionSpace, _b: &NB) -> String {
        match mem {
            VarDefinitionSpace::Arg => format!("Marg"),
            VarDefinitionSpace::Reg => format!("Mreg"),
            VarDefinitionSpace::Static => format!("Mstatic"),
            VarDefinitionSpace::Stack(x) => {
                let v = self.value(x);
                format!("Mstack({})", v)
            }
            VarDefinitionSpace::Heap => format!("Mheap"),
            VarDefinitionSpace::Default => format!("Mdef"),
        }
    }
}
