use compile_core::{AstType, SpanId};
use petgraph::graph::NodeIndex;

use std::convert::Into;

use crate::{
    CodeEntry, CodeOffset, CodeRow, Flatten, ICodeModule, LCode, Module, NodeBuilder as NB,
    StringLabel, Successor, ValueId, VarDefinitionSpace,
};

use tabled::{settings::Style, Table};

impl ICodeModule for Flatten<Module> {
    fn get_entry(&self, value_id: ValueId) -> &CodeEntry {
        let link_id = self.state.values.get(value_id);
        self.get_link_entry(link_id)
    }

    fn shared_libraries(&self) -> Vec<String> {
        self.link.shared_libraries()
    }

    fn get_span_id(&self, value_id: ValueId) -> SpanId {
        let link_id = self.state.values.get(value_id);
        let entry = self.get_link_entry(link_id);
        entry.span_id
    }

    fn get_name(&self, offset: CodeOffset) -> Option<StringLabel> {
        if let Some(value_id) = self.maybe_resolve_code_offset(offset) {
            let link_id = self.state.values.get(value_id);
            self.get_link_entry(link_id).name.map(|n| n.into())
        } else {
            None
        }
    }

    fn get_code(&self, value_id: ValueId) -> &LCode {
        let link_id = self.state.values.get(value_id);
        &self.get_link_entry(link_id).code
    }

    fn get_block_successors(&self, entry_id: ValueId) -> Vec<(Successor, CodeOffset)> {
        let link_id = self.state.values.get(entry_id);
        let entry = self.get_link_entry(link_id);
        let block_id = entry.block_id;
        self.blocks.get_block_successors(block_id)
    }

    fn get_type(&self, v: CodeOffset) -> AstType {
        let value_id = self.resolve_code_offset(v);
        let link_id = self.state.values.get(value_id);
        let entry = self.get_link_entry(link_id);
        entry.clone().ty
    }

    fn get_entry_id(&self, value_id: ValueId) -> Option<ValueId> {
        let link_id = self.state.values.get(value_id);
        let block_id = self.get_link_entry(link_id).block_id;
        self.maybe_resolve_code_offset(block_id.into())
    }

    fn is_in_static_scope(&self, offset: CodeOffset) -> bool {
        let value_id = self.resolve_code_offset(offset);
        let link_id = self.state.values.get(value_id);
        let entry = self.get_link_entry(link_id);
        let block = self.blocks.get_block(entry.block_id);
        let scope = self.blocks.get_scope(block.scope());
        scope.is_static()
    }

    fn get_mem(&self, offset: CodeOffset) -> &VarDefinitionSpace {
        let value_id = self.resolve_code_offset(offset);
        let link_id = self.state.values.get(value_id);
        &self.get_link_entry(link_id).mem
    }

    fn resolve_code_offset(&self, code_offset: CodeOffset) -> ValueId {
        self.inner.resolve_code_offset(code_offset)
    }

    fn maybe_resolve_code_offset(&self, code_offset: CodeOffset) -> Option<ValueId> {
        self.inner.maybe_resolve_code_offset(code_offset)
    }

    fn get_label_args(&self, v: ValueId) -> Vec<AstType> {
        let entry = self.get_entry(v);
        let block_id = entry.block_id;
        let block = self.blocks.get_block(block_id);
        let args: Vec<_> = block.iter_args().collect();
        let mut out = vec![];
        for current in args {
            let entry = self.get_link_entry(current);
            if let LCode::Arg(_) = &entry.code {
                out.push(entry.ty.clone());
            } else {
                unreachable!()
            }
        }
        out
    }
}

impl Flatten<Module> {
    pub fn get_code_row(&self, v: ValueId, b: &mut NB) -> Option<CodeRow> {
        let link_id = self.state.values.get(v);
        let entry = self.get_link_entry(link_id);
        let code = self.get_code(v);

        let mem = self.get_mem(v.into());
        let block_id = entry.block_id;
        let block = self
            .blocks
            .block_graph()
            .node_weight(NodeIndex::new(block_id.index()))
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

        Some(CodeRow {
            pos: v,
            link: entry.link.unwrap(),
            value: self.code_to_string(v, b),
            ty: s_ty,
            mem: format!("{:?}", mem),
            name: self
                .get_name(v.into())
                .map(|key| b.labels.r(key))
                .unwrap_or("".to_string())
                .to_string(),
            span_id: self.get_span_id(v).index(),
            scope_id: scope_id.index(),
            entry_id: entry_id.map(|v| v).unwrap_or("".to_string()),
            block_id: block_id.index(),
            term: code.is_term(),
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
}
