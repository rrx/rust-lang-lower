use anyhow::Result;
use compile_core::{AstType, LinkOptions, Literal, SpanId, StringKey, VarDefinitionSpace};
use petgraph::graph::NodeIndex;
use std::collections::HashMap;

use std::convert::Into;

use crate::{
    BlockGraph, BlockId, CodeEntry, CodeOffset, CodeRow, ContinuationFlow, Flatten,
    FunctionVariant, FunctionVariantBuilder, ICodeModule, LCode, LinkId, NodeBuilder as NB,
    ScopeGraph, ScopeType, ScopedContinuations, StringLabel, Successor, ValueId, VariantId,
};

use tabled::{settings::Style, Table};

pub struct FlattenModule {
    pub(super) link: LinkOptions,
    pub entries: Vec<CodeEntry>,
    pub values: Vec<LinkId>,
    pub blocks: BlockGraph,
    pub messages: Vec<(String, SpanId)>,
    pub scopes: ScopeGraph,
    pub block_links: HashMap<BlockId, LinkId>,
    pub(crate) functions: HashMap<StringKey, LinkId>,
    pub statics: HashMap<StringKey, Literal>,
    pub variants: FunctionVariantBuilder,
    pub scoped_continuations: ScopedContinuations,
}

impl ICodeModule for FlattenModule {
    fn get_entry(&self, value_id: ValueId) -> &CodeEntry {
        let link_id = self.values[value_id.index()];
        self.entries.get(link_id.index()).unwrap()
    }

    fn find_source_blocks(&self, flow: ContinuationFlow) -> Vec<BlockId> {
        self.scoped_continuations.find_source_blocks(flow)
    }

    fn find_sink_block(&self, flow: ContinuationFlow) -> Option<ContinuationFlow> {
        self.scoped_continuations.find_sink_block(flow)
    }

    fn get_variant_by_block(&self, block_id: BlockId) -> Option<VariantId> {
        self.variants.get_by_block(block_id)
    }

    fn get_variant(&self, variant_id: VariantId) -> &FunctionVariant {
        self.variants.get(variant_id)
    }

    fn shared_libraries(&self) -> Vec<String> {
        self.link.shared_libraries()
    }

    fn lookup_name(&self, name: &StringKey) -> Option<LinkId> {
        self.functions.get(name).cloned()
    }

    fn get_span_id(&self, value_id: ValueId) -> SpanId {
        let link_id = self.values[value_id.index()];
        let entry = self.get_link_entry(link_id);
        entry.span_id
    }

    fn get_name(&self, offset: CodeOffset) -> Option<StringLabel> {
        if let Some(value_id) = self.maybe_resolve_code_offset(offset) {
            let link_id = self.values[value_id.index()];
            self.get_link_entry(link_id).name.map(|n| n.into())
        } else {
            None
        }
    }

    fn get_code(&self, value_id: ValueId) -> &LCode {
        let link_id = self.values[value_id.index()];
        &self.get_link_entry(link_id).code
    }

    fn get_next(&self, value_id: ValueId) -> Option<ValueId> {
        let link_id = self.values[value_id.index()];
        let entry = self.get_link_entry(link_id);
        if entry.next != link_id {
            let next_entry = self.get_link_entry(entry.next);
            next_entry.value_id
        } else {
            None
        }
    }

    /*
    fn get_prev(&self, value_id: ValueId) -> Option<ValueId> {
    let value_id = LinkId(value_id.index() as u32);
    let entry = self.get_entry(value_id);
    if entry.prev != value_id {
    Some(ValueId(entry.prev.index() as u32))
    } else {
    None
    }
    }
    */

    fn get_block_successors(&self, entry_id: ValueId) -> Vec<(Successor, CodeOffset)> {
        let link_id = self.values[entry_id.index()];
        let entry = self.get_link_entry(link_id);
        let block_id = entry.block_id;
        self.blocks.get_block_successors(block_id)
    }

    fn get_type(&self, v: CodeOffset) -> AstType {
        let value_id = self.resolve_code_offset(v);
        let link_id = self.values[value_id.index()];
        let entry = self.get_link_entry(link_id);
        entry.clone().ty
    }

    fn get_entry_id(&self, value_id: ValueId) -> Option<ValueId> {
        let link_id = self.values[value_id.index()];
        let block_id = self.get_link_entry(link_id).block_id;
        self.maybe_resolve_code_offset(block_id.into())
    }

    fn is_in_static_scope(&self, offset: CodeOffset) -> bool {
        let value_id = self.resolve_code_offset(offset);
        let link_id = self.values[value_id.index()];
        let entry = self.get_link_entry(link_id);
        let block = self.blocks.get_block(entry.block_id);
        let scope = self.scopes.get_scope(block.scope_id);
        scope.scope_type == ScopeType::Static
    }

    fn get_mem(&self, offset: CodeOffset) -> &VarDefinitionSpace {
        let value_id = self.resolve_code_offset(offset);
        let link_id = self.values[value_id.index()];
        &self.get_link_entry(link_id).mem
    }

    fn resolve_code_offset(&self, code_offset: CodeOffset) -> ValueId {
        self.maybe_resolve_code_offset(code_offset)
            .expect(&format!("Unable to resolve: {}", code_offset))
    }

    fn maybe_resolve_code_offset(&self, code_offset: CodeOffset) -> Option<ValueId> {
        match code_offset {
            CodeOffset::Value(v) => Some(v),
            CodeOffset::Link(link_id) => {
                let entry = self.get_link_entry(link_id);
                entry.value_id
            }
            CodeOffset::Block(block_id) => {
                if let Some(link_id) = self.block_links.get(&block_id) {
                    let entry = self.get_link_entry(*link_id);
                    entry.value_id
                } else {
                    None
                }
            }
        }
    }

    fn code_count(&self) -> usize {
        self.entries.len()
    }

    fn dump_code_table(&self, filename: &str, b: &mut NB) {
        let mut rows = vec![];
        for index in 0..self.values.len() {
            let value_id = ValueId::new(index as u32);
            if let Some(row) = self.get_code_row(value_id, b) {
                rows.push(row);
            } else {
                println!("Unable to load entry: {}", value_id);
            }
        }
        let s = Table::new(rows).with(Style::sharp()).to_string();
        println!("{}", s);
        std::fs::write(filename, s).unwrap();
    }
}

impl FlattenModule {
    pub fn build(f: Flatten, b: &mut NB) -> Result<Self> {
        let (f, values) = f.finish(b)?;
        Ok(Self {
            link: f.link,
            entries: f.entries,
            values,
            blocks: f.blocks,
            messages: f.messages,
            scopes: f.scopes,
            block_links: f.block_links,
            functions: f.functions,
            statics: f.statics,
            variants: f.variants,
            scoped_continuations: f.scoped_continuations,
        })
    }

    fn get_link_entry(&self, link_id: LinkId) -> &CodeEntry {
        self.entries.get(link_id.index()).unwrap()
    }

    pub fn get_code_row(&self, v: ValueId, b: &mut NB) -> Option<CodeRow> {
        let link_id = self.values[v.index()];
        let entry = self.get_link_entry(link_id);
        let code = self.get_code(v);

        let mem = self.get_mem(v.into());
        let block_id = entry.block_id;
        let block = self
            .blocks
            .node_weight(NodeIndex::new(block_id.index()))
            .unwrap();
        let entry_id = self.get_entry_id(v);

        let r_ty = if let Some(r_ty) = b.types.u.resolve(&entry.ty) {
            r_ty
        } else {
            entry.ty.clone()
        };

        let is_unknown = r_ty.is_unknown();
        let s_ty = format!("{}", &r_ty);

        let scope_id = block.scope_id;

        Some(CodeRow {
            pos: v.index(),
            link: entry.link.unwrap().index(),
            next: entry.next.index(),
            //prev: entry.prev.index(),
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
            entry_id: entry_id.map(|v| v.index()).unwrap_or(0),
            block_id: block_id.index(),
            term: code.is_term(),
            dead: block.dead,
            unknown: is_unknown,
        })
    }

    pub fn dump_code_table(&self, filename: &str, b: &mut NB) {
        let mut rows = vec![];
        for index in 0..self.values.len() {
            let value_id = ValueId::new(index as u32);
            if let Some(row) = self.get_code_row(value_id, b) {
                rows.push(row);
            } else {
                println!("Unable to load entry: {}", value_id);
            }
        }
        let s = Table::new(rows).with(Style::sharp()).to_string();
        println!("{}", s);
        std::fs::write(filename, s).unwrap();
    }

    pub fn cont_graph(&self, filename: &str, b: &NB) {
        let s = format!(
            "{:?}",
            petgraph::dot::Dot::with_attr_getters(
                &self.scoped_continuations.g,
                &[
                    petgraph::dot::Config::EdgeNoLabel,
                    petgraph::dot::Config::NodeNoLabel
                ],
                &|_, edge| {
                    let w = edge.weight();
                    format!("label = \"{:?}\"", w,)
                },
                &|_, (_, c)| {
                    match c {
                        ContinuationFlow::Block(block_id) => {
                            let s_name = if let Some(name) = self.get_name(block_id.into()) {
                                b.labels.r(name)
                            } else {
                                "?".to_string()
                            };
                            format!("label = \"B.{}:{}\"", s_name, block_id)
                        }
                        ContinuationFlow::BlockArg(block_id, arg) => {
                            let s_name = if let Some(name) = self.get_name(block_id.into()) {
                                b.labels.r(name)
                            } else {
                                "?".to_string()
                            };
                            format!("label = \"BA.{}:{}:{}\"", s_name, block_id, arg)
                        }
                        ContinuationFlow::Jump(link_id) => {
                            let v = self.maybe_resolve_code_offset(link_id.into());
                            format!("label = \"JUMP:{:?}\"", v)
                        }
                        ContinuationFlow::JumpArg(link_id, arg) => {
                            let v = self.maybe_resolve_code_offset(link_id.into());
                            format!("label = \"JUMP:{:?}:{}\"", v, arg)
                        }
                        ContinuationFlow::Variable(link_id) => {
                            let v = self.resolve_code_offset(link_id.into());
                            format!("label = \"VAR:{}\"", v)
                        }
                    }
                }
            )
        );
        println!("saved graph {:?}", filename);
        std::fs::write(filename, s).unwrap();
    }

    pub fn flow_graph(&self, filename: &str, b: &NB) -> Result<()> {
        crate::flatten_graph::flow_graph(self, &self.blocks, filename, b)
    }

    pub fn dump_scopes(&self) {
        petgraph::dot::Dot::with_config(&self.scopes.0, &[petgraph::dot::Config::EdgeNoLabel]);
    }

    pub fn dump_variants(&self, b: &NB) {
        for (index, v) in self.variants.variants.iter().enumerate() {
            let variant_id = VariantId::new(index);
            let name = b.labels.r(v.name.into());
            println!("[{}] Variant: {:?}", variant_id, (name, v));
        }
    }

    pub fn block_graph(&self, filename: &str, _b: &NB) {
        use petgraph::dot::{Config, Dot};
        let g = self.blocks.0.filter_map(
            |_n_index, n| Some(n.clone()),
            |_e_index, e| {
                if let Successor::Jump = e {
                    Some(e.clone())
                } else {
                    None
                }
            },
        );

        let num = petgraph::algo::connected_components(&g);
        println!("components: {}", num);

        let s = format!(
            "{:?}",
            Dot::with_attr_getters(
                &g,
                &[Config::NodeNoLabel],
                &|_, _er| String::new(),
                &|_, (index, _block)| {
                    let block_id: BlockId = BlockId::new(index.index());
                    let block = self.blocks.get_block(block_id);
                    if block.dead {
                        // block marked dead
                        format!("label = \"B{:?}:dead\"", index.index(),)
                    } else {
                        if let Some(link_id) = self.block_links.get(&block_id) {
                            let entry = self.get_link_entry(*link_id);
                            if entry.value_id.is_some() {
                                let v = self.resolve_code_offset(block_id.into());
                                // block found
                                format!("label = \"B{:?}:{}\"", index.index(), v)
                            } else {
                                // block is not included in our list
                                format!("label = \"B{:?}:oob\"", index.index(),)
                            }
                        } else {
                            // block not found
                            // this should never happen
                            // it does happen in error cases, like unclaimed labels
                            format!("label = \"B{:?}:?\"", index.index(),)
                            //unreachable!();
                        }
                    }
                }
            )
        );
        println!("saved graph {:?}", filename);
        std::fs::write(filename, s).unwrap();
    }
}
