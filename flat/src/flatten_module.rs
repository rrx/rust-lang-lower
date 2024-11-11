use compile_core::{AstType, LinkOptions, Literal, Span, SpanId, StringKey, VarDefinitionSpace};
//use petgraph::visit::EdgeRef;
use std::collections::HashMap;

use std::convert::Into;

use crate::{
    BlockGraph, BlockId, CodeEntry, CodeOffset, CodeRow, Flatten, ICodeModule, LCode, LinkId,
    NodeBuilder as NB, ScopeGraph, ScopeId, ScopeType, StringLabel, Successor, ValueId,
};

use tabled::{settings::Style, Table};

#[derive(Debug, Clone)]
pub struct ModuleEntry {
    value_id: ValueId,
    next: ValueId,
    //prev: ValueId,
    pub(super) code: LCode,
    name: Option<StringKey>,
    link: Option<LinkId>,
    block_id: BlockId,
    scope_id: ScopeId,
    ty: AstType,
    span_id: SpanId,
    mem: VarDefinitionSpace,
    scope_type: ScopeType,
}

impl ModuleEntry {
    pub fn from_code_entry(
        value_id: ValueId,
        next: ValueId,
        //prev: ValueId,
        scope_id: ScopeId,
        scope_type: ScopeType,
        entry: CodeEntry,
    ) -> ModuleEntry {
        Self {
            value_id,
            next,
            //prev,
            scope_id,
            scope_type,
            code: entry.code,
            name: entry.name,
            link: entry.link,
            block_id: entry.block_id,
            ty: entry.ty,
            span_id: entry.span_id,
            mem: entry.mem,
        }
    }
}

pub struct FlattenModule {
    entries: Vec<ModuleEntry>,
    link_map: HashMap<LinkId, ValueId>,
    pub(super) block_map: HashMap<BlockId, ValueId>,
    functions: HashMap<StringKey, LinkId>,
    statics: HashMap<StringKey, Literal>,
    pub(super) link: LinkOptions,
    pub(super) gblocks: BlockGraph,
    pub scopes: ScopeGraph,
}

impl ICodeModule for FlattenModule {
    fn shared_libraries(&self) -> Vec<String> {
        self.link.shared_libraries()
    }

    fn lookup_name(&self, name: &StringKey) -> Option<LinkId> {
        self.functions.get(name).cloned()
    }

    fn get_span_id(&self, value_id: ValueId) -> SpanId {
        let entry = self.get_entry(value_id);
        entry.span_id
    }

    fn get_name(&self, offset: CodeOffset) -> Option<StringLabel> {
        let value_id = self.resolve_code_offset(offset);
        self.get_entry(value_id).name.map(|n| n.into())
    }

    fn get_code(&self, value_id: ValueId) -> &LCode {
        &self.get_entry(value_id).code
    }

    fn get_next(&self, value_id: ValueId) -> Option<ValueId> {
        let entry = self.get_entry(value_id);
        if entry.next != value_id {
            Some(entry.next)
        } else {
            None
        }
    }

    /*
    fn get_prev(&self, value_id: ValueId) -> Option<ValueId> {
        let entry = self.get_entry(value_id);
        if entry.prev != value_id {
            Some(entry.prev)
        } else {
            None
        }
    }
    */

    fn get_block_successors(&self, entry_id: ValueId) -> Vec<(Successor, CodeOffset)> {
        let entry = self.get_entry(entry_id);
        let block_id = entry.block_id;
        self.gblocks.get_block_successors(block_id)
    }

    fn get_type(&self, v: CodeOffset) -> AstType {
        let value_id = self.resolve_code_offset(v);
        let entry = self.get_entry(value_id);
        entry.clone().ty
    }

    fn get_entry_id(&self, value_id: ValueId) -> ValueId {
        let block_id = self.get_entry(value_id).block_id;
        *self
            .block_map
            .get(&block_id)
            .expect(&format!("Unable to find block {}", block_id))
    }

    fn is_in_static_scope(&self, offset: CodeOffset) -> bool {
        let value_id = self.resolve_code_offset(offset);
        let entry = self.get_entry(value_id);
        entry.scope_type == ScopeType::Static
    }

    fn get_mem(&self, offset: CodeOffset) -> &VarDefinitionSpace {
        let value_id = self.resolve_code_offset(offset);
        &self.get_entry(value_id).mem
    }

    fn resolve_code_offset(&self, code_offset: CodeOffset) -> ValueId {
        match code_offset {
            CodeOffset::Value(v) => v,
            CodeOffset::Link(v) => *self.link_map.get(&v).unwrap(),
            CodeOffset::Block(block_id) => *self
                .block_map
                .get(&block_id)
                .expect(&format!("Missing block {}", block_id)),
        }
    }

    fn get_entry_id_from_block_id(&self, block_id: BlockId) -> ValueId {
        self.resolve_code_offset(block_id.into())
    }

    fn code_count(&self) -> usize {
        self.entries.len()
    }

    fn dump_code_table(&self, filename: &str, b: &mut NB) {
        let mut rows = vec![];
        for entry in self.entries.iter() {
            if let Some(row) = self.get_code_row(entry.value_id, b) {
                rows.push(row);
            } else {
                println!("Unable to load entry: {}", entry.value_id);
            }
        }
        let s = Table::new(rows).with(Style::sharp()).to_string();
        println!("{}", s);
        std::fs::write(filename, s).unwrap();
    }
}

impl FlattenModule {
    pub fn new() -> Self {
        Self {
            entries: vec![],
            link: LinkOptions::new(),
            link_map: HashMap::new(),
            functions: HashMap::new(),
            statics: HashMap::new(),
            block_map: HashMap::new(),
            gblocks: BlockGraph::new(),
            scopes: ScopeGraph::new(),
        }
    }

    pub fn dump(&self, _b: &NB) {
        petgraph::dot::Dot::with_config(&self.scopes.0, &[petgraph::dot::Config::EdgeNoLabel]);
    }

    pub fn from_builder(mut flatten: Flatten, b: &mut NB) -> Self {
        // we want to output the blocks in a particular order
        // we use DFS post order search on each function, to ensure that the leaf
        // nodes show up last, such as the return block
        // This seems to create a nice ordering.

        let blocks = flatten.blocks.post_order_blocks();

        let mut m = FlattenModule::new();
        m.link = flatten.link.clone();
        for block_id in flatten.blocks.graph_get_entries() {
            let block = flatten.blocks.get_block(block_id);
            let label_link_id = block.entry.unwrap();
            let entry = flatten.get_entry(label_link_id).clone();
            let ty = flatten.get_type(label_link_id).clone();
            assert_eq!(entry.mem, VarDefinitionSpace::Static);

            if let Some(key) = entry.name {
                m.functions.insert(key, label_link_id);
            }
        }

        let mut value_count = 0;
        for index in blocks.into_iter() {
            let block_id = index.into();
            let block = flatten.blocks.get_block(block_id);
            let entry_id = block.entry.unwrap();

            let mut entries = vec![];
            let mut v = entry_id;
            loop {
                let entry = flatten.get_entry(v).clone();
                let next = entry.next;
                entries.push(entry);
                if next == v {
                    break;
                } else {
                    v = next;
                }
            }

            let mut index = 0;
            for mut entry in entries.into_iter() {
                if let Some(ty) = b.types.u.resolve(&entry.ty) {
                    entry.ty = ty;
                }

                if entry.mem == VarDefinitionSpace::Static {
                    match &entry.code {
                        LCode::Val(lit) => {
                            m.statics.insert(entry.name.unwrap(), lit.clone());
                        }
                        _ => (),
                    }
                }

                let v = ValueId(value_count);
                let mut next = v;
                //let mut prev = v;
                //if index != 0 {
                //prev = ValueId(value_count - 1);
                //}
                let scope_id = block.scope_id;
                let scope = flatten.scopes.get_scope(scope_id);
                let scope_type = scope.scope_type;
                //
                let is_term = entry.code.is_term();
                //if !is_term {
                if index < block.len() - 1 {
                    next = ValueId(value_count + 1);
                } else if index == block.len() - 1 && !is_term && scope_type != ScopeType::Static {
                    b.push_error(&format!("Unterminated Block: {}", block_id), entry.span_id);
                }

                let mentry =
                    ModuleEntry::from_code_entry(v, next, scope_id, scope.scope_type, entry);
                m.add(mentry);
                value_count += 1;
                index += 1;
            }
        }
        m.gblocks = flatten.blocks;
        m.find_dead_blocks(b);
        m
    }

    pub fn type_inference(&mut self, b: &mut NB) {
        b.types.dump();
        let mut unresolved = vec![];
        for entry in self.entries.iter_mut() {
            if !entry.ty.is_unknown() {
                continue;
            }
            if let Some(ty) = b.types.u.resolve(&entry.ty) {
                entry.ty = ty;
            }

            if let AstType::Variable(_) = &entry.ty {
                unresolved.push(&entry.ty);
            }
        }

        let mut args = vec![];
        while unresolved.len() > 0 {
            let ty = unresolved.pop().unwrap();

            // if it resolves, then skip to the next
            if let Some(_) = b.types.u.resolve(&ty) {
                continue;
            }

            // unify with an arg
            let arg = b.types.fresh_type_arg();
            b.types.u.unify(&ty, &arg).unwrap();
            args.push(arg);
        }

        if args.len() > 0 {
            println!("Module unified with {} args", args.len());
        }
    }

    pub fn type_inference_enforce(&mut self, b: &mut NB) {
        b.types.dump();
        for entry in self.entries.iter_mut() {
            if !entry.ty.is_unknown() {
                continue;
            }

            if let Some(ty) = b.types.u.resolve(&entry.ty) {
                /*
                b.push_warning(
                    &format!("Late Unresolved Type: {}=>{}", &entry.ty, &ty),
                    entry.span_id,
                );
                */
                entry.ty = ty;
            } else {
                b.push_error(&format!("Unresolved Type: {}", &entry.ty), entry.span_id);
            }
        }
    }

    pub fn find_dead_blocks(&mut self, b: &mut NB) {
        let dead_blocks = self.gblocks.find_dead_blocks_from_graph();
        for block_id in dead_blocks {
            let v = self.get_entry_id_from_block_id(block_id);
            let span_id = self.get_span_id(v);
            b.push_warning(&format!("Dead Block: {}", block_id), span_id);
        }
    }

    pub fn add(&mut self, mentry: ModuleEntry) {
        self.link_map.insert(mentry.link.unwrap(), mentry.value_id);
        if let LCode::Label = mentry.code {
            self.block_map.insert(mentry.block_id, mentry.value_id);
        }
        self.entries.push(mentry);
    }

    pub fn get_entry(&self, value_id: ValueId) -> &ModuleEntry {
        self.entries.get(value_id.index()).unwrap()
    }

    pub fn get_span(&self, value_id: ValueId, b: &NB) -> Span {
        let span_id = self.get_span_id(value_id);
        b.spans.lookup(span_id)
    }

    pub fn get_code_by_link(&self, link_id: LinkId) -> &LCode {
        let value_id = self.link_map.get(&link_id).unwrap();
        self.get_code(*value_id)
    }

    pub fn get_code_row(&self, v: ValueId, b: &mut NB) -> Option<CodeRow> {
        let entry = self.get_entry(v);
        let code = self.get_code(v);
        //let ty = self.get_type(v.into());

        let mem = self.get_mem(v.into());
        let block_id = entry.block_id;
        let block = self.gblocks.node_weight(block_id.into()).unwrap();
        //println!("block: {:?}", (block_id, block, v, entry));

        //let next = self.get_next(v).unwrap_or(v).index();
        //let prev = self.get_prev(v).unwrap_or(v).index();
        //println!("row: {}, {:?}", v, (self.entries.len()));
        let entry_id = self.get_entry_id(v);

        let r_ty = if let Some(r_ty) = b.types.u.resolve(&entry.ty) {
            r_ty
        } else {
            entry.ty.clone()
        };
        //println!("X: {} => {}", &entry.ty, &r_ty);

        //let is_unknown = r_ty.as_ref().map(|ty| ty.is_unknown()).unwrap_or(true);
        //let s_ty = format!("{}", &r_ty.unwrap_or(ty)); //AstType::Error));
        let is_unknown = r_ty.is_unknown();
        let s_ty = format!("{}", &r_ty);

        Some(CodeRow {
            pos: v.index(),
            link: entry.link.unwrap().index(),
            next: entry.next.index(),
            //prev: entry.prev.index(),
            value: self.code_to_string(v, b),
            //ty: ty.clone(),
            ty: s_ty,
            //r_ty: r_ty.unwrap_or(AstType::Error),
            mem: format!("{:?}", mem),
            name: self
                .get_name(v.into())
                .map(|key| b.labels.r(key))
                .unwrap_or("".to_string())
                .to_string(),
            span_id: self.get_span_id(v).index(),
            scope_id: entry.scope_id.index(),
            entry_id: entry_id.index(),
            block_id: block_id.index(),
            term: code.is_term(),
            dead: block.dead,
            unknown: is_unknown,
        })
    }
}
