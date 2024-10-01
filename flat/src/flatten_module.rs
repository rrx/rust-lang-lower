use compile_core::{AstType, LinkOptions, Literal, Span, SpanId, StringKey, VarDefinitionSpace};
use petgraph::visit::EdgeRef;
use std::collections::{HashMap, HashSet};

use std::convert::Into;

use crate::{
    BlockGraph, BlockId, CodeEntry, CodeOffset, CodeRow, Flatten, FlattenEnvironment, ICodeModule,
    LCode, LinkId, NodeBuilder as NB, ScopeId, ScopeType, StringLabel, Successor, ValueId,
};

use tabled::{settings::Style, Table};

#[derive(Debug, Clone)]
pub struct ModuleEntry {
    value_id: ValueId,
    next: ValueId,
    prev: ValueId,
    code: LCode,
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
        prev: ValueId,
        scope_id: ScopeId,
        scope_type: ScopeType,
        entry: CodeEntry,
    ) -> ModuleEntry {
        Self {
            value_id,
            next,
            prev,
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
    block_map: HashMap<BlockId, ValueId>,
    functions: HashMap<StringKey, LinkId>,
    statics: HashMap<StringKey, Literal>,
    pub(super) link: LinkOptions,
    pub(super) gblocks: BlockGraph,
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

    fn get_prev(&self, value_id: ValueId) -> Option<ValueId> {
        let entry = self.get_entry(value_id);
        if entry.prev != value_id {
            Some(entry.prev)
        } else {
            None
        }
    }

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
            let row = self.get_code_row(entry.value_id, b);
            rows.push(row);
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
        }
    }

    pub fn dump(&self, fenv: &FlattenEnvironment, _b: &NB) {
        petgraph::dot::Dot::with_config(&fenv.scopes.0, &[petgraph::dot::Config::EdgeNoLabel]);
    }

    pub fn from_builder(mut flatten: Flatten, fenv: &FlattenEnvironment, b: &mut NB) -> Self {
        // we want to output the blocks in a particular order
        // we use DFS post order search on each function, to ensure that the leaf
        // nodes show up last, such as the return block
        // This seems to create a nice ordering.

        let mut dfs = petgraph::visit::Dfs::new(&flatten.blocks.0, BlockId(0).into());
        let mut blocks = vec![BlockId(0).into()];

        let mut function_entries = vec![];
        let mut template_entries = vec![];
        while let Some(visited) = dfs.next(&flatten.blocks.0) {
            for edge in flatten.blocks.0.edges(visited) {
                match *edge.weight() {
                    Successor::FunctionDeclaration => {
                        function_entries.push(edge.target());
                    }
                    Successor::TemplateDeclaration => {
                        template_entries.push(edge.target());
                    }
                    _ => (), //_ => unreachable!("{:?}", edge.weight())
                }
            }
        }

        let mut value_count = 0;
        for index in function_entries.iter().chain(template_entries.iter()) {
            let mut seq = vec![];
            let mut dfs = petgraph::visit::DfsPostOrder::new(&flatten.blocks.0, *index);
            while let Some(index) = dfs.next(&flatten.blocks.0) {
                seq.push(index);
            }
            blocks.extend(seq.into_iter().rev());
        }

        // inject builtin prototypes
        let print_index = b.labels.s("print_index".into());
        let print_float = b.labels.s("print_float".into());
        let print_bool = b.labels.s("print_bool".into());
        let builtins = vec![
            (print_index, AstType::Int, AstType::Unit),
            (print_float, AstType::Float, AstType::Unit),
            (print_bool, AstType::Bool, AstType::Unit),
        ];
        let unknown = b.spans.get_span_unknown();
        for (key, var_ty, ret_ty) in builtins {
            let func_ty = AstType::func(vec![var_ty], ret_ty);
            flatten.push_code(
                LCode::DeclareFunction(None),
                func_ty,
                Some(key),
                unknown,
                VarDefinitionSpace::Static,
                fenv,
            );
        }

        let mut m = FlattenModule::new();
        m.link = flatten.link.clone();
        for index in function_entries.iter() {
            let block_id = (*index).into();
            let block = flatten.blocks.get_block(block_id);
            let label_link_id = block.links.first().unwrap();
            let entry = flatten.get_entry(*label_link_id).clone();
            let ty = flatten.get_type(*label_link_id).clone();
            /*
            let name = entry
                .name
                .map(|key| b.labels.r(key.into()))
                .unwrap_or("".to_string());
            println!("X: {:?}", entry);
            println!("X: {}, {}", name, &ty);
            */
            assert_eq!(entry.mem, VarDefinitionSpace::Static);

            if let Some(key) = entry.name {
                m.functions.insert(key, *label_link_id);
            }

            flatten.push_code(
                LCode::DeclareFunction(Some(block_id)),
                ty,
                entry.name,
                entry.span_id,
                entry.mem,
                fenv,
            );
        }

        for index in blocks.into_iter() {
            let block_id = index.into();
            let block = flatten.blocks.get_block(block_id);
            for (index, link_id) in block.links.iter().enumerate() {
                let mut entry = flatten.get_entry(*link_id).clone();
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
                let mut prev = v;
                if index != 0 {
                    prev = ValueId(value_count - 1);
                }
                if index < block.links.len() - 1 {
                    next = ValueId(value_count + 1);
                }
                let scope_id = block.scope_id;
                let scope = fenv.get_scope(scope_id);

                if index == block.links.len() - 1
                    && !entry.code.is_term()
                    && scope.scope_type != ScopeType::Static
                {
                    b.push_error(&format!("Unterminated Block: {}", block_id), entry.span_id);
                }

                let mentry =
                    ModuleEntry::from_code_entry(v, next, prev, scope_id, scope.scope_type, entry);
                m.add(mentry);
                value_count += 1;
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

        /*

        for (index, entry) in self.entries.iter().enumerate() {
            let _v = ValueId::new(index as u32);
            /*
            if let LCode::Label = entry.code {
                //let v_target = self.resolve_code_offset(v);
                //let t = self.get_entry(v_target);
                if let ty = b.types.u.resolve(&entry.ty) {
                    if let AstType::Func(arg_ty, ret_ty) = entry.ty {
                        let fields
                        if arg_ty.fields() == vec![
                        if *arg_ty == AstType::Struct(vec![(AstType::Unit]) {
                        }
                    }

                    entry.ty = ty;
                } else {
                    b.push_error(&format!("Unresolved Type: {}", &entry.ty), entry.span_id);
                }

            } else
                */
            /*
            if let LCode::Jump(target) = entry.code {
                let v_target = self.resolve_code_offset(target);
                let t = self.get_entry(v_target);

                let entry_ty = if let AstType::Func(arg, _ret) = &entry.ty {
                    arg
                } else {
                    unreachable!()
                };

                let t_ty = if let AstType::Func(arg, _ret) = &t.ty {
                    arg
                } else {
                    unreachable!()
                    //&t.ty
                };
                if b.types.u.unify(entry_ty, t_ty).is_err() {
                    b.push_error(
                        &format!("Jump Type Mismatch: from: {}, target: {}", entry_ty, t_ty),
                        entry.span_id,
                    );
                }
            }
            */
        }
        */
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
        let mut dfs = petgraph::visit::Dfs::new(&self.gblocks.0, BlockId(0).into());
        let mut entries = HashSet::new();
        while let Some(visited) = dfs.next(&self.gblocks.0) {
            for edge in self.gblocks.edges(visited) {
                if Successor::FunctionDeclaration == *edge.weight() {
                    entries.insert(edge.target());
                }
            }
        }

        let subgraph = self.gblocks.filter_map(
            |_n_index, n| Some(n.clone()),
            |_e_index, e| {
                if let Successor::Jump = e {
                    Some(e.clone())
                } else {
                    None
                }
            },
        );

        for entry in entries {
            let mut reachable = HashSet::new();
            let mut all = HashSet::new();
            reachable.insert(entry.into());
            all.insert(entry.into());

            let mut dfs = petgraph::visit::Dfs::new(&subgraph, entry.into());
            while let Some(visited) = dfs.next(&self.gblocks.0) {
                for edge in self.gblocks.edges(visited) {
                    let b: BlockId = edge.target().into();
                    all.insert(b);
                }
            }

            let mut dfs = petgraph::visit::Dfs::new(&subgraph, entry.into());
            while let Some(visited) = dfs.next(&subgraph) {
                for edge in subgraph.edges(visited) {
                    if Successor::Jump == *edge.weight() {
                        let b: BlockId = edge.target().into();
                        reachable.insert(b);
                    }
                }
            }
            let dead = all.difference(&reachable);
            //println!("[{:?}] Dead: {:?}", entry, &dead);
            //println!("[{:?}] All: {:?}", entry, &all);
            //println!("[{:?}] Reachable: {:?}", entry, &reachable);
            for block_id in dead {
                let index = (*block_id).into();
                let block = self.gblocks.node_weight_mut(index).unwrap();
                block.dead = true;
                let v = self.get_entry_id_from_block_id(*block_id);
                let span_id = self.get_span_id(v);
                b.push_warning(&format!("Dead Block: {}", block_id), span_id);
            }
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

    pub fn get_code_row(&self, v: ValueId, b: &mut NB) -> CodeRow {
        let entry = self.get_entry(v);
        let code = self.get_code(v);
        //let ty = self.get_type(v.into());

        let mem = self.get_mem(v.into());
        //let next = self.get_next(v).unwrap_or(v).index();
        //let prev = self.get_prev(v).unwrap_or(v).index();
        //println!("row: {}, {:?}", v, (self.entries.len()));
        let entry_id = self.get_entry_id(v);
        let block_id = entry.block_id;
        let block = self.gblocks.node_weight(block_id.into()).unwrap();

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

        CodeRow {
            pos: v.index(),
            link: entry.link.unwrap().index(),
            //next: 0,
            //prev: 0,
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
        }
    }
}
