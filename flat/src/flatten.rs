use anyhow::Error;
use anyhow::Result;
use compile_core::{
    Argument,
    AssignTarget,
    Ast,
    AstNode,
    AstType,
    //BinaryOperation, BuiltinId, ControlFlowMarker,
    Lambda,
    LinkOptions,
    //Literal,
    ParameterNode,
    Span,
    SpanId,
    StringKey,
    //UnaryOperation,
    VarDefinitionSpace,
};
use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use std::collections::HashMap;
use std::convert::From;
use std::convert::Into;

use crate::{
    scope::Data,
    BlockId,
    BlockifyError,
    Builtin,
    CodeOffset,
    CodeRow,
    FlattenEnvironment,
    ICodeModule,
    LCode,
    LinkId,
    NodeBuilder,
    ScopeId,
    //NodeBuilder as NB,
    ScopeType,
    StringLabel,
    Successor,
    TemplateId,
    ValueId,
};

use tabled::{
    settings::{
        //object::Rows,
        //Border,
        Style,
    },
    Table,
};

pub type BlockGraph = DiGraph<IRBlock, Successor>;

impl Into<NodeIndex> for BlockId {
    fn into(self) -> NodeIndex {
        NodeIndex::new(self.index())
        //BlockId(self.index() as u32)
    }
}

impl From<NodeIndex> for BlockId {
    fn from(item: NodeIndex) -> Self {
        Self(item.index() as u32)
    }
}

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

#[derive(Debug, Clone)]
pub struct CodeEntry {
    code: LCode,
    name: Option<StringKey>,
    link: Option<LinkId>,
    block_id: BlockId,
    ty: AstType,
    span_id: SpanId,
    mem: VarDefinitionSpace,
}

impl CodeEntry {
    pub fn new(
        block_id: BlockId,
        code: LCode,
        ty: AstType,
        name: Option<StringKey>,
        span_id: SpanId,
        mem: VarDefinitionSpace,
    ) -> Self {
        Self {
            block_id,
            code,
            name,
            link: None,
            ty,
            span_id,
            mem,
        }
    }

    pub fn add_mem(mut self, mem: VarDefinitionSpace) -> Self {
        self.mem = mem;
        self
    }
}

pub struct IRBlock {
    stack: Vec<ScopeId>,
    ast: Option<AstNode>,
    next: Option<BlockId>,
    ret: Option<BlockId>,
    links: Vec<LinkId>,
}

impl IRBlock {
    pub fn new(stack: Vec<ScopeId>, ast: Option<AstNode>) -> Self {
        Self {
            stack,
            ast,
            links: vec![],
            ret: None,
            next: None,
        }
    }

    pub fn push(&mut self, link_id: LinkId) {
        self.links.push(link_id);
    }

    pub fn add_next(&mut self, block_id: BlockId) {
        self.next = Some(block_id);
    }

    pub fn add_ret(&mut self, block_id: BlockId) {
        self.ret = Some(block_id);
    }
}

#[derive(Debug)]
pub struct FlattenResult {
    link_id: Option<LinkId>,
    block_id: BlockId,
    ty: AstType,
    is_term: bool,
}

impl FlattenResult {
    pub fn new(block_id: BlockId, link_id: Option<LinkId>, ty: AstType, is_term: bool) -> Self {
        Self {
            block_id,
            link_id,
            ty,
            is_term,
        }
    }
}

pub struct FlattenModule {
    entries: Vec<ModuleEntry>,
    link_map: HashMap<LinkId, ValueId>,
    block_map: HashMap<BlockId, ValueId>,
    succ: HashMap<BlockId, Vec<(Successor, CodeOffset)>>,
    link: LinkOptions,
    gblocks: BlockGraph,
}

impl ICodeModule for FlattenModule {
    fn shared_libraries(&self) -> Vec<String> {
        self.link.shared_libraries()
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
        let index = NodeIndex::new(block_id.index());
        self.gblocks
            .neighbors_directed(index, petgraph::Direction::Outgoing)
            .map(|i| (Successor::BlockScope, BlockId(i.index() as u32).into()))
            .collect::<Vec<_>>()
    }

    fn get_type(&self, v: CodeOffset) -> AstType {
        let value_id = self.resolve_code_offset(v);
        let entry = self.get_entry(value_id);
        entry.clone().ty
    }

    fn get_entry_id(&self, value_id: ValueId) -> ValueId {
        let block_id = self.get_entry(value_id).block_id;
        *self.block_map.get(&block_id).unwrap()
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
            CodeOffset::Block(block_id) => *self.block_map.get(&block_id).unwrap(),
        }
    }

    fn get_entry_id_from_block_id(&self, block_id: BlockId) -> ValueId {
        self.resolve_code_offset(block_id.into())
    }

    fn code_count(&self) -> usize {
        self.entries.len()
    }

    fn dump(&self, b: &NodeBuilder) {
        let mut rows = vec![];
        for entry in self.entries.iter() {
            let row = self.get_code_row(entry.value_id, b);
            rows.push(row);
        }
        let s = Table::new(rows).with(Style::sharp()).to_string();
        println!("{}", s);
        save_graph(self, "out.dot", b);
    }
}

impl FlattenModule {
    pub fn new() -> Self {
        Self {
            entries: vec![],
            link: LinkOptions::new(),
            link_map: HashMap::new(),
            block_map: HashMap::new(),
            succ: HashMap::new(),
            gblocks: BlockGraph::new(),
        }
    }

    pub fn add(&mut self, mentry: ModuleEntry) {
        self.link_map.insert(mentry.link.unwrap(), mentry.value_id);
        if let LCode::Label(_, _) = mentry.code {
            self.block_map.insert(mentry.block_id, mentry.value_id);
        }
        self.entries.push(mentry);
    }

    pub fn get_entry(&self, value_id: ValueId) -> &ModuleEntry {
        self.entries.get(value_id.index()).unwrap()
    }

    pub fn get_span(&self, value_id: ValueId, b: &NodeBuilder) -> Span {
        let span_id = self.get_span_id(value_id);
        b.spans.lookup(span_id)
    }

    pub fn get_code_by_link(&self, link_id: LinkId) -> &LCode {
        let value_id = self.link_map.get(&link_id).unwrap();
        self.get_code(*value_id)
    }

    pub fn get_code_row(&self, v: ValueId, b: &NodeBuilder) -> CodeRow {
        let entry = self.get_entry(v);
        let code = self.get_code(v);
        let ty = self.get_type(v.into());
        let mem = self.get_mem(v.into());
        //let next = self.get_next(v).unwrap_or(v).index();
        //let prev = self.get_prev(v).unwrap_or(v).index();
        let entry_id = self.get_entry_id(v);
        let block_id = entry.block_id;

        CodeRow {
            pos: v.index(),
            link: entry.link.unwrap().index(),
            //next: 0,
            //prev: 0,
            value: self.code_to_string(v, b),
            ty,
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
        }
    }
}

pub struct Flatten {
    module_key: Option<StringKey>,
    ast_blocks: Vec<BlockId>,
    link: LinkOptions,
    entries: Vec<CodeEntry>,
    gblocks: BlockGraph,
    templates: Vec<Lambda>,
}

impl Flatten {
    pub fn new() -> Self {
        Self {
            module_key: None,
            ast_blocks: vec![],
            entries: vec![],
            gblocks: BlockGraph::new(),
            link: LinkOptions::new(),
            templates: vec![],
        }
    }

    pub fn dump_scope(&self, block_id: BlockId, fenv: &FlattenEnvironment, b: &NodeBuilder) {
        println!("DumpScope");
        let block = self.get_block(block_id);
        for scope_id in block.stack.iter() {
            let scope = fenv.get_scope(*scope_id);
            scope.dump(b);
        }
    }

    pub fn resolve_name(
        &self,
        block_id: BlockId,
        name: StringKey,
        fenv: &FlattenEnvironment,
    ) -> Option<Data> {
        // resolve scope through the tree, starting at the current scope
        let block = self.get_block(block_id);
        for scope_id in block.stack.iter().rev() {
            let scope = fenv.get_scope(*scope_id);
            if let Some(data) = scope.names.get(&name) {
                return Some(data.clone());
            }
        }
        None
    }

    pub fn resolve_lambda_scope(
        &self,
        block_id: BlockId,
        name: StringLabel,
        fenv: &FlattenEnvironment,
    ) -> Option<ScopeId> {
        // resolve scope through the tree, starting at the current scope
        let block = self.get_block(block_id);
        for scope_id in block.stack.iter().rev() {
            let scope = fenv.get_scope(*scope_id);
            if let Some(_data) = scope.lambdas.get(&name) {
                return Some(*scope_id);
            }
        }
        None
    }

    pub fn module(self, fenv: &FlattenEnvironment, _b: &NodeBuilder) -> FlattenModule {
        assert!(self.ast_blocks.is_empty());
        let mut m = FlattenModule::new();

        let mut value_count = 0;
        let mut dfs = petgraph::visit::Dfs::new(&self.gblocks, NodeIndex::new(0));
        while let Some(index) = dfs.next(&self.gblocks) {
            let block_id = BlockId(index.index() as u32);
            println!("o: {:?}", index);
            let block = self.get_block(block_id);

            for (index, link_id) in block.links.iter().enumerate() {
                let entry = self.get_entry(*link_id).clone();
                let v = ValueId(value_count);
                let mut next = v;
                let mut prev = v;
                if index != 0 {
                    prev = ValueId(value_count - 1);
                }
                if index < block.links.len() - 1 {
                    next = ValueId(value_count + 1);
                }
                let scope_id = block.stack.last().unwrap();
                let scope = fenv.get_scope(*scope_id);
                let mentry =
                    ModuleEntry::from_code_entry(v, next, prev, *scope_id, scope.scope_type, entry);
                m.add(mentry);
                value_count += 1;
            }
        }
        m.gblocks = self.gblocks;

        m
    }

    pub fn dump_ast(&self, b: &NodeBuilder) {
        for block_id in self.ast_blocks.iter() {
            let block = self.get_block(*block_id);
            for link_id in block.links.iter() {
                let entry = self.get_entry(*link_id);
                let name = entry.name.map(|n| b.labels.r(n.into()));
                println!(
                    "AST: B: {}, N: {:?}, C: {:?}, T: {:?}, A: {:?}",
                    block_id,
                    name,
                    entry.code,
                    entry.ty,
                    block.ast.as_ref().map(|a| &a.node).unwrap()
                );
            }
        }
    }

    pub fn flatten_module(
        node: AstNode,
        fenv: &mut FlattenEnvironment,
        b: &mut NodeBuilder,
    ) -> Result<Self> {
        let mut f = Self::new();
        if let Ast::Module(key, body) = node.node {
            f.module_key = Some(key);
            let static_scope = fenv.new_scope(ScopeType::Static);
            let stack = vec![static_scope];
            let block_id = f.new_ast_block(None, stack);
            let code = LCode::Label(0, 0);
            let entry = CodeEntry::new(
                block_id,
                code,
                AstType::Unit,
                Some(key),
                node.span_id,
                VarDefinitionSpace::Static,
            );
            f.push_entry_with_link(entry);
            fenv.static_block = Some(block_id);
            fenv.static_scope = Some(static_scope);
            for ast in body.to_vec() {
                let _ = f.flatten(block_id, ast, fenv, b)?;
            }
            Ok(f)
        } else {
            unreachable!()
        }
    }

    pub fn step(&mut self, fenv: &mut FlattenEnvironment, b: &mut NodeBuilder) -> Result<bool> {
        if let Some(block_id) = self.ast_blocks.pop() {
            let block = self.get_block_mut(block_id);
            let ast = block.ast.take().unwrap();
            self.flatten(block_id, ast, fenv, b)?;
        }
        Ok(self.ast_blocks.is_empty())
    }

    pub fn run_loop(&mut self, fenv: &mut FlattenEnvironment, b: &mut NodeBuilder) -> Result<()> {
        loop {
            if self.step(fenv, b)? {
                break;
            }
        }
        Ok(())
    }

    pub fn push(&mut self, mut entry: CodeEntry) -> LinkId {
        let index = self.entries.len();
        let link_id = LinkId(index as u32);
        entry.link = Some(link_id);
        self.entries.push(entry);
        link_id
    }

    pub fn push_link(&mut self, block_id: BlockId, link_id: LinkId) {
        self.get_block_mut(block_id).push(link_id);
    }

    pub fn push_entry_with_link(&mut self, entry: CodeEntry) -> LinkId {
        let block_id = entry.block_id;
        let link_id = self.push(entry);
        self.get_block_mut(block_id).push(link_id);
        link_id
    }

    pub fn new_ast_block(&mut self, ast: Option<AstNode>, stack: Vec<ScopeId>) -> BlockId {
        let ast = if let Some(ast) = ast {
            Some(Ast::Sequence(ast.to_vec()).into())
        } else {
            None
        };
        let ir_block = IRBlock::new(stack, ast);
        let index = self.gblocks.add_node(ir_block);
        BlockId(index.index() as u32)
    }

    pub fn successor(
        &mut self,
        block_id: BlockId,
        ast: Option<AstNode>,
        scope_id: Option<ScopeId>,
        succ_type: Successor,
        ret: Option<BlockId>,
        next: Option<BlockId>,
    ) -> BlockId {
        //let block = self.get_block(block_id);
        let succ_block_id = self._successor(block_id, ast, scope_id, ret, next);
        self.gblocks
            .add_edge(block_id.into(), succ_block_id.into(), succ_type);
        succ_block_id
    }

    pub fn function_successor(
        &mut self,
        block_id: BlockId,
        ast: Option<AstNode>,
        ret: BlockId,
        fenv: &mut FlattenEnvironment,
    ) -> BlockId {
        let fun_scope_id = fenv.new_scope(ScopeType::Function);
        self._successor(block_id, ast, Some(fun_scope_id), Some(ret), Some(ret))
    }

    pub fn _successor(
        &mut self,
        block_id: BlockId,
        ast: Option<AstNode>,
        scope_id: Option<ScopeId>,
        ret: Option<BlockId>,
        next: Option<BlockId>,
    ) -> BlockId {
        let block = self.get_block(block_id);
        let mut stack = block.stack.clone();
        if let Some(scope_id) = scope_id {
            stack.push(scope_id);
        }
        let new_block_id = self.new_ast_block(ast, stack);
        let new_block = self.get_block_mut(new_block_id);
        new_block.ret = ret;
        new_block.next = next;
        new_block_id
    }

    pub fn get_block(&self, block_id: BlockId) -> &IRBlock {
        let index = NodeIndex::new(block_id.index());
        self.gblocks.node_weight(index).unwrap()
    }

    pub fn get_block_mut(&mut self, block_id: BlockId) -> &mut IRBlock {
        let index = NodeIndex::new(block_id.index());
        self.gblocks.node_weight_mut(index).unwrap()
    }

    pub fn get_entry(&self, link_id: LinkId) -> &CodeEntry {
        self.entries.get(link_id.index()).unwrap()
    }

    pub fn get_entry_mut(&mut self, link_id: LinkId) -> &mut CodeEntry {
        self.entries.get_mut(link_id.index()).unwrap()
    }

    pub fn push_template(&mut self, def: Lambda) -> TemplateId {
        let offset = self.templates.len();
        self.templates.push(def);
        TemplateId(offset as u32)
    }

    pub fn get_template(&mut self, template_id: TemplateId) -> &Lambda {
        self.templates.get(template_id.index()).unwrap()
    }

    fn flatten_sequence(
        &mut self,
        block_id: BlockId,
        mut seq: Vec<AstNode>,
        fenv: &mut FlattenEnvironment,
        b: &mut NodeBuilder,
    ) -> Result<FlattenResult> {
        let mut current_block_id = block_id;
        let mut ty = AstType::Unit;
        let mut link_id = None;
        let mut is_term = false;
        let mut span_id = b.spans.get_span_unknown();

        let mut d = seq.drain(..);
        loop {
            if let Some(ast) = d.next() {
                span_id = ast.span_id;
                if d.len() > 0 && ast.node.is_term() {
                    println!("term: {:?}", ast);
                    let next_seq = d.collect::<Vec<_>>();
                    let next_node = AstNode {
                        node: Ast::Sequence(next_seq),
                        span_id,
                    };
                    let next_block =
                        Ast::Block(b.fresh_block_name(), vec![], Box::new(next_node)).into();
                    println!("next_node: {:?}", next_block);
                    let next_r = self.flatten(current_block_id, next_block, fenv, b)?;
                    let next = Some(next_r.block_id);
                    let block = self.get_block_mut(current_block_id);
                    block.next = next;
                    let r = self.flatten(current_block_id, ast, fenv, b)?;
                    current_block_id = r.block_id;
                    ty = r.ty;
                    link_id = r.link_id;
                    is_term = r.is_term;
                    return Ok(FlattenResult::new(current_block_id, link_id, ty, is_term));
                }

                let r = self.flatten(current_block_id, ast, fenv, b)?;
                current_block_id = r.block_id;
                ty = r.ty;
                link_id = r.link_id;
                is_term = r.is_term;
            } else {
                break;
            }
        }

        if !is_term {
            let block = self.get_block(current_block_id);
            println!("missing term: {:?}", block.next);
            self.add_jump(current_block_id, block.next.unwrap(), vec![], span_id);
        }
        Ok(FlattenResult::new(current_block_id, link_id, ty, is_term))
    }

    pub fn add_return_block(
        &mut self,
        fun_block_id: BlockId,
        scope_id: ScopeId,
        return_type: AstType,
        b: &mut NodeBuilder,
    ) -> BlockId {
        let span_id = b.spans.get_span_unknown();
        let name = b.labels.s("ret");
        let args = match &return_type {
            AstType::Unit => vec![],
            _ => vec![return_type.clone()],
        };
        let ret_block_id = self.successor(
            fun_block_id,
            None,
            Some(scope_id),
            Successor::BlockScope,
            None,
            None,
        );

        let code = LCode::Label(args.len() as u8, 0);
        let entry = CodeEntry::new(
            ret_block_id,
            code,
            return_type.clone(),
            Some(name),
            span_id,
            VarDefinitionSpace::Reg,
        );
        self.push_entry_with_link(entry);

        let v_args = args
            .iter()
            .enumerate()
            .map(|(i, _arg)| {
                let code = LCode::Arg(i as u8);
                let name = b.labels.s(&format!("arg{}", i));
                let entry = CodeEntry::new(
                    ret_block_id,
                    code,
                    return_type.clone(),
                    Some(name),
                    span_id,
                    VarDefinitionSpace::Arg,
                );
                self.push_entry_with_link(entry)
            })
            .collect::<Vec<_>>();

        for link_id in v_args.iter() {
            let code = LCode::Link(*link_id);
            let entry = CodeEntry::new(
                ret_block_id,
                code,
                return_type.clone(),
                None,
                span_id,
                VarDefinitionSpace::Reg,
            );
            self.push_entry_with_link(entry);
        }

        let code = LCode::Return(v_args.len() as u8);
        let entry = CodeEntry::new(
            ret_block_id,
            code,
            AstType::Unit,
            None,
            span_id,
            VarDefinitionSpace::Reg,
        );
        self.push_entry_with_link(entry);
        ret_block_id
    }

    pub fn add_jump(
        &mut self,
        block_id: BlockId,
        target_id: BlockId,
        jump_args: Vec<(LinkId, AstType)>,
        span_id: SpanId,
    ) {
        let num_args = jump_args.len();
        for (link_id, ty) in jump_args.into_iter() {
            let code = LCode::Link(link_id);
            let entry = CodeEntry::new(block_id, code, ty, None, span_id, VarDefinitionSpace::Reg);
            self.push_entry_with_link(entry);
        }

        let code = LCode::Jump(target_id.into(), num_args as u8);
        let entry = CodeEntry::new(
            block_id,
            code,
            AstType::Unit,
            None,
            span_id,
            VarDefinitionSpace::Reg,
        );

        self.push_entry_with_link(entry);
    }

    pub fn add_function_call(
        &mut self,
        block_id: BlockId,
        fun_offset: CodeOffset,
        fun_ty: AstType,
        args: Vec<Argument>,
        span_id: SpanId,
        fenv: &mut FlattenEnvironment,
        b: &mut NodeBuilder,
    ) -> Result<FlattenResult> {
        if let AstType::Func(func_arg_types, ret) = &fun_ty {
            if func_arg_types.len() != args.len() {
                b.push_error(
                    &format!(
                        "Call arity mismatch: {}<=>{}",
                        func_arg_types.len(),
                        args.len()
                    ),
                    span_id,
                );
                return Err(Error::new(BlockifyError::Invalid));
            }

            let args_size = args.len() as u8;
            let mut values = vec![];
            let mut current_block_id = block_id;
            for (a, ty) in args.into_iter().zip(func_arg_types.iter()) {
                match a {
                    Argument::Positional(expr) => {
                        let r = self.flatten(current_block_id, *expr, fenv, b)?;
                        current_block_id = r.block_id;
                        values.push((r.link_id.unwrap(), ty.clone()));
                    }
                }
            }

            for (link_id, ty) in values {
                let code = LCode::Link(link_id);
                let entry = CodeEntry::new(
                    current_block_id,
                    code,
                    ty,
                    None,
                    span_id,
                    VarDefinitionSpace::Reg,
                );
                self.push_entry_with_link(entry);
            }

            let code = LCode::Call(fun_offset, args_size, 0);
            let entry = CodeEntry::new(
                current_block_id,
                code,
                *ret.clone(),
                None,
                span_id,
                VarDefinitionSpace::Default,
            );
            let link_id = self.push_entry_with_link(entry);
            Ok(FlattenResult::new(
                current_block_id,
                Some(link_id),
                *ret.clone(),
                false,
            ))
        } else {
            b.push_error(&format!("Type not function: {:?}", fun_ty), span_id);
            return Err(Error::new(BlockifyError::Invalid));
        }
    }

    fn add_block(
        &mut self,
        scope_id: ScopeId,
        parent_block_id: BlockId,
        args: &[AstType],
        kwargs: &[ParameterNode],
        ast: Option<AstNode>,
        ty: AstType,
        name: Option<StringKey>,
        succ_type: Successor,
        span_id: SpanId,
        mem: VarDefinitionSpace,
        ret: Option<BlockId>,
        next: Option<BlockId>,
        fenv: &mut FlattenEnvironment,
        b: &mut NodeBuilder,
    ) -> Result<BlockId> {
        let new_block_id =
            self.successor(parent_block_id, ast, Some(scope_id), succ_type, ret, next);
        let code = LCode::Label(args.len() as u8, kwargs.len() as u8);
        let entry = CodeEntry::new(new_block_id, code, ty, name, span_id, mem);
        self.push_entry_with_link(entry);

        for (i, p) in kwargs.iter().enumerate() {
            let ty = b.types.r(p.ty);
            let code = LCode::Arg(i as u8);
            let entry = CodeEntry::new(
                new_block_id,
                code,
                ty.clone(),
                Some(p.name),
                p.span_id,
                VarDefinitionSpace::Arg,
            );
            let link_id = self.push_entry_with_link(entry);
            fenv.scope_define(
                scope_id,
                p.name,
                link_id.into(),
                ty.clone(),
                VarDefinitionSpace::Arg,
            );
        }
        Ok(new_block_id)
    }

    fn add_lambda(
        &mut self,
        block_id: BlockId,
        def: Lambda,
        name: Option<StringKey>,
        scope_type: ScopeType,
        ret: Option<BlockId>,
        next: Option<BlockId>,
        fenv: &mut FlattenEnvironment,
        b: &mut NodeBuilder,
    ) -> Result<(ScopeId, BlockId, AstType)> {
        let fun_ty = def_to_type(&def, b);

        if let Some(body) = def.body {
            let span_id = body.span_id;
            let fun_scope_id = fenv.new_scope(scope_type);
            let fun_block_id = self.add_block(
                fun_scope_id,
                block_id,
                &[],
                &def.params,
                Some(*body),
                fun_ty.clone(),
                name,
                Successor::FunctionDeclaration,
                span_id,
                VarDefinitionSpace::Static,
                ret,
                next,
                fenv,
                b,
            )?;

            //let r = self.flatten(fun_block_id, *body, fenv, b)?;
            self.ast_blocks.push(fun_block_id);
            Ok((fun_scope_id, fun_block_id, fun_ty))
        } else {
            unreachable!()
        }
    }

    pub fn flatten(
        &mut self,
        block_id: BlockId,
        node: AstNode,
        fenv: &mut FlattenEnvironment,
        b: &mut NodeBuilder,
    ) -> Result<FlattenResult> {
        let block = self.get_block_mut(block_id);
        let span_id = node.span_id;
        let ast = node.node;

        match ast {
            Ast::Module(_, _) => {
                unimplemented!("No nested modules yet")
            }

            Ast::Sequence(exprs) => self.flatten_sequence(block_id, exprs, fenv, b),

            Ast::Global(name, expr) => {
                match expr.node {
                    Ast::Lambda(def) => {
                        let ret_ty = b.types.r(def.return_type).clone();
                        if def.body.is_some() {
                            let (fun_scope_id, fun_block_id, fun_ty) = self.add_lambda(
                                block_id,
                                def,
                                Some(name),
                                ScopeType::Function,
                                None,
                                None,
                                fenv,
                                b,
                            )?;

                            let ret_block_id =
                                self.add_return_block(fun_block_id, fun_scope_id, ret_ty, b);

                            let fun_block = self.get_block_mut(fun_block_id);
                            fun_block.ret = Some(ret_block_id);
                            fun_block.next = Some(ret_block_id);

                            // push declaration into static block
                            let code = LCode::DeclareFunction(Some(fun_block_id));
                            let entry = CodeEntry::new(
                                block_id,
                                code,
                                fun_ty.clone(),
                                Some(name),
                                span_id,
                                VarDefinitionSpace::Static,
                            );
                            let link_id = self.push_entry_with_link(entry);

                            let scope_id = fenv.static_scope_id();
                            fenv.scope_define(
                                scope_id,
                                name,
                                fun_block_id.into(),
                                fun_ty.clone(),
                                VarDefinitionSpace::Static,
                            );

                            Ok(FlattenResult::new(block_id, Some(link_id), fun_ty, false))
                        } else {
                            let fun_ty = def_to_type(&def, b);
                            let code = LCode::DeclareFunction(None);
                            let entry = CodeEntry::new(
                                block_id,
                                code,
                                fun_ty.clone(),
                                Some(name),
                                span_id,
                                VarDefinitionSpace::Static,
                            );
                            let link_id = self.push_entry_with_link(entry);
                            Ok(FlattenResult::new(block_id, Some(link_id), fun_ty, false))
                        }
                    }

                    Ast::Literal(lit) => {
                        let scope_id = block.stack.last().unwrap().clone();
                        let scope = fenv.get_scope(scope_id);

                        let static_block_id = fenv.static_block_id();
                        let global_name = if let ScopeType::Static = scope.scope_type {
                            b.labels.r(name.into()).to_string()
                        } else {
                            // static var with local name
                            let unique_name = b.unique_static_name();
                            let base = b.labels.r(name.into());
                            format!("{}{}", base, unique_name).clone()
                        };

                        let ast_ty: AstType = lit.clone().into();
                        let code = LCode::Const(lit);
                        let global_name_key = b.labels.s(&global_name);
                        let entry = CodeEntry::new(
                            static_block_id,
                            code,
                            ast_ty.clone(),
                            Some(global_name_key),
                            node.span_id,
                            VarDefinitionSpace::Static,
                        );
                        let link_id = self.push_entry_with_link(entry);

                        let code = LCode::Link(link_id);
                        let entry = CodeEntry::new(
                            block_id,
                            code,
                            ast_ty.clone(),
                            Some(name),
                            node.span_id,
                            VarDefinitionSpace::Static,
                        );
                        let link_id = self.push_entry_with_link(entry);

                        fenv.scope_define(
                            scope_id,
                            name,
                            link_id.into(),
                            ast_ty.clone(),
                            VarDefinitionSpace::Static,
                        );

                        Ok(FlattenResult::new(block_id, Some(link_id), ast_ty, false))
                    }
                    _ => unreachable!(),
                }
            }

            Ast::Builtin(id, mut args) => {
                let bi = b.builtins.get_enum(id);
                match bi {
                    Builtin::Import => {
                        let arg = args.pop().unwrap();
                        if let Some(s) = arg.try_string() {
                            self.link.add_library(&s);
                        } else {
                            b.push_error("Expected string", span_id);
                        }
                        Ok(FlattenResult::new(block_id, None, AstType::Unit, false))
                    }
                    _ => {
                        let ty = bi.get_return_type();
                        let args_size = args.len();
                        assert_eq!(args_size, bi.arity());
                        let mut values = vec![];
                        for a in args.into_iter() {
                            let Argument::Positional(expr) = a;
                            let r = self.flatten(block_id, *expr, fenv, b)?;
                            let link_id = r.link_id.unwrap();
                            let entry = self.get_entry(link_id);
                            values.push((link_id, entry.ty.clone()));
                        }

                        for (link_id, ty) in values {
                            let code = LCode::Link(link_id);
                            let entry = CodeEntry::new(
                                block_id,
                                code,
                                ty,
                                None,
                                node.span_id,
                                VarDefinitionSpace::Reg,
                            );
                            self.push_entry_with_link(entry);
                        }

                        let code = LCode::Builtin(id, args_size as u8, 0);
                        let entry = CodeEntry::new(
                            block_id,
                            code,
                            ty.clone(),
                            None,
                            node.span_id,
                            VarDefinitionSpace::Default,
                        );
                        let link_id = self.push_entry_with_link(entry);
                        Ok(FlattenResult::new(block_id, Some(link_id), ty, false))
                    }
                }
            }

            Ast::Return(maybe_expr) => {
                let ret_block_id = block.ret.as_ref().unwrap().clone();

                let mut jump_args = vec![];
                let mut block_id = block_id;
                if let Some(expr) = maybe_expr {
                    let r = self.flatten(block_id, *expr, fenv, b)?;
                    block_id = r.block_id;
                    let link_id = r.link_id.unwrap();
                    let entry = self.get_entry(link_id);
                    jump_args.push((link_id, entry.ty.clone()));
                }

                self.add_jump(block_id, ret_block_id, jump_args, node.span_id);
                Ok(FlattenResult::new(block_id, None, AstType::Unit, true)) //Some(link_id)))
            }

            Ast::Literal(lit) => {
                // literal is expression, non-terminal
                let ty: AstType = lit.clone().into();
                let code = LCode::Const(lit);
                let entry = CodeEntry::new(
                    block_id,
                    code,
                    ty.clone(),
                    None,
                    node.span_id,
                    VarDefinitionSpace::Default,
                );
                let link_id = self.push_entry_with_link(entry);
                Ok(FlattenResult::new(block_id, Some(link_id), ty, false))
            }

            Ast::BinaryOp(op, x, y) => {
                // expression, non-terminal
                let rx = self.flatten(block_id, *x, fenv, b)?;
                let ry = self.flatten(rx.block_id, *y, fenv, b)?;
                let vx = rx.link_id.unwrap();
                let vy = ry.link_id.unwrap();
                let code = LCode::Op2(op.node, vx.into(), vy.into());
                let entry = self.get_entry(vx);
                let ty = entry.ty.clone();
                let entry = CodeEntry::new(
                    ry.block_id,
                    code,
                    ty.clone(),
                    None,
                    node.span_id,
                    VarDefinitionSpace::Default,
                );
                let link_id = self.push_entry_with_link(entry);
                Ok(FlattenResult::new(ry.block_id, Some(link_id), ty, false))
            }

            Ast::Identifier(key) => {
                // identifier is expression, non-terminal
                self.dump_scope(block_id, fenv, b);
                if let Some(data) = self.resolve_name(block_id, key, fenv) {
                    let ty = data.ty.clone();
                    let code = if let VarDefinitionSpace::Arg = data.mem {
                        LCode::Value(data.offset)
                    } else {
                        LCode::Load(data.offset)
                    };
                    let entry =
                        CodeEntry::new(block_id, code, ty.clone(), None, node.span_id, data.mem);
                    let link_id = self.push_entry_with_link(entry);
                    Ok(FlattenResult::new(block_id, Some(link_id), ty, false))
                } else {
                    b.push_error("Name not found", node.span_id);
                    let s = b.labels.r(key.into());
                    Err(Error::new(BlockifyError::NotFound(s)))
                }
            }

            Ast::Assign(target, expr) => {
                // assign is expression, non-terminal
                let name = match target {
                    AssignTarget::Identifier(name) | AssignTarget::Alloca(name) => name,
                };

                // push the definition into the lambda list
                if let Ast::Lambda(def) = expr.node {
                    let ty = def_to_type(&def, b);
                    let template_id = self.push_template(def);
                    let block = self.get_block(block_id);
                    let scope_id = block.stack.last().unwrap();
                    let scope = fenv.get_scope_mut(*scope_id);
                    scope.lambdas.insert(name.into(), template_id);
                    return Ok(FlattenResult::new(block_id, None, ty, false));
                }

                let r = self.flatten(block_id, *expr, fenv, b)?;
                let v_expr = r.link_id.unwrap();
                let expr_ty = self.get_entry(v_expr).ty.clone();
                let v_block = r.block_id;

                self.dump_scope(block_id, fenv, b);
                let offset_decl = if let Some(data) = self.resolve_name(block_id, name, fenv) {
                    assert_eq!(data.ty, expr_ty);
                    data.offset
                } else {
                    let block = self.get_block(block_id);
                    let scope_id = block.stack.last().unwrap().clone();
                    //let scope = fenv.get_scope_mut(*scope_id);
                    let code = LCode::Declare;
                    let expr_ty = self.get_entry(v_expr).ty.clone();
                    let entry = CodeEntry::new(
                        v_block,
                        code,
                        expr_ty.clone(),
                        Some(name),
                        node.span_id,
                        VarDefinitionSpace::Default,
                    );
                    let link_id = self.push_entry_with_link(entry);
                    fenv.scope_define(
                        scope_id,
                        name,
                        link_id.into(),
                        expr_ty,
                        VarDefinitionSpace::Stack,
                    );
                    link_id.into()
                };

                let code = LCode::Store(offset_decl, v_expr.into());
                let entry = CodeEntry::new(
                    v_block,
                    code,
                    AstType::Unit,
                    Some(name),
                    node.span_id,
                    VarDefinitionSpace::Default,
                );
                let link_id = self.push_entry_with_link(entry);
                Ok(FlattenResult::new(
                    block_id,
                    Some(link_id),
                    AstType::Unit,
                    false,
                ))
            }

            Ast::Call(expr, args, _ret_ty) => {
                match &expr.node {
                    // call is an expression, it's non-terminal
                    // lambdas should also be non-terminal
                    Ast::Identifier(ident) => {
                        let name = b.labels.r(ident.into());
                        if let Some(data) = self.resolve_name(block_id, *ident, fenv) {
                            return self.add_function_call(
                                block_id,
                                data.offset,
                                data.ty,
                                args,
                                node.span_id,
                                fenv,
                                b,
                            );
                        }

                        if let Some(scope_id) =
                            self.resolve_lambda_scope(block_id, ident.into(), fenv)
                        {
                            let scope = fenv.get_scope(scope_id);
                            let label: StringLabel = (*ident).into();
                            let template_id = scope.lambdas.get(&label).unwrap();
                            let def = self.get_template(*template_id).clone();

                            let (_, fun_block_id, fun_ty) = self.add_lambda(
                                block_id,
                                def,
                                None,
                                ScopeType::Block,
                                None,
                                None,
                                fenv,
                                b,
                            )?;
                            return self.add_function_call(
                                block_id,
                                fun_block_id.into(),
                                fun_ty,
                                args,
                                node.span_id,
                                fenv,
                                b,
                            );
                        }
                        b.push_error(&format!("Call name not found: {}", name), node.span_id);
                        return Err(Error::new(BlockifyError::Invalid));
                    }
                    _ => {
                        unimplemented!("{:?}", expr.node);
                    }
                }
            }

            Ast::UnaryOp(op, x) => {
                // op1 is expression, non-terminal
                let r = self.flatten(block_id, *x, fenv, b)?;
                let code = LCode::Op1(op, r.link_id.unwrap().into());
                let entry = CodeEntry::new(
                    block_id,
                    code,
                    r.ty.clone(),
                    None,
                    node.span_id,
                    VarDefinitionSpace::Reg,
                );
                let link_id = self.push_entry_with_link(entry);
                Ok(FlattenResult::new(block_id, Some(link_id), r.ty, false))
            }

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
                let block = self.get_block(block_id);
                let v_next = block.next.unwrap();
                let v_ret = block.ret.unwrap();

                let then_scope_id = fenv.new_scope(ScopeType::Block);
                let span_id = then_expr.span_id;
                let then_block_id = self.successor(
                    block_id,
                    Some(*then_expr),
                    Some(then_scope_id),
                    Successor::BlockScope,
                    Some(v_ret),
                    Some(v_next),
                );
                let block = self.get_block_mut(then_block_id);
                block.next = Some(v_next);
                block.ret = Some(v_ret);

                self.ast_blocks.push(then_block_id);
                let name = b.labels.s("then");
                let code = LCode::Label(0, 0);
                let entry = CodeEntry::new(
                    then_block_id,
                    code,
                    AstType::Unit,
                    Some(name),
                    span_id,
                    VarDefinitionSpace::Reg,
                );
                self.push_entry_with_link(entry);

                let else_block_id = if let Some(else_expr) = maybe_else_expr {
                    let span_id = else_expr.span_id;
                    let else_scope_id = fenv.new_scope(ScopeType::Block);
                    let else_block_id = self.successor(
                        block_id,
                        Some(*else_expr),
                        Some(else_scope_id),
                        Successor::BlockScope,
                        Some(v_ret),
                        Some(v_next),
                    );
                    let block = self.get_block_mut(then_block_id);
                    block.next = Some(v_next);
                    block.ret = Some(v_ret);

                    self.ast_blocks.push(else_block_id);
                    let code = LCode::Label(0, 0);
                    let name = b.labels.s("else");
                    let entry = CodeEntry::new(
                        else_block_id,
                        code,
                        AstType::Unit,
                        Some(name),
                        span_id,
                        VarDefinitionSpace::Reg,
                    );
                    self.push_entry_with_link(entry);
                    else_block_id
                } else {
                    v_next
                };

                // condition
                let span_id = condition.span_id;
                let r = self.flatten(block_id, *condition, fenv, b)?;
                let code = LCode::Branch(
                    r.link_id.unwrap().into(),
                    then_block_id.into(),
                    else_block_id.into(),
                );
                let entry = CodeEntry::new(
                    block_id,
                    code,
                    AstType::Unit,
                    None,
                    span_id,
                    VarDefinitionSpace::Reg,
                );
                let v = self.push_entry_with_link(entry);
                Ok(FlattenResult::new(block_id, Some(v), AstType::Unit, true))
            }

            Ast::Block(name, args, body) => {
                let new_scope_id = fenv.new_scope(ScopeType::Block);
                let block = self.get_block(block_id);
                let new_block_id = self.add_block(
                    new_scope_id,
                    block_id,
                    &[],
                    &args,
                    None,
                    //Some(*body),
                    AstType::Unit,
                    Some(name),
                    Successor::BlockScope,
                    span_id,
                    VarDefinitionSpace::Static,
                    block.ret,
                    block.next,
                    fenv,
                    b,
                )?;
                let r = self.flatten(new_block_id, *body, fenv, b)?;
                //Some(*body),

                //self.ast_blocks.push(new_block_id);

                Ok(FlattenResult::new(
                    r.block_id,
                    r.link_id,
                    AstType::Unit,
                    true,
                ))
            }

            /*
            Ast::Lambda(_def) => {
            }

            Ast::ControlFlowMarker(ControlFlowMarker::BlockStart(name, args)) => {
            }

            Ast::ControlFlowMarker(ControlFlowMarker::Goto(label)) => {
            }




            Ast::Ternary(c, x, y) => {
            }

            Ast::Yield(maybe_expr) => {
            }


            Ast::Loop(name, body) => {
            }

            Ast::CloseBlock => {
            }

            Ast::Break(maybe_name, args) => {
            }

            Ast::Continue(maybe_name, args) => {
            }
            */
            Ast::Error => {
                b.push_error(&format!("AST Error"), node.span_id);
                Err(Error::new(BlockifyError::Invalid))
            }

            _ => unimplemented!("{:?}", ast),
        }
    }
}

pub fn save_graph(blockify: &dyn ICodeModule, filename: &str, b: &NodeBuilder) {
    use petgraph::dot::{Config, Dot};
    let cfg = blockify.get_graph(ValueId::new(0), None, b);
    let s = format!(
        "{:?}",
        Dot::with_attr_getters(
            &cfg.g,
            &[Config::EdgeNoLabel, Config::NodeNoLabel],
            &|_, _er| String::new(),
            &|_, (_index, data)| {
                match data.code_offset {
                    CodeOffset::Link(link_id) => {
                        format!(
                            "label = \"L{}:{}\" shape={:?}",
                            link_id.index(),
                            &data.name,
                            &data.ty.to_string()
                        )
                    }
                    CodeOffset::Value(value_id) => {
                        format!(
                            "label = \"V{}:{}\" shape={:?}",
                            value_id.index(),
                            &data.name,
                            &data.ty.to_string()
                        )
                    }
                    CodeOffset::Block(block_id) => {
                        format!(
                            "label = \"B{}:{}\" shape={:?}",
                            block_id.index(),
                            &data.name,
                            &data.ty.to_string()
                        )
                    }
                }
            }
        )
    );
    println!("saved graph {:?}", filename);
    println!("{}", s);
    std::fs::write(filename, s).unwrap();
}

fn def_to_type(def: &Lambda, b: &mut NodeBuilder) -> AstType {
    let params = def
        .params
        .iter()
        .map(|p| {
            let ty = b.types.r(p.ty);
            ty.clone()
        })
        .collect();

    let return_type = b.types.r(def.return_type).clone();
    let fun_ty = AstType::Func(params, return_type.into());
    fun_ty
}
