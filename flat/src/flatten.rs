use anyhow::Error;
use anyhow::Result;
use compile_core::{
    Argument,
    //AssignTarget,
    Ast,
    AstNode,
    AstType,
    //BinaryOperation, BuiltinId, ControlFlowMarker,
    //Lambda,
    LinkOptions,
    //Literal,
    //ParameterNode,
    Span,
    SpanId,
    StringKey,
    //UnaryOperation,
    VarDefinitionSpace,
};
use std::collections::HashMap;

use crate::{
    BlockId,
    BlockifyError,
    CodeRow,
    Builtin,
    CodeOffset,
    ICodeModule,
    LCode,
    LinkId,
    NodeBuilder,
    ScopeId,
    ScopeLayer,
    //NodeBuilder as NB,
    ScopeType,
    StringLabel,
    Successor,
    //TemplateId,
    ValueId,
};

use tabled::{
    settings::{
        //object::Rows,
        //Border,
        Style,
    },
    Table
};

pub struct FlattenEnvironment {
    current_block: Option<BlockId>,
    static_block: Option<BlockId>,
    static_scope: Option<ScopeId>,
    stack: Vec<ScopeId>,
    scopes: Vec<ScopeLayer>,
}

impl FlattenEnvironment {
    pub fn new() -> Self {
        Self {
            current_block: None,
            static_block: None,
            static_scope: None,
            stack: vec![],
            scopes: vec![],
        }
    }

    pub fn static_scope_id(&self) -> ScopeId {
        self.static_scope.unwrap()
    }

    pub fn static_block_id(&self) -> BlockId {
        self.static_block.unwrap()
    }

    pub fn new_scope(&mut self, scope_type: ScopeType) -> ScopeId {
        let offset = self.scopes.len();
        let scope = ScopeLayer::new(scope_type);
        self.scopes.push(scope);
        ScopeId(offset as u32)
    }

    pub fn current_scope(&self) -> Option<ScopeId> {
        self.stack.last().cloned()
    }

    pub fn enter_scope(&mut self, scope_id: ScopeId) {
        self.stack.push(scope_id);
    }

    pub fn exit_scope(&mut self) {
        self.stack.pop().unwrap();
    }

    pub fn get_scope(&self, scope_id: ScopeId) -> &ScopeLayer {
        self.scopes.get(scope_id.0 as usize).unwrap()
    }

    pub fn get_scope_mut(&mut self, scope_id: ScopeId) -> &mut ScopeLayer {
        self.scopes.get_mut(scope_id.0 as usize).unwrap()
    }

    pub fn push_block(&mut self, block_id: BlockId) {
        self.current_block = Some(block_id);
    }

    pub fn current_block(&mut self) -> BlockId {
        self.current_block.unwrap().clone()
    }

    pub fn pop_block(&mut self) -> BlockId {
        self.current_block.take().unwrap()
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
        scope_type: ScopeType,
        entry: CodeEntry,
    ) -> ModuleEntry {
        Self {
            value_id,
            next,
            prev,
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
    pub fn new(block_id: BlockId, code: LCode, ty: AstType, name: Option<StringKey>, span_id: SpanId) -> Self {
        Self {
            block_id,
            code,
            name,
            link: None,
            ty,
            span_id,
            mem: VarDefinitionSpace::Default,
        }
    }

    pub fn add_mem(mut self, mem: VarDefinitionSpace) -> Self {
        self.mem = mem;
        self
    }
}

pub struct IRBlock {
    block_id: BlockId,
    stack: Vec<ScopeId>,
    ast: Option<AstNode>,
    next: Option<BlockId>,
    ret: Option<BlockId>,
    links: Vec<LinkId>,
    succ: Vec<(Successor, BlockId)>,
}

impl IRBlock {
    pub fn new(block_id: BlockId, stack: Vec<ScopeId>, ast: Option<AstNode>) -> Self {
        Self {
            block_id,
            stack,
            ast,
            links: vec![],
            ret: None,
            next: None,
            succ: vec![],
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

    pub fn add_succ(&mut self, block_id: BlockId, succ_type: Successor) {
        self.succ.push((succ_type, block_id));
    }
}

#[derive(Debug)]
pub struct FlattenResult {
    link_id: Option<LinkId>,
    block_id: BlockId,
}

impl FlattenResult {
    pub fn new(block_id: BlockId, link_id: Option<LinkId>) -> Self {
        Self { block_id, link_id }
    }
}

pub struct FlattenModule {
    entries: Vec<ModuleEntry>,
    link_map: HashMap<LinkId, ValueId>,
    block_map: HashMap<BlockId, ValueId>,
    succ: HashMap<BlockId, Vec<(Successor, CodeOffset)>>,
    link: LinkOptions,
}

impl ICodeModule for FlattenModule {
    fn shared_libraries(&self) -> Vec<String> {
        self.link.shared_libraries()
    }

    fn get_span_id(&self, value_id: ValueId) -> SpanId {
        let entry = self.get_entry(value_id);
        entry.span_id
    }

    fn get_name(&self, v: ValueId) -> Option<StringLabel> {
        self.get_entry(v).name.map(|n| n.into())
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
        self.succ.get(&block_id).unwrap().clone()
    }

    fn get_type(&self, v: ValueId) -> AstType {
        let entry = self.get_entry(v);
        entry.clone().ty
    }

    fn get_entry_id(&self, value_id: ValueId) -> ValueId {
        let block_id = self.get_entry(value_id).block_id;
        *self.block_map.get(&block_id).unwrap()
    }

    fn is_in_static_scope(&self, v: ValueId) -> bool {
        self.get_entry(v).scope_type == ScopeType::Static
    }

    fn get_mem(&self, value_id: ValueId) -> &VarDefinitionSpace {
        &self.get_entry(value_id).mem
    }

    fn resolve_code_offset(&self, code_offset: CodeOffset) -> ValueId {
        match code_offset {
            CodeOffset::Value(v) => v,
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
            let name = entry.name.map(|n| b.labels.r(n.into()));
            let row = self.get_code_row(entry.value_id, b);
            rows.push(row);

            println!(
                "IR: V: {}, Nx: {}, Pr: {}, B: {}, L:{}, N: {:?}, C: {:?}, T: {:?}, S: {:?}",
                entry.value_id,
                entry.next,
                entry.prev,
                entry.block_id,
                entry.link.unwrap(),
                name.unwrap_or("".into()),
                entry.code,
                entry.ty,
                entry.scope_type,
            );
        }
        let s = Table::new(rows).with(Style::sharp()).to_string();
        println!("{}", s);
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
        let ty = self.get_type(v);
        let mem = self.get_mem(v);
        let next = self.get_next(v).unwrap_or(v).index();
        let prev = self.get_prev(v).unwrap_or(v).index();
        let scope_id = ScopeId(0);//self.get_scope_id(v);
        let entry_id = self.get_entry_id(v);
        let block_id = entry.block_id;

        CodeRow {
            pos: v.index(),
            next,
            prev,
            value: self.code_to_string(v, b),
            ty,
            mem: format!("{:?}", mem),
            name: self
                .get_name(v)
                .map(|key| b.labels.r(key))
                .unwrap_or("".to_string())
                .to_string(),
            span_id: self.get_span_id(v).index(),
            scope_id: scope_id.index(),
            entry_id: entry_id.index(),
            block_id: block_id.index(),
            term: code.is_term(),
        }
    }

}

pub struct Flatten {
    module_key: Option<StringKey>,
    ast_blocks: Vec<BlockId>,
    ir_blocks: Vec<BlockId>,
    link: LinkOptions,
    entries: Vec<CodeEntry>,
    blocks: Vec<IRBlock>,
}

impl Flatten {
    pub fn new() -> Self {
        Self {
            module_key: None,
            ast_blocks: vec![],
            ir_blocks: vec![],
            entries: vec![],
            blocks: vec![],
            link: LinkOptions::new(),
        }
    }

    pub fn module(self, fenv: &FlattenEnvironment, _b: &NodeBuilder) -> FlattenModule {
        assert!(self.ast_blocks.is_empty());
        let mut m = FlattenModule::new();

        let mut value_count = 0;
        for block_id in self.ir_blocks.iter() {
            let block = self.get_block(*block_id);

            m.succ.insert(
                *block_id,
                block
                    .succ
                    .iter()
                    .map(|(a, b)| (*a, (*b).into()))
                    .collect::<Vec<_>>(),
            );

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
                let mentry = ModuleEntry::from_code_entry(v, next, prev, scope.scope_type, entry);
                m.add(mentry);
                value_count += 1;
            }
        }
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
                    block.block_id,
                    name,
                    entry.code,
                    entry.ty,
                    block.ast.as_ref().map(|a| &a.node).unwrap()
                );
            }
        }
    }

    pub fn flatten_module(node: AstNode, fenv: &mut FlattenEnvironment) -> Result<Self> {
        let mut f = Self::new();
        if let Ast::Module(key, body) = node.node {
            f.module_key = Some(key);
            let static_scope = fenv.new_scope(ScopeType::Static);
            let stack = vec![static_scope];
            let block_id = f.new_ast_block(Some(*body), stack);
            let code = LCode::Label(0, 0);
            let entry = CodeEntry::new(block_id, code, AstType::Unit, Some(key), node.span_id);
            f.push_entry_with_link(block_id, entry);
            fenv.static_block = Some(block_id);
            fenv.static_scope = Some(static_scope);
            f.ast_blocks.push(block_id);
            f.ir_blocks.push(block_id);
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

    pub fn push_entry_with_link(&mut self, block_id: BlockId, entry: CodeEntry) -> LinkId {
        let link_id = self.push(entry);
        self.get_block_mut(block_id).push(link_id);
        link_id
    }

    pub fn new_ast_block(&mut self, ast: Option<AstNode>, stack: Vec<ScopeId>) -> BlockId {
        let index = self.blocks.len();
        let block_id = BlockId(index as u32);
        let ir_block = IRBlock::new(block_id, stack, ast);
        self.blocks.push(ir_block);
        block_id
    }

    pub fn successor(
        &mut self,
        block_id: BlockId,
        ast: Option<AstNode>,
        scope_id: Option<ScopeId>,
        succ_type: Successor,
    ) -> BlockId {
        let block = self.get_block(block_id);
        let succ_block_id = self._successor(block_id, ast, scope_id, block.ret, block.next);
        let block = self.get_block_mut(block_id);
        block.add_succ(succ_block_id, succ_type);
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
        self.blocks.get(block_id.index()).unwrap()
    }

    pub fn get_block_mut(&mut self, block_id: BlockId) -> &mut IRBlock {
        self.blocks.get_mut(block_id.index()).unwrap()
    }

    pub fn get_entry(&self, link_id: LinkId) -> &CodeEntry {
        self.entries.get(link_id.index()).unwrap()
    }

    pub fn get_entry_mut(&mut self, link_id: LinkId) -> &mut CodeEntry {
        self.entries.get_mut(link_id.index()).unwrap()
    }

    fn flatten_sequence(
        &mut self,
        block_id: BlockId,
        mut seq: Vec<AstNode>,
        fenv: &mut FlattenEnvironment,
        b: &mut NodeBuilder,
    ) -> Result<FlattenResult> {
        let block = self.get_block_mut(block_id);
        let is_static = block.stack.len() == 1;
        let r = if seq.is_empty() {
            if is_static {
                // don't do anything, static block is already present
            } else {
                self.ir_blocks.push(block_id);
            }
            FlattenResult::new(block_id, None)
        } else {
            let rem = seq.split_off(1);
            let node = seq.pop().unwrap();
            let r = self.flatten(block_id, node, fenv, b)?;
            if r.block_id != block_id {
                self.ir_blocks.push(block_id);
            }

            let block = self.get_block_mut(r.block_id);
            block.ast = Some(Ast::Sequence(rem).into());
            self.ast_blocks.push(r.block_id);
            r
        };
        Ok(r)
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
        let ret_block_id = self.successor(fun_block_id, None, Some(scope_id), Successor::BlockScope);

        let code = LCode::Label(args.len() as u8, 0);
        let entry =
            CodeEntry::new(ret_block_id, code, return_type.clone(), Some(name), span_id);
        self.push_entry_with_link(ret_block_id, entry);

        let v_args = args
            .iter()
            .enumerate()
            .map(|(i, _arg)| {
                let code = LCode::Arg(i as u8);
                let name = b.labels.s(&format!("arg{}", i));
                let entry = CodeEntry::new(ret_block_id, code, return_type.clone(), Some(name), span_id);
                self.push_entry_with_link(ret_block_id, entry)
            })
            .collect::<Vec<_>>();

        for link_id in v_args.iter() {
            let code = LCode::Link(*link_id);
            let entry =
                CodeEntry::new(ret_block_id, code, return_type.clone(), None, span_id);
            self.push_entry_with_link(ret_block_id, entry);
        }

        let code = LCode::Return(v_args.len() as u8);
        let entry = CodeEntry::new(ret_block_id, code, AstType::Unit, None, span_id);
        self.push_entry_with_link(ret_block_id, entry);
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
            let entry = CodeEntry::new(block_id, code, ty, None, span_id);
            self.push_entry_with_link(block_id, entry);
        }

        let code = LCode::Jump(target_id.into(), num_args as u8);
        let entry = CodeEntry::new(block_id, code, AstType::Unit, None, span_id);
        self.push_entry_with_link(block_id, entry);
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

                        let r = if let Some(body) = def.body {
                            let fun_scope_id = fenv.new_scope(ScopeType::Function);
                            let fun_block_id = self.successor(
                                block_id,
                                Some(*body),
                                Some(fun_scope_id),
                                Successor::FunctionDeclaration,
                            );
                            let code = LCode::Label(0, 0);

                            let entry = CodeEntry::new(fun_block_id, code, fun_ty.clone(), Some(name), span_id);
                            self.push_entry_with_link(fun_block_id, entry);

                            self.ir_blocks.push(fun_block_id);
                            let ret_ty = b.types.r(def.return_type).clone();
                            let ret_block_id = self.add_return_block(fun_block_id, fun_scope_id, ret_ty, b);

                            let fun_block = self.get_block_mut(fun_block_id);
                            fun_block.ret = Some(ret_block_id);
                            fun_block.next = Some(ret_block_id);

                            self.ast_blocks.push(fun_block_id);
                            self.ir_blocks.push(ret_block_id);

                            // push declaration into static block
                            let code = LCode::DeclareFunction(Some(fun_block_id));
                            let entry = CodeEntry::new(block_id, code, fun_ty.clone(), Some(name), span_id);
                            let link_id = self.push_entry_with_link(block_id, entry);
                            FlattenResult::new(block_id, Some(link_id))
                        } else {
                            let code = LCode::DeclareFunction(None);
                            let entry = CodeEntry::new(block_id, code, fun_ty, Some(name), span_id);
                            let link_id = self.push_entry_with_link(block_id, entry);
                            FlattenResult::new(block_id, Some(link_id))
                        };
                        Ok(r)
                    }

                    Ast::Literal(lit) => {
                        let scope_id = block.stack.last().unwrap();
                        let scope = fenv.get_scope(*scope_id);
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
                        let entry =
                            CodeEntry::new(block_id, code, ast_ty.clone(), Some(global_name_key), node.span_id);
                        let link_id = self.push_entry_with_link(block_id, entry);

                        let code = LCode::Link(link_id);
                        let entry = CodeEntry::new(block_id, code, ast_ty, Some(name), node.span_id);
                        let link_id = self.push_entry_with_link(block_id, entry);
                        Ok(FlattenResult::new(block_id, Some(link_id)))
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
                        Ok(FlattenResult::new(block_id, None))
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
                            let entry = CodeEntry::new(block_id, code, ty, None, node.span_id);
                            self.push_entry_with_link(block_id, entry);
                        }

                        let code = LCode::Builtin(id, args_size as u8, 0);
                        let entry = CodeEntry::new(block_id, code, ty, None, node.span_id);
                        let link_id = self.push_entry_with_link(block_id, entry);
                        Ok(FlattenResult::new(block_id, Some(link_id)))
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
                Ok(FlattenResult::new(block_id, None)) //Some(link_id)))
            }

            Ast::Literal(lit) => {
                // literal is expression, non-terminal
                let ty: AstType = lit.clone().into();
                let code = LCode::Const(lit);
                let entry = CodeEntry::new(block_id, code, ty, None, node.span_id);
                let link_id = self.push_entry_with_link(block_id, entry);
                Ok(FlattenResult::new(block_id, Some(link_id)))
            }

            /*
            Ast::Lambda(_def) => {
            }

            Ast::Call(expr, args, _ret_ty) => {
            },

            Ast::ControlFlowMarker(ControlFlowMarker::BlockStart(name, args)) => {
            }

            Ast::ControlFlowMarker(ControlFlowMarker::Goto(label)) => {
            }

            Ast::Identifier(key) => {
            }

            Ast::Assign(target, expr) => {
            }

            Ast::UnaryOp(op, x) => {
            }

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
            }

            Ast::Ternary(c, x, y) => {
            }

            Ast::BinaryOp(op, x, y) => {
            }

            Ast::Yield(maybe_expr) => {
            }


            Ast::Loop(name, body) => {
            }

            Ast::Block(name, args, body) => {
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
