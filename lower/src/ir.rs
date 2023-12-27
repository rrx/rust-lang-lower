use anyhow::Error;
use anyhow::Result;

use crate::{AstNode, AstType, Diagnostics, Extra, NodeBuilder, ParseError, StringKey, SymIndex};
use codespan_reporting::diagnostic::{Diagnostic, Label};
//use melior::Context;
use std::fmt::Debug;

use crate::ast::{
    Argument,
    AssignTarget,
    Ast,
    BinaryOperation,
    Builtin,
    //DerefTarget,
    Literal,
    //NodeBlock,
    Parameter,
    //ParameterNode,
    Span,
    Terminator,
    UnaryOperation,
    VarDefinitionSpace,
};

use petgraph::algo::dominators::simple_fast;
use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use std::collections::HashMap;
//use std::collections::HashSet;

#[derive(Debug)]
pub enum IRTypeSelect {
    This,
    // array offset
    Offset(usize),
    // attribute select on tuple
    Attr(usize),
    // byte level view (width, offset)
    Byte(u8, usize),
}

impl Default for IRTypeSelect {
    fn default() -> Self {
        Self::This
    }
}

#[derive(Debug, Clone)]
pub struct IRArg {
    pub(crate) name: StringKey,
    pub(crate) ty: AstType,
}

#[derive(Debug)]
pub struct IRBlock {
    pub(crate) index: NodeIndex,
    pub(crate) name: StringKey,
    pub(crate) params: Vec<IRArg>,
    pub(crate) children: Vec<IRNode>,
}

impl IRBlock {
    pub fn new(name: StringKey, params: Vec<IRArg>, children: Vec<IRNode>) -> Self {
        Self {
            index: NodeIndex::new(0),
            name,
            params,
            children,
        }
    }

    pub fn terminator(&self) -> Option<Terminator> {
        self.children.last().unwrap().kind.terminator()
    }
}

#[derive(Debug)]
pub struct IRControlBlock {
    arg_count: usize,
    block_index: NodeIndex,
    params: Vec<IRArg>,
    symbols: HashMap<StringKey, SymIndex>,
    def_count: usize,
}

impl IRControlBlock {
    pub fn new(params: Vec<IRArg>) -> Self {
        Self {
            def_count: 0,
            arg_count: 0,
            block_index: NodeIndex::new(0),
            params,
            symbols: HashMap::new(),
        }
    }
    pub fn lookup(&self, name: StringKey) -> Option<SymIndex> {
        self.symbols.get(&name).cloned()
    }
    pub fn add_symbol(&mut self, name: StringKey, index: SymIndex) {
        assert_eq!(index.block(), self.block_index);
        self.symbols.insert(name, index);
    }

    pub fn push_arg(&mut self, name: StringKey) -> SymIndex {
        assert!(self.arg_count < self.params.len());
        let index = SymIndex::Arg(self.block_index, self.arg_count);
        self.symbols.insert(name, index);
        self.arg_count += 1;
        index
    }

    pub fn add_definition(&mut self, name: StringKey) -> SymIndex {
        let offset = self.def_count;
        self.def_count += 1;
        let index = SymIndex::Def(self.block_index, offset);
        self.add_symbol(name, index);
        index
    }
}

#[derive(Debug, Default)]
pub struct IREnvironment {
    stack: Vec<(NodeIndex, Span)>,
    block_names: HashMap<StringKey, NodeIndex>,
    block_names_index: HashMap<NodeIndex, StringKey>,
    types: HashMap<SymIndex, (AstType, VarDefinitionSpace)>,
    label_count: usize,
    pub g: IRGraph,
}

pub type IRGraph = DiGraph<IRControlBlock, ()>;

impl IREnvironment {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn fresh_label<E: Extra>(&mut self, name: &str, b: &mut NodeBuilder<E>) -> StringKey {
        let s = b.s(&format!("b_{}_{}", name, self.label_count));
        self.label_count += 1;
        s
    }

    pub fn lookup_type(&self, index: SymIndex) -> Option<(AstType, VarDefinitionSpace)> {
        if let SymIndex::Arg(block_index, offset) = index {
            let block = self.g.node_weight(block_index).unwrap();
            Some((
                block.params.get(offset).unwrap().ty.clone(),
                VarDefinitionSpace::Arg,
            ))
        } else {
            self.types.get(&index).cloned()
        }
    }

    pub fn set_type(&mut self, index: SymIndex, ty: AstType, mem: VarDefinitionSpace) {
        self.types.insert(index, (ty, mem));
    }

    pub fn connect_block(&mut self, source: NodeIndex, target: NodeIndex) {
        self.g.add_edge(source, target, ());
    }

    pub fn error(&self, msg: &str, span: Span) -> Diagnostic<usize> {
        let r = span.begin.pos as usize..span.end.pos as usize;
        let mut labels = vec![Label::primary(span.file_id, r).with_message(msg)];
        for (_, span) in self.stack.iter().rev() {
            let r = span.begin.pos as usize..span.end.pos as usize;
            labels.push(Label::secondary(span.file_id, r));
        }
        let error = Diagnostic::error()
            .with_labels(labels)
            .with_message("error");

        error
    }

    pub fn enter_block(&mut self, index: NodeIndex, span: Span) {
        self.stack.push((index, span));
    }

    pub fn exit_block(&mut self) {
        self.stack.pop();
    }

    pub fn stack_size(&self) -> usize {
        self.stack.len()
    }

    pub fn root(&self) -> NodeIndex {
        self.stack.first().unwrap().clone().0
    }

    pub fn current_block(&self) -> NodeIndex {
        self.stack.last().unwrap().clone().0
    }

    pub fn lookup_block(&self, name: StringKey) -> Option<NodeIndex> {
        self.block_names.get(&name).cloned()
    }

    pub fn add_definition(&mut self, block_index: NodeIndex, ident: StringKey) -> SymIndex {
        let data = self.g.node_weight_mut(block_index).unwrap();
        let index = data.add_definition(ident);
        index
    }

    pub fn add_block(
        &mut self,
        name: StringKey,
        params: Vec<IRArg>,
        _d: &Diagnostics,
    ) -> NodeIndex {
        let index = self.g.add_node(IRControlBlock::new(params.clone()));
        self.g.node_weight_mut(index).unwrap().block_index = index;
        self.block_names.insert(name, index);
        self.block_names_index.insert(index, name);

        let data = self.g.node_weight_mut(index).unwrap();
        for a in params {
            data.push_arg(a.name);
        }

        index
    }

    pub fn add_edge(&mut self, a: StringKey, b: StringKey, g: &mut IRGraph) {
        let index_a = self.block_names.get(&a).unwrap();
        let index_b = self.block_names.get(&b).unwrap();
        g.add_edge(*index_a, *index_b, ());
    }

    pub fn name_in_scope(&self, index: NodeIndex, name: StringKey) -> Option<SymIndex> {
        let maybe_dom = simple_fast(&self.g, self.root())
            .dominators(index)
            .map(|it| it.collect::<Vec<_>>());
        //println!("dom: {:?} => {:?}", index, dom);
        if let Some(dom) = maybe_dom {
            for i in dom.into_iter().rev() {
                let data = self.g.node_weight(i).unwrap();
                if let Some(r) = data.lookup(name) {
                    return Some(r);
                }
            }
        }
        None
    }

    pub fn symbol_is_static(&self, index: SymIndex) -> bool {
        // root block is static block, and there's only one for now
        self.root() == index.block()
    }

    pub fn block_is_static(&self, block_index: NodeIndex) -> bool {
        // root block is static block, and there's only one for now
        self.root() == block_index
    }

    pub fn dump_node<E>(
        &self,
        //g: &IRGraph,
        b: &NodeBuilder<E>,
        index: NodeIndex,
        current_block: NodeIndex,
        depth: usize,
    ) {
        let data = &self.g[index];
        let name = b
            .strings
            .resolve(self.block_names_index.get(&index).unwrap());
        if index == current_block {
            println!("{:width$}Current: {}", "", name, width = depth * 2);
        } else {
            println!("{:width$}Node: {}", "", name, width = depth * 2);
        }
        for (k, v) in data.symbols.iter() {
            println!(
                "{:width$}  Symbol: {}, {:?}, {:?}",
                "",
                b.strings.resolve(k),
                k,
                v,
                width = depth * 2
            );
        }
        for n in self.g.neighbors(index) {
            self.dump_node(b, n, current_block, depth + 1);
        }
    }

    pub fn dump<E>(&self, b: &NodeBuilder<E>, current_block: NodeIndex) {
        self.dump_node(b, self.root(), current_block, 0);
    }

    pub fn save_graph<E>(&self, filename: &str, b: &NodeBuilder<E>) {
        use petgraph::dot::{Config, Dot};

        let s = format!(
            "{:?}",
            Dot::with_attr_getters(
                &self.g,
                &[Config::EdgeNoLabel, Config::NodeNoLabel],
                &|_, _er| String::new(),
                &|_, (_index, data)| {
                    let key = self.block_names_index.get(&data.block_index).unwrap();
                    let name = b.strings.resolve(key);
                    format!(
                        //"label = \"[{}]{}\" shape={:?}",
                        "label = \"{}\"",
                        name,
                        //data.block_index.index(),
                        //&data.name,
                        //&data.ty.to_string()
                    )
                }
            )
        );
        let path = std::fs::canonicalize(filename).unwrap();
        println!("{}", path.clone().into_os_string().into_string().unwrap());
        println!("{}", s);
        std::fs::write(path, s).unwrap();
    }
}

#[derive(Debug)]
pub enum IRKind {
    Decl(StringKey, AstType, VarDefinitionSpace),
    // set(variable, expr, type offset)
    Set(StringKey, Box<IRNode>, IRTypeSelect),
    // get(variable, type offset)
    Get(StringKey, IRTypeSelect),
    // ret(args)
    Ret(Vec<IRNode>),
    Cond(Box<IRNode>, Box<IRNode>, Option<Box<IRNode>>),
    Branch(Box<IRNode>, StringKey, StringKey),
    // start block
    Label(StringKey, Vec<IRArg>),
    Jump(StringKey, Vec<IRNode>),
    // function, a collection of blocks, the first of which is the entry, return type
    Func(Vec<IRBlock>, AstType),
    // call(variable, args), return type is inferred from variable
    Call(StringKey, Vec<IRNode>),
    // op(operation, args)
    Op1(UnaryOperation, Box<IRNode>),
    Op2(BinaryOperation, Box<IRNode>, Box<IRNode>),
    Block(IRBlock),
    Seq(Vec<IRNode>),
    Literal(Literal),
    Builtin(Builtin, Vec<IRNode>),
    Noop,
}

impl IRKind {
    pub fn terminator(&self) -> Option<Terminator> {
        match self {
            Self::Seq(exprs) => exprs.last().unwrap().kind.terminator(),
            Self::Block(nb) => nb.terminator(),
            Self::Jump(key, _args) => Some(Terminator::Jump(*key)),
            Self::Branch(_, then_key, else_key) => Some(Terminator::Branch(*then_key, *else_key)),
            Self::Ret(_) => Some(Terminator::Return),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub struct IRNode {
    pub(crate) kind: IRKind,
    pub(crate) span: Span,
}

pub fn error(msg: &str, span: Span) -> Diagnostic<usize> {
    let r = span.begin.pos as usize..span.end.pos as usize;
    let error = Diagnostic::error()
        .with_labels(vec![Label::primary(span.file_id, r).with_message(msg)])
        .with_message("error");
    error
}

pub struct IRBlockSorter {
    pub stack: Vec<IRNode>,
    pub blocks: Vec<IRBlock>,
}

impl IRBlockSorter {
    pub fn new() -> Self {
        Self {
            stack: vec![],
            blocks: vec![],
        }
    }

    pub fn blocks<E: Extra>(self, b: &mut NodeBuilder<E>) -> Vec<IRNode> {
        self.blocks
            .into_iter()
            .map(|block| IRNode::new(IRKind::Block(block), b.extra().get_span()))
            .collect()
    }

    pub fn run<E: Extra>(ir: IRNode, b: &mut NodeBuilder<E>) -> IRNode {
        let mut s = Self::new();
        let ir = match ir.kind {
            IRKind::Seq(exprs) => {
                let module = b.s("module");
                let mut block = IRBlock::new(module, vec![], exprs);
                block.children.insert(0, b.ir_label(module, vec![]));
                IRNode::new(IRKind::Block(block), b.extra().get_span())
            }
            IRKind::Block(ref _block) => ir,
            _ => unreachable!(),
        };

        s.sort(ir, b);
        s.close_block(b);
        let blocks = s.blocks(b);
        b.ir_seq(blocks)
    }

    pub fn sort_block<E: Extra>(&mut self, block: IRBlock, b: &mut NodeBuilder<E>) {
        let mut s = Self::new();
        for c in block.children {
            s.sort(c, b);
        }
        s.close_block(b);
        for block in s.blocks {
            self.blocks.push(block);
        }
    }

    pub fn sort<E: Extra>(&mut self, ir: IRNode, b: &mut NodeBuilder<E>) {
        match ir.kind {
            IRKind::Seq(exprs) => {
                for e in exprs {
                    self.sort(e, b);
                }
            }
            //IRKind::Set(_, v, _) => {
            //self.sort(*v, b);
            //}
            IRKind::Block(nb) => {
                self.sort_block(nb, b);
            }
            IRKind::Jump(_, _) => {
                self.stack.push(ir);
                self.close_block(b);
            }
            IRKind::Label(_, _) => {
                self.close_block(b);
                self.stack.push(ir);
            }
            _ => {
                self.stack.push(ir);
            }
        }
    }

    fn close_block<E: Extra>(&mut self, b: &mut NodeBuilder<E>) {
        if self.stack.len() == 0 {
            return;
        }

        let first = self.stack.first();

        let span_first = first.as_ref().unwrap().span.clone();
        let span_last = self.stack.last().unwrap().span.clone();
        let _span = Span {
            file_id: span_first.file_id,
            begin: span_last.begin,
            end: span_last.end,
        };

        let nb = if let IRKind::Label(name, args) = &first.as_ref().unwrap().kind {
            IRBlock {
                index: NodeIndex::new(0),
                name: *name,
                params: args.clone(),
                // skip the first child which is a label, it's redundant now that we have a block
                children: self.stack.drain(..).skip(1).collect(),
            }
        } else {
            let offset = self.blocks.len();
            let name = b.strings.intern(format!("_block{}", offset));
            IRBlock {
                index: NodeIndex::new(0),
                name,
                params: vec![],
                children: self.stack.drain(..).collect(),
            }
        };
        // end of block

        self.blocks.push(nb);
    }
}

impl IRNode {
    pub fn new(kind: IRKind, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn try_string(&self) -> Option<String> {
        if let IRKind::Literal(Literal::String(s)) = &self.kind {
            Some(s.clone())
        } else {
            None
        }
    }

    pub fn get_span(&self) -> Span {
        self.span.clone()
    }

    pub fn to_vec(self) -> Vec<Self> {
        if let IRKind::Seq(exprs) = self.kind {
            exprs
        } else {
            vec![self]
        }
    }

    pub fn dump<E: Extra>(&self, b: &NodeBuilder<E>, mut depth: usize) {
        match &self.kind {
            IRKind::Func(blocks, _ret_ty) => {
                println!("{:width$}func:", "", width = depth * 2);
                depth += 1;
                for block in blocks {
                    println!(
                        "{:width$}block({})",
                        "",
                        b.strings.resolve(&block.name),
                        width = depth * 2
                    );
                    for a in &block.params {
                        println!(
                            "{:width$}arg: {}: {:?}",
                            "",
                            b.strings.resolve(&a.name),
                            a.ty,
                            width = (depth + 1) * 2
                        );
                    }
                    for a in &block.children {
                        a.dump(b, depth + 1);
                    }
                }
            }
            IRKind::Seq(exprs) => {
                //println!("{:width$}seq:", "", width = depth * 2);
                for e in exprs {
                    e.dump(b, depth);
                }
            }
            IRKind::Branch(cond, br_then, br_else) => {
                println!(
                    "{:width$}branch({}, {})",
                    "",
                    b.strings.resolve(br_then),
                    b.strings.resolve(br_else),
                    width = depth * 2
                );
                cond.dump(b, depth + 1);
            }
            IRKind::Decl(key, ty, mem) => {
                println!(
                    "{:width$}decl({}, {:?}, {:?})",
                    "",
                    b.strings.resolve(key),
                    ty,
                    mem,
                    width = depth * 2
                );
            }
            IRKind::Set(key, v, select) => {
                println!(
                    "{:width$}set({}, {:?})",
                    "",
                    b.strings.resolve(key),
                    select,
                    width = depth * 2
                );
                v.dump(b, depth + 1);
            }
            IRKind::Get(key, select) => {
                println!(
                    "{:width$}get({}, {:?})",
                    "",
                    b.strings.resolve(key),
                    select,
                    width = depth * 2
                );
            }
            IRKind::Ret(vs) => {
                println!("{:width$}ret:", "", width = depth * 2);
                for e in vs {
                    e.dump(b, depth + 1);
                }
            }

            IRKind::Cond(c, a, mb) => {
                println!("{:width$}cond:", "", width = depth * 2);
                c.dump(b, depth + 1);
                a.dump(b, depth + 1);
                if let Some(else_expr) = mb {
                    else_expr.dump(b, depth + 1);
                }
            }

            IRKind::Label(name, args) => {
                println!(
                    "{:width$}label: {}",
                    "",
                    b.strings.resolve(name),
                    width = depth * 2
                );
                for e in args {
                    println!(
                        "{:width$}arg: {}, {:?}",
                        "",
                        b.strings.resolve(&e.name),
                        e.ty,
                        width = (depth + 1) * 2
                    );
                }
            }

            IRKind::Jump(key, args) => {
                println!(
                    "{:width$}jump({})",
                    "",
                    b.strings.resolve(key),
                    width = depth * 2
                );
                for a in args {
                    a.dump(b, depth + 1);
                }
            }

            IRKind::Call(key, args) => {
                println!(
                    "{:width$}call({})",
                    "",
                    b.strings.resolve(key),
                    width = depth * 2
                );
                if args.len() > 0 {
                    for a in args {
                        a.dump(b, depth + 1);
                    }
                }
            }

            IRKind::Op1(op, expr) => {
                println!("{:width$}unary: {:?}", "", op, width = depth * 2);
                expr.dump(b, depth + 1);
            }

            IRKind::Op2(op, x, y) => {
                println!("{:width$}binop: {:?}", "", op, width = depth * 2);
                x.dump(b, depth + 1);
                y.dump(b, depth + 1);
            }

            IRKind::Literal(lit) => {
                println!("{:width$}{:?}", "", lit, width = depth * 2);
            }

            IRKind::Builtin(bi, args) => {
                println!("{:width$}builtin({:?})", "", bi, width = depth * 2);
                for a in args {
                    a.dump(b, depth + 1);
                }
            }

            IRKind::Noop => {
                println!("{:width$}noop", "", width = depth * 2);
            }

            IRKind::Block(block) => {
                println!(
                    "{:width$}block({})",
                    "",
                    b.strings.resolve(&block.name),
                    width = depth * 2
                );
                for a in &block.params {
                    println!(
                        "{:width$}arg: {}: {:?}",
                        "",
                        b.strings.resolve(&a.name),
                        a.ty,
                        width = (depth + 1) * 2
                    );
                }
                for a in &block.children {
                    a.dump(b, depth + 1);
                }
            } //_ => ()//unimplemented!()
        }
    }

    pub fn build_graph<'c, E: Extra>(
        self,
        d: &mut Diagnostics,
        env: &mut IREnvironment,
        b: &mut NodeBuilder<E>,
    ) -> Result<IRNode> {
        let span = self.get_span().clone();
        match self.kind {
            IRKind::Noop => Ok(self),

            IRKind::Seq(exprs) => {
                //let current_index = env.current_block();
                //let data = g.node_weight(current_index).unwrap();

                let mut out = vec![];
                for expr in exprs {
                    out.push(expr.build_graph(d, env, b)?);
                    /*
                    if let IRKind::Block(block) = &expr.kind {
                        let block_index = env.add_block(block.name, block.params.clone(), d, g);
                        g.add_edge(current_index, block_index, ());
                        for block_expr in &block.children {
                            block_expr.build_graph(d, env, g, b)?;
                        }
                    } else {
                        expr.build_graph(d, env, g, b)?;
                    }
                    */
                }
                Ok(b.ir_seq(out))
            }

            IRKind::Ret(exprs) => {
                let mut out = vec![];
                for expr in exprs {
                    out.push(expr.build_graph(d, env, b)?);
                }
                Ok(b.ir_ret(out))
            }

            IRKind::Label(ref _name, ref _args) => {
                //let index = env.add_block(*name, args.clone(), d, g);
                //env.enter_block(index, self.span.clone());
                Ok(self)
            }

            IRKind::Jump(label, ref args) => {
                let block_index = env.current_block();
                let target_index = env.lookup_block(label).unwrap();
                env.connect_block(block_index, target_index);
                let target = env.g.node_weight(target_index).unwrap();

                // check arity of target
                if target.params.len() == args.len() {
                    Ok(self)
                } else {
                    d.push_diagnostic(error(
                        &format!(
                            "Jump to block, mismatch parameters: to {}",
                            b.strings.resolve(&label),
                        ),
                        self.span.clone(),
                    ));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            IRKind::Get(name, ref _select) => {
                let current_block = env.current_block();
                //self.dump(b, 0);
                if let Some(_sym_index) = env.name_in_scope(current_block, name) {
                    Ok(self)
                } else {
                    d.push_diagnostic(error(
                        &format!("Get undefined variable: {:?}", b.strings.resolve(&name)),
                        self.span.clone(),
                    ));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            IRKind::Set(name, value, select) => {
                let current_index = env.current_block();
                if let Some(_index) = env.name_in_scope(current_index, name) {
                    let value = value.build_graph(d, env, b)?;
                    Ok(b.ir_set(name, value, select))
                } else {
                    d.push_diagnostic(error(
                        &format!("Set undefined variable: {:?}", b.strings.resolve(&name)),
                        self.span.clone(),
                    ));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            IRKind::Decl(name, ref ty, _mem) => {
                let current_block = env.current_block();
                let index = env.add_definition(current_block, name);
                env.set_type(index, ty.clone(), VarDefinitionSpace::default());
                Ok(self)
            }

            IRKind::Call(_name, ref _args) => Ok(self),

            IRKind::Func(blocks, ret_type) => {
                let current_block = env.current_block();
                let mut seq = vec![];
                for (i, mut block) in blocks.into_iter().enumerate() {
                    let block_index = env.add_block(block.name, block.params.clone(), d);
                    block.index = block_index;
                    if 0 == i {
                        env.g.add_edge(current_block, block_index, ());
                    }
                    seq.push(block);
                }

                let mut blocks = vec![];
                for mut block in seq {
                    env.enter_block(block.index, self.span.clone());
                    let mut children = vec![];
                    for child in block.children {
                        children.push(child.build_graph(d, env, b)?);
                    }
                    env.exit_block();
                    block.children = children;
                    blocks.push(block);
                }
                Ok(IRNode {
                    kind: IRKind::Func(blocks, ret_type),
                    span,
                })
            }

            IRKind::Block(mut block) => {
                //let span = self.get_span().clone();
                let block_index = env.add_block(block.name, block.params.clone(), d);
                block.index = block_index;
                env.enter_block(block_index, span.clone());
                if let Some(last_block) = env.stack.last() {
                    if last_block.0 != block_index {
                        env.g.add_edge(last_block.0, block_index, ());
                    }
                }

                let mut children = vec![];
                for (_i, child) in block.children.into_iter().enumerate() {
                    children.push(child.build_graph(d, env, b)?);
                }
                env.exit_block();
                block.children = children;
                Ok(IRNode {
                    kind: IRKind::Block(block),
                    span,
                })
            }

            IRKind::Literal(ref _lit) => Ok(self),

            IRKind::Builtin(ref _bi, ref _args) => Ok(self),

            IRKind::Branch(condition, then_key, else_key) => {
                let condition = condition.build_graph(d, env, b)?;
                let current_block = env.current_block();
                let then_block = env.lookup_block(then_key).unwrap();
                env.g.add_edge(current_block, then_block, ());
                let else_block = env.lookup_block(else_key).unwrap();
                env.g.add_edge(current_block, else_block, ());
                Ok(b.ir_branch(condition, then_key, else_key))
            }

            IRKind::Cond(condition, then_expr, maybe_else_expr) => {
                let condition = condition.build_graph(d, env, b)?;
                let current_block = env.current_block();

                let next_block = env.add_block(b.s("next"), vec![], d);

                let then_block = env.add_block(b.s("then"), vec![], d);
                //let then_term = then_expr.kind.terminator();
                let then_expr = then_expr.build_graph(d, env, b)?;
                env.g.add_edge(current_block, then_block, ());
                env.g.add_edge(then_block, next_block, ());
                let maybe_else_expr = if let Some(else_expr) = maybe_else_expr {
                    let else_block = env.add_block(b.s("else"), vec![], d);
                    env.enter_block(else_block, else_expr.span.clone());
                    let else_expr = else_expr.build_graph(d, env, b)?;
                    env.exit_block();
                    env.g.add_edge(current_block, else_block, ());
                    env.g.add_edge(else_block, next_block, ());
                    Some(else_expr)
                } else {
                    None
                };
                Ok(b.ir_cond(condition, then_expr, maybe_else_expr))
            }

            IRKind::Op1(op, a) => {
                let a = a.build_graph(d, env, b)?;
                Ok(b.ir_op1(op, a))
            }

            IRKind::Op2(op_node, x, y) => {
                let x = x.build_graph(d, env, b)?;
                let y = y.build_graph(d, env, b)?;
                Ok(b.ir_op2(op_node, x, y))
            }
        }
    }
}

impl<E: Extra> AstNode<E> {
    pub fn normalize<'c>(mut self, d: &mut Diagnostics, b: &mut NodeBuilder<E>) -> Self {
        self.preprocess(d, b);
        self.analyze(b);
        self
    }

    pub fn preprocess<'c>(&mut self, d: &mut Diagnostics, b: &mut NodeBuilder<E>) {
        match &mut self.node {
            _ => (),
        }
        for child in self.children_mut() {
            child.preprocess(d, b);
        }
    }

    pub fn analyze<'c>(&mut self, b: &mut NodeBuilder<E>) {
        b.identify_node(self);
        for child in self.children_mut() {
            child.analyze(b);
        }
    }
    pub fn lower_ir_expr<'c>(
        self,
        d: &mut Diagnostics,
        env: &mut IREnvironment,
        b: &mut NodeBuilder<E>,
    ) -> Result<(IRNode, AstType)> {
        let mut out = vec![];
        let ty = self.lower_ir(&mut out, d, env, b)?;
        if out.len() == 0 {
            Ok((b.ir_noop(), ty))
        } else if out.len() == 1 {
            Ok((out.pop().unwrap(), ty))
        } else {
            Ok((b.ir_seq(out), ty))
        }
    }

    pub fn lower_ir<'c>(
        self,
        out: &mut Vec<IRNode>,
        d: &mut Diagnostics,
        env: &mut IREnvironment,
        b: &mut NodeBuilder<E>,
    ) -> Result<AstType> {
        if !self.node_id.is_valid() {
            d.push_diagnostic(self.extra.error(&format!("Invalid NodeID: {:#?}", self)));
            return Err(Error::new(ParseError::Invalid));
        }

        match self.node {
            Ast::Noop => Ok(AstType::Unit),

            Ast::Sequence(exprs) => {
                let mut ty = AstType::Unit;
                for expr in exprs {
                    let (ir, ret_ty) = expr.lower_ir_expr(d, env, b)?;
                    out.extend(ir.to_vec());
                    ty = ret_ty;
                }
                Ok(ty)
            }

            Ast::Return(maybe_expr) => {
                let mut args = vec![];
                let mut ty = AstType::Unit;
                if let Some(expr) = maybe_expr {
                    ty = expr.lower_ir(&mut args, d, env, b)?;
                }
                out.push(b.ir_ret(args));
                Ok(ty)
            }

            Ast::Label(name, ast_args) => {
                let mut args = vec![];
                for a in &ast_args {
                    args.push(IRArg {
                        name: a.name,
                        ty: a.ty.clone(),
                    });
                }
                out.push(b.ir_label(name, args));
                Ok(AstType::Unit)
            }

            Ast::Goto(label, ast_args) => {
                let mut args = vec![];
                for a in ast_args.into_iter() {
                    let Argument::Positional(expr) = a;
                    let (ir, _ty) = expr.lower_ir_expr(d, env, b)?;
                    args.push(ir);
                }

                out.push(b.ir_jump(label, args));
                Ok(AstType::Unit)
            }

            Ast::Identifier(name) => {
                let current_block = env.current_block();
                if let Some(sym_index) = env.name_in_scope(current_block, name) {
                    let (ty, _mem) = env.lookup_type(sym_index).unwrap();
                    out.push(b.ir_get(name, IRTypeSelect::default()));
                    Ok(ty)
                } else {
                    d.push_diagnostic(
                        self.extra
                            .error(&format!("Name not found: {}", b.strings.resolve(&name))),
                    );
                    Err(Error::new(ParseError::Invalid))
                }
            }

            Ast::Global(ident, expr) => {
                if let Ast::Literal(ref _lit) = expr.node {
                    let (v, ty) = expr.lower_ir_expr(d, env, b)?;
                    out.push(b.ir_decl(ident, ty.clone(), VarDefinitionSpace::Static));
                    out.push(b.ir_set(ident, v, IRTypeSelect::default()));
                    let current_block = env.current_block();
                    let index = env.add_definition(current_block, ident);
                    env.set_type(index, ty.clone(), VarDefinitionSpace::Static);

                    /*

                    let is_static = env.root() == current_block;

                    let (global_name_key, global_name) = if is_static {
                        (ident, b.strings.resolve(&ident).clone())
                    } else {
                        // we create a unique global name to prevent conflict
                        // and then we add ops to provide a local reference to the global name
                        let name = b.unique_static_name();
                        let name = format!("{}{}", b.strings.resolve(&ident), name).clone();
                        (b.strings.intern(name.clone()), name)
                    };

                    let ty: AstType = lit.into();
                    let v = expr.lower_ir_expr(context, d, env, g, b)?;

                    let data = g.node_weight_mut(env.root()).unwrap();
                    let index = data.add_definition(global_name_key);
                    //let v = IRNode::new(IRKind::Literal(lit.clone()), self.extra.get_span());
                    //env.set_type(index, ty.clone());
                    out.push(b.ir_decl(global_name_key, ty));
                    out.push(b.ir_set(global_name_key, v, IRTypeSelect::default()));
                    */
                    Ok(ty)
                } else {
                    unimplemented!()
                }
            }

            Ast::Assign(target, expr) => match target {
                AssignTarget::Alloca(name) | AssignTarget::Identifier(name) => {
                    let (ir, ty) = expr.lower_ir_expr(d, env, b)?;
                    let current_block = env.current_block();
                    if let Some(sym_index) = env.name_in_scope(current_block, name) {
                        let (ty, mem) = env.lookup_type(sym_index).unwrap();
                        out.push(b.ir_set(name, ir, IRTypeSelect::Offset(0)));
                        env.set_type(sym_index, ty.clone(), mem);
                        Ok(ty)
                    } else {
                        out.push(b.ir_decl(name, ty.clone(), VarDefinitionSpace::Stack));
                        out.push(b.ir_set(name, ir, IRTypeSelect::Offset(0)));
                        let index = env.add_definition(current_block, name);
                        env.set_type(index, ty.clone(), VarDefinitionSpace::Stack);
                        Ok(ty)
                    }
                }
            },

            Ast::Mutate(lhs, rhs) => match lhs.node {
                Ast::Identifier(name) => {
                    let (ir, ty) = rhs.lower_ir_expr(d, env, b)?;
                    out.push(b.ir_set(name, ir, IRTypeSelect::Offset(0)));
                    Ok(ty)
                }
                _ => unimplemented!("{:?}", &lhs.node),
            },

            Ast::Call(expr, args, _ret_ty) => {
                // function to call
                let current_block = env.current_block();
                let (f, ty, f_args, name) = match &expr.node {
                    Ast::Identifier(ident) => {
                        let name = b.strings.resolve(ident);
                        if let Some(index) = env.name_in_scope(current_block, *ident) {
                            if let Some((ty, _mem)) = env.lookup_type(index) {
                                if let AstType::Func(f_args, _) = ty.clone() {
                                    (ident, ty, f_args, name)
                                } else {
                                    d.push_diagnostic(
                                        self.extra.error(&format!(
                                            "Type not function: {}, {:?}",
                                            name, ty
                                        )),
                                    );
                                    return Err(Error::new(ParseError::Invalid));
                                }
                            } else {
                                d.push_diagnostic(
                                    self.extra
                                        .error(&format!("Type not found: {}, {:?}", name, index)),
                                );
                                return Err(Error::new(ParseError::Invalid));
                            }
                        } else {
                            d.push_diagnostic(
                                self.extra.error(&format!("Name not found: {}", name)),
                            );
                            return Err(Error::new(ParseError::Invalid));
                        }
                    }
                    _ => {
                        unimplemented!("{:?}", expr.node);
                    }
                };

                if let AstType::Func(_func_arg_types, ret) = &ty {
                    if f_args.len() != args.len() {
                        d.push_diagnostic(
                            self.extra.error(&format!("Call arity mismatch: {}", name)),
                        );
                        return Err(Error::new(ParseError::Invalid));
                    }

                    let mut ir_args = vec![];
                    for a in args {
                        match a {
                            Argument::Positional(expr) => {
                                expr.lower_ir(&mut ir_args, d, env, b)?;
                            }
                        }
                    }
                    out.push(b.ir_call(*f, ir_args));
                    Ok(*ret.clone())
                } else {
                    unimplemented!("calling non function type: {:?}", ty);
                }
            }

            Ast::Definition(mut def) => {
                def = def.normalize(b);
                let current_block = env.current_block();
                assert!(env.block_is_static(current_block));

                let mut ast_types = vec![];
                for p in &def.params {
                    match p.node {
                        Parameter::Normal => {
                            //| Parameter::WithDefault(_) => {
                            ast_types.push(p.ty.clone());
                        } //_ => unimplemented!("{:?}", p),
                    }
                }
                let ast_ret_type = *def.return_type;
                let f_type = AstType::Func(ast_types, ast_ret_type.clone().into());

                let index = env.add_definition(current_block, def.name);
                //let data = g.node_weight_mut(current_block).unwrap();
                //let index = data.add_definition(def.name);
                env.set_type(index, f_type.clone(), VarDefinitionSpace::Static);
                out.push(b.ir_decl(def.name, f_type, VarDefinitionSpace::Static));

                let mut output_blocks = vec![];
                let mut edges = vec![];
                if let Some(body) = def.body {
                    let blocks = body.try_seq().unwrap();

                    for (i, block) in blocks.into_iter().enumerate() {
                        if let Ast::Block(mut nb) = block.node {
                            let mut args = vec![];
                            for a in &nb.params {
                                args.push(IRArg {
                                    name: a.name,
                                    ty: a.ty.clone(),
                                });
                            }

                            if 0 == i {
                                nb.name = def.name;
                            }

                            let block_index = env.add_block(nb.name, args.clone(), d);
                            edges.push((current_block, block_index));

                            output_blocks.push((nb, block_index));
                        } else {
                            unreachable!()
                        }
                    }
                }

                for (a, b) in edges {
                    env.g.add_edge(a, b, ());
                }

                if output_blocks.len() > 0 {
                    let mut blocks = vec![];
                    let span = self.extra.get_span();
                    for (_i, (nb, block_index)) in output_blocks.into_iter().enumerate() {
                        env.enter_block(block_index, span.clone());

                        let mut args = vec![];
                        for a in nb.params {
                            args.push(IRArg {
                                name: a.name,
                                ty: a.ty,
                            });
                        }

                        let mut exprs = vec![];
                        let (ir, _ty) = nb.body.lower_ir_expr(d, env, b)?;
                        exprs.extend(ir.to_vec());

                        let block = IRBlock::new(nb.name, args, exprs);
                        blocks.push(block);
                        env.exit_block();
                    }

                    let mut s = IRBlockSorter::new();
                    for (_i, block) in blocks.into_iter().enumerate() {
                        s.sort_block(block, b);
                    }
                    s.close_block(b);
                    let blocks = s.blocks;

                    let ir = IRNode::new(IRKind::Func(blocks, ast_ret_type), span);
                    out.push(b.ir_set(def.name, ir, IRTypeSelect::default()));
                }
                Ok(AstType::Unit)
            }

            Ast::Literal(lit) => {
                let ir = match lit {
                    Literal::Float(f) => b.ir_float(f),
                    Literal::Int(f) => b.ir_integer(f),
                    Literal::Index(f) => b.ir_index(f),
                    Literal::Bool(f) => b.ir_bool(f),
                    Literal::String(ref f) => b.ir_string(f.clone()),
                    _ => unimplemented!("{:?}", lit),
                };
                let ty = lit.into();
                out.push(ir);
                Ok(ty)
            }

            Ast::Builtin(bi, args) => {
                let mut ir_args = vec![];
                for a in args {
                    match a {
                        Argument::Positional(expr) => {
                            expr.lower_ir(&mut ir_args, d, env, b)?;
                        }
                    }
                }
                out.push(IRNode::new(
                    IRKind::Builtin(bi, ir_args),
                    self.extra.get_span(),
                ));
                Ok(AstType::Unit)
            }

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
                let current_block = env.current_block();
                let b_then = env.fresh_label("then", b);
                let b_next = env.fresh_label("next", b);

                // then
                let then_index = env.add_block(b_then, vec![], d);
                //let span = then_expr.extra.get_span();
                env.g.add_edge(current_block, then_index, ());
                let mut then_seq = vec![b.ir_label(b_then, vec![])];
                let (then_block, _ty) = then_expr.lower_ir_expr(d, env, b)?;
                let term = then_block.kind.terminator();
                then_seq.extend(then_block.to_vec());
                if term.is_none() {
                    then_seq.push(b.ir_jump(b_next, vec![]));
                }

                // else
                let (b_else, else_seq) = if let Some(else_expr) = maybe_else_expr {
                    //let else_index = env.add_block(b_then, vec![], d, g);
                    //let span = else_expr.extra.get_span();
                    let b_else = Some(env.fresh_label("else", b));
                    let mut else_seq = vec![b.ir_label(b_else.unwrap(), vec![])];
                    let (else_block, _ty) = else_expr.lower_ir_expr(d, env, b)?;
                    //g.add_edge(current_block, else_block, ());
                    let term = else_block.kind.terminator();
                    else_seq.extend(else_block.to_vec());
                    if term.is_none() {
                        else_seq.push(b.ir_jump(b_next, vec![]));
                        //g.add_edge(else_index, then_index, ());
                    }
                    (b_else, Some(else_seq))
                } else {
                    (None, None)
                };

                let (ir_cond, _ty) = condition.lower_ir_expr(d, env, b)?;

                out.push(b.ir_branch(ir_cond, b_then, b_else.unwrap_or(b_next)));
                out.extend(then_seq);
                if let Some(seq) = else_seq {
                    out.extend(seq);
                }
                out.push(b.ir_label(b_next, vec![]));
                Ok(AstType::Unit)
            }

            Ast::UnaryOp(op, a) => {
                let (ir, ty) = a.lower_ir_expr(d, env, b)?;
                out.push(b.ir_op1(op, ir));
                Ok(ty)
            }

            Ast::BinaryOp(op_node, x, y) => {
                let (x, _ty) = x.lower_ir_expr(d, env, b)?;
                let (y, ty) = y.lower_ir_expr(d, env, b)?;
                out.push(b.ir_op2(op_node.node, x, y));
                Ok(ty)
            }

            // do nothing
            Ast::Deref(expr, _target) => expr.lower_ir(out, d, env, b),

            Ast::Error => {
                d.push_diagnostic(self.extra.error(&format!("Error")));
                Err(Error::new(ParseError::Invalid))
            }
            _ => {
                d.push_diagnostic(
                    self.extra
                        .error(&format!("Ast Unimplemented: {:?}", self.node)),
                );
                Err(Error::new(ParseError::Invalid))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::SimpleExtra;
    use crate::tests::gen_block;
    use crate::{Diagnostics, NodeBuilder};
    use test_log::test;

    #[test]
    fn test_ir_1() {
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let mut b: NodeBuilder<SimpleExtra> = NodeBuilder::new();
        b.enter(file_id, "type.py");

        let mut env = IREnvironment::new();
        let ast = gen_block(&mut b).normalize(&mut d, &mut b);
        let index = env.add_block(b.s("module"), vec![], &d);
        env.enter_block(index, ast.extra.get_span());

        let r = ast.lower_ir_expr(&mut d, &mut env, &mut b);
        d.dump();
        assert!(!d.has_errors);
        let (ir, _ty) = r.unwrap();
        println!("ir: {:#?}", ir);
        ir.dump(&b, 0);
        assert_eq!(1, env.stack.len());
    }

    #[test]
    fn test_ir_2() {
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let mut b: NodeBuilder<SimpleExtra> = NodeBuilder::new();
        b.enter(file_id, "type.py");

        let mut env = IREnvironment::new();

        let ast = crate::tests::gen_function_call(&mut b).normalize(&mut d, &mut b);

        let index = env.add_block(b.s("module"), vec![], &d);
        env.enter_block(index, ast.extra.get_span());

        let r = ast.lower_ir_expr(&mut d, &mut env, &mut b);
        d.dump();
        assert!(!d.has_errors);
        let (ir, _ty) = r.unwrap();
        println!("ir: {:#?}", ir);
        ir.dump(&b, 0);
        assert_eq!(1, env.stack.len());
    }
}
