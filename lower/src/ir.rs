use anyhow::Error;
use anyhow::Result;

use crate::cfg::SymIndex;
use crate::{AstNode, AstType, Diagnostics, Extra, NodeBuilder, ParseError, StringKey};
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
    name: StringKey,
    ty: AstType,
}

#[derive(Debug)]
pub struct IRBlock {
    name: StringKey,
    params: Vec<IRArg>,
    children: Vec<IRNode>,
}

impl IRBlock {
    pub fn new(name: StringKey, params: Vec<IRArg>, children: Vec<IRNode>) -> Self {
        Self {
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
    types: HashMap<SymIndex, AstType>,
    label_count: usize,
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

    pub fn lookup_type(&self, index: SymIndex) -> Option<AstType> {
        self.types.get(&index).cloned()
    }

    pub fn set_type(&mut self, index: SymIndex, ty: AstType) {
        self.types.insert(index, ty);
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
        println!("enter: {:?}", self.stack);
    }

    pub fn exit_block(&mut self) {
        self.stack.pop();
        println!("exit: {:?}", self.stack);
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

    pub fn add_block(
        &mut self,
        name: StringKey,
        params: Vec<IRArg>,
        d: &Diagnostics,
        g: &mut IRGraph,
    ) -> NodeIndex {
        let index = g.add_node(IRControlBlock::new(params));
        g.node_weight_mut(index).unwrap().block_index = index;
        self.block_names.insert(name, index);
        self.block_names_index.insert(index, name);
        index
    }

    pub fn add_edge(&mut self, a: StringKey, b: StringKey, g: &mut IRGraph) {
        let index_a = self.block_names.get(&a).unwrap();
        let index_b = self.block_names.get(&b).unwrap();
        g.add_edge(*index_a, *index_b, ());
    }

    pub fn name_in_scope(
        &self,
        index: NodeIndex,
        name: StringKey,
        g: &IRGraph,
    ) -> Option<SymIndex> {
        let maybe_dom = simple_fast(g, self.root())
            .dominators(index)
            .map(|it| it.collect::<Vec<_>>());
        //println!("dom: {:?} => {:?}", index, dom);
        if let Some(dom) = maybe_dom {
            for i in dom.into_iter().rev() {
                let data = g.node_weight(i).unwrap();
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
        g: &IRGraph,
        b: &NodeBuilder<E>,
        index: NodeIndex,
        current_block: NodeIndex,
        depth: usize,
    ) {
        let data = &g[index];
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
        for n in g.neighbors(index) {
            self.dump_node(g, b, n, current_block, depth + 1);
        }
    }

    pub fn dump<E>(&self, g: &IRGraph, b: &NodeBuilder<E>, current_block: NodeIndex) {
        self.dump_node(g, b, self.root(), current_block, 0);
    }

    pub fn save_graph<E>(&self, filename: &str, g: &IRGraph, b: &NodeBuilder<E>) {
        use petgraph::dot::{Config, Dot};

        let s = format!(
            "{:?}",
            Dot::with_attr_getters(
                &g,
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
    Branch(Box<IRNode>, StringKey, Option<StringKey>),
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
            Self::Ret(_) => Some(Terminator::Return),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub struct IRNode {
    kind: IRKind,
    span: Span,
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

    pub fn run<E: Extra>(ir: IRNode, b: &mut NodeBuilder<E>) -> Vec<IRNode> {
        let mut s = Self::new();
        s.sort(ir, b);
        s.close_block(b);
        s.blocks(b)
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
                name: *name,
                params: args.clone(),
                // skip the first child which is a label, it's redundant now that we have a block
                children: self.stack.drain(..).skip(1).collect(),
            }
        } else {
            let offset = self.blocks.len();
            let name = b.strings.intern(format!("_block{}", offset));
            IRBlock {
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
                    "{:width$}branch({}, {:?})",
                    "",
                    b.strings.resolve(br_then),
                    br_else.map(|key| b.strings.resolve(&key)),
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
    /*
    pub fn to_blocks<'c, E: Extra>(
        &self,
        d: &mut Diagnostics,
        env: &mut IREnvironment,
        g: &mut IRGraph,
        b: &mut NodeBuilder<E>,
    ) -> Result<Vec<IRNode>> {
        let mut out = vec![];
        if let IRKind::Block(block) = self {
            out.append(block.children
        }
    }
    */

    pub fn build_graph<'c, E: Extra>(
        &self,
        d: &mut Diagnostics,
        env: &mut IREnvironment,
        g: &mut IRGraph,
        b: &mut NodeBuilder<E>,
    ) -> Result<()> {
        match &self.kind {
            IRKind::Noop => Ok(()),

            IRKind::Seq(exprs) => {
                let current_index = env.current_block();
                //let data = g.node_weight(current_index).unwrap();

                for expr in exprs {
                    if let IRKind::Block(block) = &expr.kind {
                        let block_index = env.add_block(block.name, block.params.clone(), d, g);
                        g.add_edge(current_index, block_index, ());
                        for block_expr in &block.children {
                            block_expr.build_graph(d, env, g, b)?;
                        }
                    } else {
                        expr.build_graph(d, env, g, b)?;
                    }
                }
                Ok(())
            }

            IRKind::Ret(exprs) => {
                for expr in exprs {
                    expr.build_graph(d, env, g, b)?;
                }
                Ok(())
            }

            IRKind::Label(name, args) => {
                let index = env.add_block(*name, args.clone(), d, g);
                env.enter_block(index, self.span.clone());
                Ok(())
            }

            IRKind::Jump(label, args) => {
                let block_index = env.current_block();
                let target_index = env.lookup_block(*label).unwrap();
                let target = g.node_weight(target_index).unwrap();
                // check arity of target
                assert_eq!(target.params.len(), args.len());
                g.add_edge(block_index, target_index, ());
                Ok(())
            }

            IRKind::Get(name, ref _select) => {
                let current_block = env.current_block();
                //self.dump(b, 0);
                if let Some(_sym_index) = env.name_in_scope(current_block, *name, g) {
                    Ok(())
                } else {
                    d.push_diagnostic(error(
                        &format!("Get undefined variable: {:?}", b.strings.resolve(&name)),
                        self.span.clone(),
                    ));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            IRKind::Set(name, value, ref _select) => {
                let current_index = env.current_block();
                if let Some(_index) = env.name_in_scope(current_index, *name, g) {
                    //let data = g.node_weight_mut(index.block()).unwrap();
                    //data.add_symbol(name, index);
                    value.build_graph(d, env, g, b)?;
                    Ok(())
                } else {
                    d.push_diagnostic(error(
                        &format!("Set undefined variable: {:?}", b.strings.resolve(&name)),
                        self.span.clone(),
                    ));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            IRKind::Decl(name, ty, _mem) => {
                let current_block = env.current_block();
                let data = g.node_weight_mut(current_block).unwrap();
                let index = data.add_definition(*name);
                env.set_type(index, ty.clone());
                Ok(())
            }

            IRKind::Call(_name, _args) => Ok(()),

            IRKind::Func(blocks, _ret_type) => {
                let current_block = env.current_block();
                for (i, block) in blocks.iter().enumerate() {
                    let block_index = env.add_block(block.name, block.params.clone(), d, g);
                    if 0 == i {
                        g.add_edge(current_block, block_index, ());
                    }
                    env.enter_block(block_index, self.span.clone());

                    let data = g.node_weight_mut(block_index).unwrap();
                    for p in &block.params {
                        data.push_arg(p.name);
                    }

                    for child in &block.children {
                        child.build_graph(d, env, g, b)?;
                    }

                    env.exit_block();
                }
                Ok(())
            }

            /*
            IRKind::Block(block) => {
                let mut edges = vec![];
                let current_block = env.current_block();
                let current = g.node_weight_mut(current_block).unwrap();
                let block_index = env.add_block(block.name, block.params.clone(), d, g);
                let block_index = env.lookup_block(block.name).unwrap();
                env.enter_block(block_index);
                for (i, _child) in block.children.into_iter().enumerate() {
                    edges.push((current_block, block_index));
                    let mut data = g.node_weight_mut(block_index).unwrap();
                    for a in &block.params {
                        data.push_arg(a.name);
                    }
                }
                env.exit_block9);
                Ok(())
            }
            */
            IRKind::Literal(_lit) => Ok(()),

            IRKind::Builtin(_bi, _args) => Ok(()),

            IRKind::Cond(condition, then_expr, maybe_else_expr) => {
                condition.build_graph(d, env, g, b)?;
                let current_block = env.current_block();

                let next_block = env.add_block(b.s("next"), vec![], d, g);

                let then_block = env.add_block(b.s("then"), vec![], d, g);
                //let then_term = then_expr.kind.terminator();
                then_expr.build_graph(d, env, g, b)?;
                g.add_edge(current_block, then_block, ());
                g.add_edge(then_block, next_block, ());
                if let Some(else_expr) = maybe_else_expr {
                    let else_block = env.add_block(b.s("else"), vec![], d, g);
                    env.enter_block(else_block, else_expr.span.clone());
                    else_expr.build_graph(d, env, g, b)?;
                    env.exit_block();
                    g.add_edge(current_block, else_block, ());
                    g.add_edge(else_block, next_block, ());
                };
                Ok(())
            }

            IRKind::Op1(_op, a) => {
                a.build_graph(d, env, g, b)?;
                Ok(())
            }

            IRKind::Op2(_op_node, x, y) => {
                x.build_graph(d, env, g, b)?;
                y.build_graph(d, env, g, b)?;
                Ok(())
            }

            _ => {
                d.push_diagnostic(error(
                    &format!("Unimplemented: {:?}", self.kind,),
                    self.span.clone(),
                ));
                Err(Error::new(ParseError::Invalid))
            }
        }
    }
}

impl<E: Extra> AstNode<E> {
    pub fn lower_ir_expr<'c>(
        self,
        //context: &'c Context,
        d: &mut Diagnostics,
        env: &mut IREnvironment,
        g: &mut IRGraph,
        b: &mut NodeBuilder<E>,
    ) -> Result<IRNode> {
        let mut out = vec![];
        self.lower_ir(&mut out, d, env, g, b)?;
        if out.len() == 0 {
            Ok(b.ir_noop())
        } else if out.len() == 1 {
            Ok(out.pop().unwrap())
        } else {
            Ok(b.ir_seq(out))
        }
    }

    pub fn lower_ir<'c>(
        self,
        //context: &'c Context,
        out: &mut Vec<IRNode>,
        d: &mut Diagnostics,
        env: &mut IREnvironment,
        g: &mut IRGraph,
        b: &mut NodeBuilder<E>,
    ) -> Result<()> {
        if !self.node_id.is_valid() {
            d.push_diagnostic(self.extra.error(&format!("Invalid NodeID: {:#?}", self)));
            return Err(Error::new(ParseError::Invalid));
        }

        match self.node {
            Ast::Noop => Ok(()),

            Ast::Sequence(exprs) => {
                for expr in exprs {
                    let ir = expr.lower_ir_expr(d, env, g, b)?.to_vec();
                    out.extend(ir);
                }
                Ok(())
            }

            Ast::Return(maybe_expr) => {
                let mut args = vec![];
                if let Some(expr) = maybe_expr {
                    expr.lower_ir(&mut args, d, env, g, b)?;
                }
                out.push(b.ir_ret(args));
                Ok(())
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
                Ok(())
            }
            Ast::Goto(label, ast_args) => {
                let mut args = vec![];
                for a in ast_args.into_iter() {
                    let Argument::Positional(expr) = a;
                    let ir = expr.lower_ir_expr(d, env, g, b)?;
                    args.push(ir);
                }

                out.push(b.ir_jump(label, args));
                Ok(())
            }

            Ast::Identifier(name) => {
                out.push(b.ir_get(name, IRTypeSelect::default()));
                Ok(())
            }

            Ast::Global(ident, expr) => {
                if let Ast::Literal(ref lit) = expr.node {
                    let ty: AstType = lit.into();
                    let v = expr.lower_ir_expr(d, env, g, b)?;
                    out.push(b.ir_decl(ident, ty.clone(), VarDefinitionSpace::Static));
                    out.push(b.ir_set(ident, v, IRTypeSelect::default()));
                    let current_block = env.current_block();
                    let data = g.node_weight_mut(current_block).unwrap();
                    let index = data.add_definition(ident);
                    env.set_type(index, ty);

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
                    Ok(())
                } else {
                    unimplemented!()
                }
            }

            Ast::Assign(target, expr) => match target {
                AssignTarget::Alloca(name) | AssignTarget::Identifier(name) => {
                    let mut seq = vec![];
                    expr.lower_ir(&mut seq, d, env, g, b)?;
                    let current_block = env.current_block();
                    if let Some(_sym_index) = env.name_in_scope(current_block, name, g) {
                        out.push(b.ir_set(name, b.ir_seq(seq), IRTypeSelect::Offset(0)));
                        Ok(())
                    } else {
                        let ty = AstType::Int;
                        out.push(b.ir_decl(name, ty.clone(), VarDefinitionSpace::default()));
                        let data = g.node_weight_mut(current_block).unwrap();
                        let index = data.add_definition(name);
                        env.set_type(index, ty);
                        Ok(())
                    }
                }
            },

            Ast::Mutate(lhs, rhs) => match lhs.node {
                Ast::Identifier(name) => {
                    let mut seq = vec![];
                    rhs.lower_ir(&mut seq, d, env, g, b)?;
                    out.push(b.ir_set(name, b.ir_seq(seq), IRTypeSelect::Offset(0)));
                    Ok(())
                }
                _ => unimplemented!("{:?}", &lhs.node),
            },

            Ast::Call(expr, args, _ret_ty) => {
                // function to call
                let current_block = env.current_block();
                env.dump(g, b, current_block);
                let (f, ty, f_args, name) = match &expr.node {
                    Ast::Identifier(ident) => {
                        let name = b.strings.resolve(ident);
                        if let Some(index) = env.name_in_scope(current_block, *ident, g) {
                            if let Some(ty) = env.lookup_type(index) {
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

                if let AstType::Func(_func_arg_types, _ret) = &ty {
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
                                expr.lower_ir(&mut ir_args, d, env, g, b)?;
                            }
                        }
                    }
                    out.push(b.ir_call(*f, ir_args));
                    Ok(())
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
                        }
                        _ => unimplemented!("{:?}", p),
                    }
                }
                let ast_ret_type = *def.return_type;
                let f_type = AstType::Func(ast_types, ast_ret_type.clone().into());

                let data = g.node_weight_mut(current_block).unwrap();
                let index = data.add_definition(def.name);
                env.set_type(index, f_type.clone());
                out.push(b.ir_decl(def.name, f_type, VarDefinitionSpace::default()));
                println!("declare: {}", b.strings.resolve(&def.name));

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
                                //nb.params = args;
                            }

                            let block_index = env.add_block(nb.name, args.clone(), d, g);
                            edges.push((current_block, block_index));

                            let data = g.node_weight_mut(block_index).unwrap();
                            for a in &nb.params {
                                data.push_arg(a.name);
                            }

                            output_blocks.push((nb, block_index));
                        } else {
                            unreachable!()
                        }
                    }
                }

                for (a, b) in edges {
                    g.add_edge(a, b, ());
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
                        //if 0 == i {
                        //exprs.push(b.ir_label(def.name, args.clone()));
                        //}
                        exprs.extend(nb.body.lower_ir_expr(d, env, g, b)?.to_vec());

                        let block = IRBlock::new(nb.name, args, exprs);
                        blocks.push(block);
                        env.exit_block();
                    }

                    let mut s = IRBlockSorter::new();
                    for (_i, block) in blocks.into_iter().enumerate() {
                        s.sort_block(block, b);
                    }
                    s.close_block(b);

                    let ir = IRNode::new(IRKind::Func(s.blocks, ast_ret_type), span);
                    out.push(b.ir_set(def.name, ir, IRTypeSelect::default()));
                }
                Ok(())
            }

            Ast::Literal(lit) => {
                let ir = match lit {
                    Literal::Float(f) => b.ir_float(f),
                    Literal::Int(f) => b.ir_integer(f),
                    Literal::Index(f) => b.ir_index(f),
                    Literal::Bool(f) => b.ir_bool(f),
                    _ => unimplemented!("{:?}", lit),
                };
                out.push(ir);
                Ok(())
            }

            Ast::Builtin(bi, args) => {
                let mut ir_args = vec![];
                for a in args {
                    match a {
                        Argument::Positional(expr) => {
                            expr.lower_ir(&mut ir_args, d, env, g, b)?;
                        }
                    }
                }
                out.push(IRNode::new(
                    IRKind::Builtin(bi, ir_args),
                    self.extra.get_span(),
                ));
                Ok(())
            }

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
                let current_block = env.current_block();
                let b_then = env.fresh_label("then", b);
                let b_next = env.fresh_label("next", b);

                // then
                let then_index = env.add_block(b_then, vec![], d, g);
                //let span = then_expr.extra.get_span();
                g.add_edge(current_block, then_index, ());
                let mut then_seq = vec![b.ir_label(b_then, vec![])];
                let then_block = then_expr.lower_ir_expr(d, env, g, b)?;
                let term = then_block.kind.terminator();
                then_seq.extend(then_block.to_vec());
                if term.is_none() {
                    then_seq.push(b.ir_jump(b_next, vec![]));
                }

                // else
                let (b_else, else_seq) = if let Some(else_expr) = maybe_else_expr {
                    //let span = else_expr.extra.get_span();
                    let b_else = Some(env.fresh_label("else", b));
                    let mut else_seq = vec![b.ir_label(b_else.unwrap(), vec![])];
                    let else_block = else_expr.lower_ir_expr(d, env, g, b)?;
                    let term = else_block.kind.terminator();
                    else_seq.extend(else_block.to_vec());
                    if term.is_none() {
                        else_seq.push(b.ir_jump(b_next, vec![]));
                    }
                    (b_else, Some(else_seq))
                } else {
                    (None, None)
                };

                let ir_cond = condition.lower_ir_expr(d, env, g, b)?;
                out.push(b.ir_branch(ir_cond, b_then, b_else));
                out.extend(then_seq);
                if let Some(seq) = else_seq {
                    out.extend(seq);
                }
                out.push(b.ir_label(b_next, vec![]));
                Ok(())
            }

            Ast::UnaryOp(op, a) => {
                let ir = a.lower_ir_expr(d, env, g, b)?;
                out.push(b.ir_op1(op, ir));
                Ok(())
            }

            Ast::BinaryOp(op_node, x, y) => {
                let x = x.lower_ir_expr(d, env, g, b)?;
                let y = y.lower_ir_expr(d, env, g, b)?;
                out.push(b.ir_op2(op_node.node, x, y));
                Ok(())
            }

            Ast::Deref(expr, _target) => expr.lower_ir(out, d, env, g, b),

            Ast::Error => {
                d.push_diagnostic(self.extra.error(&format!("Error")));
                Err(Error::new(ParseError::Invalid))
            }
            _ => {
                d.push_diagnostic(self.extra.error(&format!("Unimplemented: {:?}", self.node)));
                Err(Error::new(ParseError::Invalid))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::SimpleExtra;
    use crate::cfg::{CFGGraph, CFG};
    use crate::tests::gen_block;
    use crate::{default_context, Diagnostics, NodeBuilder};
    use test_log::test;

    #[test]
    fn test_ir_1() {
        let context = default_context();
        let mut cfg_g = CFGGraph::new();
        let mut g = IRGraph::new();
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let mut b = NodeBuilder::new();
        b.enter(file_id, "type.py");

        let mut cfg: CFG<SimpleExtra> = CFG::new(
            &context,
            b.strings.intern("module".to_string()),
            &d,
            &mut cfg_g,
        );
        let mut env = IREnvironment::new();
        let ast = gen_block(&mut b).normalize(&mut cfg, &mut d, &mut b);
        //let mut stack = vec![cfg.root()];
        let index = env.add_block(b.s("module"), vec![], &d, &mut g);
        env.enter_block(index, ast.extra.get_span());

        let r = ast.lower_ir_expr(&mut d, &mut env, &mut g, &mut b);
        d.dump();
        assert!(!d.has_errors);
        let ir = r.unwrap();
        println!("ir: {:#?}", ir);
        ir.dump(&b, 0);
        assert_eq!(1, env.stack.len());
    }

    #[test]
    fn test_ir_2() {
        let context = default_context();
        let mut cfg_g = CFGGraph::new();
        let mut g = IRGraph::new();
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let mut b = NodeBuilder::new();
        b.enter(file_id, "type.py");

        let mut cfg: CFG<SimpleExtra> = CFG::new(
            &context,
            b.strings.intern("module".to_string()),
            &d,
            &mut cfg_g,
        );
        let mut env = IREnvironment::new();

        let ast = crate::tests::gen_function_call(&mut b).normalize(&mut cfg, &mut d, &mut b);

        let index = env.add_block(b.s("module"), vec![], &d, &mut g);
        env.enter_block(index, ast.extra.get_span());

        let r = ast.lower_ir_expr(&mut d, &mut env, &mut g, &mut b);
        d.dump();
        assert!(!d.has_errors);
        let ir = r.unwrap();
        println!("ir: {:#?}", ir);
        ir.dump(&b, 0);
        assert_eq!(1, env.stack.len());
    }
}
