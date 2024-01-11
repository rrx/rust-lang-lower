use crate::sort::IRBlockSorter;
use crate::{
    AstNode, AstType, BlockId, Diagnostics, Extra, IRPlaceTable, NodeBuilder, ParseError, PlaceId,
    PlaceNode, StringKey, StringLabel, SymIndex,
};

use anyhow::Error;
use anyhow::Result;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use indexmap::IndexMap;
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
    //Terminator,
    UnaryOperation,
    //VarDefinitionSpace,
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
    pub(crate) name: StringLabel,
    pub(crate) ty: AstType,
}

#[derive(Debug)]
pub struct IRBlock {
    pub(crate) index: NodeIndex,
    pub(crate) label: BlockId,
    pub(crate) params: Vec<IRArg>,
    pub(crate) children: Vec<IRNode>,
}

impl IRBlock {
    pub fn new(
        index: NodeIndex,
        label: BlockId,
        params: Vec<IRArg>,
        children: Vec<IRNode>,
    ) -> Self {
        Self {
            index,
            label,
            params,
            children,
        }
    }

    pub fn terminator(&self) -> Option<IRTerminator> {
        self.children.last().unwrap().kind.terminator()
    }
}

#[derive(Debug)]
pub struct IRControlBlock {
    arg_count: usize,
    pub(crate) block_index: NodeIndex,
    pub(crate) params: Vec<IRArg>,
    symbols: HashMap<StringLabel, PlaceId>,
    places: HashMap<PlaceId, SymIndex>,
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
            places: HashMap::new(),
        }
    }
    pub fn lookup(&self, name: StringLabel) -> Option<PlaceId> {
        self.symbols.get(&name).cloned()
    }

    pub fn alloca_add(&mut self, place_id: PlaceId, name: StringLabel, index: SymIndex) {
        self.symbols.insert(name, place_id);
        assert_eq!(index.block(), self.block_index);
        self.places.insert(place_id, index);
    }

    pub fn alloca_get(&self, place_id: PlaceId) -> Option<SymIndex> {
        self.places.get(&place_id).cloned()
    }

    pub fn push_arg(&mut self, place_id: PlaceId, name: StringLabel) -> SymIndex {
        assert!(self.arg_count < self.params.len());
        let index = SymIndex::Arg(self.block_index, self.arg_count);
        self.symbols.insert(name, place_id);
        self.arg_count += 1;
        index
    }

    pub fn add_definition(&mut self, _place_id: PlaceId) -> SymIndex {
        let offset = self.def_count;
        self.def_count += 1;
        let index = SymIndex::Def(self.block_index, offset);
        index
    }
}

pub type IRBlockGraph = DiGraph<IRControlBlock, ()>;

#[derive(Default, Debug)]
pub struct BlockTable {
    root: Option<NodeIndex>,
    pub g: IRBlockGraph,
    names: Vec<StringKey>,
    block_names: HashMap<BlockId, NodeIndex>,
    block_names_index: HashMap<NodeIndex, BlockId>,
}

impl BlockTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn set_root(&mut self, index: NodeIndex) {
        self.root = Some(index);
    }

    pub fn root(&self) -> NodeIndex {
        self.root.unwrap()
    }

    pub fn block_is_static(&self, block_index: NodeIndex) -> bool {
        // root block is static block, and there's only one for now
        self.root.unwrap() == block_index
    }

    pub fn fresh_block_label<E: Extra>(&mut self, name: &str, b: &mut NodeBuilder<E>) -> BlockId {
        let offset = self.names.len();
        let s = b.s(&format!("b_{}_{}", name, offset));
        self.names.push(s);
        //BlockLabel(offset as u32)
        //StringLabel::Block(offset)
        BlockId::U(offset)
    }

    /*
    pub fn fresh_label<E: Extra>(&mut self, name: &str, b: &mut NodeBuilder<E>) -> StringLabel {
        let block_label = self.fresh_block_label(name, b);
        //self.names.get(block_label.0 as usize).unwrap().clone()
        block_label
    }
    */

    pub fn lookup_block_label(&self, label: BlockId) -> Option<NodeIndex> {
        self.block_names.get(&label).cloned()
    }

    //pub fn lookup_block(&self, name: StringKey) -> Option<NodeIndex> {
    //self.block_names.get(&name).cloned()
    //}

    pub fn connect_block(&mut self, source: NodeIndex, target: NodeIndex) {
        self.g.add_edge(source, target, ());
    }

    pub fn add_block(
        &mut self,
        places: &mut IRPlaceTable,
        label: BlockId,
        params: Vec<IRArg>,
        _d: &Diagnostics,
    ) -> NodeIndex {
        let index = self.g.add_node(IRControlBlock::new(params.clone()));
        println!("add_block: index: {}, label: {:?}", index.index(), label);
        //let block_label = self.fresh_block_label(name, b);
        self.g.node_weight_mut(index).unwrap().block_index = index;
        //assert!(!self.block_names.contains_key(&label));
        self.block_names.insert(label, index);
        self.block_names_index.insert(index, label);

        let data = self.g.node_weight_mut(index).unwrap();
        for a in params {
            let p = PlaceNode::new_arg(a.name, a.ty);
            let place_id = places.add_place(p);
            data.push_arg(place_id, a.name);
        }

        index
    }

    pub fn dump_node<E: Extra>(
        &self,
        b: &NodeBuilder<E>,
        index: NodeIndex,
        current_block: NodeIndex,
        depth: usize,
    ) {
        let data = &self.g[index];
        let key = self.block_names_index.get(&index).unwrap();
        //let key = self.names.get(label.0 as usize).unwrap();
        let name = b.resolve_block_label(*key);
        if index == current_block {
            println!("{:width$}Current: {}", "", name, width = depth * 2);
        } else {
            println!("{:width$}Node: {}", "", name, width = depth * 2);
        }
        for (k, v) in data.symbols.iter() {
            println!(
                "{:width$}  Symbol: {}, {:?}, {:?}",
                "",
                b.resolve_label(*k),
                k,
                v,
                width = depth * 2
            );
        }
        for n in self.g.neighbors(index) {
            self.dump_node(b, n, current_block, depth + 1);
        }
    }

    pub fn save_graph<E: Extra>(&self, filename: &str, b: &NodeBuilder<E>) {
        use petgraph::dot::{Config, Dot};

        let s = format!(
            "{:?}",
            Dot::with_attr_getters(
                &self.g,
                &[Config::EdgeNoLabel, Config::NodeNoLabel],
                &|_, _er| String::new(),
                &|_, (index, data)| {
                    let label = self.block_names_index.get(&data.block_index).unwrap();
                    //let key = self.names.get(label.0 as usize).unwrap();
                    //let key = self.block_names_index.get(&data.block_index).unwrap();
                    let name = b.resolve_block_label(*label);
                    format!(
                        //"label = \"[{}]{}\" shape={:?}",
                        "label = \"{}:{:?}:{}\"",
                        index.index(),
                        label,
                        name,
                        //data.block_index.index(),
                        //&data.name,
                        //&data.ty.to_string()
                    )
                }
            )
        );
        //let path = std::fs::canonicalize(filename).unwrap();
        //println!("{}", path.clone().into_os_string().into_string().unwrap());
        println!("saved graph {}", filename);
        std::fs::write(filename, s).unwrap();
    }
}

#[derive(Debug)]
pub struct IREnvironment {
    stack: Vec<(NodeIndex, Span)>,
    places: IndexMap<PlaceId, SymIndex>,
    label_count: usize,
    pub blocks: BlockTable,
}

impl IREnvironment {
    pub fn new() -> Self {
        Self {
            stack: vec![],
            places: IndexMap::new(),
            label_count: 0,
            blocks: BlockTable::new(),
        }
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
        if self.stack.len() == 0 {
            self.blocks.set_root(index);
        }

        self.stack.push((index, span));
    }

    pub fn exit_block(&mut self) {
        self.stack.pop();
    }

    pub fn stack_size(&self) -> usize {
        self.stack.len()
    }

    pub fn root(&self) -> NodeIndex {
        self.blocks.root()
        //self.stack.first().unwrap().clone().0
    }

    pub fn current_block(&self) -> NodeIndex {
        self.stack.last().unwrap().clone().0
    }

    pub fn add_definition(
        &mut self,
        block_index: NodeIndex,
        place_id: PlaceId,
        name: StringLabel,
    ) -> SymIndex {
        let data = self.blocks.g.node_weight_mut(block_index).unwrap();
        let index = data.add_definition(place_id);
        data.alloca_add(place_id, name, index);
        self.places.insert(place_id, index);
        //data.add_symbol(name, index);
        index
    }

    pub fn block_name_in_scope(&self, index: NodeIndex, name: StringLabel) -> Option<PlaceId> {
        let maybe_dom = simple_fast(&self.blocks.g, self.root())
            .dominators(index)
            .map(|it| it.collect::<Vec<_>>());
        //println!("dom: {:?} => {:?}", index, maybe_dom);
        if let Some(dom) = maybe_dom {
            for i in dom.into_iter().rev() {
                let data = self.blocks.g.node_weight(i).unwrap();
                //println!("searching {:?}", (i, name));
                if let Some(place_id) = data.symbols.get(&name) {
                    //println!("found {:?}", (place_id, name));
                    return Some(*place_id);
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

    pub fn dump<E: Extra>(&self, b: &NodeBuilder<E>, current_block: NodeIndex) {
        let root = self.blocks.block_names_index.get(&self.root()).unwrap();
        let current = self.blocks.block_names_index.get(&current_block).unwrap();
        println!("dump: root: {:?} => {:?}", self.root(), current_block);
        println!(
            "dump: root: {:?} => {:?}",
            b.resolve_block_label(*root),
            b.resolve_block_label(*current)
        );

        self.blocks.dump_node(b, self.root(), current_block, 0);
        self.blocks.save_graph("out.dot", b);
    }
}

#[derive(Debug)]
pub enum IRTerminator {
    Jump(BlockId),
    Branch(BlockId, BlockId),
    Return,
}

#[derive(Debug)]
pub enum IRKind {
    Decl(PlaceId),
    // set(variable, expr, type offset)
    Set(PlaceId, Box<IRNode>, IRTypeSelect),
    // get(variable, type offset)
    Get(PlaceId, IRTypeSelect),
    // ret(args)
    Ret(Vec<IRNode>),
    Cond(Box<IRNode>, Box<IRNode>, Option<Box<IRNode>>),
    Branch(Box<IRNode>, BlockId, BlockId),
    // start block
    Label(BlockId, NodeIndex, Vec<IRArg>),
    Jump(BlockId, Vec<IRNode>),
    // function, a collection of blocks, the first of which is the entry, return type
    Func(Vec<IRBlock>, AstType),
    // call(variable, args), return type is inferred from variable
    Call(StringLabel, Vec<IRNode>),
    // op(operation, args)
    Op1(UnaryOperation, Box<IRNode>),
    Op2(BinaryOperation, Box<IRNode>, Box<IRNode>),
    Ternary(Box<IRNode>, Box<IRNode>, Box<IRNode>),
    Block(IRBlock),
    Module(IRBlock),
    Seq(Vec<IRNode>),
    Literal(Literal),
    Builtin(Builtin, Vec<IRNode>),
    Noop,
}

impl IRKind {
    pub fn terminator(&self) -> Option<IRTerminator> {
        match self {
            Self::Seq(exprs) => exprs.last().unwrap().kind.terminator(),
            Self::Block(nb) => nb.terminator(),
            Self::Jump(key, _args) => Some(IRTerminator::Jump(*key)),
            Self::Branch(_, then_key, else_key) => Some(IRTerminator::Branch(*then_key, *else_key)),
            Self::Ret(_) => Some(IRTerminator::Return),
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

    pub fn dump<E: Extra>(&self, places: &IRPlaceTable, b: &NodeBuilder<E>, mut depth: usize) {
        match &self.kind {
            IRKind::Func(blocks, _ret_ty) => {
                println!("{:width$}func:", "", width = depth * 2);
                depth += 1;
                for block in blocks {
                    println!(
                        "{:width$}block({})",
                        "",
                        b.resolve_block_label(block.label),
                        //block.label.0,
                        width = depth * 2
                    );
                    for a in &block.params {
                        println!(
                            "{:width$}arg: {}: {:?}",
                            "",
                            b.resolve_label(a.name),
                            a.ty,
                            width = (depth + 1) * 2
                        );
                    }
                    for a in &block.children {
                        a.dump(places, b, depth + 1);
                    }
                }
            }
            IRKind::Seq(exprs) => {
                //println!("{:width$}seq:", "", width = depth * 2);
                for e in exprs {
                    e.dump(places, b, depth);
                }
            }
            IRKind::Branch(cond, br_then, br_else) => {
                println!(
                    "{:width$}branch({}, {})",
                    "",
                    //br_then.0,
                    b.resolve_block_label(*br_then),
                    //br_else.0,
                    b.resolve_block_label(*br_else),
                    width = depth * 2
                );
                cond.dump(places, b, depth + 1);
            }
            IRKind::Decl(place_id) => {
                let p = places.get_place(*place_id);
                println!(
                    "{:width$}decl({}, {:?}, {:?})",
                    "",
                    b.resolve_label(p.name),
                    p.ty,
                    p.mem,
                    width = depth * 2
                );
            }
            IRKind::Set(place_id, v, select) => {
                let p = places.get_place(*place_id);
                println!(
                    "{:width$}set({}, {:?})",
                    "",
                    b.resolve_label(p.name),
                    select,
                    width = depth * 2
                );
                v.dump(places, b, depth + 1);
            }
            IRKind::Get(place_id, select) => {
                let p = places.get_place(*place_id);
                println!(
                    "{:width$}get({}, {:?})",
                    "",
                    b.resolve_label(p.name),
                    select,
                    width = depth * 2
                );
            }
            IRKind::Ret(vs) => {
                println!("{:width$}ret:", "", width = depth * 2);
                for e in vs {
                    e.dump(places, b, depth + 1);
                }
            }

            IRKind::Ternary(c, x, y) => {
                println!("{:width$}ternary:", "", width = depth * 2);
                c.dump(places, b, depth + 1);
                x.dump(places, b, depth + 1);
                y.dump(places, b, depth + 1);
            }

            IRKind::Cond(c, a, mb) => {
                println!("{:width$}cond:", "", width = depth * 2);
                c.dump(places, b, depth + 1);
                a.dump(places, b, depth + 1);
                if let Some(else_expr) = mb {
                    else_expr.dump(places, b, depth + 1);
                }
            }

            IRKind::Label(name, _block_index, args) => {
                println!(
                    "{:width$}label: {}",
                    "",
                    //name.0,
                    b.resolve_block_label(*name),
                    width = depth * 2
                );
                for e in args {
                    println!(
                        "{:width$}arg: {}, {:?}",
                        "",
                        b.resolve_label(e.name),
                        e.ty,
                        width = (depth + 1) * 2
                    );
                }
            }

            IRKind::Jump(key, args) => {
                println!(
                    "{:width$}jump({})",
                    "",
                    //key.0,
                    b.resolve_block_label(*key),
                    width = depth * 2
                );
                for a in args {
                    a.dump(places, b, depth + 1);
                }
            }

            IRKind::Call(key, args) => {
                println!(
                    "{:width$}call({})",
                    "",
                    b.resolve_label(*key),
                    width = depth * 2
                );
                if args.len() > 0 {
                    for a in args {
                        a.dump(places, b, depth + 1);
                    }
                }
            }

            IRKind::Op1(op, expr) => {
                println!("{:width$}unary: {:?}", "", op, width = depth * 2);
                expr.dump(places, b, depth + 1);
            }

            IRKind::Op2(op, x, y) => {
                println!("{:width$}binop: {:?}", "", op, width = depth * 2);
                x.dump(places, b, depth + 1);
                y.dump(places, b, depth + 1);
            }

            IRKind::Literal(lit) => {
                println!("{:width$}{:?}", "", lit, width = depth * 2);
            }

            IRKind::Builtin(bi, args) => {
                println!("{:width$}builtin({:?})", "", bi, width = depth * 2);
                for a in args {
                    a.dump(places, b, depth + 1);
                }
            }

            IRKind::Noop => {
                println!("{:width$}noop", "", width = depth * 2);
            }

            IRKind::Module(block) => {
                println!(
                    "{:width$}module({})",
                    "",
                    //block.label.0,
                    b.resolve_block_label(block.label),
                    width = depth * 2
                );
                for a in &block.params {
                    println!(
                        "{:width$}arg: {}: {:?}",
                        "",
                        b.resolve_label(a.name),
                        a.ty,
                        width = (depth + 1) * 2
                    );
                }
                for a in &block.children {
                    a.dump(places, b, depth + 1);
                }
            }

            IRKind::Block(block) => {
                println!(
                    "{:width$}block({})",
                    "",
                    //block.label.0,
                    b.resolve_block_label(block.label),
                    width = depth * 2
                );
                for a in &block.params {
                    println!(
                        "{:width$}arg: {}: {:?}",
                        "",
                        b.resolve_label(a.name),
                        a.ty,
                        width = (depth + 1) * 2
                    );
                }
                for a in &block.children {
                    a.dump(places, b, depth + 1);
                }
            } //_ => ()//unimplemented!()
        }
    }

    pub fn build_graph<'c, E: Extra>(
        self,
        places: &mut IRPlaceTable,
        env: &mut IREnvironment,
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) -> Result<IRNode> {
        let span = self.get_span().clone();
        match self.kind {
            IRKind::Module(mut block) => {
                //let block_index =
                //env.blocks
                //.add_block(places, block.label, block.params.clone(), d);
                //block.index = block_index;

                env.enter_block(block.index, span.clone());
                let mut out = vec![];

                // insert proper label
                let ir = b.ir_label(block.label, block.index, vec![]);
                out.push(ir.build_graph(places, env, d, b)?);
                //b.ir_label(block.label, block.index, vec![]));

                for c in block.children {
                    out.push(c.build_graph(places, env, d, b)?);
                }
                block.children = out;
                env.exit_block();

                Ok(IRNode::new(IRKind::Module(block), span))
            }

            IRKind::Block(mut block) => {
                //let span = self.get_span().clone();
                //let s = b.strings.resolve(&block.name);
                //let label = env.blocks.fresh_block_label(&s, b);
                //let block_index =
                //env.blocks
                //.add_block(places, block.label, block.params.clone(), d);
                //block.index = block_index;

                env.enter_block(block.index, span.clone());
                if let Some(last_block) = env.stack.last() {
                    if last_block.0 != block.index {
                        env.blocks.g.add_edge(last_block.0, block.index, ());
                    }
                }

                let mut children = vec![];
                for (_i, child) in block.children.into_iter().enumerate() {
                    children.push(child.build_graph(places, env, d, b)?);
                }
                env.exit_block();
                block.children = children;
                Ok(IRNode {
                    kind: IRKind::Block(block),
                    span,
                })
            }

            IRKind::Noop => Ok(self),

            //IRKind::Module(_) => Ok(self),
            IRKind::Seq(exprs) => {
                let mut out = vec![];
                for expr in exprs {
                    out.push(expr.build_graph(places, env, d, b)?);
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
                    out.push(expr.build_graph(places, env, d, b)?);
                }
                Ok(b.ir_ret(out))
            }

            IRKind::Label(ref _name, _block_index, ref _args) => {
                //let index = env.add_block(*name, args.clone(), d, g);
                //env.enter_block(index, self.span.clone());
                Ok(self)
            }

            IRKind::Jump(label, ref args) => {
                let block_index = env.current_block();
                let target_index = env.blocks.lookup_block_label(label).unwrap();
                env.blocks.connect_block(block_index, target_index);
                let target = env.blocks.g.node_weight(target_index).unwrap();

                // check arity of target
                if target.params.len() == args.len() {
                    Ok(self)
                } else {
                    d.push_diagnostic(error(
                        &format!(
                            "Jump to block, mismatch parameters: to {}",
                            //label.0,
                            b.resolve_block_label(label),
                        ),
                        self.span.clone(),
                    ));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            IRKind::Get(_place_id, ref _select) => {
                return Ok(self);

                /*
                let current_block = env.current_block();
                //self.dump(places, b, 0);
                //env.dump(b, current_block);
                let p = places.get_place(place_id);
                if let Some(_sym_index) = env.name_in_scope(current_block, p.name) {
                    Ok(self)
                } else {
                    d.push_diagnostic(error(
                        &format!("Get undefined variable: {:?}", b.resolve_label(p.name)),
                        self.span.clone(),
                    ));
                    Err(Error::new(ParseError::Invalid))
                }
                */
            }

            IRKind::Set(place_id, value, select) => {
                //Ok(self)

                let value = value.build_graph(places, env, d, b)?;
                Ok(b.ir_set(place_id, value, select))
                //
                //let current_index = env.current_block();
                //if let Some(_index) = env.name_in_scope(current_index, name) {
                //let current_index = env.current_block();
                //if let Some(_index) = env.name_in_scope(current_index, name) {
                //} else {
                //d.push_diagnostic(error(
                //&format!("Set undefined variable: {:?}", b.strings.resolve(&name)),
                //self.span.clone(),
                //));
                //Err(Error::new(ParseError::Invalid))
                //}
            }

            IRKind::Decl(_place_id) => {
                //let current_block = env.current_block();
                //let place_data = places.get_place(place_id);
                //let index = env.add_definition(current_block, place_id, place_data.name);
                //env.set_type(index, place_data.ty.clone(), place_data.mem);
                Ok(self)
            }

            IRKind::Call(_name, ref _args) => Ok(self),

            IRKind::Func(blocks, ret_type) => {
                let _current_block = env.current_block();
                let mut seq = vec![];
                for (i, block) in blocks.into_iter().enumerate() {
                    //let s = b.strings.resolve(&block.name);
                    //let label = env.blocks.fresh_block_label(&s, b);
                    // TODO: remove this, add_block
                    //println!("func: addblock");
                    //let block_index =
                    //env.blocks
                    //.add_block(places, block.label, block.params.clone(), d);
                    //block.index = block_index;
                    if 0 == i {
                        //env.blocks.g.add_edge(current_block, block.index, ());
                    }
                    seq.push(block);
                }

                let mut blocks = vec![];
                for mut block in seq {
                    env.enter_block(block.index, self.span.clone());
                    let mut children = vec![];
                    for child in block.children {
                        children.push(child.build_graph(places, env, d, b)?);
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

            IRKind::Literal(ref _lit) => Ok(self),

            IRKind::Builtin(ref _bi, ref _args) => Ok(self),

            IRKind::Branch(condition, then_key, else_key) => {
                let condition = condition.build_graph(places, env, d, b)?;
                let _current_block = env.current_block();
                let _then_block = env.blocks.lookup_block_label(then_key).unwrap();
                //env.blocks.g.add_edge(current_block, then_block, ());
                let _else_block = env.blocks.lookup_block_label(else_key).unwrap();
                //env.blocks.g.add_edge(current_block, else_block, ());
                Ok(b.ir_branch(condition, then_key, else_key))
            }

            IRKind::Ternary(_, _, _) => Ok(self),

            IRKind::Cond(_condition, _then_expr, _maybe_else_expr) => {
                unreachable!();
                /*
                let condition = condition.build_graph(places, env, d, b)?;
                let current_block = env.current_block();

                // TODO: remove the add blocks, they are declared earlier
                let label = env.blocks.fresh_block_label("next", b);
                let next_block = env.blocks.add_block(places, label, vec![], d);

                let label = env.blocks.fresh_block_label("then", b);
                let then_block = env.blocks.add_block(places, label, vec![], d);
                //let then_term = then_expr.kind.terminator();
                let then_expr = then_expr.build_graph(places, env, d, b)?;
                //env.blocks.g.add_edge(current_block, then_block, ());
                //env.blocks.g.add_edge(then_block, next_block, ());
                let maybe_else_expr = if let Some(else_expr) = maybe_else_expr {
                    let label = env.blocks.fresh_block_label("else", b);
                    let else_block = env.blocks.add_block(places, label, vec![], d);
                    env.enter_block(else_block, else_expr.span.clone());
                    let else_expr = else_expr.build_graph(places, env, d, b)?;
                    env.exit_block();
                    //env.blocks.g.add_edge(current_block, else_block, ());
                    //env.blocks.g.add_edge(else_block, next_block, ());
                    Some(else_expr)
                } else {
                    None
                };
                Ok(b.ir_cond(condition, then_expr, maybe_else_expr))
                */
            }

            IRKind::Op1(op, a) => {
                let a = a.build_graph(places, env, d, b)?;
                Ok(b.ir_op1(op, a))
            }

            IRKind::Op2(op_node, x, y) => {
                let x = x.build_graph(places, env, d, b)?;
                let y = y.build_graph(places, env, d, b)?;
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

    pub fn lower_ir_module<'c>(
        self,
        env: &mut IREnvironment,
        place: &mut IRPlaceTable,
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) -> Result<(IRNode, AstType, NodeIndex)> {
        match self.node {
            Ast::Module(name, body) => {
                assert_eq!(env.stack_size(), 0);
                println!("Module: addblock");
                let index = env.blocks.add_block(place, name.into(), vec![], d);
                env.enter_block(index, self.extra.get_span());
                //let mut children = vec![b.ir_label(nb.name, index, vec![])];
                let mut children = vec![];
                let mut ty = AstType::Unit;
                for c in body.to_vec() {
                    let (ir, _ty) = c.lower_ir_expr(env, place, d, b)?;
                    children.extend(ir.to_vec());
                    ty = _ty;
                }
                let ir = b.ir_module(name.into(), index, children);
                env.exit_block();
                Ok((ir, ty, index))
            }
            Ast::Sequence(ref _exprs) => {
                let module_name = b.s("module");
                let module = b.module(module_name.into(), self);
                module.lower_ir_module(env, place, d, b)
            }
            _ => {
                let module_name = b.s("module");
                let module = b.module(module_name.into(), b.seq(vec![self]));
                module.lower_ir_module(env, place, d, b)
            }
        }
    }

    pub fn lower_ir_function_body(
        self,
        name: StringKey,
        current_block: NodeIndex,
        env: &mut IREnvironment,
        place: &mut IRPlaceTable,
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) -> Result<Vec<IRBlock>> {
        let span = self.extra.get_span();
        let mut output_blocks = vec![];
        let mut edges = vec![];

        let blocks = self.try_seq().unwrap();

        //let mut scope = crate::sort::BlockScope::default();
        //let blocks = crate::sort::AstBlockSorter::run(blocks, env, place, &mut scope, d, b);

        for (i, block) in blocks.into_iter().enumerate() {
            if let Ast::Block(mut nb) = block.node {
                let mut args = vec![];
                for a in &nb.params {
                    args.push(IRArg {
                        name: StringLabel::Intern(a.name),
                        ty: a.ty.clone(),
                    });
                }

                //nb.body.
                //let s = b.strings.resolve(&nb.name);
                //let label = env.blocks.fresh_block_label(s, b);
                let is_label = nb.children.first().unwrap().node.is_label();

                println!("irfuncbody: addblock: {}", is_label);
                //if let Ast::Label(key, args) = nb.children.first().as_ref().unwrap().node. {
                //}
                if 0 == i {
                    nb.name = name.into();

                    // skip label on first
                    //let children = nb.children.into_iter().skip(1).collect();
                    //nb.children = children;
                }
                //
                let block_index = env.blocks.add_block(place, nb.name, args.clone(), d);
                edges.push((current_block, block_index));

                output_blocks.push((nb, block_index));
            } else {
                unreachable!()
            }
        }

        for (a, b) in edges {
            env.blocks.g.add_edge(a, b, ());
        }

        let mut blocks = vec![];
        //let mut s = IRBlockSorter::new();
        for (_i, (nb, block_index)) in output_blocks.into_iter().enumerate() {
            let mut args = vec![];
            for a in nb.params {
                args.push(IRArg {
                    name: StringLabel::Intern(a.name),
                    ty: a.ty,
                });
            }

            let mut exprs = vec![];
            env.enter_block(block_index, span.clone());
            for c in nb.children {
                let (ir, _ty) = c.lower_ir_expr(env, place, d, b)?;
                exprs.extend(ir.to_vec());
            }
            //let (ir, _ty) = nb.body.lower_ir_expr(env, place, d, b)?;
            env.exit_block();

            //exprs.extend(ir.to_vec());

            let block = IRBlock::new(block_index, nb.name, args, exprs);
            blocks.extend(IRBlockSorter::sort_block(
                block,
                place,
                &mut env.blocks,
                d,
                b,
            ));
            //blocks.push(block);
        }

        //for (_i, block) in blocks.into_iter().enumerate() {
        //}
        //s.close_block(place, &mut env.blocks, d, b);
        //let blocks = s.blocks;
        Ok(blocks)
    }

    pub fn lower_ir_expr<'c>(
        self,
        env: &mut IREnvironment,
        place: &mut IRPlaceTable,
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) -> Result<(IRNode, AstType)> {
        let mut out = vec![];
        let ty = self.lower_ir(&mut out, env, place, d, b)?;
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
        env: &mut IREnvironment,
        place: &mut IRPlaceTable,
        d: &mut Diagnostics,
        b: &mut NodeBuilder<E>,
    ) -> Result<AstType> {
        //if !self.node_id.is_valid() {
        //d.push_diagnostic(self.extra.error(&format!("Invalid NodeID: {:#?}", self)));
        //return Err(Error::new(ParseError::Invalid));
        //}

        match self.node {
            Ast::Noop => Ok(AstType::Unit),

            Ast::Module(_, _) => {
                unreachable!();
                /*
                let index = env.blocks.add_block(place, nb.name, vec![], d);
                env.enter_block(index, self.extra.get_span());
                //env.module_root = Some(index);
                let ty = AstType::Unit;
                for c in nb.children {
                    let (ir, _ty) = c.lower_ir_expr(env, place, d, b)?;
                    out.push(ir);
                    ty = _ty;
                }
                env.exit_block();
                Ok(ty)
                */
            }

            Ast::Sequence(exprs) => {
                let mut ty = AstType::Unit;
                for expr in exprs {
                    let (ir, ret_ty) = expr.lower_ir_expr(env, place, d, b)?;
                    out.extend(ir.to_vec());
                    ty = ret_ty;
                }
                Ok(ty)
            }

            Ast::Return(maybe_expr) => {
                let mut args = vec![];
                let mut ty = AstType::Unit;
                if let Some(expr) = maybe_expr {
                    ty = expr.lower_ir(&mut args, env, place, d, b)?;
                }
                out.push(b.ir_ret(args));
                Ok(ty)
            }

            Ast::Label(name, ast_args) => {
                //out.push(b.ir_noop());
                //return Ok(AstType::Unit);
                //unreachable!();
                //env.block_names

                let mut args = vec![];
                for a in &ast_args {
                    args.push(IRArg {
                        name: a.name.into(),
                        ty: a.ty.clone(),
                    });
                }

                println!("label: addblock");
                //let block_index = env.blocks.add_block(place, name, args.clone(), d);
                //let block_index = NodeIndex::new(0);
                //let s = b.strings.resolve(&name);
                //let label = env.blocks.fresh_block_label(s, b);
                //env.block_names.last_mut().unwrap().insert(name, label);
                let block_index = env.stack.last().unwrap().0;
                out.push(b.ir_label(name.into(), block_index, args));
                Ok(AstType::Unit)
            }

            Ast::Goto(name) => {
                let mut args = vec![];
                //for a in ast_args.into_iter() {
                //let Argument::Positional(expr) = a;
                //let (ir, _ty) = a.lower_ir_expr(env, place, d, b)?;
                //args.push(ir);
                //}
                //let label = env.block_names.last_mut().unwrap().get(&name).unwrap();

                out.push(b.ir_jump(name.into(), args));
                Ok(AstType::Unit)
            }

            Ast::Identifier(name) => {
                let current_block = env.current_block();
                if let Some(place_id) = env.block_name_in_scope(current_block, name.into()) {
                    let p = place.get_place(place_id);
                    out.push(b.ir_get(place_id, IRTypeSelect::default()));
                    Ok(p.ty.clone())
                } else {
                    d.push_diagnostic(self.extra.error(&format!(
                        "Variable name not found: {}",
                        b.resolve_label(name.into())
                    )));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            Ast::Global(ident, expr) => {
                if let Ast::Literal(ref _lit) = expr.node {
                    let (v, ty) = expr.lower_ir_expr(env, place, d, b)?;

                    let current_block = env.current_block();
                    let is_static = env.root() == current_block;

                    let mut place_data = PlaceNode::new_static(ident, ty.clone());
                    if !is_static {
                        // create a unique static name
                        let name = b.unique_static_name();
                        let name = format!("{}{}", b.r(ident), name).clone();
                        let key = b.s(&name);
                        place_data.static_name = Some(key);
                    }

                    let place_id = place.add_place(place_data);

                    out.push(b.ir_decl(place_id));
                    out.push(b.ir_set(place_id, v, IRTypeSelect::default()));
                    let _index = env.add_definition(current_block, place_id, ident.into());
                    Ok(ty)
                } else {
                    unimplemented!()
                }
            }

            Ast::Assign(target, expr) => match target {
                AssignTarget::Alloca(name) | AssignTarget::Identifier(name) => {
                    let (ir, ty) = expr.lower_ir_expr(env, place, d, b)?;
                    let current_block = env.current_block();
                    if let Some(place_id) = env.block_name_in_scope(current_block, name.into()) {
                        let _p = place.get_place(place_id);
                        out.push(b.ir_set(place_id, ir, IRTypeSelect::Offset(0)));
                        Ok(ty)
                    } else {
                        let place_data = PlaceNode::new_stack(name.into(), ty.clone());
                        let place_id = place.add_place(place_data);
                        out.push(b.ir_decl(place_id));
                        out.push(b.ir_set(place_id, ir, IRTypeSelect::Offset(0)));
                        let _index = env.add_definition(current_block, place_id, name.into());
                        Ok(ty)
                    }
                }
            },

            Ast::Mutate(lhs, rhs) => match lhs.node {
                Ast::Identifier(name) => {
                    let (ir, ty) = rhs.lower_ir_expr(env, place, d, b)?;
                    let current_block = env.current_block();
                    if let Some(place_id) = env.block_name_in_scope(current_block, name.into()) {
                        let _p = place.get_place(place_id);
                        out.push(b.ir_set(place_id, ir, IRTypeSelect::Offset(0)));
                        Ok(ty)
                    } else {
                        d.push_diagnostic(
                            self.extra.error(&format!(
                                "Name not found: {}",
                                b.resolve_label(name.into())
                            )),
                        );
                        return Err(Error::new(ParseError::Invalid));
                    }
                }
                _ => unimplemented!("{:?}", &lhs.node),
            },

            Ast::Call(expr, args, _ret_ty) => {
                // function to call
                let current_block = env.current_block();
                let (f, ty, f_args, name) = match &expr.node {
                    Ast::Identifier(ident) => {
                        let name = b.resolve_label(ident.into());
                        if let Some(place_id) = env.block_name_in_scope(current_block, ident.into())
                        {
                            let p = place.get_place(place_id);
                            if let AstType::Func(f_args, _) = p.ty.clone() {
                                (ident, p.ty.clone(), f_args, name)
                            } else {
                                d.push_diagnostic(
                                    self.extra
                                        .error(&format!("Type not function: {}, {:?}", name, p.ty)),
                                );
                                return Err(Error::new(ParseError::Invalid));
                            }
                        } else {
                            d.push_diagnostic(
                                self.extra.error(&format!("Call name not found: {}", name)),
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
                                expr.lower_ir(&mut ir_args, env, place, d, b)?;
                            }
                        }
                    }
                    out.push(b.ir_call(f.into(), ir_args));
                    Ok(*ret.clone())
                } else {
                    unimplemented!("calling non function type: {:?}", ty);
                }
            }

            Ast::Definition(def) => {
                let span = self.extra.get_span();
                //def = def.normalize(b);
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

                let place_data = PlaceNode::new_static(def.name, f_type.clone());
                let place_id = place.add_place(place_data);

                let _sym_index = env.add_definition(current_block, place_id, def.name.into());
                out.push(b.ir_decl(place_id));

                if let Some(body) = def.body {
                    let blocks = body.lower_ir_function_body(
                        def.name.into(),
                        current_block,
                        env,
                        place,
                        d,
                        b,
                    )?;

                    let ir = IRNode::new(IRKind::Func(blocks, ast_ret_type), span);
                    out.push(b.ir_set(place_id, ir, IRTypeSelect::default()));
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
                            expr.lower_ir(&mut ir_args, env, place, d, b)?;
                        }
                    }
                }
                out.push(IRNode::new(
                    IRKind::Builtin(bi, ir_args),
                    self.extra.get_span(),
                ));
                Ok(AstType::Unit)
            }

            Ast::Ternary(condition, then_expr, else_expr) => {
                let (c, _ty) = condition.lower_ir_expr(env, place, d, b)?;
                let (then_expr, _ty) = then_expr.lower_ir_expr(env, place, d, b)?;
                let (else_expr, ty) = else_expr.lower_ir_expr(env, place, d, b)?;
                out.push(b.ir_ternary(c, then_expr, else_expr));
                Ok(ty)
            }

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
                let current_block = env.current_block();
                let b_then = env.blocks.fresh_block_label("then", b);
                let b_next = env.blocks.fresh_block_label("next", b);
                let next_index = env.blocks.add_block(place, b_next, vec![], d);

                // then
                let then_index = env.blocks.add_block(place, b_then, vec![], d);
                //let span = then_expr.extra.get_span();
                env.blocks.g.add_edge(current_block, then_index, ());
                env.blocks.g.add_edge(then_index, next_index, ());
                let mut then_seq = vec![b.ir_label(b_then, then_index, vec![])];
                env.enter_block(then_index, self.extra.get_span());
                let (then_block, _ty) = then_expr.lower_ir_expr(env, place, d, b)?;
                env.exit_block();
                let term = then_block.kind.terminator();
                then_seq.extend(then_block.to_vec());
                if term.is_none() {
                    then_seq.push(b.ir_jump(b_next, vec![]));
                }
                //env.blocks.g.add_edge(then_index, next_index, ());

                // else
                let (b_else, else_seq) = if let Some(else_expr) = maybe_else_expr {
                    //let else_index = env.add_block(b_then, vec![], d, g);
                    //let span = else_expr.extra.get_span();
                    let b_else = env.blocks.fresh_block_label("else", b);
                    let else_index = env.blocks.add_block(place, b_else, vec![], d);
                    env.blocks.g.add_edge(current_block, else_index, ());
                    //env.blocks.g.add_edge(else_index, next_index, ());
                    //let else_index = NodeIndex::new(0);
                    let mut else_seq = vec![b.ir_label(b_else, else_index, vec![])];
                    env.enter_block(else_index, self.extra.get_span());
                    let (else_block, _ty) = else_expr.lower_ir_expr(env, place, d, b)?;
                    env.exit_block();
                    //g.add_edge(current_block, else_block, ());
                    let term = else_block.kind.terminator();
                    else_seq.extend(else_block.to_vec());
                    if term.is_none() {
                        else_seq.push(b.ir_jump(b_next, vec![]));
                        //env.blocks.g.add_edge(else_index, next_index, ());
                    }
                    (Some(b_else), Some(else_seq))
                } else {
                    (None, None)
                };

                let (ir_cond, _ty) = condition.lower_ir_expr(env, place, d, b)?;

                out.push(b.ir_branch(ir_cond, b_then, b_else.unwrap_or(b_next)));
                out.extend(then_seq);
                if let Some(seq) = else_seq {
                    out.extend(seq);
                }
                out.push(b.ir_label(b_next, next_index, vec![]));
                Ok(AstType::Unit)
            }

            Ast::UnaryOp(op, a) => {
                let (ir, ty) = a.lower_ir_expr(env, place, d, b)?;
                out.push(b.ir_op1(op, ir));
                Ok(ty)
            }

            Ast::BinaryOp(op_node, x, y) => {
                let (x, _ty) = x.lower_ir_expr(env, place, d, b)?;
                let (y, ty) = y.lower_ir_expr(env, place, d, b)?;
                out.push(b.ir_op2(op_node.node, x, y));
                Ok(ty)
            }

            // do nothing
            Ast::Deref(expr, _target) => expr.lower_ir(out, env, place, d, b),

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
        let mut place = IRPlaceTable::new();
        let ast = gen_block(&mut b).normalize(&mut d, &mut b);
        let r = ast.lower_ir_module(&mut env, &mut place, &mut d, &mut b);
        d.dump();
        assert!(!d.has_errors);
        let (ir, _ty, root) = r.unwrap();
        ir.dump(&place, &b, 0);
        assert_eq!(0, env.stack.len());
        env.blocks.g.node_weight(root).unwrap();
    }

    #[test]
    fn test_ir_2() {
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let mut b: NodeBuilder<SimpleExtra> = NodeBuilder::new();
        b.enter(file_id, "type.py");
        let mut env = IREnvironment::new();
        let mut place = IRPlaceTable::new();
        let ast = crate::tests::gen_function_call(&mut b).normalize(&mut d, &mut b);
        ast.dump(&mut b, 0);
        let ast = ast.first_pass(&mut b, &mut d).unwrap();
        ast.dump(&mut b, 0);

        let r = ast.lower_ir_module(&mut env, &mut place, &mut d, &mut b);

        d.dump();
        assert!(!d.has_errors);
        let (ir, _ty, root) = r.unwrap();
        ir.dump(&place, &b, 0);
        assert_eq!(0, env.stack.len());
        env.blocks.g.node_weight(root).unwrap();
    }
}
