use crate::ast::{
    Argument, AssignTarget, Ast, AstNode, AstType, Builtin, Extra, Literal, Parameter,
    ParameterNode,
};
use crate::lower::from_type;
use melior::ir::operation::OperationPrintingFlags;
//use crate::scope::LayerIndex;
use crate::default_pass_manager;
use crate::op;
use crate::{Diagnostics, ParseError};
use anyhow::Error;
use anyhow::Result;
use melior::ir::Location;
use melior::{
    dialect::{
        //arith,
        cf,
        func,
        //llvm,
        memref,
        //ods, scf,
    },
    ir::{
        attribute::{
            //DenseElementsAttribute,
            FlatSymbolRefAttribute,
            FloatAttribute,
            IntegerAttribute,
            StringAttribute,
            TypeAttribute,
        },
        r#type::{
            FunctionType,
            IntegerType,
            MemRefType,
            //RankedTensorType,
        },
        Attribute,
        Block,
        Identifier,
        Module,
        Operation,
        Region,
        //Type,
        TypeLike,
        Value,
        ValueLike,
    },
    Context, ExecutionEngine,
};
use petgraph::algo::dominators::simple_fast;
use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct BlockIndex(NodeIndex, usize);

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct SymIndex(NodeIndex, usize);

#[derive(Debug, Clone, Copy)]
pub enum NodeType {
    Module,
    Function,
    Block,
}

#[derive(Debug)]
pub struct OpCollection<'c> {
    block_index: NodeIndex,
    ops: Vec<Operation<'c>>,
    symbols: HashMap<String, usize>,
}

impl<'c> OpCollection<'c> {
    pub fn new(block_index: NodeIndex) -> Self {
        Self {
            block_index,
            ops: vec![],
            symbols: HashMap::new(),
        }
    }

    pub fn push(&mut self, op: Operation<'c>) -> SymIndex {
        let offset = self.ops.len();
        self.ops.push(op);
        SymIndex(self.block_index, offset)
    }

    pub fn push_with_name(&mut self, op: Operation<'c>, name: &str) -> SymIndex {
        let index = self.push(op);
        self.symbols.insert(name.to_string(), index.1);
        index
    }

    pub fn value0(&self, index: SymIndex) -> Option<Value<'c, '_>> {
        let rs = self.values(index);
        if rs.len() > 0 {
            Some(rs[0])
        } else {
            None
        }
    }

    pub fn values(&self, index: SymIndex) -> Vec<Value<'c, '_>> {
        assert_eq!(index.0, self.block_index);
        assert!(index.1 < self.ops.len());
        self.ops
            .get(index.1)
            .expect("Op missing")
            .results()
            .map(|x| x.into())
            .collect()
    }

    pub fn lookup(&self, name: &str) -> Option<SymIndex> {
        self.symbols
            .get(name)
            .map(|offset| SymIndex(self.block_index, *offset))
    }

    pub fn append_ops(&mut self, block_ref: &Block<'c>) {
        for op in self.take_ops() {
            block_ref.append_operation(op);
        }
    }

    pub fn take_ops(&mut self) -> Vec<Operation<'c>> {
        self.symbols.clear();
        self.ops.drain(..).collect()
    }

    pub fn add_symbol(&mut self, name: &str, index: SymIndex) {
        assert_eq!(index.0, self.block_index);
        self.symbols.insert(name.to_string(), index.1);
    }
}

#[derive(Debug)]
pub struct GData<'c, E> {
    ops: Vec<Operation<'c>>,
    //name: String,
    //node_type: NodeType,
    //params: Vec<ParameterNode<E>>,
    symbols: HashMap<String, SymIndex>,
    index: HashMap<SymIndex, usize>,
    _e: std::marker::PhantomData<E>,
}
impl<'c, E: Extra> GData<'c, E> {
    pub fn new() -> Self {
        //, params: Vec<ParameterNode<E>>) -> Self {
        Self {
            ops: vec![],
            //name: name.to_string(),
            //node_type,
            //params,
            symbols: HashMap::new(),
            index: HashMap::new(),
            _e: std::marker::PhantomData::default(),
        }
    }

    pub fn push(&mut self, op: Operation<'c>, sym_index: SymIndex) {
        let offset = self.ops.len();
        self.ops.push(op);
        self.index.insert(sym_index, offset);
    }

    pub fn push_with_name(&mut self, op: Operation<'c>, sym_index: SymIndex, name: &str) {
        self.push(op, sym_index);
        self.symbols.insert(name.to_string(), sym_index);
    }

    pub fn value0(&self, index: SymIndex) -> Option<Value<'c, '_>> {
        self.values(index).map(|vs| vs[0])
    }

    pub fn values(&self, index: SymIndex) -> Option<Vec<Value<'c, '_>>> {
        if let Some(offset) = self.index.get(&index) {
            Some(
                self.ops
                    .get(*offset)
                    .expect("Op missing")
                    .results()
                    .map(|x| x.into())
                    .collect(),
            )
        } else {
            None
        }
    }

    pub fn lookup(&self, name: &str) -> Option<SymIndex> {
        self.symbols.get(name).cloned()
    }

    pub fn add_symbol(&mut self, name: &str, index: SymIndex) {
        self.symbols.insert(name.to_string(), index);
    }

    pub fn append_ops(&mut self, block_ref: &Block<'c>) {
        for op in self.take_ops() {
            block_ref.append_operation(op);
        }
    }

    pub fn take_ops(&mut self) -> Vec<Operation<'c>> {
        //self.names.clear();
        self.ops.drain(..).collect()
    }

    /*
    pub fn push(&mut self, op: Operation<'c>, index: LayerIndex) -> LayerIndex {
        let pos = self.ops.len();
        self.ops.push(op);
        self.index.insert(index.clone(), pos);
        self._last_index = Some(index.clone());
        index
    }

    */
}

#[derive(Debug)]
pub struct SymbolData {
    ty: AstType,
}

impl SymbolData {
    pub fn new(ty: AstType) -> Self {
        Self { ty }
    }
}

#[derive(Default)]
pub struct CFG<'c, E> {
    shared: HashSet<String>,
    root: NodeIndex,
    index_count: usize,
    static_count: usize,
    g: DiGraph<GData<'c, E>, ()>,
    block_names: HashMap<String, NodeIndex>,
    block_names_index: HashMap<NodeIndex, String>,
    symbols: HashMap<SymIndex, SymbolData>,
    blocks: HashMap<NodeIndex, Block<'c>>,
}

impl<'c, E: Extra> CFG<'c, E> {
    pub fn new(module_name: &str) -> Self {
        let g = DiGraph::new();
        let block = Block::new(&[]);
        let data = GData::new();

        let mut cfg = Self {
            // dummy
            root: NodeIndex::new(0),
            index_count: 0,
            static_count: 0,
            g,
            block_names: HashMap::new(),
            block_names_index: HashMap::new(),
            symbols: HashMap::new(),
            blocks: HashMap::new(),
            shared: HashSet::new(),
        };
        cfg.add_block(module_name, data, block);

        cfg
    }

    pub fn module(&mut self, context: &Context, module: &mut Module<'c>) {
        let data = self.g.node_weight_mut(self.root).unwrap();
        for op in data.ops.drain(..) {
            module.body().append_operation(op);
        }
        log::debug!(
            "lowered {}",
            module
                .as_operation()
                .to_string_with_flags(OperationPrintingFlags::new())
                .unwrap()
        );

        println!("module: {:?}", module);
        let pass_manager = default_pass_manager(context);
        pass_manager.run(module).unwrap();
        assert!(module.as_operation().verify());

        log::debug!(
            "after pass {}",
            module
                .as_operation()
                .to_string_with_flags(OperationPrintingFlags::new())
                .unwrap()
        );
    }

    pub fn unique_static_name(&mut self) -> String {
        let s = format!("__static_x{}", self.static_count);
        self.static_count += 1;
        s
    }

    pub fn add_symbol(&mut self, index: SymIndex, data: SymbolData) {
        self.symbols.insert(index, data);
    }

    pub fn fresh_sym_index(&mut self, block_index: NodeIndex) -> SymIndex {
        let index = SymIndex(block_index, self.index_count);
        self.index_count += 1;
        index
    }

    pub fn add_block(&mut self, name: &str, data: GData<'c, E>, block: Block<'c>) -> NodeIndex {
        //let name = data.name.clone();
        let index = self.g.add_node(data);
        self.block_names.insert(name.to_string(), index);
        self.block_names_index.insert(index, name.to_string());
        self.blocks.insert(index, block);
        index
    }

    pub fn add_edge(&mut self, a: &str, b: &str) {
        println!("adding {}, {}", a, b);
        let index_a = self.block_names.get(a).unwrap();
        let index_b = self.block_names.get(b).unwrap();
        self.g.add_edge(*index_a, *index_b, ());
    }

    pub fn block_index(&self, name: &str) -> Option<NodeIndex> {
        self.block_names.get(name).cloned()
    }

    pub fn data_by_index(&self, index: NodeIndex) -> Option<&GData<E>> {
        self.g.node_weight(index)
    }

    pub fn data_mut_by_index(&mut self, index: NodeIndex) -> Option<&mut GData<'c, E>> {
        self.g.node_weight_mut(index)
    }

    pub fn data_mut_by_name(&mut self, name: &str) -> Option<&mut GData<'c, E>> {
        if let Some(index) = self.block_names.get(name) {
            self.data_mut_by_index(*index)
        } else {
            None
        }
    }

    pub fn save_graph(&self, filename: &str) {
        use petgraph::dot::{Config, Dot};
        #[derive(Debug)]
        enum Shape {
            Box,
            Ellipsis,
        }
        impl Shape {
            fn to_string(&self) -> &str {
                match self {
                    Self::Box => "box",
                    Self::Ellipsis => "circle",
                }
            }
        }
        #[derive(Debug)]
        struct Node {
            ty: Shape,
            name: String,
        }
        impl Node {
            fn new_block(name: String) -> Self {
                Self {
                    ty: Shape::Box,
                    name,
                }
            }
            fn new_symbol(name: String) -> Self {
                Self {
                    ty: Shape::Ellipsis,
                    name,
                }
            }
        }
        let mut g = DiGraph::new();
        for node_index in self.g.node_indices() {
            let data = self.g.node_weight(node_index).unwrap();
            let block_name = self.block_names_index.get(&node_index).unwrap();
            g.add_node(Node::new_block(block_name.clone()));
        }
        for node_index in self.g.node_indices() {
            let data = self.g.node_weight(node_index).unwrap();
            for name in data.symbols.keys() {
                let index = g.add_node(Node::new_symbol(name.clone()));
                g.add_edge(node_index, index, ());
            }
            for n in self
                .g
                .neighbors_directed(node_index, petgraph::Direction::Outgoing)
            {
                g.add_edge(node_index, n, ());
            }
        }

        let s = format!(
            "{:?}",
            Dot::with_attr_getters(
                &g,
                &[Config::EdgeNoLabel, Config::NodeNoLabel],
                &|_, _er| String::new(),
                &|_, (_index, data)| {
                    format!(
                        "label = \"{}\" shape={:?}",
                        &data.name,
                        &data.ty.to_string()
                    )
                }
            )
        );
        println!("{}", s);
        std::fs::write(filename, s).unwrap();
    }

    pub fn type_from_expr(&self, index: NodeIndex, expr: &AstNode<E>) -> AstType {
        match &expr.node {
            Ast::Literal(x) => x.into(),
            Ast::Identifier(name) => {
                // infer type from the operation
                let index = self.name_in_scope(index, name).unwrap();
                self.symbols.get(&index).unwrap().ty.clone()
            }
            Ast::Call(_f, _args, ty) => ty.clone(),

            _ => unreachable!("{:?}", expr),
        }
    }

    pub fn values_in_scope(
        &'c self,
        block_index: NodeIndex,
        sym_index: SymIndex,
    ) -> Option<Vec<Value<'c, '_>>> {
        let dom = simple_fast(&self.g, self.root)
            .dominators(block_index)
            .unwrap()
            .collect::<Vec<_>>();
        println!("dom: {:?} => {:?}", block_index, dom);
        for i in dom.into_iter().rev() {
            let data = self.data_by_index(i).unwrap();
            if let Some(r) = data.values(sym_index) {
                return Some(r);
            }
        }
        None
    }

    pub fn name_in_scope(&self, index: NodeIndex, name: &str) -> Option<SymIndex> {
        let dom = simple_fast(&self.g, self.root)
            .dominators(index)
            .unwrap()
            .collect::<Vec<_>>();
        println!("dom: {:?} => {:?}", index, dom);
        for i in dom.into_iter().rev() {
            let data = self.data_by_index(i).unwrap();
            if let Some(r) = data.lookup(name) {
                return Some(r);
            }
        }
        None
    }

    pub fn lower(&mut self, expr: AstNode<E>, stack: &mut Vec<NodeIndex>) {
        println!("lower: {:?}, {:?}", expr.node, stack);
        match expr.node {
            Ast::Sequence(exprs) => {
                for expr in exprs {
                    self.lower(expr, stack);
                }
            }
            Ast::Block(_name, _params, _body) => {
                unreachable!();
                /*
                let block_args = params
                    .iter()
                    .map(|a| (from_type(context, &a.ty), a.extra.location(context, d)))
                    .collect::<Vec<_>>();

                let block = Block::new(args);
                let current = stack.last().unwrap().clone();
                let data = GData::new(&name, NodeType::Block, params);
                let index = self.add_block(data);
                self.g.add_edge(current, index, ());
                let t = body.node.terminator().unwrap();
                self.lower(*body, stack);
                */
            }
            Ast::Builtin(_, _) => (),
            Ast::Literal(_) => (),
            Ast::Return(_) => {}
            Ast::Identifier(name) => {
                let current = stack.last().unwrap();
                let dom = simple_fast(&self.g, self.root)
                    .dominators(*current)
                    .unwrap()
                    .collect::<Vec<_>>();
                println!("X: {:?}", dom);
                let r = self.name_in_scope(*current, &name).unwrap();
                let symbol_data = self.symbols.get(&r).unwrap();
                println!("lookup identifier: {}, {:?}, {:?}", name, r, symbol_data.ty);
            }
            Ast::Goto(label) => {
                let current = stack.last().unwrap();
                let index = self.block_index(&label).unwrap();
                self.g.add_edge(*current, index, ());
            }
            Ast::Mutate(target, expr) => match target.node {
                Ast::Identifier(name) => {
                    let current = stack.last().unwrap();
                    let r = self.name_in_scope(*current, &name).unwrap();
                    let symbol_data = self.symbols.get(&r).unwrap();
                    println!("lookup identifier: {}, {:?}, {:?}", name, r, symbol_data.ty);
                    self.lower(*expr, stack);
                }
                _ => unimplemented!(),
            },
            Ast::Assign(target, expr) => {
                match target {
                    AssignTarget::Identifier(name) | AssignTarget::Alloca(name) => {
                        let block_index = stack.last().unwrap();
                        let index = self.fresh_sym_index(*block_index);
                        let ty = self.type_from_expr(*block_index, &expr);
                        let data = self.data_mut_by_index(*stack.last().unwrap()).unwrap();
                        let symbol_data = SymbolData::new(ty);
                        data.add_symbol(&name, index);
                        self.symbols.insert(index, symbol_data);
                    }
                }
                self.lower(*expr, stack);
            }
            Ast::Definition(mut def) => {
                def = def.normalize();
                let current = stack.last().unwrap().clone();

                if let Some(body) = def.body {
                    let mut edges = vec![];
                    let blocks = body.try_seq().unwrap();
                    let mut exprs = vec![];
                    for (i, b) in blocks.into_iter().enumerate() {
                        if let Ast::Block(name, params, expr) = b.node {
                            // connect the first block to the function
                            let block_name = if i == 0 { def.name.clone() } else { name };
                            let block = Block::new(&[]);
                            let data = GData::new(); //&block_name); //, params);
                            let index = self.add_block(&block_name, data, block);
                            if i == 0 {
                                edges.push((current, index));
                            }
                            exprs.push((index, *expr));
                        } else {
                            unreachable!()
                        }
                    }
                    for (a, b) in edges {
                        self.g.add_edge(a, b, ());
                    }

                    for (index, expr) in exprs {
                        stack.push(index);
                        self.dump_scope(index);
                        self.lower(expr, stack);
                        stack.pop();
                    }
                }
                stack.pop().unwrap();
            }
            Ast::Global(name, body) => {
                let block_index = self.block_index("module").unwrap();
                let index = self.fresh_sym_index(block_index);
                let ty = self.type_from_expr(block_index, &body);
                let data = self.data_mut_by_index(block_index).unwrap();
                let symbol_data = SymbolData::new(ty);
                data.add_symbol(&name, index);
                self.symbols.insert(index, symbol_data);
                self.lower(*body, stack);
            }
            _ => unreachable!("{:?}", expr.node),
        }
    }

    pub fn dump_scope(&self, index: NodeIndex) {
        let dom = simple_fast(&self.g, self.root)
            .dominators(index)
            .unwrap()
            .collect::<Vec<_>>();
        println!("dom: {:?} => {:?}", index, dom);
        for i in dom.into_iter().rev() {
            let data = self.data_by_index(i).unwrap();
            let block_name = self.block_names_index.get(&i).unwrap();
            println!("\t{:?}: {}, {:?}", i, block_name, data.symbols.keys());
        }
    }

    pub fn take_block(&mut self, index: NodeIndex) -> Block<'c> {
        let data = self.g.node_weight_mut(index).unwrap();
        let block = self.blocks.remove(&index).unwrap();
        for op in data.ops.drain(..) {
            block.append_operation(op);
        }
        block
    }
}

impl<E: Extra> AstNode<E> {
    pub fn location<'c>(&self, context: &'c Context, d: &Diagnostics) -> Location<'c> {
        self.extra.location(context, d)
    }

    pub fn lower<'c>(
        self,
        context: &'c Context,
        d: &mut Diagnostics,
        cfg: &mut CFG<'c, E>,
        stack: &mut Vec<NodeIndex>,
    ) -> Result<SymIndex> {
        let location = self.location(context, d);
        match self.node {
            /*
            Ast::Builtin(_, _) => {
                let current_block = stack.last().unwrap();
                let sym_index = cfg.fresh_sym_index(*current_block);
                Ok(sym_index)
            }
            */
            Ast::Sequence(exprs) => {
                let mut out = vec![];
                for expr in exprs {
                    out.push(expr.lower(context, d, cfg, stack)?);
                }
                Ok(out.last().cloned().unwrap())
            }
            Ast::Return(maybe_expr) => {
                let current_block = stack.last().unwrap().clone();
                let sym_index = cfg.fresh_sym_index(current_block);
                if let Some(expr) = maybe_expr {
                    let index = expr.lower(context, d, cfg, stack)?;
                    //let rs = &[];
                    let current = cfg.data_mut_by_index(current_block).unwrap();
                    let rs = current.values(index).unwrap();
                    current.push(func::r#return(&rs, location), sym_index);
                } else {
                    let current = cfg.data_mut_by_index(current_block).unwrap();
                    current.push(func::r#return(&[], location), sym_index);
                }
                Ok(sym_index)
            }

            Ast::Goto(label) => {
                let current_block = stack.last().unwrap();
                let sym_index = cfg.fresh_sym_index(*current_block);
                let op = if let Some(index) = cfg.block_index(&label) {
                    cfg.g.add_edge(*current_block, index, ());
                    let block = cfg.blocks.get(&index).unwrap();
                    cf::br(block, &[], location)
                } else {
                    d.push_diagnostic(self.extra.error(&format!("Missing block: {}", label)));
                    return Err(Error::new(ParseError::Invalid));
                };
                let current = cfg.data_mut_by_index(*current_block).unwrap();
                current.push(op, sym_index);
                Ok(sym_index)
            }

            Ast::Identifier(name) => {
                let current_block = stack.last().unwrap();
                if let Some(sym_index) = cfg.name_in_scope(*current_block, &name) {
                    println!("lookup identifier: {}, {:?}", name, sym_index);
                    return Ok(sym_index);
                }
                Err(Error::new(ParseError::Invalid))
            }

            Ast::Assign(target, expr) => {
                let current_block = stack.last().unwrap().clone();
                let sym_index = match target {
                    AssignTarget::Alloca(name) => {
                        let ty = IntegerType::new(context, 64);
                        let memref_ty = MemRefType::new(ty.into(), &[], None, None);
                        let op = memref::alloca(context, memref_ty, &[], &[], None, location);

                        let ptr_index = cfg.fresh_sym_index(current_block);
                        let op_index = cfg.fresh_sym_index(current_block);
                        let rhs_index = expr.lower(context, d, cfg, stack)?;
                        let current = cfg.g.node_weight_mut(current_block).unwrap();
                        current.push(op, ptr_index);
                        let r_value = current.value0(rhs_index).unwrap();
                        let r_addr = current.value0(ptr_index).unwrap();
                        let op = memref::store(r_value, r_addr, &[], location);
                        current.push(op, op_index);
                        current.add_symbol(&name, op_index);
                        op_index
                    }
                    AssignTarget::Identifier(name) => {
                        let current_block = stack.last().unwrap().clone();
                        let index = expr.lower(context, d, cfg, stack)?;
                        let current = cfg.data_mut_by_index(current_block).unwrap();
                        current.add_symbol(&name, index);
                        index
                    }
                };
                Ok(sym_index)
            }

            Ast::Definition(mut def) => {
                def = def.normalize();
                let current_block = stack.last().unwrap().clone();
                let sym_index = cfg.fresh_sym_index(current_block);

                let mut attributes = vec![(
                    Identifier::new(context, "sym_visibility"),
                    StringAttribute::new(context, "private").into(),
                )];

                let ret_ty = from_type(context, &*def.return_type);
                let mut ast_types = vec![];
                let mut types = vec![];
                //let ast_ret_type = def.return_type;

                for p in &def.params {
                    match p.node {
                        Parameter::Normal | Parameter::WithDefault(_) => {
                            //log::debug!("params {:?}: {:?}", p.name, p.ty);
                            types.push(from_type(context, &p.ty));
                            ast_types.push(p.ty.clone());
                        }
                        _ => unimplemented!("{:?}", p),
                    }
                }
                let ret_type = if ret_ty.is_none() {
                    vec![]
                } else {
                    vec![ret_ty]
                };
                let func_type = FunctionType::new(context, &types, &ret_type);

                let region = if let Some(body) = def.body {
                    let mut edges = vec![];
                    let blocks = body.try_seq().unwrap();
                    let mut exprs = vec![];
                    let mut block_indicies = vec![];
                    for (i, b) in blocks.into_iter().enumerate() {
                        if let Ast::Block(name, params, expr) = b.node {
                            // connect the first block to the function
                            let block_name = if i == 0 { def.name.clone() } else { name };
                            let block = Block::new(&[]);
                            let data = GData::new(); //&block_name); //, params);
                            let index = cfg.add_block(&block_name, data, block);
                            block_indicies.push(index);
                            if i == 0 {
                                edges.push((current_block, index));
                            }
                            exprs.push((index, *expr));
                        } else {
                            unreachable!()
                        }
                    }
                    for (a, b) in edges {
                        cfg.g.add_edge(a, b, ());
                    }

                    for (index, expr) in exprs {
                        stack.push(index);
                        cfg.dump_scope(index);
                        expr.lower(context, d, cfg, stack)?;
                        stack.pop();
                    }

                    let region = Region::new();
                    for index in block_indicies {
                        let block = cfg.take_block(index);
                        region.append_block(block);
                    }

                    // declare as C interface only if body is defined
                    // function declarations represent functions that are already C interfaces
                    attributes.push((
                        Identifier::new(context, "llvm.emit_c_interface"),
                        Attribute::unit(context),
                    ));

                    region
                } else {
                    Region::new()
                };

                let op = func::func(
                    context,
                    StringAttribute::new(context, &def.name),
                    TypeAttribute::new(func_type.into()),
                    region,
                    &attributes,
                    location,
                );
                let current = cfg.data_mut_by_index(current_block).unwrap();
                current.push(op, sym_index);
                Ok(sym_index)
            }

            Ast::Literal(lit) => {
                let current_block = stack.last().unwrap().clone();
                let sym_index = cfg.fresh_sym_index(current_block);
                let current = cfg.data_mut_by_index(current_block).unwrap();
                match lit {
                    Literal::Float(f) => {
                        let op = op::build_float_op(context, f, location);
                        current.push(op, sym_index);
                        Ok(sym_index)
                    }

                    Literal::Int(x) => {
                        let op = op::build_int_op(context, x, location);
                        current.push(op, sym_index);
                        Ok(sym_index)
                    }

                    Literal::Index(x) => {
                        let op = op::build_index_op(context, x as i64, location);
                        current.push(op, sym_index);
                        Ok(sym_index)
                    }

                    Literal::Bool(x) => {
                        let op = op::build_bool_op(context, x, location);
                        current.push(op, sym_index);
                        Ok(sym_index)
                    }
                    _ => unimplemented!("{:?}", lit),
                }
            }

            Ast::Builtin(bi, mut args) => {
                let arity = bi.arity();
                assert_eq!(arity, args.len());
                let current_block = stack.last().unwrap().clone();
                //let current = cfg.data_mut_by_index(current_block).unwrap();
                match bi {
                    Builtin::Assert => {
                        let arg = args.pop().unwrap();
                        match arg {
                            Argument::Positional(expr) => {
                                let index = expr.lower(context, d, cfg, stack)?;
                                //let index = self.lower_expr(*expr, env, d, b)?;
                                let msg = format!("assert at {}", location);
                                let sym_index = cfg.fresh_sym_index(current_block);
                                let current = cfg.g.node_weight_mut(current_block).unwrap();
                                let r = current.value0(index).unwrap();
                                let op = cf::assert(
                                    context, r, //env.value0(&index),
                                    &msg, location,
                                );
                                current.push(op, sym_index);
                                Ok(sym_index)
                            }
                        }
                    }
                    Builtin::Print => {
                        let arg = args.pop().unwrap();
                        match arg {
                            Argument::Positional(expr) => {
                                let sym_index = cfg.fresh_sym_index(current_block);
                                //let ast_ty = cfg.type_from_expr(current_block, &expr);

                                // eval expr
                                let index = expr.lower(context, d, cfg, stack)?; //(*expr, env, d, b)?;
                                let current = cfg.g.node_weight_mut(current_block).unwrap();
                                let rs = current.values(index).unwrap();
                                //let r = env.value0(&index);
                                let ty = rs[0].r#type();

                                // Select the baked version based on parameters
                                // TODO: A more dynamic way of doing this
                                // TODO: We only want to import these if they are referenced
                                let ident = if ty.is_index() || ty.is_integer() {
                                    "print_index"
                                } else if ty.is_f64() {
                                    "print_float"
                                } else {
                                    unimplemented!("{:?}", &ty)
                                };

                                let f = FlatSymbolRefAttribute::new(context, ident);
                                let op = func::call(
                                    context,
                                    f,
                                    &rs,
                                    //&env.values(&index),
                                    &[],
                                    location,
                                );

                                current.push(op, sym_index);
                                Ok(sym_index)
                            }
                        }
                    }
                    Builtin::Import => {
                        let arg = args.pop().unwrap();
                        if let Argument::Positional(expr) = arg {
                            if let Some(s) = expr.try_string() {
                                cfg.shared.insert(s);
                            } else {
                                d.push_diagnostic(expr.extra.error("Expected string"));
                            }
                        } else {
                            unimplemented!()
                        }
                        // do nothing?
                        let sym_index = cfg.fresh_sym_index(current_block);
                        Ok(sym_index)
                    } //_ => unimplemented!("{:?}", b),
                }
            }

            Ast::Global(ident, expr) => {
                let current_block = stack.last().unwrap().clone();
                let global_name = if cfg.root == current_block {
                    ident.clone()
                } else {
                    // we create a unique global name to prevent conflict
                    // and then we add ops to provide a local reference to the global name
                    let mut global_name = ident.clone();
                    global_name.push_str(&cfg.unique_static_name());
                    global_name
                };

                // evaluate expr at compile time
                let (ast_ty, op) = match expr.node {
                    Ast::Literal(Literal::Bool(x)) => {
                        let ast_ty = AstType::Bool;
                        let ty = from_type(context, &ast_ty);
                        let v = if x { 1 } else { 0 };
                        let value = IntegerAttribute::new(v, ty).into();
                        let op =
                            op::build_static(context, &global_name, ty, value, false, location);
                        (ast_ty, op)
                    }

                    Ast::Literal(Literal::Int(x)) => {
                        let ast_ty = AstType::Int;
                        let ty = from_type(context, &ast_ty);
                        let value = IntegerAttribute::new(x, ty).into();
                        let op =
                            op::build_static(context, &global_name, ty, value, false, location);
                        (ast_ty, op)
                    }

                    Ast::Literal(Literal::Index(x)) => {
                        let ast_ty = AstType::Int;
                        let ty = from_type(context, &ast_ty);
                        let value = IntegerAttribute::new(x as i64, ty).into();
                        let op =
                            op::build_static(context, &global_name, ty, value, false, location);
                        (ast_ty, op)
                    }

                    Ast::Literal(Literal::Float(x)) => {
                        let ast_ty = AstType::Float;
                        let ty = from_type(context, &ast_ty);
                        let value = FloatAttribute::new(context, x, ty).into();
                        let op =
                            op::build_static(context, &global_name, ty, value, false, location);
                        (ast_ty, op)
                    }

                    _ => unreachable!("{:?}", expr.node),
                };

                let ptr_ty = AstType::Ptr(ast_ty.clone().into());
                if cfg.root == current_block {
                    // STATIC/GLOBAL VARIABLE
                    let index = cfg.fresh_sym_index(current_block);
                    let current = cfg.g.node_weight_mut(current_block).unwrap();
                    current.push_with_name(op, index, &global_name);
                    Ok(index)
                    //let index = env.push_with_name(op, &global_name);
                    //env.index_data(&index, ptr_ty);
                    //env.index_static_name(&index, &global_name);
                    //Ok(index)
                } else {
                    // STATIC VARIABLE IN FUNCTION CONTEXT
                    let index = cfg.fresh_sym_index(current_block);
                    let current = cfg.g.node_weight_mut(current_block).unwrap();
                    current.push_with_name(op, index, &global_name);
                    Ok(index)

                    /*
                    // push static operation
                    let index = env.push_static(op, &global_name);
                    env.index_data(&index, ptr_ty);

                    env.index_static_name(&index, &global_name);
                    env.name_index(index.clone(), &ident);

                    // push name into current context
                    env.name_index(index.clone(), &ident);
                    Ok(index)
                    */
                }
            }

            /*
            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
                let bool_type = from_type(context, &AstType::Bool);

                let then_location = then_expr.location(context, d);

                // condition (outside of blocks)
                let index_conditions = condition.lower(context, d, cfg, current, stack)?;
                let r: Value<'_, '_> = env.last_values()[0];
                // should be bool type
                assert!(r.r#type() == bool_type);

                // then block

                let mut data = GData::new("then", NodeType::Block, vec![]);
                //let layer_type = LayerType::Block;
                //let layer = Layer::new(layer_type);
                let block = Block::new(&[]);
                env.enter(layer);
                let _index = then_expr.lower(context, d, cfg, &mut data, stack)?;
                env.push(scf::r#yield(&[], then_location));
                let mut layer = env.exit();
                data.append_ops(&block);
                let then_region = Region::new();
                then_region.append_block(block);

                // else block

                let else_region = match maybe_else_expr {
                    Some(else_expr) => {
                        let else_location = else_expr.location(context, d);

                        let mut data = GData::new("else", NodeType::Block, vec![]);
                        //let layer_type = LayerType::Block;
                        //let layer = Layer::new(layer_type);
                        let block = Block::new(&[]);
                        env.enter(layer);
                        let _index = else_expr.lower(context, d, cfg, &mut data, stack)?;
                        env.push(scf::r#yield(&[], else_location));
                        let mut layer = env.exit();
                        data.append_ops(&block);
                        let else_region = Region::new();
                        else_region.append_block(block);
                        else_region
                    }
                    None => Region::new(),
                };
                let if_op = scf::r#if(
                    env.value0(&index_conditions),
                    &[],
                    then_region,
                    else_region,
                    self.location(context, d),
                    );
                Ok(current.push(if_op))
            }
            */
            _ => {
                //unimplemented!("{:?}", self.node),
                d.push_diagnostic(self.extra.error(&format!("Unimplemented: {:?}", self.node)));
                Err(Error::new(ParseError::Invalid))
            }
        }
    }
}

pub fn exec_main<'c, E>(cfg: &CFG<'c, E>, module: &Module<'c>, libpath: &str) -> i32 {
    let paths = cfg
        .shared
        .iter()
        .map(|s| {
            let mut path = format!("{}/{}.so", libpath, s);
            path.push('\0');
            path
        })
        .collect::<Vec<_>>();
    let shared = paths.iter().map(|p| p.as_str()).collect::<Vec<_>>();

    let engine = ExecutionEngine::new(&module, 0, &shared, true);
    let mut result: i32 = -1;
    unsafe {
        engine
            .invoke_packed("main", &mut [&mut result as *mut i32 as *mut ()])
            .unwrap();
        println!("exec: {}", result);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{AstType, SimpleExtra};
    use crate::lower::tests::gen_block;
    use crate::{default_context, Diagnostics, NodeBuilder};
    use test_log::test;

    #[test]
    fn test_cfg_block_ast() {
        let context = default_context();
        let mut module = Module::new(Location::unknown(&context));
        let mut cfg: CFG<SimpleExtra> = CFG::new("module");
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let b = NodeBuilder::new(file_id, "type.py");
        let ast = gen_block(&b);
        let mut stack = vec![cfg.root];
        let r = ast.lower(&context, &mut d, &mut cfg, &mut stack);
        assert_eq!(1, stack.len());
        d.dump();
        assert!(!d.has_errors);
        r.unwrap();
        cfg.module(&context, &mut module);
        exec_main(&cfg, &module, "../target/debug/");
        cfg.save_graph("out.dot");
    }

    //#[test]
    fn test_cfg_while() {
        use crate::lower::tests::gen_while;
        let context = default_context();
        let mut module = Module::new(Location::unknown(&context));
        let mut cfg: CFG<SimpleExtra> = CFG::new("module");
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let b = NodeBuilder::new(file_id, "type.py");
        let ast = gen_while(&b);
        let mut stack = vec![cfg.root];
        let r = ast.lower(&context, &mut d, &mut cfg, &mut stack);
        d.dump();
        assert!(!d.has_errors);
        r.unwrap();
        cfg.module(&context, &mut module);
        exec_main(&cfg, &module, "../target/debug/");
        cfg.save_graph("out.dot");
        assert_eq!(1, stack.len());
    }

    #[test]
    fn test_cfg_block2() {
        let mut cfg: CFG<SimpleExtra> = CFG::new("module");
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let b = NodeBuilder::new(file_id, "type.py");
        let ast = gen_block(&b);
        let mut stack = vec![cfg.root];
        cfg.lower(ast, &mut stack);
        cfg.save_graph("out.dot");
        assert_eq!(0, stack.len());
    }

    #[test]
    fn test_cfg() {
        let mut cfg: CFG<SimpleExtra> = CFG::new("module");
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let b: NodeBuilder<SimpleExtra> = NodeBuilder::new(file_id, "type.py");

        (0..8).into_iter().for_each(|i| {
            let p = b.param(&format!("p{}", i), AstType::Int);
            let block = Block::new(&[]);
            let block_name = format!("b{}", i);
            let data = GData::new();
            cfg.add_block(&block_name, data, block);
            //data.add_symbol(&format!("scope{}", i), cfg.fresh_index());
        });

        cfg.add_edge("module", "b0");
        //cfg.g.add_edge(is[0], is[1], ());
        cfg.add_edge("b0", "b1");
        //cfg.g.add_edge(is[1], is[2], ());
        cfg.add_edge("b1", "b2");
        //cfg.g.add_edge(is[2], is[1], ());
        cfg.add_edge("b2", "b1");
        //cfg.g.add_edge(is[1], is[3], ());
        cfg.add_edge("b1", "b3");
        //cfg.g.add_edge(is[3], is[4], ());
        cfg.add_edge("b3", "b4");
        //cfg.g.add_edge(is[3], is[5], ());
        cfg.add_edge("b3", "b5");
        //cfg.g.add_edge(is[4], is[3], ());
        cfg.add_edge("b4", "b3");
        //cfg.g.add_edge(is[5], is[6], ());
        cfg.add_edge("b5", "b6");
        //cfg.g.add_edge(is[4], is[6], ());
        cfg.add_edge("b4", "b6");
        //cfg.g.add_edge(is[6], is[7], ());
        cfg.add_edge("b6", "b7");

        (0..8).into_iter().for_each(|i| {
            let name = format!("b{}", i);
            let index = cfg.block_index(&name).unwrap();
            let im = simple_fast(&cfg.g, cfg.root).immediate_dominator(index);
            let w = cfg.g.node_weight(index).unwrap();
            let block_name = cfg.block_names_index.get(&index).unwrap();
            println!("node {} has immediate dominator {:?}", block_name, im);
        });
        (0..8).into_iter().for_each(|i| {
            let name = format!("b{}", i);
            let index = cfg.block_index(&name).unwrap();
            let im = simple_fast(&cfg.g, cfg.root)
                .immediately_dominated_by(index)
                .collect::<Vec<_>>();
            let w = cfg.g.node_weight(index).unwrap();
            let block_name = cfg.block_names_index.get(&index).unwrap();
            println!("node {} is the immediate dominator of {:?}", block_name, im);
        });
        (0..8).into_iter().for_each(|i| {
            let name = format!("b{}", i);
            let index = cfg.block_index(&name).unwrap();
            let im = simple_fast(&cfg.g, cfg.root)
                .strict_dominators(index)
                .unwrap()
                .collect::<Vec<_>>();
            let w = cfg.g.node_weight(index).unwrap();
            let block_name = cfg.block_names_index.get(&index).unwrap();
            println!("node {} has strict dominators {:?}", block_name, im);
        });
        (0..8).into_iter().for_each(|i| {
            let name = format!("b{}", i);
            let index = cfg.block_index(&name).unwrap();
            let im = simple_fast(&cfg.g, cfg.root)
                .dominators(index)
                .unwrap()
                .collect::<Vec<_>>();
            let w = cfg.g.node_weight(index).unwrap();
            let block_name = cfg.block_names_index.get(&index).unwrap();
            println!("node {} has dominators {:?}", block_name, im);
        });
        cfg.save_graph("out.dot");
    }
}
