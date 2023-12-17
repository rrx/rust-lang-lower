use crate::ast::{
    Argument, AssignTarget, Ast, AstNode, AstType, Builtin, Extra, Literal, Parameter,
    ParameterNode,
};
use crate::compile::exec_main;
use crate::default_pass_manager;
use crate::lower::from_type;
use crate::op;
use crate::{Diagnostics, ParseError};
use anyhow::Error;
use anyhow::Result;
use melior::ir::operation::OperationPrintingFlags;
use melior::ir::Location;
use melior::{
    dialect::{
        arith,
        cf,
        func,
        //llvm,
        memref,
        //ods,
        scf,
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
    Context,
};
use petgraph::algo::dominators::simple_fast;
use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct BlockIndex(NodeIndex, usize);

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum SymIndex {
    Op(NodeIndex, usize),
    Arg(NodeIndex, usize),
}

impl SymIndex {
    pub fn block(&self) -> NodeIndex {
        match self {
            SymIndex::Op(block_index, _offset) | SymIndex::Arg(block_index, _offset) => {
                *block_index
            }
        }
    }

    pub fn offset(&self) -> usize {
        match self {
            SymIndex::Op(_block_index, offset) | SymIndex::Arg(_block_index, offset) => *offset,
        }
    }

    pub fn is_op(&self) -> bool {
        if let SymIndex::Op(_, _) = self {
            true
        } else {
            false
        }
    }

    pub fn is_arg(&self) -> bool {
        if let SymIndex::Arg(_, _) = self {
            true
        } else {
            false
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum NodeType {
    Module,
    Function,
    Block,
}

#[derive(Debug)]
pub struct OpCollection<'c> {
    arg_count: usize,
    block: Option<Block<'c>>,
    parent_symbol: Option<SymIndex>,
    block_index: NodeIndex,
    ops: Vec<Operation<'c>>,
    symbols: HashMap<String, SymIndex>,
}

impl<'c> OpCollection<'c> {
    pub fn new(block: Block<'c>) -> Self {
        Self {
            arg_count: 0,
            parent_symbol: None,
            block: Some(block),
            block_index: NodeIndex::new(0),
            ops: vec![],
            symbols: HashMap::new(),
        }
    }

    pub fn set_parent_symbol(&mut self, parent_symbol: SymIndex) {
        self.parent_symbol = Some(parent_symbol);
    }

    pub fn push(&mut self, op: Operation<'c>) -> SymIndex {
        let offset = self.ops.len();
        self.ops.push(op);
        SymIndex::Op(self.block_index, offset)
    }

    pub fn push_with_name(&mut self, op: Operation<'c>, name: &str) -> SymIndex {
        let index = self.push(op);
        self.symbols.insert(name.to_string(), index);
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
        match index {
            SymIndex::Op(block_index, offset) => {
                assert_eq!(block_index, self.block_index);
                assert!(offset < self.ops.len());
                self.ops
                    .get(offset)
                    .expect("Op missing")
                    .results()
                    .map(|x| x.into())
                    .collect()
            }
            SymIndex::Arg(block_index, offset) => {
                assert_eq!(block_index, self.block_index);
                vec![self
                    .block
                    .as_ref()
                    .unwrap()
                    .argument(offset)
                    .unwrap()
                    .into()]
            }
        }
    }

    pub fn lookup(&self, name: &str) -> Option<SymIndex> {
        self.symbols.get(name).cloned()
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
        assert_eq!(index.block(), self.block_index);
        self.symbols.insert(name.to_string(), index);
    }

    pub fn add_arg(&mut self, name: &str) {
        assert!(self.arg_count < self.block.as_ref().unwrap().argument_count());
        let index = SymIndex::Arg(self.block_index, self.arg_count);
        self.symbols.insert(name.to_string(), index);
        self.arg_count += 1;
    }

    pub fn last(&self) -> SymIndex {
        assert!(self.ops.len() > 0);
        SymIndex::Op(self.block_index, self.ops.len() - 1)
    }
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

pub type CFGGraph<'c> = DiGraph<OpCollection<'c>, ()>;

pub fn values_in_scope<'c, 'a>(g: &'a CFGGraph<'c>, sym_index: SymIndex) -> Vec<Value<'c, 'a>> {
    let data = g.node_weight(sym_index.block()).unwrap();
    data.values(sym_index)
}

pub struct CFG<'c, E> {
    context: &'c Context,
    shared: HashSet<String>,
    root: NodeIndex,
    index_count: usize,
    static_count: usize,
    block_names: HashMap<String, NodeIndex>,
    block_names_index: HashMap<NodeIndex, String>,
    symbols: HashMap<SymIndex, SymbolData>,
    types: HashMap<SymIndex, AstType>,
    static_names: HashMap<SymIndex, String>,
    _e: std::marker::PhantomData<E>,
}

impl<'c, E: Extra> CFG<'c, E> {
    pub fn new(
        context: &'c Context,
        module_name: &str,
        d: &Diagnostics,
        g: &mut CFGGraph<'c>,
    ) -> Self {
        let mut cfg = Self {
            // dummy
            context,
            root: NodeIndex::new(0),
            index_count: 0,
            static_count: 0,
            block_names: HashMap::new(),
            block_names_index: HashMap::new(),
            symbols: HashMap::new(),
            types: HashMap::new(),
            static_names: HashMap::new(),
            shared: HashSet::new(),
            _e: std::marker::PhantomData::default(),
        };
        cfg.add_block(context, module_name, &[], d, g);
        cfg
    }

    pub fn lookup_type(&self, index: SymIndex) -> Option<AstType> {
        self.types.get(&index).cloned()
    }

    pub fn set_type(&mut self, index: SymIndex, ty: AstType) {
        self.types.insert(index, ty);
    }

    pub fn root(&self) -> NodeIndex {
        self.root
    }

    pub fn exec_main(&self, module: &Module<'c>, libpath: &str) -> i32 {
        let shared = self.shared.iter().cloned().collect::<Vec<_>>();
        exec_main(&shared, module, libpath)
    }

    pub fn block_is_static(&self, block_index: NodeIndex) -> bool {
        // root block is static block, and there's only one for now
        self.root == block_index
    }

    pub fn module(&mut self, context: &Context, module: &mut Module<'c>, g: &mut CFGGraph<'c>) {
        let data = g.node_weight_mut(self.root).unwrap();
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

    pub fn add_block(
        &mut self,
        context: &'c Context,
        name: &str,
        params: &[ParameterNode<E>],
        d: &Diagnostics,
        g: &mut CFGGraph<'c>,
    ) -> NodeIndex {
        // build parameter list for block
        let mut block_params = vec![];
        for p in params {
            match p.node {
                Parameter::Normal | Parameter::WithDefault(_) => {
                    block_params.push((from_type(context, &p.ty), p.extra.location(context, d)));
                }
                _ => unimplemented!("{:?}", p),
            }
        }

        let block = Block::new(&block_params);
        let data = OpCollection::new(block);
        let index = g.add_node(data);
        g.node_weight_mut(index).unwrap().block_index = index;
        self.block_names.insert(name.to_string(), index);
        self.block_names_index.insert(index, name.to_string());
        index
    }

    pub fn add_edge(&mut self, a: &str, b: &str, g: &mut CFGGraph<'c>) {
        println!("adding {}, {}", a, b);
        let index_a = self.block_names.get(a).unwrap();
        let index_b = self.block_names.get(b).unwrap();
        g.add_edge(*index_a, *index_b, ());
    }

    pub fn block_index(&self, name: &str) -> Option<NodeIndex> {
        self.block_names.get(name).cloned()
    }

    pub fn data_mut_by_name(
        &mut self,
        name: &str,
        g: &'c mut CFGGraph<'c>,
    ) -> Option<&mut OpCollection<'c>> {
        if let Some(index) = self.block_names.get(name) {
            g.node_weight_mut(*index)
        } else {
            None
        }
    }

    pub fn save_graph(&self, filename: &str, g: &CFGGraph<'c>) {
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
            block_index: NodeIndex,
        }
        impl Node {
            fn new_block(name: String, block_index: NodeIndex) -> Self {
                Self {
                    ty: Shape::Box,
                    name,
                    block_index,
                }
            }
            fn new_symbol(name: String, block_index: NodeIndex) -> Self {
                Self {
                    ty: Shape::Ellipsis,
                    name,
                    block_index,
                }
            }
        }
        let mut g_out = DiGraph::new();
        for node_index in g.node_indices() {
            let block_name = self.block_names_index.get(&node_index).unwrap();
            g_out.add_node(Node::new_block(block_name.clone(), node_index));
        }
        for block_node_index in g.node_indices() {
            let data = g.node_weight(block_node_index).unwrap();

            let mut x = HashMap::new();
            for (name, symbol_index) in data.symbols.iter() {
                let symbol_node_index =
                    g_out.add_node(Node::new_symbol(name.clone(), block_node_index));
                g_out.add_edge(block_node_index, symbol_node_index, ());
                x.insert(symbol_index, symbol_node_index);
            }

            for n in g.neighbors_directed(block_node_index, petgraph::Direction::Outgoing) {
                if let Some(parent) = g.node_weight(n).unwrap().parent_symbol {
                    let symbol_node_index = x.get(&parent).unwrap();
                    g_out.add_edge(*symbol_node_index, n, ());
                } else {
                    g_out.add_edge(block_node_index, n, ());
                }
            }
        }

        let s = format!(
            "{:?}",
            Dot::with_attr_getters(
                &g_out,
                &[Config::EdgeNoLabel, Config::NodeNoLabel],
                &|_, _er| String::new(),
                &|_, (_index, data)| {
                    format!(
                        "label = \"[{}]{}\" shape={:?}",
                        data.block_index.index(),
                        &data.name,
                        &data.ty.to_string()
                    )
                }
            )
        );
        let path = std::fs::canonicalize(filename).unwrap();
        println!("{}", path.clone().into_os_string().into_string().unwrap());
        println!("{}", s);
        std::fs::write(path, s).unwrap();
    }

    pub fn type_from_expr(&self, index: NodeIndex, expr: &AstNode<E>, g: &CFGGraph<'c>) -> AstType {
        match &expr.node {
            Ast::Literal(x) => x.into(),
            Ast::Identifier(name) => {
                // infer type from the operation
                let index = self.name_in_scope(index, name, g).unwrap();
                self.symbols.get(&index).unwrap().ty.clone()
            }
            Ast::Call(_f, _args, ty) => ty.clone(),

            _ => unreachable!("{:?}", expr),
        }
    }

    /*
    pub fn values_in_scope<'a>(
        &self,
        current_block_index: NodeIndex,
        sym_index: SymIndex,
        g: &'a CFGGraph<'c>,
    ) -> Option<Vec<Value<'c, 'a>>> {
        let data = g.node_weight(sym_index.block()).unwrap();
        //let dom = simple_fast(g, self.root)
        //.dominators(block_index)
        //.unwrap()
        //.collect::<Vec<_>>();
        //println!("dom: {:?} => {:?}", block_index, dom);
        //for i in dom.into_iter().rev() {
        //let data = g.node_weight(i).unwrap();
        Some(data.values(sym_index))
        //return Some(data.values(sym_index));
        //}
        //None
    }
    */

    pub fn name_in_scope(
        &self,
        index: NodeIndex,
        name: &str,
        g: &CFGGraph<'c>,
    ) -> Option<SymIndex> {
        self.save_graph("out.dot", g);
        let dom = simple_fast(g, self.root)
            .dominators(index)
            .expect("Node not connected to root")
            .collect::<Vec<_>>();
        println!("dom: {:?} => {:?}", index, dom);
        for i in dom.into_iter().rev() {
            let data = g.node_weight(i).unwrap();
            if let Some(r) = data.lookup(name) {
                return Some(r);
            }
        }
        None
    }

    pub fn dump_scope(&self, index: NodeIndex, g: &CFGGraph<'c>) {
        let dom = simple_fast(g, self.root)
            .dominators(index)
            .unwrap()
            .collect::<Vec<_>>();
        println!("dom: {:?} => {:?}", index, dom);
        for i in dom.into_iter().rev() {
            let data = g.node_weight(i).unwrap();
            let block_name = self.block_names_index.get(&i).unwrap();
            println!("\t{:?}: {}, {:?}", i, block_name, data.symbols.keys());
        }
    }

    pub fn take_block(&mut self, index: NodeIndex, g: &mut CFGGraph<'c>) -> Block<'c> {
        let data = g.node_weight_mut(index).unwrap();
        let block = data.block.take().unwrap();
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
        g: &mut CFGGraph<'c>,
    ) -> Result<SymIndex> {
        let location = self.location(context, d);
        match self.node {
            Ast::Sequence(exprs) => {
                let mut out = vec![];
                for expr in exprs {
                    out.push(expr.lower(context, d, cfg, stack, g)?);
                }
                Ok(out.last().cloned().unwrap())
            }
            Ast::Return(maybe_expr) => {
                let current_block = stack.last().unwrap().clone();
                if let Some(expr) = maybe_expr {
                    let index = expr.lower(context, d, cfg, stack, g)?;
                    let current = g.node_weight_mut(current_block).unwrap();
                    let rs = current.values(index);
                    Ok(current.push(func::r#return(&rs, location)))
                } else {
                    let current = g.node_weight_mut(current_block).unwrap();
                    Ok(current.push(func::r#return(&[], location)))
                }
            }

            Ast::Goto(label) => {
                let current_block = stack.last().unwrap().clone();
                if let Some(index) = cfg.block_index(&label) {
                    g.add_edge(current_block, index, ());
                    let target_block = g.node_weight_mut(index).unwrap();
                    let block = target_block.block.as_ref().unwrap();
                    let op = cf::br(block, &[], location);
                    let current = g.node_weight_mut(current_block).unwrap();
                    Ok(current.push(op))
                } else {
                    d.push_diagnostic(self.extra.error(&format!("Missing block: {}", label)));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            Ast::Identifier(name) => {
                let current_block = stack.last().unwrap().clone();
                match name.as_str() {
                    "True" => {
                        let op = op::build_bool_op(context, true, location);
                        let current = g.node_weight_mut(current_block).unwrap();
                        let index = current.push(op);
                        cfg.set_type(index, AstType::Bool);
                        //env.index_data(&index, Data::new(AstType::Bool).ty);
                        Ok(index)
                    }
                    "False" => {
                        let op = op::build_bool_op(context, false, location);
                        let current = g.node_weight_mut(current_block).unwrap();
                        let index = current.push(op);
                        cfg.set_type(index, AstType::Bool);
                        //env.index_data(&index, Data::new(AstType::Bool).ty);
                        Ok(index)
                    }
                    _ => {
                        if let Some(sym_index) = cfg.name_in_scope(current_block, &name, g) {
                            println!("lookup identifier: {}, {:?}", name, sym_index);
                            if cfg.block_is_static(sym_index.block()) {
                                let ast_ty = cfg.lookup_type(sym_index).unwrap();
                                if let AstType::Ptr(ty) = &ast_ty {
                                    let lower_ty = from_type(context, ty);
                                    let memref_ty = MemRefType::new(lower_ty, &[], None, None);
                                    let static_name =
                                        cfg.static_names.get(&sym_index).unwrap().clone();
                                    let op = memref::get_global(
                                        context,
                                        &static_name,
                                        memref_ty,
                                        location,
                                    );
                                    let current = g.node_weight_mut(current_block).unwrap();
                                    let index = current.push(op);
                                    cfg.set_type(index, ast_ty);
                                    return Ok(index);
                                } else {
                                    unreachable!("Identifier of static variable must be pointer");
                                }
                            } else {
                                return Ok(sym_index);
                            }
                        }
                        d.push_diagnostic(self.extra.error(&format!("Name not found: {:?}", name)));
                        Err(Error::new(ParseError::Invalid))
                    }
                }
            }

            Ast::Mutate(lhs, rhs) => match lhs.node {
                Ast::Identifier(ident) => emit_mutate(context, &ident, *rhs, d, cfg, stack, g),
                _ => unimplemented!("{:?}", &lhs.node),
            },

            Ast::Assign(target, expr) => {
                let current_block = stack.last().unwrap().clone();
                let sym_index = match target {
                    AssignTarget::Alloca(name) => {
                        let ty = IntegerType::new(context, 64);
                        let memref_ty = MemRefType::new(ty.into(), &[], None, None);
                        let op = memref::alloca(context, memref_ty, &[], &[], None, location);
                        let rhs_index = expr.lower(context, d, cfg, stack, g)?;
                        let current = g.node_weight_mut(current_block).unwrap();
                        let ptr_index = current.push(op);
                        let r_value = current.value0(rhs_index).unwrap();
                        let r_addr = current.value0(ptr_index).unwrap();

                        let op = memref::store(r_value, r_addr, &[], location);
                        let index = current.push_with_name(op, &name);
                        index
                    }
                    AssignTarget::Identifier(name) => {
                        let current_block = stack.last().unwrap().clone();
                        let index = expr.lower(context, d, cfg, stack, g)?;
                        let current = g.node_weight_mut(current_block).unwrap();
                        current.add_symbol(&name, index);
                        index
                    }
                };
                Ok(sym_index)
            }

            Ast::Call(expr, args, _ret_ty) => {
                // function to call
                let current_block = stack.last().unwrap().clone();
                let (f, ty) = match &expr.node {
                    Ast::Identifier(ident) => {
                        if let Some(index) = cfg.name_in_scope(current_block, ident, g) {
                            let ty = cfg.lookup_type(index).unwrap();
                            (FlatSymbolRefAttribute::new(context, ident), ty)
                        } else {
                            d.push_diagnostic(
                                self.extra.error(&format!("Name not found: {}", ident)),
                            );
                            return Err(Error::new(ParseError::Invalid));
                        }
                    }
                    _ => {
                        unimplemented!("{:?}", expr.node);
                    }
                };

                if let AstType::Func(_func_arg_types, ret) = &ty {
                    let ret_ty = from_type(context, &ret);
                    // handle call arguments
                    let mut indices = vec![];

                    // lower call args
                    for a in args {
                        match a {
                            Argument::Positional(arg) => {
                                let index = arg.lower(context, d, cfg, stack, g)?; //(*arg, env, d, b)?;
                                indices.push(index);
                            } //_ => unimplemented!("{:?}", a)
                        };
                    }

                    let call_args = indices
                        .into_iter()
                        .map(|index| values_in_scope(g, index)[0])
                        .collect::<Vec<_>>();

                    let op = func::call(
                        context,
                        f,
                        call_args.as_slice(),
                        &[ret_ty.clone()],
                        location,
                    );
                    let current = g.node_weight_mut(current_block).unwrap();
                    Ok(current.push(op))
                } else {
                    unimplemented!("calling non function type: {:?}", ty);
                }
            }

            Ast::Definition(mut def) => {
                def = def.normalize();
                let current_block = stack.last().unwrap().clone();

                assert!(cfg.block_is_static(current_block));

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
                let ast_ret_type = def.return_type;
                let f_type = AstType::Func(ast_types, ast_ret_type);

                let mut entry_block = None;

                let region = if let Some(body) = def.body {
                    let mut edges = vec![];
                    let blocks = body.try_seq().unwrap();
                    let mut exprs = vec![];
                    let mut block_indicies = vec![];

                    // build parameter list for block
                    let mut entry_params = vec![];
                    for p in &def.params {
                        match p.node {
                            Parameter::Normal | Parameter::WithDefault(_) => {
                                entry_params.push((
                                    from_type(context, &p.ty),
                                    p.extra.location(context, d),
                                ));
                            }
                            _ => unimplemented!("{:?}", p),
                        }
                    }

                    for (i, b) in blocks.into_iter().enumerate() {
                        if let Ast::Block(nb) = b.node {
                            // connect the first block to the function
                            let block_name = if i == 0 { def.name.clone() } else { nb.name };

                            let block_index =
                                cfg.add_block(context, &block_name, &def.params, d, g);
                            let data = g.node_weight_mut(block_index).unwrap();

                            if i == 0 {
                                entry_block = Some(block_index);
                            }
                            for p in nb.params {
                                data.add_arg(&p.name);
                            }

                            block_indicies.push(block_index);
                            if i == 0 {
                                edges.push((current_block, block_index));
                            }
                            exprs.push((block_index, *nb.body));
                        } else {
                            unreachable!()
                        }
                    }
                    for (a, b) in edges {
                        g.add_edge(a, b, ());
                    }

                    for (index, expr) in exprs {
                        stack.push(index);
                        cfg.dump_scope(index, g);
                        if let Ok(_index) = expr.lower(context, d, cfg, stack, g) {
                            stack.pop();
                        } else {
                            stack.pop();
                            return Err(Error::new(ParseError::Invalid));
                        }
                    }

                    let region = Region::new();
                    for index in block_indicies {
                        let block = cfg.take_block(index, g);
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
                let current = g.node_weight_mut(current_block).unwrap();
                let index = current.push_with_name(op, &def.name);
                cfg.set_type(index, f_type);

                if let Some(entry_block) = entry_block {
                    let data = g.node_weight_mut(entry_block).unwrap();
                    data.set_parent_symbol(index);
                }

                Ok(index)
            }

            Ast::Literal(lit) => {
                let current_block = stack.last().unwrap().clone();
                let current = g.node_weight_mut(current_block).unwrap();
                let op = match lit {
                    Literal::Float(f) => op::build_float_op(context, f, location),

                    Literal::Int(x) => op::build_int_op(context, x, location),

                    Literal::Index(x) => op::build_index_op(context, x as i64, location),

                    Literal::Bool(x) => op::build_bool_op(context, x, location),
                    _ => unimplemented!("{:?}", lit),
                };
                Ok(current.push(op))
            }

            Ast::Builtin(bi, mut args) => {
                let arity = bi.arity();
                assert_eq!(arity, args.len());
                let current_block = stack.last().unwrap().clone();
                match bi {
                    Builtin::Assert => {
                        let arg = args.pop().unwrap();
                        match arg {
                            Argument::Positional(expr) => {
                                let index = expr.lower(context, d, cfg, stack, g)?;
                                let msg = format!("assert at {}", location);
                                let current = g.node_weight_mut(current_block).unwrap();
                                let r = current.value0(index).unwrap();
                                let op = cf::assert(context, r, &msg, location);
                                Ok(current.push(op))
                            }
                        }
                    }
                    Builtin::Print => {
                        let arg = args.pop().unwrap();
                        match arg {
                            Argument::Positional(expr) => {
                                // eval expr
                                let index = expr.lower(context, d, cfg, stack, g)?;
                                let current = g.node_weight_mut(current_block).unwrap();
                                let r = current.value0(index).unwrap();
                                let ty = r.r#type();

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
                                let op = func::call(context, f, &[r], &[], location);

                                Ok(current.push(op))
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
                        // do nothing
                        let op = op::build_bool_op(context, true, location);
                        let current = g.node_weight_mut(current_block).unwrap();
                        Ok(current.push(op))
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
                    let current = g.node_weight_mut(current_block).unwrap();
                    let index = current.push_with_name(op, &global_name);
                    cfg.set_type(index, ptr_ty);
                    cfg.static_names.insert(index, global_name);
                    Ok(index)
                    //let index = env.push_with_name(op, &global_name);
                    //env.index_data(&index, ptr_ty);
                    //env.index_static_name(&index, &global_name);
                    //Ok(index)
                } else {
                    // STATIC VARIABLE IN FUNCTION CONTEXT
                    //let index = cfg.fresh_sym_index(current_block);
                    let current = g.node_weight_mut(current_block).unwrap();
                    let index = current.push_with_name(op, &global_name);
                    cfg.set_type(index, ptr_ty);
                    cfg.static_names.insert(index, global_name);
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

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
                let current_block = stack.last().unwrap().clone();
                let bool_type = from_type(context, &AstType::Bool);
                let then_location = then_expr.location(context, d);

                // condition (outside of blocks)
                let index_conditions = condition.lower(context, d, cfg, stack, g)?;
                let current = g.node_weight_mut(current_block).unwrap();
                let rs = current.values(current.last());
                // should be bool type
                assert!(rs[0].r#type() == bool_type);

                // then block

                //let block = Block::new(&[]);
                //let data = OpCollection::new(block);

                let then_block_index = cfg.add_block(context, "then", &[], d, g);
                g.add_edge(current_block, then_block_index, ());

                // else
                let (maybe_else_block_index, maybe_else_expr) = match maybe_else_expr {
                    Some(else_expr) => {
                        //let block = Block::new(&[]);
                        //let data = OpCollection::new(block);
                        let block_index = cfg.add_block(context, "else", &[], d, g);
                        g.add_edge(current_block, block_index, ());

                        (Some(block_index), Some(else_expr))
                    }
                    None => (None, None),
                };

                stack.push(then_block_index);
                if let Ok(_index) = then_expr.lower(context, d, cfg, stack, g) {
                    let data = g.node_weight_mut(then_block_index).unwrap();
                    data.push(scf::r#yield(&[], then_location));
                    stack.pop();
                } else {
                    stack.pop();
                    return Err(Error::new(ParseError::Invalid));
                }

                if let Some(else_block_index) = &maybe_else_block_index {
                    let else_expr = maybe_else_expr.unwrap();
                    let else_location = else_expr.location(context, d);
                    stack.push(*else_block_index);
                    println!("else: {:?}", else_expr.node);
                    if let Ok(_index) = else_expr.lower(context, d, cfg, stack, g) {
                        let data = g.node_weight_mut(*else_block_index).unwrap();
                        data.push(scf::r#yield(&[], else_location));
                        stack.pop();
                    } else {
                        stack.pop();
                        return Err(Error::new(ParseError::Invalid));
                    }
                }

                let block = cfg.take_block(then_block_index, g);
                let then_region = Region::new();
                then_region.append_block(block);

                let else_region = if let Some(else_block_index) = maybe_else_block_index {
                    let block = cfg.take_block(else_block_index, g);
                    let region = Region::new();
                    region.append_block(block);
                    region
                } else {
                    Region::new()
                };

                let current = g.node_weight_mut(current_block).unwrap();
                let if_op = scf::r#if(
                    current.value0(index_conditions).unwrap(),
                    &[],
                    then_region,
                    else_region,
                    location,
                );
                Ok(current.push(if_op))
            }

            Ast::Deref(expr, _target) => {
                // we are expecting a memref here
                let index = expr.lower(context, d, cfg, stack, g)?;
                let current_block = stack.last().unwrap().clone();

                println!("current {:?}", current_block);
                println!("index {:?}", index);
                let ty = cfg.lookup_type(index).unwrap();
                println!("ty {:?}", ty);

                // ensure proper type
                if let AstType::Ptr(ast_ty) = &ty {
                    let r = values_in_scope(g, index)[0];
                    //let r = current.value0(index).unwrap();
                    let op = memref::load(r, &[], location);
                    let current = g.node_weight_mut(current_block).unwrap();
                    let index = current.push(op);
                    cfg.set_type(index, *ast_ty.clone());
                    Ok(index)
                } else {
                    unreachable!("Trying to dereference a non-pointer")
                }
            }

            Ast::UnaryOp(op, a) => {
                use crate::ast::UnaryOperation;
                let index = a.lower(context, d, cfg, stack, g)?;
                let current_block = stack.last().unwrap().clone();
                let current = g.node_weight_mut(current_block).unwrap();
                let ty = {
                    println!("{:?}", current);
                    // get the type of the RHS
                    let ty = current.value0(index).unwrap().r#type();
                    ty
                };

                match op {
                    UnaryOperation::Minus => {
                        if ty.is_index() {
                            unreachable!("Unable to negate index type");
                        } else if ty.is_integer() {
                            // Multiply by -1
                            let int_op = op::build_int_op(context, -1, location);
                            //let current = g.node_weight_mut(current_block).unwrap();
                            let index_lhs = current.push(int_op);
                            let r = current.value0(index_lhs).unwrap();
                            let r_rhs = current.value0(index).unwrap();
                            Ok(current.push(arith::muli(r, r_rhs, location)))
                        } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                            // arith has an op for negation
                            //let current = g.node_weight_mut(current_block).unwrap();
                            let r_rhs = current.value0(index).unwrap();
                            Ok(current.push(arith::negf(r_rhs, location)))
                        } else {
                            unimplemented!()
                        }
                    }
                }
            }

            Ast::BinaryOp(op, x, y) => {
                let index_x = x.lower(context, d, cfg, stack, g)?;
                let index_y = y.lower(context, d, cfg, stack, g)?;

                let current_block = stack.last().unwrap().clone();
                {
                    let current = g.node_weight_mut(current_block).unwrap();
                    println!("{:?}", current);
                }

                // types must be the same for binary operation, no implicit casting yet
                let a = values_in_scope(g, index_x)[0];
                let b = values_in_scope(g, index_y)[0];
                let op = op::build_binop(context, op, a, b, location);
                let current = g.node_weight_mut(current_block).unwrap();
                let index = current.push(op);
                Ok(index)
            }

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

pub fn emit_mutate<'c, E: Extra>(
    context: &'c Context,
    ident: &str,
    rhs: AstNode<E>,
    d: &mut Diagnostics,
    cfg: &mut CFG<'c, E>,
    stack: &mut Vec<NodeIndex>,
    g: &mut CFGGraph<'c>,
) -> Result<SymIndex> {
    let location = rhs.location(context, d);
    let current_block = stack.last().unwrap().clone();

    let index = cfg.name_in_scope(current_block, ident, g).unwrap();
    let name_is_static = cfg.block_is_static(index.block());
    let value_index = rhs.lower(context, d, cfg, stack, g)?;
    let current = g.node_weight_mut(current_block).expect("Name not found");

    if name_is_static {
        let ty = MemRefType::new(IntegerType::new(context, 64).into(), &[], None, None);
        let op1 = memref::get_global(context, &ident, ty, location);
        let addr_index = current.push(op1);
        let r_addr = current.value0(addr_index).unwrap();
        let r_value = current.value0(value_index).unwrap();
        let op = memref::store(r_value, r_addr, &[], location);
        Ok(current.push(op))
    } else {
        let r_addr = current.value0(index).unwrap();
        let r_value = current.value0(value_index).unwrap();
        let op = memref::store(r_value, r_addr, &[], location);
        Ok(current.push(op))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::SimpleExtra;
    use crate::lower::tests::gen_block;
    use crate::{default_context, Diagnostics, NodeBuilder};
    use test_log::test;

    #[test]
    fn test_cfg_block_ast() {
        let context = default_context();
        let mut module = Module::new(Location::unknown(&context));
        let mut g = CFGGraph::new();
        let mut d = Diagnostics::new();
        let mut cfg: CFG<SimpleExtra> = CFG::new(&context, "module", &d, &mut g);

        let file_id = d.add_source("test.py".into(), "test".into());
        let b = NodeBuilder::new(file_id, "type.py");
        let ast = gen_block(&b);
        let mut stack = vec![cfg.root];
        let r = ast.lower(&context, &mut d, &mut cfg, &mut stack, &mut g);
        assert_eq!(1, stack.len());
        d.dump();
        assert!(!d.has_errors);
        r.unwrap();
        cfg.module(&context, &mut module, &mut g);
        let shared = cfg.shared.iter().cloned().collect::<Vec<_>>();
        exec_main(&shared, &module, "../target/debug/");
        cfg.save_graph("out.dot", &g);
    }

    //#[test]
    fn test_cfg_while() {
        use crate::lower::tests::gen_while;
        let context = default_context();
        let mut module = Module::new(Location::unknown(&context));
        let mut g = CFGGraph::new();
        let mut d = Diagnostics::new();
        let mut cfg: CFG<SimpleExtra> = CFG::new(&context, "module", &d, &mut g);

        let file_id = d.add_source("test.py".into(), "test".into());
        let b = NodeBuilder::new(file_id, "type.py");

        let ast = gen_while(&b);
        let mut stack = vec![cfg.root];
        let r = ast.lower(&context, &mut d, &mut cfg, &mut stack, &mut g);
        d.dump();
        assert!(!d.has_errors);
        r.unwrap();
        cfg.module(&context, &mut module, &mut g);
        let shared = cfg.shared.iter().cloned().collect::<Vec<_>>();
        exec_main(&shared, &module, "../target/debug/");
        cfg.save_graph("out.dot", &g);
        assert_eq!(1, stack.len());
    }

    #[test]
    fn test_cfg_graph() {
        let context = default_context();
        let d = Diagnostics::new();
        let mut g = CFGGraph::new();
        let mut cfg: CFG<SimpleExtra> = CFG::new(&context, "module", &d, &mut g);
        //let mut d = Diagnostics::new();
        //let file_id = d.add_source("test.py".into(), "test".into());
        //let b: NodeBuilder<SimpleExtra> = NodeBuilder::new(file_id, "type.py");

        (0..8).into_iter().for_each(|i| {
            //let p = b.param(&format!("p{}", i), AstType::Int);
            let block_name = format!("b{}", i);
            cfg.add_block(&context, &block_name, &[], &d, &mut g);
        });

        cfg.add_edge("module", "b0", &mut g);
        cfg.add_edge("b0", "b1", &mut g);
        cfg.add_edge("b2", "b1", &mut g);
        cfg.add_edge("b1", "b2", &mut g);
        cfg.add_edge("b1", "b3", &mut g);
        cfg.add_edge("b3", "b4", &mut g);
        cfg.add_edge("b3", "b5", &mut g);
        cfg.add_edge("b4", "b3", &mut g);
        cfg.add_edge("b5", "b6", &mut g);
        cfg.add_edge("b4", "b6", &mut g);
        cfg.add_edge("b6", "b7", &mut g);

        (0..8).into_iter().for_each(|i| {
            let name = format!("b{}", i);
            let index = cfg.block_index(&name).unwrap();
            let im = simple_fast(&g, cfg.root).immediate_dominator(index);
            let block_name = cfg.block_names_index.get(&index).unwrap();
            println!("node {} has immediate dominator {:?}", block_name, im);
        });

        (0..8).into_iter().for_each(|i| {
            let name = format!("b{}", i);
            let index = cfg.block_index(&name).unwrap();
            let im = simple_fast(&g, cfg.root)
                .immediately_dominated_by(index)
                .collect::<Vec<_>>();
            let block_name = cfg.block_names_index.get(&index).unwrap();
            println!("node {} is the immediate dominator of {:?}", block_name, im);
        });

        cfg.save_graph("out.dot", &g);
        (0..8).into_iter().for_each(|i| {
            let name = format!("b{}", i);
            let index = cfg.block_index(&name).unwrap();
            let im = simple_fast(&g, cfg.root)
                .strict_dominators(index)
                .unwrap()
                .collect::<Vec<_>>();
            let block_name = cfg.block_names_index.get(&index).unwrap();
            println!("node {} has strict dominators {:?}", block_name, im);
        });

        (0..8).into_iter().for_each(|i| {
            let name = format!("b{}", i);
            let index = cfg.block_index(&name).unwrap();
            let im = simple_fast(&g, cfg.root)
                .dominators(index)
                .unwrap()
                .collect::<Vec<_>>();
            let block_name = cfg.block_names_index.get(&index).unwrap();
            println!("node {} has dominators {:?}", block_name, im);
        });

        cfg.save_graph("out.dot", &g);
    }
}
