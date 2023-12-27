use crate::ast::{
    //Argument,
    //AssignTarget,
    //Ast,
    //AstNode,
    //Builtin,
    //DerefTarget,
    //Literal,
    Parameter,
    ParameterNode,
    VarDefinitionSpace,
};
//use crate::compile::exec_main;
//use crate::default_pass_manager;
use crate::intern::StringKey;
use crate::ir::IRArg;
use crate::op;
use crate::types::TypeBuilder;
use crate::{AstType, Diagnostics, Extra, NodeBuilder};
//use anyhow::Error;
//use anyhow::Result;
//use melior::ir::operation::OperationPrintingFlags;
use melior::ir::Location;
use melior::{
    //dialect::memref,
    ir::{
        //attribute::{
        //DenseElementsAttribute,
        //FlatSymbolRefAttribute,
        //FloatAttribute,
        //IntegerAttribute,
        //StringAttribute,
        //TypeAttribute,
        //},
        //r#type::{
        //FunctionType,
        //IntegerType,
        //MemRefType,
        //RankedTensorType,
        //},
        //Attribute,
        Block,
        //Identifier,
        //Module,
        Operation,
        //OperationRef,
        //Region,
        //Type,
        //TypeLike,
        Value,
        //ValueLike,
    },
    Context,
};
use petgraph::algo::dominators::simple_fast;
use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use std::collections::HashMap;
//use std::collections::HashSet;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct BlockIndex(NodeIndex, usize);

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum SymIndex {
    Op(NodeIndex, usize),
    Arg(NodeIndex, usize),
    Def(NodeIndex, usize),
}

impl SymIndex {
    pub fn block(&self) -> NodeIndex {
        match self {
            SymIndex::Op(block_index, _)
            | SymIndex::Arg(block_index, _)
            | SymIndex::Def(block_index, _) => *block_index,
        }
    }

    pub fn offset(&self) -> usize {
        match self {
            SymIndex::Op(_, offset) | SymIndex::Arg(_, offset) | SymIndex::Def(_, offset) => {
                *offset
            }
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
    op_count: usize,
    arg_count: usize,
    pub(crate) block: Option<Block<'c>>,
    parent_symbol: Option<SymIndex>,
    block_index: NodeIndex,
    ops: Vec<Operation<'c>>,
    symbols: HashMap<StringKey, SymIndex>,
}

impl<'c> OpCollection<'c> {
    pub fn new(block: Block<'c>) -> Self {
        Self {
            op_count: 0,
            arg_count: 0,
            parent_symbol: None,
            block: Some(block),
            block_index: NodeIndex::new(0),
            ops: vec![],
            symbols: HashMap::new(),
        }
    }

    pub fn get_next_index(&mut self) -> SymIndex {
        let offset = self.op_count;
        self.op_count += 1;
        SymIndex::Op(self.block_index, offset)
    }

    pub fn save_op(&mut self, index: SymIndex, op: Operation<'c>) {
        assert_eq!(index.block(), self.block_index);
        assert_eq!(index.offset(), self.ops.len());
        self.ops.push(op);
        assert!(self.ops.len() <= self.op_count);
    }

    pub fn set_parent_symbol(&mut self, parent_symbol: SymIndex) {
        self.parent_symbol = Some(parent_symbol);
    }

    pub fn push(&mut self, op: Operation<'c>) -> SymIndex {
        let offset = self.op_count;
        self.ops.push(op);
        self.op_count += 1;
        SymIndex::Op(self.block_index, offset)
    }

    pub fn push_with_name(&mut self, op: Operation<'c>, name: StringKey) -> SymIndex {
        let index = self.push(op);
        self.symbols.insert(name, index);
        index
    }

    pub fn value0<'a>(&'a self, index: SymIndex) -> Option<Value<'c, 'a>> {
        let rs = self.values(index);
        if rs.len() > 0 {
            Some(rs[0])
        } else {
            None
        }
    }

    pub fn op_ref(&mut self, index: SymIndex) -> &mut Operation<'c> {
        match index {
            SymIndex::Op(block_index, offset) => {
                assert_eq!(block_index, self.block_index);
                assert!(offset < self.ops.len());
                self.ops.get_mut(offset).expect("Op missing")
            }
            SymIndex::Arg(_, _) => {
                unreachable!()
            }
            _ => unimplemented!(),
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
            _ => unimplemented!(),
        }
    }

    pub fn lookup(&self, name: StringKey) -> Option<SymIndex> {
        self.symbols.get(&name).cloned()
    }

    pub fn append_ops(&mut self, block_ref: &Block<'c>) {
        for op in self.take_ops() {
            block_ref.append_operation(op);
        }
    }

    pub fn take_ops(&mut self) -> Vec<Operation<'c>> {
        assert_eq!(self.op_count, self.ops.len());
        self.symbols.clear();
        self.ops.drain(..).collect()
    }

    pub fn add_symbol(&mut self, name: StringKey, index: SymIndex) {
        assert_eq!(index.block(), self.block_index);
        self.symbols.insert(name, index);
    }

    pub fn push_arg(&mut self, name: StringKey) -> SymIndex {
        assert!(self.arg_count < self.block.as_ref().unwrap().argument_count());
        let index = SymIndex::Arg(self.block_index, self.arg_count);
        self.symbols.insert(name, index);
        self.arg_count += 1;
        index
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
    root: NodeIndex,
    index_count: usize,
    block_names: HashMap<StringKey, NodeIndex>,
    block_names_index: HashMap<NodeIndex, StringKey>,
    //types: HashMap<SymIndex, (AstType, VarDefinitionSpace)>,
    pub(crate) types: TypeBuilder,
    pub(crate) static_names: HashMap<SymIndex, StringKey>,
    _e: std::marker::PhantomData<E>,
}

impl<'c, E: Extra> CFG<'c, E> {
    pub fn new(
        context: &'c Context,
        module_name: StringKey,
        d: &Diagnostics,
        g: &mut CFGGraph<'c>,
    ) -> Self {
        let mut cfg = Self {
            // dummy
            context,
            root: NodeIndex::new(0),
            index_count: 0,
            block_names: HashMap::new(),
            block_names_index: HashMap::new(),
            types: TypeBuilder::new(),
            //types: HashMap::new(),
            static_names: HashMap::new(),
            //shared: HashSet::new(),
            _e: std::marker::PhantomData::default(),
        };
        cfg.add_block(context, module_name, &[], d, g);
        cfg
    }

    /*
    pub fn lookup_type(&self, index: SymIndex) -> Option<(AstType, VarDefinitionSpace)> {
        self.types.get(&index).cloned()
    }

    pub fn set_type(&mut self, index: SymIndex, ty: AstType, mem: VarDefinitionSpace) {
        self.types.insert(index, (ty, mem));
    }
    */

    pub fn root(&self) -> NodeIndex {
        self.root
    }

    /*
    pub fn exec_main(&self, module: &Module<'c>, libpath: &str) -> i32 {
        let shared = self.shared.iter().cloned().collect::<Vec<_>>();
        exec_main(&shared, module, libpath)
    }
    */

    pub fn block_is_static(&self, block_index: NodeIndex) -> bool {
        // root block is static block, and there's only one for now
        self.root == block_index
    }

    pub fn add_block_ir(
        &mut self,
        context: &'c Context,
        name: StringKey,
        params: &[IRArg],
        _d: &Diagnostics,
        g: &mut CFGGraph<'c>,
    ) -> NodeIndex {
        // build parameter list for block
        let mut block_params = vec![];
        for p in params {
            block_params.push((op::from_type(context, &p.ty), Location::unknown(context)));
            //p..extra.location(context, d)));
        }
        let block = Block::new(&block_params);
        let data = OpCollection::new(block);
        let index = g.add_node(data);
        let block_node = g.node_weight_mut(index).unwrap();
        block_node.block_index = index;
        for p in params {
            let index = block_node.push_arg(p.name);
            self.types
                .set_type(index, p.ty.clone(), VarDefinitionSpace::Arg);
        }
        self.block_names.insert(name, index);
        self.block_names_index.insert(index, name);
        index
    }

    pub fn add_block(
        &mut self,
        context: &'c Context,
        name: StringKey,
        params: &[ParameterNode<E>],
        d: &Diagnostics,
        g: &mut CFGGraph<'c>,
    ) -> NodeIndex {
        // build parameter list for block
        let mut block_params = vec![];
        for p in params {
            match p.node {
                Parameter::Normal => {
                    //| Parameter::WithDefault(_) => {
                    block_params
                        .push((op::from_type(context, &p.ty), p.extra.location(context, d)));
                }
                _ => unimplemented!("{:?}", p),
            }
        }

        let block = Block::new(&block_params);
        let data = OpCollection::new(block);
        let index = g.add_node(data);
        g.node_weight_mut(index).unwrap().block_index = index;
        self.block_names.insert(name, index);
        self.block_names_index.insert(index, name);
        index
    }

    pub fn add_edge(&mut self, a: StringKey, b: StringKey, g: &mut CFGGraph<'c>) {
        let index_a = self.block_names.get(&a).unwrap();
        let index_b = self.block_names.get(&b).unwrap();
        g.add_edge(*index_a, *index_b, ());
    }

    pub fn block_index(&self, name: &StringKey) -> Option<NodeIndex> {
        self.block_names.get(name).cloned()
    }

    /*
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
    */

    pub fn save_graph(&self, filename: &str, g: &CFGGraph<'c>, b: &NodeBuilder<E>) {
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
            let block_name = b
                .strings
                .resolve(self.block_names_index.get(&node_index).unwrap())
                .clone();
            g_out.add_node(Node::new_block(block_name, node_index));
        }
        for block_node_index in g.node_indices() {
            let data = g.node_weight(block_node_index).unwrap();

            let mut x = HashMap::new();
            for (name, symbol_index) in data.symbols.iter() {
                let name = b.strings.resolve(name).clone();
                let name = match symbol_index {
                    SymIndex::Op(_, _) => {
                        format!("op:{}", name)
                    }
                    SymIndex::Arg(_, _) => {
                        format!("arg:{}", name)
                    }
                    SymIndex::Def(_, _) => {
                        format!("def:{}", name)
                    }
                };

                let symbol_node_index = g_out.add_node(Node::new_symbol(
                    name,
                    //b.strings.resolve(name).clone(),
                    //format!("{}{:?}", b.strings.resolve(name), symbol_index),
                    block_node_index,
                ));
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

    pub fn name_in_scope(
        &self,
        index: NodeIndex,
        name: StringKey,
        g: &CFGGraph<'c>,
    ) -> Option<SymIndex> {
        let dom = simple_fast(g, self.root)
            .dominators(index)
            .expect("Node not connected to root")
            .collect::<Vec<_>>();
        //println!("dom: {:?} => {:?}", index, dom);
        for i in dom.into_iter().rev() {
            let data = g.node_weight(i).unwrap();
            if let Some(r) = data.lookup(name) {
                return Some(r);
            }
        }
        None
    }

    pub fn dump_scope(&self, index: NodeIndex, g: &CFGGraph<'c>, b: &NodeBuilder<E>) {
        let dom = simple_fast(g, self.root)
            .dominators(index)
            .unwrap()
            .collect::<Vec<_>>();
        println!("dom: {:?} => {:?}", index, dom);
        for i in dom.into_iter().rev() {
            let data = g.node_weight(i).unwrap();
            let block_name = self.block_names_index.get(&i).unwrap();
            println!(
                "\t{:?}: {}, {:?}",
                i,
                b.strings.resolve(block_name),
                data.symbols.keys()
            );
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

//impl<E: Extra> AstNode<E> {
/*
   pub fn lower<'c>(
       self,
       context: &'c Context,
       d: &mut Diagnostics,
       cfg: &mut CFG<'c, E>,
       stack: &mut Vec<NodeIndex>,
       g: &mut CFGGraph<'c>,
       b: &mut NodeBuilder<E>,
   ) -> Result<SymIndex> {
       if !self.node_id.is_valid() {
           d.push_diagnostic(self.extra.error(&format!("Invalid NodeID: {:#?}", self)));
           return Err(Error::new(ParseError::Invalid));
       }

       let location = self.location(context, d);
       match self.node {
           Ast::Noop => {
               let current_block = stack.last().unwrap().clone();
               let op = op::build_bool_op(context, false, location);
               let current = g.node_weight_mut(current_block).unwrap();
               Ok(current.push(op))
           }

           Ast::Sequence(exprs) => {
               let mut out = vec![];
               for expr in exprs {
                   let index = expr.lower(context, d, cfg, stack, g, b)?;
                   out.push(index);
               }
               Ok(out.last().cloned().unwrap())
           }

           Ast::Return(maybe_expr) => {
               let current_block = stack.last().unwrap().clone();
               if let Some(expr) = maybe_expr {
                   let index = expr.lower(context, d, cfg, stack, g, b)?;
                   let current = g.node_weight_mut(current_block).unwrap();
                   let rs = current.values(index);
                   Ok(current.push(func::r#return(&rs, location)))
               } else {
                   let current = g.node_weight_mut(current_block).unwrap();
                   Ok(current.push(func::r#return(&[], location)))
               }
           }

           Ast::Label(label, args) => {
               let current_block = stack.last().unwrap().clone();
               let op = op::build_bool_op(context, false, location);
               let current = g.node_weight_mut(current_block).unwrap();
               Ok(current.push(op))
           }

           Ast::Goto(label, args) => {
               let current_block = stack.last().unwrap().clone();
               if let Some(index) = cfg.block_index(&label) {
                   g.add_edge(current_block, index, ());
                   let target_block = g.node_weight_mut(index).unwrap();
                   let block = target_block.block.as_ref().unwrap();
                   let op = cf::br(block, &[], location);
                   let current = g.node_weight_mut(current_block).unwrap();
                   Ok(current.push(op))
               } else {
                   d.push_diagnostic(
                       self.extra
                           .error(&format!("Missing block: {}", b.strings.resolve(&label))),
                   );
                   Err(Error::new(ParseError::Invalid))
               }
           }

           Ast::Identifier(name) => {
               let current_block = stack.last().unwrap().clone();
               let s = b.strings.resolve(&name);
               if let Some((op, ty)) = op::build_reserved(context, &s, location) {
                   let current = g.node_weight_mut(current_block).unwrap();
                   let index = current.push(op);
                   cfg.set_type(index, ty, VarDefinitionSpace::Reg);
                   Ok(index)
               } else {
                   if let Some(sym_index) = cfg.name_in_scope(current_block, name, g) {
                       println!(
                           "lookup identifier: {}, {:?}",
                           b.strings.resolve(&name),
                           sym_index
                       );
                       if cfg.block_is_static(sym_index.block()) {
                           let (ast_ty, mem) = cfg.lookup_type(sym_index).unwrap();
                           if let AstType::Ptr(ty) = &ast_ty {
                               let lower_ty = op::from_type(context, ty);
                               let memref_ty = MemRefType::new(lower_ty, &[], None, None);
                               let static_name = b.strings.resolve(
                                   &cfg.static_names.get(&sym_index).cloned().unwrap_or(name),
                               );
                               let op =
                                   memref::get_global(context, &static_name, memref_ty, location);
                               let current = g.node_weight_mut(current_block).unwrap();
                               let index = current.push(op);
                               cfg.set_type(index, ast_ty, mem);
                               return Ok(index);
                           } else {
                               //unreachable!("Identifier of static variable must be pointer");
                               d.push_diagnostic(
                                   self.extra
                                       .error(&format!("Expected pointer: {:?}", &ast_ty)),
                               );
                               return Err(Error::new(ParseError::Invalid));
                           }
                       } else {
                           return Ok(sym_index);
                       }
                   }
                   d.push_diagnostic(self.extra.error(&format!("Name not found: {:?}", name)));
                   Err(Error::new(ParseError::Invalid))
               }
           }

           Ast::Mutate(lhs, rhs) => {
               match lhs.node {
                   Ast::Identifier(ident) => {
                       emit_mutate(context, ident, *rhs, d, cfg, stack, g, b)
                   }
                   //Ast::Deref(expr, target) => {
                   //let index = emit_deref(context, *expr, target, d, cfg, stack, g)?;
                   //emit_mutate(context, &ident, *rhs, d, cfg, stack, g)
                   //}
                   _ => unimplemented!("{:?}", &lhs.node),
               }
           }

           Ast::Assign(target, expr) => {
               let current_block = stack.last().unwrap().clone();
               let sym_index = match target {
                   AssignTarget::Alloca(name) => {
                       //log::debug!("assign alloca: {}", name);
                       let ty = IntegerType::new(context, 64);
                       let memref_ty = MemRefType::new(ty.into(), &[], None, None);
                       let op = memref::alloca(context, memref_ty, &[], &[], None, location);
                       let rhs_index = expr.lower(context, d, cfg, stack, g, b)?;
                       let current = g.node_weight_mut(current_block).unwrap();

                       // name the pointer
                       let ptr_index = current.push_with_name(op, name);
                       let (ast_ty, mem) = cfg.lookup_type(rhs_index).unwrap();
                       let ast_ty = ast_ty.to_ptr();
                       //let ptr_ty = AstType::Ptr(ast_ty.into());
                       cfg.set_type(ptr_index, ast_ty, mem);

                       let r_value = current.value0(rhs_index).unwrap();
                       let r_addr = current.value0(ptr_index).unwrap();

                       // emit store
                       let op = memref::store(r_value, r_addr, &[], location);
                       let _index = current.push(op);
                       ptr_index
                   }
                   AssignTarget::Identifier(name) => {
                       //log::debug!("assign local: {}", name);
                       let current_block = stack.last().unwrap().clone();
                       if cfg.block_is_static(current_block) {
                           d.push_diagnostic(
                               self.extra
                                   .error(&format!("Assign static not possible: {:?}", name)),
                           );
                           return Err(Error::new(ParseError::Invalid));
                       }

                       let index = expr.lower(context, d, cfg, stack, g, b)?;
                       let current = g.node_weight_mut(index.block()).unwrap();
                       current.add_symbol(name, index);
                       //assert!(cfg.lookup_type(index).is_some());
                       index
                   }
               };
               Ok(sym_index)
           }

           Ast::Call(expr, args, ret_ty) => {
               // function to call
               let current_block = stack.last().unwrap().clone();
               let (f, ty, mem) = match &expr.node {
                   Ast::Identifier(ident) => {
                       let name = b.strings.resolve(ident);
                       if let Some(index) = cfg.name_in_scope(current_block, *ident, g) {
                           if let Some((ty, mem)) = cfg.lookup_type(index) {
                               (FlatSymbolRefAttribute::new(context, name), ty, mem)
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
                   let ret_type = op::from_type(context, &ret);
                   // handle call arguments
                   let mut indices = vec![];

                   // lower call args
                   for a in args {
                       match a {
                           Argument::Positional(arg) => {
                               let index = arg.lower(context, d, cfg, stack, g, b)?;
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
                       &[ret_type.clone()],
                       location,
                   );
                   let current = g.node_weight_mut(current_block).unwrap();

                   let index = current.push(op);
                   cfg.set_type(index, ret_ty, mem);
                   Ok(index)
               } else {
                   unimplemented!("calling non function type: {:?}", ty);
               }
           }

           Ast::Definition(mut def) => {
               def = def.normalize(b);
               let current_block = stack.last().unwrap().clone();

               assert!(cfg.block_is_static(current_block));

               let mut attributes = vec![(
                   Identifier::new(context, "sym_visibility"),
                   StringAttribute::new(context, "private").into(),
               )];

               let ret_ty = op::from_type(context, &*def.return_type);
               let mut ast_types = vec![];
               let mut types = vec![];
               //let ast_ret_type = def.return_type;

               for p in &def.params {
                   match p.node {
                       Parameter::Normal => {
                           //| Parameter::WithDefault(_) => {
                           types.push(op::from_type(context, &p.ty));
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

               let function_block = g.node_weight_mut(current_block).unwrap();
               let func_index = function_block.get_next_index();
               function_block.add_symbol(def.name, func_index);
               cfg.set_type(func_index, f_type, VarDefinitionSpace::Static);

               let region = if let Some(body) = def.body {
                   let mut edges = vec![];
                   let blocks = body.try_seq().unwrap();
                   let mut exprs = vec![];
                   let mut block_indicies = vec![];

                   // build parameter list for block
                   let mut entry_params = vec![];
                   for p in &def.params {
                       match p.node {
                           Parameter::Normal => {
                               //| Parameter::WithDefault(_) => {
                               entry_params.push((
                                   op::from_type(context, &p.ty),
                                   p.extra.location(context, d),
                               ));
                           }
                           _ => unimplemented!("{:?}", p),
                       }
                   }

                   //function_block.add_symbol();

                   for (i, b) in blocks.into_iter().enumerate() {
                       if let Ast::Block(nb) = b.node {
                           // connect the first block to the function
                           let block_name = if i == 0 { def.name.clone() } else { nb.name };

                           let block_index = cfg.add_block(context, block_name, &def.params, d, g);
                           let data = g.node_weight_mut(block_index).unwrap();

                           if i == 0 {
                               entry_block = Some(block_index);
                           }
                           for p in nb.params {
                               let index = data.push_arg(p.name);
                               cfg.set_type(index, p.ty, VarDefinitionSpace::Arg);
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
                       //cfg.dump_scope(index, g);
                       if let Ok(_index) = expr.lower(context, d, cfg, stack, g, b) {
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
                   StringAttribute::new(context, b.strings.resolve(&def.name)),
                   TypeAttribute::new(func_type.into()),
                   region,
                   &attributes,
                   location,
               );

               let function_block = g.node_weight_mut(current_block).unwrap();
               function_block.save_op(func_index, op);

               if let Some(entry_block) = entry_block {
                   let data = g.node_weight_mut(entry_block).unwrap();
                   data.set_parent_symbol(func_index);
               }

               Ok(func_index)
           }

           Ast::Literal(lit) => {
               let current_block = stack.last().unwrap().clone();
               let current = g.node_weight_mut(current_block).unwrap();
               let (op, ast_ty) = match lit {
                   Literal::Float(f) => (op::build_float_op(context, f, location), AstType::Float),

                   Literal::Int(x) => (op::build_int_op(context, x, location), AstType::Int),

                   Literal::Index(x) => (
                       op::build_index_op(context, x as i64, location),
                       AstType::Index,
                   ),

                   Literal::Bool(x) => (op::build_bool_op(context, x, location), AstType::Bool),
                   _ => unimplemented!("{:?}", lit),
               };
               let index = current.push(op);
               cfg.set_type(index, ast_ty, VarDefinitionSpace::Reg);
               Ok(index)
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
                               let index = expr.lower(context, d, cfg, stack, g, b)?;
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
                               let mut index = expr.lower(context, d, cfg, stack, g, b)?;
                               let (ast_ty, mem) = cfg.lookup_type(index).unwrap();

                               // deref
                               if ast_ty.is_ptr() {
                                   let target = DerefTarget::Offset(0);
                                   index = emit_deref(
                                       context,
                                       index,
                                       self.extra.location(context, d),
                                       target,
                                       d,
                                       cfg,
                                       stack,
                                       g,
                                   )?;
                               }

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
                   _ => unreachable!("{:?}", bi),
               }
           }

           Ast::Global(ident, expr) => {
               let current_block = stack.last().unwrap().clone();

               let is_static = cfg.root == current_block;

               let (global_name_key, global_name) = if is_static {
                   (ident, b.strings.resolve(&ident).clone())
               } else {
                   // we create a unique global name to prevent conflict
                   // and then we add ops to provide a local reference to the global name
                   let name = b.unique_static_name();
                   let name = format!("{}{}", b.strings.resolve(&ident), name).clone();
                   (b.strings.intern(name.clone()), name)
               };

               // evaluate expr at compile time
               let (op, ast_ty) = op::emit_static(context, global_name, *expr, location);

               let ptr_ty = AstType::Ptr(ast_ty.clone().into());
               if is_static {
                   // STATIC/GLOBAL VARIABLE
                   let current = g.node_weight_mut(current_block).unwrap();
                   let index = current.push_with_name(op, global_name_key);
                   cfg.set_type(index, ptr_ty, VarDefinitionSpace::Static);
                   //cfg.static_names.insert(index, global_name);
                   Ok(index)
               } else {
                   // STATIC VARIABLE IN FUNCTION CONTEXT
                   let current = g.node_weight_mut(current_block).unwrap();
                   let index = current.push_with_name(op, global_name_key);
                   cfg.set_type(index, ptr_ty, VarDefinitionSpace::Static);
                   cfg.static_names.insert(index, global_name_key);
                   Ok(index)
               }
           }

           Ast::Conditional(condition, then_expr, maybe_else_expr) => {
               let current_block = stack.last().unwrap().clone();
               let bool_type = op::from_type(context, &AstType::Bool);
               let then_location = then_expr.location(context, d);

               // condition (outside of blocks)
               let index_conditions = condition.lower(context, d, cfg, stack, g, b)?;
               let current = g.node_weight_mut(current_block).unwrap();
               let rs = current.values(current.last());
               // should be bool type
               assert!(rs[0].r#type() == bool_type);

               // then block

               //let block = Block::new(&[]);
               //let data = OpCollection::new(block);

               let then_block_index =
                   cfg.add_block(context, b.strings.intern("then".into()), &[], d, g);
               g.add_edge(current_block, then_block_index, ());

               // else
               let (maybe_else_block_index, maybe_else_expr) = match maybe_else_expr {
                   Some(else_expr) => {
                       //let block = Block::new(&[]);
                       //let data = OpCollection::new(block);
                       let block_index =
                           cfg.add_block(context, b.strings.intern("else".into()), &[], d, g);
                       g.add_edge(current_block, block_index, ());

                       (Some(block_index), Some(else_expr))
                   }
                   None => (None, None),
               };

               stack.push(then_block_index);
               if let Ok(_index) = then_expr.lower(context, d, cfg, stack, g, b) {
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
                   if let Ok(_index) = else_expr.lower(context, d, cfg, stack, g, b) {
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

           Ast::Deref(expr, target) => {
               let extra = expr.extra.clone();
               let index = expr.lower(context, d, cfg, stack, g, b)?;
               emit_deref(
                   context,
                   index,
                   extra.location(context, d),
                   target,
                   d,
                   cfg,
                   stack,
                   g,
               )
           }

           Ast::UnaryOp(op, a) => {
               use crate::ast::UnaryOperation;
               let index = a.lower(context, d, cfg, stack, g, b)?;
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
                           let index_lhs = current.push(int_op);
                           let r = current.value0(index_lhs).unwrap();
                           let r_rhs = current.value0(index).unwrap();
                           let index = current.push(arith::muli(r, r_rhs, location));
                           cfg.set_type(index, AstType::Int, VarDefinitionSpace::Reg);
                           Ok(index)
                       } else if ty.is_f64() || ty.is_f32() || ty.is_f16() {
                           // arith has an op for negation
                           let r_rhs = current.value0(index).unwrap();
                           let index = current.push(arith::negf(r_rhs, location));
                           cfg.set_type(index, AstType::Float, VarDefinitionSpace::Reg);
                           Ok(index)
                       } else {
                           unimplemented!()
                       }
                   }
               }
           }

           Ast::BinaryOp(op, x, y) => {
               let fx = format!("x: {:?}", x);
               let fy = format!("y: {:?}", y);
               let x_extra = x.extra.clone();
               let y_extra = y.extra.clone();
               let index_x = x.lower(context, d, cfg, stack, g, b)?;
               let index_y = y.lower(context, d, cfg, stack, g, b)?;
               //cfg.save_graph("out.dot", g);
               println!("ix: {:?}, {}", index_x, fx);
               println!("iy: {:?}, {}", index_y, fy);
               let (ty_x, mem_x) = cfg
                   .lookup_type(index_x)
                   .expect(&format!("missing type for {:?}, {}", index_x, fx));
               let (ty_y, mem_y) = cfg
                   .lookup_type(index_y)
                   .expect(&format!("missing type for {:?}, {}", index_y, fy));
               let current_block = stack.last().unwrap().clone();
               let current = g.node_weight_mut(current_block).unwrap();
               println!("{:?}", current);

               let (_ty_x, index_x) = if let AstType::Ptr(ty) = ty_x {
                   let target = DerefTarget::Offset(0);
                   let index = emit_deref(
                       context,
                       index_x,
                       x_extra.location(context, d),
                       target,
                       d,
                       cfg,
                       stack,
                       g,
                   )?;
                   (*ty, index)
               } else {
                   (ty_x, index_x)
               };

               let (_ty_y, index_y) = if let AstType::Ptr(ty) = ty_y {
                   let target = DerefTarget::Offset(0);
                   let index = emit_deref(
                       context,
                       index_y,
                       y_extra.location(context, d),
                       target,
                       d,
                       cfg,
                       stack,
                       g,
                   )?;
                   (*ty, index)
               } else {
                   (ty_y, index_y)
               };

               // types must be the same for binary operation, no implicit casting yet
               let a = values_in_scope(g, index_x)[0];
               let b = values_in_scope(g, index_y)[0];
               let (op, ast_ty) =
                   op::build_binop(context, op.node, a, &x_extra, b, &y_extra, location, d)?;
               let current = g.node_weight_mut(current_block).unwrap();
               let index = current.push(op);
               cfg.set_type(index, ast_ty, VarDefinitionSpace::Reg);
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
*/
//}

/*
pub fn emit_mutate<'a, 'c, E: Extra>(
    context: &'c Context,
    name_key: StringKey,
    rhs: AstNode<E>,
    d: &mut Diagnostics,
    cfg: &mut CFG<'c, E>,
    stack: &mut Vec<NodeIndex>,
    g: &mut CFGGraph<'c>,
    b: &mut NodeBuilder<E>,
) -> Result<SymIndex> {
    let name = b.strings.resolve(&name_key).clone();
    log::debug!("mutate: {}", name);

    cfg.save_graph("out.dot", g, b);
    let location = rhs.location(context, d);
    let current_block = stack.last().unwrap().clone();

    let index = cfg.name_in_scope(current_block, name_key, g).unwrap();
    //let name_is_static = cfg.block_is_static(index.block());
    let value_index = rhs.lower(context, d, cfg, stack, g, b)?;
    let (ast_ty, mem) = cfg.lookup_type(index).unwrap();
    log::debug!("mutate: {}, {:?}, {:?}", name, ast_ty, value_index);

    if ast_ty.is_ptr() {
        //{
        //let data = g.raw_nodes().get(value_index.block().index()).map(|n| &n.weight).unwrap();
        //drop(data);
        //}
        //let data = g.node_weight_mut(value_index.block()).unwrap();

        let ty = MemRefType::new(IntegerType::new(context, 64).into(), &[], None, None);
        let op1 = memref::get_global(context, &name, ty, location);
        let current = g.node_weight_mut(current_block).expect("Name not found");
        let addr_index = current.push(op1);
        let current = g.node_weight(current_block).expect("Name not found");
        let r_addr = current
            .ops
            .get(addr_index.offset())
            .unwrap()
            .result(0)
            .unwrap()
            .into();
        //let r_addr = current.value0(addr_index).unwrap().clone();

        let data = g.node_weight(value_index.block()).expect("Name not found");
        //let data = g.node_weight_mut(value_index.block()).unwrap();
        println!("{:?}", data.ops.get(value_index.offset()));

        let r_value = data
            .ops
            .get(value_index.offset())
            .unwrap()
            .result(0)
            .unwrap()
            .into();
        //let r_value = data.value0(value_index).unwrap().clone();

        //let r_value = values_in_scope(g, value_index)[0];
        //let current = g.node_weight_mut(current_block).expect("Name not found");
        //let r_value = data.value0(value_index).unwrap();
        //let r_addr = current.value0(addr_index).unwrap();
        let op = memref::store(r_value, r_addr, &[], location);
        //op
        let current = g.node_weight_mut(current_block).expect("Name not found");
        let _index = current.push(op);
        Ok(addr_index)
    } else {
        let current = g.node_weight_mut(current_block).expect("Name not found");
        let r_addr = current.value0(index).unwrap();
        let r_value = current.value0(value_index).unwrap();
        let op = memref::store(r_value, r_addr, &[], location);
        current.push(op);
        Ok(index)
    }
}
*/

/*
#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::SimpleExtra;
    use crate::tests::gen_block;
    use crate::{default_context, Diagnostics, NodeBuilder};
    use test_log::test;

    /*
    #[test]
    fn test_cfg_block_ast() {
        let context = default_context();
        let mut module = Module::new(Location::unknown(&context));
        let mut g = CFGGraph::new();
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let mut b = NodeBuilder::new();
        b.enter(file_id, "type.py");

        let mut cfg: CFG<SimpleExtra> =
            CFG::new(&context, b.strings.intern("module".to_string()), &d, &mut g);

        let ast = gen_block(&mut b).normalize(&mut cfg, &mut d, &mut b);
        let mut stack = vec![cfg.root];
        let r = ast.lower(&context, &mut d, &mut cfg, &mut stack, &mut g, &mut b);
        assert_eq!(1, stack.len());
        d.dump();
        assert!(!d.has_errors);
        r.unwrap();
        cfg.module(&context, &mut module, &mut g);
        let shared = cfg.shared.iter().cloned().collect::<Vec<_>>();
        exec_main(&shared, &module, "../target/debug/");
        cfg.save_graph("out.dot", &g, &b);
    }


    //#[test]
    fn test_cfg_while() {
        use crate::tests::gen_while;
        let context = default_context();
        let mut module = Module::new(Location::unknown(&context));
        let mut g = CFGGraph::new();
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let mut b = NodeBuilder::new();
        b.enter(file_id, "type.py");
        let mut cfg: CFG<SimpleExtra> =
            CFG::new(&context, b.strings.intern("module".to_string()), &d, &mut g);

        let mut ast = gen_while(&mut b);
        let mut stack = vec![cfg.root];
        ast.preprocess(&mut cfg, &mut d, &mut b);
        ast.analyze(&mut b);
        let r = ast.lower(&context, &mut d, &mut cfg, &mut stack, &mut g, &mut b);
        d.dump();
        assert!(!d.has_errors);
        r.unwrap();
        cfg.module(&context, &mut module, &mut g);
        let shared = cfg.shared.iter().cloned().collect::<Vec<_>>();
        exec_main(&shared, &module, "../target/debug/");
        cfg.save_graph("out.dot", &g, &b);
        assert_eq!(1, stack.len());
    }
    */

    /*
    #[test]
    fn test_cfg_graph() {
        let context = default_context();
        let d = Diagnostics::new();
        let mut g = CFGGraph::new();
        let mut b = NodeBuilder::new();
        let mut cfg: CFG<SimpleExtra> = CFG::new(&context, b.strings.intern("module".to_string()), &d, &mut g);

        (0..8).into_iter().for_each(|i| {
            let block_name = b.strings.intern(format!("b{}", i));
            cfg.add_block(&context, block_name, &[], &d, &mut g);
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
    */
}
*/
