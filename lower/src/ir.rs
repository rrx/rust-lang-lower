use anyhow::Error;
use anyhow::Result;

use crate::cfg::{CFGGraph, SymIndex, CFG};
use crate::{AstNode, AstType, Diagnostics, Extra, NodeBuilder, NodeID, ParseError, StringKey};
use melior::Context;
use std::fmt::Debug;

use crate::ast::{
    Argument, AssignTarget, Ast, BinaryOperation, Builtin, DerefTarget, Literal, Parameter,
    ParameterNode, UnaryOperation,
};

use petgraph::algo::dominators::simple_fast;
use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;
use std::collections::HashMap;
//use std::collections::HashSet;

#[derive(Debug)]
pub enum IRTypeSelect {
    // array offset
    Offset(usize),
    // attribute select on tuple
    Attr(usize),
    // byte level view (width, offset)
    Byte(u8, usize),
}

impl Default for IRTypeSelect {
    fn default() -> Self {
        Self::Offset(0)
    }
}
#[derive(Debug, Clone)]
pub struct IRArg {
    name: StringKey,
    ty: AstType,
}

#[derive(Debug)]
pub struct IRBlock {
    arg_count: usize,
    block_index: NodeIndex,
    params: Vec<IRArg>,
    symbols: HashMap<StringKey, SymIndex>,
    def_count: usize,
}

impl IRBlock {
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
    stack: Vec<NodeIndex>,
    block_names: HashMap<StringKey, NodeIndex>,
    block_names_index: HashMap<NodeIndex, StringKey>,
    types: HashMap<SymIndex, AstType>,
}

pub type IRGraph = DiGraph<IRBlock, ()>;

impl IREnvironment {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn lookup_type(&self, index: SymIndex) -> Option<AstType> {
        self.types.get(&index).cloned()
    }

    pub fn set_type(&mut self, index: SymIndex, ty: AstType) {
        self.types.insert(index, ty);
    }

    pub fn enter_block(&mut self, index: NodeIndex) {
        self.stack.push(index);
    }

    pub fn exit_block(&mut self) {
        self.stack.pop();
    }

    pub fn stack_size(&self) -> usize {
        self.stack.len()
    }

    pub fn root(&self) -> NodeIndex {
        self.stack.first().unwrap().clone()
    }

    pub fn current_block(&self) -> NodeIndex {
        self.stack.last().unwrap().clone()
    }

    pub fn add_block(
        &mut self,
        name: StringKey,
        params: Vec<IRArg>,
        d: &Diagnostics,
        g: &mut IRGraph,
    ) -> NodeIndex {
        let index = g.add_node(IRBlock::new(params));
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
        let dom = simple_fast(g, self.root())
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

    pub fn symbol_is_static(&self, index: SymIndex) -> bool {
        // root block is static block, and there's only one for now
        self.root() == index.block()
    }

    pub fn block_is_static(&self, block_index: NodeIndex) -> bool {
        // root block is static block, and there's only one for now
        self.root() == block_index
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
    Decl(StringKey, AstType),
    // set(variable, expr, type offset)
    Set(StringKey, Box<IRNode>, IRTypeSelect),
    // get(variable, type offset)
    Get(StringKey, IRTypeSelect),
    // ret(args)
    Ret(Vec<IRNode>),
    Cond(Box<IRNode>, Box<IRNode>, Option<Box<IRNode>>),
    Jump(StringKey, Vec<IRNode>),
    // call(variable, args), return type is inferred from variable
    Call(StringKey, Vec<IRNode>),
    // op(operation, args)
    Op1(UnaryOperation, Box<IRNode>),
    Op2(BinaryOperation, Box<IRNode>, Box<IRNode>),
    Block(StringKey, Vec<IRArg>, Vec<IRNode>),
    Seq(Vec<IRNode>),
    Literal(Literal),
    Builtin(Builtin, Vec<IRNode>),
    Noop,
}

#[derive(Debug)]
pub struct IRNode {
    kind: IRKind,
    loc: usize,
}

impl IRNode {
    pub fn new(kind: IRKind) -> Self {
        Self { kind, loc: 0 }
    }
    pub fn to_vec(self) -> Vec<Self> {
        if let IRKind::Seq(exprs) = self.kind {
            exprs
        } else {
            vec![self]
        }
    }

    pub fn dump<E: Extra>(&self, b: &NodeBuilder<E>, depth: usize) {
        match &self.kind {
            IRKind::Seq(exprs) => {
                //println!("{:width$}seq:", "", width = depth * 2);
                for e in exprs {
                    e.dump(b, depth);
                }
            }
            IRKind::Decl(key, ty) => {
                println!(
                    "{:width$}decl({}, {:?})",
                    "",
                    b.strings.resolve(key),
                    ty,
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

            IRKind::Block(key, args, body) => {
                println!(
                    "{:width$}block({})",
                    "",
                    b.strings.resolve(key),
                    width = depth * 2
                );
                for a in args {
                    println!(
                        "{:width$}arg: {}: {:?}",
                        "",
                        b.strings.resolve(&a.name),
                        a.ty,
                        width = (depth + 1) * 2
                    );
                }
                for a in body {
                    a.dump(b, depth + 1);
                }
            } //_ => ()//unimplemented!()
        }
    }
}

impl<E: Extra> AstNode<E> {
    pub fn lower_ir_expr<'c>(
        self,
        context: &'c Context,
        d: &mut Diagnostics,
        env: &mut IREnvironment,
        g: &mut IRGraph,
        b: &mut NodeBuilder<E>,
    ) -> Result<IRNode> {
        let mut out = vec![];
        self.lower_ir(context, &mut out, d, env, g, b)?;
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
        context: &'c Context,
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
            Ast::Noop => {
                //out.push(b.ir_noop());
                Ok(())
            }

            Ast::Sequence(exprs) => {
                for expr in exprs {
                    let ir = expr.lower_ir_expr(context, d, env, g, b)?.to_vec();
                    out.extend(ir);
                }
                Ok(())
            }

            Ast::Return(maybe_expr) => {
                let mut args = vec![];
                if let Some(expr) = maybe_expr {
                    expr.lower_ir(context, &mut args, d, env, g, b)?;
                }
                out.push(b.ir_ret(args));
                Ok(())
            }

            Ast::Goto(label) => {
                let block_index = env.current_block();
                //let data = g.node_weight(block_index).unwrap();
                let block_name = env.block_names_index.get(&block_index).unwrap().clone();
                out.push(b.ir_jump(label, vec![]));
                env.add_edge(block_name, label, g);
                Ok(())
            }

            Ast::Identifier(name) => {
                let current_block = env.current_block();
                //let s = b.strings.resolve(&name);
                env.save_graph("out.dot", g, b);
                if let Some(sym_index) = env.name_in_scope(current_block, name, g) {
                    println!(
                        "lookup identifier: {}, {:?}",
                        b.strings.resolve(&name),
                        sym_index
                    );
                    if env.symbol_is_static(sym_index) {
                        let ast_ty = env.lookup_type(sym_index).unwrap();
                        //if let AstType::Ptr(_ty) = &ast_ty {
                        //Ok(b.ir_get(name, IRTypeSelect::default()))
                        out.push(b.ir_get(name, IRTypeSelect::default()));
                        Ok(())

                        /*
                        let lower_ty = op::from_type(context, ty);
                        let memref_ty = MemRefType::new(lower_ty, &[], None, None);
                        let static_name = b.strings.resolve(
                            &env.static_names.get(&sym_index).cloned().unwrap_or(name),
                        );
                        let op =
                            memref::get_global(context, &static_name, memref_ty, location);
                        let current = g.node_weight_mut(current_block).unwrap();
                        let index = current.push(op);
                        env.set_type(index, ast_ty);
                        return Ok(index);
                        */
                        /*
                        } else {
                            d.push_diagnostic(
                                self.extra
                                    .error(&format!("Expected pointer: {:?}", &ast_ty)),
                            );
                            return Err(Error::new(ParseError::Invalid));
                        }
                        */
                    } else {
                        out.push(b.ir_get(name, IRTypeSelect::default()));
                        Ok(())
                    }
                } else {
                    d.push_diagnostic(self.extra.error(&format!(
                        "Undefined variable: {:?}",
                        b.strings.resolve(&name)
                    )));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            Ast::Global(ident, expr) => {
                let current_block = env.current_block();

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

                if let Ast::Literal(lit) = expr.node {
                    let ty: AstType = lit.into();
                    //Ok(b.ir_decl(global_name_key, ty))
                    let data = g.node_weight_mut(current_block).unwrap();
                    let index = data.add_definition(global_name_key);
                    env.set_type(index, ty.clone());
                    out.push(b.ir_decl(global_name_key, ty));
                    Ok(())
                } else {
                    unreachable!()
                }
            }

            Ast::Assign(target, expr) => {
                //let current_block = stack.last().unwrap().clone();
                match target {
                    AssignTarget::Alloca(name) | AssignTarget::Identifier(name) => {
                        let mut seq = vec![];
                        expr.lower_ir(context, &mut seq, d, env, g, b)?;
                        let current_block = env.current_block();
                        //let s = b.strings.resolve(&name);
                        env.save_graph("out.dot", g, b);
                        if let Some(sym_index) = env.name_in_scope(current_block, name, g) {
                            out.push(b.ir_set(name, b.ir_seq(seq), IRTypeSelect::Offset(0)));
                            Ok(())
                        } else {
                            //Ok(b.ir_decl(name, AstType::Int))
                            let ty = AstType::Int;
                            out.push(b.ir_decl(name, ty.clone()));
                            let data = g.node_weight_mut(current_block).unwrap();
                            let index = data.add_definition(name);
                            env.set_type(index, ty);
                            Ok(())
                        }

                        /*
                        //log::debug!("assign alloca: {}", name);
                        let ty = IntegerType::new(context, 64);
                        let memref_ty = MemRefType::new(ty.into(), &[], None, None);
                        let op = memref::alloca(context, memref_ty, &[], &[], None, location);
                        let rhs_index = expr.lower(context, d, env, stack, g, b)?;
                        let current = g.node_weight_mut(current_block).unwrap();

                        // name the pointer
                        let ptr_index = current.push_with_name(op, name);
                        let ast_ty = env.lookup_type(rhs_index).unwrap().to_ptr();
                        //let ptr_ty = AstType::Ptr(ast_ty.into());
                        env.set_type(ptr_index, ast_ty);

                        let r_value = current.value0(rhs_index).unwrap();
                        let r_addr = current.value0(ptr_index).unwrap();

                        // emit store
                        let op = memref::store(r_value, r_addr, &[], location);
                        let _index = current.push(op);
                        ptr_index
                        */
                    } /*
                      AssignTarget::Identifier(name) => {
                          //log::debug!("assign local: {}", name);
                          let current_block = stack.last().unwrap().clone();
                          if env.block_is_static(current_block) {
                              d.push_diagnostic(
                                  self.extra
                                      .error(&format!("Assign static not possible: {:?}", name)),
                              );
                              return Err(Error::new(ParseError::Invalid));
                          }

                          //let index = expr.lower(context, d, env, stack, g, b)?;
                          let current = g.node_weight_mut(index.block()).unwrap();
                          current.add_symbol(name, index);
                          //assert!(env.lookup_type(index).is_some());
                          index
                      }
                      */
                }
                //Ok(sym_index)
            }

            Ast::Mutate(lhs, rhs) => {
                match lhs.node {
                    Ast::Identifier(name) => {
                        let mut seq = vec![];
                        rhs.lower_ir(context, &mut seq, d, env, g, b)?;
                        out.push(b.ir_set(name, b.ir_seq(seq), IRTypeSelect::Offset(0)));
                        Ok(())
                        //emit_mutate(context, ident, *rhs, d, env, stack, g, b)
                    }
                    //Ast::Deref(expr, target) => {
                    //let index = emit_deref(context, *expr, target, d, env, stack, g)?;
                    //emit_mutate(context, &ident, *rhs, d, env, stack, g)
                    //}
                    _ => unimplemented!("{:?}", &lhs.node),
                }
            }

            Ast::Call(expr, args, ret_ty) => {
                // function to call
                let current_block = env.current_block();
                let (f, ty, f_args, name) = match &expr.node {
                    Ast::Identifier(ident) => {
                        let name = b.strings.resolve(ident);
                        env.save_graph("out.dot", g, b);
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
                                //(FlatSymbolRefAttribute::new(context, name), ty)
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
                                expr.lower_ir(context, &mut ir_args, d, env, g, b)?;
                            }
                        }
                    }
                    out.push(b.ir_call(*f, ir_args));
                    Ok(())

                    /*
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
                    env.set_type(index, ret_ty);
                    Ok(index)
                    */
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
                        Parameter::Normal | Parameter::WithDefault(_) => {
                            ast_types.push(p.ty.clone());
                        }
                        _ => unimplemented!("{:?}", p),
                    }
                }
                let ast_ret_type = def.return_type;
                let f_type = AstType::Func(ast_types, ast_ret_type);

                let mut data = g.node_weight_mut(current_block).unwrap();
                let index = data.add_definition(def.name);
                env.set_type(index, f_type.clone());
                out.push(b.ir_decl(def.name, f_type));

                let mut output_blocks = vec![];
                let mut edges = vec![];
                if let Some(body) = def.body {
                    let blocks = body.try_seq().unwrap();
                    for (i, block) in blocks.into_iter().enumerate() {
                        if let Ast::Block(nb) = block.node {
                            let mut args = vec![];
                            for a in &nb.params {
                                args.push(IRArg {
                                    name: a.name,
                                    ty: a.ty.clone(),
                                });
                            }

                            let block_index = env.add_block(nb.name, args.clone(), d, g);
                            if i == 0 {
                                edges.push((current_block, block_index));
                            }

                            let mut data = g.node_weight_mut(block_index).unwrap();
                            for a in &nb.params {
                                data.push_arg(a.name);
                            }

                            //env.enter_block(block_index);

                            //let exprs = nb.body.lower_ir_expr(context, d, env, g, b)?.to_vec();
                            //let ir = IRNode::new(IRKind::Block(nb.name, args, exprs));
                            output_blocks.push((nb, block_index)); //ir);

                        //env.exit_block();
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
                    for (nb, block_index) in output_blocks {
                        env.enter_block(block_index);
                        let exprs = nb.body.lower_ir_expr(context, d, env, g, b)?.to_vec();
                        let mut args = vec![];
                        for a in nb.params {
                            args.push(IRArg {
                                name: a.name,
                                ty: a.ty,
                            });
                        }
                        let ir = IRNode::new(IRKind::Block(nb.name, args, exprs));
                        blocks.push(ir);
                        env.exit_block();
                    }
                    out.push(b.ir_set(def.name, b.ir_seq(blocks), IRTypeSelect::default()));
                }
                Ok(()) //b.ir_seq(out))
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
                            expr.lower_ir(context, &mut ir_args, d, env, g, b)?;
                        }
                    }
                }
                out.push(IRNode::new(IRKind::Builtin(bi, ir_args)));
                Ok(())
            }

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
                let ir_cond = condition.lower_ir_expr(context, d, env, g, b)?;
                //let b_then = b.s("then");
                //let b_next = b.s("next");
                let then_block = then_expr.lower_ir_expr(context, d, env, g, b)?;

                let else_block = if let Some(else_expr) = maybe_else_expr {
                    //let b_else = b.s("else");
                    Some(else_expr.lower_ir_expr(context, d, env, g, b)?)
                } else {
                    None
                };

                out.push(b.ir_cond(ir_cond, then_block, else_block));
                Ok(())
            }

            Ast::UnaryOp(op, a) => {
                let ir = a.lower_ir_expr(context, d, env, g, b)?;
                out.push(b.ir_op1(op, ir));
                Ok(())
            }

            Ast::BinaryOp(op_node, x, y) => {
                let x = x.lower_ir_expr(context, d, env, g, b)?;
                let y = y.lower_ir_expr(context, d, env, g, b)?;
                out.push(b.ir_op2(op_node.node, x, y));
                Ok(())
            }

            Ast::Deref(expr, _target) => expr.lower_ir(context, out, d, env, g, b),

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
        env.enter_block(index);

        let r = ast.lower_ir_expr(&context, &mut d, &mut env, &mut g, &mut b);
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
        env.enter_block(index);

        let r = ast.lower_ir_expr(&context, &mut d, &mut env, &mut g, &mut b);
        d.dump();
        assert!(!d.has_errors);
        let ir = r.unwrap();
        println!("ir: {:#?}", ir);
        ir.dump(&b, 0);
        assert_eq!(1, env.stack.len());
    }
}
