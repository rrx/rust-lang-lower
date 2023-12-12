use crate::ast::{AstNode, AstType, Extra, ParameterNode};
use crate::blocks::{BlockGraph, Index};
use crate::Diagnostics;
use melior::ir::*;
use melior::ir::{Operation, Value};
use melior::Context;
use std::collections::{HashMap, HashSet};

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum LayerType {
    Static,
    Function,
    Block,
    Closed,
    Preserve,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct OpIndex(usize);

impl From<usize> for OpIndex {
    fn from(item: usize) -> Self {
        Self(item)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LayerIndex {
    Op(usize),
    Noop,
    Argument(usize),
    BlockArg(usize, usize),
    Static(usize),
}

impl LayerIndex {
    pub fn op(index: OpIndex) -> Self {
        Self::Op(index.0)
    }

    pub fn arg(index: usize) -> Self {
        Self::Argument(index)
    }

    pub fn static_index(index: usize) -> Self {
        Self::Static(index)
    }
}

#[derive(Debug)]
pub struct Layer<'c, E> {
    ty: LayerType,
    pub(crate) ops: Vec<Operation<'c>>,
    pub(crate) names: HashMap<String, LayerIndex>,
    pub(crate) index: HashMap<LayerIndex, usize>,
    blocks: Vec<Block<'c>>,
    pub(crate) g: BlockGraph<'c, E>,
    block_names: HashMap<String, usize>,
    _last_index: Option<LayerIndex>,
}

impl<'c, E: Extra> Layer<'c, E> {
    pub fn new(ty: LayerType) -> Self {
        Self {
            ty,
            ops: vec![],
            names: HashMap::new(),
            index: HashMap::new(),
            g: BlockGraph::new(),
            blocks: vec![],
            block_names: HashMap::new(),
            _last_index: None,
        }
    }

    /*
    pub fn append_block(&mut self, block: Block<'c>) {
        self.region.as_ref().unwrap().append_block(block);
    }

    pub fn enter_region(&mut self, region: Region<'c>) {
        assert!(self.region.is_none());
        self.region = Some(region);
    }

    pub fn exit_region(&mut self) -> Region<'c> {
        let region = self.region.take().unwrap();
        self.block_names.clear();
        for block in self.blocks.drain(..) {
            region.append_block(block);
        }
        region
    }
    */

    pub fn build(&mut self) {
        self.g.build();
    }

    pub fn dfs_first(&mut self) -> Vec<(Index, Vec<Index>)> {
        self.g.dfs_first()
    }

    pub fn get_params(&self, index: Index) -> &Vec<ParameterNode<E>> {
        self.g.get_params(index)
    }

    pub fn enter_block(&mut self, name: &str, block: Block<'c>) -> usize {
        assert!(!self.block_names.contains_key(name));
        let offset = self.blocks.len();
        self.blocks.push(block);
        self.block_names.insert(name.to_string(), offset);
        offset
    }

    pub fn exit_block(&mut self) -> Block<'c> {
        let block = self.blocks.pop().unwrap();
        if self.blocks.len() == 0 {
            self.block_names.clear();
        }
        let ops = self.take_ops();
        for op in ops {
            block.append_operation(op);
        }
        block
    }

    pub fn block(&self, name: &str) -> Option<&Block<'c>> {
        self.block_names
            .get(name)
            .map(|index| self.blocks.get(*index).unwrap())
    }

    /*
    pub fn merge(&mut self, mut layer: Layer<'c>) {
        let preserve_names = match layer.ty {
            LayerType::Closed | LayerType::Function | LayerType::Block => false,
            _ => true,
        };

        // optionally preserve names
        // overwrite existing names, thus shadowing
        if preserve_names {
            for (k, v) in layer.names {
                // only do ops, not args
                if let LayerIndex::Op(_) = v {
                    self.names.insert(k, v);
                }
            }
        }

        for op in layer.ops.drain(..) {
            self.ops.push(op);
        }
        self._last_index = layer._last_index;
    }
    */

    pub fn index_name(&mut self, index: LayerIndex, name: &str) {
        self.names.insert(name.to_string(), index);
    }

    pub fn name_index(&mut self, index: LayerIndex, name: &str) {
        self.names.insert(name.to_string(), index);
    }

    pub fn push(&mut self, op: Operation<'c>, index: LayerIndex) {
        let pos = self.ops.len();
        self.ops.push(op);
        self.index.insert(index.clone(), pos);
        self._last_index = Some(index);
    }

    pub fn push_with_name(&mut self, op: Operation<'c>, index: LayerIndex, name: &str) {
        self.push(op, index.clone());
        self.names.insert(name.to_string(), index);
    }

    pub fn last_index(&self) -> LayerIndex {
        self._last_index.clone().unwrap()
    }

    pub fn value_from_name(&self, name: &str) -> Option<Vec<Value<'c, '_>>> {
        match self.index_from_name(name) {
            //match self.names.get(name) {
            Some(index) => {
                self.values(&index)
                /*
                let offset = self.index.get(index).unwrap();
                Some(match index {
                    LayerIndex::BlockArg(block_offset, arg_offset) => {
                        use crate::blocks::Index;
                        let block = self.g.as_ref().unwrap().get_block(Index::new(*block_offset));
                        vec![block.argument(*arg_offset).unwrap().into()]
                    }
                    LayerIndex::Noop => vec![],
                    LayerIndex::Static(_) => vec![],
                    LayerIndex::Op(_) => self
                        .ops
                        .get(*offset)
                        .unwrap()
                        .results()
                        .map(|x| x.into())
                        .collect(),
                    LayerIndex::Argument(_) => {
                        vec![self
                            .blocks
                            .last()
                            .unwrap()
                            .argument(*offset)
                            .unwrap()
                            .into()]
                    }
                })
                */
            }
            _ => None,
        }
    }

    pub fn index_from_name(&self, name: &str) -> Option<LayerIndex> {
        self.names.get(name).cloned()
    }

    pub fn values(&self, index: &LayerIndex) -> Option<Vec<Value<'c, '_>>> {
        println!("looking for {:?} in {:?}", index, self.ty);
        if let LayerIndex::BlockArg(block_offset, arg_offset) = index {
            //use crate::blocks::Index;
            //if let Some(g) = &self.g {
            let result = if self.g.blocks.len() > 0 {
                let block = self.g.get_block(Index::new(*block_offset));
                Some(vec![block.argument(*arg_offset).unwrap().into()])
            } else {
                None
            };
            println!(
                "len blocks: {:?}, {}, result: {}",
                self.ty,
                self.g.blocks.len(),
                result.is_some()
            );
            return result;
            //}
        }

        if let Some(offset) = self.index.get(&index) {
            log::debug!(
                "found: {:?} - {}/{}, {:?}",
                index,
                offset,
                self.ops.len(),
                self.ty
            );
            match index {
                //LayerIndex::Static(_) => vec![],
                /*
                LayerIndex::BlockArg(block_offset, arg_offset) => {
                    use crate::blocks::Index;
                    if let Some(g) = &self.g {
                        println!("len blocks: {}", g.blocks.len());
                        if g.blocks.len() > 0 {
                            let block = g.get_block(Index::new(*block_offset));
                            Some(vec![block.argument(*arg_offset).unwrap().into()])
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
                */
                LayerIndex::Op(_) => Some(
                    self.ops
                        .get(*offset)
                        .expect("Op missing")
                        .results()
                        .map(|x| x.into())
                        .collect(),
                ),
                LayerIndex::Argument(_) => Some(vec![self
                    .blocks
                    .first()
                    .expect("Argument Missing")
                    .argument(*offset)
                    .unwrap()
                    .into()]),
                _ => unimplemented!("{:?}", index),
            }
        } else {
            None
        }
    }

    pub fn push_index(&mut self, index: LayerIndex) {
        self._last_index = Some(index);
    }

    pub fn push_noop(&mut self) -> LayerIndex {
        self.push_index(LayerIndex::Noop);
        LayerIndex::Noop
    }

    pub fn take_ops(&mut self) -> Vec<Operation<'c>> {
        self.names.clear();
        self.ops.drain(..).collect()
    }

    pub fn take_region(&mut self) -> Region<'c> {
        let region = Region::new();
        for block in self.blocks.drain(..) {
            region.append_block(block);
        }
        region
    }

    pub fn select(&mut self, name: &str, mut layer: Layer<'c, E>) {
        let ops = layer.take_ops();
        let block = self.block(name).unwrap();
        for op in ops {
            block.append_operation(op);
        }
    }

    pub fn push_block(
        &mut self,
        context: &'c Context,
        name: &str,
        params: Vec<ParameterNode<E>>,
        expr: AstNode<E>,
        d: &Diagnostics,
    ) {
        //assert!(self.g.is_some());
        log::debug!("block block: {}", name);
        let _ = self.g.add_node(context, &name, params, expr, d);
    }
}

#[derive(Debug)]
pub struct ScopeStack<'c, E> {
    op_count: usize,
    static_count: usize,
    layers: Vec<Layer<'c, E>>,
    types: HashMap<LayerIndex, AstType>,
    static_names: HashMap<LayerIndex, String>,
    pub shared: HashSet<String>,
}

impl<'c, E> Default for ScopeStack<'c, E> {
    fn default() -> Self {
        Self {
            op_count: 0,
            static_count: 0,
            layers: vec![],
            types: HashMap::new(),
            static_names: HashMap::new(),
            shared: HashSet::new(),
        }
    }
}

impl<'c, E: Extra> ScopeStack<'c, E> {
    pub fn layer_count(&self) -> usize {
        self.layers.len()
    }

    pub fn dump(&self) {
        //println!("env: {:?}", self);
        for layer in &self.layers {
            println!("Layer: {:?}", layer.ty);
            for (name, index) in layer.names.iter() {
                println!(
                    "\t{:?}: {:?}, ty: {:?}, index: {:?}",
                    name,
                    index,
                    self.types.get(index),
                    layer.index.get(index)
                );
            }
            for (name, index) in layer.block_names.iter() {
                println!("Block: {}, {}", index, name);
                let block = layer.blocks.get(*index).unwrap();
                for i in 0..block.argument_count() {
                    println!("\tArg: {}, {:?}", i, block.argument(i).unwrap().r#type());
                }
            }
            //if let Some(g) = &layer.g {
            for (block_index, block) in layer.g.blocks.iter().enumerate() {
                println!("XBlock: {}", block_index);
                for i in 0..block.argument_count() {
                    println!(
                        "\tXArg: {}, {}, {:?}",
                        block_index,
                        i,
                        block.argument(i).unwrap().r#type()
                    );
                }
            }
            //println!("g: {:?}", g);
            //}
        }
    }

    pub fn add_shared(&mut self, s: &str) {
        self.shared.insert(s.to_string());
    }

    pub fn index_data(&mut self, index: &LayerIndex, ty: AstType) {
        self.types.insert(index.clone(), ty);
    }

    pub fn index_static_name(&mut self, index: &LayerIndex, static_name: &str) {
        self.static_names
            .insert(index.clone(), static_name.to_string());
    }

    pub fn data(&self, index: &LayerIndex) -> Option<AstType> {
        self.types.get(index).cloned()
    }

    pub fn static_name(&self, index: &LayerIndex) -> Option<&String> {
        self.static_names.get(index)
    }

    pub fn current_layer_type(&self) -> LayerType {
        self.layers.last().unwrap().ty
    }

    pub fn fresh_argument(&mut self) -> LayerIndex {
        LayerIndex::Argument(self.fresh_index())
    }

    pub fn unique_static_name(&mut self) -> String {
        let s = format!("__static_x{}", self.static_count);
        self.static_count += 1;
        s
    }

    pub fn fresh_op(&mut self) -> LayerIndex {
        LayerIndex::Op(self.fresh_index())
    }

    pub fn fresh_index(&mut self) -> usize {
        let index = self.op_count;
        self.op_count += 1;
        index
    }

    pub fn enter_closed(&mut self) {
        let layer = Layer::new(LayerType::Closed);
        self.enter(layer);
    }

    pub fn enter_func(&mut self) {
        let layer = Layer::new(LayerType::Function);
        self.enter(layer);
    }

    pub fn enter_static(&mut self) {
        let layer = Layer::new(LayerType::Static);
        self.enter(layer);
    }

    pub fn enter(&mut self, layer: Layer<'c, E>) {
        self.layers.push(layer);
    }

    pub fn exit(&mut self) -> Layer<'c, E> {
        let layer = self.layers.pop().unwrap();
        //self.merge(layer);
        layer
    }

    /*
    pub fn merge(&mut self, layer: Layer<'c>) {
        if let Some(last) = self.layers.last_mut() {
            last.merge(layer);
        } else {
            unreachable!()
        }
    }
    */

    pub fn last(&mut self) -> &Layer<'c, E> {
        if let Some(last) = self.layers.last() {
            last
        } else {
            unreachable!("No more layers")
        }
    }

    pub fn last_mut(&mut self) -> &mut Layer<'c, E> {
        if let Some(last) = self.layers.last_mut() {
            last
        } else {
            unreachable!("No more layers")
        }
    }

    pub fn index_name(&mut self, index: LayerIndex, name: &str) {
        self.last_mut().index_name(index, name);
    }

    pub fn name_index(&mut self, index: LayerIndex, name: &str) {
        self.last_mut().index_name(index, name);
    }

    pub fn push_static(&mut self, op: Operation<'c>, name: &str) -> LayerIndex {
        let index = LayerIndex::Op(self.fresh_index());
        self.layers
            .first_mut()
            .unwrap()
            .push_with_name(op, index.clone(), name);
        index
    }

    pub fn push(&mut self, op: Operation<'c>) -> LayerIndex {
        let index = LayerIndex::Op(self.fresh_index());
        self.last_mut().push(op, index.clone());
        index
    }

    pub fn push_op_index(&mut self, index: LayerIndex, op: Operation<'c>) {
        self.last_mut().push(op, index);
    }

    pub fn push_with_name(&mut self, op: Operation<'c>, name: &str) -> LayerIndex {
        let index = match self.current_layer_type() {
            // naming ops in static context doesn't make sense
            //LayerType::Static => unreachable!("Unable to name op in static context"), //LayerIndex::Static(self.fresh_op()),
            _ => LayerIndex::Op(self.fresh_index()),
        };
        self.last_mut().push_with_name(op, index.clone(), name);
        index
    }

    pub fn push_index(&mut self, index: LayerIndex) {
        self.layers.last_mut().unwrap().push_index(index)
    }

    pub fn push_noop(&mut self) -> LayerIndex {
        self.layers.last_mut().unwrap().push_noop()
    }

    pub fn last_index(&self) -> Option<LayerIndex> {
        self.layers.last().map(|x| x.last_index())
    }

    pub fn value0_from_name(&self, name: &str) -> Value<'c, '_> {
        self.values_from_name(name)[0]
    }

    pub fn values_from_name(&self, name: &str) -> Vec<Value<'c, '_>> {
        for layer in self.layers.iter().rev() {
            if let Some(r) = layer.value_from_name(name) {
                return r;
            }
        }
        unreachable!("Name not found: {:?}", name);
    }

    pub fn value0(&self, index: &LayerIndex) -> Value<'c, '_> {
        //self.dump();
        for layer in self.layers.iter().rev() {
            if let Some(result) = layer.values(&index) {
                if result.len() == 0 {
                    println!("xlayer: {:?}", &layer);
                    unreachable!("Lookup op without value: {:?}", index);
                }
                return result[0]; //.get(0).expect("Missing value");
            }
        }
        unreachable!("Index not found: {:?}", index);
    }

    pub fn values(&self, index: &LayerIndex) -> Vec<Value<'c, '_>> {
        for layer in self.layers.iter().rev() {
            if let Some(result) = layer.values(&index) {
                return result;
            }
        }
        unreachable!("Index not found: {:?}", index);
    }

    pub fn last_values(&self) -> Vec<Value<'c, '_>> {
        self.values(&self.last_index().unwrap())
    }

    pub fn data_from_name(&self, name: &str) -> Option<(LayerIndex, AstType, Option<String>)> {
        if let Some(index) = self.index_from_name(name) {
            let ty = self.types.get(&index).unwrap();
            let static_name = self.static_name(&index).cloned();
            Some((index, ty.clone(), static_name))
        } else {
            None
        }
    }

    pub fn index_from_name(&self, name: &str) -> Option<LayerIndex> {
        for layer in self.layers.iter().rev() {
            let result = layer.index_from_name(name);
            if result.is_some() {
                return result;
            }
        }
        None
    }

    pub fn take_ops(&mut self) -> Vec<Operation<'c>> {
        let mut out = vec![];
        for layer in self.layers.iter_mut() {
            out.extend(layer.take_ops());
        }
        out
    }

    pub fn exit_block(&mut self) -> Block<'c> {
        self.layers.last_mut().unwrap().exit_block()
    }

    pub fn block(&self, name: &str) -> Option<&Block<'c>> {
        for layer in self.layers.iter().rev() {
            let result = layer.block(name);
            if result.is_some() {
                return result;
            }
        }
        None
    }

    pub fn select(&mut self, name: &str, mut layer: Layer<'c, E>) {
        let ops = layer.take_ops();
        let block = self.block(name).unwrap();
        for op in ops {
            block.append_operation(op);
        }
    }

    pub fn push_block(
        &mut self,
        context: &'c Context,
        name: &str,
        params: Vec<ParameterNode<E>>,
        expr: AstNode<E>,
        d: &Diagnostics,
    ) {
        self.layers
            .last_mut()
            .unwrap()
            .push_block(context, name, params, expr, d);
    }

    pub fn build_layers(&mut self) -> HashMap<Index, Layer<'c, E>> {
        self.last_mut().build();
        let s = self.last_mut().dfs_first();

        let mut items = HashMap::new();
        // create layers with appropriate scoped variables
        let mut out = vec![];
        for (index, dominants) in s {
            // for each block, we want to push valid arguments into the layer based on the graph
            // there will be duplicates in each block, because we need to make visible all
            // variables in it's dominants
            //
            // create a layer and add all of the dominant parameters
            println!("push {:?}", index);
            let mut layer: Layer<E> = Layer::new(LayerType::Block);

            for d_index in dominants.iter() {
                let params = self.last().get_params(*d_index);
                // create a new layer, adding arguments as scoped variables
                for (offset, a) in params.iter().enumerate() {
                    let arg = LayerIndex::BlockArg(d_index.get(), offset);
                    layer.name_index(arg.clone(), &a.name);
                    layer.index.insert(arg.clone(), 0);
                    out.push((arg, a.ty.clone()));
                    //let data = Data::new(a.ty.clone());
                    //self.index_data(&arg, a.ty);

                    // record argument offset
                    println!("p: {:?}", (index, d_index, offset, &a.name, &a.ty));
                }
            }
            items.insert(index, layer);
        }

        for (arg, ty) in out {
            self.index_data(&arg, ty);
        }

        items
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast;
    use crate::ast::{Extra, SimpleExtra};
    //use crate::lower::FileDB;
    use crate::lower::Lower;
    use crate::{Diagnostics, Environment, NodeBuilder};
    use melior::dialect::{arith, func};
    use melior::ir::attribute::{StringAttribute, TypeAttribute};
    use melior::ir::r#type::FunctionType;
    use melior::ir::{Location, Type};
    use melior::{
        dialect::DialectRegistry,
        utility::{register_all_dialects, register_all_llvm_translations},
        Context,
    };
    use test_log::test;

    fn assert_op_index<E: Extra>(s: &Environment<E>, name: &str, index: LayerIndex) {
        assert_eq!(s.index_from_name(name).unwrap(), index);
    }

    type Node = ast::AstNode<ast::SimpleExtra>;

    fn test_context() -> Context {
        let context = Context::new();
        context.set_allow_unregistered_dialects(true);

        let registry = DialectRegistry::new();
        register_all_dialects(&registry);
        context.append_dialect_registry(&registry);
        context.load_all_available_dialects();
        register_all_llvm_translations(&context);
        context
    }

    #[test]
    fn test_scope1() {
        let context = test_context();
        let lower: Lower<SimpleExtra> = Lower::new(&context);
        let mut d = Diagnostics::new();
        let file_id = d.add_source("test.py".into(), "test".into());
        let mut s = Environment::default();
        s.enter_static();
        let location = Location::unknown(&context);

        // 3 ops in static context
        let b = NodeBuilder::new(file_id, "test.py");
        let expr = b.bool(false);
        let ast = b.global("x", expr);
        lower.lower_expr(ast, &mut s, &mut d, &b).unwrap();

        let expr = b.bool(false);
        let ast = b.global("x", expr);
        lower.lower_expr(ast, &mut s, &mut d, &b).unwrap();
        let g_index_x = s.last_index().unwrap();

        let expr = b.bool(true);
        let ast = b.global("y", expr);
        lower.lower_expr(ast, &mut s, &mut d, &b).unwrap();
        let g_index_y = s.last_index().unwrap();

        // ensure x is shadowed
        let index_x2 = s.index_from_name("x").unwrap();
        assert_eq!(g_index_x, index_x2);

        // ensure y
        let index_y2 = s.index_from_name("y").unwrap();
        assert_eq!(g_index_y, index_y2);

        // enter function context
        s.enter_func();

        // push y, should shadow static context
        let expr = b.bool(true);
        let ast = b.assign("y", expr);
        lower.lower_expr(ast, &mut s, &mut d, &b).unwrap();
        let y_index = s.last_index().unwrap();
        assert_op_index(&s, "y", y_index);

        // push x, should shadow static context
        let expr = b.bool(false);
        let ast = b.assign("x", expr);
        lower.lower_expr(ast, &mut s, &mut d, &b).unwrap();
        let x_index = s.last_index().unwrap();
        assert_op_index(&s, "x", x_index);

        // enter closed context
        s.enter_closed();

        // push x in a closed context
        let op = lower.build_bool_op(false, location);
        let index = s.push_with_name(op, "x");
        assert_op_index(&s, "x", index);

        // push z in a closed context
        let op = lower.build_bool_op(false, location);
        let index = s.push_with_name(op, "z");
        assert_op_index(&s, "z", index);

        // check z existence in closed
        assert_eq!(s.last_index().unwrap(), s.index_from_name("z").unwrap());

        // exit closed
        let layer = s.exit();
        //s.merge(layer);

        // exit func
        let layer = s.exit();
        //s.merge(layer);

        // check that previous block is no longer visible
        // but we should have all of the ops

        s.dump();
        assert_op_index(&s, "y", g_index_y);
        assert_op_index(&s, "x", g_index_x);

        // z is not visible, out of scope
        assert!(s.index_from_name("z").is_none());
        s.exit();
        assert_eq!(0, s.layer_count());
    }

    fn test_int<'c, E: Extra>(
        lower: &Lower<'c, E>,
        scope: &mut Environment<'c, E>,
        location: Location<'c>,
        v: i64,
    ) -> LayerIndex {
        let op = lower.build_int_op(v, location);
        scope.push(op)
    }

    fn test_int_name<'c, E: Extra>(
        lower: &Lower<'c, E>,
        scope: &mut Environment<'c, E>,
        location: Location<'c>,
        v: i64,
        name: &str,
    ) -> LayerIndex {
        let op = lower.build_int_op(v, location);
        scope.push_with_name(op, name)
    }

    fn test_add<'c, E: Extra>(
        scope: &mut Environment<'c, E>,
        location: Location<'c>,
        a: LayerIndex,
        b: LayerIndex,
    ) -> LayerIndex {
        scope.push(arith::addi(scope.value0(&a), scope.value0(&b), location))
    }

    fn test_fill<'c, E: Extra>(
        lower: &Lower<'c, E>,
        scope: &mut Environment<'c, E>,
        location: Location<'c>,
    ) {
        let x = test_int_name(lower, scope, location, 1, "x");
        let y = test_add(scope, location, x.clone(), x.clone());

        let one = lower.build_int_op(1, location);
        let two = lower.build_int_op(2, location);
        let r_x = scope.push_with_name(one, "x");
        scope.push_with_name(two, "y");

        let op1 = lower.build_int_op(100, location);
        let r_op1 = scope.push(op1);

        let rx = scope.value0(&r_x);
        let ry = scope.value0_from_name("y");
        let op2 = arith::addi(rx, ry, location);
        scope.push(op2);

        let a = lower.build_int_op(1, location);
        let b = lower.build_int_op(2, location);
        let r_a = scope.push(a);
        let r_b = scope.push(b);
        let r_c = test_add(scope, location, r_a, r_b);
        let r_d = test_add(scope, location, x, y);
        let r_e = test_add(scope, location, r_c, r_d);

        let r = test_add(scope, location, r_op1, r_e);
        let rz = scope.index_from_name("z").unwrap();
        let r = test_add(scope, location, rz, r);
        //let p0 = scope.index_from_name("p0").unwrap();
        //let r = test_add(scope, location, r, p0);
        scope.name_index(r, "result");

        let ret = func::r#return(&scope.values_from_name("result"), location);
        scope.push(ret);
    }

    fn test_env3<'c, E: Extra>(
        lower: &Lower<'c, E>,
        env: &mut Environment<'c, E>,
        location: Location<'c>,
    ) {
        let index_type = Type::index(lower.context);
        let types = vec![index_type];
        let ret_type = vec![index_type];
        let func_type = FunctionType::new(&lower.context, &types, &ret_type);

        let mut layer = Layer::new(LayerType::Block);
        layer.enter_block("test", Block::new(&[]));
        env.enter(layer);

        let three = lower.build_int_op(3, location);
        env.push_with_name(three, "z");
        test_fill(lower, env, location);
        let mut layer = env.exit();

        // append ops
        let block = layer.blocks.pop().unwrap();
        for op in layer.ops {
            block.append_operation(op);
        }

        // build region
        let region = Region::new();
        region.append_block(block);

        // build function
        let f = func::func(
            &lower.context,
            StringAttribute::new(&lower.context, "test"),
            TypeAttribute::new(func_type.into()),
            region,
            &[(
                Identifier::new(&lower.context, "sym_visibility"),
                StringAttribute::new(&lower.context, "private").into(),
            )],
            location,
        );

        // push result
        env.push(f);
    }

    #[test]
    fn test_scope3() {
        let context = test_context();
        //let mut files = FileDB::new();
        let lower: Lower<SimpleExtra> = Lower::new(&context);
        //let file_id = lower.add_source("test.py".into(), "test".into());
        let location = Location::unknown(&context);
        let mut env = ScopeStack::default();
        env.enter_static();
        test_env3(&lower, &mut env, location);
        println!("layer: {:?}", env);
        env.exit();
        assert_eq!(0, env.layer_count());
    }
}
