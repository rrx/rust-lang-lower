use melior::ir::*;
use melior::ir::{Operation, Value};
use std::collections::HashMap;

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum LayerType {
    Static,
    Function,
    Block,
    Closed,
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
    Argument(usize),
    //Ref(usize),
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
pub struct Layer<'c> {
    ty: LayerType,
    pub(crate) ops: Vec<Operation<'c>>,
    pub(crate) names: HashMap<String, LayerIndex>,
    pub(crate) index: HashMap<LayerIndex, usize>,
    pub(crate) block: Option<Block<'c>>,
    _last_index: Option<LayerIndex>,
}

impl<'c> Layer<'c> {
    pub fn new(ty: LayerType) -> Self {
        Self {
            ty,
            ops: vec![],
            names: HashMap::new(),
            index: HashMap::new(),
            block: None,
            _last_index: None,
        }
    }

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
        match self.names.get(name) {
            Some(index) => {
                let offset = self.index.get(index).unwrap();
                Some(match index {
                    LayerIndex::Static(_) => vec![],
                    //LayerIndex::Ref(source_index) => {
                    //return self.values(source_index);
                    //unreachable!();
                    //}
                    LayerIndex::Op(_) => self
                        .ops
                        .get(*offset)
                        .unwrap()
                        .results()
                        .map(|x| x.into())
                        .collect(),
                    LayerIndex::Argument(_) => {
                        vec![self
                            .block
                            .as_ref()
                            .unwrap()
                            .argument(*offset)
                            .unwrap()
                            .into()]
                    }
                })
            }
            _ => None,
        }
    }

    pub fn index_from_name(&self, name: &str) -> Option<LayerIndex> {
        self.names.get(name).cloned()
    }

    pub fn values(&self, index: &LayerIndex) -> Option<Vec<Value<'c, '_>>> {
        if let Some(offset) = self.index.get(&index) {
            //println!("found: {:?} - {}, {:?}", index, offset, self.ops.len()); //self.ops.get(*offset).unwrap().results().collect::<Vec<_>>());
            return Some(match index {
                //LayerIndex::Static(_) => vec![],
                LayerIndex::Op(_) => self
                    .ops
                    .get(*offset)
                    .unwrap()
                    .results()
                    .map(|x| x.into())
                    .collect(),
                LayerIndex::Argument(_) => vec![self
                    .block
                    .as_ref()
                    .unwrap()
                    .argument(*offset)
                    .unwrap()
                    .into()],
                _ => unimplemented!("{:?}", index),
            });
        }
        None
    }

    /*
    pub fn values2(&self, index: &LayerIndex) -> Option<Vec<Value<'c, '_>>> {
        log::debug!("self: {:?}", self);
        let v = if let LayerIndex::Ref(op_index) = index {
            return self.values(&LayerIndex::Op(*op_index));
            //if let Some(offset) = self.index.get(&LayerIndex::Op(*op_index)) {
            //Some((offset, &LayerIndex::Op(0)))
            //} else {
            //None
            //}
        } else if let Some(offset) = self.index.get(&index) {
            Some((offset, index))
        } else {
            None
        };

        if let Some((offset, index)) = v {
            println!("found: {:?} - {}, {:?}", index, offset, self.ops.len()); //self.ops.get(*offset).unwrap().results().collect::<Vec<_>>());
            return Some(match index {
                //LayerIndex::Static(_) => vec![],
                LayerIndex::Op(_) => self
                    .ops
                    .get(*offset)
                    .unwrap()
                    .results()
                    .map(|x| x.into())
                    .collect(),
                LayerIndex::Argument(_) => vec![self
                    .block
                    .as_ref()
                    .unwrap()
                    .argument(*offset)
                    .unwrap()
                    .into()],
                _ => unimplemented!("{:?}", index),
            });
        }
        None
    }
    */

    pub fn push_index(&mut self, index: LayerIndex) {
        self._last_index = Some(index);
    }

    pub fn take_ops(&mut self) -> Vec<Operation<'c>> {
        self.names.clear();
        self.ops.drain(..).collect()
    }
}

#[derive(Debug)]
pub struct ScopeStack<'c, D> {
    op_count: usize,
    static_count: usize,
    layers: Vec<Layer<'c>>,
    types: HashMap<LayerIndex, D>,
}

impl<'c, D> Default for ScopeStack<'c, D> {
    fn default() -> Self {
        let layer = Layer::new(LayerType::Static);
        Self {
            op_count: 0,
            static_count: 0,
            layers: vec![layer],
            types: HashMap::new(),
        }
    }
}

impl<'c, D: std::fmt::Debug + Clone> ScopeStack<'c, D> {
    pub fn dump(&self) {
        println!("env: {:?}", self);
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
        }
    }

    pub fn index_data(&mut self, index: &LayerIndex, data: D) {
        self.types.insert(index.clone(), data);
    }

    pub fn data(&self, index: &LayerIndex) -> Option<&D> {
        self.types.get(index)
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

    /*
    pub fn enter_block(&mut self, arguments: &[(Type<'c>, Location<'c>, String)]) {
        let mut layer = Layer::new(LayerType::Block);
        //layer.args_count = arguments.len();
        for (i, a) in arguments.iter().enumerate() {
            let index = self.fresh_argument();
            layer.name_index(index, &a.2);
            //let data = crate::lower::Data::new(a.3);
            //layer.names.insert(a.2.to_string(), index);
            //layer.index.insert(index, i);
        }
        let block_args = arguments.iter().map(|a| (a.0, a.1)).collect::<Vec<_>>();
        let block = Block::new(&block_args);
        layer.block = Some(block);
        self.enter(layer);
    }
    */

    pub fn enter(&mut self, layer: Layer<'c>) {
        self.layers.push(layer);
    }

    pub fn exit(&mut self) -> Layer<'c> {
        let layer = self.layers.pop().unwrap();
        //self.merge(layer);
        layer
    }

    pub fn merge(&mut self, layer: Layer<'c>) {
        if let Some(last) = self.layers.last_mut() {
            last.merge(layer);
        } else {
            unreachable!()
        }
    }

    pub fn last_mut(&mut self) -> &mut Layer<'c> {
        if let Some(last) = self.layers.last_mut() {
            last
        } else {
            unreachable!()
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
        for layer in self.layers.iter().rev() {
            if let Some(result) = layer.values(&index) {
                return result[0];
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast;
    use crate::ast::{Extra, SimpleExtra};
    use crate::lower::FileDB;
    use crate::lower::Lower;
    use crate::{Environment, NodeBuilder};
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

    fn assert_op_index(s: &Environment, name: &str, index: LayerIndex) {
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
        let mut files = FileDB::new();
        let mut lower: Lower<SimpleExtra> = Lower::new(&context);
        let file_id = lower.add_source("test.py".into(), "test".into());
        let mut s = Environment::default();
        let location = Location::unknown(&context);

        // 3 ops in static context
        let mut b = NodeBuilder::new();
        b.enter_file(file_id, "test.py");
        let expr = b.bool(false);
        let ast = b.global("x", expr);
        lower.lower_expr(ast, &mut s);

        let expr = b.bool(false);
        let ast = b.global("x", expr);
        lower.lower_expr(ast, &mut s);
        let g_index_x = s.last_index().unwrap();

        let expr = b.bool(true);
        let ast = b.global("y", expr);
        lower.lower_expr(ast, &mut s);
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
        lower.lower_expr(ast, &mut s);
        let y_index = s.last_index().unwrap();
        assert_op_index(&s, "y", y_index);

        // push x, should shadow static context
        let expr = b.bool(false);
        let ast = b.assign("x", expr);
        lower.lower_expr(ast, &mut s);
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
        s.merge(layer);

        // exit func
        let layer = s.exit();
        s.merge(layer);

        // check that previous block is no longer visible
        // but we should have all of the ops

        s.dump();
        assert_op_index(&s, "y", g_index_y);
        assert_op_index(&s, "x", g_index_x);

        // z is not visible, out of scope
        assert!(s.index_from_name("z").is_none());
    }

    fn test_int<'c, E: Extra>(
        lower: &Lower<'c, E>,
        scope: &mut Environment<'c>,
        location: Location<'c>,
        v: i64,
    ) -> LayerIndex {
        let op = lower.build_int_op(v, location);
        scope.push(op)
    }

    fn test_int_name<'c, E: Extra>(
        lower: &Lower<'c, E>,
        scope: &mut Environment<'c>,
        location: Location<'c>,
        v: i64,
        name: &str,
    ) -> LayerIndex {
        let op = lower.build_int_op(v, location);
        scope.push_with_name(op, name)
    }

    fn test_add<'c>(
        scope: &mut Environment<'c>,
        location: Location<'c>,
        a: LayerIndex,
        b: LayerIndex,
    ) -> LayerIndex {
        scope.push(arith::addi(scope.value0(&a), scope.value0(&b), location))
    }

    fn test_fill<'c, E: Extra>(
        lower: &Lower<'c, E>,
        scope: &mut Environment<'c>,
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
        env: &mut Environment<'c>,
        location: Location<'c>,
    ) {
        let index_type = Type::index(lower.context);
        let types = vec![index_type];
        let ret_type = vec![index_type];
        let func_type = FunctionType::new(&lower.context, &types, &ret_type);

        let mut layer = Layer::new(LayerType::Block);
        layer.block = Some(Block::new(&[]));
        env.enter(layer);

        let three = lower.build_int_op(3, location);
        env.push_with_name(three, "z");
        test_fill(lower, env, location);
        let mut layer = env.exit();

        // append ops
        let block = layer.block.take().unwrap();
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
        let mut files = FileDB::new();
        let mut lower: Lower<SimpleExtra> = Lower::new(&context);
        let file_id = lower.add_source("test.py".into(), "test".into());
        let location = Location::unknown(&context);
        let mut env = ScopeStack::default();
        test_env3(&lower, &mut env, location);
        println!("layer: {:?}", env);
    }
}
