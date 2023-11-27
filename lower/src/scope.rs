use im::OrdMap;
use melior::ir::*;
use melior::ir::{Operation, Value};
use std::collections::HashMap;

#[derive(Debug, PartialEq)]
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum LayerIndex {
    Op(usize),
    Argument(usize),
}
impl LayerIndex {
    pub fn op(index: OpIndex) -> Self {
        Self::Op(index.0)
    }

    pub fn arg(index: usize) -> Self {
        Self::Argument(index)
    }
}

#[derive(Debug)]
pub struct Layer<'c> {
    ty: LayerType,
    pub(crate) ops: Vec<Operation<'c>>,
    args_count: usize,
    names: HashMap<String, LayerIndex>,
    index: HashMap<LayerIndex, usize>,
    pub(crate) block: Option<Block<'c>>,
    last_index: Option<LayerIndex>,
}

impl<'c> Layer<'c> {
    pub fn new(ty: LayerType) -> Self {
        Self {
            ty,
            ops: vec![],
            args_count: 0,
            names: HashMap::new(),
            index: HashMap::new(),
            block: None,
            last_index: None,
        }
    }
    pub fn merge(&mut self, mut layer: Layer<'c>) {
        //let start = self.ops.len();

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
        self.last_index = layer.last_index;
    }

    pub fn name_index(&mut self, index: LayerIndex, name: &str) {
        self.names.insert(name.to_string(), index);
    }

    pub fn push(&mut self, op: Operation<'c>, index: LayerIndex) {
        let pos = self.ops.len();
        self.ops.push(op);
        self.index.insert(index, pos);
        self.last_index = Some(index);
    }

    pub fn push_with_name(&mut self, op: Operation<'c>, index: LayerIndex, name: &str) {
        self.push(op, index);
        self.names.insert(name.to_string(), index);
        self.last_index = Some(index);
    }

    pub fn last_index(&self) -> OpIndex {
        OpIndex(self.ops.len())
    }

    pub fn value_from_name(&self, name: &str) -> Vec<Value<'c, '_>> {
        match self.names.get(name) {
            Some(index) => {
                let offset = self.index.get(index).unwrap();
                match index {
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
                }
            }
            _ => vec![],
        }
    }

    pub fn index_from_name(&self, name: &str) -> Option<LayerIndex> {
        self.names.get(name).cloned()
    }

    pub fn values(&self, index: LayerIndex) -> Vec<Value<'c, '_>> {
        if let Some(offset) = self.index.get(&index) {
            return match index {
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
            };
        }
        vec![]
    }

    pub fn take_ops(&mut self) -> Vec<Operation<'c>> {
        self.names.clear();
        self.ops.drain(..).collect()
    }
}

#[derive(Debug)]
pub struct ScopeStack<'c> {
    arg_count: usize,
    op_count: usize,
    layers: Vec<Layer<'c>>,
}

impl<'c> Default for ScopeStack<'c> {
    fn default() -> Self {
        let layer = Layer::new(LayerType::Static);
        Self {
            arg_count: 0,
            op_count: 0,
            layers: vec![layer],
        }
    }
}

impl<'c> ScopeStack<'c> {
    pub fn fresh_argument(&mut self) -> LayerIndex {
        let index = LayerIndex::Argument(self.arg_count);
        self.arg_count += 1;
        index
    }

    pub fn fresh_op(&mut self) -> LayerIndex {
        let index = LayerIndex::Op(self.op_count);
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

    pub fn enter_block(&mut self, arguments: &[(Type<'c>, Location<'c>, &str)]) {
        let mut layer = Layer::new(LayerType::Block);
        layer.args_count = arguments.len();
        for (i, a) in arguments.iter().enumerate() {
            let index = LayerIndex::Argument(self.arg_count);
            self.arg_count += 1;
            layer.names.insert(a.2.to_string(), index);
            layer.index.insert(index, i);
        }
        let block_args = arguments.iter().map(|a| (a.0, a.1)).collect::<Vec<_>>();
        let block = Block::new(&block_args);
        layer.block = Some(block);
        self.enter(layer);
    }

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

    pub fn name_index(&mut self, index: LayerIndex, name: &str) {
        self.last_mut().name_index(index, name);
    }

    pub fn push(&mut self, op: Operation<'c>) -> LayerIndex {
        let index = self.fresh_op();
        self.last_mut().push(op, index);
        index
    }

    pub fn push_with_name(&mut self, op: Operation<'c>, name: &str) -> LayerIndex {
        let index = self.fresh_op();
        self.last_mut().push_with_name(op, index, name);
        index
    }

    pub fn last_index(&self) -> Option<LayerIndex> {
        self.layers.last().map(|x| x.last_index.unwrap())
    }

    pub fn value_from_name(&self, name: &str) -> Vec<Value<'c, '_>> {
        for layer in self.layers.iter().rev() {
            let r = layer.value_from_name(name);
            if r.len() > 0 {
                return r;
            }
        }
        vec![]
    }

    pub fn values(&self, index: LayerIndex) -> Vec<Value<'c, '_>> {
        for layer in self.layers.iter().rev() {
            let result = layer.values(index);
            if result.len() > 0 {
                return result;
            }
        }
        vec![]
    }

    pub fn last_values(&self) -> Vec<Value<'c, '_>> {
        self.values(self.last_index().unwrap())
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
    //use test_log::test;
    use crate::lower::tests::test_context;
    use crate::lower::FileDB;
    use crate::lower::Lower;
    use melior::dialect::{arith, func, memref};
    use melior::ir::{
        attribute::{StringAttribute, TypeAttribute},
        operation::{OperationRef, OperationResult},
        r#type::{FunctionType, MemRefType},
        *,
    };
    use melior::ir::{Location, Type};
    use melior::Context;

    fn assert_op_index(s: &ScopeStack, name: &str, index: LayerIndex) {
        assert_eq!(s.index_from_name(name).unwrap(), index);
    }

    #[test]
    fn test_scope1() {
        let context = test_context();
        let files = FileDB::new();
        //let file_id = files.add("test.py".into(), "test".into());
        let lower = Lower::new(&context, &files);
        let mut s = ScopeStack::default();
        let location = Location::unknown(&context);

        // 3 ops in static context
        let op = lower.build_bool_op(false, location);
        s.push_with_name(op, "x");
        let op = lower.build_bool_op(true, location);
        let x_index = s.push_with_name(op, "x");
        // ensure x is shadowed
        assert_op_index(&s, "x", x_index);

        let op = lower.build_bool_op(true, location);
        let y_index = s.push_with_name(op, "y");
        assert_eq!(s.last_index().unwrap(), y_index);
        assert_op_index(&s, "y", y_index);

        let rs = s.value_from_name("x");
        assert!(rs.len() > 0);

        // ensure y
        let rs = s.value_from_name("y");
        assert!(rs.len() > 0);

        // enter function context
        s.enter_func();

        // push y, should shadow static context
        let op = lower.build_bool_op(true, location);
        let index = s.push_with_name(op, "y");
        assert_op_index(&s, "y", index);

        // push x, should shadow static context
        let op = lower.build_bool_op(false, location);
        let index = s.push_with_name(op, "x");
        assert_op_index(&s, "x", index);

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

        //println!("s: {:?}", s);
        //assert_eq!(s.last_index(), 5.into());

        println!("s2: {:?}", s);
        assert_eq!(s.last_index().unwrap(), s.index_from_name("z").unwrap());

        println!("s1: {:?}", s);
        let layer = s.exit();
        s.merge(layer);
        let layer = s.exit();
        s.merge(layer);

        // check that previous block is no longer visible
        // but we should have all of the ops

        assert_op_index(&s, "y", y_index);
        assert_op_index(&s, "x", x_index);
        let rs = s.value_from_name("y");
        assert!(rs.len() > 0);

        assert!(s.index_from_name("z").is_none());
    }

    fn test_int<'c>(
        lower: &'c Lower,
        scope: &mut ScopeStack<'c>,
        location: Location<'c>,
        v: i64,
    ) -> LayerIndex {
        let op = lower.build_int_op(v, location);
        scope.push(op)
    }

    fn test_int_name<'c>(
        lower: &'c Lower,
        scope: &mut ScopeStack<'c>,
        location: Location<'c>,
        v: i64,
        name: &str,
    ) -> LayerIndex {
        let op = lower.build_int_op(v, location);
        scope.push_with_name(op, name)
    }

    fn test_add<'c>(
        scope: &mut ScopeStack<'c>,
        location: Location<'c>,
        a: LayerIndex,
        b: LayerIndex,
    ) -> LayerIndex {
        scope.push(arith::addi(
            scope.values(a)[0],
            scope.values(b)[0],
            location,
        ))
    }

    fn test_fill<'c>(lower: &'c Lower, scope: &mut ScopeStack<'c>, location: Location<'c>) {
        let x = test_int_name(lower, scope, location, 1, "x");
        let y = test_add(scope, location, x, x);

        let one = lower.build_int_op(1, location);
        let two = lower.build_int_op(2, location);
        let r_x = scope.push_with_name(one, "x");
        scope.push_with_name(two, "y");

        let op1 = lower.build_int_op(100, location);
        let r_op1 = scope.push(op1);

        let rx = scope.values(r_x)[0];
        let ry = scope.value_from_name("y")[0];
        let op2 = arith::addi(rx, ry, location);
        println!("r: {:?}", rx);
        println!("r: {:?}", ry);
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
        let p0 = scope.index_from_name("p0").unwrap();
        let r = test_add(scope, location, r, p0);
        scope.name_index(r, "result");

        let ret = func::r#return(&scope.value_from_name("result"), location);
        scope.push(ret);
    }

    fn test_env3<'c>(lower: &'c Lower, env: &mut ScopeStack<'c>, location: Location<'c>) {
        let index_type = Type::index(lower.context);
        let types = vec![index_type];
        let ret_type = vec![index_type];
        let func_type = FunctionType::new(&lower.context, &types, &ret_type);

        env.enter_block(&[(index_type, location, "p0")]);
        assert_eq!(env.index_from_name("p0").unwrap(), LayerIndex::Argument(0));

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
        let _file_id = files.add("test.py".into(), "test".into());
        let location = Location::unknown(&context);
        //let ast = crate::lower::tests::gen_test(file_id);
        let lower = Lower::new(&context, &files);
        let mut env = ScopeStack::default();
        test_env3(&lower, &mut env, location);
        println!("layer: {:?}", env);
    }
}
