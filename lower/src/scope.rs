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

#[derive(Debug)]
pub struct Layer<'c> {
    ty: LayerType,
    ops: Vec<Operation<'c>>,
    names: HashMap<String, OpIndex>,
}

impl<'c> Layer<'c> {
    pub fn merge(&mut self, mut layer: Layer<'c>) {
        let start = self.ops.len();

        let preserve_names = match layer.ty {
            LayerType::Closed | LayerType::Function | LayerType::Block => false,
            _ => true,
        };

        // optionally preserve names
        // overwrite existing names, thus shadowing
        if preserve_names {
            for (k, v) in layer.names {
                self.names.insert(k, OpIndex(v.0 + start));
            }
        }

        for op in layer.ops.drain(..) {
            self.ops.push(op);
        }
    }

    pub fn push(&mut self, op: Operation<'c>) {
        self.ops.push(op);
    }

    pub fn push_with_name(&mut self, op: Operation<'c>, name: &str) {
        let index = OpIndex(self.ops.len());
        self.ops.push(op);
        self.names.insert(name.to_string(), index);
    }

    pub fn last_index(&self) -> OpIndex {
        OpIndex(self.ops.len())
    }

    pub fn value_from_name(&self, name: &str) -> Vec<Value<'c, '_>> {
        if let Some(index) = self.names.get(name) {
            return self
                .ops
                .get(index.0)
                .unwrap()
                .results()
                .map(|x| x.into())
                .collect();
        }
        vec![]
    }

    pub fn index_from_name(&self, name: &str) -> Option<OpIndex> {
        self.names.get(name).cloned()
    }

    pub fn values(&self, index: OpIndex) -> Vec<Value<'c, '_>> {
        let index = index.0;
        self.ops[index].results().map(|x| x.into()).collect()
    }
}

#[derive(Debug)]
pub struct ScopeStack<'c> {
    statics: Layer<'c>,
    layers: Vec<Layer<'c>>,
}

impl<'c> Default for ScopeStack<'c> {
    fn default() -> Self {
        Self {
            statics: Layer {
                ty: LayerType::Static,
                ops: vec![],
                names: HashMap::new(),
            },
            layers: vec![],
        }
    }
}

impl<'c> ScopeStack<'c> {
    pub fn enter_closed(&mut self) {
        self.enter(LayerType::Closed);
    }
    pub fn enter_func(&mut self) {
        self.enter(LayerType::Closed);
    }
    pub fn enter_block(&mut self) {
        self.enter(LayerType::Block);
    }
    pub fn enter(&mut self, ty: LayerType) {
        self.layers.push(Layer {
            ty,
            ops: vec![],
            names: HashMap::new(),
        });
    }

    pub fn exit(&mut self) {
        let layer = self.layers.pop().unwrap();
        self.merge(layer);
    }

    pub fn merge(&mut self, layer: Layer<'c>) {
        if let Some(last) = self.layers.last_mut() {
            last.merge(layer);
        } else {
            self.statics.merge(layer);
        }
    }

    pub fn last_mut(&mut self) -> &mut Layer<'c> {
        if let Some(last) = self.layers.last_mut() {
            last
        } else {
            &mut self.statics
        }
    }

    pub fn push(&mut self, op: Operation<'c>) {
        self.last_mut().push(op);
    }

    pub fn push_with_name(&mut self, op: Operation<'c>, name: &str) {
        self.last_mut().push_with_name(op, name);
    }

    pub fn last_index(&self) -> OpIndex {
        let mut index = self.statics.ops.len();
        for layer in self.layers.iter() {
            index += layer.ops.len();
        }
        OpIndex(index - 1)
    }

    pub fn value_from_name(&self, name: &str) -> Vec<Value<'c, '_>> {
        for layer in self.layers.iter().rev() {
            println!("x: {:?}", self);
            if let Some(_) = layer.names.get(name) {
                return layer.value_from_name(name); //.ops.get(index.0).unwrap().results().map(|x| x.into()).collect();
            }
        }
        self.statics.value_from_name(name)
    }

    pub fn values(&self, index: OpIndex) -> Vec<Value<'c, '_>> {
        let mut index = index.0;
        if index < self.statics.ops.len() {
            self.statics.values(OpIndex(index))
        } else {
            index -= self.statics.ops.len();
            for layer in self.layers.iter() {
                if index < layer.ops.len() {
                    return layer.values(OpIndex(index));
                }
            }
            unreachable!()
        }
    }

    pub fn index_from_name(&self, name: &str) -> Option<OpIndex> {
        let mut exists = false;
        let mut result = 0;
        for layer in self.layers.iter().rev() {
            if exists {
                result += layer.ops.len();
            } else {
                if let Some(index) = layer.index_from_name(name) {
                    result = index.0;
                    exists = true;
                }
            }
        }

        if exists {
            result += self.statics.ops.len();
            Some(OpIndex(result))
        } else {
            if let Some(index) = self.statics.index_from_name(name) {
                Some(index)
            } else {
                None
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    //use test_log::test;
    //
    use crate::lower::tests::test_context;
    use crate::lower::FileDB;
    use crate::lower::Lower;
    use melior::ir::Location;

    #[test]
    fn test_scope() {
        let context = test_context();
        let mut files = FileDB::new();
        //let file_id = files.add("test.py".into(), "test".into());
        let lower = Lower::new(&context, &files);
        let mut s = ScopeStack::default();
        let location = Location::unknown(&context);
        let op = lower.build_bool_op(false, location);
        s.push_with_name(op, "x");
        let op = lower.build_bool_op(true, location);
        s.push_with_name(op, "x");
        let op = lower.build_bool_op(true, location);
        s.push_with_name(op, "y");
        assert_eq!(s.last_index(), 2.into());

        let rs = s.values(s.last_index());
        //println!("rs: {:?}", rs);

        let rs = s.value_from_name("x");
        //println!("rs: {:?}", rs);
        //println!("s: {:?}", s);
        assert!(rs.len() > 0);
        assert_eq!(s.index_from_name("x").unwrap(), 1.into());

        let rs = s.value_from_name("y");
        //println!("rs: {:?}", rs);
        assert!(rs.len() > 0);
        assert_eq!(s.index_from_name("y").unwrap(), 2.into());

        //println!("s: {:?}", s);

        s.enter_block();

        let op = lower.build_bool_op(true, location);
        s.push_with_name(op, "y");
        assert_eq!(s.last_index(), 3.into());
        assert_eq!(s.index_from_name("y").unwrap(), 3.into());

        let op = lower.build_bool_op(false, location);
        s.push_with_name(op, "x");
        assert_eq!(s.last_index(), 4.into());
        assert_eq!(s.index_from_name("x").unwrap(), 4.into());

        s.enter_closed();
        let op = lower.build_bool_op(false, location);
        s.push_with_name(op, "z");
        println!("s: {:?}", s);
        assert_eq!(s.last_index(), 5.into());
        assert_eq!(s.index_from_name("z").unwrap(), 5.into());
        assert_eq!(s.index_from_name("x").unwrap(), 4.into());
        let rs = s.value_from_name("z");
        assert!(rs.len() > 0);

        s.exit();
        s.exit();

        // check that previous block is no longer visible
        // but we should have all of the ops
        println!("s: {:?}", s);
        assert_eq!(s.last_index(), 5.into());
        assert_eq!(s.index_from_name("x").unwrap(), 1.into());
        assert!(s.index_from_name("z").is_none());
        let rs = s.value_from_name("y");
        assert!(rs.len() > 0);
    }
}
