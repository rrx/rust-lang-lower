//use crate::StringLabel;
use std::fmt::Debug;
use std::hash::Hash;

pub trait InternKey {
    fn index(&self) -> usize;
    fn new(index: usize) -> Self;
}

pub trait InternValue: Eq + PartialEq + Hash {}

#[derive(Debug)]
pub struct InternPool<K, V> {
    h: indexmap::IndexSet<V>,
    _k: std::marker::PhantomData<K>,
}

impl<K: InternKey, V: InternValue> InternPool<K, V> {
    pub fn new() -> Self {
        Self {
            h: indexmap::IndexSet::new(),
            _k: std::marker::PhantomData::default(),
        }
    }

    pub fn intern(&mut self, v: V) -> K {
        let offset = if let Some(offset) = self.h.get_index_of(&v) {
            K::new(offset)
        } else {
            let (offset, _) = self.h.insert_full(v);
            K::new(offset)
        };
        offset
    }

    pub fn resolve(&self, k: &K) -> &V {
        self.h.get_index(k.index()).unwrap()
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Copy, Hash, PartialOrd, Ord)]
pub struct StringKey(usize);
impl InternValue for String {}
impl InternKey for StringKey {
    fn index(&self) -> usize {
        self.0
    }
    fn new(index: usize) -> Self {
        Self(index)
    }
}
pub type StringPool = InternPool<StringKey, String>;
