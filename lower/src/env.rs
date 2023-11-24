use log::debug;
use std::fmt;
use std::hash::Hash;

pub trait LayerKey: Hash + Eq + fmt::Debug + fmt::Display + Clone {}
pub trait LayerValue: fmt::Debug + fmt::Display + Clone {}

impl LayerValue for usize {}
impl LayerKey for String {}

#[derive(Clone, PartialEq)]
pub struct Layer<K: LayerKey, V> {
    values: im::HashMap<K, V>,
}

impl<K: LayerKey, V> Default for Layer<K, V> {
    fn default() -> Self {
        Self {
            values: im::HashMap::new(),
        }
    }
}

impl<K: LayerKey, V: LayerValue> fmt::Debug for Layer<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map()
            .entries(self.values.iter().map(|(k, v)| (k, v)))
            .finish()
    }
}

impl<K: LayerKey, V: LayerValue> Layer<K, V> {
    pub fn define(mut self, name: K, value: V) -> Layer<K, V> {
        self.values.insert(name, value);
        self
        //Layer {
        //values: self.values.insert(name, value),
        //}
    }

    pub fn contains(&self, name: &K) -> bool {
        self.values.contains_key(name)
    }

    pub fn get(&self, name: &K) -> Option<V> {
        match self.values.get(name) {
            Some(v) => Some(v.clone()),
            None => None,
        }
    }
}

pub struct EnvLayersIterator<'a, K, V> {
    values: Vec<(&'a K, &'a V)>,
}

impl<'a, K, V> Iterator for EnvLayersIterator<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        self.values.pop()
    }
}

#[derive(Clone, PartialEq)]
pub struct EnvLayers<K: LayerKey, V: LayerValue> {
    enclosing: Option<Box<EnvLayers<K, V>>>,
    layers: im::vector::Vector<Layer<K, V>>,
}

impl<K: LayerKey, V: LayerValue> Default for EnvLayers<K, V> {
    fn default() -> Self {
        let mut layers = im::Vector::new();
        let layer = Layer::default();
        layers.push_front(layer);
        Self {
            layers,
            enclosing: None,
        }
    }
}

impl<K: LayerKey, V: LayerValue> fmt::Debug for EnvLayers<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map()
            .entries(self.iter().map(|(k, v)| (k, v)))
            .finish()
    }
}

impl<K: LayerKey, V: LayerValue> EnvLayers<K, V> {
    pub fn iter<'a>(&'a self) -> EnvLayersIterator<'a, K, V> {
        let mut values = vec![];
        for layer in &self.layers {
            for (k, v) in layer.values.iter() {
                values.push((k, v));
            }
        }
        EnvLayersIterator { values }
    }

    pub fn push(&mut self) {
        let enclosing = Some(Box::new(self.clone()));
        let layers = im::Vector::new();
        self.enclosing = enclosing;
        self.layers = layers;
    }

    pub fn pop(&mut self) {
        let orig = self.enclosing.take().unwrap();
        self.enclosing = orig.enclosing;
        self.layers = orig.layers;
    }

    pub fn define(&mut self, name: K, value: V) {
        if self.layers.len() > 0 && self.layers.front().unwrap().contains(&name) {
            let layer = Layer::default().define(name, value);
            self.layers.push_front(layer);
        } else {
            match self.layers.pop_front() {
                Some(layer) => {
                    let layer = layer.define(name, value);
                    self.layers.push_front(layer);
                }
                None => {
                    let layer = Layer::default().define(name, value);
                    self.layers.push_front(layer);
                }
            }
        }
    }

    pub fn resolve(&self, name: &K) -> Option<V> {
        self.layers
            .iter()
            .find(|layer| layer.values.contains_key(name))
            .map(|layer| layer.get(name).clone())
            .flatten()
    }

    pub fn resolve_all(&self, name: &K) -> Vec<V> {
        self.layers
            .iter()
            .filter(|layer| layer.values.contains_key(name))
            .map(|layer| layer.get(name).unwrap())
            .collect()
    }

    pub fn debug(&self) {
        self.layers.iter().enumerate().for_each(|(i, layer)| {
            debug!("Layer: {:?}", i);
            layer.values.iter().for_each(|(k, v)| {
                debug!("\t{:?}: {:?}", k, v);
            });
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    //use test_log::test;
    pub type Environment = EnvLayers<String, usize>;

    #[test]
    fn lexical_scope() {
        let v_id = 0;
        let mut env = Environment::default();
        env.define("asdf".into(), v_id);

        env.define("Asdf".into(), 1);
        assert_eq!(Some(1), env.resolve(&"Asdf".into()));
        env.define("Asdf".into(), 2);
        assert_eq!(Some(2), env.resolve(&"Asdf".into()));

        let all_asdf = env.resolve_all(&"Asdf".to_string());
        assert_eq!(all_asdf.len(), 2);

        let env1 = env.clone();
        let env2 = env1.clone();
        assert_eq!(env1, env2);

        let mut env3 = env2.clone();
        env3.define("Asdf2".into(), 1);
        assert!(env1 != env3);

        assert_eq!(Some(1), env3.resolve(&"Asdf2".into()));
        assert_eq!(None, env.resolve(&"Asdf2".into()));
        assert_eq!(None, env2.resolve(&"Asdf2".into()));
    }

    #[test]
    fn push_pop() {
        let mut env = Environment::default();
        env.push();
        env.define(String::from("asdf"), 0);
        assert_eq!(Some(0), env.resolve(&"asdf".into()));
        env.pop();
        assert_eq!(None, env.resolve(&"asdf".into()));
    }
}
