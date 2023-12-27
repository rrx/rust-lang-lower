use std::collections::HashSet;

#[derive(Default)]
pub struct LinkOptions {
    shared: HashSet<String>,
}

impl LinkOptions {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_library(&mut self, name: &str) {
        self.shared.insert(name.to_string());
    }

    pub fn shared_libraries(&self) -> Vec<String> {
        self.shared.iter().cloned().collect::<Vec<_>>()
    }
}
