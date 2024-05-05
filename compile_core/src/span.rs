#[derive(Debug, Clone, Copy)]
pub struct SpanId(u32);
impl SpanId {
    pub fn new(v: u32) -> Self {
        Self(v)
    }

    pub fn index(&self) -> usize {
        self.0 as usize
    }
}
