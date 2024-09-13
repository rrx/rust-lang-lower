//use compile_core::AstType;
use serde::Serialize;
use tabled::Tabled;

#[derive(Tabled, Serialize)]
pub struct CodeRow {
    pub pos: usize,
    pub link: usize,
    //pub next: usize,
    //pub prev: usize,
    pub value: String,
    pub ty: String,
    pub mem: String,
    pub name: String,
    pub span_id: usize,
    pub scope_id: usize,
    pub block_id: usize,
    pub entry_id: usize,
    pub term: bool,
    pub dead: bool,
    pub unknown: bool,
}

impl CodeRow {
    pub fn header() -> Vec<&'static str> {
        vec![
            "pos", "link", "next", "prev", "value", "ty", "mem", "name", "span_id", "scope_id",
            "block_id", "term", "dead", "unknown",
        ]
    }
}
