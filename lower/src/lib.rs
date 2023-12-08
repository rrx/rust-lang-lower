pub mod ast;
pub mod builder;
pub mod code;
pub mod compile;
pub mod env;
pub mod lower;
pub mod scope;

pub use builder::NodeBuilder;
pub use lower::{FileDB, Lower};

// re-export melior structs
pub use melior::Context;

pub type Environment<'c> = scope::ScopeStack<'c, lower::Data>;
