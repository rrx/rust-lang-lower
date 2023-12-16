pub mod ast;
mod blocks;
pub mod builder;
pub mod cfg;
pub mod compile;
pub mod diagnostics;
pub mod env;
pub mod lower;
pub mod scope;

pub use builder::NodeBuilder;
pub use compile::{default_context, default_pass_manager};
pub use diagnostics::{Diagnostics, FileDB, ParseError};
pub use lower::Lower;

// re-export melior structs
pub use melior::Context;

pub type Environment<'c, E> = scope::ScopeStack<'c, E>;
