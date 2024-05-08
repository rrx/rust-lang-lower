pub mod ast;
pub mod compile;
pub mod link;
//pub mod op;

pub use compile::{default_context, default_pass_manager};
pub use link::LinkOptions;

// re-export melior structs
pub use melior;
pub use melior::{
    ir::operation::OperationPrintingFlags,
    ir::{Location, Module},
    Context,
};

pub use petgraph::graph::NodeIndex;
