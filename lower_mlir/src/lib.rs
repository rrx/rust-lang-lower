pub mod compile;
mod mlir;

pub use compile::*;
pub use mlir::*;

pub use melior::{
    ir::operation::OperationPrintingFlags,
    ir::{Location, Module},
    Context,
};
