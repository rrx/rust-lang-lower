use petgraph::graph::DiGraph;
use petgraph::graph::NodeIndex;

use crate::{
    scope::LoopScope, BlockId, LinkId, NodeBuilder, ScopeId, ScopeLayer, ScopeType, StringLabel,
    VariantId,
};
use compile_core::{AstType, StringKey};
use std::ops::{Deref, DerefMut};
