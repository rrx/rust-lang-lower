use std::collections::VecDeque;
use thiserror::Error;

use compile_core::{
    AstType, BinaryOperation, BuiltinId, Literal, NaryOperation, SpanId, StringKey, UnaryOperation,
    VarDefinitionSpace,
};

use crate::{
    BlockId, CodeOffset, Environment, LinkId, Node, NodeBuilder, StringLabel, Successor, ValueId,
    CFG,
};

#[derive(Error, Debug)]
pub enum BlockifyError {
    #[error("BlockifyError: Invalid")]
    Invalid,
    #[error("BlockifyError: NotFound")]
    NotFound(String),
    #[error("BlockifyError: Template Not Found")]
    TemplateNotFound(String),
}

#[derive(Debug, Clone)]
pub enum UseIndex {
    Attr(StringKey),
    Pos(usize),
    Use(CodeOffset),
}

impl UseIndex {
    pub fn offset(self) -> CodeOffset {
        match self {
            Self::Use(offset) => offset,
            _ => unimplemented!(),
        }
    }
}

impl From<LinkId> for UseIndex {
    fn from(item: LinkId) -> Self {
        Self::Use(item.into())
    }
}

impl From<&LinkId> for UseIndex {
    fn from(item: &LinkId) -> Self {
        Self::Use(item.into())
    }
}

#[derive(Debug, Clone)]
pub struct UseIndexList(Vec<UseIndex>);
impl UseIndexList {
    pub fn new() -> Self {
        Self(vec![])
    }
    pub fn offset(self) -> CodeOffset {
        self.0.get(0).unwrap().clone().offset()
    }
}

impl From<LinkId> for UseIndexList {
    fn from(item: LinkId) -> Self {
        Self(vec![item.into()])
    }
}

impl From<&LinkId> for UseIndexList {
    fn from(item: &LinkId) -> Self {
        Self(vec![item.into()])
    }
}

#[derive(Debug, Clone)]
pub enum LCode {
    Label, // number of positional arguments, number of named arguments
    Noop,
    Declare,
    DeclareFunction(Option<BlockId>), // optional entry block
    DeclareTemplate(Option<BlockId>), // optional entry block
    Extern,                           // optional entry block
    //Value(LinkId),
    ValueIndex(LinkId, u8), // index into a struct
    CallValue(UseIndexList),
    Arg(u8), // get the value of a positional arg
    Val(Literal),
    Use(Vec<UseIndex>),
    Op1(UnaryOperation),
    Op2(BinaryOperation),
    NaryOp(NaryOperation),
    Load(LinkId),          // memref
    Store(LinkId, LinkId), // memref, value to store
    Return,                // return values
    Yield,                 // yield values

    // jump to block, with num args
    Jump(CodeOffset),

    Branch(CodeOffset, BlockId, BlockId),
    Ternary(CodeOffset, BlockId, BlockId), // condition, then_entry, else_entry
    Builtin(BuiltinId),
    Call(CodeOffset),
}

impl LCode {
    pub fn is_start(&self) -> bool {
        match self {
            Self::Label => true,
            _ => false,
        }
    }

    pub fn is_term(&self) -> bool {
        match self {
            Self::Jump(_) => true,
            Self::Branch(_, _, _) => true,
            Self::Return => true,
            Self::Yield => true,
            _ => false,
        }
    }
}

pub trait ICodeModule {
    fn shared_libraries(&self) -> Vec<String>;
    fn lookup_name(&self, name: &StringKey) -> Option<LinkId>;
    fn get_span_id(&self, value_id: ValueId) -> SpanId;
    fn get_name(&self, v: CodeOffset) -> Option<StringLabel>;
    fn get_code(&self, value_id: ValueId) -> &LCode;
    fn get_next(&self, value_id: ValueId) -> Option<ValueId>;
    fn get_prev(&self, value_id: ValueId) -> Option<ValueId>;

    fn get_cfg(&self, block_id: BlockId, b: &NodeBuilder) -> CFG {
        let entry_id = self.resolve_code_offset(block_id.into());
        self.get_graph(entry_id, Some(Successor::BlockScope), b)
    }

    fn get_block_successors(&self, entry_id: ValueId) -> Vec<(Successor, CodeOffset)>;

    fn get_graph(&self, entry_id: ValueId, scope: Option<Successor>, b: &NodeBuilder) -> CFG {
        let mut cfg = CFG::new();

        let mut stack = VecDeque::new();
        stack.push_back(entry_id);

        loop {
            if let Some(entry_id) = stack.pop_front() {
                if cfg.ids.contains_key(&entry_id) {
                    continue;
                }
                let name = self.code_to_string(entry_id, b);
                let c = cfg.g.add_node(Node::new_block(name, entry_id.into()));
                cfg.ids.insert(entry_id, c);
                for (succ_type, next_code_offset) in self.get_block_successors(entry_id) {
                    let v = self.resolve_code_offset(next_code_offset);
                    if scope.is_none() || scope == Some(succ_type) {
                        stack.push_back(v);
                    }
                }
            } else {
                break;
            }
        }

        for entry_id in cfg.ids.keys() {
            //let block = self.env.get_block(*entry_id);
            let id = cfg.ids.get(entry_id).unwrap();
            for (succ_type, next_code_offset) in self.get_block_successors(*entry_id) {
                if let Successor::BlockScope = succ_type {
                    let v = self.resolve_code_offset(next_code_offset);
                    let child_id = cfg.ids.get(&v).unwrap();
                    cfg.g.add_edge(*id, *child_id, ());
                }
            }
        }
        cfg
    }

    fn resolve_declaration<'c>(&self, offset: CodeOffset) -> Option<CodeOffset> {
        let mut current = offset;
        loop {
            let value_id = self.resolve_code_offset(current);
            let code = self.get_code(value_id);
            if let LCode::CallValue(inds) = code {
                current = inds.clone().offset();
                continue;
            }

            return Some(current);
        }
    }

    fn get_previous_values(&self, v: ValueId) -> Vec<CodeOffset> {
        let mut values = VecDeque::new();
        loop {
            let i = values.len();
            let v = ValueId((v.index() - 1 - i) as u32);
            let code = self.get_code(v);
            if let LCode::CallValue(inds) = code {
                let offset = inds.clone().offset();
                values.push_front(offset.into());
                continue;
            }
            break;
        }
        values.into()
    }

    fn get_type(&self, v: CodeOffset) -> AstType;
    fn get_entry_id(&self, value_id: ValueId) -> ValueId;
    fn is_in_static_scope(&self, v: CodeOffset) -> bool;
    fn get_mem(&self, offset: CodeOffset) -> &VarDefinitionSpace;
    fn resolve_code_offset(&self, code_offset: CodeOffset) -> ValueId;

    fn blocks(&self, block_id: BlockId, v: ValueId, b: &NodeBuilder) -> Vec<CodeOffset> {
        let cfg = self.get_cfg(block_id, b);
        cfg.blocks(v)
    }

    fn get_entry_id_from_block_id(&self, block_id: BlockId) -> ValueId;
    fn dump_code_table(&self, filename: &str, b: &mut NodeBuilder);
    fn dump_graph(&self, filename: &str, b: &NodeBuilder);

    fn get_label_args(&self, v: ValueId) -> Vec<AstType> {
        let mut current = v;
        let mut out = vec![];
        loop {
            if let Some(next) = self.get_next(current) {
                current = next;
                let code = self.get_code(current);
                if let LCode::Arg(_) = code {
                    let ty = self.get_type(current.into());
                    out.push(ty);
                    continue;
                }
            }
            break;
        }
        out
    }

    fn code_to_string(&self, v: ValueId, b: &NodeBuilder) -> String {
        let code = self.get_code(v);
        match code {
            LCode::Declare => {
                let code_str = b.labels.r(self.get_name(v.into()).unwrap());
                format!("declare {}: {:?}", code_str, self.get_type(v.into()))
            }

            LCode::DeclareFunction(maybe_entry) => {
                let code_str = b.labels.r(self.get_name(v.into()).unwrap());
                if let Some(entry_id) = maybe_entry {
                    format!("declare_function({},{:?})", code_str, entry_id)
                } else {
                    format!("declare_function({})", code_str)
                }
            }

            LCode::DeclareTemplate(maybe_entry) => {
                let code_str = b.labels.r(self.get_name(v.into()).unwrap());
                if let Some(entry_id) = maybe_entry {
                    format!("declare_template({},{:?})", code_str, entry_id)
                } else {
                    format!("declare_template({})", code_str)
                }
            }

            LCode::Label => {
                let args = self.get_label_args(v);
                if let Some(key) = self.get_name(v.into()) {
                    format!("label({},{})", b.labels.r(key), args.len())
                } else {
                    format!("label(_,{})", args.len())
                }
            }

            LCode::Jump(value_id) => {
                let values = self.get_previous_values(v);
                format!("jump({:?}, num_args: {})", value_id, values.len())
            }

            LCode::Val(Literal::String(s)) => {
                format!("String({})", s)
            }

            LCode::Ternary(c, x, y) => {
                format!("Ternary({:?},{},{})", c, x, y)
            }

            LCode::Branch(c, x, y) => {
                format!("Branch({:?},{},{})", c, x, y)
            }

            _ => {
                format!("{:?}", code)
            }
        }
    }
    fn code_count(&self) -> usize;
}

pub fn dump_env(env: &Environment, b: &NodeBuilder) {
    println!("current scope: {:?}", env.current_scope());
    //println!("static block: {:?}", self.static_block_id());
    //println!("static scope: {:?}", self.static_scope_id());
    for block in env.blocks.iter() {
        //let block_id = BlockId(offset as u32);
        println!("block({:?}, {:?})", block.entry_id, block);
    }

    for (index, layer) in env.scopes.iter().enumerate() {
        println!("scope({},{:?})", index, layer.scope_type);
        for (key, data) in layer.names.iter() {
            println!("  name  {} = {:?}", b.labels.r((*key).into()), data);
        }
        for (key, data) in layer.labels.iter() {
            println!("  label {} = {:?}", b.labels.r(*key), data);
        }
        for next_id in layer.next_block.iter() {
            println!("  next  {:?}", next_id);
        }
        for block_id in layer.blocks.iter() {
            println!("  block {:?}", block_id);
        }
        for (name, def) in layer.lambdas.iter() {
            println!("  def {:?}", (b.labels.r(*name), def));
        }
    }
}
