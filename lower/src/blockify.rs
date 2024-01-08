use anyhow::Result;
use codespan_reporting::diagnostic::{Diagnostic, Label};
//use indexmap::IndexMap;

use crate::{
    ast::AssignTarget,
    ast::Builtin,
    Argument,
    Ast,
    AstNode,
    AstType,
    BinaryOperation,
    Diagnostics,
    Extra,
    IREnvironment,
    IRPlaceTable,
    Literal,
    NodeBuilder,
    ParameterNode,
    PlaceId,
    PlaceNode,
    Span,
    StringKey,
    //StringLabel,
    UnaryOperation,
    //Definition,
    VarDefinitionSpace,
};

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum BlockId {
    Name(StringKey),
    // unique
    U(usize),
}

impl From<StringKey> for BlockId {
    fn from(item: StringKey) -> BlockId {
        BlockId::Name(item)
    }
}

impl From<&StringKey> for BlockId {
    fn from(item: &StringKey) -> BlockId {
        BlockId::Name(*item)
    }
}

#[derive(Debug)]
pub struct AstBlock {
    name: BlockId,
}

#[derive(Debug)]
pub struct LoopLayer {
    next: BlockId,
    restart: BlockId,
}

#[derive(Debug)]
pub struct ValueId(u32);

#[derive(Debug)]
pub enum LCode {
    Label(BlockId, u8, u8), // BlockId, number of positional arguments, number of named arguments
    Declare,
    DeclareFunction(BlockId), // block_id of entry point
    Value(ValueId),
    NamedArg(StringKey),
    Const(Literal),
    Op1(UnaryOperation, ValueId),
    Op2(BinaryOperation, ValueId, ValueId),
    Load(PlaceId),
    Store(PlaceId, ValueId),
    Jump(BlockId, u8),
    Branch(ValueId, BlockId, BlockId),
    Builtin(Builtin, u8, u8),
    Call(PlaceId, u8, u8),
}

impl LCode {
    pub fn is_start(&self) -> bool {
        match self {
            Self::Label(_, _, _) => true,
            _ => false,
        }
    }

    pub fn is_term(&self) -> bool {
        match self {
            Self::Jump(_, _) => true,
            Self::Branch(_, _, _) => true,
            _ => false,
        }
    }

    pub fn dump<E: Extra>(&self, depth: usize, env: &IREnvironment, b: &NodeBuilder<E>) {
        match self {
            Self::Label(block_id, _args, _kwargs) => {
                let index = env.blocks.lookup_block_label(*block_id).unwrap();
                let _block = env.blocks.g.node_weight(index).unwrap();
                env.blocks.dump_node(b, index, index, depth);
                //println!("{:width$}label({:?}", "", b.resolve_block_label(block.name.into()), width = depth * 2);
            }
            _ => unimplemented!(),
        }
    }
}

pub fn dump_codes<E: Extra>(codes: &[LCode], _places: &IRPlaceTable, _b: &NodeBuilder<E>) {
    let mut pos = 0;
    let depth = 0;
    loop {
        println!(
            "%{} = {:width$}{:?}",
            pos,
            "",
            codes[pos],
            width = depth * 2
        );
        pos += 1;
        if pos == codes.len() {
            break;
        }
    }
}

#[derive(Debug)]
pub struct Environment {
    stack: Vec<BlockId>,
    //places: IndexMap<PlaceId, SymIndex>,
    //label_count: usize,
    //pub blocks: BlockTable,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            stack: vec![],
            //places: IndexMap::new(),
            //label_count: 0,
            //blocks: BlockTable::new(),
        }
    }

    pub fn error(&self, msg: &str, span: Span) -> Diagnostic<usize> {
        let r = span.begin.pos as usize..span.end.pos as usize;
        let labels = vec![Label::primary(span.file_id, r).with_message(msg)];
        let error = Diagnostic::error()
            .with_labels(labels)
            .with_message("error");
        error
    }

    pub fn enter_block(&mut self, block_id: BlockId, _span: Span) {
        self.stack.push(block_id);
    }

    pub fn exit_block(&mut self) {
        self.stack.pop();
    }

    pub fn stack_size(&self) -> usize {
        self.stack.len()
    }

    pub fn root(&self) -> BlockId {
        self.stack.first().unwrap().clone()
    }

    pub fn current_block(&self) -> BlockId {
        self.stack.last().unwrap().clone()
    }

    pub fn block_is_static(&self, block_index: BlockId) -> bool {
        // root block is static block, and there's only one for now
        self.root() == block_index
    }

    /*
    pub fn add_definition(
        &mut self,
        block_id: BlockId,
        place_id: PlaceId,
        name: StringLabel,
    ) -> SymIndex {
        let data = self.blocks.g.node_weight_mut(block_index).unwrap();
        let index = data.add_definition(place_id);
        data.alloca_add(place_id, name, index);
        self.places.insert(place_id, index);
        //data.add_symbol(name, index);
        index
    }

    pub fn block_name_in_scope(&self, index: NodeIndex, name: StringLabel) -> Option<PlaceId> {
        let maybe_dom = simple_fast(&self.blocks.g, self.root())
            .dominators(index)
            .map(|it| it.collect::<Vec<_>>());
        //println!("dom: {:?} => {:?}", index, maybe_dom);
        if let Some(dom) = maybe_dom {
            for i in dom.into_iter().rev() {
                let data = self.blocks.g.node_weight(i).unwrap();
                //println!("searching {:?}", (i, name));
                if let Some(place_id) = data.symbols.get(&name) {
                    //println!("found {:?}", (place_id, name));
                    return Some(*place_id);
                }
            }
        }
        None
    }
    */

    /*
    pub fn dump<E: Extra>(&self, b: &NodeBuilder<E>, current_block: NodeIndex) {
        let root = self.blocks.block_names_index.get(&self.root()).unwrap();
        let current = self.blocks.block_names_index.get(&current_block).unwrap();
        println!("dump: root: {:?} => {:?}", self.root(), current_block);
        println!(
            "dump: root: {:?} => {:?}",
            b.resolve_block_label(*root),
            b.resolve_block_label(*current)
        );

        self.blocks.dump_node(b, self.root(), current_block, 0);
        self.blocks.save_graph("out.dot", b);
    }
    */
}

#[derive(Debug)]
pub struct Blockify<E> {
    code: Vec<LCode>,
    place: Vec<Option<PlaceNode>>,
    pending_blocks: Vec<AstNode<E>>,
    loop_stack: Vec<LoopLayer>,
}

impl<E: Extra> Blockify<E> {
    pub fn new() -> Self {
        Self {
            code: vec![],
            place: vec![],
            pending_blocks: vec![],
            loop_stack: vec![],
        }
    }

    pub fn dump(&self, places: &IRPlaceTable, b: &NodeBuilder<E>) {
        dump_codes(&self.code, places, b);
    }

    pub fn push_code(&mut self, code: LCode, place: Option<PlaceNode>) -> ValueId {
        let offset = self.code.len();
        self.code.push(code);
        self.place.push(place);
        ValueId(offset as u32)
    }

    pub fn get_place(&self, v: ValueId) -> &PlaceNode {
        self.place.get(v.0 as usize).unwrap().as_ref().unwrap()
    }

    pub fn build(
        &mut self,
        env: &mut IREnvironment,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        let nodes = self.pending_blocks.drain(..).collect::<Vec<_>>();
        for ast in nodes {
            self.add(ast, env, b, d)?;
        }
        Ok(())
    }

    pub fn add(
        &mut self,
        node: AstNode<E>,
        env: &mut IREnvironment,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<ValueId> {
        match node.node {
            Ast::Module(block) => {
                let value_id = self.push_code(LCode::Label(block.name, 0, 0), None);

                for c in block.children.into_iter() {
                    self.add(c, env, b, d)?;
                }
                Ok(value_id)
            }

            Ast::Sequence(exprs) => {
                let mut value_id = None;
                for c in exprs.into_iter() {
                    value_id = Some(self.add(c, env, b, d)?);
                }
                Ok(value_id.unwrap())
            }

            Ast::Definition(def) => {
                let params = def.params.iter().map(|p| p.ty.clone()).collect();
                let ty = AstType::Func(params, def.return_type);
                let p = PlaceNode::new_static(def.name, ty);
                //let place_id = self.place.push(p);
                if let Some(body) = def.body {
                    let seq = vec![
                        b.node(Ast::Label(def.name.into(), def.params.clone())),
                        *body,
                    ];
                    self.pending_blocks.push(b.seq(seq));
                }
                Ok(self.push_code(LCode::DeclareFunction(def.name.into()), Some(p)))
            }

            Ast::Label(block_id, params) => {
                //env.enter_block(
                let v = self.push_code(LCode::Label(block_id, 0, params.len() as u8), None);
                for p in params {
                    self.push_code(LCode::NamedArg(p.name.into()), None);
                }
                Ok(v)
            }

            Ast::Assign(target, expr) => {
                let name = match target {
                    AssignTarget::Identifier(name) | AssignTarget::Alloca(name) => name,
                };

                let v = self.add(*expr, env, b, d)?;
                let ty = self.get_place(v).ty.clone();
                let p = PlaceNode::new_stack(name, ty);
                Ok(self.push_code(LCode::Declare, Some(p)))
            }

            Ast::Builtin(bi, args) => {
                let _ty = bi.get_return_type();
                let args_size = args.len();
                assert_eq!(args_size, bi.arity());
                let mut values = vec![];
                for a in args.into_iter() {
                    let Argument::Positional(expr) = a;
                    let v = self.add(*expr, env, b, d)?;
                    values.push(v);
                }
                let value_id = self.push_code(LCode::Builtin(bi, args_size as u8, 0), None);
                for v in values {
                    self.push_code(LCode::Value(v), None);
                }
                Ok(value_id)
            }

            Ast::Literal(lit) => {
                let ty: AstType = lit.clone().into();
                let name = b.labels.fresh_var_id();
                let p = PlaceNode::new(name, ty, VarDefinitionSpace::Reg);
                Ok(self.push_code(LCode::Const(lit), Some(p)))
            }

            //Ast::Identifier(label) => {
            //}
            Ast::UnaryOp(op, x) => {
                let vx = self.add(*x, env, b, d)?;
                let code = LCode::Op1(op, vx);
                Ok(self.push_code(code, None))
            }

            Ast::Ternary(c, x, y) => {
                let v = self.add(*c, env, b, d)?;

                let then_block_id = b.labels.fresh_block_id();
                let seq = vec![b.node(Ast::Label(then_block_id, vec![])), *x];
                self.pending_blocks.push(b.seq(seq));

                let else_block_id = b.labels.fresh_block_id();
                let seq = vec![b.node(Ast::Label(else_block_id, vec![])), *y];
                self.pending_blocks.push(b.seq(seq));

                let code = LCode::Branch(v, then_block_id, else_block_id);
                Ok(self.push_code(code, None))
            }

            Ast::BinaryOp(op, x, y) => {
                let vx = self.add(*x, env, b, d)?;
                let vy = self.add(*y, env, b, d)?;
                let code = LCode::Op2(op.node, vx, vy);
                Ok(self.push_code(code, None))
            }

            Ast::Goto(block_id, args) => {
                let code = LCode::Jump(block_id, args.len() as u8);
                let jump_value = self.push_code(code, None);
                for a in args {
                    let v = self.add(a, env, b, d)?;
                    self.push_code(LCode::Value(v), None);
                }
                Ok(jump_value)
            }

            _ => unimplemented!("{:?}", node.node),
        }
    }

    pub fn build_block(
        &mut self,
        node: AstNode<E>,
        name: StringKey,
        params: Vec<ParameterNode<E>>,
        //places: &mut IRPlaceTable,
        env: &mut IREnvironment,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        let seq = node.to_vec();
        if !seq.first().unwrap().node.is_label() {
            self.code
                .push(LCode::Label(name.into(), 0, params.len() as u8));
            for p in params {
                self.code.push(LCode::NamedArg(p.name));
            }
        }
        for n in seq {
            self.add(n, env, b, d)?;
        }
        Ok(())
    }
}

/*
impl<E: Extra> Definition<E> {
    fn flatten(self, b: &mut NodeBuilder<E>) -> Result<()> {
        //let code = LCode::Label();
        Ok(())
    }
}

impl<E: Extra> Definition<E> {
    fn blockify(mut self, places: &mut IRPlaceTable, env: &mut IREnvironment, b: &mut NodeBuilder<E>, d: &mut Diagnostics) -> Result<()> {
        if let Some(ref _body) = self.body {
            let mut blockify = Blockify::new();
            blockify.build_block(
                *self.body.take().unwrap(),
                self.name.into(),
                self.params.clone(),
                places,
                env,
                b,
                d,
            )?;
            Ok(())
        } else {
            Ok(())
        }
    }
}
*/

/*
impl<E: Extra> AstNode<E> {
    pub fn is_term_recursive(&self) -> bool {
        false
    }

    pub fn blockify(
        self,
        places: &mut IRPlaceTable,
        env: &mut IREnvironment,
        b: &mut NodeBuilder<E>,
        d: &mut Diagnostics,
    ) -> Result<()> {
        match self.node {
            Ast::Module(block) => {
                let _block_index = env.blocks.add_block(places, block.name, vec![], d);

                //env.enter_block(block.
                for c in block.children.into_iter() {
                    c.blockify(places, env, b, d)?;
                }
                Ok(())
            }

            Ast::Sequence(exprs) => {
                for c in exprs.into_iter() {
                    c.blockify(places, env, b, d)?;
                }
                Ok(())
            }

            Ast::Definition(def) => {
                //let def = def.blockify(places, env, b, d)?;
                Ok(())
            }

            _ => Ok(()),
        }
    }
}
*/
