use crate::{
    Builtin, Flatten, ICodeModule, LCode, Module, NodeBuilder, UseIndex, ValueId,
    VarDefinitionSpace,
};
use anyhow::Result;
use std::collections::{HashMap, VecDeque};

use compile_core::{BinaryOperation, Literal, NaryOperation, StringKey, UnaryOperation};

#[derive(Debug, Clone)]
pub enum Value {
    Int(i64),
    Index(usize),
    Float(f64),
    Bool(bool),
    Tuple(Vec<Value>),
    Link(usize),
    Uninitialized,
    None,
}

impl Value {
    pub fn from_lit(lit: &Literal) -> Self {
        match lit {
            Literal::Int(i) => Value::Int(*i),
            Literal::Float(f) => Value::Float(*f),
            Literal::Bool(v) => Value::Bool(*v),
            Literal::Index(v) => Value::Index(*v),
            Literal::Link(x) => Value::Link(*x),
            Literal::Block(_) => {
                unreachable!("{:?}", lit);
            }
            _ => unimplemented!("{:?}", lit),
        }
    }

    pub fn resolve_index(&self, inds: &Vec<UseIndex>) -> Value {
        let mut value = self;
        for i in inds {
            match value {
                Self::Tuple(values) => match i {
                    UseIndex::Pos(pos) => {
                        value = values.get(*pos).unwrap();
                    }
                    _ => unimplemented!("{:?}", i),
                },
                _ => unimplemented!("{:?}", value),
            }
        }
        return value.clone();
    }
}

#[derive(Debug, Copy, Clone)]
enum ScopeType {
    Static,
    Function,
    Block,
}

#[derive(Debug)]
struct Scope {
    ty: ScopeType,
    return_link_id: Option<ValueId>,
    args: VecDeque<Value>,
}

impl Scope {
    pub fn new(ty: ScopeType, return_link_id: Option<ValueId>) -> Self {
        Self {
            ty,
            return_link_id,
            args: VecDeque::new(),
        }
    }
}

pub struct Interp<'a> {
    m: &'a dyn ICodeModule,
    b: &'a mut NodeBuilder,
    pos: ValueId,
    stack: Vec<Scope>,
    call_args: VecDeque<Value>,
    return_link_id: Option<ValueId>,
    jump_type: ScopeType,
    values: HashMap<ValueId, Value>,
}

impl<'a> Interp<'a> {
    pub fn new(m: &'a Flatten<Module>, b: &'a mut NodeBuilder, name: StringKey) -> Self {
        let link_id = m.lookup_name(&name).unwrap();
        let pos = m.resolve_code_offset(link_id.into());
        let scope = Scope::new(ScopeType::Static, None);

        let block_id = m.static_block_id();
        let block = m.blocks.get_block(block_id);
        let links = block.iter().collect::<Vec<_>>();
        let mut values = HashMap::new();

        // statics
        for link_id in links {
            let entry = m.get_link_entry(link_id);
            let code = &entry.code;
            let value_id = entry.value_id.unwrap();
            match code {
                LCode::Val(lit) => {
                    let value = Value::from_lit(lit);
                    values.insert(value_id, value);
                }
                _ => (),
            }
        }

        Self {
            m,
            b,
            pos,
            stack: vec![scope],
            call_args: VecDeque::new(),
            return_link_id: None,
            jump_type: ScopeType::Function,
            values,
        }
    }

    pub fn advance(&mut self) {
        self.pos = ValueId::new(self.pos.index() as u32 + 1);
    }

    pub fn jump(&mut self, target: ValueId) {
        let entry = self.m.get_entry(self.pos);
        let ty = &entry.ty;
        println!("ty: {:?}", ty);
        println!("@{}: jump: {}", self.pos, target);

        // ensure arity match
        assert_eq!(ty.fields().len(), self.call_args.len());
        self.jump_type = ScopeType::Block;
        self.pos = target;
    }

    pub fn call(&mut self, target: ValueId) {
        self.return_link_id = Some(self.pos);
        self.jump_type = ScopeType::Function;
        self.pos = target;
    }

    pub fn push_arg(&mut self, v: Value) {
        self.stack.last_mut().unwrap().args.push_back(v);
    }

    pub fn pop_arg(&mut self) -> Value {
        self.stack.last_mut().unwrap().args.pop_front().unwrap()
    }

    pub fn save_value(&mut self, value: Value) {
        self.values.insert(self.pos, value);
    }

    fn get_value(&self, v: ValueId) -> Option<Value> {
        let entry = self.m.get_entry(v);
        let v = if let VarDefinitionSpace::Stack(decl_link_id) = entry.mem {
            let v_decl = self.m.resolve_code_offset(decl_link_id.into());
            v_decl
        } else {
            v
        };

        self.values.get(&v).cloned()
    }

    pub fn resolve_value(&mut self, v: ValueId) -> Result<Value> {
        let entry = self.m.get_entry(v);
        let code = &entry.code;

        match code {
            LCode::Arg(_index) => {
                return Ok(self.get_value(v).unwrap());
            }
            LCode::Declare => {
                let value = self.values.get(&v).unwrap().clone();
                return Ok(value);
            }

            LCode::Val(_)
            | LCode::Load(_)
            | LCode::Call(_)
            | LCode::Op2(_)
            | LCode::NaryOp(_)
            | LCode::Ternary(_, _, _)
            | LCode::Op1(_) => {
                return Ok(self.values.get(&v).unwrap().clone());
            }

            LCode::Tuple(link_ids) => {
                let mut values = vec![];
                for offset in link_ids {
                    let v = self.m.resolve_code_offset(offset.into());
                    values.push(self.resolve_value(v)?);
                }
                return Ok(Value::Tuple(values));
            }

            LCode::Use(base, inds) => {
                let v = self.m.resolve_code_offset(*base);
                let value = self.values.get(&v).unwrap().clone();
                //let value = scope.values.get(&v).unwrap().clone();
                let inds = inds
                    .iter()
                    .cloned()
                    .map(|i| match i {
                        UseIndex::Use(offset) => {
                            let v = self.m.resolve_code_offset(offset);
                            let v = self.resolve_value(v).unwrap();
                            match v {
                                Value::Int(i) => UseIndex::Pos(i as usize),
                                Value::Index(i) => UseIndex::Pos(i),
                                _ => unimplemented!(),
                            }
                        }
                        _ => i.clone(),
                    })
                    .collect::<Vec<_>>();
                return Ok(value.resolve_index(&inds));
            }

            _ => unimplemented!("{:?}", (code, v)),
        }
    }

    fn unwind(&mut self) -> Scope {
        loop {
            let scope = self.stack.pop().unwrap();
            match scope.ty {
                ScopeType::Function => return scope,
                ScopeType::Block => (),
                ScopeType::Static => (),
            }
        }
    }

    fn store_value(&mut self, value: Value) {
        let v = self.pos;
        let entry = self.m.get_entry(v);
        let v_decl = if let VarDefinitionSpace::Stack(decl_link_id) = entry.mem {
            let v_decl = self.m.resolve_code_offset(decl_link_id.into());
            v_decl
        } else {
            v
        };
        self.values.insert(v_decl, value);
    }

    pub fn step(&mut self) -> Result<bool> {
        let pos = self.pos;
        let entry = self.m.get_entry(pos);
        let code = &entry.code;
        let result = match code {
            LCode::DeclareFunction(_) => {
                self.advance();
                true
            }
            LCode::Label => {
                let s_name = self.b.labels.r(entry.name.unwrap().into());
                println!("@{}: label: {}, {:?}", pos, s_name, self.call_args);

                // load args into scope
                let scope = Scope::new(self.jump_type, self.return_link_id);
                self.stack.push(scope);

                self.advance();
                true
            }

            LCode::Arg(_) => {
                if let Some(value) = self.call_args.pop_front() {
                    self.store_value(value);
                    self.advance();
                } else {
                    unreachable!("missing arg: {}", pos);
                }
                true
            }

            LCode::Declare => {
                self.save_value(Value::Uninitialized);
                self.advance();
                true
            }

            LCode::Store(decl, v) => {
                let v_decl = self.m.resolve_code_offset(decl.into());
                let v_value = self.m.resolve_code_offset(v.into());
                let value = self.resolve_value(v_value)?;
                if self.values.contains_key(&v_decl) {
                    self.values.insert(v_decl, value);
                    self.advance();
                    return Ok(true);
                }
                unreachable!()
            }

            LCode::Load(decl) => {
                let v_decl = self.m.resolve_code_offset(decl.into());
                let value = self.resolve_value(v_decl).unwrap();
                self.save_value(value);
                self.advance();
                true
            }

            LCode::Call(f) => {
                let v_func = self.m.resolve_code_offset(f.into());
                self.call(v_func);
                true
            }

            LCode::Tuple(_) => {
                let value = self.resolve_value(self.pos)?;
                self.store_value(value);
                self.advance();
                true
            }

            LCode::NaryOp(op) => {
                let values = self.call_args.drain(..).collect();
                let output = match op {
                    NaryOperation::Struct => Value::Tuple(values),
                };
                self.store_value(output);
                self.advance();
                true
            }

            LCode::Op1(op) => {
                let v1 = self.call_args.pop_front().unwrap();
                let v = match (op, v1.clone()) {
                    (UnaryOperation::Minus, Value::Int(i1)) => Value::Int(-i1),
                    (UnaryOperation::Minus, Value::Float(i1)) => Value::Float(-i1),
                    _ => unimplemented!("{:?}", (op, v1)),
                };
                self.store_value(v);
                self.advance();
                true
            }

            LCode::Op2(op) => {
                assert_eq!(self.call_args.len(), 2);
                let v1 = self.call_args.pop_front().unwrap();
                let v2 = self.call_args.pop_front().unwrap();
                let v = match (op, v1.clone(), v2.clone()) {
                    (BinaryOperation::EQ, Value::Int(i1), Value::Int(i2)) => Value::Bool(i1 == i2),
                    (BinaryOperation::NE, Value::Int(i1), Value::Int(i2)) => Value::Bool(i1 != i2),
                    (BinaryOperation::GT, Value::Int(i1), Value::Int(i2)) => Value::Bool(i1 > i2),
                    (BinaryOperation::GTE, Value::Int(i1), Value::Int(i2)) => Value::Bool(i1 >= i2),
                    (BinaryOperation::GT, Value::Float(i1), Value::Float(i2)) => {
                        Value::Bool(i1 > i2)
                    }
                    (BinaryOperation::GTE, Value::Float(i1), Value::Float(i2)) => {
                        Value::Bool(i1 >= i2)
                    }
                    (BinaryOperation::Add, Value::Int(i1), Value::Int(i2)) => Value::Int(i1 + i2),
                    (BinaryOperation::Add, Value::Float(i1), Value::Float(i2)) => {
                        Value::Float(i1 + i2)
                    }
                    (BinaryOperation::Subtract, Value::Int(i1), Value::Int(i2)) => {
                        Value::Int(i1 - i2)
                    }
                    (BinaryOperation::Subtract, Value::Float(i1), Value::Float(i2)) => {
                        Value::Float(i1 - i2)
                    }
                    _ => {
                        let span_id = self.m.get_span_id(pos);
                        self.b.push_error_labels(vec![self.b.primary_label(
                            &format!("Not implemented: {:?}", (op, v1, v2)),
                            span_id,
                        )]);
                        return Ok(false);
                    }
                };
                self.store_value(v);
                self.advance();
                true
            }

            LCode::Val(Literal::Block(block_id)) => {
                // the index is actually the block_id
                let index = block_id.index() as i64;
                let value = Value::Int(index);
                self.store_value(value);
                self.advance();
                true
            }

            LCode::Val(lit) => {
                let value = Value::from_lit(lit);
                self.store_value(value);
                self.advance();
                true
            }

            LCode::Use(_base, _inds) => {
                self.advance();
                true
            }

            LCode::CallValue(base) => {
                let base = self.m.resolve_code_offset(*base);
                let value = self.resolve_value(base)?;
                self.call_args.push_back(value);
                self.advance();
                true
            }

            LCode::Jump(target) => {
                // push args
                let v = self.m.resolve_code_offset(target.into());
                self.jump(v);
                true
            }

            LCode::Switch(link_id, m) => {
                // push args
                let base = self.m.resolve_code_offset((*link_id).into());
                let value = self.resolve_value(base)?;

                match value {
                    Value::Int(i) => {
                        // lookup the block_id in the switch map
                        let block_id = m.get(&(i as usize)).unwrap();
                        let target = self.m.resolve_code_offset(block_id.into());
                        self.jump(target);
                    }
                    _ => unreachable!(),
                }
                true
            }

            LCode::Ternary(condition, then_target, else_target) => {
                let v = self.m.resolve_code_offset(*condition);
                let c = self.resolve_value(v)?;

                match c {
                    Value::Bool(cond) => {
                        if cond {
                            let target = self.m.resolve_code_offset(then_target.clone().into());
                            self.call(target);
                        } else {
                            let target = self.m.resolve_code_offset(else_target.clone().into());
                            self.call(target);
                        }
                    }
                    _ => unreachable!(),
                }
                true
            }

            LCode::Branch(condition, then_target, else_target) => {
                let v = self.m.resolve_code_offset(*condition);
                let c = self.resolve_value(v)?;

                match c {
                    Value::Bool(cond) => {
                        if cond {
                            let target = self.m.resolve_code_offset(then_target.clone().into());
                            self.jump(target);
                        } else {
                            let target = self.m.resolve_code_offset(else_target.clone().into());
                            self.jump(target);
                        }
                    }
                    _ => unreachable!(),
                }
                true
            }

            LCode::Builtin(bi) => {
                let bi = self.b.builtins.get_enum(*bi);
                let result = match bi {
                    Builtin::Import => {
                        unreachable!()
                    }
                    Builtin::Assert => {
                        assert_eq!(self.call_args.len(), bi.arity());
                        let value = self.call_args.pop_front().unwrap();
                        match value {
                            Value::Bool(condition) => {
                                if !condition {
                                    let span_id = self.m.get_span_id(pos);
                                    self.b.push_error_labels(vec![self
                                        .b
                                        .primary_label(&format!("Check Failed"), span_id)]);
                                }
                                condition
                            }
                            _ => unreachable!(),
                        }
                    }
                    Builtin::Print => {
                        assert_eq!(self.call_args.len(), bi.arity());
                        let value = self.call_args.pop_front().unwrap();
                        println!("========================");
                        println!("***print: {:?}", value);
                        println!("========================");
                        //assert!(false);
                        true
                    }
                };
                self.advance();
                result
            }

            LCode::Return | LCode::Yield => {
                let scope = self.unwind();
                if let Some(target) = scope.return_link_id {
                    if self.call_args.len() > 0 {
                        let value = self.call_args.pop_back().unwrap();
                        // save the value in the return link
                        self.values.insert(target, value);
                    }

                    // only support a single return value
                    assert!(self.call_args.len() <= 1);

                    self.jump(target.succ());
                    true
                } else {
                    // program terminates
                    false
                }
            }

            LCode::Noop => {
                self.advance();
                true
            }

            _ => unimplemented!("{:?}", code),
        };

        Ok(result)
    }
}

pub fn interp<'c>(
    shared: &[String],
    m: &Flatten<Module>,
    libpath: &str,
    b: &mut NodeBuilder,
) -> i32 {
    let paths = shared
        .iter()
        .map(|s| {
            let mut path = format!("{}/{}.so", libpath, s);
            path.push('\0');
            path
        })
        .collect::<Vec<_>>();

    let _shared = paths.iter().map(|p| p.as_str()).collect::<Vec<_>>();

    let main = b.labels.s("main");
    let mut interp = Interp::new(m, b, main);
    loop {
        //let pos = interp.pos;
        //let code = interp.m.get_code(pos);
        let r = interp.step();
        //println!("step: {}, {}", pos, interp.format_code(pos));
        //println!("\tcall_args: {:?}", interp.call_args);
        //for (index, scope) in interp.stack.iter().enumerate() {
        //println!("\t[{}] scope: {:?}", index, scope);
        //}

        if let Ok(cond) = r {
            if !cond {
                break;
            }
        } else {
            break;
        }
    }

    let mut result: i32 = -1;
    println!("exec: {:?}, {:?}", interp.call_args, interp.stack);
    if let Some(Value::Int(value)) = interp.call_args.get(0) {
        result = *value as i32;
    }
    println!("main({:?}) => {:?}", interp.call_args, result);
    result
}
