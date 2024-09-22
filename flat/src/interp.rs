use crate::{Builtin, ICodeModule, LCode, NodeBuilder, ValueId};
use std::collections::{HashMap, VecDeque};

use compile_core::{BinaryOperation, Literal, StringKey};

#[derive(Debug, Clone)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
    None,
}

impl Value {
    pub fn from_lit(lit: &Literal) -> Self {
        match lit {
            Literal::Int(i) => Value::Int(*i),
            Literal::Float(f) => Value::Float(*f),
            Literal::Bool(v) => Value::Bool(*v),
            _ => unimplemented!("{:?}", lit),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum ScopeType {
    Function,
    Block,
}

#[derive(Debug)]
pub struct Scope {
    ty: ScopeType,
    return_link_id: Option<ValueId>,
    args: VecDeque<Value>,
    values: HashMap<ValueId, Value>,
}

impl Scope {
    pub fn new(ty: ScopeType, return_link_id: Option<ValueId>) -> Self {
        Self {
            ty,
            return_link_id,
            args: VecDeque::new(),
            values: HashMap::new(),
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
}

impl<'a> Interp<'a> {
    pub fn new(m: &'a dyn ICodeModule, b: &'a mut NodeBuilder, name: StringKey) -> Self {
        let link_id = m.lookup_name(&name).unwrap();
        let pos = m.resolve_code_offset(link_id.into());
        Self {
            m,
            b,
            pos,
            stack: vec![],
            call_args: VecDeque::new(),
            return_link_id: None,
            jump_type: ScopeType::Function,
        }
    }

    pub fn advance(&mut self) {
        self.pos = ValueId::new(self.pos.index() as u32 + 1);
    }

    pub fn jump(&mut self, target: ValueId) {
        self.jump_type = ScopeType::Block;
        self.pos = target;
    }

    pub fn call(&mut self, target: ValueId) {
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
        self.stack
            .last_mut()
            .unwrap()
            .values
            .insert(self.pos, value);
    }

    pub fn resolve_value(&mut self, v: ValueId) -> Value {
        let code = self.m.get_code(v);
        for scope in self.stack.iter().rev() {
            match code {
                LCode::Const(lit) => {
                    return Value::from_lit(lit);
                }
                LCode::Arg(index) => {
                    if let Some(value) = scope.args.get(*index as usize) {
                        return value.clone();
                    }
                }
                LCode::Load(_) => {
                    if let Some(value) = scope.values.get(&v) {
                        return value.clone();
                    }
                }
                LCode::Call(_) | LCode::Op2(_) => {
                    return scope.values.get(&v).unwrap().clone();
                }
                _ => unimplemented!("{:?}", code),
            }
        }
        unreachable!()
    }

    pub fn resolve_declaration(&mut self, v: ValueId) -> Value {
        println!("resolve decl: {}", v);
        let code = self.m.get_code(v);
        for scope in self.stack.iter().rev() {
            match code {
                LCode::Declare => {
                    if let Some(value) = scope.values.get(&v) {
                        return value.clone();
                    }
                }
                _ => unimplemented!("{:?}", code),
            }
        }
        unreachable!()
    }

    pub fn unwind(&mut self) -> Scope {
        loop {
            let scope = self.stack.pop().unwrap();
            match scope.ty {
                ScopeType::Function => return scope,
                ScopeType::Block => (),
            }
        }
    }

    pub fn step(&mut self) -> bool {
        let pos = self.pos;
        let code = self.m.get_code(self.pos);
        let result = match code {
            LCode::DeclareFunction(_) => {
                self.advance();
                true
            }
            LCode::Label => {
                // load args into scope
                let mut scope = Scope::new(self.jump_type, self.return_link_id);
                scope.args = self.call_args.clone();
                self.call_args.clear();
                self.stack.push(scope);

                self.advance();
                true
            }

            LCode::Declare => {
                self.stack
                    .last_mut()
                    .unwrap()
                    .values
                    .insert(self.pos, Value::None);
                self.advance();
                true
            }

            LCode::Store(decl, v) => {
                let v_decl = self.m.resolve_code_offset(decl.into());
                let v_value = self.m.resolve_code_offset(v.into());
                let value = self.resolve_value(v_value);
                self.stack.last_mut().unwrap().values.insert(v_decl, value);
                self.advance();
                true
            }

            LCode::Load(decl) => {
                let v_decl = self.m.resolve_code_offset(decl.into());
                let value = self.resolve_declaration(v_decl);
                /*
                let value = self
                    .stack
                    .last()
                    .unwrap()
                    .values
                    .get(&v_decl)
                    .unwrap()
                    .clone();
                */
                self.stack
                    .last_mut()
                    .unwrap()
                    .values
                    .insert(self.pos, value);
                self.advance();
                true
            }

            LCode::Call(f) => {
                let v_func = self.m.resolve_code_offset(f.into());
                self.return_link_id = Some(self.pos);
                self.call(v_func);
                true
            }

            LCode::Op2(op) => {
                assert_eq!(self.call_args.len(), 2);
                let v1 = self.call_args.pop_front().unwrap();
                let v2 = self.call_args.pop_front().unwrap();
                let v = match (op, v1.clone(), v2.clone()) {
                    (BinaryOperation::EQ, Value::Int(i1), Value::Int(i2)) => Value::Bool(i1 == i2),
                    (BinaryOperation::GT, Value::Int(i1), Value::Int(i2)) => Value::Bool(i1 > i2),
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
                    _ => unimplemented!("{:?}", (op, v1, v2)),
                };
                self.stack.last_mut().unwrap().values.insert(self.pos, v);
                //self.call_args.push_back(v);
                self.advance();
                true
            }

            LCode::Arg(_) => {
                self.advance();
                true
            }

            LCode::Const(lit) => {
                let value = Value::from_lit(lit);
                self.save_value(value);
                self.advance();
                true
            }

            LCode::CallValue(v) => {
                let v = self.m.resolve_code_offset(*v);
                let value = self.resolve_value(v);
                self.call_args.push_back(value);
                self.advance();
                true
            }

            LCode::Jump(target) => {
                // push args
                let v = self.m.resolve_code_offset(*target);
                self.jump(v);
                true
            }

            LCode::Branch(condition, then_target, else_target) => {
                let v = self.m.resolve_code_offset(*condition);
                let c = self.resolve_value(v);

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
                match bi {
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
                                    return false;
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                    Builtin::Print => {
                        assert_eq!(self.call_args.len(), bi.arity());
                        let value = self.call_args.pop_front().unwrap();
                        println!("print: {:?}", value);
                    }
                }
                self.advance();
                true
            }

            LCode::Return => {
                let scope = self.unwind();
                if let Some(target) = scope.return_link_id {
                    assert!(self.call_args.len() <= 1);
                    if self.call_args.len() == 1 {
                        let value = self.call_args.pop_back().unwrap();
                        self.stack.last_mut().unwrap().values.insert(target, value);
                        //scope.values.insert(target, value);
                    }

                    self.jump(target.succ());
                    true
                } else {
                    // program terminates
                    //self.call_args = scope.args;
                    false
                }
            }
            _ => unimplemented!("{:?}", code),
        };

        println!("step: {}, {:?}", pos, code);
        println!("\tcall_args: {:?}", self.call_args);

        for scope in self.stack.iter() {
            println!("\tscope: {:?}", scope);
        }
        result
    }
}

pub fn interp<'c>(
    shared: &[String],
    m: &dyn ICodeModule,
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
        if !interp.step() {
            break;
        }
    }

    let mut result: i32 = -1;
    println!(
        "exec: {:?}, {:?}, {}",
        interp.call_args, interp.stack, result
    );
    if let Some(Value::Int(value)) = interp.call_args.get(0) {
        result = *value as i32;
    }
    result
}
