use anyhow::Result;
use ena::unify::*;
use std::convert::Into;
use thiserror::Error;

use compile_core::AstType;

#[derive(Debug, Error)]
pub enum UError {
    #[error("Bad")]
    Bad,
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct IntKey(u32);

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct UType(AstType);

impl std::ops::Deref for UType {
    type Target = AstType;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl From<AstType> for UType {
    fn from(item: AstType) -> Self {
        Self(item)
    }
}

impl Into<AstType> for UType {
    fn into(self) -> AstType {
        self.0
    }
}

impl UnifyKey for IntKey {
    type Value = UType;
    fn index(&self) -> u32 {
        self.0
    }
    fn from_index(u: u32) -> IntKey {
        IntKey(u)
    }
    fn tag() -> &'static str {
        "IntKey"
    }
    fn order_roots(
        a: IntKey,
        a_rank: &UType,
        b: IntKey,
        b_rank: &UType,
    ) -> Option<(IntKey, IntKey)> {
        if a_rank > b_rank {
            Some((a, b))
        } else if b_rank > a_rank {
            Some((b, a))
        } else {
            None
        }
    }
}

fn ast_unify_values(value1: &AstType, value2: &AstType) -> Result<AstType, UError> {
    let id1 = value1.try_unknown();
    let id2 = value2.try_unknown();
    match (id1, id2) {
        (None, None) => match (value1, value2) {
            //(Self::Int, Self::Float) | (Self::Float, Self::Int) => {
            //Ok(Self::Number)
            //}
            (AstType::Ptr(v1), AstType::Ptr(v2)) => {
                let ty = ast_unify_values(v1, v2)?;
                Ok(AstType::Ptr(ty.into()))
            }
            (AstType::Func(c1, r1), AstType::Func(c2, r2)) => {
                let r = ast_unify_values(r1, r2)?;
                let c1_fields = c1.fields();
                let c2_fields = c2.fields();
                if c1_fields.len() != c2_fields.len() {
                    Err(UError::Bad)
                } else {
                    let result = c1_fields
                        .iter()
                        .zip(c2_fields.iter())
                        .map_while(|((_, a), (_, b))| match ast_unify_values(a, b) {
                            Ok(s) => Some(s),
                            Err(_) => None,
                        })
                        .collect::<Vec<_>>();
                    if result.len() == c1_fields.len() {
                        Ok(AstType::func(result, r.into()))
                    } else {
                        Err(UError::Bad)
                    }
                }
            }
            (AstType::Struct(c1), AstType::Struct(c2)) => {
                if c1.len() != c2.len() {
                    Err(UError::Bad)
                } else {
                    let result = c1
                        .iter()
                        .zip(c2.iter())
                        .map_while(|((_, a), (_, b))| match ast_unify_values(a, b) {
                            Ok(s) => Some((None, s)),
                            Err(_) => None,
                        })
                        .collect::<Vec<_>>();
                    if result.len() == c1.len() {
                        Ok(AstType::Struct(result))
                    } else {
                        Err(UError::Bad)
                    }
                }
            }
            _ => {
                if value1 == value2 {
                    Ok(value1.clone())
                } else {
                    Err(UError::Bad)
                }
            }
        },
        (Some(_), None) => Ok(value2.clone()),
        (None, Some(_)) => Ok(value1.clone()),
        (Some(a), Some(_)) => Ok(AstType::Variable(a)),
    }
}

impl UnifyValue for UType {
    type Error = UError;

    fn unify_values(value1: &Self, value2: &Self) -> Result<Self, UError> {
        ast_unify_values(&value1.0, &value2.0).map(|ast| UType(ast))
    }
}

pub type TypeUnifyTable = UnificationTable<InPlace<IntKey>>;

pub struct TypeUnify {
    ut: TypeUnifyTable,
    //unknown_count: u32,
    variables: Vec<IntKey>,
}

impl TypeUnify {
    pub fn new() -> Self {
        Self {
            ut: TypeUnifyTable::new(),
            //unknown_count: 0,
            variables: vec![],
        }
    }

    pub fn fresh_unknown(&mut self) -> UType {
        let offset = self.variables.len();
        let r = UType(AstType::Variable(offset as u32));
        self.variables.push(self.ut.new_key(r.clone()));
        r
    }

    fn add_var(&mut self, a: UType) -> IntKey {
        match a.0 {
            AstType::Variable(v) => self.variables[v as usize],
            _ => self.ut.new_key(a),
        }
    }

    pub fn dump(&mut self) {
        println!("dump: {}", self.variables.len());
        for i in 0..self.variables.len() {
            let ty = AstType::Variable(i as u32);
            let x = self.resolve(&ty);
            println!("Type: {}: {:?}", i, x);
        }
    }

    pub fn unify(&mut self, a: &AstType, b: &AstType) -> Result<(), UError> {
        println!("Unify: {:?}, {:?}", a, b);
        match (a, b) {
            (AstType::Args(v1), AstType::Args(v2)) => self.unify(&*v1, &*v2),
            (AstType::Args(v), _) => self.unify(v, b),
            (_, AstType::Args(v)) => self.unify(a, v),
            (AstType::Variable(v1), AstType::Variable(v2)) => {
                let k1 = self.variables[*v1 as usize];
                let k2 = self.variables[*v2 as usize];
                self.ut.unify_var_var(k1, k2)
            }
            (AstType::Variable(v1), _) => {
                let k1 = self.variables[*v1 as usize];
                let k2 = self.ut.new_key(b.clone().into());
                self.ut.unify_var_var(k1, k2)
            }
            (_, AstType::Variable(v2)) => {
                let k1 = self.ut.new_key(a.clone().into());
                let k2 = self.variables[*v2 as usize];
                self.ut.unify_var_var(k1, k2)
            }
            (AstType::Ptr(v1), AstType::Ptr(v2)) => self.unify(&*v1, &*v2),
            (AstType::Struct(vs1), AstType::Struct(vs2)) => {
                for ((_, x), (_, y)) in vs1.iter().zip(vs2.iter()) {
                    if self.unify(x, y).is_err() {
                        return Err(UError::Bad);
                    }
                }
                Ok(())
            }
            (AstType::Func(vs1, ret1), AstType::Func(vs2, ret2)) => {
                if self.unify(ret1, ret2).is_err() {
                    return Err(UError::Bad);
                }
                for ((_, x), (_, y)) in vs1.fields().iter().zip(vs2.fields().iter()) {
                    if self.unify(x, y).is_err() {
                        return Err(UError::Bad);
                    }
                }
                Ok(())
            }
            (AstType::Struct(fields), AstType::Unit) | (AstType::Unit, AstType::Struct(fields)) => {
                if fields.len() == 0 {
                    Ok(())
                } else {
                    Err(UError::Bad)
                }
            }
            _ => {
                if a == b {
                    Ok(())
                } else {
                    Err(UError::Bad)
                }
            }
        }
    }

    pub fn resolve(&mut self, a: &AstType) -> Option<AstType> {
        match a {
            AstType::Args(v) => self.resolve(v).map(|x| AstType::Args(x.into())),
            AstType::Ptr(v) => self.resolve(v).map(|x| AstType::Ptr(x.into())),
            AstType::Struct(vs) => {
                let size = vs.len();
                let vs2 = vs
                    .into_iter()
                    .filter_map(|(_, v)| self.resolve(v).map(|x| (None, x.into())))
                    .collect::<Vec<_>>();
                if vs2.len() == size {
                    Some(AstType::Struct(vs2))
                } else {
                    None
                }
            }
            AstType::Func(args, ret) => {
                if let Some(ret) = self.resolve(ret) {
                    let fields = args.fields();
                    let size = fields.len();
                    let args2 = fields
                        .into_iter()
                        .filter_map(|(_, v)| self.resolve(&v).map(|x| x.into()))
                        .collect::<Vec<_>>();
                    if args2.len() == size {
                        Some(AstType::func(args2, ret.into()))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            AstType::Variable(offset) => {
                let k = self.variables[*offset as usize];
                let v = self.ut.probe_value(k);
                if let AstType::Variable(_) = *v {
                    None
                } else {
                    self.resolve(&v)
                }
            }
            _ => Some(a.clone()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stuff1() {
        let mut u = TypeUnify::new();

        // just unify
        let ut0 = u.fresh_unknown();
        let ut1 = u.fresh_unknown();
        let ut2 = AstType::Int;
        u.unify(&ut0, &ut1).unwrap();
        u.unify(&ut1, &ut2).unwrap();
        assert_eq!(AstType::Int, u.resolve(&ut0).unwrap());
        assert_eq!(AstType::Int, u.resolve(&ut1).unwrap());

        // unify float
        let ut3 = u.fresh_unknown();
        let ut4 = AstType::Float;
        u.unify(&ut3, &ut4).unwrap();
        assert_eq!(AstType::Float, u.resolve(&ut3).unwrap());

        // Test tuple unify
        let ut7 = u.fresh_unknown();
        let ut8 = u.fresh_unknown();
        let ut9 = u.fresh_unknown();
        let ut10 = u.fresh_unknown();
        u.unify(&ut9, &ut10).unwrap();
        let ut11 = AstType::Struct(vec![(None, ut7.0), (None, AstType::Int), (None, ut8.0)]);
        let ut12 = AstType::Struct(vec![
            (None, AstType::Float),
            (None, ut9.0.clone()),
            (None, ut10.0.clone()),
        ]);
        let ut13 = u.fresh_unknown();
        u.unify(&ut11, &ut12).unwrap();
        u.unify(&ut12, &ut13).unwrap();
        println!("ut9 {:?}", u.resolve(&ut9));
        assert_eq!(AstType::Int, u.resolve(&ut9).unwrap());
        println!("ut10 {:?}", u.resolve(&ut10));
        println!("ut11 {:?}", u.resolve(&ut11));
        println!("ut12 {:?}", u.resolve(&ut12));
        println!("ut13 {:?}", u.resolve(&ut13));
        assert_eq!(AstType::Int, u.resolve(&ut10).unwrap());
        assert_eq!(u.resolve(&ut11).unwrap(), u.resolve(&ut12).unwrap());
        assert_eq!(u.resolve(&ut11).unwrap(), u.resolve(&ut13).unwrap());

        // test ptr unify
        let ut14 = u.fresh_unknown();
        let p0 = AstType::Ptr(Box::new(ut14.0.clone()));
        let p1 = AstType::Ptr(AstType::Int.into());
        u.unify(&p0, &p1).unwrap();
        println!("{:?}", u.resolve(&ut14));
        assert_eq!(AstType::Int, u.resolve(&ut14).unwrap());

        // resolve function parameter
        let ut15 = u.fresh_unknown();
        let f0 = AstType::func(vec![AstType::Int], AstType::Int.into());
        let f1 = AstType::func(vec![AstType::Float], AstType::Float.into());
        let f2 = AstType::func(vec![ut15.0.clone()], AstType::Int.into());
        let ut16 = u.fresh_unknown();
        let ut17 = u.fresh_unknown();
        let f3 = AstType::func(vec![ut16.0.clone()], ut17.0.clone());
        assert!(u.unify(&f0, &f2).is_ok());
        assert!(u.unify(&f1, &f2).is_err());
        assert!(u.unify(&f2, &f3).is_ok());
        assert_eq!(u.resolve(&ut15), Some(AstType::Int));
        assert_eq!(u.resolve(&ut16), Some(AstType::Int));
        assert_eq!(u.resolve(&ut17), Some(AstType::Int));
    }
}
