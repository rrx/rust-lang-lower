use crate::StringKey;
use anyhow::Result;
use ena::unify::*;
//use std::collections::HashMap;
use thiserror::Error;

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct IntKey(u32);

#[derive(Debug, Error)]
pub enum UError {
    #[error("Bad")]
    Bad,
}

//#[derive(Debug, PartialEq, Clone)]
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AstType {
    //Number,
    Int,
    Index,
    String,
    Float,
    Bool,
    Unit,
    Never,
    Type,
    Ptr(Box<AstType>),
    Tuple(Vec<AstType>),
    NamedTuple(Vec<(StringKey, AstType)>),
    // Func(parameters, return type)
    Func(Vec<AstType>, Box<AstType>),
    Variable(u32),
}

impl std::fmt::Display for AstType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl AstType {
    pub fn unknown(id: u32) -> Self {
        Self::Variable(id)
    }

    pub fn is_unknown(&self) -> bool {
        match self {
            Self::Ptr(ty) => ty.is_unknown(),
            Self::Tuple(values) => {
                for a in values {
                    if a.is_unknown() {
                        return true;
                    }
                }
                false
            }
            Self::Func(args, ret) => {
                if ret.is_unknown() {
                    return true;
                }

                for a in args {
                    if a.is_unknown() {
                        return true;
                    }
                }
                false
            }
            Self::Variable(_) => true,
            _ => false,
        }
    }

    pub fn to_ptr(self) -> Self {
        Self::Ptr(self.into())
    }

    pub fn is_ptr(&self) -> bool {
        if let Self::Ptr(_) = self {
            true
        } else {
            false
        }
    }

    fn try_unknown(&self) -> Option<u32> {
        if let Self::Variable(s) = self {
            Some(*s)
        } else {
            None
        }
    }

    fn children(&self) -> Vec<&AstType> {
        match self {
            Self::Ptr(v) => vec![v],
            _ => unimplemented!(),
        }
    }
}

/*
#[derive(Default)]
pub struct TypeBuilder {
    types: HashMap<SymIndex, (AstType, VarDefinitionSpace)>,
}

impl TypeBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn lookup_type(&self, index: SymIndex) -> Option<(AstType, VarDefinitionSpace)> {
        self.types.get(&index).cloned()
    }

    pub fn set_type(&mut self, index: SymIndex, ty: AstType, mem: VarDefinitionSpace) {
        self.types.insert(index, (ty, mem));
    }
}
*/

impl UnifyKey for IntKey {
    type Value = AstType;
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
        a_rank: &AstType,
        b: IntKey,
        b_rank: &AstType,
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

impl UnifyValue for AstType {
    type Error = UError;

    fn unify_values(value1: &Self, value2: &Self) -> Result<Self, UError> {
        let id1 = value1.try_unknown();
        let id2 = value2.try_unknown();
        match (id1, id2) {
            (None, None) => match (value1, value2) {
                //(Self::Int, Self::Float) | (Self::Float, Self::Int) => {
                //Ok(Self::Number)
                //}
                (Self::Ptr(v1), Self::Ptr(v2)) => {
                    let ty = Self::unify_values(v1, v2)?;
                    Ok(Self::Ptr(ty.into()))
                }
                (AstType::Func(c1, r1), AstType::Func(c2, r2)) => {
                    let r = Self::unify_values(r1, r2)?;
                    if c1.len() != c2.len() {
                        Err(UError::Bad)
                    } else {
                        let result = c1
                            .iter()
                            .zip(c2.iter())
                            .map_while(|(a, b)| match Self::unify_values(a, b) {
                                Ok(s) => Some(s),
                                Err(_) => None,
                            })
                            .collect::<Vec<_>>();
                        if result.len() == c1.len() {
                            Ok(AstType::Func(result, r.into()))
                        } else {
                            Err(UError::Bad)
                        }
                    }
                }
                (AstType::Tuple(c1), AstType::Tuple(c2)) => {
                    if c1.len() != c2.len() {
                        Err(UError::Bad)
                    } else {
                        let result = c1
                            .iter()
                            .zip(c2.iter())
                            .map_while(|(a, b)| match Self::unify_values(a, b) {
                                Ok(s) => Some(s),
                                Err(_) => None,
                            })
                            .collect::<Vec<_>>();
                        if result.len() == c1.len() {
                            Ok(AstType::Tuple(result))
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
            (Some(a), Some(_)) => Ok(Self::Variable(a)),
        }
    }
}

pub type TypeUnifyTable = UnificationTable<InPlace<IntKey>>;

/*
impl AstType {
    pub fn probe(self, ut: &TypeUnifyTable) -> Self {
        match self {
            Self::Ptr(v) => Self::Ptr(v.probe(ut).into()),
            Self::Tuple(vs) => {
                let vs = vs.into_iter().map(|v| v.probe(ut).into()).collect();
                Self::Tuple(vs)
            }
            Self::Func(args, ret) => {
                let ret = ret.probe(ut);
                let args = args.into_iter().map(|v| v.probe(ut).into()).collect();
                Self::Func(args, ret.into())
            }
            //Self::Variable(_) => self
            _ => self
        }
    }
}
*/

pub struct TypeUnify {
    ut: TypeUnifyTable,
    unknown_count: u32,
    variables: Vec<IntKey>,
}

impl TypeUnify {
    pub fn new() -> Self {
        Self {
            ut: TypeUnifyTable::new(),
            unknown_count: 0,
            variables: vec![],
        }
    }

    pub fn fresh_unknown(&mut self) -> AstType {
        let offset = self.variables.len();
        let r = AstType::Variable(offset as u32);
        self.variables.push(self.ut.new_key(r.clone()));
        r
    }

    fn add_var(&mut self, a: AstType) -> IntKey {
        match a {
            AstType::Variable(v) => self.variables[v as usize],
            _ => self.ut.new_key(a),
        }
    }

    pub fn unify(&mut self, a: &AstType, b: &AstType) -> Result<(), UError> {
        match (a, b) {
            (AstType::Variable(v1), AstType::Variable(v2)) => {
                let k1 = self.variables[*v1 as usize];
                let k2 = self.variables[*v2 as usize];
                self.ut.unify_var_var(k1, k2)
            }
            (AstType::Variable(v1), _) => {
                let k1 = self.variables[*v1 as usize];
                let k2 = self.ut.new_key(b.clone());
                self.ut.unify_var_var(k1, k2)
            }
            (_, AstType::Variable(v2)) => {
                let k1 = self.ut.new_key(a.clone());
                let k2 = self.variables[*v2 as usize];
                self.ut.unify_var_var(k1, k2)
            }
            (AstType::Ptr(v1), AstType::Ptr(v2)) => self.unify(&*v1, &*v2),
            (AstType::Tuple(vs1), AstType::Tuple(vs2)) => {
                for (x, y) in vs1.iter().zip(vs2.iter()) {
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
                for (x, y) in vs1.iter().zip(vs2.iter()) {
                    if self.unify(x, y).is_err() {
                        return Err(UError::Bad);
                    }
                }
                Ok(())
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

    pub fn resolve(&mut self, a: AstType) -> Option<AstType> {
        match a {
            AstType::Ptr(v) => self.resolve(*v).map(|x| AstType::Ptr(x.into())),
            AstType::Tuple(vs) => {
                let size = vs.len();
                let vs2 = vs
                    .into_iter()
                    .filter_map(|v| self.resolve(v).map(|x| x.into()))
                    .collect::<Vec<_>>();
                if vs2.len() == size {
                    Some(AstType::Tuple(vs2))
                } else {
                    None
                }
            }
            AstType::Func(args, ret) => {
                if let Some(ret) = self.resolve(*ret) {
                    let size = args.len();
                    let args2 = args
                        .into_iter()
                        .filter_map(|v| self.resolve(v).map(|x| x.into()))
                        .collect::<Vec<_>>();
                    if args2.len() == size {
                        Some(AstType::Func(args2, ret.into()))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            AstType::Variable(offset) => {
                let k = self.variables[offset as usize];
                let v = self.ut.probe_value(k);
                if let AstType::Variable(_) = v {
                    None
                } else {
                    self.resolve(v)
                }
            }
            _ => Some(a),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stuff1() {
        let mut u = TypeUnify::new();
        let ut0 = u.fresh_unknown();
        let ut1 = u.fresh_unknown();
        let ut2 = AstType::Int;
        u.unify(&ut0, &ut1).unwrap();
        u.unify(&ut1, &ut2).unwrap();
        assert_eq!(AstType::Int, u.resolve(ut0).unwrap());
        assert_eq!(AstType::Int, u.resolve(ut1).unwrap());

        let ut3 = u.fresh_unknown();
        let ut4 = AstType::Float;
        u.unify(&ut3, &ut4).unwrap();

        let ut5 = u.fresh_unknown();
        let ut6 = u.fresh_unknown();
        u.unify(&ut5, &ut6).unwrap();

        let ut7 = u.fresh_unknown();
        let ut8 = u.fresh_unknown();
        let ut9 = u.fresh_unknown();
        let ut10 = u.fresh_unknown();
        u.unify(&ut9, &ut10).unwrap();
        let ut11 = AstType::Tuple(vec![ut7, AstType::Int, ut8]);
        let ut12 = AstType::Tuple(vec![AstType::Float, ut9.clone(), ut10.clone()]);
        let ut13 = u.fresh_unknown();
        u.unify(&ut11, &ut12).unwrap();
        u.unify(&ut12, &ut13).unwrap();
        println!("ut9 {:?}", u.resolve(ut9));
        println!("ut10 {:?}", u.resolve(ut10));
        println!("ut11 {:?}", u.resolve(ut11));
        println!("ut12 {:?}", u.resolve(ut12));
        println!("ut13 {:?}", u.resolve(ut13));

        let ut14 = u.fresh_unknown();
        let p0 = AstType::Ptr(ut14.clone().into());
        let p1 = AstType::Ptr(AstType::Int.into());
        u.unify(&p0, &p1).unwrap();
        println!("{:?}", u.resolve(ut14));

        let ut15 = u.fresh_unknown();
        let f0 = AstType::Func(vec![AstType::Int], AstType::Int.into());
        let f1 = AstType::Func(vec![AstType::Float], AstType::Float.into());
        let f2 = AstType::Func(vec![ut15.clone()], AstType::Int.into());

        let ut16 = u.fresh_unknown();
        let f3 = AstType::Func(vec![ut16.clone()], ut16.clone().into());
        assert!(u.unify(&f0, &f2).is_ok());
        assert!(u.unify(&f1, &f2).is_err());
        assert!(u.unify(&f2, &f3).is_ok());
        assert_eq!(u.resolve(ut15), Some(AstType::Int));
        assert_eq!(u.resolve(ut16), Some(AstType::Int));
    }

    #[test]
    fn test_stuff2() {
        let mut ut = TypeUnifyTable::new();
        //let start = ut.snapshot();
        let k1 = ut.new_key(AstType::unknown(1));
        let k2 = ut.new_key(AstType::unknown(0));
        ut.unify_var_var(k1, k2).unwrap();
        let k3 = ut.new_key(AstType::Int);
        ut.unify_var_var(k2, k3).unwrap();

        let k4 = ut.new_key(AstType::Float);
        let ut2 = ut.new_key(AstType::unknown(2));
        ut.unify_var_var(k4, ut2).unwrap();

        let x3 = ut.new_key(AstType::unknown(3));
        let x4 = ut.new_key(AstType::unknown(4));
        ut.unify_var_var(x3, x4).unwrap();

        let ut7 = AstType::unknown(7);
        let ut8 = AstType::unknown(8);
        let k7 = ut.new_key(ut7.clone());
        let k8 = ut.new_key(ut8.clone());
        ut.unify_var_value(k8, AstType::Float).unwrap();
        let kt0 = ut.new_key(AstType::Tuple(vec![AstType::unknown(5), AstType::Int, ut7]));
        let kt1 = ut.new_key(AstType::Tuple(vec![
            AstType::Float,
            AstType::unknown(6),
            ut8,
        ]));
        ut.unify_var_var(kt0, kt1).unwrap();
        ut.unify_var_var(k7, k8).unwrap();

        let ut9 = AstType::unknown(9);
        let ut10 = AstType::unknown(10);
        let k9 = ut.new_key(ut9.clone());
        let k10 = ut.new_key(ut10.clone());
        let p0 = ut.new_key(AstType::Ptr(ut9.clone().into()));
        let p1 = ut.new_key(AstType::Ptr(ut10.into()));
        ut.unify_var_var(p0, p1).unwrap();
        let p2 = ut.new_key(AstType::Ptr(AstType::Float.into()));
        ut.unify_var_var(p1, p2).unwrap();
        let p3 = ut.new_key(AstType::Ptr(ut9.clone().into()));
        ut.unify_var_var(p2, p3).unwrap();

        let f0 = ut.new_key(AstType::Func(vec![AstType::Int], AstType::Int.into()));
        let f1 = ut.new_key(AstType::Func(vec![AstType::Float], AstType::Float.into()));
        let ut11 = AstType::Func(vec![AstType::unknown(11)], AstType::Int.into());
        let f2 = ut.new_key(ut11);
        assert!(ut.unify_var_var(f0, f2).is_ok());
        assert!(ut.unify_var_var(f1, f2).is_err());
        //ut.vars_since_snapshot(&start)
        //assert!(ut.unify_var_var(k2, k1).is_ok());
        //assert!(ut.unify_var_var(k2, k3).is_ok());
        //assert!(ut.unify_var_var(k4, k5).is_ok());
        //assert!(ut.unify_var_var(k6, k7).is_ok());
        //assert!(ut.unify_var_var(k8, k9).is_ok());
        //assert_eq!(ut.probe_value(k8), AstType::Tuple(vec![AstType::Float, AstType::Int, AstType::Int]));

        //assert!(ut.unify_var_var(k3, k4).is_ok());
        //assert!(ut.unify_var_value(k1, OrderedRank(3)).is_ok());
        //ut.union(k1, k2);
        //println!("{:?}", ut.vars_since_snapshot(&start));
        //for k in ut.vars_since_snapshot(&start)) {
        //println!("{} => {:?}", k, ut.probe_value(k));
        //}

        println!("{:?}", ut.probe_value(k1));
        println!("{:?}", ut.probe_value(x3));
        println!("{:?}", ut.probe_value(x4));
        println!("{:?}", ut.probe_value(kt0));
        println!("{:?}", ut.probe_value(kt1));
        println!("k7 {:?}", ut.probe_value(k7));
        println!("k8 {:?}", ut.probe_value(k8));
        println!("p0 {:?}", ut.probe_value(p0));
        println!("p1 {:?}", ut.probe_value(p1));
        println!("p2 {:?}", ut.probe_value(p2));
        println!("p3 {:?}", ut.probe_value(p3));
        println!("k9 {:?}", ut.probe_value(k9));
        println!("k10 {:?}", ut.probe_value(k10));
        println!("kt0 {:?}", ut.probe_value(kt0));
        println!("kt1 {:?}", ut.probe_value(kt1));
        println!("f2 {:?}", ut.probe_value(f2));

        assert_eq!(ut.probe_value(p0), AstType::Ptr(AstType::Float.into()));
        //assert_eq!(ut.probe_value(p0).is_unknown(), false);
        //assert_eq!(ut.probe_value(p1).is_unknown(), false);
        assert!(ut.probe_value(k1).try_unknown().is_none());
        assert!(ut.probe_value(ut2).try_unknown().is_none());
        //assert!(ut.probe_value(x3).try_unknown().is_none());
        //assert!(ut.probe_value(x4).try_unknown().is_none());
    }
}
