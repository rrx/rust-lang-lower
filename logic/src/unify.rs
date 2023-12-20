use ena::unify::*;

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
struct IntKey(u32);

#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum Type {
    Int,
    Float,
    Seq(Vec<Type>),
    Var(usize),
}
impl Type {
    fn unknown(&self) -> Option<usize> {
        if let Self::Var(s) = self {
            Some(*s)
        } else {
            None
        }
    }
}

impl UnifyKey for IntKey {
    type Value = Type;
    fn index(&self) -> u32 {
        self.0
    }
    fn from_index(u: u32) -> IntKey {
        IntKey(u)
    }
    fn tag() -> &'static str {
        "IntKey"
    }
    fn order_roots(a: IntKey, a_rank: &Type, b: IntKey, b_rank: &Type) -> Option<(IntKey, IntKey)> {
        //println!("{:?} vs {:?}", a_rank, b_rank);
        if a_rank > b_rank {
            Some((a, b))
        } else if b_rank > a_rank {
            Some((b, a))
        } else {
            None
        }
    }
}

enum UError {
    Bad,
}

impl UnifyValue for Type {
    type Error = UError;

    fn unify_values(value1: &Self, value2: &Self) -> Result<Self, UError> {
        let id1 = value1.unknown();
        let id2 = value2.unknown();
        match (id1, id2) {
            (None, None) => match (value1, value2) {
                (Type::Seq(c1), Type::Seq(c2)) => {
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
                            Ok(Type::Seq(result))
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
            (Some(_), Some(_)) => Ok(value1.clone()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test<
        S: Clone + Default + UnificationStore<Key = IntKey, Value = <IntKey as UnifyKey>::Value>,
    >() {
        let mut ut: UnificationTable<S> = UnificationTable::new();
        let start = ut.snapshot();
        let k1 = ut.new_key(Type::Var(1));
        let k2 = ut.new_key(Type::Var(0));
        let k3 = ut.new_key(Type::Int);
        let k4 = ut.new_key(Type::Float);
        let k5 = ut.new_key(Type::Var(2));
        let k6 = ut.new_key(Type::Var(3));
        let k7 = ut.new_key(Type::Var(4));
        let k8 = ut.new_key(Type::Seq(vec![Type::Var(5), Type::Int, Type::Var(7)]));
        let k9 = ut.new_key(Type::Seq(vec![Type::Float, Type::Var(6), Type::Var(7)]));
        assert!(ut.unify_var_var(k2, k1).is_ok());
        assert!(ut.unify_var_var(k2, k3).is_ok());
        assert!(ut.unify_var_var(k4, k5).is_ok());
        assert!(ut.unify_var_var(k6, k7).is_ok());
        assert!(ut.unify_var_var(k8, k9).is_ok());
        //assert!(ut.unify_var_var(k3, k4).is_ok());
        //assert!(ut.unify_var_value(k1, OrderedRank(3)).is_ok());
        //ut.union(k1, k2);
        println!("{:?}", ut.vars_since_snapshot(&start));
        //for k in ut.vars_since_snapshot(&start)) {
        //println!("{} => {:?}", k, ut.probe_value(k));
        //}
        println!("{:?}", ut.probe_value(k1));
        println!("{:?}", ut.probe_value(k6));
        println!("{:?}", ut.probe_value(k7));
        println!("{:?}", ut.probe_value(k8));
        println!("{:?}", ut.probe_value(k9));
    }

    #[test]
    fn test_stuff() {
        test::<InPlace<IntKey>>();
    }
}
