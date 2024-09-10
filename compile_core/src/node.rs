use crate::{Argument, Ast, Literal, SpanId};

#[derive(Debug, Clone)]
pub struct AstNode {
    pub node: Ast,
    pub span_id: SpanId,
}

impl AstNode {
    pub fn try_string(&self) -> Option<String> {
        if let Ast::Literal(Literal::String(s)) = &self.node {
            Some(s.clone())
        } else {
            None
        }
    }

    /*
    pub fn is_block(&self) -> bool {
        if let Ast::Block(_nb) = &self.node {
            true
        } else {
            false
        }
    }

    pub fn try_block(self) -> Option<Vec<AstNode<E>>> {
        if let Ast::Block(nb) = self.node {
            Some(nb.children)
        } else {
            None
        }
    }
    */

    pub fn is_seq(&self) -> bool {
        if let Ast::Sequence(_) = self.node {
            true
        } else {
            false
        }
    }

    pub fn try_seq(self) -> Option<Vec<AstNode>> {
        if let Ast::Sequence(seq) = self.node {
            Some(seq)
        } else {
            None
        }
    }

    pub fn to_vec(self) -> Vec<AstNode> {
        match self.node {
            Ast::Sequence(exprs) => exprs
                .into_iter()
                .map(|expr| expr.to_vec())
                .flatten()
                .collect(),
            _ => vec![self],
        }
    }

    pub fn to_vec_ref(&self) -> Vec<&AstNode> {
        match self.node {
            Ast::Sequence(ref exprs) => exprs
                .iter()
                .map(|expr| expr.to_vec_ref())
                .flatten()
                .collect(),
            _ => vec![self],
        }
    }

    pub fn make_yield(node: Self) -> Self {
        // the last element should be yielded
        if let Ast::Yield(_) = &node.node {
            return node;
        }

        let span_id = node.span_id;
        Ast::Yield(Some(node.into())).node(span_id)
    }

    pub fn append(self, node: Self) -> Self {
        // we should merge spans here to be correct
        let span_id = self.span_id;
        if let Ast::Sequence(mut seq) = self.node {
            seq.push(node);
            Self {
                node: Ast::Sequence(seq),
                span_id,
            }
        } else {
            let seq = vec![self, node];
            Self {
                node: Ast::Sequence(seq),
                span_id,
            }
        }
    }

    pub fn children_mut<'a>(&'a mut self) -> AstNodeIterator<'a> {
        let mut values = vec![];
        match &mut self.node {
            Ast::Sequence(ref mut exprs) => {
                for e in exprs.iter_mut() {
                    values.push(e);
                }
            }
            Ast::Lambda(def) => {
                if let Some(ref mut body) = def.body {
                    values.push(body);
                }
            }
            Ast::BinaryOp(_, a, b) | Ast::While(a, b) => {
                values.push(a);
                values.push(b);
            }
            Ast::UnaryOp(_, a) | Ast::Assign(_, a) | Ast::Loop(_, a) => {
                values.push(a);
            }
            Ast::Call(f, args, _ty) => {
                values.push(f);
                for a in args {
                    match a {
                        Argument::Positional(expr) => values.push(expr),
                        Argument::Named(_, expr) => values.push(expr),
                        _ => unimplemented!(),
                    }
                }
            }
            Ast::Global(_, body) => {
                values.push(body);
            }
            Ast::Conditional(a, b, c) => {
                values.push(a);
                values.push(b);
                if let Some(c) = c {
                    values.push(c);
                }
            }
            Ast::Return(a) => {
                if let Some(a) = a {
                    values.push(a);
                }
            }
            Ast::Module(_name, ref mut body) => {
                values.push(body);
            }
            Ast::Builtin(_, args) => {
                for a in args {
                    match a {
                        Argument::Positional(expr) => values.push(expr),
                        Argument::Named(_, expr) => values.push(expr),
                        _ => unimplemented!(),
                    }
                }
            }
            _ => (),
        }
        AstNodeIterator { values }
    }
}

pub struct AstNodeIterator<'a> {
    values: Vec<&'a mut AstNode>,
}

impl<'a> Iterator for AstNodeIterator<'a> {
    type Item = &'a mut AstNode;
    fn next(&mut self) -> Option<Self::Item> {
        self.values.pop()
    }
}

impl From<Argument> for AstNode {
    fn from(item: Argument) -> Self {
        item.expr()
    }
}

impl From<Ast> for AstNode {
    fn from(ast: Ast) -> Self {
        Self {
            node: ast,
            span_id: SpanId::unknown(),
        }
    }
}

impl From<i64> for AstNode {
    fn from(i: i64) -> Self {
        Ast::Literal(Literal::Int(i)).into()
    }
}

impl From<&str> for AstNode {
    fn from(s: &str) -> Self {
        Ast::Literal(Literal::String(s.to_string())).into()
    }
}

impl From<bool> for AstNode {
    fn from(b: bool) -> Self {
        Ast::Literal(Literal::Bool(b)).into()
    }
}
