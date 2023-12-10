use crate::ast::*;
use melior::ir;

pub struct NodeBuilder<E> {
    span: Span,
    filename: String,
    _e: std::marker::PhantomData<E>,
}

impl<E: Extra> NodeBuilder<E> {
    pub fn new(file_id: usize, filename: &str) -> Self {
        let begin = CodeLocation {
            pos: 0,
            line: 0,
            col: 0,
        };
        let end = CodeLocation {
            pos: 0,
            line: 0,
            col: 0,
        };
        let span = Span {
            file_id,
            begin,
            end,
        };
        Self {
            span,
            filename: filename.to_string(),
            _e: std::marker::PhantomData::default(),
        }
    }

    pub fn with_span(span: Span, filename: &str) -> Self {
        Self {
            span,
            filename: filename.to_string(),
            _e: std::marker::PhantomData::default(),
        }
    }

    pub fn with_loc(&mut self, span: Span) {
        //assert_eq!(span.file_id, self.span.file_id);
        self.span = span;
    }

    pub fn current_file_id(&self) -> usize {
        self.span.file_id
    }

    pub fn get_location<'c>(&self, context: &'c melior::Context) -> ir::Location<'c> {
        ir::Location::new(
            context,
            &self.filename,
            self.span.begin.line,
            self.span.begin.col,
        )
    }

    pub fn node_span(&self, ast: AstNode<E>) -> AstNode<E> {
        AstNode {
            node: ast.node,
            extra: ast.extra,
        }
    }

    pub fn node(&self, ast: Ast<E>) -> AstNode<E> {
        AstNode {
            node: ast,
            extra: E::span(self.span.clone()),
        }
    }

    pub fn extra(&self) -> E {
        let begin = CodeLocation {
            pos: 0,
            line: 0,
            col: 0,
        };
        let end = CodeLocation {
            pos: 0,
            line: 0,
            col: 0,
        };
        E::new(self.current_file_id(), begin, end)
    }

    pub fn error(&self) -> AstNode<E> {
        AstNode {
            node: Ast::Error,
            extra: self.extra(),
        }
    }

    pub fn definition(
        &self,
        name: &str,
        params: &[(&str, AstType)],
        return_type: AstType,
        body: Option<AstNode<E>>,
    ) -> AstNode<E> {
        let params = params
            .iter()
            .map(|(name, ty)| ParameterNode {
                name: name.to_string(),
                ty: ty.clone(),
                node: Parameter::Normal,
                extra: self.extra(),
            })
            .collect();
        self.node(Ast::Definition(Definition {
            name: name.to_string(),
            params,
            return_type: return_type.into(),
            body: body.map(|b| b.into()),
        }))
    }

    pub fn import_prelude(&self) -> AstNode<E> {
        self.node(Ast::Builtin(
            Builtin::Import,
            vec![self.arg(self.string("prelude"))],
        ))
    }

    pub fn prelude(&self) -> Vec<AstNode<E>> {
        vec![
            self.definition("print_index", &[("a", AstType::Int)], AstType::Unit, None),
            self.definition("print_float", &[("a", AstType::Float)], AstType::Unit, None),
        ]
    }

    pub fn string(&self, s: &str) -> AstNode<E> {
        self.node(Ast::Literal(Literal::String(s.to_string())))
    }

    pub fn integer(&self, x: i64) -> AstNode<E> {
        self.node(Ast::Literal(Literal::Int(x)))
    }

    pub fn index(&self, x: i64) -> AstNode<E> {
        self.node(Ast::Literal(Literal::Index(x as usize)))
    }

    pub fn bool(&self, x: bool) -> AstNode<E> {
        self.node(Ast::Literal(Literal::Bool(x)))
    }

    pub fn binop(&self, op: BinaryOperation, a: AstNode<E>, b: AstNode<E>) -> AstNode<E> {
        self.node(Ast::BinaryOp(op, a.into(), b.into()))
    }

    pub fn subtract(&self, a: AstNode<E>, b: AstNode<E>) -> AstNode<E> {
        self.node(Ast::BinaryOp(BinaryOperation::Subtract, a.into(), b.into()))
    }

    pub fn add(&self, a: AstNode<E>, b: AstNode<E>) -> AstNode<E> {
        self.node(Ast::BinaryOp(BinaryOperation::Add, a.into(), b.into()))
    }

    pub fn multiply(&self, a: AstNode<E>, b: AstNode<E>) -> AstNode<E> {
        self.node(Ast::BinaryOp(BinaryOperation::Multiply, a.into(), b.into()))
    }

    pub fn ne(&self, a: AstNode<E>, b: AstNode<E>) -> AstNode<E> {
        self.node(Ast::BinaryOp(BinaryOperation::NE, a.into(), b.into()))
    }

    pub fn eq(&self, a: AstNode<E>, b: AstNode<E>) -> AstNode<E> {
        self.node(Ast::BinaryOp(BinaryOperation::EQ, a.into(), b.into()))
    }

    pub fn seq(&self, nodes: Vec<AstNode<E>>) -> AstNode<E> {
        self.node(Ast::Sequence(nodes))
    }

    pub fn v(&self, name: &str) -> AstNode<E> {
        self.ident(name)
    }

    pub fn ident(&self, name: &str) -> AstNode<E> {
        AstNode {
            extra: self.extra(),
            node: Ast::Identifier(name.to_string()),
        }
    }

    pub fn deref_offset(&self, value: AstNode<E>, offset: usize) -> AstNode<E> {
        self.node(Ast::Deref(value.into(), DerefTarget::Offset(offset)))
    }

    pub fn global(&self, name: &str, value: AstNode<E>) -> AstNode<E> {
        AstNode {
            extra: value.extra.clone(),
            node: Ast::Global(name.to_string(), value.into()),
        }
    }

    pub fn test(&self, condition: AstNode<E>, body: AstNode<E>) -> AstNode<E> {
        AstNode {
            extra: body.extra.clone(),
            node: Ast::Test(condition.into(), body.into()),
        }
    }

    pub fn while_loop(&self, condition: AstNode<E>, body: AstNode<E>) -> AstNode<E> {
        self.node(Ast::While(condition.into(), body.into()))
    }

    pub fn func(
        &self,
        name: &str,
        params: &[(&str, AstType)],
        return_type: AstType,
        body: AstNode<E>,
    ) -> AstNode<E> {
        self.definition(name, params, return_type, Some(body))
    }

    pub fn ret(&self, node: Option<AstNode<E>>) -> AstNode<E> {
        AstNode::new(Ast::Return(node.map(|n| n.into())), self.extra())
    }

    pub fn arg(&self, node: AstNode<E>) -> Argument<E> {
        node.into()
    }

    pub fn apply(&self, name: &str, args: Vec<Argument<E>>) -> AstNode<E> {
        //let args = args
        //.into_iter()
        //.map(|expr| self.arg(expr))
        //.collect::<Vec<_>>();
        AstNode::new(Ast::Call(self.ident(name).into(), args), self.extra())
    }

    pub fn call(&self, f: AstNode<E>, args: Vec<Argument<E>>) -> AstNode<E> {
        //let args = args
        //.into_iter()
        //.map(|expr| self.arg(expr))
        //.collect::<Vec<_>>();
        let extra = f.extra.clone();
        AstNode::new(Ast::Call(f.into(), args), extra)
    }

    pub fn main(&self, body: AstNode<E>) -> AstNode<E> {
        self.func("main", &[], AstType::Int, body)
    }

    pub fn mutate(&self, lhs: AstNode<E>, rhs: AstNode<E>) -> AstNode<E> {
        let extra = lhs.extra.clone();
        AstNode::new(Ast::Mutate(lhs.into(), rhs.into()), extra)
    }

    pub fn assign(&self, name: &str, rhs: AstNode<E>) -> AstNode<E> {
        self.node(Ast::Assign(
            AssignTarget::Identifier(name.to_string()),
            rhs.into(),
        ))
    }

    pub fn alloca(&self, name: &str, rhs: AstNode<E>) -> AstNode<E> {
        self.node(Ast::Assign(
            AssignTarget::Alloca(name.to_string()),
            rhs.into(),
        ))
    }

    pub fn cond(
        &self,
        condition: AstNode<E>,
        then: AstNode<E>,
        else_block: Option<AstNode<E>>,
    ) -> AstNode<E> {
        self.node(Ast::Conditional(
            condition.into(),
            then.into(),
            else_block.map(|x| x.into()),
        ))
    }

    pub fn try_string(&self, expr: &AstNode<E>) -> Option<String> {
        if let Ast::Literal(Literal::String(s)) = &expr.node {
            Some(s.clone())
        } else {
            None
        }
    }
}
