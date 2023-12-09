use crate::ast::*;
use melior::ir;

pub struct NodeBuilder<E> {
    file_ids: Vec<(usize, String)>,
    begin: CodeLocation,
    end: CodeLocation,
    _e: std::marker::PhantomData<E>,
}

impl<E: Extra> NodeBuilder<E> {
    pub fn new(file_id: usize, filename: &str) -> Self {
        let begin = CodeLocation { line: 0, col: 0 };
        let end = CodeLocation { line: 0, col: 0 };
        Self {
            file_ids: vec![(file_id, filename.to_string())],
            begin,
            end,
            _e: std::marker::PhantomData::default(),
        }
    }

    pub fn enter_file(&mut self, file_id: usize, filename: &str) {
        self.file_ids.push((file_id, filename.to_string()));
    }

    pub fn location(&mut self) {
        self.begin = CodeLocation { line: 0, col: 0 };
        self.end = CodeLocation { line: 0, col: 0 };
    }

    pub fn exit_file(&mut self) {
        self.file_ids.pop().unwrap();
    }

    pub fn current_file_id(&self) -> usize {
        self.file_ids.last().unwrap().0
    }

    pub fn get_location<'c>(&self, context: &'c melior::Context) -> ir::Location<'c> {
        ir::Location::new(
            context,
            &self.file_ids.last().unwrap().1,
            self.begin.line,
            self.begin.col,
        )
    }

    pub fn node(&self, ast: Ast<E>) -> AstNode<E> {
        AstNode {
            node: ast,
            extra: E::new(self.current_file_id(), self.begin.clone(), self.end.clone()),
        }
    }

    pub fn extra(&self) -> E {
        let begin = CodeLocation { line: 0, col: 0 };
        let end = CodeLocation { line: 0, col: 0 };
        E::new(self.current_file_id(), begin, end)
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
                node: Parameter::Normal(name.to_string(), ty.clone()),
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

    pub fn prelude(&self) -> Vec<AstNode<E>> {
        vec![
            self.definition("print_index", &[("a", AstType::Int)], AstType::Unit, None),
            self.definition("print_float", &[("a", AstType::Float)], AstType::Unit, None),
        ]
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

    pub fn ident(&self, name: &str) -> AstNode<E> {
        self.node(Ast::Identifier(name.to_string()))
    }

    pub fn deref_offset(&self, value: AstNode<E>, offset: usize) -> AstNode<E> {
        self.node(Ast::Deref(value.into(), DerefTarget::Offset(offset)))
    }

    pub fn global(&self, name: &str, value: AstNode<E>) -> AstNode<E> {
        self.node(Ast::Global(name.to_string(), value.into()))
    }

    pub fn test(&self, condition: AstNode<E>, body: AstNode<E>) -> AstNode<E> {
        self.node(Ast::Test(condition.into(), body.into()))
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
        self.node(Ast::Return(node.map(|n| n.into())))
    }

    pub fn apply(&self, name: &str, args: Vec<AstNode<E>>) -> AstNode<E> {
        let args = args
            .into_iter()
            .map(|expr| Argument::Positional(expr.into()))
            .collect::<Vec<_>>();
        self.node(Ast::Call(self.ident(name).into(), args))
    }

    pub fn main(&self, body: AstNode<E>) -> AstNode<E> {
        self.func("main", &[], AstType::Int, body)
    }

    pub fn replace(&self, name: &str, rhs: AstNode<E>) -> AstNode<E> {
        self.node(Ast::Replace(
            AssignTarget::Identifier(name.to_string()),
            rhs.into(),
        ))
    }

    pub fn mutate(&self, lhs: AstNode<E>, rhs: AstNode<E>) -> AstNode<E> {
        self.node(Ast::Mutate(lhs.into(), rhs.into()))
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
}
