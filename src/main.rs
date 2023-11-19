
use std::path::Path;
use std::error::Error;
use std::fs::File;
use std::io::Write;
use std::ops::Deref;
use std::fmt::Debug;

use melior::{
    Context,
    dialect::{arith, DialectRegistry, func},
    ir::{*, attribute::{StringAttribute, TypeAttribute}, r#type::FunctionType},
    utility::{register_all_dialects, register_all_llvm_translations},
};

use starlark_syntax::syntax;
use starlark_syntax::syntax::{Dialect};
use starlark_syntax::lexer;
use starlark_syntax::syntax::module::AstModuleFields;
use starlark_syntax::codemap;
use starlark_syntax::codemap::CodeMap;

/*
function fibonacci(a, b, n) {
if (n === 0) {
return a;
}

if (n === 1) {
return b;
}

return fibonacci(b, a + b, n - 1);
}

x1(x) => x+1
// increment by 1
int main() {
  return x1(4);

*/

#[derive(Debug)]
pub enum Literal {
    Int(i64),
    Float(f64),
}


#[derive(Debug)]
pub enum BinaryOperation {
    Add,
    Subtract,
    Equal
}

impl From<syntax::ast::BinOp> for BinaryOperation {
    fn from(item: syntax::ast::BinOp) -> Self {
        use syntax::ast::BinOp;
        match item {
            BinOp::Add => BinaryOperation::Add,
            BinOp::Subtract => BinaryOperation::Subtract,
            BinOp::Equal => BinaryOperation::Equal,
            _ => unimplemented!()
        }
    }
}

#[derive(Debug)]
pub enum Argument<P> {
    Positional(Box<AstNode<P>>)
}

impl<E: Extra> Argument<E> {
    fn from<P: syntax::ast::AstPayload>(item: syntax::ast::AstArgumentP<P>, context: &Context, codemap: &CodeMap) -> Self {
        use syntax::ast::ArgumentP;
        match item.node {
            ArgumentP::Positional(expr) => Argument::Positional(Box::new(AstNode::from_expr(expr, context, codemap))),
            _ => unimplemented!()
        }
    }
}

#[derive(Debug)]
pub enum Parameter<E> {
    Normal(String),
    Dummy(AstNode<E>)
}

impl<E: Extra> Parameter<E> {
    fn from<P: syntax::ast::AstPayload>(item: syntax::ast::AstParameterP<P>, context: &Context, codemap: &CodeMap) -> Self {
        use syntax::ast::ParameterP;
        match item.node {
            ParameterP::Normal(ident, maybe_type) => Parameter::Normal(ident.node.ident),
            _ => unimplemented!()
        }
    }
}

#[derive(Debug)]
pub struct Definition<E> {
    pub name: String,
    pub params: Vec<Parameter<E>>,
    //pub return_type: Option<Box<AstTypeExprP<P>>>,
    pub body: Box<AstNode<E>>,
    //pub payload: P::DefPayload,
}

#[derive(Debug)]
pub enum Ast<E> {
    BinaryOp(BinaryOperation, Box<AstNode<E>>, Box<AstNode<E>>),
    Call(Box<AstNode<E>>, Vec<Argument<E>>),
    Identifier(String),
    Literal(Literal),
    Sequence(Vec<AstNode<E>>),
    Definition(Definition<E>),
    Assign(AssignTarget, Box<AstNode<E>>),
    Conditional(Box<AstNode<E>>, Box<AstNode<E>>, Option<Box<AstNode<E>>>),
    Return(Option<Box<AstNode<E>>>),
}

#[derive(Debug)]
pub struct CodeLocation {
    line: usize,
    col: usize
}

#[derive(Debug)]
pub struct SimpleExtra {
    span: Span
}

impl Extra for SimpleExtra {
    fn new(begin: CodeLocation, end: CodeLocation ) -> Self {
        Self { span: Span { begin, end } }
    }
    fn location<'c> (&self, context: &'c Context, codemap: &CodeMap) -> Location<'c> {
        Location::new(context, codemap.filename(), self.span.begin.line, self.span.begin.col)
    }
}

trait Extra: Debug {
    fn new(begin: CodeLocation, end: CodeLocation ) -> Self;
    fn location<'c>(&self, context: &'c Context, codemap: &CodeMap) -> Location<'c>;
}

#[derive(Debug)]
pub struct Span {
    begin: CodeLocation,
    end: CodeLocation,
}

#[derive(Debug)]
pub struct AstNode<E> {
    node: Ast<E>,
    extra: E,
}

#[derive(Debug)]
pub enum AssignTarget {
    Identifier(String)
}
impl<P: syntax::ast::AstPayload> From<syntax::ast::AssignTargetP<P>> for AssignTarget {
    fn from(item: syntax::ast::AssignTargetP<P>) -> Self {
        use syntax::ast::AssignTargetP;
        match item {
            AssignTargetP::Identifier(ident) => AssignTarget::Identifier(ident.node.ident),
            _ => unimplemented!()
        }
    }
}

//impl<E: Extra> Ast<E> {
    //fn node(self, begin: CodeLocation, end: CodeLocation ) -> AstNode {
        //AstNode { node: self, extra: extrabegin, end }
    //}
//}
impl<E: Extra> AstNode<E> {
    fn from_stmt<P: syntax::ast::AstPayload>(
        item: syntax::ast::AstStmtP<P>,
        context: &Context,
        codemap: &CodeMap) -> Self {
        use syntax::ast::StmtP;
        use syntax::ast::ParameterP;

        let r = codemap.resolve_span(item.span);
        let begin = CodeLocation { line: r.begin.line, col: r.begin.column};
        let end = CodeLocation { line: r.end.line, col: r.end.column};

        match item.node {
            StmtP::Statements(stmts) => {
                let exprs = stmts.into_iter().map(|stmt| AstNode::from_stmt(stmt, context, codemap)).collect::<Vec<AstNode<E>>>();
                let ast = Ast::Sequence(exprs);
                AstNode { node: ast, extra: E::new(begin, end) }
            }

            StmtP::Def(def) => {
                let d = Definition {
                    name: def.name.ident.clone(),
                    body: Box::new(AstNode::from_stmt(*def.body, context, codemap)),
                    params: vec![],
                };
                let ast = Ast::Definition(d);
                AstNode { node: ast, extra: E::new(begin, end) }
            }

            StmtP::IfElse(expr, options) => {
                let condition = AstNode::from_expr(expr, context, codemap);
                let truestmt = AstNode::from_stmt(options.0, context, codemap);
                let elsestmt = Some(Box::new(AstNode::from_stmt(options.1, context, codemap)));
                AstNode { node: Ast::Conditional(condition.into(), truestmt.into(), elsestmt), extra: E::new(begin, end) }
            }

            StmtP::Return(maybe_expr) => {
                let expr = maybe_expr.map(|x| {
                    Box::new(AstNode::from_expr(x, context, codemap))
                });
                AstNode { node: Ast::Return(expr.into()), extra: E::new(begin, end) }
            }

            StmtP::Assign(assign) => {
                let rhs = AstNode::from_expr(assign.rhs, context, codemap);
                let target: AssignTarget = assign.lhs.node.into();
                AstNode { node: Ast::Assign(target, Box::new(rhs)), extra: E::new(begin, end) }
            }

            StmtP::Expression(expr) => {
                AstNode::from_expr(expr, context, codemap)
            }


            _ => unimplemented!()
        }
    }
}

impl<E: Extra> AstNode<E> {
    fn from_expr<P: syntax::ast::AstPayload>(
        item: syntax::ast::AstExprP<P>,
        context: &Context,
        codemap: &CodeMap) -> Self {
        use syntax::ast::ExprP;
        let r = codemap.resolve_span(item.span);
        let begin = CodeLocation { line: r.begin.line, col: r.begin.column};
        let end = CodeLocation { line: r.end.line, col: r.end.column};

        match item.node {
            ExprP::Op(lhs, op, rhs) => {
                let ast = Ast::BinaryOp(
                    op.into(),
                    Box::new(AstNode::from_expr(*lhs, context, codemap)),
                    Box::new(AstNode::from_expr(*rhs, context, codemap)),
                    );
                //.node(begin, end)
                AstNode { node: ast, extra: E::new(begin, end) }
            }
            ExprP::Call(expr, args) => {
                let args = args.into_iter().map(|arg| Argument::from(arg, context, codemap)).collect::<Vec<Argument<E>>>();
                let ast = Ast::Call(Box::new(AstNode::from_expr(*expr, context, codemap)), args);
                //.node(begin, end)
                //kkkkk
                AstNode { node: ast, extra: E::new(begin, end) }
            }
            _ => unimplemented!()
        }
    }
}

pub fn parse<'a>(context: &'a Context, path: &Path, module: &mut Module) -> Result<Vec<Operation<'a>>, Box<dyn Error>> {
    let dialect = syntax::Dialect::Extended;
    let m = syntax::AstModule::parse_file(&path, &dialect)?;
    let stmt = m.statement();
    let codemap = m.codemap();
    println!("m: {:?}", &stmt);
    Ok(lower_stmt(context, codemap, &stmt))
}

fn lower_expr2<'c, E: Extra>(context: &'c Context, codemap: &CodeMap, expr: &'c AstNode<E>) -> Vec<Operation<'c>> {
    let index_type = Type::index(context);
    let location = expr.extra.location(context, codemap);
    //let location = Location::new(context, codemap.filename(), expr.begin.line, expr.begin.col);
    match &expr.node {
        Ast::BinaryOp(op, a, b) =>  {
            let mut lhs_ops = lower_expr2(context, codemap, a);
            let mut rhs_ops = lower_expr2(context, codemap, b);
            let r_lhs = lhs_ops.last().unwrap().result(0).unwrap();
            let r_rhs = rhs_ops.last().unwrap().result(0).unwrap();
            println!("lhs: {:?}", lhs_ops);
            println!("rhs: {:?}", rhs_ops);
            println!("lhs: {:?}", r_lhs.r#type());
            println!("rhs: {:?}", r_rhs.r#type());

            // types must be the same for binary operation, no implicit casting
            assert!(r_lhs.r#type() == r_rhs.r#type());

            let ty = r_lhs.r#type();
            let float_type = Type::float64(context);

            let mut out = vec![];
            let binop = match op {
                BinaryOperation::Add => {
                    if ty == index_type {
                        arith::addi(r_lhs.into(), r_rhs.into(), location)
                    } else if ty == float_type {
                        arith::addf(r_lhs.into(), r_rhs.into(), location)
                    } else {
                        unimplemented!()
                    }
                }
                BinaryOperation::Subtract => {
                    if ty == index_type {
                        arith::subi(r_lhs.into(), r_rhs.into(), location)
                    } else if ty == float_type {
                        arith::subf(r_lhs.into(), r_rhs.into(), location)
                    } else {
                        unimplemented!()
                    }
                }
                BinaryOperation::Equal => {
                    if ty == index_type {
                        arith::cmpi(context, arith::CmpiPredicate::Eq, r_lhs.into(), r_rhs.into(), location)
                    } else if ty == float_type {
                        // ordered comparison
                        arith::cmpf(context, arith::CmpfPredicate::Oeq, r_lhs.into(), r_rhs.into(), location)
                    } else {
                        unimplemented!()
                    }
                }
                _ => {
                    println!("not implemented: {:?}", op);
                    unimplemented!();
                }

            };
            out.append(&mut lhs_ops);
            out.append(&mut rhs_ops);
            out.push(binop); 
            out
        }

        Ast::Identifier(ident) => {
            println!("not implemented: {:?}", ident);
            unimplemented!();
        }

        Ast::Call(expr, args) => {
            // function to call
            let f = match &expr.node {
                Ast::Identifier(ident) => {
                    attribute::FlatSymbolRefAttribute::new(context, ident)
                }
                _ => {
                    println!("not implemented: {:?}", expr.node);
                    unimplemented!();
                }
            };


            // handle call arguments
            let mut ops: Vec<Operation> = vec![];
            let mut call_index: Vec<usize> = vec![];
            for a in args {
                match &a {
                    Argument::Positional(arg) => {
                        println!("arg: {:?}", arg.node);
                        let mut arg_ops = lower_expr2(context, codemap, arg);
                        ops.append(&mut arg_ops);
                        call_index.push(ops.len()-1);
                    }
                    _ => {
                        println!("not implemented: {:?}", a);
                        unimplemented!();
                    }
                };

            }

            let call_args: Vec<Value> = call_index.iter().map(|index| {
                let results = ops.get(*index).unwrap().results();
                let results: Vec<Value> = results.map(|r| r.into()).collect();
                results.last().unwrap().clone()
            }).collect::<Vec<Value>>();

            println!("call_index: {:?}", call_index);
            println!("call_args: {:?}", call_args);
            let op = func::call(context, f, call_args.as_slice(), &[index_type], location);
            ops.push(op);
            println!("ops: {:?}", ops);
            ops
        }

        Ast::Literal(lit) => {
            match lit {
                Literal::Float(f) => {
                    let float_type = Type::float64(context);
                    vec![arith::constant(context, attribute::FloatAttribute::new(context, *f, float_type).into(), location)]
                }
                Literal::Int(x) => {
                    vec![arith::constant(context, attribute::IntegerAttribute::new(*x, index_type).into(), location)]
                }
                _ => {
                    println!("not implemented: {:?}", lit);
                    unimplemented!();
                }
            }
        }

        Ast::Sequence(exprs) => {
            let mut out = vec![];
            for s in exprs {
                out.extend(lower_expr2(context, codemap, s));
            }
            out
        }


        _ => {
            println!("not implemented: {:?}", expr.node);
            unimplemented!();
        }
    }
}

fn lower_expr<'c>(context: &'c Context, codemap: &CodeMap, expr: &syntax::ast::AstExpr) -> Vec<Operation<'c>> {
    use syntax::ast::ExprP;
    use syntax::ast::BinOp;
    use syntax::ast::AstLiteral;
    use syntax::ast::ArgumentP;
    use lexer::TokenInt;

    let index_type = Type::index(context);
    let r = codemap.resolve_span(expr.span);
    let location = Location::new(context, codemap.filename(), r.begin.line, r.begin.column);

    match &expr.node {
        ExprP::Op(a, op, b) =>  {
            let mut lhs_ops = lower_expr(context, codemap, a);
            let mut rhs_ops = lower_expr(context, codemap, b);
            let r_lhs = lhs_ops.last().unwrap().result(0).unwrap();
            let r_rhs = rhs_ops.last().unwrap().result(0).unwrap();
            println!("lhs: {:?}", lhs_ops);
            println!("rhs: {:?}", rhs_ops);
            println!("lhs: {:?}", r_lhs.r#type());
            println!("rhs: {:?}", r_rhs.r#type());

            // types must be the same for binary operation, no implicit casting
            assert!(r_lhs.r#type() == r_rhs.r#type());

            let ty = r_lhs.r#type();
            let float_type = Type::float64(context);

            let mut out = vec![];
            let binop = match op {
                BinOp::Add => {
                    if ty == index_type {
                        arith::addi(r_lhs.into(), r_rhs.into(), location)
                    } else if ty == float_type {
                        arith::addf(r_lhs.into(), r_rhs.into(), location)
                    } else {
                        unimplemented!()
                    }
                }
                BinOp::Subtract => {
                    if ty == index_type {
                        arith::subi(r_lhs.into(), r_rhs.into(), location)
                    } else if ty == float_type {
                        arith::subf(r_lhs.into(), r_rhs.into(), location)
                    } else {
                        unimplemented!()
                    }
                }
                BinOp::Equal => {
                    if ty == index_type {
                        arith::cmpi(context, arith::CmpiPredicate::Eq, r_lhs.into(), r_rhs.into(), location)
                    } else if ty == float_type {
                        // ordered comparison
                        arith::cmpf(context, arith::CmpfPredicate::Oeq, r_lhs.into(), r_rhs.into(), location)
                    } else {
                        unimplemented!()
                    }
                }
                _ => {
                    println!("not implemented: {:?}", op);
                    unimplemented!();
                }

            };
            out.append(&mut lhs_ops);
            out.append(&mut rhs_ops);
            out.push(binop); 
            out
        }

        ExprP::Identifier(ident) => {
            let name = &ident.node.ident;
            println!("ident: {}", name);
            //vec![dummy]
            println!("not implemented: {:?}", ident);
            unimplemented!();
        }

        ExprP::Call(expr, args) => {
            // function to call
            let f = match &expr.node {
                ExprP::Identifier(ident) => {
                    let name = &ident.node.ident;
                    attribute::FlatSymbolRefAttribute::new(context, name)
                }
                _ => {
                    println!("not implemented: {:?}", expr.node);
                    unimplemented!();
                }
            };


            // handle call arguments
            let mut ops: Vec<Operation> = vec![];
            let mut call_index: Vec<usize> = vec![];
            for a in args {
                match &a.node {
                    ArgumentP::Positional(arg) => {
                        println!("arg: {:?}", arg.node);
                        let mut arg_ops = lower_expr(context, codemap, arg);
                        ops.append(&mut arg_ops);
                        call_index.push(ops.len()-1);
                    }
                    _ => {
                        println!("not implemented: {:?}", a.node);
                        unimplemented!();
                    }
                };

            }

            let call_args: Vec<Value> = call_index.iter().map(|index| {
                let results = ops.get(*index).unwrap().results();
                let results: Vec<Value> = results.map(|r| r.into()).collect();
                results.last().unwrap().clone()
            }).collect::<Vec<Value>>();

            println!("call_index: {:?}", call_index);
            println!("call_args: {:?}", call_args);
            let op = func::call(context, f, call_args.as_slice(), &[index_type], location);
            ops.push(op);
            println!("ops: {:?}", ops);
            ops
        }

        ExprP::Literal(lit) => {
            match lit {
                AstLiteral::Float(ast) => {
                    let f = ast.node;
                    let float_type = Type::float64(context);
                    vec![arith::constant(context, attribute::FloatAttribute::new(context, f, float_type).into(), location)]
                }
                AstLiteral::Int(ast) => {
                    match ast.node {
                        TokenInt::I32(x) => {
                            vec![arith::constant(context, attribute::IntegerAttribute::new(x as i64, index_type).into(), location)]
                        }
                        _ => {
                            println!("not implemented: {:?}", ast.node);
                            unimplemented!();
                        }
                    }
                }
                _ => {
                    println!("not implemented: {:?}", lit);
                    unimplemented!();
                }
            }
        }

        _ => {
            println!("not implemented: {:?}", expr.node);
            unimplemented!();
        }
    }
}

fn lower_stmt<'a>(context: &'a Context, codemap: &CodeMap, ast: &syntax::ast::AstStmt) -> Vec<Operation<'a>> {
    use syntax::ast::StmtP;
    use syntax::ast::ParameterP;
    match &ast.node {
        StmtP::Statements(stmts) => {
            let mut out = vec![];
            for s in stmts {
                out.extend(lower_stmt(context, codemap, s));
            }
            out
        }

        StmtP::Def(def) => {
            println!("name {:?}", def.name.ident);
            let mut params = vec![];
            let index_type = Type::index(context);
            for p in &def.params {
                match &p.node {
                    ParameterP::Normal(ident, maybe_ty) => {
                        println!("params {:?}", ident.node.ident);
                        let r = codemap.resolve_span(ident.span);
                        let location = Location::new(context, codemap.filename(), r.begin.line, r.begin.column);
                        params.push((index_type, location));
                    }
                    _ => {
                        println!("not implemented: {:?}", p);
                        unimplemented!();
                    }
                }
            }
            println!("ret {:?}", def.return_type);

            let ops = lower_stmt(context, codemap, &*def.body);
            let index_type = Type::index(context);
            let r = codemap.resolve_span(ast.span);
            let location = Location::new(context, codemap.filename(), r.begin.line, r.begin.column);
            

            let block = Block::new(params.as_slice());
            for op in ops {
                block.append_operation(op);
            }

            let region = Region::new();
            region.append_block(block);

            let types = params.iter().map(|x| x.0).collect::<Vec<Type>>();
            let ret_type = vec![index_type];
            let func_type = FunctionType::new(context, &types, &ret_type);

            let f = func::func(
                context,
                StringAttribute::new(context, &def.name.ident),
                TypeAttribute::new(func_type.into()),
                region,
                &[(
                    Identifier::new(&context, "sym_visibility"),
                    StringAttribute::new(&context, "private").into(),
                )],
                location,
                );
            vec![f]
        }

        StmtP::IfElse(expr, options) => {
            println!("ifexpr {:?}", expr);
            lower_expr(context, codemap, expr);
            println!("if {:?}", options.0);
            lower_stmt(context, codemap, &options.0);
            println!("else {:?}", options.1);
            lower_stmt(context, codemap, &options.1);
            vec![]
        }

        StmtP::Return(maybe_expr) => {
            let r = codemap.resolve_span(ast.span);
            let location = Location::new(context, codemap.filename(), r.begin.line, r.begin.column);
            match maybe_expr {
                Some(expr) => {
                    let mut ops = lower_expr(context, codemap, expr);
                    let results: Vec<Value> = ops.last().unwrap().results().map(|r| r.into()).collect();
                    let ret_op = func::r#return( results.as_slice(), location);
                    ops.push(ret_op);
                    ops
                }
                None =>  {
                    vec![func::r#return( &[], location)]
                }
            }
        }

        StmtP::Assign(assign) => {
            let ops = lower_expr(context, codemap, &assign.rhs);
            match &*assign.lhs {
                syntax::ast::AssignTarget::Identifier(ident) => {
                    println!("assign ident {:?}", ident.node.ident);
                }
                _ => {
                    println!("not implemented: {:?}", assign.lhs);
                    unimplemented!();
                }
            }
            ops
            //vec![ops]
        }

        StmtP::Expression(expr) => {
            let ops = lower_expr(context, codemap, expr);
            println!("not implemented: {:?}", expr);
            unimplemented!();
            //vec![ops]
        }

        _ => {
            println!("not implemented: {:?}", ast.node);
            unimplemented!();
        }
    }
}

fn test(context: &Context) {
    let index_type = Type::index(context);
    let location = Location::unknown(context);
    let dummy = arith::constant(context, attribute::IntegerAttribute::new(1, index_type).into(), location);
    let op = func::r#return( &[dummy.result(0).unwrap().into()], location);
    
    let func_type = FunctionType::new(context, &[], &[index_type]);
    let block = Block::new(&[]);
    block.append_operation(dummy);
    block.append_operation(op);

    let region = Region::new();
    region.append_block(block);

    let f = func::func(
        context,
        StringAttribute::new(context, "test"),
        TypeAttribute::new(func_type.into()),
        region,
        &[(
            Identifier::new(&context, "sym_visibility"),
            StringAttribute::new(&context, "private").into(),
        )],
        location,
        );

    let module = Module::new(location);
    module.body().append_operation(f);

    module.as_operation().dump();
    assert!(module.as_operation().verify());
    module.as_operation().dump();
}

fn main() -> Result<(), Box<dyn Error>> {
    let context = Context::new();

    context.attach_diagnostic_handler(|diagnostic| {
        eprintln!("E: {}", diagnostic);
        true
    });

    let registry = DialectRegistry::new();
    register_all_dialects(&registry);
    context.append_dialect_registry(&registry);
    context.load_all_available_dialects();
    register_all_llvm_translations(&context);

    //test(&context);

    let location = Location::unknown(&context);
    let mut module = Module::new(location);

    let ops = parse(&context, Path::new("examples/test_simple.py"), &mut module).unwrap();
    for op in ops {
        module.body().append_operation(op);
    }
    let s = module.as_operation().to_string();
    module.as_operation().dump();

    assert!(module.as_operation().verify());
    let mut output = File::create("out.mlir")?;
    write!(output, "{}", s)?;
    Ok(())
}
