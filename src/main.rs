
use std::path::Path;
use std::error::Error;


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

pub fn parse<'a>(context: &'a Context, path: &Path, module: &mut Module) -> Result<Vec<Operation<'a>>, Box<dyn Error>> {
    let dialect = syntax::Dialect::Extended;
    let m = syntax::AstModule::parse_file(&path, &dialect)?;
    let stmt = m.statement();
    let codemap = m.codemap();
    Ok(lower_stmt(context, codemap, &stmt))
}

fn lower_expr<'c>(context: &'c Context, codemap: &CodeMap, expr: &syntax::ast::AstExpr) -> Operation<'c> {
    use syntax::ast::ExprP;
    use syntax::ast::BinOp;
    use syntax::ast::AstLiteral;
    use syntax::ast::ArgumentP;
    use lexer::TokenInt;

    let index_type = Type::index(context);
    let r = codemap.resolve_span(expr.span);
    let location = Location::new(context, codemap.filename(), r.begin.line, r.begin.column);
    let dummy = arith::constant(context, attribute::IntegerAttribute::new(1, index_type).into(), location);

    match &expr.node {
        ExprP::Op(a, op, b) =>  {
            //let mut ops = vec![];
            match op {
                BinOp::Add => {
                    let r = codemap.resolve_span(expr.span);
                    let location = Location::new(context, codemap.filename(), r.begin.line, r.begin.column);
                    let lhs = lower_expr(context, codemap, a);
                    let rhs = lower_expr(context, codemap, b);
                    let index_type = Type::index(context);
                    let lhs = arith::constant(context, attribute::IntegerAttribute::new(1, index_type).into(), location);
                    let rhs = arith::constant(context, attribute::IntegerAttribute::new(2, index_type).into(), location);
                    //arith::addi(lhs.result(0).unwrap().into(), rhs.result(0).unwrap().into(), location)
                    dummy
                }
                BinOp::Subtract => {
                    lower_expr(context, codemap, a);
                    lower_expr(context, codemap, b);
                    dummy
                }
                BinOp::Equal => {
                    lower_expr(context, codemap, a);
                    lower_expr(context, codemap, b);
                    dummy
                }
                _ => {
                    println!("not implemented: {:?}", op);
                    unimplemented!();
                }

            }
        }

        ExprP::Identifier(ident) => {
            let name = &ident.node.ident;
            println!("ident: {}", name);
            dummy
        }

        ExprP::Call(expr, args) => {
            lower_expr(context, codemap, expr);
            for a in args {
                match &a.node {
                    ArgumentP::Positional(ref arg) => {
                        println!("arg: {:?}", arg.node);
                        lower_expr(context, codemap, arg);
                    }
                    _ => {
                        println!("not implemented: {:?}", a.node);
                        unimplemented!();
                    }
                }
            }
            dummy
        }

        ExprP::Literal(lit) => {
            match lit {
                AstLiteral::Int(ast) => {
                    match ast.node {
                        TokenInt::I32(x) => {
                            println!("lit: {:?}", x);
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
            dummy
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
            //println!("body {:?}", def.body);
            println!("ret {:?}", def.return_type);

            let ops = lower_stmt(context, codemap, &*def.body);
            //println!("body {:?}", ops);
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
            //let ret_type = vec![];
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
                    let op = lower_expr(context, codemap, expr);
                    let results: Vec<Value> = op.results().map(|r| r.into()).collect();
                    let ret_op = func::r#return( results.as_slice(), location);
                    println!("op: {:?}", results);
                    vec![op, ret_op]
                }
                None =>  {
                    vec![func::r#return( &[], location)]
                }
            }
        }

        StmtP::Assign(assign) => {
            lower_expr(context, codemap, &assign.rhs);
            match &*assign.lhs {
                syntax::ast::AssignTarget::Identifier(ident) => {
                    println!("assign ident {:?}", ident.node.ident);
                }
                _ => {
                    println!("not implemented: {:?}", assign.lhs);
                    unimplemented!();
                }
            }
            vec![]
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

fn main() {
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
    //println!("{}", module.as_operation().to_string());
    module.as_operation().dump();

    assert!(module.as_operation().verify());
    module.as_operation().dump();
}
