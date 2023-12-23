use anyhow::Error;
use anyhow::Result;

use crate::cfg::{CFGGraph, CFG};
use crate::{AstNode, AstType, Diagnostics, Extra, NodeBuilder, NodeID, ParseError, StringKey};
use melior::{ir::Location, Context};
use std::fmt::Debug;

use crate::ast::{
    Argument, AssignTarget, Ast, BinaryOperation, Builtin, DerefTarget, Literal, Parameter,
    ParameterNode, UnaryOperation,
};

use petgraph::graph::NodeIndex;
use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Debug)]
pub enum IRTypeSelect {
    // array offset
    Offset(usize),
    // attribute select on tuple
    Attr(usize),
    // byte level view (width, offset)
    Byte(u8, usize),
}

impl Default for IRTypeSelect {
    fn default() -> Self {
        Self::Offset(0)
    }
}
#[derive(Debug)]
pub struct IRArg {
    name: StringKey,
    ty: AstType,
}

#[derive(Debug)]
pub enum IRKind {
    Decl(StringKey, AstType),
    // set(variable, expr, type offset)
    Set(StringKey, Box<IRNode>, IRTypeSelect),
    // get(variable, type offset)
    Get(StringKey, IRTypeSelect),
    // ret(args)
    Ret(Vec<IRNode>),
    Cond(Box<IRNode>, Box<IRNode>, Option<Box<IRNode>>),
    Jump(StringKey, Vec<IRNode>),
    // call(variable, args), return type is inferred from variable
    Call(StringKey, Vec<IRNode>),
    // op(operation, args)
    Op1(UnaryOperation, Box<IRNode>),
    Op2(BinaryOperation, Box<IRNode>, Box<IRNode>),
    Block(StringKey, Vec<IRArg>, Vec<IRNode>),
    Seq(Vec<IRNode>),
    Literal(Literal),
    Builtin(Builtin, Vec<IRNode>),
    Noop,
}

#[derive(Debug)]
pub struct IRNode {
    kind: IRKind,
    loc: usize,
}

impl IRNode {
    pub fn new(kind: IRKind) -> Self {
        Self { kind, loc: 0 }
    }
    pub fn to_vec(self) -> Vec<Self> {
        if let IRKind::Seq(exprs) = self.kind {
            exprs
        } else {
            vec![self]
        }
    }
}

impl<E: Extra> AstNode<E> {
    pub fn lower_ir<'c>(
        self,
        context: &'c Context,
        d: &mut Diagnostics,
        cfg: &mut CFG<'c, E>,
        stack: &mut Vec<NodeIndex>,
        g: &mut CFGGraph<'c>,
        b: &mut NodeBuilder<E>,
    ) -> Result<IRNode> {
        if !self.node_id.is_valid() {
            d.push_diagnostic(self.extra.error(&format!("Invalid NodeID: {:#?}", self)));
            return Err(Error::new(ParseError::Invalid));
        }

        match self.node {
            Ast::Noop => Ok(b.ir_noop()),
            Ast::Sequence(exprs) => {
                let mut out = vec![];
                for expr in exprs {
                    out.extend(expr.lower_ir(context, d, cfg, stack, g, b)?.to_vec());
                }
                Ok(b.ir_seq(out))
            }

            Ast::Return(maybe_expr) => {
                if let Some(expr) = maybe_expr {
                    let ir = expr.lower_ir(context, d, cfg, stack, g, b)?;
                    Ok(b.ir_ret(vec![ir]))
                } else {
                    Ok(b.ir_ret(vec![]))
                }
            }

            Ast::Goto(label) => Ok(b.ir_jump(label, vec![])),

            Ast::Identifier(name) => {
                let current_block = stack.last().unwrap().clone();
                //let s = b.strings.resolve(&name);
                if let Some(sym_index) = cfg.name_in_scope(current_block, name, g) {
                    println!(
                        "lookup identifier: {}, {:?}",
                        b.strings.resolve(&name),
                        sym_index
                    );
                    if cfg.block_is_static(sym_index.block()) {
                        let ast_ty = cfg.lookup_type(sym_index).unwrap();
                        if let AstType::Ptr(_ty) = &ast_ty {
                            Ok(b.ir_get(name, IRTypeSelect::default()))

                            /*
                            let lower_ty = op::from_type(context, ty);
                            let memref_ty = MemRefType::new(lower_ty, &[], None, None);
                            let static_name = b.strings.resolve(
                                &cfg.static_names.get(&sym_index).cloned().unwrap_or(name),
                            );
                            let op =
                                memref::get_global(context, &static_name, memref_ty, location);
                            let current = g.node_weight_mut(current_block).unwrap();
                            let index = current.push(op);
                            cfg.set_type(index, ast_ty);
                            return Ok(index);
                            */
                        } else {
                            d.push_diagnostic(
                                self.extra
                                    .error(&format!("Expected pointer: {:?}", &ast_ty)),
                            );
                            return Err(Error::new(ParseError::Invalid));
                        }
                    } else {
                        Ok(b.ir_get(name, IRTypeSelect::default()))
                        //return Ok(sym_index);
                    }
                } else {
                    d.push_diagnostic(self.extra.error(&format!("Undefined variable: {:?}", name)));
                    Err(Error::new(ParseError::Invalid))
                }
            }

            Ast::Global(ident, expr) => {
                let current_block = stack.last().unwrap().clone();

                let is_static = cfg.root() == current_block;

                let (global_name_key, global_name) = if is_static {
                    (ident, b.strings.resolve(&ident).clone())
                } else {
                    // we create a unique global name to prevent conflict
                    // and then we add ops to provide a local reference to the global name
                    let name = b.unique_static_name();
                    let name = format!("{}{}", b.strings.resolve(&ident), name).clone();
                    (b.strings.intern(name.clone()), name)
                };

                if let Ast::Literal(lit) = expr.node {
                    let ty = lit.into();
                    Ok(b.ir_decl(global_name_key, ty))
                } else {
                    unreachable!()
                }
            }

            Ast::Assign(target, expr) => {
                //let current_block = stack.last().unwrap().clone();
                match target {
                    AssignTarget::Alloca(name) | AssignTarget::Identifier(name) => {
                        let ir = expr.lower_ir(context, d, cfg, stack, g, b)?;
                        let current_block = stack.last().unwrap().clone();
                        //let s = b.strings.resolve(&name);
                        if let Some(sym_index) = cfg.name_in_scope(current_block, name, g) {
                            Ok(b.ir_set(name, ir, IRTypeSelect::Offset(0)))
                        } else {
                            Ok(b.ir_decl(name, AstType::Int))
                        }

                        /*
                        //log::debug!("assign alloca: {}", name);
                        let ty = IntegerType::new(context, 64);
                        let memref_ty = MemRefType::new(ty.into(), &[], None, None);
                        let op = memref::alloca(context, memref_ty, &[], &[], None, location);
                        let rhs_index = expr.lower(context, d, cfg, stack, g, b)?;
                        let current = g.node_weight_mut(current_block).unwrap();

                        // name the pointer
                        let ptr_index = current.push_with_name(op, name);
                        let ast_ty = cfg.lookup_type(rhs_index).unwrap().to_ptr();
                        //let ptr_ty = AstType::Ptr(ast_ty.into());
                        cfg.set_type(ptr_index, ast_ty);

                        let r_value = current.value0(rhs_index).unwrap();
                        let r_addr = current.value0(ptr_index).unwrap();

                        // emit store
                        let op = memref::store(r_value, r_addr, &[], location);
                        let _index = current.push(op);
                        ptr_index
                        */
                    } /*
                      AssignTarget::Identifier(name) => {
                          //log::debug!("assign local: {}", name);
                          let current_block = stack.last().unwrap().clone();
                          if cfg.block_is_static(current_block) {
                              d.push_diagnostic(
                                  self.extra
                                      .error(&format!("Assign static not possible: {:?}", name)),
                              );
                              return Err(Error::new(ParseError::Invalid));
                          }

                          //let index = expr.lower(context, d, cfg, stack, g, b)?;
                          let current = g.node_weight_mut(index.block()).unwrap();
                          current.add_symbol(name, index);
                          //assert!(cfg.lookup_type(index).is_some());
                          index
                      }
                      */
                }
                //Ok(sym_index)
            }

            Ast::Mutate(lhs, rhs) => {
                match lhs.node {
                    Ast::Identifier(name) => {
                        let ir = rhs.lower_ir(context, d, cfg, stack, g, b)?;
                        Ok(b.ir_set(name, ir, IRTypeSelect::Offset(0)))
                        //emit_mutate(context, ident, *rhs, d, cfg, stack, g, b)
                    }
                    //Ast::Deref(expr, target) => {
                    //let index = emit_deref(context, *expr, target, d, cfg, stack, g)?;
                    //emit_mutate(context, &ident, *rhs, d, cfg, stack, g)
                    //}
                    _ => unimplemented!("{:?}", &lhs.node),
                }
            }

            Ast::Call(expr, args, ret_ty) => {
                // function to call
                let current_block = stack.last().unwrap().clone();
                let (f, ty, f_args, name) = match &expr.node {
                    Ast::Identifier(ident) => {
                        let name = b.strings.resolve(ident);
                        if let Some(index) = cfg.name_in_scope(current_block, *ident, g) {
                            if let Some(ty) = cfg.lookup_type(index) {
                                if let AstType::Func(f_args, _) = ty.clone() {
                                    (ident, ty, f_args, name)
                                } else {
                                    d.push_diagnostic(
                                        self.extra.error(&format!(
                                            "Type not function: {}, {:?}",
                                            name, ty
                                        )),
                                    );
                                    return Err(Error::new(ParseError::Invalid));
                                }
                                //(FlatSymbolRefAttribute::new(context, name), ty)
                            } else {
                                d.push_diagnostic(
                                    self.extra
                                        .error(&format!("Type not found: {}, {:?}", name, index)),
                                );
                                return Err(Error::new(ParseError::Invalid));
                            }
                        } else {
                            d.push_diagnostic(
                                self.extra.error(&format!("Name not found: {}", name)),
                            );
                            return Err(Error::new(ParseError::Invalid));
                        }
                    }
                    _ => {
                        unimplemented!("{:?}", expr.node);
                    }
                };

                if let AstType::Func(_func_arg_types, ret) = &ty {
                    if f_args.len() != args.len() {
                        d.push_diagnostic(
                            self.extra.error(&format!("Call arity mismatch: {}", name)),
                        );
                        return Err(Error::new(ParseError::Invalid));
                    }

                    let mut ir_args = vec![];
                    for a in args {
                        match a {
                            Argument::Positional(expr) => {
                                ir_args.push(expr.lower_ir(context, d, cfg, stack, g, b)?);
                            }
                        }
                    }
                    Ok(b.ir_call(*f, ir_args))

                    /*
                    let ret_type = op::from_type(context, &ret);
                    // handle call arguments
                    let mut indices = vec![];

                    // lower call args
                    for a in args {
                        match a {
                            Argument::Positional(arg) => {
                                let index = arg.lower(context, d, cfg, stack, g, b)?;
                                indices.push(index);
                            } //_ => unimplemented!("{:?}", a)
                        };
                    }

                    let call_args = indices
                        .into_iter()
                        .map(|index| values_in_scope(g, index)[0])
                        .collect::<Vec<_>>();

                    let op = func::call(
                        context,
                        f,
                        call_args.as_slice(),
                        &[ret_type.clone()],
                        location,
                    );
                    let current = g.node_weight_mut(current_block).unwrap();

                    let index = current.push(op);
                    cfg.set_type(index, ret_ty);
                    Ok(index)
                    */
                } else {
                    unimplemented!("calling non function type: {:?}", ty);
                }
            }

            Ast::Definition(mut def) => {
                def = def.normalize(b);
                let current_block = stack.last().unwrap().clone();
                assert!(cfg.block_is_static(current_block));

                let mut ast_types = vec![];
                for p in &def.params {
                    match p.node {
                        Parameter::Normal | Parameter::WithDefault(_) => {
                            ast_types.push(p.ty.clone());
                        }
                        _ => unimplemented!("{:?}", p),
                    }
                }
                let ast_ret_type = def.return_type;
                let f_type = AstType::Func(ast_types, ast_ret_type);
                let mut out = vec![b.ir_decl(def.name, f_type)];
                let mut output_blocks = vec![];
                if let Some(body) = def.body {
                    let blocks = body.try_seq().unwrap();
                    for (_i, block) in blocks.into_iter().enumerate() {
                        if let Ast::Block(nb) = block.node {
                            output_blocks.push(nb.body.lower_ir(context, d, cfg, stack, g, b)?);
                        } else {
                            unreachable!()
                        }
                    }
                }

                if output_blocks.len() > 0 {
                    out.push(b.ir_seq(output_blocks));
                }
                Ok(b.ir_seq(out))
            }

            Ast::Literal(lit) => match lit {
                Literal::Float(f) => Ok(b.ir_float(f)),
                Literal::Int(f) => Ok(b.ir_integer(f)),
                Literal::Index(f) => Ok(b.ir_index(f)),
                Literal::Bool(f) => Ok(b.ir_bool(f)),
                _ => unimplemented!("{:?}", lit),
            },

            Ast::Builtin(bi, args) => {
                let mut ir_args = vec![];
                for a in args {
                    match a {
                        Argument::Positional(expr) => {
                            ir_args.push(expr.lower_ir(context, d, cfg, stack, g, b)?);
                        }
                    }
                }
                Ok(IRNode::new(IRKind::Builtin(bi, ir_args)))
            }

            Ast::Conditional(condition, then_expr, maybe_else_expr) => {
                let ir_cond = condition.lower_ir(context, d, cfg, stack, g, b)?;
                //let b_then = b.s("then");
                //let b_next = b.s("next");
                let then_block = then_expr.lower_ir(context, d, cfg, stack, g, b)?;

                let else_block = if let Some(else_expr) = maybe_else_expr {
                    //let b_else = b.s("else");
                    Some(else_expr.lower_ir(context, d, cfg, stack, g, b)?)
                } else {
                    None
                };

                Ok(b.ir_cond(ir_cond, then_block, else_block))
            }

            Ast::UnaryOp(op, a) => {
                let ir = a.lower_ir(context, d, cfg, stack, g, b)?;
                Ok(b.ir_op1(op, ir))
            }

            Ast::BinaryOp(op_node, x, y) => {
                let x = x.lower_ir(context, d, cfg, stack, g, b)?;
                let y = y.lower_ir(context, d, cfg, stack, g, b)?;
                Ok(b.ir_op2(op_node.node, x, y))
            }

            Ast::Error => {
                d.push_diagnostic(self.extra.error(&format!("Error")));
                Err(Error::new(ParseError::Invalid))
            }
            _ => {
                d.push_diagnostic(self.extra.error(&format!("Unimplemented: {:?}", self.node)));
                Err(Error::new(ParseError::Invalid))
            }
        }
    }
}
