use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};
use std::hash::{Hash};
use std::str::FromStr;
use num_bigint_dig::BigInt;
use program_structure::ast;
use serde::{Serialize};
use crate::error::CFGError;
use crate::expr::binop::{BinaryOperator, BinOp};
use crate::expr::function_call::{FunctionCall, FunctionReturnType};
use crate::expr::instantiate::Instantiate;
use crate::expr::literal::Literal;
use crate::expr::ternary::Ternary;
use crate::expr::unop::{UnaryOperator, UnOp};
use crate::expr::variable_ref::{Ref};
use crate::named_storage::{NamedStorage};
use crate::storage_type::TypeInference;

pub trait Expr {
    fn variable_refs(&self) -> HashSet<&Ref>;
    //fn rename(&self, var: &String, new_name: &String) -> Self;
    fn rename(&self, from: &Ref, to: &Ref) -> Result<Self, CFGError> where Self: Sized;

    fn rename_all(&self, renamings: &HashMap<Ref, Ref>) -> Result<Self, CFGError> where Self: Sized + Clone + Display {
        let mut ret: Self = self.clone();
        for (from, to) in renamings {
            ret = ret.rename(from, to)?;
        }

        Ok(ret)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Debug)]
pub enum Expression {
    BinOp(BinOp),
    UnOp(UnOp),
    Ternary(Ternary),
    Variable(Ref),
    Literal(Literal),
    Instantiate(Instantiate),
    FunctionCall(FunctionCall)
}

impl From<BigInt> for Expression {
    fn from(value: BigInt) -> Self {
        Expression::new_number(value)
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::BinOp(e) => { write!(f, "{}", e) }
            Expression::UnOp(e) => { write!(f, "{}", e) }
            Expression::Ternary(e) => { write!(f, "{}", e) }
            Expression::Variable(e) => { write!(f, "{}", e) }
            Expression::Literal(e) => { write!(f, "{}", e) }
            Expression::Instantiate(e) => { write!(f, "{}", e) }
            Expression::FunctionCall(e) => { write!(f, "{}", e) }
        }
    }
}

impl Expr for Expression {
    fn variable_refs(&self) -> HashSet<&Ref> {
        match self {
            Expression::BinOp(e) => {
                e.variable_refs()
            }
            Expression::UnOp(e) => {
                e.variable_refs()
            }
            Expression::Ternary(e) => {
                e.variable_refs()
            }
            Expression::Variable(e) => {
                e.variable_refs()
            }
            Expression::Literal(e) => {
                e.variable_refs()
            }
            Expression::Instantiate(e) => {
                e.variable_refs()
            }
            Expression::FunctionCall(e) => {
                e.variable_refs()
            }
        }
    }

    fn rename(&self, from: &Ref, to: &Ref) -> Result<Self, CFGError> {
        match self {
            Self::BinOp(e) => {
                Ok(Self::BinOp(e.rename(from, to)?))
            }
            Self::UnOp(e) => {
                Ok(Self::UnOp(e.rename(from, to)?))
            }
            Self::Ternary(e) => {
                Ok(Self::Ternary(e.rename(from, to)?))
            }
            Self::Variable(e) => {
                Ok(Self::Variable(e.rename(from, to)?))
            }
            Self::Literal(e) => {
                Ok(Self::Literal(e.rename(from, to)?))
            }
            Self::Instantiate(e) => {
                Ok(Self::Instantiate(e.rename(from, to)?))
            }
            Expression::FunctionCall(e) => {
                Ok(Self::FunctionCall(e.rename(from, to)?))
            }
        }
    }
}

impl Expression {
    pub fn and_all(mut conjuncts: Vec<Self>) -> Self {
        // Iterate over all signal equality constraints and conjoin them so that quantifiers get merged
        if let Some(mut lhs) = conjuncts.pop() {
            while let Some(rhs) = conjuncts.pop() {
                lhs = Self::new_binop(Box::new(lhs), BinaryOperator::And, Box::new(rhs));
            }
            lhs
        }
        else {
            Expression::new_literal(Literal::new_boolean(true))
        }
    }

    pub fn or_all(mut conjuncts: Vec<Self>) -> Self {
        // Iterate over all signal equality constraints and conjoin them so that quantifiers get merged
        if let Some(mut lhs) = conjuncts.pop() {
            while let Some(rhs) = conjuncts.pop() {
                lhs = Self::new_binop(Box::new(lhs), BinaryOperator::Or, Box::new(rhs));
            }
            lhs
        }
        else {
            Expression::new_literal(Literal::new_boolean(true))
        }
    }

    pub fn from_ast(type_inference: &TypeInference, vars_and_signals: &HashMap<String, (usize, NamedStorage)>, template_params: &HashMap<String, Vec<String>>, parent: &String, ast_expr: &ast::Expression, var_versions: &HashMap<String, usize>) -> Result<Expression, CFGError> {
        match ast_expr {
            ast::Expression::InfixOp { lhe, infix_op, rhe, ..} => {
                Ok(Self::new_binop(Self::from_ast(type_inference, vars_and_signals, template_params, parent, lhe, var_versions)?.into(), infix_op.into(), Self::from_ast(type_inference, vars_and_signals, template_params, parent, rhe, var_versions)?.into()))
            }
            ast::Expression::PrefixOp { prefix_op, rhe, .. } => {
                Ok(Self::new_unop(prefix_op.into(), Self::from_ast(type_inference, vars_and_signals, template_params, parent, rhe, var_versions)?.into()))
            }
            ast::Expression::InlineSwitchOp { cond, if_true, if_false, .. } => {
                Ok(Self::new_ternary(Self::from_ast(type_inference, vars_and_signals, template_params, parent, cond, var_versions)?.into(), Self::from_ast(type_inference, vars_and_signals, template_params, parent, if_true, var_versions)?.into(), Self::from_ast(type_inference, vars_and_signals, template_params, parent, if_false, var_versions)?.into()))
            }
            ast::Expression::ParallelOp { rhe, .. } => {
                Self::from_ast(type_inference, vars_and_signals, template_params, parent, rhe, var_versions)
            }
            ast::Expression::Variable { name, access, .. } => {
                //let access_list = AccessList::from_ast(vars_and_signals, template_params, access, var_versions)?;
                Ok(Self::new_variable(Ref::from_ast(type_inference, vars_and_signals, template_params, parent, var_versions, name.clone(), access, false)?))
            }
            ast::Expression::Call { id, args, .. } => {
                let arg_list = args.iter().map(|arg| Self::from_ast(type_inference, vars_and_signals, template_params, parent, arg, var_versions)).collect::<Result<Vec<Expression>, CFGError>>()?;
                if template_params.contains_key(id) {
                    Ok(Self::new_instantiate(id.clone(), arg_list))
                }
                else {
                    let inferred_ret_type = type_inference.get_fn_ret_type(id);
                    let mut dims = vec![];
                    for _ in inferred_ret_type.dims() {
                        dims.push(Expression::new_number(BigInt::from_str("100000000000000000000000000000000000").unwrap()));
                    }

                    if dims.is_empty() {
                        Ok(Self::new_function_call(id.clone(), arg_list, FunctionReturnType::var()))
                    }
                    else {
                        Ok(Self::new_function_call(id.clone(), arg_list, FunctionReturnType::array(dims)))
                    }
                }
            }
            ast::Expression::Number(_, val) => {
                Ok(Self::new_number(val.clone()))
            }
            ast::Expression::ArrayInLine { values, .. } => {
                let entries = values.iter().map(|v| Self::from_ast(type_inference, vars_and_signals, template_params, parent, v, var_versions)).collect::<Result<Vec<Expression>, CFGError>>()?;
                Ok(Self::Literal(Literal::new_inline_array(entries)))
            }
            ast::Expression::UniformArray { value, dimension, .. } => {
                Ok(Self::new_literal(Literal::new_uniform_array(Self::from_ast(type_inference, vars_and_signals, template_params, parent, value, var_versions)?.into(), Self::from_ast(type_inference, vars_and_signals, template_params, parent, dimension, var_versions)?.into())))
            }
            ast::Expression::Tuple { .. } => { Err(CFGError::UnsupportedExpr("Tuple")) }
            ast::Expression::AnonymousComp { .. } => { Err(CFGError::UnsupportedExpr("AnonymousComp")) }
        }
    }

    pub fn new_binop(lhs: Box<Expression>, op: BinaryOperator, rhs: Box<Expression>) -> Self {
        Self::BinOp(BinOp::new(lhs, op, rhs))
    }

    pub fn new_unop(op: UnaryOperator, expr: Box<Expression>) -> Self {
        Self::UnOp(UnOp::new(op, expr))
    }

    pub fn new_variable(r: Ref) -> Self {
        Self::Variable(r)
    }

    pub fn new_ternary(cond: Box<Expression>, true_case: Box<Expression>, false_case: Box<Expression>) -> Self {
        Self::Ternary(Ternary::new(cond, true_case, false_case))
    }

    pub fn new_instantiate(name: String, args: Vec<Expression>) -> Self {
        Self::Instantiate(Instantiate::new(name, args))
    }

    pub fn new_number(val: BigInt) -> Self {
        Self::Literal(Literal::new_number(val))
    }

    pub fn new_literal(literal: Literal) -> Self {
        Self::Literal(literal)
    }

    pub fn new_function_call(name: String, args: Vec<Expression>, ret_type: FunctionReturnType) -> Self {
        Self::FunctionCall(FunctionCall::new(name, args, ret_type))
    }
}