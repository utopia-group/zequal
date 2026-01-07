use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use program_structure::ast::{ExpressionInfixOpcode};
use serde::{Serialize};
use crate::error::CFGError;
use crate::expr::expression::{Expr, Expression};
use crate::expr::variable_ref::Ref;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Debug)]
pub enum BinaryOperator {
    //Arithmetic
    Mul, MulInv, Add, Sub, Pow, IntDiv, Mod,
    //Bitwise
    Shl, Shr, BitOr, BitAnd, BitXor,
    //Comparison
    Lt, Lte, Gt, Gte, Eq, Neq,
    //Logical
    And, Or
}

#[derive(Clone, PartialEq, Eq, Serialize, Debug)]
pub struct BinOp {
    lhs: Box<Expression>,
    op: BinaryOperator,
    rhs: Box<Expression>,
}

impl Hash for BinOp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_string().hash(state)
    }
}

impl From<&ExpressionInfixOpcode> for BinaryOperator {
    fn from(value: &ExpressionInfixOpcode) -> Self {
        match value {
            ExpressionInfixOpcode::Mul => { Self::Mul }
            ExpressionInfixOpcode::Div => { Self::MulInv }
            ExpressionInfixOpcode::Add => { Self::Add }
            ExpressionInfixOpcode::Sub => { Self::Sub }
            ExpressionInfixOpcode::Pow => { Self::Pow }
            ExpressionInfixOpcode::IntDiv => { Self::IntDiv }
            ExpressionInfixOpcode::Mod => { Self::Mod }
            ExpressionInfixOpcode::ShiftL => { Self::Shl }
            ExpressionInfixOpcode::ShiftR => { Self::Shr }
            ExpressionInfixOpcode::LesserEq => { Self::Lte }
            ExpressionInfixOpcode::GreaterEq => { Self::Gte }
            ExpressionInfixOpcode::Lesser => { Self::Lt }
            ExpressionInfixOpcode::Greater => { Self::Gt }
            ExpressionInfixOpcode::Eq => { Self::Eq }
            ExpressionInfixOpcode::NotEq => { Self::Neq }
            ExpressionInfixOpcode::BoolOr => { Self::Or }
            ExpressionInfixOpcode::BoolAnd => { Self::And }
            ExpressionInfixOpcode::BitOr => { Self::BitOr }
            ExpressionInfixOpcode::BitAnd => { Self::BitAnd }
            ExpressionInfixOpcode::BitXor => { Self::BitXor }
        }
    }
}

impl Display for BinaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOperator::Mul => { write!(f, "*") }
            BinaryOperator::MulInv => { write!(f, "/") }
            BinaryOperator::Add => { write!(f, "+") }
            BinaryOperator::Sub => { write!(f, "-") }
            BinaryOperator::Pow => { write!(f, "**") }
            BinaryOperator::IntDiv => { write!(f, "\\") }
            BinaryOperator::Mod => { write!(f, "%") }
            BinaryOperator::Shl => { write!(f, "<<") }
            BinaryOperator::Shr => { write!(f, ">>") }
            BinaryOperator::BitOr => { write!(f, "|") }
            BinaryOperator::BitAnd => { write!(f, "&") }
            BinaryOperator::BitXor => { write!(f, "^") }
            BinaryOperator::Lt => { write!(f, "<") }
            BinaryOperator::Lte => { write!(f, "<=") }
            BinaryOperator::Gt => { write!(f, ">") }
            BinaryOperator::Gte => { write!(f, ">=") }
            BinaryOperator::Eq => { write!(f, "==") }
            BinaryOperator::Neq => { write!(f, "!=") }
            BinaryOperator::And => { write!(f, "&&") }
            BinaryOperator::Or => { write!(f, "||") }
        }
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let use_parens = match self.op {
            BinaryOperator::And => { true }
            BinaryOperator::Or => { true }
            _ => { false }
        };
        if use_parens {
            write!(f, "({} {} {})", self.lhs, self.op, self.rhs)
        }
        else {
            write!(f, "{} {} {}", self.lhs, self.op, self.rhs)
        }
    }
}

impl Expr for BinOp {
    fn variable_refs(&self) -> HashSet<&Ref> {
        let mut refs = self.lhs().variable_refs();
        refs.extend(self.rhs().variable_refs());
        refs
    }

    fn rename(&self, from: &Ref, to: &Ref) -> Result<Self, CFGError> {
        let lhs = Box::new(self.lhs.rename(from, to)?);
        let rhs = Box::new(self.rhs.rename(from, to)?);
        Ok(Self::new(lhs, self.op, rhs))
    }
}

impl BinOp {
    pub fn lhs(&self) -> &Expression { &self.lhs }
    pub fn op(&self) -> BinaryOperator { self.op }
    pub fn rhs(&self) -> &Expression { &self.rhs }

    pub fn new(lhs: Box<Expression>, op: BinaryOperator, rhs: Box<Expression>) -> Self {
        Self { lhs, op, rhs }
    }
}