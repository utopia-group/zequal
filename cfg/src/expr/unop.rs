use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use program_structure::ast::{ExpressionPrefixOpcode};
use serde::{Serialize};
use crate::error::CFGError;
use crate::expr::expression::{Expr, Expression};
use crate::expr::variable_ref::Ref;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Debug)]
pub enum UnaryOperator {
    Negate,
    Not,
    Complement
}

#[derive(Clone, PartialEq, Eq, Serialize, Debug)]
pub struct UnOp {
    op: UnaryOperator,
    expr: Box<Expression>,
}

impl Display for UnaryOperator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            UnaryOperator::Negate => { write!(f, "-") }
            UnaryOperator::Not => { write!(f, "!") }
            UnaryOperator::Complement => { write!(f, "~") }
        }
    }
}

impl From<&ExpressionPrefixOpcode> for UnaryOperator {
    fn from(value: &ExpressionPrefixOpcode) -> Self {
        match value {
            ExpressionPrefixOpcode::Sub => { Self::Negate }
            ExpressionPrefixOpcode::BoolNot => { Self::Not }
            ExpressionPrefixOpcode::Complement => { Self::Complement }
        }
    }
}

impl Hash for UnOp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_string().hash(state)
    }
}


impl Display for UnOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.op, self.expr)
    }
}

impl Expr for UnOp {
    fn variable_refs(&self) -> HashSet<&Ref> {
        self.expr().variable_refs()
    }

    fn rename(&self, from: &Ref, to: &Ref) -> Result<Self, CFGError> {
        let expr = Box::new(self.expr.rename(from, to)?);
        Ok(Self::new(self.op, expr))
    }
}

impl UnOp {
    pub fn op(&self) -> UnaryOperator { self.op }
    pub fn expr(&self) -> &Expression { &self.expr }

    pub fn new(op: UnaryOperator, expr: Box<Expression>) -> Self {
        Self { op, expr }
    }
}