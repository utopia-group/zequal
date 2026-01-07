use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use serde::{Serialize};
use crate::expr::expression::Expr;
use crate::expr::invariant::InvariantExpr;
use crate::expr::variable_ref::Ref;
use crate::stmt::statement::Stmt;

#[derive(Clone, Serialize, Debug, PartialEq, Eq)]
pub struct Assumption {
    expr: InvariantExpr
}

impl Display for Assumption {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}", self.expr)
    }
}

impl Stmt for Assumption {
    fn reads(&self) -> HashSet<&Ref> {
        self.expr.variable_refs()
    }

    fn writes(&self) -> Option<&Ref> {
        None
    }
}

impl Assumption {
    pub fn expr(&self) -> &InvariantExpr { &self.expr }

    pub fn new(expr: InvariantExpr) -> Self {
        Self {expr}
    }
}