use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use serde::{Serialize};
use crate::expr::expression::{Expr};
use crate::expr::invariant::InvariantExpr;
use crate::expr::variable_ref::Ref;
use crate::stmt::statement::Stmt;

#[derive(Clone, Serialize, Debug, PartialEq, Eq)]
pub struct Assertion {
    expr: InvariantExpr
}

impl Display for Assertion {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}", self.expr)
    }
}

impl Stmt for Assertion {
    fn reads(&self) -> HashSet<&Ref> {
        self.expr().variable_refs()
    }

    fn writes(&self) -> Option<&Ref> {
        Option::None
    }
}

impl Assertion {
    pub fn expr(&self) -> &InvariantExpr { &self.expr }

    pub fn new(expr: InvariantExpr) -> Self {
        Self {expr}
    }
}