use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use serde::{Serialize};
use crate::expr::expression::{Expr, Expression};
use crate::expr::variable_ref::Ref;
use crate::stmt::statement::Stmt;

#[derive(Clone, Serialize, Debug, PartialEq, Eq)]
pub struct Constrain {
    lhs: Expression,
    rhs: Expression,
}

impl Display for Constrain {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} === {};", self.lhs, self.rhs)
    }
}

impl Stmt for Constrain {
    fn reads(&self) -> HashSet<&Ref> {
        let mut reads = self.lhs().variable_refs();
        reads.extend(self.rhs().variable_refs());
        reads
    }

    fn writes(&self) -> Option<&Ref> {
        None
    }
}

impl Constrain {
    pub fn lhs(&self) -> &Expression { &self.lhs }
    pub fn rhs(&self) -> &Expression { &self.rhs }

    pub fn new(lhs: Expression, rhs: Expression) -> Self {
        Self { lhs, rhs }
    }
}