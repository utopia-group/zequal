use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use serde::{Serialize};
use crate::expr::var_access::Access;
use crate::expr::expression::{Expr, Expression};
use crate::expr::variable_ref::{Ref};
use crate::stmt::statement::Stmt;

#[derive(Clone, Serialize, Debug, PartialEq, Eq)]
pub struct AssignVar {
    lhs: Ref,
    rhs: Expression,
}

impl Display for AssignVar {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = {};", self.lhs, self.rhs)
    }
}

impl Stmt for AssignVar {
    fn reads(&self) -> HashSet<&Ref> {
        let mut reads = HashSet::new();
        for acc in self.lhs().access().iter() {
            match acc {
                Access::Array { ind } => {
                    reads.extend(ind.variable_refs())
                }
                Access::Component { .. } => {}
            }
        }
        reads.extend(self.rhs().variable_refs());

        reads
    }

    fn writes(&self) -> Option<&Ref> {
        Some(self.lhs())
    }
}

impl AssignVar {
    pub fn lhs(&self) -> &Ref { &self.lhs }
    pub fn rhs(&self) -> &Expression { &self.rhs }

    pub fn new(lhs: Ref, rhs: Expression) -> Self {
        Self {lhs, rhs}
    }
}