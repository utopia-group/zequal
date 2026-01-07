use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use serde::{Serialize};
use crate::error::CFGError;
use crate::expr::expression::{Expr, Expression};
use crate::expr::variable_ref::Ref;

#[derive(Clone, PartialEq, Eq, Serialize, Debug)]
pub struct Ternary {
    cond: Box<Expression>,
    true_case: Box<Expression>,
    false_case: Box<Expression>,
}

impl Display for Ternary {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ? {} : {}", self.cond, self.true_case, self.false_case)
    }
}

impl Hash for Ternary {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_string().hash(state)
    }
}


impl Expr for Ternary {
    fn variable_refs(&self) -> HashSet<&Ref> {
        let mut refs = self.cond().variable_refs();
        refs.extend(self.true_case().variable_refs());
        refs.extend(self.false_case().variable_refs());
        refs
    }

    fn rename(&self, from: &Ref, to: &Ref) -> Result<Self, CFGError> {
        let cond = Box::new(self.cond.rename(from, to)?);
        let true_case = Box::new(self.true_case.rename(from, to)?);
        let false_case = Box::new(self.false_case.rename(from, to)?);
        Ok(Self::new(cond, true_case, false_case))
    }
}

impl Ternary {
    pub fn cond(&self) -> &Expression { &self.cond }
    pub fn true_case(&self) -> &Expression { &self.true_case }
    pub fn false_case(&self) -> &Expression { &self.false_case }

    pub fn new(cond: Box<Expression>, true_case: Box<Expression>, false_case: Box<Expression>) -> Self {
        Ternary { cond, true_case, false_case }
    }
}