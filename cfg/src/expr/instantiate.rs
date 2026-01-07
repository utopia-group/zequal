use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use crate::expr::expression::{Expr, Expression};
use itertools::Itertools;
use serde::{Serialize};
use crate::error::CFGError;
use crate::expr::variable_ref::Ref;

#[derive(Clone, PartialEq, Eq, Serialize, Debug)]
pub struct Instantiate {
    name: String,
    args: Vec<Expression>
}

impl Display for Instantiate {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}({})", self.name, self.args.iter().join(", "))
    }
}

impl Hash for Instantiate {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_string().hash(state)
    }
}

impl Expr for Instantiate {
    fn variable_refs(&self) -> HashSet<&Ref> {
        let mut refs = HashSet::new();
        for arg in self.args() {
            refs.extend(arg.variable_refs())
        }

        refs
    }

    fn rename(&self, from: &Ref, to: &Ref) -> Result<Self, CFGError> {
        let args = self.args.iter().map(|e| e.rename(from, to)).collect::<Result<Vec<_>, _>>()?;
        Ok(Self::new(self.name.clone(), args))
    }
}

impl Instantiate {
    pub fn name(&self) -> &str { self.name.as_str() }
    pub fn args(&self) -> &Vec<Expression> { &self.args }

    pub fn new(name: String, args: Vec<Expression>) -> Self {
        Self { name, args }
    }
}