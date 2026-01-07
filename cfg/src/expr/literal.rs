use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use num_bigint_dig::BigInt;
use crate::expr::expression::{Expr, Expression};
use itertools::Itertools;
use serde::{Serialize, Serializer};
use crate::error::CFGError;
use crate::expr::variable_ref::Ref;

#[derive(Clone, PartialEq, Eq, Serialize, Debug)]
pub struct Boolean {
    val: bool
}

#[derive(Clone, PartialEq, Eq, Serialize, Debug)]
pub struct Number {
    #[serde(serialize_with = "Number::serialize_number")]
    val: BigInt,
}
#[derive(Clone, PartialEq, Eq, Serialize, Debug)]
pub struct UniformArray {
    val: Box<Expression>,
    dim: Box<Expression>,
}
#[derive(Clone, PartialEq, Eq, Serialize, Debug)]
pub struct InlineArray {
    entries: Vec<Expression>,
}

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Debug)]
pub enum Literal {
    Number(Number),
    UniformArray(UniformArray),
    InlineArray(InlineArray),
    Boolean(Boolean)
}

impl Display for Number {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val)
    }
}

impl Display for UniformArray {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "uniform_array({}[{}])", self.val, self.dim)
    }
}

impl Display for Boolean {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", if self.val {"true"} else {"false"})
    }
}

impl Display for InlineArray {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]", self.entries.iter().join(", "))
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Number(l) => { write!(f, "{}", l) }
            Literal::UniformArray(l) => { write!(f, "{}", l) }
            Literal::InlineArray(l) => { write!(f, "{}", l) }
            Literal::Boolean(l) => { write!(f, "{}", l) }
        }
    }
}

impl Expr for Number {
    fn variable_refs(&self) -> HashSet<&Ref> {
        HashSet::new()
    }

    fn rename(&self, _from: &Ref, _to: &Ref) -> Result<Self, CFGError> {
        Ok(self.clone())
    }
}

impl Hash for Number {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_string().hash(state)
    }
}

impl Number {
    pub fn serialize_number<S>(num: &BigInt, serializer: S) -> Result<S::Ok, S::Error> where S: Serializer {
        serializer.serialize_str(num.to_string().as_str())
    }
    pub fn val(&self) -> &BigInt { &self.val }
}

impl Expr for UniformArray {
    fn variable_refs(&self) -> HashSet<&Ref> {
        let mut refs = self.val.variable_refs();
        refs.extend(self.dim.variable_refs());
        refs
    }

    fn rename(&self, _from: &Ref, _to: &Ref) -> Result<Self, CFGError> {
        Ok(self.clone())
    }
}

impl Hash for UniformArray {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_string().hash(state)
    }
}

impl UniformArray {
    pub fn val(&self) -> &Expression { &self.val }
    pub fn dim(&self) -> &Expression { &self.dim }
}

impl Expr for InlineArray {
    fn variable_refs(&self) -> HashSet<&Ref> {
        let mut refs = HashSet::new();
        for e in self.entries() {
            refs.extend(e.variable_refs())
        }
        refs
    }

    fn rename(&self, _from: &Ref, _to: &Ref) -> Result<Self, CFGError> {
        Ok(self.clone())
    }
}

impl Hash for InlineArray {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_string().hash(state)
    }
}


impl InlineArray {
    pub fn entries(&self) -> &Vec<Expression> { &self.entries }
}

impl Expr for Boolean {
    fn variable_refs(&self) -> HashSet<&Ref> {
        HashSet::new()
    }

    fn rename(&self, _from: &Ref, _to: &Ref) -> Result<Self, CFGError> {
        Ok(self.clone())
    }
}

impl Hash for Boolean {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.val.hash(state)
    }
}

impl Boolean {
    pub fn val(&self) -> bool { self.val }
}

impl Expr for Literal {
    fn variable_refs(&self) -> HashSet<&Ref> {
        match self {
            Literal::Number(n) => {
                n.variable_refs()
            }
            Literal::UniformArray(a) => {
                a.variable_refs()
            }
            Literal::InlineArray(a) => {
                a.variable_refs()
            }
            Literal::Boolean(b) => {
                b.variable_refs()
            }
        }
    }

    fn rename(&self, _from: &Ref, _to: &Ref) -> Result<Self, CFGError> {
        Ok(self.clone())
    }
}

impl Literal {
    pub fn new_number(val: BigInt) -> Self {
        Self::Number(Number {val})
    }

    pub fn new_uniform_array(val: Box<Expression>, dim: Box<Expression>) -> Self {
        Self::UniformArray(UniformArray { val, dim })
    }

    pub fn new_inline_array(entries: Vec<Expression>) -> Self {
        Self::InlineArray(InlineArray { entries } )
    }

    pub fn new_boolean(val: bool) -> Self {
        Self::Boolean(Boolean { val })
    }
}