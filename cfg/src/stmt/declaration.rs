use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use itertools::Itertools;
use program_structure::ast::{SignalType};
use serde::{Serialize};
use crate::expr::expression::{Expr, Expression};
use crate::expr::variable_ref::Ref;
use crate::stmt::statement::Stmt;

#[derive(Clone, Copy, Serialize, Debug, PartialEq, Eq)]
pub enum SigType {
    Input,
    Output,
    Intermediate
}

#[derive(Clone, Serialize, Debug, PartialEq, Eq)]
pub enum VType {
    Var{is_input: bool},
    Sig{sig_type: SigType, tags: HashSet<String>},
    Component(String)
}

#[derive(Clone, Serialize, Debug, PartialEq, Eq)]
pub struct Declaration {
    is_const: bool,
    v_type: VType,
    name: String,
    dims: Vec<Expression>,
}

impl Display for SigType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SigType::Input => { write!(f, "input") }
            SigType::Output => { write!(f, "output") }
            SigType::Intermediate => { write!(f, "") }
        }
    }
}

impl Display for VType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            VType::Var {..} => { write!(f, "var") }
            VType::Sig { sig_type, tags } => {
                let s_type = sig_type.to_string();
                let mut mods = if s_type.is_empty() {  vec![] } else { vec![s_type] };
                mods.extend(tags.iter().map(|s| s.clone()));

                if mods.is_empty() {
                    write!(f, "signal")
                }
                else {
                    write!(f, "signal {}", mods.iter().join(" "))
                }
            }
            VType::Component(_) => { write!(f, "component")}
        }
    }
}

impl Display for Declaration {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.dims.len() == 0 {
            write!(f, "{} {};", self.v_type, self.name)
        }
        else {
            write!(f, "{} {}[{}];", self.v_type, self.name, self.dims.iter().join(""))
        }
    }
}

impl From<&SignalType> for SigType {
    fn from(value: &SignalType) -> Self {
        match value {
            SignalType::Output => { Self::Output }
            SignalType::Input => { Self::Input }
            SignalType::Intermediate => { Self::Intermediate }
        }
    }
}

impl Stmt for Declaration {
    fn reads(&self) -> HashSet<&Ref> {
        let mut refs: HashSet<&Ref> = HashSet::new();
        for d in self.dims() {
            refs.extend(d.variable_refs())
        }
        refs
    }

    fn writes(&self) -> Option<&Ref> {
        None
    }
}

impl Declaration {
    pub fn is_const(&self) -> bool { self.is_const }
    pub fn v_type(&self) -> &VType { &self.v_type }
    pub fn name(&self) -> &str { self.name.as_str() }
    pub fn dims(&self) -> &Vec<Expression> { &self.dims }

    pub fn new(v_type: VType, is_const: bool, name: String, dims: Vec<Expression>) -> Self {
        Self { v_type, is_const, name, dims }
    }
}