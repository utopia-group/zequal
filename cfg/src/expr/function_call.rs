use std::collections::HashSet;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use itertools::Itertools;
use serde::Serialize;

use crate::error::CFGError;
use crate::expr::expression::{Expr, Expression};
use crate::expr::variable_ref::Ref;

#[derive(Clone, PartialEq, Eq, Serialize, Debug)]
pub enum FunctionReturnType {
    Var,
    VarArray(Vec<Expression>)
}

impl FunctionReturnType {
    pub fn var() -> Self {
        Self::Var
    }

    pub fn array(dims: Vec<Expression>) -> Self {
        Self::VarArray(dims)
    }
}

/* We are going to interpret functions as uninterpreted functions and assume that the return type
   is correct as circom does not requrie return types to be specified*/
#[derive(Clone, PartialEq, Eq, Serialize, Debug)]
pub struct FunctionCall {
    name: String,
    args: Vec<Expression>,
    ret_type: FunctionReturnType
}

impl Display for FunctionCall {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}({})", self.name, self.args.iter().map(|e| e.to_string()).join(", "))
    }
}

impl Hash for FunctionCall {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_string().hash(state)
    }
}

impl Expr for FunctionCall {
    fn variable_refs(&self) -> HashSet<&Ref> {
        let mut vars = HashSet::new();
        for arg in &self.args {
            vars.extend(arg.variable_refs());
        }

        vars
    }

    fn rename(&self, from: &Ref, to: &Ref) -> Result<Self, CFGError>
    where
        Self: Sized
    {
        let mut new_args = vec![];
        for arg in &self.args {
            new_args.push(arg.rename(from, to)?);
        }

        let new_ret_type = match &self.ret_type {
            FunctionReturnType::Var => { self.ret_type.clone() }
            FunctionReturnType::VarArray(dims) => {
                let mut new_dims = vec![];
                for dim in dims {
                    new_dims.push(dim.rename(from, to)?)
                }

                FunctionReturnType::array(new_dims)
            }
        };

        Ok(Self::new(self.name.clone(), new_args, new_ret_type))
    }
}

impl FunctionCall {
    pub fn name(&self) -> &String {
        &self.name
    }

    pub fn args(&self) -> &Vec<Expression> {
        &self.args
    }

    pub fn ret_type(&self) -> &FunctionReturnType {
        &self.ret_type
    }

    pub fn new(name: String, args: Vec<Expression>, ret_type: FunctionReturnType) -> Self {
        Self {name, args, ret_type }
    }
}