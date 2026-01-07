use std::cmp::min;
use std::collections::HashSet;
use std::fmt::Display;
use std::hash::{Hash, Hasher};

use serde::Serialize;
use crate::error::CFGError;

use crate::expr::binop::BinaryOperator;
use crate::expr::expression::{Expr, Expression};
use crate::expr::literal::Literal;
use crate::expr::var_access::AccessList;
use crate::expr::variable_ref::Ref;

#[derive(Clone, PartialEq, Eq, Serialize, Debug)]
pub enum InvariantExpr {
    Forall(Vec<String>, Box<InvariantExpr>),
    Exists(Vec<String>, Box<InvariantExpr>),
    Expr(Expression),
}

impl From<Expression> for InvariantExpr {
    fn from(value: Expression) -> Self {
        Self::Expr(value)
    }
}

impl Hash for InvariantExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_string().hash(state)
    }
}


impl Display for InvariantExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            InvariantExpr::Forall(v, t) => {
                format!("\u{2200} {}. {}", v.join(", "), t.to_string())
            }
            InvariantExpr::Exists(v, t) => {
                format!("\u{2203} {}. {}", v.join(", "), t.to_string())
            }
            InvariantExpr::Expr(e) => {
                e.to_string()
            }
        };
        write!(f, "{}", str)
    }
}

impl Expr for InvariantExpr {
    fn variable_refs(&self) -> HashSet<&Ref> {
        match self {
            InvariantExpr::Forall(vars, expr) => {
                let refs = expr.variable_refs();
                refs.into_iter()
                    .filter(|v_ref| !vars.contains(&v_ref.name().into()))
                    .collect()
            }
            InvariantExpr::Exists(vars, expr) => {
                let refs = expr.variable_refs();
                refs.into_iter()
                    .filter(|v_ref| !vars.contains(&v_ref.name().into()))
                    .collect()
            }
            InvariantExpr::Expr(expr) => {
                expr.variable_refs()
            }
        }
    }

    fn rename(&self, from: &Ref, to: &Ref) -> Result<Self, CFGError> {
        match self {
            InvariantExpr::Forall(vars, expr) => {
                let mut new_vars = vars.clone();
                match from {
                    Ref::Var(v) => {
                        for i in 0..new_vars.len() {
                            if new_vars[i].as_str() == v.name() {
                                new_vars[i] = to.name().into()
                            }
                        }
                    }
                    _ => { /* Skip */ }
                }

                let new_expr = Box::new(expr.rename(from, to)?);
                Ok(InvariantExpr::Forall(new_vars, new_expr))
            }
            InvariantExpr::Exists(vars, expr) => {
                let mut new_vars = vars.clone();
                match from {
                    Ref::Var(v) => {
                        for i in 0..new_vars.len() {
                            if new_vars[i].as_str() == v.name() {
                                new_vars[i] = to.name().into()
                            }
                        }
                    }
                    _ => { /* Skip */ }
                }

                let new_expr = Box::new(expr.rename(from, to)?);
                Ok(InvariantExpr::Exists(new_vars, new_expr))
            }
            InvariantExpr::Expr(expr) => {
                Ok(InvariantExpr::Expr(expr.rename(from, to)?))
            }
        }
    }
}

impl InvariantExpr {
    pub fn forall(self, mut vars: Vec<String>) -> Self {
        if vars.is_empty() {
            return self
        }

        match self {
            InvariantExpr::Forall(v, e) => {
                vars.extend(v);
                InvariantExpr::Forall(vars, e)
            }
            _ => {
                InvariantExpr::Forall(vars, Box::new(self))
            }
        }
    }

    pub fn rename_quantifier(&self, old_name: &String, new_name: &String) -> Result<Self, CFGError> {
        let old_quantifier = Ref::new_var_ref(old_name.clone(), AccessList::empty(), 0, true, true);
        let new_quantifier = Ref::new_var_ref(new_name.clone(), AccessList::empty(), 0, true, true);
        self.rename(&old_quantifier, &new_quantifier)
    }

    pub fn exists(self, mut vars: Vec<String>) -> Self {
        if vars.is_empty() {
            return self
        }

        match self {
            InvariantExpr::Exists(v, e) => {
                vars.extend(v);
                InvariantExpr::Exists(vars, e)
            }
            _ => {
                InvariantExpr::Exists(vars, Box::new(self))
            }
        }
    }

    fn create_name<F>(base_name: &str, mut ind: usize, alias_check: F) -> String
        where F: Fn(&String) -> bool
    {
        let mut new_name = format!("{}{}", base_name, ind);
        while !alias_check(&new_name) {
            ind += 1;
            new_name = format!("{}{}", base_name, ind)
        }
        new_name
    }

    fn ensure_fresh_vars(vars: &Vec<String>, mut expr: InvariantExpr, existing_vars: &HashSet<String>, base_name: &str) -> Result<(Vec<String>, Self), CFGError> {
        let mut ret_vars = vec![];
        for var in vars {
            let mut q_name = var.clone();
            if existing_vars.contains(&q_name) {
                q_name = Self::create_name(base_name, existing_vars.len() + ret_vars.len(), |n| existing_vars.contains(n) || vars.contains(n) || ret_vars.contains(n));
                expr = expr.rename_quantifier(var, &q_name)?;
            }
            ret_vars.push(q_name)
        }

        Ok((ret_vars, expr))
    }

    fn and_helper(&self, other: &Self, mut all_vars: HashSet<String>) -> Result<Self, CFGError> {
        match self {
            InvariantExpr::Forall(self_vars, self_expr) => {
                match other {
                    InvariantExpr::Forall(other_vars, other_expr) => {
                        let mut ret_vars = self_vars.clone();
                        let mut other_renamed = other_expr.as_ref().clone();
                        let mut other_diff = other_vars.clone();
                        other_diff.retain(|v| !self_vars.contains(v));
                        let mut self_diff = self_vars.clone();
                        self_diff.retain(|v| !other_vars.contains(v));
                        for i in 0..min(other_diff.len(), self_diff.len()) {
                            other_renamed = other_renamed.rename_quantifier(&other_diff[i], &self_diff[i])?
                        }

                        if other_diff.len() > self_diff.len() {
                            //add variables to ret vars
                            for i in self_diff.len()..other_diff.len() {
                                let mut q_name = other_diff[i].clone();
                                if all_vars.contains(&q_name) {
                                    q_name = Self::create_name("uq", all_vars.len(), |n| all_vars.contains(n) || other_diff.contains(n));
                                    other_renamed = other_renamed.rename_quantifier(&other_diff[i], &q_name)?;
                                }
                                all_vars.insert(q_name.clone());
                                ret_vars.push(q_name)
                            }
                        }

                        //recurse
                        let unquantified = self_expr.and_helper(&other_renamed, all_vars)?;
                        Ok(InvariantExpr::Forall(ret_vars, Box::new(unquantified)))
                    }
                    _ => {
                        // recurse to find matching statement type (exists or unquantified)
                        let unquantified = self_expr.and_helper(other, all_vars)?;
                        Ok(InvariantExpr::Forall(self_vars.clone(), Box::new(unquantified)))
                    }
                }
            }
            InvariantExpr::Exists(self_vars, self_expr) => {
                match other {
                    InvariantExpr::Exists(other_vars, other_expr) => {
                        let mut ret_vars = self_vars.clone();
                        let (other_renamed_vars, other_renamed) = Self::ensure_fresh_vars(other_vars, other_expr.as_ref().clone(), &all_vars, "eq")?;
                        ret_vars.extend(other_renamed_vars.clone().into_iter());
                        all_vars.extend(other_renamed_vars.into_iter());
                        let unquantified = self_expr.and_helper(&other_renamed, all_vars)?;
                        Ok(InvariantExpr::Exists(ret_vars, Box::new(unquantified)))
                    }
                    _ => {
                        // recurse to find matching statement type (exists or unquantified)
                        let unquantified = self_expr.and_helper(other, all_vars)?;
                        Ok(InvariantExpr::Exists(self_vars.clone(), Box::new(unquantified)))
                    }
                }
            }
            InvariantExpr::Expr(self_expr) => {
                match other {
                    InvariantExpr::Forall(other_vars, other_expr) => {
                        //rename to fresh vars if necessary
                        let (other_renamed_vars, other_renamed) = Self::ensure_fresh_vars(other_vars, other_expr.as_ref().clone(), &all_vars, "uq")?;
                        all_vars.extend(other_renamed_vars.clone().into_iter());
                        let unquantified = self.and_helper(&other_renamed, all_vars)?;
                        Ok(InvariantExpr::Forall(other_renamed_vars, Box::new(unquantified)))
                    }
                    InvariantExpr::Exists(other_vars, other_expr) => {
                        //rename to fresh vars if necessary
                        let (other_renamed_vars, other_renamed) = Self::ensure_fresh_vars(other_vars, other_expr.as_ref().clone(), &all_vars, "eq")?;
                        all_vars.extend(other_renamed_vars.clone().into_iter());
                        let unquantified = self.and_helper(&other_renamed, all_vars)?;
                        Ok(InvariantExpr::Exists(other_renamed_vars, Box::new(unquantified)))
                    }
                    InvariantExpr::Expr(other_expr) => {
                        Ok(InvariantExpr::Expr(Expression::new_binop(Box::new(self_expr.clone()), BinaryOperator::And, Box::new(other_expr.clone()))))
                    }
                }
            }
        }
    }

    pub fn and_all(mut conjuncts: Vec<Self>) -> Result<Self, CFGError> {
        // Iterate over all signal equality constraints and conjoin them so that quantifiers get merged
        if let Some(mut lhs) = conjuncts.pop() {
            while let Some(rhs) = conjuncts.pop() {
                lhs = lhs.and(&rhs)?;
            }
            Ok(lhs)
        }
        else {
            Ok(Expression::new_literal(Literal::new_boolean(true)).into())
        }
    }

    pub fn and(&self, other: &Self) -> Result<Self, CFGError> {
        let mut all_vars = HashSet::new();
        let mut cur_expr = self;
        loop {
            match cur_expr {
                InvariantExpr::Forall(vars, e) => {
                    for q in vars {
                        all_vars.insert(q.clone());
                    }
                    cur_expr = e;
                }
                InvariantExpr::Exists(vars, e) => {
                    for q in vars {
                        all_vars.insert(q.clone());
                    }
                    cur_expr = e;
                }
                InvariantExpr::Expr(_) => {
                    break;
                }
            }
        }
        self.and_helper(other, all_vars)
    }
}