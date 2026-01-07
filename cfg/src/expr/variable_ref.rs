use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use itertools::Itertools;
use num_bigint_dig::BigInt;
use program_structure::ast;
use serde::{Serialize};
use crate::cfg::CFG;
use crate::error::CFGError;
use crate::expr::binop::BinaryOperator;
use crate::expr::expression::{Expr, Expression};
use crate::expr::invariant::InvariantExpr;
use crate::expr::literal::Literal;
use crate::expr::unop::UnaryOperator;
use crate::expr::var_access::{Access, AccessList, StorageAccess};
use crate::named_storage::{Component, NamedStorage, Signal, Var};
use crate::template::Template;
use num_traits::identities::Zero;
use crate::block::Block;
use crate::storage_type::TypeInference;

#[derive(Clone, PartialEq, Eq, Serialize, Debug)]
pub struct VarRef {
    id: String,
    name: String,
    access: AccessList<Access>,
    version: usize,
    ref_witness: bool,
    ref_constraint: bool
}

#[derive(Clone, PartialEq, Eq, Serialize, Debug)]
pub struct SignalRef {
    id: String,
    name: String,
    access: AccessList<Access>,
    ref_witness: bool,
    ref_constraint: bool
}

#[derive(Clone, PartialEq, Eq, Serialize, Debug)]
pub struct ComponentRef {
    name: String,
    access: AccessList<Access>,
    invoked: String,
    params: Vec<VarRef>
}

#[derive(Clone, PartialEq, Eq, Serialize, Debug)]
pub enum Ref {
    Var(VarRef),
    Sig(SignalRef),
    Comp(ComponentRef)
}

impl Display for VarRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let tag = if self.ref_witness && !self.ref_constraint {
            ".w"
        }
        else if !self.ref_witness && self.ref_constraint {
            ".c"
        }
        else {
            ""
        };
        write!(f, "{}{}:{}{}", self.name, self.access.iter().join(""), self.version, tag)
    }
}

impl Hash for VarRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_string().hash(state)
    }
}

impl Display for SignalRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let tag = if self.ref_witness && !self.ref_constraint {
            ".w"
        }
        else if !self.ref_witness && self.ref_constraint {
            ".c"
        }
        else {
            ""
        };
        write!(f, "{}{}{}", self.name, self.access.iter().join(""), tag)
    }
}

impl Hash for SignalRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_string().hash(state)
    }
}

impl Display for Ref {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Ref::Var(r) => { write!(f, "{}", r) }
            Ref::Sig(r) => { write!(f, "{}", r) }
            Ref::Comp(r) => { write!(f, "{}", r) }
        }
    }
}

impl Hash for Ref {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_string().hash(state)
    }
}

impl Display for ComponentRef {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.name, self.access)
    }
}

impl Hash for ComponentRef {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_string().hash(state)
    }
}

impl Expr for Ref {
    fn variable_refs(&self) -> HashSet<&Ref> {
        let mut refs = HashSet::new();
        refs.insert(self);
        refs.extend(self.access().variable_refs());
        refs
    }

    fn rename(&self, from: &Ref, to: &Ref) -> Result<Self, CFGError> {
        let is_match = match (self, from) {
            (Ref::Var(self_var), Ref::Var(from_var)) => {
                self_var.is_match(from_var)
            }
            (Ref::Sig(self_sig), Ref::Sig(from_sig)) => {
                self_sig.is_match(from_sig)
            }
            (Ref::Comp(self_comp), Ref::Comp(from_comp)) => {
                self_comp.is_match(from_comp)
            }
            _ => {
                false
            }
        };

        if is_match {
            // Match found! Copy to and add any access entries that are in self but not from
            let mut new_ref = to.clone();
            // We only replace the part that is referenced by self
            new_ref.change_ref_witness(self.ref_witness());
            new_ref.change_ref_constraint(self.ref_constraint());

            let new_access = new_ref.access_mut();
            for i in from.access().len()..self.access().len() {
                new_access.push(self.access().get(i).rename(from, to)?)?;
            }

            Ok(new_ref)
        }
        else {
            let access_renaming = self.access().rename(from, to)?;
            let mut new_ref = self.clone();
            new_ref.change_access(access_renaming);
            Ok(new_ref)
        }
    }

    /*fn rename(&self, var: &String, new_name: &String) -> Self {
        match self {
            Ref::Var(self_var) => {
                Self::Var(self_var.rename(var, new_name))
            }
            Ref::Sig(self_sig) => {
                Self::Sig(self_sig.rename(var, new_name))
            }
            Ref::Comp(self_comp) => {
                Self::Comp(self_comp.rename(var, new_name))
            }
        }
    }*/
}

impl ComponentRef {
    pub fn var_id(&self) -> String { Ref::identifier(&self.name, &self.access) }
    pub fn name(&self) -> &str { self.name.as_str() }
    pub fn id(&self) -> &String { &self.name }
    pub fn access(&self) -> &AccessList<Access> { &self.access }
    pub fn params(&self) -> &Vec<VarRef> { &self.params }
    pub fn invoked(&self) -> &str { self.invoked.as_str() }
    /*fn rename(&self, var: &String, new_name: &String) -> Self {
        if &self.name == var {
            Self::new(new_name.clone(), self.access.rename(var, new_name), self.invoked.clone(), self.params.clone())
        }
        else {
            self.clone()
        }
    }*/

    pub fn is_match(&self, from: &Self) -> bool {
        // don't need to check params because if invoked is equal then params should be equal
        if self.name != from.name || self.invoked != from.invoked || self.access.len() < from.access.len() {
            return false
        }

        // check if subset of access matches from
        for i in 0..from.access.len() {
            if self.access.get(i) != from.access.get(i) {
                return false
            }
        }

        true
    }

    /*
     * Assumes that any array access can alias, does not attempt to resolve distinct indices
     */
    pub fn may_alias(&self, other: &Self) -> bool {
        let self_comp = self.access.get_component_access();
        let self_comp_ind = self.access.get_component_access_ind();
        let other_comp = other.access.get_component_access();
        let other_comp_ind = other.access.get_component_access_ind();

        self.name == other.name && self_comp == other_comp && self_comp_ind == other_comp_ind &&
            self.invoked == other.invoked && self.params == other.params
    }

    pub fn change_access(&mut self, access: AccessList<Access>) {
        self.access = access;
    }

    pub fn new(name: String, access: AccessList<Access>, invoked: String, params: Vec<VarRef>) -> Self {
        Self { name, access, invoked, params }
    }

    pub fn create_equality_constraint(&self, cfg: &CFG, template: &Template, at_blk: &Block, is_before_block: bool) -> Result<Vec<InvariantExpr>, CFGError> {
        let component = template.get_referenced_component(cfg, self)?;
        let invoked = cfg.get_template(&component.instance_of().into())?;
        let component_access = self.access();
        let mut eq_constraints = vec![];

        for var in &invoked.input_vars {
            // Construct Variable Ref
            let mut var_access = component_access.clone();
            var_access.push(Access::new_component_access(var.name().into()))?;
            let var_ref = if is_before_block {
                at_blk.pre_ref_component(cfg, component, var_access, true, true)?
            }
            else {
                at_blk.post_ref_component(cfg, component, var_access, true, true)?
            };

            // Get equality constraint of var ref
            eq_constraints.extend(var_ref.create_equality_constraint(cfg, template, at_blk, is_before_block)?);
        }

        for sig in &invoked.input_signals {
            // Construct Signal Ref
            let mut sig_access = component_access.clone();
            sig_access.push(Access::new_component_access(sig.name().into()))?;
            let sig = SignalRef::new(self.name().into(), sig_access, true, true);
            // Get equality constraint of signal ref
            eq_constraints.extend(sig.create_equality_constraint(cfg, template, at_blk, is_before_block)?);
        }

        for sig in &invoked.output_signals {
            // Construct Signal Ref
            let mut sig_access = component_access.clone();
            sig_access.push(Access::new_component_access(sig.name().into()))?;
            let sig = SignalRef::new(self.name().into(), sig_access, true, true);
            // Get equality constraint of signal ref
            eq_constraints.extend(sig.create_equality_constraint(cfg, template, at_blk, is_before_block)?);
        }

        Ok(eq_constraints)
    }

    pub fn create_any_equality_constraint(&self, cfg: &CFG, template: &Template, at_blk: &Block, is_before_block: bool) -> Result<Vec<InvariantExpr>, CFGError> {
        let component = template.get_referenced_component(cfg, self)?;
        let invoked = cfg.get_template(&component.instance_of().into())?;
        let component_access = self.access();
        let mut eq_constraints = vec![];

        for var in &invoked.input_vars {
            // Construct Variable Ref
            let mut var_access = component_access.clone();
            var_access.push(Access::new_component_access(var.name().into()))?;
            let var_ref = if is_before_block {
                at_blk.pre_ref_component(cfg, component, var_access, true, true)?
            }
            else {
                at_blk.post_ref_component(cfg, component, var_access, true, true)?
            };

            // Get equality constraint of var ref
            eq_constraints.extend(var_ref.create_any_equality_constraint(cfg, template, at_blk, is_before_block)?);
        }

        for sig in &invoked.input_signals {
            // Construct Signal Ref
            let mut sig_access = component_access.clone();
            sig_access.push(Access::new_component_access(sig.name().into()))?;
            let sig = SignalRef::new(self.name().into(), sig_access, true, true);
            // Get equality constraint of signal ref
            eq_constraints.extend(sig.create_any_equality_constraint(cfg, template, at_blk, is_before_block)?);
        }

        for sig in &invoked.output_signals {
            // Construct Signal Ref
            let mut sig_access = component_access.clone();
            sig_access.push(Access::new_component_access(sig.name().into()))?;
            let sig = SignalRef::new(self.name().into(), sig_access, true, true);
            // Get equality constraint of signal ref
            eq_constraints.extend(sig.create_any_equality_constraint(cfg, template, at_blk, is_before_block)?);
        }

        Ok(eq_constraints)
    }
}

impl VarRef {
    pub fn var_id(&self) -> String { Ref::identifier(&self.name, &self.access) }
    pub fn name(&self) -> &str { &self.name }
    pub fn id(&self) -> &String { &self.id }
    pub fn access(&self) -> &AccessList<Access> { &self.access }
    pub fn version(&self) -> usize { self.version }
    pub fn ref_witness(&self) -> bool { self.ref_witness }
    pub fn ref_constraint(&self) -> bool { self.ref_constraint }

    pub fn change_version(&mut self, new_version: usize) {
        self.version = new_version
    }
    /*fn rename(&self, var: &String, new_name: &String) -> Self {
        if &self.name == var {
            Self::new(new_name.clone(), self.access.rename(var, new_name), 0)
        }
        else {
            self.clone()
        }
    }*/

    pub fn is_match(&self, from: &Self) -> bool {
        // don't need to id because it is constructed from name, access and version. We might be renaming
        // a part of the reference that would affect the id
        if self.name != from.name || self.version != from.version || self.access.len() < from.access.len() {
            return false
        }

        if self.ref_witness != from.ref_witness && self.ref_constraint != from.ref_constraint {
            return false
        }

        // check if subset of access matches from
        for i in 0..from.access.len() {
            if self.access.get(i) != from.access.get(i) {
                return false
            }
        }

        true
    }

    /*
     * Assumes that any array access can alias, does not attempt to resolve distinct indices
     * Also assumes that versions can alias each other
     */
    pub fn may_alias(&self, other: &Self) -> bool {
        let self_comp = self.access.get_component_access();
        let self_comp_ind = self.access.get_component_access_ind();
        let other_comp = other.access.get_component_access();
        let other_comp_ind = other.access.get_component_access_ind();

        self.name == other.name && self_comp == other_comp && self_comp_ind == other_comp_ind
    }

    pub fn change_access(&mut self, access: AccessList<Access>) {
        self.access = access;
    }

    pub fn new(name: String, access: AccessList<Access>, version: usize, ref_witness: bool, ref_constraint: bool) -> Self {
        let id = format!("v_{}.{}", Ref::identifier(&name, &access), version);
        Self { id, name, access, version, ref_witness, ref_constraint }
    }

    /*
     * Doing this quickly, eventually would be better to unify this with Sig::create_equality_constraint as they're pretty much the same
     */
    pub fn create_equality_constraint(&self, cfg: &CFG, template: &Template, at_blk: &Block, is_before_block: bool) -> Result<Vec<InvariantExpr>, CFGError> {
        let (maybe_component, sig) = template.get_referenced_var(cfg, self)?;
        let mut missing_dims = vec![];
        let mut dim_constraints: Vec<Expression> = vec![];
        let mut new_access = AccessList::empty();
        let mut renamings = HashMap::new();
        match maybe_component {
            Some(component) => {
                let Some(component_access_ind) = self.access().get_component_access_ind() else { unreachable!("Could not find component access index") };

                // add quantified component dims
                let component_dims = component.dims();
                for i in 0..component_dims.len() {
                    if i < component_access_ind {
                        new_access.push(self.access.get(i).clone())?;
                    }
                    else {
                        let quantifier = format!("uq{}", missing_dims.len());
                        let quant_ref = Ref::new_var_ref(quantifier.clone(), AccessList::empty(), 0, true, true);
                        let quant_expr = Expression::new_variable(quant_ref);
                        new_access.push(Access::new_array_access(quant_expr.clone()))?;

                        let zero_expr = Expression::new_literal(Literal::new_number(BigInt::zero()));
                        let lower_bound_check = Expression::new_binop(Box::new(quant_expr.clone()), BinaryOperator::Gte, Box::new(zero_expr));
                        dim_constraints.push(lower_bound_check);

                        let upper_bound = component_dims[i].clone();
                        let upper_bound_check = Expression::new_binop(Box::new(quant_expr), BinaryOperator::Lt, Box::new(upper_bound));
                        dim_constraints.push(upper_bound_check);

                        missing_dims.push(quantifier);
                    }
                }

                // need to perform a renaming
                let referenced_template = cfg.get_template(&component.instance_of().into())?;
                for var in &referenced_template.input_vars {
                    let old_var = referenced_template.pre_ref_var(var, AccessList::empty(), true, true)?;
                    let mut new_var_access = new_access.clone();
                    new_var_access.push(Access::new_component_access(var.name().into()))?;
                    let new_var = if is_before_block {
                        at_blk.pre_ref_component(cfg, component, new_var_access, true, true)?
                    }
                    else {
                        at_blk.post_ref_component(cfg, component, new_var_access, true, true)?
                    };
                    renamings.insert(old_var, new_var);
                }

                new_access.push(Access::new_component_access(sig.name().into()))?;
            }
            None => { /* Skip */ }
        }

        // add quantified signal dims
        let sig_access_start = new_access.len() - missing_dims.len();
        let sig_dims = sig.dims();
        for i in 0..sig_dims.len() {
            if sig_access_start + i < self.access.len() {
                new_access.push(self.access.get(sig_access_start + i).clone())?;
            }
            else {
                let quantifier = format!("uq{}", missing_dims.len());
                let quant_ref = Ref::new_var_ref(quantifier.clone(), AccessList::empty(), 0, true, true);
                let quant_expr = Expression::new_variable(quant_ref);
                new_access.push(Access::new_array_access(quant_expr.clone()))?;

                let zero_expr = Expression::new_literal(Literal::new_number(BigInt::zero()));
                let lower_bound = Expression::new_binop(Box::new(quant_expr.clone()), BinaryOperator::Gte, Box::new(zero_expr));
                dim_constraints.push(lower_bound);

                let upper_bound = sig_dims[i].rename_all(&renamings)?;
                let upper_bound_check = Expression::new_binop(Box::new(quant_expr), BinaryOperator::Lt, Box::new(upper_bound));
                dim_constraints.push(upper_bound_check);

                missing_dims.push(quantifier);
            }
        }

        // create equality constraint with dims
        let new_w_ref = Ref::Var(Self::new(self.name.clone(), new_access.clone(), self.version, true, false));
        let new_c_ref = Ref::Var(Self::new(self.name.clone(), new_access, self.version, false, true));
        let w_expr = Box::new(Expression::new_variable(new_w_ref));
        let c_expr = Box::new(Expression::new_variable(new_c_ref));
        let eq_expr = Expression::new_binop(w_expr, BinaryOperator::Eq, c_expr);
        let check = if dim_constraints.is_empty() {
            eq_expr
        }
        else {
            let dim_constraint = Expression::and_all(dim_constraints);
            let dim_negation = Expression::new_unop(UnaryOperator::Not, Box::new(dim_constraint));
            Expression::new_binop(Box::new(dim_negation), BinaryOperator::Or, Box::new(eq_expr))
        };

        // indices must be accessed using "known" i.e. equivalent values
        let mut ind_refs = vec![];
        for ind_ref in self.access.variable_refs() {
            ind_refs.extend(ind_ref.create_equality_constraint(cfg, template, at_blk, is_before_block)?);
        }

        if ind_refs.is_empty() {
            let check_inv: InvariantExpr = check.into();
            Ok(vec![check_inv.forall(missing_dims)])
        }
        else {
            let ind_equality = InvariantExpr::and_all(ind_refs)?;
            match ind_equality {
                InvariantExpr::Expr(expr) => {
                    let imp: InvariantExpr = Expression::new_binop(Box::new(Expression::new_unop(UnaryOperator::Not, Box::new(expr.clone()))), BinaryOperator::Or, Box::new(check)).into();
                    Ok(vec![imp.forall(missing_dims)])
                }
                _ => {unreachable!("Index expression cannot be quantified!")}
            }
        }
    }

    pub fn create_any_equality_constraint(&self, cfg: &CFG, template: &Template, at_blk: &Block, is_before_block: bool) -> Result<Vec<InvariantExpr>, CFGError> {
        let (maybe_component, sig) = template.get_referenced_var(cfg, self)?;
        let mut missing_dims = vec![];
        let mut dim_constraints: Vec<Expression> = vec![];
        let mut empty_constraints: Vec<Expression> = vec![];
        let mut new_access = AccessList::empty();
        let mut renamings = HashMap::new();
        match maybe_component {
            Some(component) => {
                let Some(component_access_ind) = self.access().get_component_access_ind() else { unreachable!("Could not find component access index") };

                // add quantified component dims
                let component_dims = component.dims();
                for i in 0..component_dims.len() {
                    if i < component_access_ind {
                        new_access.push(self.access.get(i).clone())?;
                    }
                    else {
                        let quantifier = format!("uq{}", missing_dims.len());
                        let quant_ref = Ref::new_var_ref(quantifier.clone(), AccessList::empty(), 0, true, true);
                        let quant_expr = Expression::new_variable(quant_ref);
                        new_access.push(Access::new_array_access(quant_expr.clone()))?;

                        let zero_expr = Expression::new_literal(Literal::new_number(BigInt::zero()));
                        let lower_bound_check = Expression::new_binop(Box::new(quant_expr.clone()), BinaryOperator::Gte, Box::new(zero_expr.clone()));
                        dim_constraints.push(lower_bound_check);

                        let upper_bound = component_dims[i].clone();
                        let upper_bound_check = Expression::new_binop(Box::new(quant_expr), BinaryOperator::Lt, Box::new(upper_bound.clone()));
                        dim_constraints.push(upper_bound_check);

                        let empty_check = Expression::new_binop(Box::new(zero_expr), BinaryOperator::Eq, Box::new(upper_bound));
                        empty_constraints.push(empty_check);

                        missing_dims.push(quantifier);
                    }
                }

                // need to perform a renaming
                let referenced_template = cfg.get_template(&component.instance_of().into())?;
                for var in &referenced_template.input_vars {
                    let old_var = referenced_template.pre_ref_var(var, AccessList::empty(), true, true)?;
                    let mut new_var_access = new_access.clone();
                    new_var_access.push(Access::new_component_access(var.name().into()))?;
                    let new_var = if is_before_block {
                        at_blk.pre_ref_component(cfg, component, new_var_access, true, true)?
                    }
                    else {
                        at_blk.post_ref_component(cfg, component, new_var_access, true, true)?
                    };
                    renamings.insert(old_var, new_var);
                }

                new_access.push(Access::new_component_access(sig.name().into()))?;
            }
            None => { /* Skip */ }
        }

        // add quantified signal dims
        let sig_access_start = new_access.len() - missing_dims.len();
        let sig_dims = sig.dims();
        for i in 0..sig_dims.len() {
            if sig_access_start + i < self.access.len() {
                new_access.push(self.access.get(sig_access_start + i).clone())?;
            }
            else {
                let quantifier = format!("uq{}", missing_dims.len());
                let quant_ref = Ref::new_var_ref(quantifier.clone(), AccessList::empty(), 0, true, true);
                let quant_expr = Expression::new_variable(quant_ref);
                new_access.push(Access::new_array_access(quant_expr.clone()))?;

                let zero_expr = Expression::new_literal(Literal::new_number(BigInt::zero()));
                let lower_bound = Expression::new_binop(Box::new(quant_expr.clone()), BinaryOperator::Gte, Box::new(zero_expr.clone()));
                dim_constraints.push(lower_bound);

                let upper_bound = sig_dims[i].rename_all(&renamings)?;
                let upper_bound_check = Expression::new_binop(Box::new(quant_expr), BinaryOperator::Lt, Box::new(upper_bound.clone()));
                dim_constraints.push(upper_bound_check);

                let empty_check = Expression::new_binop(Box::new(zero_expr), BinaryOperator::Eq, Box::new(upper_bound));
                empty_constraints.push(empty_check);

                missing_dims.push(quantifier);
            }
        }

        // create equality constraint with dims
        let new_w_ref = Ref::Var(Self::new(self.name.clone(), new_access.clone(), self.version, true, false));
        let new_c_ref = Ref::Var(Self::new(self.name.clone(), new_access, self.version, false, true));
        let w_expr = Box::new(Expression::new_variable(new_w_ref));
        let c_expr = Box::new(Expression::new_variable(new_c_ref));
        let eq_expr = Expression::new_binop(w_expr, BinaryOperator::Eq, c_expr);
        let check = if dim_constraints.is_empty() {
            eq_expr
        }
        else {
            let dim_constraint = Expression::and_all(dim_constraints);
            let non_empty = Expression::new_binop(Box::new(dim_constraint), BinaryOperator::And, Box::new(eq_expr));
            //empty_constraints.push(non_empty);
            //Expression::or_all(empty_constraints)
            non_empty
        };


        let check_inv: InvariantExpr = check.into();
        Ok(vec![check_inv.exists(missing_dims)])
    }
}

impl SignalRef {
    pub fn var_id(&self) -> String { Ref::identifier(&self.name, &self.access) }
    pub fn name(&self) -> &str { self.name.as_str() }
    pub fn id(&self) -> &String { &self.id }
    pub fn access(&self) -> &AccessList<Access> { &self.access }
    pub fn ref_witness(&self) -> bool { self.ref_witness }
    pub fn ref_constraint(&self) -> bool { self.ref_constraint }
    /*fn rename(&self, var: &String, new_name: &String) -> Self {
        if &self.name == var {
            Self::new(new_name.clone(), self.access.rename(var, new_name), self.ref_witness, self.ref_constraint)
        }
        else {
            self.clone()
        }
    }*/

    pub fn is_match(&self, from: &Self) -> bool {
        // don't need to id because it is constructed from name, access and version. We might be renaming
        // a part of the reference that would affect the id
        if self.name != from.name || self.access.len() < from.access.len() {
            return false
        }

        if self.ref_witness != from.ref_witness && self.ref_constraint != from.ref_constraint {
            return false
        }

        // check if subset of access matches from
        for i in 0..from.access.len() {
            if self.access.get(i) != from.access.get(i) {
                return false
            }
        }

        true
    }

    /*
     * Assumes that any array access can alias, does not attempt to resolve distinct indices
     */
    pub fn may_alias(&self, other: &Self) -> bool {
        let self_comp = self.access.get_component_access();
        let self_comp_ind = self.access.get_component_access_ind();
        let other_comp = other.access.get_component_access();
        let other_comp_ind = other.access.get_component_access_ind();

        self.name == other.name && self_comp == other_comp && self_comp_ind == other_comp_ind &&
            ((self.ref_constraint && other.ref_constraint) || (self.ref_witness && other.ref_witness))
    }

    pub fn change_access(&mut self, access: AccessList<Access>) {
        self.access = access;
    }

    pub fn new(name: String, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Self {
        let id = format!("s_{}", Ref::identifier(&name, &access));
        Self { id, name, access, ref_witness, ref_constraint }
    }

    pub fn create_equality_constraint(&self, cfg: &CFG, template: &Template, at_blk: &Block, is_before_block: bool) -> Result<Vec<InvariantExpr>, CFGError> {
        let (maybe_component, sig) = template.get_referenced_sig(cfg, self)?;
        let mut missing_dims = vec![];
        let mut dim_constraints: Vec<Expression> = vec![];
        let mut new_access = AccessList::empty();
        let mut renamings = HashMap::new();
        match maybe_component {
            Some(component) => {
                let Some(component_access_ind) = self.access().get_component_access_ind() else { unreachable!("Could not find component access index") };

                // add quantified component dims
                let component_dims = component.dims();
                for i in 0..component_dims.len() {
                    if i < component_access_ind {
                        new_access.push(self.access.get(i).clone())?;
                    }
                    else {
                        let quantifier = format!("uq{}", missing_dims.len());
                        let quant_ref = Ref::new_var_ref(quantifier.clone(), AccessList::empty(), 0, true, true);
                        let quant_expr = Expression::new_variable(quant_ref);
                        new_access.push(Access::new_array_access(quant_expr.clone()))?;

                        let zero_expr = Expression::new_literal(Literal::new_number(BigInt::zero()));
                        let lower_bound_check = Expression::new_binop(Box::new(quant_expr.clone()), BinaryOperator::Gte, Box::new(zero_expr));
                        dim_constraints.push(lower_bound_check);

                        let upper_bound = component_dims[i].clone();
                        let upper_bound_check = Expression::new_binop(Box::new(quant_expr), BinaryOperator::Lt, Box::new(upper_bound));
                        dim_constraints.push(upper_bound_check);

                        missing_dims.push(quantifier);
                    }
                }

                // need to perform a renaming
                let referenced_template = cfg.get_template(&component.instance_of().into())?;
                for var in &referenced_template.input_vars {
                    let old_var = referenced_template.pre_ref_var(var, AccessList::empty(), true, true)?;
                    let mut new_var_access = new_access.clone();
                    new_var_access.push(Access::new_component_access(var.name().into()))?;
                    let new_var = if is_before_block {
                        at_blk.pre_ref_component(cfg, component, new_var_access, true, true)?
                    }
                    else {
                        at_blk.post_ref_component(cfg, component, new_var_access, true, true)?
                    };
                    renamings.insert(old_var, new_var);
                }

                new_access.push(Access::new_component_access(sig.name().into()))?;
            }
            None => { /* Skip */ }
        }

        // add quantified signal dims
        let sig_access_start = new_access.len() - missing_dims.len();
        let sig_dims = sig.dims();
        for i in 0..sig_dims.len() {
            if sig_access_start + i < self.access.len() {
                new_access.push(self.access.get(sig_access_start + i).clone())?;
            }
            else {
                let quantifier = format!("uq{}", missing_dims.len());
                let quant_ref = Ref::new_var_ref(quantifier.clone(), AccessList::empty(), 0, true, true);
                let quant_expr = Expression::new_variable(quant_ref);
                new_access.push(Access::new_array_access(quant_expr.clone()))?;

                let zero_expr = Expression::new_literal(Literal::new_number(BigInt::zero()));
                let lower_bound = Expression::new_binop(Box::new(quant_expr.clone()), BinaryOperator::Gte, Box::new(zero_expr));
                dim_constraints.push(lower_bound);

                let upper_bound = sig_dims[i].rename_all(&renamings)?;
                let upper_bound_check = Expression::new_binop(Box::new(quant_expr), BinaryOperator::Lt, Box::new(upper_bound));
                dim_constraints.push(upper_bound_check);

                missing_dims.push(quantifier);
            }
        }

        // create equality constraint with dims
        let new_w_ref = Ref::Sig(Self::new(self.name.clone(), new_access.clone(), true, false));
        let new_c_ref = Ref::Sig(Self::new(self.name.clone(), new_access, false, true));
        let w_expr = Box::new(Expression::new_variable(new_w_ref));
        let c_expr = Box::new(Expression::new_variable(new_c_ref));
        let eq_expr = Expression::new_binop(w_expr, BinaryOperator::Eq, c_expr);
        let check = if dim_constraints.is_empty() {
            eq_expr
        }
        else {
            let dim_constraint = Expression::and_all(dim_constraints);
            let dim_negation = Expression::new_unop(UnaryOperator::Not, Box::new(dim_constraint));
            Expression::new_binop(Box::new(dim_negation), BinaryOperator::Or, Box::new(eq_expr))
        };

        // indices must be accessed using "known" i.e. equivalent values
        let mut ind_refs = vec![];
        for ind_ref in self.access.variable_refs() {
            ind_refs.extend(ind_ref.create_equality_constraint(cfg, template, at_blk, is_before_block)?);
        }

        if ind_refs.is_empty() {
            let check_inv: InvariantExpr = check.into();
            Ok(vec![check_inv.forall(missing_dims)])
        }
        else {
            let ind_equality = InvariantExpr::and_all(ind_refs)?;
            match ind_equality {
                InvariantExpr::Expr(expr) => {
                    let imp: InvariantExpr = Expression::new_binop(Box::new(Expression::new_unop(UnaryOperator::Not, Box::new(expr.clone()))), BinaryOperator::Or, Box::new(check)).into();
                    Ok(vec![imp.forall(missing_dims)])
                }
                _ => {unreachable!("Index expression cannot be quantified!")}
            }
        }
        //Ok(vec![check.forall(missing_dims)])
    }

    pub fn create_any_equality_constraint(&self, cfg: &CFG, template: &Template, at_blk: &Block, is_before_block: bool) -> Result<Vec<InvariantExpr>, CFGError> {
        let (maybe_component, sig) = template.get_referenced_sig(cfg, self)?;
        let mut missing_dims = vec![];
        let mut dim_constraints: Vec<Expression> = vec![];
        let mut empty_constraints: Vec<Expression> = vec![];
        let mut new_access = AccessList::empty();
        let mut renamings = HashMap::new();
        match maybe_component {
            Some(component) => {
                let Some(component_access_ind) = self.access().get_component_access_ind() else { unreachable!("Could not find component access index") };

                // add quantified component dims
                let component_dims = component.dims();
                for i in 0..component_dims.len() {
                    if i < component_access_ind {
                        new_access.push(self.access.get(i).clone())?;
                    }
                    else {
                        let quantifier = format!("uq{}", missing_dims.len());
                        let quant_ref = Ref::new_var_ref(quantifier.clone(), AccessList::empty(), 0, true, true);
                        let quant_expr = Expression::new_variable(quant_ref);
                        new_access.push(Access::new_array_access(quant_expr.clone()))?;

                        let zero_expr = Expression::new_literal(Literal::new_number(BigInt::zero()));
                        let lower_bound_check = Expression::new_binop(Box::new(quant_expr.clone()), BinaryOperator::Gte, Box::new(zero_expr.clone()));
                        dim_constraints.push(lower_bound_check);

                        let upper_bound = component_dims[i].clone();
                        let upper_bound_check = Expression::new_binop(Box::new(quant_expr), BinaryOperator::Lt, Box::new(upper_bound.clone()));
                        dim_constraints.push(upper_bound_check);

                        let empty_check = Expression::new_binop(Box::new(zero_expr), BinaryOperator::Eq, Box::new(upper_bound));
                        empty_constraints.push(empty_check);

                        missing_dims.push(quantifier);
                    }
                }

                // need to perform a renaming
                let referenced_template = cfg.get_template(&component.instance_of().into())?;
                for var in &referenced_template.input_vars {
                    let old_var = referenced_template.pre_ref_var(var, AccessList::empty(), true, true)?;
                    let mut new_var_access = new_access.clone();
                    new_var_access.push(Access::new_component_access(var.name().into()))?;
                    let new_var = if is_before_block {
                        at_blk.pre_ref_component(cfg, component, new_var_access, true, true)?
                    }
                    else {
                        at_blk.post_ref_component(cfg, component, new_var_access, true, true)?
                    };
                    renamings.insert(old_var, new_var);
                }

                new_access.push(Access::new_component_access(sig.name().into()))?;
            }
            None => { /* Skip */ }
        }

        // add quantified signal dims
        let sig_access_start = new_access.len() - missing_dims.len();
        let sig_dims = sig.dims();
        for i in 0..sig_dims.len() {
            if sig_access_start + i < self.access.len() {
                new_access.push(self.access.get(sig_access_start + i).clone())?;
            }
            else {
                let quantifier = format!("uq{}", missing_dims.len());
                let quant_ref = Ref::new_var_ref(quantifier.clone(), AccessList::empty(), 0, true, true);
                let quant_expr = Expression::new_variable(quant_ref);
                new_access.push(Access::new_array_access(quant_expr.clone()))?;

                let zero_expr = Expression::new_literal(Literal::new_number(BigInt::zero()));
                let lower_bound = Expression::new_binop(Box::new(quant_expr.clone()), BinaryOperator::Gte, Box::new(zero_expr.clone()));
                dim_constraints.push(lower_bound);

                let upper_bound = sig_dims[i].rename_all(&renamings)?;
                let upper_bound_check = Expression::new_binop(Box::new(quant_expr), BinaryOperator::Lt, Box::new(upper_bound.clone()));
                dim_constraints.push(upper_bound_check);

                let empty_check = Expression::new_binop(Box::new(zero_expr), BinaryOperator::Eq, Box::new(upper_bound));
                empty_constraints.push(empty_check);

                missing_dims.push(quantifier);
            }
        }

        // create equality constraint with dims
        let new_w_ref = Ref::Sig(Self::new(self.name.clone(), new_access.clone(), true, false));
        let new_c_ref = Ref::Sig(Self::new(self.name.clone(), new_access, false, true));
        let w_expr = Box::new(Expression::new_variable(new_w_ref));
        let c_expr = Box::new(Expression::new_variable(new_c_ref));
        let eq_expr = Expression::new_binop(w_expr, BinaryOperator::Eq, c_expr);
        let check = if dim_constraints.is_empty() {
            eq_expr
        }
        else {
            let dim_constraint = Expression::and_all(dim_constraints);
            let non_empty = Expression::new_binop(Box::new(dim_constraint), BinaryOperator::And, Box::new(eq_expr));
            //empty_constraints.push(non_empty);
            //Expression::or_all(dim_constraints)
            non_empty
        };

        let check_inv: InvariantExpr = check.into();
        Ok(vec![check_inv.exists(missing_dims)])
    }
}

impl Ref {
    pub fn ref_witness(&self) -> bool {
        match self {
            Ref::Var(v) => { v.ref_witness() }
            Ref::Sig(s) => { s.ref_witness() }
            Ref::Comp(_) => { true }
        }
    }
    pub fn ref_constraint(&self) -> bool {
        match self {
            Ref::Var(v) => { v.ref_constraint() }
            Ref::Sig(s) => { s.ref_constraint() }
            Ref::Comp(_) => { true }
        }
    }
    pub fn var_id(&self) -> String {
        match self {
            Ref::Var(v) => { v.var_id() }
            Ref::Sig(s) => { s.var_id() }
            Ref::Comp(c) => { c.var_id() }
        }
    }
    pub fn name(&self) -> &str {
        match self {
            Ref::Var(r) => { r.name() }
            Ref::Sig(r) => { r.name() }
            Ref::Comp(r) => { r.name() }
        }
    }

    pub fn id(&self) -> &String {
        match self {
            Ref::Var(r) => { r.id() }
            Ref::Sig(r) => { r.id() }
            Ref::Comp(r) => { r.id() }
        }
    }

    pub fn access(&self) -> &AccessList<Access> {
        match self {
            Ref::Var(r) => { r.access() }
            Ref::Sig(r) => { r.access() }
            Ref::Comp(r) => { r.access() }
        }
    }

    fn access_mut(&mut self) -> &mut AccessList<Access> {
        match self {
            Ref::Var(r) => { &mut r.access }
            Ref::Sig(r) => { &mut r.access }
            Ref::Comp(r) => { &mut r.access }
        }
    }

    pub fn may_alias(&self, other: &Self) -> bool {
        // assume that aliasing can only occur if the same type. This should hold for signals but
        // might need to be relaxed for components as the component variables are written to when
        // the component is
        match (self, other) {
            (Self::Var(v1), Self::Var(v2)) => { v1.may_alias(v2) }
            (Self::Sig(v1), Self::Sig(v2)) => { v1.may_alias(v2) }
            (Self::Comp(v1), Self::Comp(v2)) => { v1.may_alias(v2) }
            (_, _) => { false }
        }
    }

    pub fn new_sig_ref(name: String, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Self {
        Self::Sig(SignalRef::new(name, access, ref_witness, ref_constraint))
    }

    pub fn new_var_ref(name: String, access: AccessList<Access>, version: usize, ref_witness: bool, ref_constraint: bool) -> Self {
        Self::Var(VarRef::new(name, access, version, ref_witness, ref_constraint))
    }

    pub fn build_comp_ref(template_params: &HashMap<String, Vec<String>>, name: String, access: AccessList<Access>, invoked: String, var_versions: &mut HashMap<String, usize>, next_version: &mut HashMap<String, usize>) -> Result<Self, CFGError> {
        let param_names = template_params.get(&invoked).ok_or(CFGError::TemplateNotFound(invoked.clone()))?;
        let mut params: Vec<VarRef> = vec![];
        for v_name in param_names {
            let mut var_access = access.clone();
            var_access.push(Access::Component { name: v_name.clone() })?;
            // components are immutable
            params.push(VarRef::new(name.clone(), var_access, 0, true, true))
        }

        Ok(Self::new_comp_ref(name, access, invoked, params))
    }

    pub fn new_comp_ref(name: String, access: AccessList<Access>, invoked: String, params: Vec<VarRef>) -> Self {
        Self::Comp(ComponentRef::new(name, access, invoked, params))
    }

    pub fn identifier(name: &String, access: &AccessList<Access>) -> String {
        let component_access = access.get_component_access();
        match component_access {
            None => { name.clone() }
            Some(field) => { format!("{}.{}", name, field) }
        }
    }

    pub fn from_ast(type_inference: &TypeInference, vars_and_signals: &HashMap<String, (usize, NamedStorage)>, template_params: &HashMap<String, Vec<String>>, parent: &String, var_versions: &HashMap<String, usize>, name: String, access: &Vec<ast::Access>, allow_components: bool) -> Result<Self, CFGError> {
        let (_, store) = vars_and_signals.get(&name).ok_or(CFGError::VariableNotFound(parent.clone(), name.clone()))?;
        let c_access: Vec<String> = access.iter()
            .map(|a| if let ast::Access::ComponentAccess(n) = a { n.clone() } else { String::default() })
            .filter(|s| !s.is_empty())
            .collect();

        match store {
            NamedStorage::Variable(_) => {
                if c_access.len() == 0 {
                    //Can't use .c and .w with variables
                    let access_list = AccessList::<Access>::from_ast(type_inference, vars_and_signals, template_params, parent, access, var_versions)?;
                    let identifier = Ref::identifier(&name, &access_list);
                    let version = *var_versions.get(&identifier).ok_or(CFGError::VariableNotFound(parent.clone(), name.clone()))?;
                    Ok(Self::new_var_ref(name, access_list, version, true, true))
                } else if c_access.len() == 1 {
                    let a_access = access.iter().filter(|a| if let ast::Access::ArrayAccess(_) = a { true } else { false }).map(|a| a.clone()).collect();
                    let access_list = AccessList::<Access>::from_ast(type_inference, vars_and_signals, template_params, parent, &a_access, var_versions)?;
                    let identifier = Ref::identifier(&name, &access_list);
                    let version = *var_versions.get(&identifier).ok_or(CFGError::VariableNotFound(parent.clone(), name.clone()))?;
                    if c_access[0] == "c" {
                        Ok(Self::new_var_ref(name, access_list, version, false, true))
                    } else if c_access[0] == "w" {
                        Ok(Self::new_var_ref(name, access_list, version, true, false))
                    } else {
                        Err(CFGError::InvalidComponentAccess(name))
                    }
                }
                else {
                    Err(CFGError::InvalidComponentAccess(name))
                }
            }
            NamedStorage::Signal(_) => {
                if c_access.len() == 0 {
                    let access_list = AccessList::<Access>::from_ast(type_inference, vars_and_signals, template_params, parent, access, var_versions)?;
                    Ok(Self::new_sig_ref(name, access_list, true, true))
                } else if c_access.len() == 1 {
                    let a_access = access.iter().filter(|a| if let ast::Access::ArrayAccess(_) = a { true } else { false }).map(|a| a.clone()).collect();
                    let access_list = AccessList::<Access>::from_ast(type_inference, vars_and_signals, template_params, parent, &a_access, var_versions)?;
                    if c_access[0] == "c" {
                        Ok(Self::new_sig_ref(name, access_list, false, true))
                    } else if c_access[0] == "w" {
                        Ok(Self::new_sig_ref(name, access_list, true, false))
                    } else {
                        Err(CFGError::InvalidComponentAccess(name))
                    }
                } else {
                    Err(CFGError::InvalidComponentAccess(name))
                }
            }
            NamedStorage::Component(c) => {
                if c_access.is_empty() {
                    if allow_components {
                        assert_eq!(c.dims().len(), access.len(), "A component reference must fully index a component array");
                        let invoked = String::from(c.instance_of());
                        let access_list = AccessList::<Access>::from_ast(type_inference, vars_and_signals, template_params, parent, access, var_versions)?;
                        let param_names = template_params.get(&invoked).ok_or(CFGError::TemplateNotFound(invoked.clone()))?;
                        let mut params: Vec<VarRef> = vec![];
                        for v_name in param_names {
                            let mut var_access = access_list.clone();
                            var_access.push(Access::Component { name: v_name.clone() })?;
                            let id = Ref::identifier(&name, &var_access);
                            let cur_version = *var_versions.get(&id).unwrap_or(&0);
                            params.push(VarRef::new(name.clone(), var_access, cur_version, true, true))
                        }

                        Ok(Self::new_comp_ref(name, access_list, invoked, params))
                    }
                    else {
                        Err(CFGError::MissingComponentAccess(name))
                    }
                } else if c_access.len() == 1 || c_access.len() == 2 {
                    let template = c.instance_of();
                    let params = template_params.get(template).ok_or(CFGError::TemplateNotFound(String::from(template)))?;
                    if params.contains(&c_access[0]) {
                        if c_access.len() == 2 {
                            Err(CFGError::InvalidComponentAccess(name))
                        } else {
                            let access_list = AccessList::<Access>::from_ast(type_inference, vars_and_signals, template_params, parent, access, var_versions)?;
                            let identifier = Ref::identifier(&name, &access_list);
                            let version = *var_versions.get(&identifier).ok_or(CFGError::VariableNotFound(parent.clone(), name.clone()))?;
                            Ok(Self::new_var_ref(name, access_list, version, true, true))
                        }
                    } else {
                        if c_access.len() == 2 {
                            if c_access[1] == "c" {
                                let remove_pos = access.iter().rposition(|a| if let ast::Access::ComponentAccess(_) = a { true } else { false }).unwrap();
                                let mut a_access = access.clone();
                                a_access.remove(remove_pos);
                                let access_list = AccessList::<Access>::from_ast(type_inference, vars_and_signals, template_params, parent, &a_access, var_versions)?;
                                Ok(Self::new_sig_ref(name, access_list, false, true))
                            } else if c_access[1] == "w" {
                                let remove_pos = access.iter().rposition(|a| if let ast::Access::ComponentAccess(_) = a { true } else { false }).unwrap();
                                let mut a_access = access.clone();
                                a_access.remove(remove_pos);
                                let access_list = AccessList::<Access>::from_ast(type_inference, vars_and_signals, template_params, parent, &a_access, var_versions)?;
                                Ok(Self::new_sig_ref(name, access_list, true, false))
                            } else {
                                Err(CFGError::InvalidComponentAccess(name))
                            }
                        } else {
                            let access_list = AccessList::<Access>::from_ast(type_inference, vars_and_signals, template_params, parent, access, var_versions)?;
                            Ok(Self::new_sig_ref(name, access_list, true, true))
                        }
                    }
                } else {
                    Err(CFGError::InvalidComponentAccess(name))
                }
            }
        }
    }

    pub fn create_var_ref(versions: &HashMap<String, usize>, parent: &String, var: &Var, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        if let Some(version) = versions.get(var.name()) {
            Ok(Self::new_var_ref(var.name().into(), access, *version, ref_witness, ref_constraint))
        } else {
            Err(CFGError::VariableNotFound(parent.clone(), var.name().into()))
        }
    }

    pub fn create_sig_ref(sig: &Signal, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        Ok(Self::new_sig_ref(sig.name().into(), access, ref_witness, ref_constraint))
    }

    pub fn create_component_ref(cfg: &CFG, parent: &String, versions: &HashMap<String, usize>, component: &Component, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        let ref_template = cfg.get_template(&String::from(component.instance_of()))?;

        if let Some(name) = access.get_component_access() {
            let store = ref_template.vars_and_signals.get(name).ok_or(CFGError::VariableNotFound(parent.clone(), Self::identifier(&String::from(component.name()), &access)))?;
            match store {
                NamedStorage::Variable(v) => {
                    if v.is_input() {
                        let id = Ref::identifier(&String::from(component.name()), &access);
                        if let Some(version) = versions.get(&id) {
                            Ok(Self::new_var_ref(component.name().into(), access, *version, ref_witness, ref_constraint))
                        } else {
                            // We might not have a version of this if accessing a component due to the type inference. However,
                            // components are immutable so use the somewhat hacky way of resolving this by just assuming the
                            // version is 0
                            Ok(Self::new_var_ref(component.name().into(), access, 0, ref_witness, ref_constraint))
                        }
                    } else {
                        Err(CFGError::VariableNotFound(parent.clone(), Self::identifier(&String::from(component.name()), &access)))
                    }
                }
                NamedStorage::Signal(s) => {
                    if s.is_input() || s.is_output() {
                        Ok(Self::new_sig_ref(String::from(component.name()), access, ref_witness, ref_constraint))
                    } else {
                        Err(CFGError::VariableNotFound(parent.clone(), Self::identifier(&String::from(component.name()), &access)))
                    }
                }
                _ => { Err(CFGError::VariableNotFound(parent.clone(), Self::identifier(&String::from(component.name()), &access))) }
            }
        } else {
            let mut params = vec![];
            for var in &ref_template.input_vars {
                let var_access = AccessList::new(vec![Access::Component { name: var.name().into() }])?;
                let id = Ref::identifier(&String::from(component.name()), &var_access);
                if let Some(version) = versions.get(&id) {
                    let var_ref = VarRef::new(component.name().into(), var_access, *version, ref_witness, ref_constraint);
                    params.push(var_ref);
                } else {
                    return Err(CFGError::VariableNotFound(parent.clone(), id))
                }
            }
            Ok(Self::new_comp_ref(component.name().into(), AccessList::empty(), component.instance_of().into(), params))
        }
    }

    pub fn change_access(&mut self, access: AccessList<Access>) {
        match self {
            Ref::Var(v) => { v.change_access(access); }
            Ref::Sig(s) => { s.change_access(access); }
            Ref::Comp(c) => { c.change_access(access); }
        }
    }

    pub fn change_ref_witness(&mut self, val: bool) {
        match self {
            Ref::Var(v) => {
                v.ref_witness = val;
            }
            Ref::Sig(s) => {
                s.ref_witness = val;
            }
            Ref::Comp(_) => {}
        }
    }

    pub fn change_ref_constraint(&mut self, val: bool) {
        match self {
            Ref::Var(v) => {
                v.ref_constraint = val;
            }
            Ref::Sig(s) => {
                s.ref_constraint = val;
            }
            Ref::Comp(_) => {}
        }
    }

    pub fn create_ref(cfg: &CFG, parent: &String, versions: &HashMap<String, usize>, store: &NamedStorage, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        match store {
            NamedStorage::Variable(v) => { Self::create_var_ref(versions, parent, v, access, ref_witness, ref_constraint) }
            NamedStorage::Signal(s) => { Self::create_sig_ref(s, access, ref_witness, ref_constraint) }
            NamedStorage::Component(c) => { Self::create_component_ref(cfg, parent, versions, c, access, ref_witness, ref_constraint) }
        }
    }

    pub fn get_dimensions(&self, cfg: &CFG, template: &Template) -> Result<(Option<Vec<Expression>>, Vec<Expression>), CFGError> {
        let (maybe_component, store) = template.get_referenced(cfg, self)?;
        match maybe_component {
            Some(component) => {
                //If a component is present, it must have been accessed
                let component_ind = self.access().get_component_access_ind().ok_or(CFGError::InvalidComponentAccess(store.name().into()))?;
                let mut component_var_renaming = HashMap::new();
                let to_template = cfg.get_template(&component.instance_of().into())?;
                let component_access = self.access().slice(0, component_ind);
                for input_var in &to_template.input_vars {
                    let to_var = to_template.pre_ref_var(input_var, AccessList::empty(), true, true)?;
                    let mut component_var_access = component_access.clone();
                    component_var_access.push(Access::new_component_access(input_var.name().into()))?;
                    let component_var = template.post_ref_component(cfg, component, component_var_access, true, true)?;
                    component_var_renaming.insert(to_var, component_var);
                }

                let mut store_dims = vec![];
                for dim in store.dims() {
                    store_dims.push(dim.rename_all(&component_var_renaming)?);
                }

                Ok((Some(component.dims().clone()), store_dims))
            }
            None => {
                Ok((None, store.dims().clone()))
            }
        }
    }

    pub fn create_equality_constraint(&self, cfg: &CFG, template: &Template, at_blk: &Block, is_before_block: bool) -> Result<Vec<InvariantExpr>, CFGError> {
        match self {
            Ref::Var(v) => {
                v.create_equality_constraint(cfg, template, at_blk, is_before_block)
            }
            Ref::Sig(s) => {
                s.create_equality_constraint(cfg, template, at_blk, is_before_block)
            }
            Ref::Comp(c) => {
                c.create_equality_constraint(cfg, template, at_blk, is_before_block)
            }
        }
    }

    pub fn get_nonempty_array_assumption(&self, cfg: &CFG, template: &Template) -> Result<Expression, CFGError> {
        let (component_dims_opt, ref_dims) = self.get_dimensions(cfg, template)?;

        let zero_expr = Expression::new_literal(Literal::new_number(BigInt::zero()));
        let mut nonzero_constraints = vec![];
        if let Some(component_dims) = component_dims_opt {
            for dim in component_dims {
                let nonzero_check = Expression::new_binop(Box::new(dim), BinaryOperator::Gt, Box::new(zero_expr.clone()));
                nonzero_constraints.push(nonzero_check);
            }
        }

        for dim in ref_dims {
            let nonzero_check = Expression::new_binop(Box::new(dim), BinaryOperator::Gt, Box::new(zero_expr.clone()));
            nonzero_constraints.push(nonzero_check);
        }

        Ok(Expression::and_all(nonzero_constraints))
    }

    pub fn create_any_equality_constraint(&self, cfg: &CFG, template: &Template, at_blk: &Block, is_before_block: bool) -> Result<Vec<InvariantExpr>, CFGError> {
        match self {
            Ref::Var(v) => {
                v.create_any_equality_constraint(cfg, template, at_blk, is_before_block)
            }
            Ref::Sig(s) => {
                s.create_any_equality_constraint(cfg, template, at_blk, is_before_block)
            }
            Ref::Comp(c) => {
                c.create_any_equality_constraint(cfg, template, at_blk, is_before_block)
            }
        }
    }
}