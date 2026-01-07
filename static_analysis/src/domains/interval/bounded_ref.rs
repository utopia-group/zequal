use std::cmp::min;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use itertools::{equal, Itertools};
use num_bigint_dig::BigInt;
use num_traits::{One, Zero};
use cfg::cfg::CFG;
use cfg::error::CFGError;
use cfg::expr::binop::BinaryOperator;
use cfg::expr::expression::{Expr, Expression};
use cfg::expr::invariant::InvariantExpr;
use cfg::expr::literal::Literal;
use cfg::expr::unop::UnaryOperator;
use cfg::expr::var_access::{Access, AccessList, StorageAccess};
use cfg::expr::variable_ref::Ref;
use cfg::finite_fields::FiniteFieldDef;
use cfg::template::Template;
use crate::analysis::DomainValue;
use crate::domains::interval::infinite_number::infinite_number::InfiniteNumber;
use crate::domains::interval::infinite_number::symbolic_infinite_bigint::SymbolicInfiniteBigInt;
use crate::domains::interval::interval_value::{IntervalValue, SymbolicInterval};

pub type SymbolicBoundedRef<FF: FiniteFieldDef> = BoundedRef<SymbolicInfiniteBigInt<FF>>;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct BoundedArrayAccess<N: InfiniteNumber> {
    bounds: IntervalValue<N>,
    dim_size: Expression,
    access_expr: Expression
}

impl<N: InfiniteNumber> BoundedArrayAccess<N> {
    pub fn new(access_expr: Expression, bounds: IntervalValue<N>, dim_size: Expression) -> Self {
        Self { bounds, dim_size, access_expr }
    }

    pub fn get_bounds(&self) -> &IntervalValue<N> {
        &self.bounds
    }

    pub fn get_dim_size(&self) -> &Expression {
        &self.dim_size
    }

    pub fn get_access_expr(&self) -> &Expression {
        &self.access_expr
    }

    pub fn lower_bound(&self) -> Expression {
        let zero_expr = Expression::new_number(BigInt::zero());
        self.bounds.lower().to_expr_or_default(&zero_expr)
    }

    pub fn upper_bound(&self) -> Expression {
        self.bounds.upper().to_expr_or_default(&self.dim_size)
    }

    pub fn get_ind_bounds(&self, quantifier_id: usize) -> (Option<Ref>, Option<Expression>, Expression) {
        let lower = self.bounds.lower();
        let upper = self.bounds.upper();
        if lower.maybe_eq(upper).is_true() && !lower.is_infinity() && !lower.is_neg_infinity() {
            (None, None, self.lower_bound())
        }
        else {
            let lower_expr = self.lower_bound();
            let upper_expr = self.upper_bound();

            let quantifier = format!("ai{}", quantifier_id);
            let quant_ref = Ref::new_var_ref(quantifier.clone(), AccessList::empty(), 0, true, true);
            let quant_expr = Expression::new_variable(quant_ref.clone());

            let lower_bound = Expression::new_binop(Box::new(quant_expr.clone()), BinaryOperator::Gte, Box::new(lower_expr));
            let upper_bound = Expression::new_binop(Box::new(quant_expr.clone()), BinaryOperator::Lte, Box::new(upper_expr));
            let bounds = Expression::new_binop(Box::new(lower_bound), BinaryOperator::And, Box::new(upper_bound));
            (Some(quant_ref), Some(bounds), quant_expr)
        }
    }
}

impl<N: InfiniteNumber> Display for BoundedArrayAccess<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.bounds)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct BoundedUnknownArrayAccess<N: InfiniteNumber> {
    bounds: IntervalValue<N>,
    dim_size: Expression,
    // Note, we use this to add additional constraints about an index access if possible (i.e. dim_size > n)
    access_bounds: IntervalValue<N>
}

impl<N: InfiniteNumber> BoundedUnknownArrayAccess<N> {
    pub fn new(dim_size: Expression) -> Self {
        Self { bounds: IntervalValue::top(), dim_size, access_bounds: IntervalValue::top() }
    }

    pub fn get_bounds(&self) -> &IntervalValue<N> {
        &self.bounds
    }

    pub fn get_dim_size(&self) -> &Expression {
        &self.dim_size
    }

    pub fn lower_bound(&self) -> Expression {
        Expression::new_number(BigInt::zero())
    }

    pub fn upper_bound(&self) -> Expression {
        //our upper bounds are inclusive, so subtract 1
        Expression::new_binop(Box::new(self.dim_size.clone()), BinaryOperator::Sub, Box::new(Expression::new_number(BigInt::one())))
    }

    pub fn constrain_with(&self, with: &BoundedArrayAccess<N>) -> Self {
        let with_bounds = with.get_bounds().clone();
        Self { bounds: self.bounds.clone(), dim_size: self.dim_size.clone(), access_bounds: with_bounds }
    }

    pub fn get_ind_bounds(&self, quantifier_id: usize) -> (Ref, Expression, Expression) {
        let mut lower_expr = self.lower_bound();
        let mut upper_expr = self.upper_bound();

        // access is more constrained than write, so use that instead if we don't know
        let access_lower_bound_res = self.access_bounds.lower().to_expr();
        if let Ok(access_lower_bound) = access_lower_bound_res {
            lower_expr = access_lower_bound;
        }

        let access_upper_bound_res = self.access_bounds.upper().to_expr();
        if let Ok(access_upper_bound) = access_upper_bound_res {
            upper_expr = access_upper_bound;
        }

        let quantifier = format!("ai{}", quantifier_id);
        let quant_ref = Ref::new_var_ref(quantifier.clone(), AccessList::empty(), 0, true, true);
        let quant_expr = Expression::new_variable(quant_ref.clone());

        let lower_bound = Expression::new_binop(Box::new(quant_expr.clone()), BinaryOperator::Gte, Box::new(lower_expr.clone()));
        let upper_bound = Expression::new_binop(Box::new(quant_expr.clone()), BinaryOperator::Lte, Box::new(upper_expr.clone()));
        let mut bounds = Expression::new_binop(Box::new(lower_bound), BinaryOperator::And, Box::new(upper_bound));

        (quant_ref, bounds, quant_expr)
    }
}

impl<N: InfiniteNumber> Display for BoundedUnknownArrayAccess<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[*]")
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum BoundedAccess<N: InfiniteNumber> {
    Array { ind: BoundedArrayAccess<N> },
    Component { name: String },
    UnknownAccess { ind: BoundedUnknownArrayAccess<N> }
}

impl<N: InfiniteNumber> Display for BoundedAccess<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BoundedAccess::Array { ind } => { write!(f, "{}", ind) }
            BoundedAccess::Component { name } => { write!(f, ".{}", name) }
            BoundedAccess::UnknownAccess { ind } => { write!(f, "{}", ind) }
        }
    }
}

impl<N: InfiniteNumber> Into<Option<Access>> for &BoundedAccess<N> {
    fn into(self) -> Option<Access> {
        match self {
            BoundedAccess::Array { ind, .. } => { Some(Access::new_array_access( ind.access_expr.clone() )) }
            BoundedAccess::Component { name, .. } => { Some(Access::new_component_access(name.clone())) }
            BoundedAccess::UnknownAccess { .. } => { None }
        }
    }
}

impl<N: InfiniteNumber> Into<Option<Access>> for BoundedAccess<N> {
    fn into(self) -> Option<Access> {
        match self {
            BoundedAccess::Array { ind, .. } => { Some(Access::new_array_access( ind.access_expr )) }
            BoundedAccess::Component { name, .. } => { Some(Access::new_component_access(name)) }
            BoundedAccess::UnknownAccess { .. } => { None }
        }
    }
}

impl<N: InfiniteNumber> StorageAccess for BoundedAccess<N> {
    fn is_array_access(&self) -> bool {
        match self {
            BoundedAccess::Array { .. } => { true }
            BoundedAccess::Component { .. } => { false }
            BoundedAccess::UnknownAccess { .. } => { true }
        }
    }

    fn is_component_access(&self) -> bool {
        match self {
            BoundedAccess::Array { .. } => { false }
            BoundedAccess::Component { .. } => { true }
            BoundedAccess::UnknownAccess { .. } => { false }
        }
    }

    fn get_array_access(&self) -> Option<&Expression> {
        match self {
            BoundedAccess::Array { ind, .. } => { Some(&ind.access_expr) }
            BoundedAccess::Component { .. } => { None }
            BoundedAccess::UnknownAccess { .. } => { None }
        }
    }

    fn get_component_access(&self) -> Option<&String> {
        match self {
            BoundedAccess::Array { .. } => { None }
            BoundedAccess::Component { name } => { Some(name) }
            BoundedAccess::UnknownAccess { .. } => { None }
        }
    }

    /*
     * Note: we assume that the renaming will not affect the given bounds
     */
    fn rename(&self, from: &Ref, to: &Ref) -> Result<Self, CFGError> {
        match self {
            BoundedAccess::Array { ind } => {
                Ok(Self::Array { ind: BoundedArrayAccess::new(ind.access_expr.rename(from, to)?, ind.bounds.clone(), ind.dim_size.clone()) })
            }
            BoundedAccess::Component { name } => {
                Ok(self.clone())
            }
            BoundedAccess::UnknownAccess { .. } => {
                Ok(self.clone())
            }
        }
    }

    fn variable_refs(&self) -> HashSet<&Ref> {
        match self {
            BoundedAccess::Array { ind } => {
                ind.access_expr.variable_refs()
            }
            BoundedAccess::Component { name } => {
                HashSet::new()
            }
            BoundedAccess::UnknownAccess { ind } => {
                HashSet::new()
            }
        }
    }
}

impl<N: InfiniteNumber> BoundedAccess<N> {
    pub fn is_unknown_array_access(&self) -> bool {
        match self {
            BoundedAccess::Array { .. } => { false }
            BoundedAccess::Component { .. } => { false }
            BoundedAccess::UnknownAccess { .. } => { true }
        }
    }

    pub fn is_explicit_array_access(&self) -> bool {
        match self {
            BoundedAccess::Array { .. } => { true }
            BoundedAccess::Component { .. } => { false }
            BoundedAccess::UnknownAccess { .. } => { false }
        }
    }

    pub fn constrain_with(&self, other: &Self) -> BoundedAccess<N> {
        match (self, other) {
            (BoundedAccess::Array { .. }, BoundedAccess::Array { .. }) => {
                self.clone()
            }
            (BoundedAccess::Array { .. }, BoundedAccess::UnknownAccess { .. }) => {
                self.clone()
            }
            (BoundedAccess::Component { .. }, BoundedAccess::Component { .. }) => {
                self.clone()
            }
            (BoundedAccess::UnknownAccess { ind: ind1 }, BoundedAccess::Array { ind: ind2 }) => {
                Self::UnknownAccess {ind: ind1.constrain_with(ind2) }
            }
            (BoundedAccess::UnknownAccess { .. }, BoundedAccess::UnknownAccess { .. }) => {
                self.clone()
            }
            (_, _) => { unreachable!("Cannot constrain input access types") }
        }
    }
}

#[derive(Clone, Eq, PartialEq)]
pub struct BoundedRef<N: InfiniteNumber> {
    orig_ref: Ref,
    access: AccessList<BoundedAccess<N>>
}

impl<N: InfiniteNumber> Hash for BoundedRef<N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.orig_ref.hash(state)
    }
}

impl<N: InfiniteNumber> Display for BoundedRef<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let component_ind = self.orig_ref.access().get_component_access_ind();
        write!(f, "{}{}", self.name(), self.access)
    }
}

impl<N: InfiniteNumber> BoundedRef<N> {
    pub fn rename(&self, from: &Ref, to: &Ref) -> Result<Self, CFGError> {
        Ok(Self { orig_ref: self.orig_ref.rename(from, to)?, access: self.access.rename(from, to)? })
    }

    pub fn rename_all(&self, renamings: &HashMap<Ref, Ref>) -> Result<Self, CFGError> {
        Ok(Self { orig_ref: self.orig_ref.rename_all(renamings)?, access: self.access.rename_all(renamings)? })
    }

    pub fn new(cfg: &CFG, template: &Template, r: Ref, mut access_bounds: VecDeque<IntervalValue<N>>) -> Result<Self, CFGError> {
        let (component_dims, store_dims) = r.get_dimensions(cfg, template)?;
        let mut all_dims = VecDeque::new();
        all_dims.extend(component_dims.clone().unwrap_or(vec![]));
        all_dims.extend(store_dims);

        let mut access = AccessList::empty();
        for (i, a) in r.access().iter().enumerate() {
            match a {
                Access::Array { ind } => {
                    let bounded_access = BoundedArrayAccess::new(ind.clone(), access_bounds.pop_front().unwrap(), all_dims.pop_front().unwrap());
                    access.push(BoundedAccess::Array { ind: bounded_access })?;
                }
                Access::Component { name } => {
                    if let Some(dims) = &component_dims {
                        for _ in i..dims.len() {
                            let unknown_access = BoundedUnknownArrayAccess::new(all_dims.pop_front().unwrap());
                            access.push(BoundedAccess::UnknownAccess { ind: unknown_access })?;
                        }
                    }
                    access.push(BoundedAccess::Component { name: name.clone() })?;
                }
            }
        }

        for remaining_dim in all_dims {
            let unknown_access = BoundedUnknownArrayAccess::new(remaining_dim);
            access.push(BoundedAccess::UnknownAccess { ind: unknown_access })?;
        }

        Ok(Self { orig_ref: r, access })
    }

    pub fn name(&self) -> &str {
        self.orig_ref.name()
    }

    pub fn id(&self) -> &String {
        self.orig_ref.id()
    }

    pub fn access(&self) -> &AccessList<BoundedAccess<N>> {
        &self.access
    }

    pub fn get_ref(&self) -> &Ref {
        &self.orig_ref
    }

    pub fn overwrite_version(&mut self, new_version: usize) {
        match &mut self.orig_ref {
            Ref::Var(v) => {
                v.change_version(new_version)
            }
            Ref::Sig(_) => {}
            Ref::Comp(_) => {}
        }
    }

    pub fn is_var_ref(&self) -> bool {
        match self.orig_ref {
            Ref::Var(_) => { true }
            _ => { false }
        }
    }

    pub fn is_sig_ref(&self) -> bool {
        match self.orig_ref {
            Ref::Sig(_) => { true }
            _ => { false }
        }
    }

    pub fn is_component_ref(&self) -> bool {
        match self.orig_ref {
            Ref::Comp(_) => { true }
            _ => { false }
        }
    }

    pub fn constrain_with(&self, other: &Self) -> Result<Self, CFGError> {
        if !self.orig_ref.may_alias(&other.orig_ref) || self.access.len() != other.access.len() {
            Ok(self.clone())
        }
        else {
            let mut new_access = AccessList::empty();
            for i in 0..self.access.len() {
                new_access.push(self.access.get(i).constrain_with(other.access.get(i)))?;
            }

            Ok(Self { orig_ref: self.orig_ref.clone(), access: new_access })
        }
    }

    pub fn may_alias(&self, other: &Self) -> bool {
        if self.orig_ref.may_alias(&other.orig_ref) {
            let self_access = self.access.list();
            let other_access = other.access.list();
            for i in 0..min(self_access.len(), other_access.len()) {
                match (&self_access[i], &other_access[i]) {
                    (BoundedAccess::Array { ind: ind1, .. }, BoundedAccess::Array { ind: ind2, .. }) => {
                        if ind1.bounds.meet(&ind2.bounds).is_bottom() {
                            return false;
                        }
                    }
                    (BoundedAccess::Component { name: n1 }, BoundedAccess::Component { name: n2 }) => {
                        if n1 != n2 {
                            return false;
                        }
                    }
                    (BoundedAccess::Array { .. }, BoundedAccess::UnknownAccess { .. }) => { /* Unknown matches everything */ }
                    (BoundedAccess::UnknownAccess { .. }, BoundedAccess::Array { .. }) => { /* Unknown matches everything */ }
                    (BoundedAccess::UnknownAccess { .. }, BoundedAccess::UnknownAccess { .. }) => { /* Unknown matches everything */ }
                    (_, _) => {
                        return false;
                    }
                }
            }

            true
        }
        else {
            false
        }
    }

    /*
       Note, we may want to pass loop indices in here and only quantify those accesses that use them.
       For now I'm not going to do that and opt to quantify any index accessed by a range
    */
    pub fn create_equality_constraint(&self) -> Result<InvariantExpr, CFGError> {
        match &self.orig_ref {
            Ref::Sig(sig_ref) => {
                let mut equality_access = AccessList::empty();
                let mut quantifier_bounds = vec![];
                let mut quantifiers = vec![];

                for (access_ind, access) in self.access.iter().enumerate() {
                    match access {
                        BoundedAccess::Array { ind } => {
                            let (quantifier_opt, guard_opt, ind_access) = ind.get_ind_bounds(access_ind);
                            if let Some(quantifier) = quantifier_opt {
                                quantifiers.push(quantifier.name().into())
                            }
                            if let Some(guard) = guard_opt {
                                quantifier_bounds.push(guard);
                            }
                            equality_access.push(Access::new_array_access(ind_access))?;
                        }
                        BoundedAccess::Component { name } => {
                            equality_access.push(Access::new_component_access(name.clone()))?;
                        }
                        BoundedAccess::UnknownAccess { ind } => {
                            let (quantifier, guard, ind_access) = ind.get_ind_bounds(access_ind);
                            quantifiers.push(quantifier.name().into());
                            quantifier_bounds.push(guard);
                            equality_access.push(Access::new_array_access(ind_access))?;
                        }
                    }
                }

                let new_sig_w = Ref::new_sig_ref(sig_ref.name().into(), equality_access.clone(), true, false);
                let new_sig_expr_w = Expression::new_variable(new_sig_w);
                let new_sig_c = Ref::new_sig_ref(sig_ref.name().into(), equality_access, false, true);
                let new_sig_expr_c = Expression::new_variable(new_sig_c);
                let eq = Expression::new_binop(Box::new(new_sig_expr_w), BinaryOperator::Eq, Box::new(new_sig_expr_c));

                let unquantified_eq = if quantifier_bounds.is_empty() {
                    eq.into()
                }
                else {
                    let bounds = Expression::and_all(quantifier_bounds);
                    let not_bounds = Expression::new_unop(UnaryOperator::Not, Box::new(bounds));
                    Expression::new_binop(Box::new(not_bounds), BinaryOperator::Or, Box::new(eq)).into()
                };

                if quantifiers.is_empty() {
                    Ok(unquantified_eq)
                }
                else {
                    Ok(unquantified_eq.forall(quantifiers))
                }
            }
            Ref::Var(var_ref) => {
                let mut equality_access = AccessList::empty();
                let mut quantifier_bounds = vec![];
                let mut quantifiers = vec![];

                for (access_ind, access) in self.access.iter().enumerate() {
                    match access {
                        BoundedAccess::Array { ind } => {
                            let (quantifier_opt, guard_opt, ind_access) = ind.get_ind_bounds(access_ind);
                            if let Some(quantifier) = quantifier_opt {
                                quantifiers.push(quantifier.name().into())
                            }
                            if let Some(guard) = guard_opt {
                                quantifier_bounds.push(guard);
                            }
                            equality_access.push(Access::new_array_access(ind_access))?;
                        }
                        BoundedAccess::Component { name } => {
                            equality_access.push(Access::new_component_access(name.clone()))?;
                        }
                        BoundedAccess::UnknownAccess { ind } => {
                            let (quantifier, guard, ind_access) = ind.get_ind_bounds(access_ind);
                            quantifiers.push(quantifier.name().into());
                            quantifier_bounds.push(guard);
                            equality_access.push(Access::new_array_access(ind_access))?;
                        }
                    }
                }

                let new_var_w = Ref::new_var_ref(var_ref.name().into(), equality_access.clone(), var_ref.version(), true, false);
                let new_var_expr_w = Expression::new_variable(new_var_w);
                let new_var_c = Ref::new_var_ref(var_ref.name().into(), equality_access, var_ref.version(), false, true);
                let new_var_expr_c = Expression::new_variable(new_var_c);
                let eq = Expression::new_binop(Box::new(new_var_expr_w), BinaryOperator::Eq, Box::new(new_var_expr_c));

                let unquantified_eq = if quantifier_bounds.is_empty() {
                    eq.into()
                }
                else {
                    let bounds = Expression::and_all(quantifier_bounds);
                    let not_bounds = Expression::new_unop(UnaryOperator::Not, Box::new(bounds));
                    Expression::new_binop(Box::new(not_bounds), BinaryOperator::Or, Box::new(eq)).into()
                };

                if quantifiers.is_empty() {
                    Ok(unquantified_eq)
                }
                else {
                    Ok(unquantified_eq.forall(quantifiers))
                }
            }
            _ => {
                // Return true for variables and components as variables are equiv by definition
                // and component-only accesses only refer to the variable parts
                Ok(Expression::new_literal(Literal::new_boolean(true)).into())
            }
        }
    }
}