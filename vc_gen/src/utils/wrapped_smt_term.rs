use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use num_bigint_dig::BigInt;
use smtlib_lowlevel::ast::{Identifier, QualIdentifier, Sort, SpecConstant, Term};
use crate::smt::array::ArrayTerm;
use crate::smt::bool::BoolTerm;
use crate::smt::finite_field::finite_field::{FiniteFieldOp, FiniteFieldTypedTerm, TermSize};
use crate::smt::smt::{BuildableTerm, CoreTerm, NumericTerm, StaticTypedTerm, TermSort, TypedTerm, SmtUtils, NumericOp, Quantifier, UninterpretedFunction};
use std::str::FromStr;
use std::iter::Extend;
use std::ops::Deref;
use std::sync::atomic::{AtomicUsize, Ordering};
use num_traits::{One, Zero};
use cfg::finite_fields::FiniteFieldDef;
use crate::smt::error::SmtError;
use crate::smt::error::SmtError::MismatchedSort;
use crate::smt::finite_field::ff_impl::FiniteFieldTerm;
use crate::smt::finite_field::int_impl::IntFiniteFieldTerm;
use crate::smt::int::IntTerm;
use crate::smt::smt::TermSort::FiniteField;
use crate::smt::uninterpreted_fn::UniformUFTerm;

static COUNTER: AtomicUsize = AtomicUsize::new(1);
fn get_unique_id() -> usize { COUNTER.fetch_add(1, Ordering::Relaxed) }

pub trait VCTerm: TypedTerm + for<'a> From<&'a BigInt> + From<bool> + Display + PartialEq + Eq + Hash {
    fn get_prime() -> BigInt;
    fn variable_sort() -> TermSort;
    fn signal_sort() -> TermSort;
    fn is_array(&self) -> bool;
    fn is_variable(&self) -> bool;
    fn is_signal(&self) -> bool;
    fn is_bool(&self) -> bool;
    fn is_quantified(&self) -> bool;
    fn get_quantifier(&self) -> Result<Quantifier, SmtError>;
    fn get_quantified_vars(&self) -> Result<Vec<String>, SmtError>;
    fn get_quantified_term(&self) -> Result<Self, SmtError>;
    fn create_fn_application(ref_fn: &UninterpretedFunction, args: Vec<Self>) -> Result<Self, SmtError>;
    fn add(self, other: Self) -> Result<Self, SmtError>;
    fn and_all(conjuncts: Vec<Self>) -> Result<Self, SmtError>;
    fn sub(self, other: Self) -> Result<Self, SmtError>;
    fn mul(self, other: Self) -> Result<Self, SmtError>;
    fn div(self, other: Self) -> Result<Self, SmtError>;
    fn pow(self, other: Self) -> Result<Self, SmtError>;
    fn modulus(self, other: Self) -> Result<Self, SmtError>;
    fn negate(self) -> Result<Self, SmtError>;
    fn inverse(self) -> Result<Self, SmtError>;
    fn mul_by_inverse(self, other: Self) -> Result<Self, SmtError>;
    fn gt(self, other: Self) -> Result<Self, SmtError>;
    fn gte(self, other: Self) -> Result<Self, SmtError>;
    fn lt(self, other: Self) -> Result<Self, SmtError>;
    fn lte(self, other: Self) -> Result<Self, SmtError>;
    fn select(self, index: Self) -> Result<Self, SmtError>;
    fn store(self, index: Self, value: Self) -> Result<Self, SmtError>;
    fn and(self, other: Self) -> Result<Self, SmtError>;
    fn or(self, other: Self) -> Result<Self, SmtError>;
    fn or_all(disjuncts: Vec<Self>) -> Result<Self, SmtError>;
    fn bit_and(self, other: Self) -> Result<Self, SmtError>;
    fn bit_or(self, other: Self) -> Result<Self, SmtError>;
    fn bit_xor(self, other: Self) -> Result<Self, SmtError>;
    fn shl(self, other: Self) -> Result<Self, SmtError>;
    fn shr(self, other: Self) -> Result<Self, SmtError>;
    fn complement(self) -> Result<Self, SmtError>;
    fn implies(self, other: Self) -> Result<Self, SmtError>;
    fn not(self) -> Result<Self, SmtError>;
    fn ite(self, if_case: Self, else_case: Self) -> Result<Self, SmtError>;
    fn eq(self, other: Self) -> Result<Self, SmtError>;
    fn neq(self, other: Self) -> Result<Self, SmtError>;
    fn substitute(self, sub_term: Self, for_term: Self) -> Result<Self, SmtError>;
    fn substitute_vars<IT: TypedTerm>(self, var_sub: &HashMap<IT, IT>) -> Result<Self, SmtError>;
    fn to_sub_val(self, rhs: Self) -> Result<(Self, Self), SmtError>;
    fn const_array(const_val: Self) -> Result<Self, SmtError>;
    fn extract_integer(&self) -> Result<BigInt, SmtError>;
    fn quantify(self, quantifier: Quantifier, vars: Vec<(String, TermSort)>) -> Result<Self, SmtError>;
    fn label(self, label: &String) -> Result<Self, SmtError>;
    fn get_var_axiom(op: &NumericOp) -> Option<UninterpretedFunction>;
    fn get_sig_axiom(op: &FiniteFieldOp) -> Option<UninterpretedFunction>;
    fn create_struct(struct_def: HashMap<String, Self>) -> Result<Self, SmtError>;
    fn is_struct(&self) -> bool;
    fn count_vars(&self) -> usize;
    fn get_vars(&self) -> HashSet<Term>;
    fn contains_only<IT: TypedTerm>(&self, vars: &HashSet<&IT>) -> bool;
    fn contains<IT: TypedTerm>(&self, vars: &HashSet<&IT>) -> bool;
    fn cast(self, to_sort: TermSort) -> Result<Self, SmtError>;
}

pub trait LazyTerm {
    fn var_ops(&self) -> &HashSet<NumericOp>;
    fn sig_ops(&self) -> &HashSet<FiniteFieldOp>;
    fn aux_vars(&self) -> &HashSet<AuxVarDef>;
}

pub trait VCVarTerm: Sized {
    fn variable(sort: TermSort, name: &str) -> Result<Self, SmtError>;
}
#[derive(Clone, Eq, PartialEq)]
enum MixedVCTerm<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> {
    Bool(BoolTerm),
    Var(V),
    Arr(ArrayTerm<V, Self>),
    //UF_Arr(UniformUFTerm<V,Self>),
    Sig(S, PhantomData<FF>),
    Struct(HashMap<String, Self>, BoolTerm)
}

impl<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> Hash for MixedVCTerm<FF, V, S> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.term().hash(state)
    }
}

impl<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> From<bool> for MixedVCTerm<FF, V, S> {
    fn from(value: bool) -> Self {
        Self::wrap_bool(value.into())
    }
}

impl<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> From<&BigInt> for MixedVCTerm<FF, V, S> {
    fn from(value: &BigInt) -> Self {
        Self::wrap_var(value.into())
    }
}

impl<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> Into<Term> for MixedVCTerm<FF, V, S> {
    fn into(self) -> Term {
        match self {
            Self::Bool(b) => { b.into() }
            Self::Var(v) => { v.into() }
            Self::Arr(a) => { a.into() }
            Self::Sig(s, _) => { s.into() }
            Self::Struct(_, t) => { t.into() }
            //MixedVCTerm::UF_Arr(t) => { t.into() }
        }
    }
}

impl<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> BuildableTerm for MixedVCTerm<FF, V, S> {
    fn new(sort: TermSort, term: Term) -> Result<Self, SmtError> {
        if V::underlying_sort() == sort {
            Ok(Self::wrap_var(V::new(sort, term)?))
        }
        else if S::underlying_sort() == sort {
            Ok(Self::wrap_sig(S::new(sort, term)?))
        }
        else if sort == TermSort::Bool {
            Ok(Self::wrap_bool(BoolTerm::new(sort, term)?))
        }
        else if let TermSort::Array(_, _) = &sort {
            Ok(Self::wrap_arr(ArrayTerm::new(sort, term)?))
        }
        else {
            Err(SmtError::UnsupportedSort("MixedVCTerm", sort))
        }
    }
}

impl<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> TypedTerm for MixedVCTerm<FF, V, S> {
    fn term(&self) -> &Term {
        match self {
            Self::Bool(b) => { b.term() }
            Self::Var(v) => { v.term() }
            Self::Arr(a) => { a.term() }
            Self::Sig(s, _) => { s.term() }
            Self::Struct(s, t) => {
                t.term()
            }
            //MixedVCTerm::UF_Arr(a) => { a.term() }
        }
    }

    fn term_mut(&mut self) -> &mut Term {
        match self {
            Self::Bool(b) => { b.term_mut() }
            Self::Var(v) => { v.term_mut() }
            Self::Arr(a) => { a.term_mut() }
            Self::Sig(s, _) => { s.term_mut() }
            Self::Struct(s, t) => {
                t.term_mut()
            }
            //MixedVCTerm::UF_Arr(a) => { a.term_mut() }
        }
    }

    fn sort(&self) -> TermSort {
        match self {
            Self::Bool(b) => { b.sort() }
            Self::Var(v) => { v.sort() }
            Self::Arr(a) => { a.sort() }
            Self::Sig(s, _) => { s.sort() }
            Self::Struct(_, _) => { BoolTerm::underlying_sort() }
            //MixedVCTerm::UF_Arr(a) => { a.sort() }
        }
    }
}

impl<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> VCVarTerm for MixedVCTerm<FF, V, S> {
    fn variable(sort: TermSort, name: &str) -> Result<Self, SmtError> {
        if V::underlying_sort() == sort {
            Ok(Self::wrap_var(V::variable(name)))
        }
        else if S::underlying_sort() == sort {
            Ok(Self::wrap_sig(S::variable(name)))
        }
        else if sort == TermSort::Bool {
            Ok(Self::wrap_bool(BoolTerm::variable(name)))
        }
        else if let TermSort::Array(_, _) = &sort {
            let var_term = SmtUtils::variable(name);
            Ok(Self::wrap_arr(ArrayTerm::new(sort, var_term)?))
        }
        else {
            Err(SmtError::UnsupportedSort("variable", sort))
        }
    }
}

impl<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> MixedVCTerm<FF, V, S> {
    fn wrap_struct(struct_def: HashMap<String, Self>) -> Result<Self, SmtError> {
        let mut vars = vec![];
        let mut conjuncts = vec![];
        for (name, term) in &struct_def {
            let term_sort = term.sort();
            let q_term = Self::variable(term.sort(), &name)?;
            let eq_term = q_term.eq(term.clone())?;
            conjuncts.push(eq_term);
            vars.push((name.clone(), term_sort));
        }
        let var_assignment = BoolTerm::and_all(conjuncts);
        let quantified = var_assignment.quantify(Quantifier::Exists, vars)?;
        Ok(Self::Struct(struct_def, quantified))
    }
    fn eq(self, other: Self) -> Result<BoolTerm, SmtError> {
        let s1 = self.sort();
        let s2 = other.sort();
        let combined = (self, other);
        if let (Self::Bool(t1), Self::Bool(t2)) = combined {
            t1.eq(t2)
        }
        else if let (Self::Var(t1), Self::Var(t2)) = combined {
            t1.eq(t2)
        }
        else if let (Self::Sig(t1, _), Self::Sig(t2, _)) = combined {
            t1.eq(t2)
        }
        else if let (Self::Arr(t1), Self::Arr(t2)) = combined {
            t1.eq(t2)
        }
        else {
            Err(SmtError::MismatchedSort("eq", s1, s2))
        }
    }
    fn wrap_sig(term: S) -> Self {
        Self::Sig(term, Default::default())
    }
    fn wrap_var(term: V) -> Self {
        Self::Var(term)
    }
    fn wrap_arr(term: ArrayTerm<V, Self>) -> Self {
        Self::Arr(term)
    }
    fn wrap_bool(term: BoolTerm) -> Self {
        Self::Bool(term)
    }
    fn is_array(&self) -> bool {
        if let Self::Arr(_) = self { true } else { false }
    }
    fn is_variable(&self) -> bool {
        if let Self::Var(_) = self { true } else { false }
    }

    fn is_signal(&self) -> bool {
        if let Self::Sig(_, _) = self { true } else { false }
    }

    fn is_bool(&self) -> bool {
        if let Self::Bool(_) = self { true } else { false }
    }
    fn is_struct(&self) -> bool {
        if let Self::Struct(_, _) = self {true} else {false}
    }

    fn combine_term_sorts(sort1: &TermSort, sort2: &TermSort) -> Result<TermSort, SmtError> {
        if sort1 == sort2 {
            return Ok(sort1.clone());
        }
        match (sort1, sort2) {
            (TermSort::Array(i1, v1), TermSort::Array(i2, v2)) => {
                if i1 != i2 {
                    return Err(SmtError::MismatchedSort("combine_term_sort", sort1.clone(), sort2.clone()))
                }
                let value_sort = Self::combine_term_sorts(v1, v2)?;
                Ok(TermSort::Array(i1.clone(), Box::new(value_sort)))
            }
            (TermSort::UninterpretedFn(i1, o1), TermSort::UninterpretedFn(i2, o2)) => {
                if i1.len() != i2.len() {
                    return Err(SmtError::IncorrectArgumentCount("combine_term_sorts", i1.len(), i2.len()))
                }
                for i in 0..i1.len() {
                    if i1[i] != i2[i] {
                        return Err(SmtError::MismatchedSort("combine_term_sort", sort1.clone(), sort2.clone()))
                    }
                }

                let value_sort = Self::combine_term_sorts(o1, o2)?;
                Ok(TermSort::UninterpretedFn(i1.clone(), Box::new(value_sort)))
            }
            (TermSort::Int, TermSort::FiniteField(_)) => {
                Ok(sort2.clone())
            }
            (TermSort::Int, TermSort::IntFiniteField(_)) => {
                Ok(sort2.clone())
            }
            (TermSort::FiniteField(_), TermSort::Int) => {
                Ok(sort1.clone())
            }
            (TermSort::IntFiniteField(_), TermSort::Int) => {
                Ok(sort1.clone())
            }
            (_, _) => {
                Err(SmtError::MismatchedSort("combine_term_sort", sort1.clone(), sort2.clone()))
            }
        }
    }
    fn match_array_terms(self, other: Self) -> Result<(Self, Self), SmtError> {
        let combined_sort = Self::combine_term_sorts(&self.sort(), &other.sort())?;
        let self_array = ArrayTerm::new(combined_sort.clone(), self.term().clone())?;
        let other_array = ArrayTerm::new(combined_sort, other.term().clone())?;
        Ok((Self::wrap_arr(self_array), Self::wrap_arr(other_array)))
    }

    fn match_scalar_terms(self, other: Self) -> Result<(Self, Self), SmtError> {
        match (self, other) {
            (Self::Sig(s1,p1), Self::Sig(s2,p2)) => {
                Ok((Self::Sig(s1, p1), Self::Sig(s2,p2)))
            }
            (Self::Sig(s1,p1), Self::Var(v2)) => {
                Ok((Self::Sig(s1,p1), Self::Sig(v2.into(), p1.clone())))
            }
            (Self::Sig(s1,p1), Self::Bool(b2)) => {
                let one = S::from(&BigInt::one());
                let zero = S::from(&BigInt::zero());
                let bool_sig = BoolTerm::ite(b2, one, zero)?;
                Ok((Self::Sig(s1,p1), Self::Sig(bool_sig, p1.clone())))
            }
            (Self::Var(v1), Self::Sig(s2, p2)) => {
                Ok((Self::Sig(v1.into(), p2), Self::Sig(s2,p2.clone())))
            }
            (Self::Var(v1), Self::Var(v2)) => {
                Ok((Self::Var(v1), Self::Var(v2)))
            }
            (Self::Var(v1), Self::Bool(b2)) => {
                let one = V::from(&BigInt::one());
                let zero = V::from(&BigInt::zero());
                let bool_var = BoolTerm::ite(b2, one, zero)?;
                Ok((Self::Var(v1), Self::Var(bool_var)))
            }
            (Self::Bool(b1), Self::Sig(s2,p2)) => {
                let one = S::from(&BigInt::one());
                let zero = S::from(&BigInt::zero());
                let bool_sig = BoolTerm::ite(b1, one, zero)?;
                Ok((Self::Sig(bool_sig, p2), Self::Sig(s2, p2.clone())))
            }
            (Self::Bool(b1), Self::Var(v2)) => {
                let one = V::from(&BigInt::one());
                let zero = V::from(&BigInt::zero());
                let bool_var = BoolTerm::ite(b1, one, zero)?;
                Ok((Self::Var(bool_var), Self::Var(v2)))
            }
            (Self::Bool(b1), Self::Bool(b2)) => {
                Ok((Self::Bool(b1), Self::Bool(b2)))
            }
            (Self::Struct(_,_), _) => {
                Err(SmtError::IncorrectType("match_scalar_terms", "struct", None))
            }
            (Self::Arr(t), _) => {
                Err(SmtError::IncorrectType("match_scalar_terms", "array", Some(t.sort())))
            }
            (_, Self::Struct(_,_)) => {
                Err(SmtError::IncorrectType("match_scalar_terms", "struct", None))
            }
            (_, Self::Arr(t)) => {
                Err(SmtError::IncorrectType("match_scalar_terms", "array", Some(t.sort())))
            }
            /*(MixedVCTerm::UF_Arr(t), _) => {
                Err(SmtError::IncorrectType("match_scalar_terms", "uf_arr", Some(t.sort())))
            }
            (_, MixedVCTerm::UF_Arr(t)) => {
                Err(SmtError::IncorrectType("match_scalar_terms", "uf_arr", Some(t.sort())))
            }*/
        }
    }

    fn match_terms(self, other: Self) -> Result<(Self, Self), SmtError> {
        match self {
            MixedVCTerm::Bool(_) => { self.match_scalar_terms(other) }
            MixedVCTerm::Var(_) => { self.match_scalar_terms(other) }
            MixedVCTerm::Arr(_) => { self.match_array_terms(other) }
            MixedVCTerm::Sig(_, _) => { self.match_scalar_terms(other) }
            MixedVCTerm::Struct(_, _) => {
                Err(SmtError::IncorrectType("match_terms", "struct", None))
            }
            //MixedVCTerm::UF_Arr(_) => { self.match_array_terms(other) }
        }
    }

    /*fn match_numeric_terms(self, other: Self) -> Result<(Option<(S, S)>, Option<(V, V)>), SmtError> {
        if let Self::Sig(s1, _) = self {
            if let Self::Sig(s2, _) = other {
                Ok((Option::Some((s1, s2)), Option::None))
            }
            else if let Self::Var(v2) = other {
                Ok((Option::Some((s1, v2.into())), Option::None))
            }
            else {
                Err(SmtError::IncorrectSort("match_numeric_terms", S::underlying_sort(), other.sort()))
            }
        }
        else if let Self::Sig(s2, _) = other {
            if let Self::Var(v1) = self {
                Ok((Option::Some((v1.into(), s2)), Option::None))
            }
            else {
                Err(SmtError::IncorrectSort("match_numeric_terms", S::underlying_sort(), self.sort()))
            }
        }
        else if let Self::Var(v1) = self {
            if let Self::Var(v2) = other {
                Ok((Option::None, Option::Some((v1, v2))))
            }
            else {
                Err(SmtError::IncorrectSort("match_numeric_terms", V::underlying_sort(), other.sort()))
            }
        }
        else {
            println!("{}", self.term());
            println!("{}", other.term());
            Err(SmtError::IncorrectType("match_numeric_terms", "Numeric", Some(self.sort())))
        }
    }*/
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct AuxVarDef {
    pub sort: TermSort,
    pub name: String,
    pub axiom: BoolTerm
}
impl AuxVarDef {
    pub fn new(sort: TermSort, name: String, axiom: BoolTerm) -> Self {
        Self { sort, name, axiom }
    }

    pub fn fresh_identifier(base: String) -> String {
        format!("{}{}", base, get_unique_id())
    }
}

#[derive(Clone, Eq, PartialEq)]
pub struct LazyVCTerm<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> {
    var_ops: HashSet<NumericOp>,
    sig_ops: HashSet<FiniteFieldOp>,
    aux_vars: HashSet<AuxVarDef>,
    term: MixedVCTerm<FF, V, S>
}

impl<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> Hash for LazyVCTerm<FF, V, S> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.term().hash(state)
    }
}

impl<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> Display for LazyVCTerm<FF, V, S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.term().to_string())
    }
}

impl<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> Into<Term> for LazyVCTerm<FF, V, S> {
    fn into(self) -> Term {
        self.term.into()
    }
}

impl<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> TypedTerm for LazyVCTerm<FF, V, S> {
    fn term(&self) -> &Term {
        self.term.term()
    }

    fn term_mut(&mut self) -> &mut Term {
        self.term.term_mut()
    }

    fn sort(&self) -> TermSort {
        self.term.sort()
    }
}

impl<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> From<bool> for LazyVCTerm<FF, V, S> {
    fn from(value: bool) -> Self {
        Self::wrap_bool(HashSet::new(), HashSet::new(), HashSet::new(), value.into())
    }
}

impl<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> From<&BigInt> for LazyVCTerm<FF, V, S> {
    fn from(value: &BigInt) -> Self {
        Self::wrap_var(HashSet::new(), HashSet::new(), HashSet::new(), value.into())
    }
}

impl<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> VCTerm for LazyVCTerm<FF, V, S> {
    fn variable_sort() -> TermSort {
        V::underlying_sort()
    }

    fn signal_sort() -> TermSort {
        S::underlying_sort()
    }

    fn is_array(&self) -> bool {
        self.term.is_array()
    }

    fn is_variable(&self) -> bool {
        self.term.is_variable()
    }

    fn is_signal(&self) -> bool {
        self.term.is_signal()
    }

    fn is_bool(&self) -> bool {
        self.term.is_bool()
    }

    fn is_struct(&self) -> bool { self.term.is_struct() }

    fn label(self, label: &String) -> Result<Self, SmtError> {
        match self.term {
            MixedVCTerm::Bool(b) => {
                Ok(Self::wrap_bool(self.var_ops, self.sig_ops, self.aux_vars, b.label(label)?))
            }
            MixedVCTerm::Var(v) => {
                Ok(Self::wrap_var(self.var_ops, self.sig_ops, self.aux_vars, v.label(label)?))
            }
            MixedVCTerm::Arr(a) => {
                Ok(Self::wrap_arr(self.var_ops, self.sig_ops, self.aux_vars, a.label(label)?))
            }
            MixedVCTerm::Sig(s, _) => {
                Ok(Self::wrap_sig(self.var_ops, self.sig_ops, self.aux_vars, s.label(label)?))
            }
            MixedVCTerm::Struct(_, _) => {
                Err(SmtError::UnsupportedType("label", "struct", None))
            }
        }
    }

    fn quantify(self, quantifier: Quantifier, vars: Vec<(String, TermSort)>) -> Result<Self, SmtError> {
        if vars.is_empty() {
            return Ok(self)
        }

        match self.term {
            MixedVCTerm::Bool(b) => {
                Ok(Self::wrap_bool(self.var_ops, self.sig_ops, self.aux_vars, b.quantify(quantifier, vars)?))
            }
            MixedVCTerm::Var(v) => {
                Ok(Self::wrap_var(self.var_ops, self.sig_ops, self.aux_vars, v.quantify(quantifier, vars)?))
            }
            MixedVCTerm::Arr(a) => {
                Ok(Self::wrap_arr(self.var_ops, self.sig_ops, self.aux_vars, a.quantify(quantifier, vars)?))
            }
            MixedVCTerm::Sig(s, _) => {
                Ok(Self::wrap_sig(self.var_ops, self.sig_ops, self.aux_vars, s.quantify(quantifier, vars)?))
            }
            MixedVCTerm::Struct(_, _) => {
                Err(SmtError::UnsupportedType("quantify", "struct", None))
            }
        }
    }

    fn add(mut self, other: Self) -> Result<Self, SmtError> {
        let var_op = |mut var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, v1: V, v2: V| {
            var_ops.insert(NumericOp::Add);
            Ok(Self::wrap_var(var_ops, sig_ops, aux_vars, v1.add(v2)?))
        };
        let sig_op = |var_ops: HashSet<NumericOp>, mut sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, s1: S, s2: S| {
            sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Add));
            Ok(Self::wrap_sig(var_ops, sig_ops, aux_vars, s1.add(s2)?))
        };
        self.apply_numeric_op(other, var_op, sig_op)

        /*let (unified_self, unified_other) = self.match_terms(other)?;
        let self_sort = unified_self.sort();
        let mut var_ops = unified_self.var_ops;
        var_ops.extend(unified_other.var_ops);
        let mut sig_ops = unified_self.sig_ops;
        sig_ops.extend(unified_other.sig_ops);
        match (unified_self.term, unified_other.term) {
            (MixedVCTerm::Var(v1), MixedVCTerm::Var(v2)) => {
                var_ops.insert(NumericOp::Add);
                Ok(Self::wrap_var(var_ops, sig_ops, v1.add(v2)?))
            }
            (MixedVCTerm::Sig(s1,_), MixedVCTerm::Sig(s2,_)) => {
                sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Add));
                Ok(Self::wrap_sig(var_ops, sig_ops, s1.add(s2)?))
            }
            (_,_) => {
                unreachable!("Unsupported add type {}", self_sort)
            }
        }*/
    }

    fn sub(mut self, other: Self) -> Result<Self, SmtError> {
        let var_op = |mut var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, v1: V, v2: V| {
            var_ops.insert(NumericOp::Sub);
            Ok(Self::wrap_var(var_ops, sig_ops, aux_vars, v1.sub(v2)?))
        };
        let sig_op = |var_ops: HashSet<NumericOp>, mut sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, s1: S, s2: S| {
            sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Sub));
            Ok(Self::wrap_sig(var_ops, sig_ops, aux_vars, s1.sub(s2)?))
        };
        self.apply_numeric_op(other, var_op, sig_op)

        /*let (unified_self, unified_other) = self.match_terms(other)?;
        let self_sort = unified_self.sort();
        let mut var_ops = unified_self.var_ops;
        var_ops.extend(unified_other.var_ops);
        let mut sig_ops = unified_self.sig_ops;
        sig_ops.extend(unified_other.sig_ops);
        match (unified_self.term, unified_other.term) {
            (MixedVCTerm::Var(v1), MixedVCTerm::Var(v2)) => {
                var_ops.insert(NumericOp::Sub);
                Ok(Self::wrap_var(var_ops, sig_ops, v1.sub(v2)?))
            }
            (MixedVCTerm::Sig(s1,_), MixedVCTerm::Sig(s2,_)) => {
                sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Sub));
                Ok(Self::wrap_sig(var_ops, sig_ops, s1.sub(s2)?))
            }
            (_,_) => {
                unreachable!("Unsupported sub type {}", self_sort)
            }
        }*/
    }

    fn mul(mut self, other: Self) -> Result<Self, SmtError> {
        let var_op = |mut var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, v1: V, v2: V| {
            var_ops.insert(NumericOp::Mul);
            Ok(Self::wrap_var(var_ops, sig_ops, aux_vars, v1.mul(v2)?))
        };
        let sig_op = |var_ops: HashSet<NumericOp>, mut sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, s1: S, s2: S| {
            sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Mul));
            Ok(Self::wrap_sig(var_ops, sig_ops, aux_vars, s1.mul(s2)?))
        };
        self.apply_numeric_op(other, var_op, sig_op)

        /*let (unified_self, unified_other) = self.match_terms(other)?;
        let self_sort = unified_self.sort();
        let mut var_ops = unified_self.var_ops;
        var_ops.extend(unified_other.var_ops);
        let mut sig_ops = unified_self.sig_ops;
        sig_ops.extend(unified_other.sig_ops);
        match (unified_self.term, unified_other.term) {
            (MixedVCTerm::Var(v1), MixedVCTerm::Var(v2)) => {
                var_ops.insert(NumericOp::Mul);
                Ok(Self::wrap_var(var_ops, sig_ops, v1.mul(v2)?))
            }
            (MixedVCTerm::Sig(s1,_), MixedVCTerm::Sig(s2,_)) => {
                sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Mul));
                Ok(Self::wrap_sig(var_ops, sig_ops, s1.mul(s2)?))
            }
            (_,_) => {
                unreachable!("Unsupported mul type {}", self_sort)
            }
        }*/
    }

    fn mul_by_inverse(self, other: Self) -> Result<Self, SmtError> {
        let var_op = |mut var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, mut aux_vars: HashSet<AuxVarDef>, v1: V, v2: V| {
            var_ops.insert(NumericOp::Mul);
            let res_name = AuxVarDef::fresh_identifier(String::from("inverse_var"));
            let res_sig = S::variable(res_name.as_ref());
            let axiom = res_sig.clone().mul(v2.into())?.eq(v1.into())?;
            aux_vars.insert(AuxVarDef::new(V::underlying_sort(), res_name.clone(), axiom));
            let res = V::variable(res_name.as_ref());
            Ok(Self::wrap_var(var_ops, sig_ops, aux_vars, res))
        };
        let sig_op = |var_ops: HashSet<NumericOp>, mut sig_ops: HashSet<FiniteFieldOp>, mut aux_vars: HashSet<AuxVarDef>, s1: S, s2: S| {
            sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Mul));
            let res_name = AuxVarDef::fresh_identifier(String::from("inverse_sig"));
            let res = S::variable(res_name.as_ref());
            let axiom = res.clone().mul(s2)?.eq(s1)?;
            aux_vars.insert(AuxVarDef::new(V::underlying_sort(), res_name, axiom));
            Ok(Self::wrap_sig(var_ops, sig_ops, aux_vars, res))
        };
        self.apply_numeric_op(other, var_op, sig_op)
    }

    fn div(mut self, other: Self) -> Result<Self, SmtError> {
        let var_op = |mut var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, v1: V, v2: V| {
            var_ops.insert(NumericOp::Div);
            Ok(Self::wrap_var(var_ops, sig_ops, aux_vars, v1.div(v2)?))
        };
        let sig_op = |var_ops: HashSet<NumericOp>, mut sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, s1: S, s2: S| {
            sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Div));
            Ok(Self::wrap_sig(var_ops, sig_ops, aux_vars, s1.div(s2)?))
        };
        self.apply_numeric_op(other, var_op, sig_op)

        /*let (unified_self, unified_other) = self.match_terms(other)?;
        let self_sort = unified_self.sort();
        let mut var_ops = unified_self.var_ops;
        var_ops.extend(unified_other.var_ops);
        let mut sig_ops = unified_self.sig_ops;
        sig_ops.extend(unified_other.sig_ops);
        match (unified_self.term, unified_other.term) {
            (MixedVCTerm::Var(v1), MixedVCTerm::Var(v2)) => {
                var_ops.insert(NumericOp::Div);
                Ok(Self::wrap_var(var_ops, sig_ops, v1.div(v2)?))
            }
            (MixedVCTerm::Sig(s1,_), MixedVCTerm::Sig(s2,_)) => {
                sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Div));
                Ok(Self::wrap_sig(var_ops, sig_ops, s1.div(s2)?))
            }
            (_,_) => {
                unreachable!("Unsupported div type {}", self_sort)
            }
        }*/
    }

    fn modulus(mut self, other: Self) -> Result<Self, SmtError> {
        let var_op = |mut var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, v1: V, v2: V| {
            var_ops.insert(NumericOp::Mod);
            Ok(Self::wrap_var(var_ops, sig_ops, aux_vars, v1.modulus(v2)?))
        };
        let sig_op = |var_ops: HashSet<NumericOp>, mut sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, s1: S, s2: S| {
            sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Mod));
            Ok(Self::wrap_sig(var_ops, sig_ops,aux_vars, s1.modulus(s2)?))
        };
        self.apply_numeric_op(other, var_op, sig_op)

        /*let (unified_self, unified_other) = self.match_terms(other)?;
        let self_sort = unified_self.sort();
        let mut var_ops = unified_self.var_ops;
        var_ops.extend(unified_other.var_ops);
        let mut sig_ops = unified_self.sig_ops;
        sig_ops.extend(unified_other.sig_ops);
        match (unified_self.term, unified_other.term) {
            (MixedVCTerm::Var(v1), MixedVCTerm::Var(v2)) => {
                var_ops.insert(NumericOp::Mod);
                Ok(Self::wrap_var(var_ops, sig_ops, v1.modulus(v2)?))
            }
            (MixedVCTerm::Sig(s1,_), MixedVCTerm::Sig(s2,_)) => {
                sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Mod));
                Ok(Self::wrap_sig(var_ops, sig_ops, s1.modulus(s2)?))
            }
            (_,_) => {
                unreachable!("Unsupported modulus type {}", self_sort)
            }
        }*/
    }

    fn negate(mut self) -> Result<Self, SmtError> {
        if let MixedVCTerm::Sig(s, _) = self.term {
            self.sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Negate));
            Ok(Self::wrap_sig(self.var_ops, self.sig_ops, self.aux_vars, s.negate()?))
        }
        else if let MixedVCTerm::Var(v) = self.term {
            self.var_ops.insert(NumericOp::Negate);
            Ok(Self::wrap_var(self.var_ops, self.sig_ops, self.aux_vars, v.negate()?))
        }
        else {
            Err(SmtError::IncorrectType("negate", "numeric", Some(self.sort())))
        }
    }

    fn inverse(mut self) -> Result<Self, SmtError> {
        if let MixedVCTerm::Sig(s, _) = self.term {
            self.sig_ops.insert(FiniteFieldOp::Inverse);
            Ok(Self::wrap_sig(self.var_ops, self.sig_ops, self.aux_vars, s.inverse()?))
        }
        else if let MixedVCTerm::Var(v) = self.term {
            self.sig_ops.insert(FiniteFieldOp::Inverse);
            Ok(Self::wrap_sig(self.var_ops, self.sig_ops, self.aux_vars, S::from(v).inverse()?))
        }
        else {
            Err(SmtError::IncorrectType("inverse", "numeric", Some(self.sort())))
        }
    }

    fn gt(mut self, other: Self) -> Result<Self, SmtError> {
        let var_op = |mut var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, v1: V, v2: V| {
            var_ops.insert(NumericOp::Gt);
            Ok(Self::wrap_bool(var_ops, sig_ops, aux_vars, v1.gt(v2)?))
        };
        let sig_op = |var_ops: HashSet<NumericOp>, mut sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, s1: S, s2: S| {
            sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Gt));
            Ok(Self::wrap_bool(var_ops, sig_ops, aux_vars, s1.gt(s2)?))
        };
        self.apply_numeric_op(other, var_op, sig_op)

        /*let (unified_self, unified_other) = self.match_terms(other)?;
        let self_sort = unified_self.sort();
        let mut var_ops = unified_self.var_ops;
        var_ops.extend(unified_other.var_ops);
        let mut sig_ops = unified_self.sig_ops;
        sig_ops.extend(unified_other.sig_ops);
        match (unified_self.term, unified_other.term) {
            (MixedVCTerm::Var(v1), MixedVCTerm::Var(v2)) => {
                var_ops.insert(NumericOp::Gt);
                Ok(Self::wrap_bool(var_ops, sig_ops, v1.gt(v2)?))
            }
            (MixedVCTerm::Sig(s1,_), MixedVCTerm::Sig(s2,_)) => {
                sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Gt));
                Ok(Self::wrap_bool(var_ops, sig_ops, s1.gt(s2)?))
            }
            (_,_) => {
                unreachable!("Unsupported gt type {}", self_sort)
            }
        }*/
    }

    fn gte(mut self, other: Self) -> Result<Self, SmtError> {
        let var_op = |mut var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, v1: V, v2: V| {
            var_ops.insert(NumericOp::Gte);
            Ok(Self::wrap_bool(var_ops, sig_ops, aux_vars, v1.gte(v2)?))
        };
        let sig_op = |var_ops: HashSet<NumericOp>, mut sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, s1: S, s2: S| {
            sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Gte));
            Ok(Self::wrap_bool(var_ops, sig_ops, aux_vars, s1.gte(s2)?))
        };
        self.apply_numeric_op(other, var_op, sig_op)

        /*let (unified_self, unified_other) = self.match_terms(other)?;
        let self_sort = unified_self.sort();
        let mut var_ops = unified_self.var_ops;
        var_ops.extend(unified_other.var_ops);
        let mut sig_ops = unified_self.sig_ops;
        sig_ops.extend(unified_other.sig_ops);
        match (unified_self.term, unified_other.term) {
            (MixedVCTerm::Var(v1), MixedVCTerm::Var(v2)) => {
                var_ops.insert(NumericOp::Gte);
                Ok(Self::wrap_bool(var_ops, sig_ops, v1.gte(v2)?))
            }
            (MixedVCTerm::Sig(s1,_), MixedVCTerm::Sig(s2,_)) => {
                sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Gte));
                Ok(Self::wrap_bool(var_ops, sig_ops, s1.gte(s2)?))
            }
            (_,_) => {
                unreachable!("Unsupported gte type {}", self_sort)
            }
        }*/
    }

    fn lt(mut self, other: Self) -> Result<Self, SmtError> {
        let var_op = |mut var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, v1: V, v2: V| {
            var_ops.insert(NumericOp::Lt);
            Ok(Self::wrap_bool(var_ops, sig_ops, aux_vars, v1.lt(v2)?))
        };
        let sig_op = |var_ops: HashSet<NumericOp>, mut sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, s1: S, s2: S| {
            sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Lt));
            Ok(Self::wrap_bool(var_ops, sig_ops, aux_vars,  s1.lt(s2)?))
        };
        self.apply_numeric_op(other, var_op, sig_op)

        /*let (unified_self, unified_other) = self.match_terms(other)?;
        let self_sort = unified_self.sort();
        let mut var_ops = unified_self.var_ops;
        var_ops.extend(unified_other.var_ops);
        let mut sig_ops = unified_self.sig_ops;
        sig_ops.extend(unified_other.sig_ops);
        match (unified_self.term, unified_other.term) {
            (MixedVCTerm::Var(v1), MixedVCTerm::Var(v2)) => {
                var_ops.insert(NumericOp::Lt);
                Ok(Self::wrap_bool(var_ops, sig_ops, v1.lt(v2)?))
            }
            (MixedVCTerm::Sig(s1,_), MixedVCTerm::Sig(s2,_)) => {
                sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Lt));
                Ok(Self::wrap_bool(var_ops, sig_ops, s1.lt(s2)?))
            }
            (_,_) => {
                unreachable!("Unsupported lt type {}", self_sort)
            }
        }*/
    }

    fn lte(mut self, other: Self) -> Result<Self, SmtError> {
        let var_op = |mut var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, v1: V, v2: V| {
            var_ops.insert(NumericOp::Lte);
            Ok(Self::wrap_bool(var_ops, sig_ops, aux_vars, v1.lte(v2)?))
        };
        let sig_op = |var_ops: HashSet<NumericOp>, mut sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, s1: S, s2: S| {
            sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Lte));
            Ok(Self::wrap_bool(var_ops, sig_ops, aux_vars, s1.lte(s2)?))
        };
        self.apply_numeric_op(other, var_op, sig_op)

        /*let (unified_self, unified_other) = self.match_terms(other)?;
        let self_sort = unified_self.sort();
        let mut var_ops = unified_self.var_ops;
        var_ops.extend(unified_other.var_ops);
        let mut sig_ops = unified_self.sig_ops;
        sig_ops.extend(unified_other.sig_ops);
        match (unified_self.term, unified_other.term) {
            (MixedVCTerm::Var(v1), MixedVCTerm::Var(v2)) => {
                var_ops.insert(NumericOp::Lte);
                Ok(Self::wrap_bool(var_ops, sig_ops, v1.lte(v2)?))
            }
            (MixedVCTerm::Sig(s1,_), MixedVCTerm::Sig(s2,_)) => {
                sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Lte));
                Ok(Self::wrap_bool(var_ops, sig_ops, s1.lte(s2)?))
            }
            (_,_) => {
                unreachable!("Unsupported lte type {}", self_sort)
            }
        }*/
    }

    fn select(mut self, index: Self) -> Result<Self, SmtError> {
        let index_sort = index.sort();
        if let MixedVCTerm::Arr(a) = self.term {
            self.sig_ops.extend(index.sig_ops);
            self.var_ops.extend(index.var_ops);
            self.aux_vars.extend(index.aux_vars);
            if let MixedVCTerm::Var(v) = index.term {
                Ok(Self::wrap(self.var_ops, self.sig_ops, self.aux_vars, a.select(v)?))
            }
            else {
                Err(SmtError::IncorrectSort("select index", Self::variable_sort(), index_sort))
            }
        }
        else if let MixedVCTerm::Struct(s, t) = self.term {
            self.sig_ops.extend(index.sig_ops.clone());
            self.var_ops.extend(index.var_ops.clone());
            let mut selected_def = HashMap::new();
            for (field, term) in s {
                let val = Self {var_ops: HashSet::new(), sig_ops: HashSet::new(), aux_vars: HashSet::new(), term};
                selected_def.insert(field, val.select(index.clone())?);
            }
            let mut new_def = Self::create_struct(selected_def)?;
            new_def.sig_ops = self.sig_ops;
            new_def.var_ops = self.var_ops;
            Ok(new_def)
        }
        else {
            println!("arr: {}, ind: {}", self.term(), index);
            Err(SmtError::IncorrectType("select", "Array", Some(self.sort())))
        }
    }

    fn store(mut self, index: Self, mut value: Self) -> Result<Self, SmtError> {
        if let MixedVCTerm::Arr(a) = self.term {
            if let MixedVCTerm::Var(ind_var) = index.term {
                let arr_sort = a.sort();

                if let TermSort::Array(_, v) = arr_sort {
                    if v.as_ref() == &S::underlying_sort() {
                        if let MixedVCTerm::Var(var) = value.term {
                            value = Self::wrap_sig(value.var_ops, value.sig_ops, value.aux_vars, var.into())
                        }
                    }
                    if v.as_ref() != &value.sort() {
                        println!("{}, {}, {}", a.term(), ind_var.term(), value);
                        return Err(SmtError::IncorrectSort("store", v.as_ref().clone(), value.sort()))
                    }
                }
                else {
                    unreachable!("Array must have an array sort")
                }

                let result = a.store(ind_var, value.term)?;
                self.sig_ops.extend(index.sig_ops);
                self.sig_ops.extend(value.sig_ops);
                self.var_ops.extend(index.var_ops);
                self.var_ops.extend(value.var_ops);
                self.aux_vars.extend(index.aux_vars);
                self.aux_vars.extend(value.aux_vars);
                Ok(Self::wrap_arr(self.var_ops, self.sig_ops, self.aux_vars, result))
            }
            else {
                Err(SmtError::IncorrectSort("store index", Self::variable_sort(), index.sort()))
            }
        }
        else {
            Err(SmtError::IncorrectType("store", "Array", Some(self.sort())))
        }
    }

    fn and(mut self, other: Self) -> Result<Self, SmtError> {
        let other_sort = other.sort();
        self.sig_ops.extend(other.sig_ops);
        self.var_ops.extend(other.var_ops);
        self.aux_vars.extend(other.aux_vars);
        if let MixedVCTerm::Bool(b1) = self.term {
            if let MixedVCTerm::Bool(b2) = other.term {
                Ok(Self::wrap_bool(self.var_ops, self.sig_ops, self.aux_vars, b1.and(b2)))
            }
            else {
                Err(SmtError::IncorrectSort("and", TermSort::Bool, other_sort))
            }
        }
        else {
            Err(SmtError::IncorrectSort("and", TermSort::Bool, self.sort()))
        }
    }

    fn and_all(mut conjuncts: Vec<Self>) -> Result<Self, SmtError> {
        if conjuncts.is_empty() {
            return Ok(true.into())
        }
        else if conjuncts.len() == 1 {
            return Ok(conjuncts.pop().unwrap())
        }

        let mut var_ops = HashSet::new();
        let mut sig_ops = HashSet::new();
        let mut aux_vars = HashSet::new();
        let mut bool_conjuncts = vec![];
        for conjunct in conjuncts {
            if let MixedVCTerm::Bool(b) = conjunct.term {
                var_ops.extend(conjunct.var_ops);
                sig_ops.extend(conjunct.sig_ops);
                aux_vars.extend(conjunct.aux_vars);
                bool_conjuncts.push(b)
            }
            else {
                return Err(SmtError::IncorrectSort("and_all", TermSort::Bool, conjunct.sort()))
            }
        }

        Ok(Self::wrap_bool(var_ops, sig_ops, aux_vars, BoolTerm::and_all(bool_conjuncts)))
    }

    fn or(mut self, other: Self) -> Result<Self, SmtError> {
        let other_sort = other.sort();
        self.sig_ops.extend(other.sig_ops);
        self.var_ops.extend(other.var_ops);
        self.aux_vars.extend(other.aux_vars);
        if let MixedVCTerm::Bool(b1) = self.term {
            if let MixedVCTerm::Bool(b2) = other.term {
                Ok(Self::wrap_bool(self.var_ops, self.sig_ops, self.aux_vars, b1.or(b2)))
            }
            else {
                Err(SmtError::IncorrectSort("or", TermSort::Bool, other_sort))
            }
        }
        else {
            Err(SmtError::IncorrectSort("or", TermSort::Bool, self.sort()))
        }
    }

    fn or_all(mut disjuncts: Vec<Self>) -> Result<Self, SmtError> {
        if disjuncts.is_empty() {
            return Ok(true.into())
        }
        else if disjuncts.len() == 1 {
            return Ok(disjuncts.pop().unwrap())
        }

        let mut var_ops = HashSet::new();
        let mut sig_ops = HashSet::new();
        let mut aux_vars = HashSet::new();
        let mut bool_disjuncts = vec![];
        for disjunct in disjuncts {
            if let MixedVCTerm::Bool(b) = disjunct.term {
                var_ops.extend(disjunct.var_ops);
                sig_ops.extend(disjunct.sig_ops);
                aux_vars.extend(disjunct.aux_vars);
                bool_disjuncts.push(b)
            }
            else {
                return Err(SmtError::IncorrectSort("or_all", TermSort::Bool, disjunct.sort()))
            }
        }

        Ok(Self::wrap_bool(var_ops, sig_ops, aux_vars, BoolTerm::or_all(bool_disjuncts)))
    }

    fn implies(mut self, other: Self) -> Result<Self, SmtError> {
        let other_sort = other.sort();
        self.sig_ops.extend(other.sig_ops);
        self.var_ops.extend(other.var_ops);
        self.aux_vars.extend(other.aux_vars);
        if let MixedVCTerm::Bool(b1) = self.term {
            if let MixedVCTerm::Bool(b2) = other.term {
                Ok(Self::wrap_bool(self.var_ops, self.sig_ops, self.aux_vars, b1.implies(b2)))
            }
            else {
                Err(SmtError::IncorrectSort("implies", TermSort::Bool, other_sort))
            }
        }
        else {
            Err(SmtError::IncorrectSort("implies", TermSort::Bool, self.sort()))
        }
    }

    fn not(self) -> Result<Self, SmtError> {
        if let MixedVCTerm::Bool(b) = self.term {
            Ok(Self::wrap_bool(self.var_ops, self.sig_ops, self.aux_vars, b.not()))
        }
        else {
            Err(SmtError::IncorrectSort("not", TermSort::Bool, self.sort()))
        }
    }

    fn ite(mut self, if_case: Self, else_case: Self) -> Result<Self, SmtError> {
        if let MixedVCTerm::Bool(c) = self.term {
            let if_sort = if_case.sort();
            let else_sort = else_case.sort();
            let (unified_if, unified_else) = if_case.match_terms(else_case)?;
            let mut sig_ops = self.sig_ops;
            sig_ops.extend(unified_if.sig_ops);
            sig_ops.extend(unified_else.sig_ops);
            let mut var_ops = self.var_ops;
            var_ops.extend(unified_if.var_ops);
            var_ops.extend(unified_else.var_ops);
            let mut aux_vars = self.aux_vars;
            aux_vars.extend(unified_if.aux_vars);
            aux_vars.extend(unified_else.aux_vars);

            match((unified_if.term, unified_else.term)) {
                (MixedVCTerm::Bool(b1), MixedVCTerm::Bool(b2)) => {
                    Ok(Self::wrap_bool(var_ops, sig_ops, aux_vars, c.ite(b1, b2)?))
                }
                (MixedVCTerm::Var(v1), MixedVCTerm::Var(v2)) => {
                    Ok(Self::wrap_var(var_ops, sig_ops, aux_vars, c.ite(v1, v2)?))
                }
                (MixedVCTerm::Arr(a1), MixedVCTerm::Arr(a2)) => {
                    Ok(Self::wrap_arr(var_ops, sig_ops, aux_vars, c.ite(a1, a2)?))
                }
                (MixedVCTerm::Sig(s1, _), MixedVCTerm::Sig(s2, _)) => {
                    Ok(Self::wrap_sig(var_ops, sig_ops, aux_vars, c.ite(s1, s2)?))
                }
                (_, _) => {
                    Err(SmtError::MismatchedSort("ite", if_sort, else_sort))
                }
            }
        }
        else {
            Err(SmtError::IncorrectSort("ite condition", TermSort::Bool, self.sort()))
        }
    }

    fn eq(mut self, other: Self) -> Result<Self, SmtError> {
        let (unified_self, unified_other) = self.match_terms(other)?;
        let mut var_ops = unified_self.var_ops;
        var_ops.extend(unified_other.var_ops);
        let mut sig_ops = unified_self.sig_ops;
        sig_ops.extend(unified_other.sig_ops);
        let mut aux_vars = unified_self.aux_vars;
        aux_vars.extend(unified_other.aux_vars);
        Ok(Self::wrap_bool(var_ops, sig_ops, aux_vars, unified_self.term.eq(unified_other.term)?))
    }

    fn neq(mut self, other: Self) -> Result<Self, SmtError> {
        let eq = self.eq(other)?;
        eq.not()
    }

    fn to_sub_val(mut self, mut rhs: Self) -> Result<(Self, Self), SmtError> {
        let lhs_sort = self.sort();
        let rhs_sort = rhs.sort();
        if lhs_sort != rhs_sort {
            (self, rhs) = self.match_terms(rhs)?;
        }

        if self.is_struct() {
            return Ok((self, rhs))
        }

        match self.term() {
            Term::Application(app, args_ref) => {
                let app_fn = app.to_string();
                if app_fn == "select" {
                    let mut args = args_ref.clone();
                    let arr = args.get(0).unwrap().clone();
                    args.push(rhs.term.into());
                    let store_val = SmtUtils::fn_application("store", args);
                    let new_sort = TermSort::Array(Box::new(Self::variable_sort()), Box::new(lhs_sort));
                    let mixed_arr = MixedVCTerm::<FF, V, S>::new(new_sort.clone(), arr)?;
                    let mixed_store = MixedVCTerm::<FF, V, S>::new(new_sort, store_val)?;
                    rhs.var_ops.extend(self.var_ops.clone());
                    rhs.sig_ops.extend(self.sig_ops.clone());
                    let wrapped_arr = Self::wrap(self.var_ops, self.sig_ops, self.aux_vars, mixed_arr);
                    let wrapped_store = Self::wrap(rhs.var_ops, rhs.sig_ops, rhs.aux_vars, mixed_store);
                    wrapped_arr.to_sub_val(wrapped_store)
                }
                else {
                    Ok((self, rhs))
                }
            }
            _ => {Ok((self, rhs))}
        }
    }

    fn contains_only<IT: TypedTerm>(&self, vars: &HashSet<&IT>) -> bool {
        let var_terms: HashSet<Term> = vars.iter().map(|t| t.term().clone()).collect();
        Self::contains_only_identifiers(self.term(), var_terms)
    }

    fn contains<IT: TypedTerm>(&self, vars: &HashSet<&IT>) -> bool {
        let var_terms: HashSet<Term> = vars.iter().map(|t| t.term().clone()).collect();

        let mut worklist = vec![self.term()];
        while !worklist.is_empty() {
            let cur = worklist.pop().unwrap();
            if var_terms.contains(cur) {
                return true;
            }

            match cur {
                Term::Application(_, sub_terms) => {
                    for t in sub_terms {
                        worklist.push(t);
                    }
                }
                Term::Annotation(term, _) => {
                    worklist.push(term)
                }
                Term::Forall(q_vars, term) => {
                    worklist.push(term)
                }
                Term::Exists(q_vars, term) => {
                    worklist.push(term)
                }
                Term::Let(bindings, term) => {
                    worklist.push(term)
                }
                Term::Identifier(_) => {}
                Term::SpecConstant(_) => {}
                Term::Match(term, _) => {
                    worklist.push(term)
                }
            }
        }

        false
    }

    fn substitute_vars<IT: TypedTerm>(mut self, var_sub: &HashMap<IT, IT>) -> Result<Self, SmtError> {
        let term_sub: HashMap<Term, Term> = var_sub.iter().map(|t| (t.0.term().clone(), t.1.term().clone())).collect();
        if let Some(to_term) = term_sub.get(self.term()) {
            let sub_term = MixedVCTerm::<FF,V,S>::new(self.sort(), to_term.clone())?;
            return Ok(Self::wrap(self.var_ops, self.sig_ops, self.aux_vars, sub_term));
        }

        let self_sort = self.sort();
        let mut self_term: Term = self.term.into();
        let mut aux_vars = vec![];
        for mut aux_var in &self.aux_vars {
            aux_vars.push((aux_var.sort.clone(), aux_var.name.clone(), aux_var.axiom.clone()));
        }

        let mut worklist = vec![&mut self_term];
        for aux_var in &mut aux_vars {
            worklist.push(aux_var.2.term_mut())
        }

        while !worklist.is_empty() {
            let cur = worklist.pop().unwrap();
            match cur {
                Term::Application(_, sub_terms) => {
                    for t in sub_terms {
                        if let Some(to_term) = term_sub.get(t) {
                            *t = to_term.clone();
                        }
                        else {
                            worklist.push(t);
                        }
                    }
                }
                Term::Annotation(term, _) => {
                    if let Some(to_term) = term_sub.get(term.as_ref()) {
                        *term = Box::new(to_term.clone())
                    }
                    else {
                        worklist.push(term)
                    }
                }
                Term::Forall(_, term) => {
                    if let Some(to_term) = term_sub.get(term.as_ref()) {
                        *term = Box::new(to_term.clone())
                    }
                    else {
                        worklist.push(term)
                    }
                }
                Term::Exists(_, term) => {
                    if let Some(to_term) = term_sub.get(term.as_ref()) {
                        *term = Box::new(to_term.clone())
                    }
                    else {
                        worklist.push(term)
                    }
                }
                // skip
                Term::SpecConstant(_) => {}
                Term::Identifier(_) => {}
                _ => { unreachable!("Unsupported Term type during Substitution") }
            }
        }

        let mut new_defs = HashSet::new();
        for var in aux_vars {
            new_defs.insert(AuxVarDef::new(var.0, var.1, var.2));
        }
        let sub_term = MixedVCTerm::<FF,V,S>::new(self_sort, Self::simplify(self_term)?)?;
        Ok(Self::wrap(self.var_ops, self.sig_ops, new_defs, sub_term))
    }

    fn substitute(self, sub_term: Self, for_term: Self) -> Result<Self, SmtError> {
        if sub_term.sort() != for_term.sort() {
            return Err(SmtError::MismatchedSort("substitute", sub_term.sort(), for_term.sort()))
        }

        let sub = if let (MixedVCTerm::Struct(sub_struct, _), MixedVCTerm::Struct(for_struct, _)) = (&sub_term.term, &for_term.term) {
            let mut sub = HashMap::new();

            assert!(sub_struct.len() == for_struct.len());
            for key in sub_struct.keys() {
                let substitute_for = (sub_struct.get(key), for_struct.get(key));
                if let (Some(sub_val), Some(for_val)) = substitute_for {
                    sub.insert(sub_val.clone(), for_val.clone());
                }
                else {
                    return Err(SmtError::MismatchedTypes("substitute", "struct", None))
                }
            }

            Ok(sub)
        }
        else if sub_term.is_struct() || for_term.is_struct() {
            Err(SmtError::IncorrectType("substitute", "struct", None))
        }
        else {
            let mut sub = HashMap::new();
            sub.insert(sub_term.term, for_term.term);
            Ok(sub)
        }?;

        let cur_term = self.term().clone();
        let mut new_term = self.substitute_vars(&sub)?;
        if new_term.term() != &cur_term {
            new_term.var_ops.extend(for_term.var_ops);
            new_term.sig_ops.extend(for_term.sig_ops);
            new_term.aux_vars.extend(for_term.aux_vars);
        }

        Ok(new_term)
    }

    fn const_array(const_val: Self) -> Result<Self, SmtError> {
        Ok(Self::wrap_arr(const_val.var_ops, const_val.sig_ops, const_val.aux_vars, ArrayTerm::const_arr(V::underlying_sort(), const_val.term)?))
    }

    fn extract_integer(&self) -> Result<BigInt, SmtError> {
        match self.term() {
            Term::SpecConstant(c) => {
                match c {
                    SpecConstant::Numeral(n) => {
                        BigInt::from_str(&*n.0).map_err(|_| SmtError::CannotParseInt(n.0.clone()))
                    }
                    SpecConstant::Decimal(d) => {
                        BigInt::from_str(&*d.0).map_err(|_| SmtError::CannotParseInt(d.0.clone()))
                    }
                    SpecConstant::Hexadecimal(h) => {
                        BigInt::from_str(&*h.0).map_err(|_| SmtError::CannotParseInt(h.0.clone()))
                    }
                    SpecConstant::Binary(b) => {
                        BigInt::from_str(&*b.0).map_err(|_| SmtError::CannotParseInt(b.0.clone()))
                    }
                    SpecConstant::String(s) => {
                        BigInt::from_str(s).map_err(|_| SmtError::CannotParseInt(s.clone()))
                    }
                }
            }
            _ => { Err(SmtError::CannotParseInt(self.term().to_string())) }
        }
    }

    fn get_var_axiom(op: &NumericOp) -> Option<UninterpretedFunction> {
        V::get_numeric_op_axiom(op)
    }

    fn get_sig_axiom(op: &FiniteFieldOp) -> Option<UninterpretedFunction> {
        S::get_ff_op_axiom(op)
    }

    fn pow(mut self, other: Self) -> Result<Self, SmtError> {
        let var_op = |mut var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, v1: V, v2: V| {
            var_ops.insert(NumericOp::Pow);
            Ok(Self::wrap_var(var_ops, sig_ops, aux_vars, v1.pow(v2)?))
        };
        let sig_op = |var_ops: HashSet<NumericOp>, mut sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, s1: S, s2: S| {
            sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Pow));
            Ok(Self::wrap_sig(var_ops, sig_ops, aux_vars, s1.pow(s2)?))
        };
        self.apply_numeric_op(other, var_op, sig_op)

        /*let (unified_self, unified_other) = self.match_terms(other)?;
        let self_sort = unified_self.sort();
        let mut var_ops = unified_self.var_ops;
        var_ops.extend(unified_other.var_ops);
        let mut sig_ops = unified_self.sig_ops;
        sig_ops.extend(unified_other.sig_ops);
        match (unified_self.term, unified_other.term) {
            (MixedVCTerm::Var(v1), MixedVCTerm::Var(v2)) => {
                var_ops.insert(NumericOp::Pow);
                Ok(Self::wrap_var(var_ops, sig_ops, v1.pow(v2)?))
            }
            (MixedVCTerm::Sig(s1,_), MixedVCTerm::Sig(s2,_)) => {
                sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Pow));
                Ok(Self::wrap_sig(var_ops, sig_ops, s1.pow(s2)?))
            }
            (_,_) => {
                unreachable!("Unsupported pow type {}", self_sort)
            }
        }*/
    }

    fn bit_and(mut self, other: Self) -> Result<Self, SmtError> {
        let var_op = |mut var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, v1: V, v2: V| {
            var_ops.insert(NumericOp::BitAnd);
            Ok(Self::wrap_var(var_ops, sig_ops, aux_vars, v1.bit_and(v2)?))
        };
        let sig_op = |var_ops: HashSet<NumericOp>, mut sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, s1: S, s2: S| {
            sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::BitAnd));
            Ok(Self::wrap_sig(var_ops, sig_ops, aux_vars, s1.bit_and(s2)?))
        };
        self.apply_numeric_op(other, var_op, sig_op)

        /*let (unified_self, unified_other) = self.match_terms(other)?;
        let self_sort = unified_self.sort();
        let mut var_ops = unified_self.var_ops;
        var_ops.extend(unified_other.var_ops);
        let mut sig_ops = unified_self.sig_ops;
        sig_ops.extend(unified_other.sig_ops);
        match (unified_self.term, unified_other.term) {
            (MixedVCTerm::Var(v1), MixedVCTerm::Var(v2)) => {
                var_ops.insert(NumericOp::BitAnd);
                Ok(Self::wrap_var(var_ops, sig_ops, v1.bit_and(v2)?))
            }
            (MixedVCTerm::Sig(s1,_), MixedVCTerm::Sig(s2,_)) => {
                sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::BitAnd));
                Ok(Self::wrap_sig(var_ops, sig_ops, s1.bit_and(s2)?))
            }
            (_,_) => {
                unreachable!("Unsupported bitwise and type {}", self_sort)
            }
        }*/
    }

    fn bit_or(mut self, other: Self) -> Result<Self, SmtError> {
        let var_op = |mut var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, v1: V, v2: V| {
            var_ops.insert(NumericOp::BitOr);
            Ok(Self::wrap_var(var_ops, sig_ops, aux_vars, v1.bit_or(v2)?))
        };
        let sig_op = |var_ops: HashSet<NumericOp>, mut sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, s1: S, s2: S| {
            sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::BitOr));
            Ok(Self::wrap_sig(var_ops, sig_ops, aux_vars, s1.bit_or(s2)?))
        };
        self.apply_numeric_op(other, var_op, sig_op)

        /*let (unified_self, unified_other) = self.match_terms(other)?;
        let self_sort = unified_self.sort();
        let mut var_ops = unified_self.var_ops;
        var_ops.extend(unified_other.var_ops);
        let mut sig_ops = unified_self.sig_ops;
        sig_ops.extend(unified_other.sig_ops);
        match (unified_self.term, unified_other.term) {
            (MixedVCTerm::Var(v1), MixedVCTerm::Var(v2)) => {
                var_ops.insert(NumericOp::BitOr);
                Ok(Self::wrap_var(var_ops, sig_ops, v1.bit_or(v2)?))
            }
            (MixedVCTerm::Sig(s1,_), MixedVCTerm::Sig(s2,_)) => {
                sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::BitOr));
                Ok(Self::wrap_sig(var_ops, sig_ops, s1.bit_or(s2)?))
            }
            (_,_) => {
                unreachable!("Unsupported bitwise or type {}", self_sort)
            }
        }*/
    }

    fn bit_xor(mut self, other: Self) -> Result<Self, SmtError> {
        let var_op = |mut var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, v1: V, v2: V| {
            var_ops.insert(NumericOp::BitXor);
            Ok(Self::wrap_var(var_ops, sig_ops, aux_vars, v1.bit_xor(v2)?))
        };
        let sig_op = |var_ops: HashSet<NumericOp>, mut sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, s1: S, s2: S| {
            sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::BitXor));
            Ok(Self::wrap_sig(var_ops, sig_ops, aux_vars, s1.bit_xor(s2)?))
        };
        self.apply_numeric_op(other, var_op, sig_op)
        /*let (unified_self, unified_other) = self.match_terms(other)?;
        let self_sort = unified_self.sort();
        let mut var_ops = unified_self.var_ops;
        var_ops.extend(unified_other.var_ops);
        let mut sig_ops = unified_self.sig_ops;
        sig_ops.extend(unified_other.sig_ops);
        match (unified_self.term, unified_other.term) {
            (MixedVCTerm::Var(v1), MixedVCTerm::Var(v2)) => {
                var_ops.insert(NumericOp::BitXor);
                Ok(Self::wrap_var(var_ops, sig_ops, v1.bit_xor(v2)?))
            }
            (MixedVCTerm::Sig(s1,_), MixedVCTerm::Sig(s2,_)) => {
                sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::BitXor));
                Ok(Self::wrap_sig(var_ops, sig_ops, s1.bit_xor(s2)?))
            }
            (_,_) => {
                unreachable!("Unsupported bitwise or type {}", self_sort)
            }
        }*/
    }

    fn shl(mut self, other: Self) -> Result<Self, SmtError> {
        let var_op = |mut var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, v1: V, v2: V| {
            var_ops.insert(NumericOp::Shl);
            Ok(Self::wrap_var(var_ops, sig_ops, aux_vars, v1.shl(v2)?))
        };
        let sig_op = |var_ops: HashSet<NumericOp>, mut sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, s1: S, s2: S| {
            sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Shl));
            Ok(Self::wrap_sig(var_ops, sig_ops, aux_vars, s1.shl(s2)?))
        };
        self.apply_numeric_op(other, var_op, sig_op)

        /*let (unified_self, unified_other) = self.match_terms(other)?;
        let self_sort = unified_self.sort();
        let mut var_ops = unified_self.var_ops;
        var_ops.extend(unified_other.var_ops);
        let mut sig_ops = unified_self.sig_ops;
        sig_ops.extend(unified_other.sig_ops);
        match (unified_self.term, unified_other.term) {
            (MixedVCTerm::Var(v1), MixedVCTerm::Var(v2)) => {
                var_ops.insert(NumericOp::Shl);
                Ok(Self::wrap_var(var_ops, sig_ops, v1.shl(v2)?))
            }
            (MixedVCTerm::Sig(s1,_), MixedVCTerm::Sig(s2,_)) => {
                sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Shl));
                Ok(Self::wrap_sig(var_ops, sig_ops, s1.shl(s2)?))
            }
            (_,_) => {
                unreachable!("Unsupported shl type {}", self_sort)
            }
        }*/
    }

    fn shr(mut self, other: Self) -> Result<Self, SmtError> {
        let var_op = |mut var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, v1: V, v2: V| {
            var_ops.insert(NumericOp::Shr);
            Ok(Self::wrap_var(var_ops, sig_ops, aux_vars, v1.shr(v2)?))
        };
        let sig_op = |var_ops: HashSet<NumericOp>, mut sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, s1: S, s2: S| {
            sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Shr));
            Ok(Self::wrap_sig(var_ops, sig_ops, aux_vars, s1.shr(s2)?))
        };
        self.apply_numeric_op(other, var_op, sig_op)

        /*let (unified_self, unified_other) = self.match_terms(other)?;
        let self_sort = unified_self.sort();
        let mut var_ops = unified_self.var_ops;
        var_ops.extend(unified_other.var_ops);
        let mut sig_ops = unified_self.sig_ops;
        sig_ops.extend(unified_other.sig_ops);
        match (unified_self.term, unified_other.term) {
            (MixedVCTerm::Var(v1), MixedVCTerm::Var(v2)) => {
                var_ops.insert(NumericOp::Shr);
                Ok(Self::wrap_var(var_ops, sig_ops, v1.shr(v2)?))
            }
            (MixedVCTerm::Sig(s1,_), MixedVCTerm::Sig(s2,_)) => {
                sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Shr));
                Ok(Self::wrap_sig(var_ops, sig_ops, s1.shr(s2)?))
            }
            (_,_) => {
                unreachable!("Unsupported shr type {}", self_sort)
            }
        }*/
    }

    fn complement(mut self) -> Result<Self, SmtError> {
        if let MixedVCTerm::Sig(s, _) = self.term {
            self.sig_ops.insert(FiniteFieldOp::NumericOp(NumericOp::Complement));
            Ok(Self::wrap_sig(self.var_ops, self.sig_ops, self.aux_vars, s.complement()?))
        }
        else if let MixedVCTerm::Var(v) = self.term {
            self.var_ops.insert(NumericOp::Complement);
            Ok(Self::wrap_var(self.var_ops, self.sig_ops, self.aux_vars, v.complement()?))
        }
        else {
            Err(SmtError::IncorrectType("complement", "numeric", Some(self.sort())))
        }
    }

    fn is_quantified(&self) -> bool {
        match self.term() {
            Term::Forall(_, _) => { true }
            Term::Exists(_, _) => { true }
            _ => { false }
        }
    }

    fn get_quantifier(&self) -> Result<Quantifier, SmtError> {
        match self.term() {
            Term::Forall(_, _) => { Ok(Quantifier::Forall) }
            Term::Exists(_, _) => { Ok(Quantifier::Exists) }
            _ => { Err(SmtError::NotQuantified("get_quantifier", self.to_string())) }
        }
    }

    fn get_quantified_vars(&self) -> Result<Vec<String>, SmtError> {
        match self.term() {
            Term::Forall(v, t) => {
                Ok(v.iter().map(|var| var.0.0.clone()).collect::<Vec<String>>())
            }
            Term::Exists(v, t) => {
                Ok(v.iter().map(|var| var.0.0.clone()).collect::<Vec<String>>())
            }
            _ => { Err(SmtError::NotQuantified("get_quantified_vars", self.to_string())) }
        }
    }

    fn get_quantified_term(&self) -> Result<Self, SmtError> {
        let sort = self.sort();
        match self.term() {
            Term::Forall(v, t) => {
                let new_term = MixedVCTerm::<FF, V, S>::new(sort, t.deref().clone())?;
                Ok(Self::wrap(self.var_ops.clone(), self.sig_ops.clone(), self.aux_vars.clone(), new_term))
            }
            Term::Exists(v, t) => {
                let new_term = MixedVCTerm::<FF, V, S>::new(sort, t.to_owned().as_ref().clone())?;
                Ok(Self::wrap(self.var_ops.clone(), self.sig_ops.clone(), self.aux_vars.clone(), new_term))
            }
            _ => { Err(SmtError::NotQuantified("get_quantified_term", self.to_string())) }
        }
    }

    fn create_struct(struct_def: HashMap<String, Self>) -> Result<Self, SmtError> {
        let mut var_ops = HashSet::new();
        let mut sig_ops = HashSet::new();
        let mut sub_map = HashMap::new();
        let mut aux_vars = HashSet::new();

        for (name, term) in struct_def {
            var_ops.extend(term.var_ops);
            sig_ops.extend(term.sig_ops);
            sub_map.insert(name.clone(), term.term);
            aux_vars.extend(term.aux_vars);
        }

        Ok(Self {var_ops, sig_ops, aux_vars, term: MixedVCTerm::<FF, V, S>::wrap_struct(sub_map)?})
    }

    fn count_vars(&self) -> usize {
        let blacklist = HashSet::new();
        //Self::count_vars_in_term(self.term(), blacklist)
        let mut vars = HashSet::new();
        Self::get_vars_in_term(self.term(), blacklist, &mut vars);
        vars.len()
    }

    fn get_vars(&self) -> HashSet<Term> {
        let blacklist = HashSet::new();
        let mut vars = HashSet::new();
        Self::get_vars_in_term(self.term(), blacklist, &mut vars);
        vars
    }

    fn get_prime() -> BigInt {
        FF::prime()
    }

    fn create_fn_application(ref_fn: &UninterpretedFunction, args: Vec<Self>) -> Result<Self, SmtError> {
        let mut var_ops = HashSet::new();
        let mut sig_ops = HashSet::new();
        let mut aux_vars = HashSet::new();
        let mut terms = vec![];
        for arg in args {
            terms.push(arg.term().clone());
            var_ops.extend(arg.var_ops);
            sig_ops.extend(arg.sig_ops);
            aux_vars.extend(arg.aux_vars);
        }

        let fn_application = SmtUtils::fn_application(ref_fn.name.as_str(), terms);
        Ok(Self::wrap(var_ops, sig_ops, aux_vars, MixedVCTerm::new(ref_fn.ret.clone(), fn_application)?))
    }

    fn cast(self, to_sort: TermSort) -> Result<Self, SmtError> {
        /* For now we will trust that this is correct */
        let mixed_term = MixedVCTerm::new(to_sort, self.term.into())?;
        Ok(Self::wrap(self.var_ops, self.sig_ops, self.aux_vars, mixed_term))
    }
}

impl<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> VCVarTerm for LazyVCTerm<FF, V, S> {
    fn variable(sort: TermSort, name: &str) -> Result<Self, SmtError> {
        Ok(Self::wrap(HashSet::new(), HashSet::new(), HashSet::new(), MixedVCTerm::<FF,V,S>::variable(sort, name.into())?))
    }
}

impl<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> LazyTerm for LazyVCTerm<FF, V, S> {
    fn var_ops(&self) -> &HashSet<NumericOp> {
        &self.var_ops
    }

    fn sig_ops(&self) -> &HashSet<FiniteFieldOp> {
        &self.sig_ops
    }

    fn aux_vars(&self) -> &HashSet<AuxVarDef> {
        &self.aux_vars
    }
}

impl<FF: FiniteFieldDef, V: NumericTerm + Into<S>, S: FiniteFieldTypedTerm<FF> + From<V>> LazyVCTerm<FF, V, S> {
    fn apply_numeric_op<VO, SO>(mut self, other: Self, var_op: VO, sig_op: SO) -> Result<Self, SmtError>
    where
        VO: FnOnce(HashSet<NumericOp>, HashSet<FiniteFieldOp>, HashSet<AuxVarDef>, V, V) -> Result<Self, SmtError>,
        SO: FnOnce(HashSet<NumericOp>, HashSet<FiniteFieldOp>, HashSet<AuxVarDef>, S, S) -> Result<Self, SmtError>,
    {
        let (unified_self, unified_other) = self.match_terms(other)?;
        let self_sort = unified_self.sort();
        let mut var_ops = unified_self.var_ops;
        var_ops.extend(unified_other.var_ops);
        let mut sig_ops = unified_self.sig_ops;
        sig_ops.extend(unified_other.sig_ops);
        let mut aux_vars = unified_self.aux_vars;
        aux_vars.extend(unified_other.aux_vars);
        match (unified_self.term, unified_other.term) {
            (MixedVCTerm::Var(v1), MixedVCTerm::Var(v2)) => {
                var_op(var_ops, sig_ops, aux_vars, v1, v2)
            }
            (MixedVCTerm::Sig(s1,_), MixedVCTerm::Sig(s2,_)) => {
                sig_op(var_ops, sig_ops, aux_vars, s1, s2)
            }
            (_,_) => {
                unreachable!("Unsupported shr type {}", self_sort)
            }
        }
    }

    fn simplify(term: Term) -> Result<Term, SmtError> {
        match &term {
            Term::SpecConstant(_) => {
                Ok(term)
            }
            Term::Identifier(_) => {
                Ok(term)
            }
            Term::Application(name, args) => {
                let mut new_args = vec![];
                for arg in args {
                    new_args.push(Self::simplify(arg.clone())?);
                }

                if name.to_string().as_str() == "pow_i" {
                    assert_eq!(new_args.len(), 2, "pow_i must have 2 arguments");
                    let lhs = IntTerm::new(TermSort::Int, new_args[0].clone())?;
                    let rhs = IntTerm::new(TermSort::Int, new_args[1].clone())?;
                    Ok(lhs.pow(rhs)?.into())
                }
                else if name.to_string().as_str() == "mod" {
                    assert_eq!(new_args.len(), 2, "mod must have 2 arguments");
                    let lhs = IntTerm::new(TermSort::Int, new_args[0].clone())?;
                    let rhs = IntTerm::new(TermSort::Int, new_args[1].clone())?;
                    Ok(lhs.modulus(rhs)?.into())
                }
                else {
                    Ok(Term::Application(name.clone(), new_args))
                }
            }
            Term::Let(_, _) => {
                Ok(term)
            }
            Term::Forall(vars, quantified) => {
                let new_quantified = Self::simplify(quantified.as_ref().clone())?;
                Ok(Term::Forall(vars.clone(), Box::new(new_quantified)))
            }
            Term::Exists(vars, quantified) => {
                let new_quantified = Self::simplify(quantified.as_ref().clone())?;
                Ok(Term::Exists(vars.clone(), Box::new(new_quantified)))
            }
            Term::Match(_, _) => {
                Ok(term)
            }
            Term::Annotation(annotated, attributes) => {
                let new_annotated = Self::simplify(annotated.as_ref().clone())?;
                Ok(Term::Annotation(Box::new(new_annotated), attributes.clone()))
            }
        }
    }

    fn identifier_name(name: &QualIdentifier) -> &String {
        match name {
            QualIdentifier::Identifier(name) => {
                match name {
                    Identifier::Simple(s) => {
                        &s.0
                    }
                    Identifier::Indexed(s, _) => {
                        &s.0
                    }
                }
            }
            QualIdentifier::Sorted(name, _) => {
                match name {
                    Identifier::Simple(s) => {
                        &s.0
                    }
                    Identifier::Indexed(s, _) => {
                        &s.0
                    }
                }
            }
        }
    }

    fn contains_only_identifiers(self_term: &Term, var_identifiers: HashSet<Term>) -> bool {
        let mut worklist = vec![self_term];
        while !worklist.is_empty() {
            let cur = worklist.pop().unwrap();

            match cur {
                Term::Application(_, sub_terms) => {
                    for t in sub_terms {
                        worklist.push(t);
                    }
                }
                Term::Annotation(term, _) => {
                    worklist.push(term)
                }
                Term::Forall(q_vars, term) => {
                    let mut new_identifiers = var_identifiers.clone();
                    for v in q_vars {
                        new_identifiers.insert(Term::Identifier(QualIdentifier::Identifier(Identifier::Simple(v.0.clone()))));
                    }

                    if !Self::contains_only_identifiers(term, new_identifiers) {
                        return false;
                    }
                }
                Term::Exists(q_vars, term) => {
                    let mut new_identifiers = var_identifiers.clone();
                    for v in q_vars {
                        new_identifiers.insert(Term::Identifier(QualIdentifier::Identifier(Identifier::Simple(v.0.clone()))));
                    }

                    if !Self::contains_only_identifiers(term, new_identifiers) {
                        return false;
                    }
                }
                Term::Identifier(_) => {
                    if !var_identifiers.contains(cur) {
                        return false;
                    }
                }
                Term::Let(bindings, t) => {
                    let mut new_identifiers = var_identifiers.clone();
                    for v in bindings {
                        new_identifiers.insert(Term::Identifier(QualIdentifier::Identifier(Identifier::Simple(v.0.clone()))));
                    }

                    if !Self::contains_only_identifiers(t, new_identifiers) {
                        return false;
                    }
                }
                Term::SpecConstant(_) => {}
                Term::Match(t, _) => {
                    worklist.push(t)
                }
            }
        }

        true
    }

    fn count_vars_in_term(term: &Term, blacklist: HashSet<&String>) -> usize {
        let mut var_cnt = 0;
        let mut worklist = vec![term];
        while let Some(t) = worklist.pop() {
            match t {
                Term::SpecConstant(c) => {}
                Term::Identifier(name) => {
                    let name = Self::identifier_name(name);
                    if !blacklist.contains(name) {
                        var_cnt += 1;
                    }
                }
                Term::Application(name, args) => {
                    if args.len() == 0 {
                        let name = Self::identifier_name(name);
                        if !blacklist.contains(name) {
                            var_cnt += 1;
                        }
                    }
                    else {
                        for arg in args {
                            worklist.push(arg);
                        }
                    }
                }
                Term::Let(bindings, t) => {
                    let mut new_blacklist = blacklist.clone();
                    for v in bindings {
                        new_blacklist.insert(&v.0.0);
                    }

                    var_cnt += Self::count_vars_in_term(t, new_blacklist);
                }
                Term::Forall(q_vars, t) => {
                    let mut new_blacklist = blacklist.clone();
                    for v in q_vars {
                        new_blacklist.insert(&v.0.0);
                    }

                    var_cnt += Self::count_vars_in_term(t, new_blacklist);
                }
                Term::Exists(q_vars, t) => {
                    let mut new_blacklist = blacklist.clone();
                    for v in q_vars {
                        new_blacklist.insert(&v.0.0);
                    }

                    var_cnt += Self::count_vars_in_term(t, new_blacklist);
                }
                Term::Match(t, _) => {
                    worklist.push(t)
                }
                Term::Annotation(t, _) => {
                    worklist.push(t)
                }
            }
        }

        var_cnt
    }

    fn get_vars_in_term(term: &Term, blacklist: HashSet<&String>, vars: &mut HashSet<Term>) {
        let mut worklist = vec![term];
        while let Some(t) = worklist.pop() {
            match t {
                Term::SpecConstant(c) => {}
                Term::Identifier(name) => {
                    let name = Self::identifier_name(name);
                    if !blacklist.contains(name) {
                        vars.insert(t.clone());
                    }
                }
                Term::Application(name, args) => {
                    if args.len() == 0 {
                        let name = Self::identifier_name(name);
                        if !blacklist.contains(name) {
                            vars.insert(t.clone());
                        }
                    }
                    else {
                        for arg in args {
                            worklist.push(arg);
                        }
                    }
                }
                Term::Let(bindings, t) => {
                    let mut new_blacklist = blacklist.clone();
                    for v in bindings {
                        new_blacklist.insert(&v.0.0);
                    }

                    Self::get_vars_in_term(t, new_blacklist, vars);
                }
                Term::Forall(q_vars, t) => {
                    let mut new_blacklist = blacklist.clone();
                    for v in q_vars {
                        new_blacklist.insert(&v.0.0);
                    }

                    Self::get_vars_in_term(t, new_blacklist, vars);
                }
                Term::Exists(q_vars, t) => {
                    let mut new_blacklist = blacklist.clone();
                    for v in q_vars {
                        new_blacklist.insert(&v.0.0);
                    }

                    Self::get_vars_in_term(t, new_blacklist, vars);
                }
                Term::Match(t, _) => {
                    worklist.push(t)
                }
                Term::Annotation(t, _) => {
                    worklist.push(t)
                }
            }
        }
    }

    fn match_array_terms(self, other: Self) -> Result<(Self, Self), SmtError> {
        let (s1, s2) = MixedVCTerm::match_array_terms(self.term, other.term)?;
        Ok((Self::wrap(self.var_ops, self.sig_ops, self.aux_vars, s1), Self::wrap(other.var_ops, other.sig_ops, other.aux_vars, s2)))
    }

    fn match_scalar_terms(self, other: Self) -> Result<(Self, Self), SmtError> {
        let (s1, s2) = MixedVCTerm::match_scalar_terms(self.term, other.term)?;
        Ok((Self::wrap(self.var_ops, self.sig_ops, self.aux_vars, s1), Self::wrap(other.var_ops, other.sig_ops, other.aux_vars, s2)))
    }

    fn match_terms(self, other: Self) -> Result<(Self, Self), SmtError> {
        let (s1, s2) = MixedVCTerm::match_terms(self.term, other.term)?;
        Ok((Self::wrap(self.var_ops, self.sig_ops, self.aux_vars, s1), Self::wrap(other.var_ops, other.sig_ops, other.aux_vars, s2)))
    }

    fn wrap(var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, term: MixedVCTerm<FF, V, S>) -> Self {
        Self {
            var_ops,
            sig_ops,
            aux_vars,
            term
        }
    }

    fn wrap_sig(var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, t: S) -> Self {
        Self {
            var_ops,
            sig_ops,
            aux_vars,
            term: MixedVCTerm::<FF, V, S>::wrap_sig(t)
        }
    }
    fn wrap_var(var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, t: V) -> Self {
        Self {
            var_ops,
            sig_ops,
            aux_vars,
            term: MixedVCTerm::<FF, V, S>::wrap_var(t)
        }
    }
    fn wrap_arr(var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, t: ArrayTerm<V, MixedVCTerm<FF, V, S>>) -> Self {
        Self {
            var_ops,
            sig_ops,
            aux_vars,
            term: MixedVCTerm::<FF, V, S>::wrap_arr(t)
        }
    }
    fn wrap_bool(var_ops: HashSet<NumericOp>, sig_ops: HashSet<FiniteFieldOp>, aux_vars: HashSet<AuxVarDef>, t: BoolTerm) -> Self {
        Self {
            var_ops,
            sig_ops,
            aux_vars,
            term: MixedVCTerm::<FF, V, S>::wrap_bool(t)
        }
    }
}