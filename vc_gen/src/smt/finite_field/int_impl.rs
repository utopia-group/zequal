use std::marker::PhantomData;
use std::str::FromStr;
use num_bigint_dig::BigInt;
use num_traits::{One, Pow, Signed, ToPrimitive, Zero};
use smtlib_lowlevel::ast::{SpecConstant, Term};
use cfg::finite_fields::FiniteFieldDef;
use crate::smt::bool::BoolTerm;
use crate::smt::error::SmtError;
use crate::smt::finite_field::finite_field::{FiniteFieldOp, FiniteFieldTypedTerm, TermSize};
use crate::smt::int::{IntTerm};
use crate::smt::smt::{BuildableTerm, CoreTerm, NumericOp, NumericTerm, Quantifier, SmtUtils, StaticTypedTerm, TermSort, TypedTerm, UninterpretedFunction};

#[derive(Clone, Eq, PartialEq)]
pub enum IntFiniteFieldTerm<FF:FiniteFieldDef> {
    DelayedMod(Term, PhantomData<FF>),
    NoMod(Term)
}

impl<FF:FiniteFieldDef> From<IntTerm> for IntFiniteFieldTerm<FF> {
    fn from(value: IntTerm) -> Self {
        let res = Self::new(TermSort::IntFiniteField(FF::prime()), value.into());
        if let Ok(t) = res {
            t
        }
        else {
            unreachable!("Could not convert from int to int finite field")
        }
        //Self::new_delayed_unchecked(value.into())
    }
}

impl<FF:FiniteFieldDef> Into<Term> for IntFiniteFieldTerm<FF> {
    fn into(self) -> Term {
        match self {
            IntFiniteFieldTerm::DelayedMod(t, _) => {
                SmtUtils::fn_application("mod", vec![t, Self::as_term()])
            }
            IntFiniteFieldTerm::NoMod(t) => {
                t
            }
        }
    }
}

impl<FF:FiniteFieldDef> TypedTerm for IntFiniteFieldTerm<FF> {
    fn term(&self) -> &Term {
        match self {
            IntFiniteFieldTerm::DelayedMod(t, _) => { &t }
            IntFiniteFieldTerm::NoMod(t) => { &t }
        }
    }

    fn term_mut(&mut self) -> &mut Term {
        match self {
            IntFiniteFieldTerm::DelayedMod(t, _) => { t }
            IntFiniteFieldTerm::NoMod(t) => { t }
        }
    }

    fn sort(&self) -> TermSort {
        Self::underlying_sort()
    }
}

impl<FF:FiniteFieldDef> BuildableTerm for IntFiniteFieldTerm<FF> {
    fn new(sort: TermSort, term: Term) -> Result<Self, SmtError> {
        if sort != TermSort::IntFiniteField(Self::size()) {
            return Err(SmtError::IncorrectSort("IntFiniteField", TermSort::IntFiniteField(Self::size()), sort))
        }
        match &term {
            Term::SpecConstant(c) => {
                match c {
                    SpecConstant::Numeral(n) => {
                        Ok((&BigInt::from_str(&n.0).map_err(|_| SmtError::CannotParseInt(n.0.clone()))?).into())
                    }
                    SpecConstant::Decimal(d) => {
                        Ok((&BigInt::from_str(&d.0).map_err(|_| SmtError::CannotParseInt(d.0.clone()))?).into())
                    }
                    SpecConstant::String(s) => {
                        Ok((&BigInt::from_str(s).map_err(|_| SmtError::CannotParseInt(s.clone()))?).into())
                    }
                    _ => { Ok(Self::new_delayed_unchecked(term)) }
                }
            }
            Term::Application(app, ..) => {
                let fn_name = app.to_string();
                if fn_name == "select" {
                    Ok(Self::new_nomod_unchecked(term))
                }
                else {
                    Ok(Self::new_delayed_unchecked(term))
                }
            }
            Term::Identifier(_) => {
                Ok(Self::new_nomod_unchecked(term))
            }
            _ => { Ok(Self::new_delayed_unchecked(term)) }
        }
    }
}

impl<FF:FiniteFieldDef> From<&BigInt> for IntFiniteFieldTerm<FF> {
    fn from(value: &BigInt) -> Self {
        if value.is_negative() {
            println!("{value}");
        }
        // Eagerly calculate mod
        let mod_val = value.modpow(&BigInt::one(), &Self::size());
        let mod_str = mod_val.to_string();
        Self::new_nomod_unchecked(SmtUtils::constant(&*mod_str))
    }
}

impl<FF:FiniteFieldDef> CoreTerm for IntFiniteFieldTerm<FF> {}

impl<FF:FiniteFieldDef> StaticTypedTerm for IntFiniteFieldTerm<FF> {
    fn underlying_sort() -> TermSort {
        TermSort::IntFiniteField(Self::size())
    }
    fn variable(name: &str) -> Self {
        Self::new_nomod_unchecked(SmtUtils::variable(name))
    }
}

impl<FF:FiniteFieldDef> NumericTerm for IntFiniteFieldTerm<FF> {
    fn get_numeric_op_axiom(op: &NumericOp) -> Option<UninterpretedFunction> {
        IntTerm::get_numeric_op_axiom(op)
    }

    fn add(self, other: Self) -> Result<Self, SmtError> {
        Ok(Self::new_delayed_unchecked(SmtUtils::fn_application("+", vec![self.delayed_term(), other.delayed_term()])))
    }
    fn sub(self, other: Self) -> Result<Self, SmtError> {
        Ok(Self::new_delayed_unchecked(SmtUtils::fn_application("-", vec![self.delayed_term(), other.delayed_term()])))
    }
    fn mul(self, other: Self) -> Result<Self, SmtError> {
        Ok(Self::new_delayed_unchecked(SmtUtils::fn_application("*", vec![self.delayed_term(), other.delayed_term()])))
    }
    fn div(self, other: Self) -> Result<Self, SmtError> {
        Ok(Self::new_delayed_unchecked(SmtUtils::fn_application("div", vec![self.delayed_term(), other.delayed_term()])))
    }

    fn pow(self, other: Self) -> Result<Self, SmtError> {
        let lhs = self.delayed_term();
        let rhs = other.delayed_term();
        match (&lhs, &rhs) {
            (Term::SpecConstant(c1), Term::SpecConstant(c2)) => {
                let lhs_val = BigInt::from_str(c1.to_string().as_str()).unwrap();
                let rhs_val = BigInt::from_str(c2.to_string().as_str()).unwrap();
                Ok(Self::new_nomod_unchecked(SmtUtils::constant(lhs_val.modpow(&rhs_val, &Self::size()).to_string().as_str())))
            }
            (_, _) => {
                Ok(Self::new_delayed_unchecked(SmtUtils::fn_application("pow_i", vec![lhs, rhs])))
            }
        }
    }

    fn modulus(self, other: Self) -> Result<Self, SmtError> {
        Ok(Self::new_delayed_unchecked(SmtUtils::fn_application("mod", vec![self.delayed_term(), other.delayed_term()])))
    }
    fn negate(self) -> Result<Self, SmtError> {
        Ok(Self::new_delayed_unchecked(SmtUtils::fn_application("-", vec![self.delayed_term()])))
    }

    fn shr(self, other: Self) -> Result<Self, SmtError> {
        let two_term = Self::from(&BigInt::from(2));
        self.div(two_term.pow(other)?)
    }

    fn shl(self, other: Self) -> Result<Self, SmtError> {
        let two_term = Self::from(&BigInt::from(2));
        self.mul(two_term.pow(other)?)
    }

    fn bit_and(self, other: Self) -> Result<Self, SmtError> {
        Ok(Self::new_delayed_unchecked(SmtUtils::fn_application("and_i", vec![self.delayed_term(), other.delayed_term()])))
    }

    fn bit_or(self, other: Self) -> Result<Self, SmtError> {
        Ok(Self::new_delayed_unchecked(SmtUtils::fn_application("or_i", vec![self.delayed_term(), other.delayed_term()])))
    }

    fn bit_xor(self, other: Self) -> Result<Self, SmtError> {
        Ok(Self::new_delayed_unchecked(SmtUtils::fn_application("xor_i", vec![self.delayed_term(), other.delayed_term()])))
    }

    fn complement(self) -> Result<Self, SmtError> {
        Ok(Self::new_delayed_unchecked(SmtUtils::fn_application("complement_i", vec![self.delayed_term()])))
    }
}

impl<FF: FiniteFieldDef> TermSize<FF> for IntFiniteFieldTerm<FF> {}

impl<FF:FiniteFieldDef> FiniteFieldTypedTerm<FF> for IntFiniteFieldTerm<FF> {
    fn get_ff_op_axiom(op: &FiniteFieldOp) -> Option<UninterpretedFunction> {
        match op {
            FiniteFieldOp::NumericOp(op) => {
                Self::get_numeric_op_axiom(op)
            }
            FiniteFieldOp::Inverse => {
                let self_sort = Self::underlying_sort();
                let name = String::from("x");
                let var = Self::variable(&name);
                let one: Self = (&BigInt::one()).into();
                let prime_term = Self::new_nomod_unchecked(Self::as_term());
                let zero_term: IntFiniteFieldTerm<FF> = (&BigInt::zero()).into();
                let inv_def = var.clone().mul(var.clone().inverse().ok()?).ok()?.eq(one.clone()).ok()?;
                let lower_bound = var.clone().inverse().ok()?.gt(zero_term.clone()).ok()?;
                let upper_bound = var.clone().inverse().ok()?.lt(prime_term.clone()).ok()?;
                let zero_cond = var.clone().eq(zero_term.clone()).ok()?.and(var.inverse().ok()?.eq(zero_term).ok()?);
                /*let under_bound = var.clone().lt(one).ok()?;
                let above_bound = var.clone().gte(prime_term).ok()?;*/
                let inv_behavior = BoolTerm::and_all(vec![/*inv_def,*/ lower_bound, upper_bound]);
                //let axiom_term = BoolTerm::or_all(vec![under_bound, above_bound, inv_behavior]);
                let axiom_term = BoolTerm::or_all(vec![zero_cond, inv_behavior]);
                let axiom = axiom_term.quantify(Quantifier::Forall, vec![(name, Self::underlying_sort())]).ok()?;
                Some(UninterpretedFunction {
                    name: String::from("inv_i"),
                    args: vec![self_sort.clone()],
                    ret: self_sort,
                    axioms: vec![axiom]
                })
            }
        }
    }

    fn inverse(self) -> Result<Self, SmtError> {
        Ok(Self::new_nomod_unchecked(SmtUtils::fn_application("inv_i", vec![self.into()])))
    }
}

impl<FF:FiniteFieldDef> IntFiniteFieldTerm<FF> {
    fn new_delayed_unchecked(term: Term) -> Self {
        IntFiniteFieldTerm::DelayedMod(term, Default::default())
        //IntFiniteFieldTerm { term, phantom: Default::default() }
    }

    fn new_nomod_unchecked(term: Term) -> Self {
        IntFiniteFieldTerm::NoMod(term)
    }

    fn delayed_term(self) -> Term {
        match self {
            IntFiniteFieldTerm::DelayedMod(t, _) => { t }
            IntFiniteFieldTerm::NoMod(t) => { t }
        }
    }
}
