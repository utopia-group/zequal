use std::marker::PhantomData;
use std::ops::Sub;
use num_bigint_dig::BigInt;
use num_traits::One;
use smtlib_lowlevel::ast::{Term};
use cfg::finite_fields::FiniteFieldDef;
use crate::smt::bool::BoolTerm;
use crate::smt::error::SmtError;
use crate::smt::finite_field::finite_field::{FiniteFieldOp, FiniteFieldTypedTerm, TermSize};
use crate::smt::smt::{BuildableTerm, CoreTerm, NumericOp, NumericTerm, Quantifier, SmtUtils, StaticTypedTerm, TermSort, TypedTerm, UninterpretedFunction};

#[derive(Clone, Eq, PartialEq)]
pub struct FiniteFieldTerm<FF:FiniteFieldDef> {
    term: Term,
    phantom: PhantomData<FF>
}

impl<FF:FiniteFieldDef> Into<Term> for FiniteFieldTerm<FF> {
    fn into(self) -> Term {
        self.term
    }
}

impl<FF:FiniteFieldDef> TypedTerm for FiniteFieldTerm<FF> {
    fn term(&self) -> &Term {
        &self.term
    }

    fn term_mut(&mut self) -> &mut Term {
        &mut self.term
    }

    fn sort(&self) -> TermSort {
        Self::underlying_sort()
    }
}

impl<FF:FiniteFieldDef> BuildableTerm for FiniteFieldTerm<FF> {
    fn new(sort: TermSort, term: Term) -> Result<Self, SmtError> {
        if sort != TermSort::FiniteField(FF::prime()) {
            return Err(SmtError::IncorrectSort("FiniteFieldTerm", TermSort::FiniteField(FF::prime()), sort))
        }
        Ok(Self::new_unchecked(term))
    }
}

impl<FF:FiniteFieldDef> From<&BigInt> for FiniteFieldTerm<FF> {
    fn from(value: &BigInt) -> Self {
        let str = format!("(as ff{} {})", value.to_string(), Self::underlying_sort().sort().to_string());
        Self::new_unchecked(SmtUtils::constant(&*str))
    }
}

impl<FF:FiniteFieldDef> CoreTerm for FiniteFieldTerm<FF> {}

impl<FF:FiniteFieldDef> StaticTypedTerm for FiniteFieldTerm<FF> {
    fn variable(name: &str) -> Self {
        Self::new_unchecked(SmtUtils::variable(name))
    }
    fn underlying_sort() -> TermSort {
        TermSort::FiniteField(FF::prime())
    }
}

impl<FF:FiniteFieldDef> NumericTerm for FiniteFieldTerm<FF> {
    fn get_numeric_op_axiom(op: &NumericOp) -> Option<UninterpretedFunction> {
        match op {
            NumericOp::Add => { None }
            NumericOp::Sub => { None }
            NumericOp::Mul => { None }
            NumericOp::Div => {
                let self_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("ff.div"),
                    args: vec![self_sort.clone(), self_sort.clone()],
                    ret: self_sort,
                    axioms: vec![],
                })
            }
            NumericOp::Mod => {
                let self_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("ff.mod"),
                    args: vec![self_sort.clone(), self_sort.clone()],
                    ret: self_sort,
                    axioms: vec![],
                })
            }
            NumericOp::Negate => { None }
            NumericOp::Shl => {
                Self::get_numeric_op_axiom(&NumericOp::Pow)
                /*let self_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("ff.shl"),
                    args: vec![self_sort.clone(), self_sort.clone()],
                    ret: self_sort,
                    axioms: vec![],
                })*/
            }
            NumericOp::Shr => {
                Self::get_numeric_op_axiom(&NumericOp::Pow)
                /*let self_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("ff.shr"),
                    args: vec![self_sort.clone(), self_sort.clone()],
                    ret: self_sort,
                    axioms: vec![],
                })*/
            }
            NumericOp::BitAnd => {
                let self_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("ff.and"),
                    args: vec![self_sort.clone(), self_sort.clone()],
                    ret: self_sort,
                    axioms: vec![],
                })
            }
            NumericOp::BitOr => {
                let self_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("ff.or"),
                    args: vec![self_sort.clone(), self_sort.clone()],
                    ret: self_sort,
                    axioms: vec![],
                })
            }
            NumericOp::Complement => {
                let self_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("ff.complement"),
                    args: vec![self_sort.clone()],
                    ret: self_sort,
                    axioms: vec![],
                })
            }
            NumericOp::Gt => {
                let self_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("ff.gt"),
                    args: vec![self_sort.clone(), self_sort],
                    ret: BoolTerm::underlying_sort(),
                    axioms: vec![],
                })
            }
            NumericOp::Gte => {
                let self_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("ff.gte"),
                    args: vec![self_sort.clone(), self_sort],
                    ret: BoolTerm::underlying_sort(),
                    axioms: vec![],
                })
            }
            NumericOp::Lt => {
                let self_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("ff.lt"),
                    args: vec![self_sort.clone(), self_sort],
                    ret: BoolTerm::underlying_sort(),
                    axioms: vec![],
                })
            }
            NumericOp::Lte => {
                let self_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("ff.lte"),
                    args: vec![self_sort.clone(), self_sort],
                    ret: BoolTerm::underlying_sort(),
                    axioms: vec![],
                })
            }
            NumericOp::Pow => {
                let self_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("ff.pow"),
                    args: vec![self_sort.clone(), self_sort.clone()],
                    ret: self_sort,
                    axioms: vec![],
                })
            }
            NumericOp::BitXor => {
                let self_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("ff.xor"),
                    args: vec![self_sort.clone(), self_sort.clone()],
                    ret: self_sort,
                    axioms: vec![],
                })
            }
        }
    }

    fn add(self, other: Self) -> Result<Self, SmtError> {
        Ok(Self::new_unchecked(SmtUtils::fn_application("ff.add", vec![self.term, other.term])))
    }
    fn sub(self, other: Self) -> Result<Self, SmtError> {
        self.add(other.mul((&FF::prime().sub(BigInt::one())).into())?)
    }
    fn mul(self, other: Self) -> Result<Self, SmtError> {
        Ok(Self::new_unchecked(SmtUtils::fn_application("ff.mul", vec![self.term, other.term])))
    }
    fn div(self, other: Self) -> Result<Self, SmtError> {
        Ok(Self::new_unchecked(SmtUtils::fn_application("ff.div", vec![self.into(), other.into()])))
    }

    fn pow(self, other: Self) -> Result<Self, SmtError> {
        Ok(Self::new_unchecked(SmtUtils::fn_application("ff.pow", vec![self.into(), other.into()])))
    }

    fn modulus(self, other: Self) -> Result<Self, SmtError> {
        Ok(Self::new_unchecked(SmtUtils::fn_application("ff.mod", vec![self.into(), other.into()])))
    }
    fn negate(self) -> Result<Self, SmtError> {
        self.mul(<&BigInt as Into<Self>>::into(&FF::prime().sub(BigInt::one())))
    }
    fn gt(self, other: Self) -> Result<BoolTerm, SmtError> {
        BoolTerm::new(TermSort::Bool, SmtUtils::fn_application("ff.gt", vec![self.into(), other.into()]))
    }
    fn gte(self, other: Self) -> Result<BoolTerm, SmtError> {
        BoolTerm::new(TermSort::Bool, SmtUtils::fn_application("ff.gte", vec![self.into(), other.into()]))
    }
    fn lt(self, other: Self) -> Result<BoolTerm, SmtError> {
        BoolTerm::new(TermSort::Bool, SmtUtils::fn_application("ff.lt", vec![self.into(), other.into()]))
    }
    fn lte(self, other: Self) -> Result<BoolTerm, SmtError> {
        BoolTerm::new(TermSort::Bool, SmtUtils::fn_application("ff.lte", vec![self.into(), other.into()]))
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
        Ok(Self::new_unchecked(SmtUtils::fn_application("ff.and", vec![self.into(), other.into()])))
    }

    fn bit_or(self, other: Self) -> Result<Self, SmtError> {
        Ok(Self::new_unchecked(SmtUtils::fn_application("ff.or", vec![self.into(), other.into()])))
    }

    fn bit_xor(self, other: Self) -> Result<Self, SmtError> {
        Ok(Self::new_unchecked(SmtUtils::fn_application("ff.xor", vec![self.into(), other.into()])))
    }

    fn complement(self) -> Result<Self, SmtError> {
        Ok(Self::new_unchecked(SmtUtils::fn_application("ff.complement", vec![self.into()])))
    }
}

impl<FF: FiniteFieldDef> TermSize<FF> for FiniteFieldTerm<FF> {}

impl<FF:FiniteFieldDef> FiniteFieldTypedTerm<FF> for FiniteFieldTerm<FF> {
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
                let axiom_term = var.clone().mul(var.inverse().ok()?).ok()?.eq(one).ok()?;
                let axiom = axiom_term.quantify(Quantifier::Forall, vec![(name, Self::underlying_sort())]).ok()?;
                Some(UninterpretedFunction {
                    name: String::from("ff.inv"),
                    args: vec![self_sort.clone()],
                    ret: self_sort,
                    axioms: vec![axiom],
                })
            }
        }
    }

    fn inverse(self) -> Result<Self, SmtError> {
        Ok(Self::new_unchecked(SmtUtils::fn_application("ff.inv", vec![self.term])))
    }
}

impl<FF:FiniteFieldDef> FiniteFieldTerm<FF> {
    fn new_unchecked(term: Term) -> Self {
        FiniteFieldTerm { term, phantom: Default::default() }
    }
}