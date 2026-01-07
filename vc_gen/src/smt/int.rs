use std::ops::Neg;
use std::str::FromStr;
use num_bigint_dig::BigInt;
use num_traits::{One, Pow, Signed, ToPrimitive};
use smtlib_lowlevel::ast::{Term};
use crate::smt::error::SmtError;
use crate::smt::smt::{BuildableTerm, CoreTerm, NumericOp, NumericTerm, SmtUtils, StaticTypedTerm, TermSort, TypedTerm, UninterpretedFunction};

pub struct IntTermSort {}

#[derive(Clone, Eq, PartialEq)]
pub struct IntTerm {
    term: Term
}

impl Into<Term> for IntTerm {
    fn into(self) -> Term {
        self.term
    }
}

impl From<&BigInt> for IntTerm {
    fn from(value: &BigInt) -> Self {
        if value.is_negative() {
            let neg_const = Self::new_unchecked(SmtUtils::constant(&*value.neg().to_string()));
            Self::negate(neg_const).unwrap()
        }
        else {
            Self::new_unchecked(SmtUtils::constant(&*value.to_string()))
        }
    }
}

impl TypedTerm for IntTerm {
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

impl BuildableTerm for IntTerm {
    fn new(sort: TermSort, term: Term) -> Result<Self, SmtError> {
        if sort != TermSort::Int {
            return Err(SmtError::IncorrectSort("IntTerm", TermSort::Int, sort))
        }
        Ok(Self::new_unchecked(term))
    }
}

impl CoreTerm for IntTerm {}

impl StaticTypedTerm for IntTerm {
    fn variable(name: &str) -> Self {
        Self::new_unchecked(SmtUtils::variable(name))
    }
    fn underlying_sort() -> TermSort {
        TermSort::Int
    }
}

impl NumericTerm for IntTerm {
    fn get_numeric_op_axiom(op: &NumericOp) -> Option<UninterpretedFunction> {
        match op {
            NumericOp::Add => { None }
            NumericOp::Sub => { None }
            NumericOp::Mul => { None }
            NumericOp::Div => { None }
            NumericOp::Mod => { None }
            NumericOp::Negate => { None }
            NumericOp::Shl => {
                Self::get_numeric_op_axiom(&NumericOp::Pow)
                /*let int_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("shl_i"),
                    args: vec![int_sort.clone(), int_sort.clone()],
                    ret: int_sort,
                    axioms: vec![],
                })*/
            }
            NumericOp::Shr => {
                Self::get_numeric_op_axiom(&NumericOp::Pow)
                /*let int_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("shr_i"),
                    args: vec![int_sort.clone(), int_sort.clone()],
                    ret: int_sort,
                    axioms: vec![],
                })*/
            }
            NumericOp::BitAnd => {
                let int_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("and_i"),
                    args: vec![int_sort.clone(), int_sort.clone()],
                    ret: int_sort,
                    axioms: vec![],
                })
            }
            NumericOp::BitOr => {
                let int_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("or_i"),
                    args: vec![int_sort.clone(), int_sort.clone()],
                    ret: int_sort,
                    axioms: vec![],
                })
            }
            NumericOp::Complement => {
                let int_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("complement_i"),
                    args: vec![int_sort.clone()],
                    ret: int_sort,
                    axioms: vec![],
                })
            }
            NumericOp::Gt => { None }
            NumericOp::Gte => { None }
            NumericOp::Lt => { None }
            NumericOp::Lte => { None }
            NumericOp::Pow => {
                let int_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("pow_i"),
                    args: vec![int_sort.clone(), int_sort.clone()],
                    ret: int_sort,
                    axioms: vec![],
                })
            }
            NumericOp::BitXor => {
                let int_sort = Self::underlying_sort();
                Some(UninterpretedFunction {
                    name: String::from("xor_i"),
                    args: vec![int_sort.clone(), int_sort.clone()],
                    ret: int_sort,
                    axioms: vec![],
                })
            }
        }
    }

    fn pow(self, other: Self) -> Result<Self, SmtError> {
        let sort = self.sort();
        let lhs = self.into();
        let rhs = other.into();
        match (&lhs, &rhs) {
            (Term::SpecConstant(c1), Term::SpecConstant(c2)) => {
                let lhs_val = BigInt::from_str(c1.to_string().as_str()).unwrap();
                let rhs_val = BigInt::from_str(c2.to_string().as_str()).unwrap();
                let rhs_usize_opt = rhs_val.to_usize();
                match rhs_usize_opt {
                    None => {
                        panic!("constant {} is too big to evaluate", rhs_val);
                    }
                    Some(rhs_usize) => {
                        Self::new(sort, SmtUtils::constant(lhs_val.pow(&rhs_usize).to_string().as_str()))
                    }
                }
            }
            (_, _) => {
                Self::new(sort, SmtUtils::fn_application("pow_i", vec![lhs, rhs]))
            }
        }
    }

    fn modulus(self, other: Self) -> Result<Self, SmtError> {
        let sort = self.sort();
        let lhs = self.into();
        let rhs = other.into();
        match (&lhs, &rhs) {
            (Term::SpecConstant(c1), Term::SpecConstant(c2)) => {
                let lhs_val = BigInt::from_str(c1.to_string().as_str()).unwrap();
                let rhs_val = BigInt::from_str(c2.to_string().as_str()).unwrap();
                Self::new(sort, SmtUtils::constant(lhs_val.modpow(&BigInt::one(), &rhs_val).to_string().as_str()))
            }
            (_, _) => {
                Self::new(sort, SmtUtils::fn_application("mod", vec![lhs, rhs]))
            }
        }

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
        Self::new(self.sort(), SmtUtils::fn_application("and_i", vec![self.into(), other.into()]))
    }

    fn bit_or(self, other: Self) -> Result<Self, SmtError> {
        Self::new(self.sort(), SmtUtils::fn_application("or_i", vec![self.into(), other.into()]))
    }

    fn bit_xor(self, other: Self) -> Result<Self, SmtError> {
        Self::new(self.sort(), SmtUtils::fn_application("xor_i", vec![self.into(), other.into()]))
    }

    fn complement(self) -> Result<Self, SmtError> {
        Self::new(self.sort(), SmtUtils::fn_application("complement_i", vec![self.into()]))
    }
}

impl IntTerm {
    fn new_unchecked(term: Term) -> Self {
        IntTerm { term }
    }
    pub fn add_all(terms: Vec<Self>) -> Self {
        Self::new_unchecked(SmtUtils::fn_application("+", terms.into_iter().map(|t| t.term).collect()))
    }
}
