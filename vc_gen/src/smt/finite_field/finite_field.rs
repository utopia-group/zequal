use std::str::FromStr;
use num_bigint_dig::BigInt;
use smtlib_lowlevel::ast::{Term};
use cfg::finite_fields::FiniteFieldDef;
use crate::smt::error::SmtError;
use crate::smt::smt::{NumericOp, NumericTerm, SmtUtils, UninterpretedFunction};
pub trait TermSize<FF: FiniteFieldDef>: Clone + PartialEq + Eq {
    fn as_term() -> Term {
        SmtUtils::constant(&*Self::size().to_string())
    }

    fn size() -> BigInt {
        FF::prime()
    }
}

#[derive(Clone, Eq, Hash, PartialEq)]
pub enum FiniteFieldOp {
    NumericOp(NumericOp),
    Inverse
}

pub trait FiniteFieldTypedTerm<FF: FiniteFieldDef>: NumericTerm + TermSize<FF> {
    fn get_ff_op_axiom(op: &FiniteFieldOp) -> Option<UninterpretedFunction>;
    fn inverse(self) -> Result<Self, SmtError>;
}