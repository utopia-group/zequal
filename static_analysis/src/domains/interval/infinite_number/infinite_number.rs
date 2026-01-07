use std::fmt::Display;
use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::{Add, Div, Mul, Sub};
use num_bigint_dig::BigInt;
use cfg::error::CFGError;
use cfg::expr::expression::Expression;

#[derive(Clone, Eq, PartialEq, Hash)]
pub enum UncertainBool {
    True,
    False,
    Unknown
}

impl From<bool> for UncertainBool {
    fn from(value: bool) -> Self {
        if value { UncertainBool::True } else { UncertainBool::False }
    }
}

impl UncertainBool {
    pub fn is_true(&self) -> bool {
        match self {
            UncertainBool::True => { true }
            _ => { false }
        }
    }

    pub fn is_false(&self) -> bool {
        match self {
            UncertainBool::False => { true }
            _ => { false }
        }
    }

    pub fn is_unknown(&self) -> bool {
        match self {
            UncertainBool::Unknown => { true }
            _ => { false }
        }
    }
}

pub trait InfiniteNumber: Display + From<BigInt> + Clone + PartialEq + Eq + Hash {
    fn infinity() -> Self;
    fn neg_infinity() -> Self;
    fn to_expr(&self) -> Result<Expression, CFGError>;
    fn to_expr_or_default(&self, default: &Expression) -> Expression;
    fn number(value: BigInt) -> Self;
    fn is_infinity(&self) -> bool;
    fn is_neg_infinity(&self) -> bool;
    fn is_number(&self) -> bool;
    fn expr_min(expr: &Expression) -> Self;
    fn expr_max(expr: &Expression) -> Self;
    fn min(&self, other: &Self) -> Self;
    fn max(&self, other: &Self) -> Self;
    fn add(&self, other: &Self) -> Self;
    fn sub(&self, other: &Self) -> Self;
    fn mul(&self, other: &Self) -> Self;
    fn div(&self, other: &Self) -> Self;
    fn pow(&self, other: &Self) -> Self;
    fn shr(&self, other: &Self) -> Self;
    fn shl(&self, other: &Self) -> Self;
    fn lt(&self, other: &Self) -> UncertainBool;
    fn gt(&self, other: &Self) -> UncertainBool;
    fn maybe_eq(&self, other: &Self) -> UncertainBool;
    fn negate(&self) -> Self;
}