use std::fmt::{Display, Formatter};
use std::marker::PhantomData;
use std::ops::{Add, Div, Mul, Neg, Sub};
use num_bigint_dig::BigInt;
use cfg::error::CFGError;
use cfg::expr::expression::Expression;
use cfg::finite_fields::FiniteFieldDef;
use crate::domains::interval::infinite_number::infinite_number::{InfiniteNumber, UncertainBool};

#[derive(Hash, PartialEq, Eq, Clone)]
pub enum InfiniteBigInt<F: FiniteFieldDef> {
    NegInfinity,
    Number(BigInt, PhantomData<F>),
    Infinity,
}

impl<F: FiniteFieldDef> Display for InfiniteBigInt<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NegInfinity => { write!(f, "-\u{221E}") }
            Self::Number(n, _) => { write!(f, "{}", n) }
            Self::Infinity => { write!(f, "\u{221E}") }
        }
    }
}

impl<F: FiniteFieldDef> From<BigInt> for InfiniteBigInt<F> {
    fn from(value: BigInt) -> Self {
        Self::number(value)
    }
}

impl<F: FiniteFieldDef> From<&BigInt> for InfiniteBigInt<F> {
    fn from(value: &BigInt) -> Self {
        Self::number(value.clone())
    }
}

impl<F: FiniteFieldDef> InfiniteNumber for InfiniteBigInt<F> {
    fn infinity() -> Self {
        Self::Infinity
    }

    fn neg_infinity() -> Self {
        Self::NegInfinity
    }

    fn to_expr(&self) -> Result<Expression, CFGError> {
        match self {
            InfiniteBigInt::NegInfinity => {
                Err(CFGError::UnsupportedExpr("Cannot convert negative infinity to an expression"))
            }
            InfiniteBigInt::Number(n, _) => {
                Ok(Expression::new_number(n.clone()))
            }
            InfiniteBigInt::Infinity => {
                Err(CFGError::UnsupportedExpr("Cannot convert infinity to an expression"))
            }
        }
    }

    fn to_expr_or_default(&self, default: &Expression) -> Expression {
        match self {
            InfiniteBigInt::NegInfinity => {
                default.clone()
            }
            InfiniteBigInt::Number(n, _) => {
                Expression::new_number(n.clone())
            }
            InfiniteBigInt::Infinity => {
                default.clone()
            }
        }
    }

    fn number(value: BigInt) -> Self {
        Self::Number(value, PhantomData::default())
    }

    fn is_infinity(&self) -> bool {
        match self {
            Self::Infinity => { true }
            _ => { false }
        }
    }

    fn is_neg_infinity(&self) -> bool {
        match self {
            Self::NegInfinity => { true }
            _ => { false }
        }
    }

    fn is_number(&self) -> bool {
        match self {
            Self::Number(_, _) => { true }
            _ => { false }
        }
    }

    fn expr_min(_expr: &Expression) -> Self {
        Self::NegInfinity
    }

    fn expr_max(_expr: &Expression) -> Self {
        Self::Infinity
    }

    fn min(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::NegInfinity, _) => {
                self.clone()
            }
            (_, Self::NegInfinity) => {
                other.clone()
            }
            (Self::Infinity, _) => {
                other.clone()
            }
            (_, Self::Infinity) => {
                self.clone()
            }
            (Self::Number(n1, _), Self::Number(n2, _)) => {
                if n1 < n2 { self.clone() } else { other.clone() }
            }
        }
    }

    fn max(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::NegInfinity, _) => {
                other.clone()
            }
            (_, Self::NegInfinity) => {
                self.clone()
            }
            (Self::Infinity, _) => {
                self.clone()
            }
            (_, Self::Infinity) => {
                other.clone()
            }
            (Self::Number(n1, _), Self::Number(n2, _)) => {
                if n1 > n2 { self.clone() } else { other.clone() }
            }
        }
    }

    fn add(&self, other: &Self) -> Self {
        self.numeric_binop(other, |n1, n2| n1.add(n2))
    }

    fn sub(&self, other: &Self) -> Self {
        self.numeric_binop(other, |n1, n2| n1.sub(n2))
    }

    fn mul(&self, other: &Self) -> Self {
        self.numeric_binop(other, |n1, n2| n1.mul(n2))
    }

    fn div(&self, other: &Self) -> Self {
        self.numeric_binop(other, |n1, n2| n1.div(n2))
    }

    fn pow(&self, other: &Self) -> Self {
        self.numeric_binop(other, |n1, n2| n1.modpow(n2, &F::prime()))
    }

    fn shr(&self, other: &Self) -> Self {
        let two: Self = BigInt::from(2).into();
        let rhs = two.pow(other);
        self.mul(&rhs)
    }

    fn shl(&self, other: &Self) -> Self {
        let two: Self = BigInt::from(2).into();
        let rhs = two.pow(other);
        self.div(&rhs)
    }

    fn lt(&self, other: &Self) -> UncertainBool {
        match (self, other) {
            (Self::NegInfinity, Self::NegInfinity) => {
                false.into()
            }
            (Self::NegInfinity, _) => {
                true.into()
            }
            (Self::Number(n1, _), Self::NegInfinity) => {
                false.into()
            }
            (Self::Number(n1, _), Self::Number(n2, _)) => {
                (n1 < n2).into()
            }
            (Self::Number(n1, _), Self::Infinity) => {
                true.into()
            }
            (Self::Infinity, _) => {
                false.into()
            }
        }
    }

    fn gt(&self, other: &Self) -> UncertainBool {
        match (self, other) {
            (Self::NegInfinity, _) => {
                false.into()
            }
            (Self::Number(n1, _), Self::NegInfinity) => {
                true.into()
            }
            (Self::Number(n1, _), Self::Number(n2, _)) => {
                (n1 > n2).into()
            }
            (Self::Number(n1, _), Self::Infinity) => {
                false.into()
            }
            (Self::Infinity, Self::Infinity) => {
                false.into()
            }
            (Self::Infinity, _) => {
                true.into()
            }
        }
    }

    fn maybe_eq(&self, other: &Self) -> UncertainBool {
        match (self, other) {
            (Self::NegInfinity, Self::NegInfinity) => {
                true.into()
            }
            (Self::Number(n1, _), Self::Number(n2, _)) => {
                (n1 == n2).into()
            }
            (Self::Infinity, Self::Infinity) => {
                true.into()
            }
            _ => {
                false.into()
            }
        }
    }

    /*
    unary ops
     */
    fn negate(&self) -> Self {
        match self {
            Self::NegInfinity => {
                Self::Infinity
            }
            Self::Number(n, _) => {
                n.neg().into()
            }
            Self::Infinity => {
                Self::NegInfinity
            }
        }
    }
}

impl<F: FiniteFieldDef> InfiniteBigInt<F> {
    fn numeric_binop(&self, other: &Self, op: fn(&BigInt, &BigInt) -> BigInt) -> Self {
        match (self, other) {
            (Self::NegInfinity, _) => {
                self.clone()
            }
            (Self::Infinity, _) => {
                self.clone()
            }
            (_, Self::NegInfinity) => {
                other.clone()
            }
            (_, Self::Infinity) => {
                other.clone()
            }
            (Self::Number(n1, _), Self::Number(n2, _)) => {
                Self::number(op(n1, n2))
            }
        }
    }
}