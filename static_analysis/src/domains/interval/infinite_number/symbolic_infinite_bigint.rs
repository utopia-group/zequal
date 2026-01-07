use std::fmt::{Display, Formatter};
use std::marker::PhantomData;
use std::ops::{Add, Div, Mul, Neg, Sub};
use num_bigint_dig::BigInt;
use cfg::error::CFGError;
use cfg::expr::binop::BinaryOperator;
use cfg::expr::expression::Expression;
use cfg::expr::unop::UnaryOperator;
use cfg::finite_fields::FiniteFieldDef;
use crate::domains::interval::infinite_number::infinite_number::{InfiniteNumber, UncertainBool};

#[derive(Hash, PartialEq, Eq, Clone)]
pub enum SymbolicInfiniteBigInt<F: FiniteFieldDef> {
    NegInfinity,
    Number(BigInt, PhantomData<F>),
    Symbol(Expression),
    Infinity
}

impl<F: FiniteFieldDef> Display for SymbolicInfiniteBigInt<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NegInfinity => { write!(f, "-\u{221E}") }
            Self::Number(n, _) => { write!(f, "{}", n) }
            Self::Symbol(e) => { write!(f, "{}", e) }
            Self::Infinity => { write!(f, "\u{221E}") }
        }
    }
}

impl<F: FiniteFieldDef> From<BigInt> for SymbolicInfiniteBigInt<F> {
    fn from(value: BigInt) -> Self {
        Self::number(value)
    }
}

impl<F: FiniteFieldDef> From<&BigInt> for SymbolicInfiniteBigInt<F> {
    fn from(value: &BigInt) -> Self {
        Self::number(value.clone())
    }
}

impl<F: FiniteFieldDef> From<Expression> for SymbolicInfiniteBigInt<F> {
    fn from(value: Expression) -> Self {
        Self::symbol(value)
    }
}

impl<F: FiniteFieldDef> From<&Expression> for SymbolicInfiniteBigInt<F> {
    fn from(value: &Expression) -> Self {
        Self::symbol(value.clone())
    }
}

impl<F: FiniteFieldDef> InfiniteNumber for SymbolicInfiniteBigInt<F> {
    fn infinity() -> Self {
        Self::Infinity
    }

    fn neg_infinity() -> Self {
        Self::NegInfinity
    }

    fn to_expr(&self) -> Result<Expression, CFGError> {
        match self {
            SymbolicInfiniteBigInt::NegInfinity => {
                Err(CFGError::UnsupportedExpr("Cannot convert negative infinity to an expression"))
            }
            SymbolicInfiniteBigInt::Number(n, _) => {
                Ok(Expression::new_number(n.clone()))
            }
            SymbolicInfiniteBigInt::Symbol(expr) => {
                Ok(expr.clone())
            }
            SymbolicInfiniteBigInt::Infinity => {
                Err(CFGError::UnsupportedExpr("Cannot convert infinity to an expression"))
            }
        }
    }

    fn to_expr_or_default(&self, default: &Expression) -> Expression {
        match self {
            SymbolicInfiniteBigInt::NegInfinity => {
                default.clone()
            }
            SymbolicInfiniteBigInt::Number(n, _) => {
                Expression::new_number(n.clone())
            }
            SymbolicInfiniteBigInt::Symbol(expr) => {
                expr.clone()
            }
            SymbolicInfiniteBigInt::Infinity => {
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

    fn expr_min(expr: &Expression) -> Self {
        Self::symbol(expr.clone())
    }

    fn expr_max(expr: &Expression) -> Self {
        Self::symbol(expr.clone())
    }

    fn min(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::NegInfinity, _) => {
                Self::NegInfinity
            }
            (_, Self::NegInfinity) => {
                Self::NegInfinity
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
            (Self::Number(n1, _), Self::Symbol(s2)) => {
                let n1_expr = Expression::new_number(n1.clone());
                let check = Expression::new_binop(Box::new(n1_expr.clone()), BinaryOperator::Lt, Box::new(s2.clone()));
                let min_check = Expression::new_ternary(Box::new(check), Box::new(n1_expr), Box::new(s2.clone()));
                min_check.into()
            }
            (Self::Symbol(s1), Self::Number(n2, _)) => {
                let n2_expr = Expression::new_number(n2.clone());
                let check = Expression::new_binop(Box::new(s1.clone()), BinaryOperator::Lt, Box::new(n2_expr.clone()));
                let min_check = Expression::new_ternary(Box::new(check), Box::new(s1.clone()), Box::new(n2_expr));
                min_check.into()
            }
            (Self::Symbol(s1), Self::Symbol(s2)) => {
                if s1 == s2 { self.clone() } else { Self::NegInfinity }
            }
        }
    }

    fn max(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Infinity, _) => {
                Self::Infinity
            }
            (_, Self::Infinity) => {
                Self::Infinity
            }
            (Self::NegInfinity, _) => {
                other.clone()
            }
            (_, Self::NegInfinity) => {
                self.clone()
            }
            (Self::Number(n1, _), Self::Number(n2, _)) => {
                if n1 > n2 { self.clone() } else { other.clone() }
            }
            (Self::Number(n1, _), Self::Symbol(s2)) => {
                let n1_expr = Expression::new_number(n1.clone());
                let check = Expression::new_binop(Box::new(n1_expr.clone()), BinaryOperator::Gt, Box::new(s2.clone()));
                let min_check = Expression::new_ternary(Box::new(check), Box::new(n1_expr), Box::new(s2.clone()));
                min_check.into()
            }
            (Self::Symbol(s1), Self::Number(n2, _)) => {
                let n2_expr = Expression::new_number(n2.clone());
                let check = Expression::new_binop(Box::new(s1.clone()), BinaryOperator::Gt, Box::new(n2_expr.clone()));
                let min_check = Expression::new_ternary(Box::new(check), Box::new(s1.clone()), Box::new(n2_expr));
                min_check.into()
            }
            (Self::Symbol(s1), Self::Symbol(s2)) => {
                if s1 == s2 { self.clone() } else { Self::Infinity }
            }
        }
    }

    fn add(&self, other: &Self) -> Self {
        self.numeric_binop(other, BinaryOperator::Add, |n1, n2| n1.add(n2))
    }

    fn sub(&self, other: &Self) -> Self {
        self.numeric_binop(other, BinaryOperator::Sub, |n1, n2| n1.sub(n2))
    }

    fn mul(&self, other: &Self) -> Self {
        self.numeric_binop(other, BinaryOperator::Mul, |n1, n2| n1.mul(n2))
    }

    fn div(&self, other: &Self) -> Self {
        self.numeric_binop(other, BinaryOperator::IntDiv, |n1, n2| n1.div(n2))
    }

    fn pow(&self, other: &Self) -> Self {
        self.numeric_binop(other, BinaryOperator::Pow, |n1, n2| n1.modpow(n2, &F::prime()))
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
            (_, Self::NegInfinity) => {
                false.into()
            }
            (Self::NegInfinity, _) => {
                true.into()
            }
            (Self::Infinity, _) => {
                false.into()
            }
            (_, Self::Infinity) => {
                true.into()
            }
            (Self::Number(n1, _), Self::Number(n2, _)) => {
                (n1 < n2).into()
            }
            (Self::Number(n1, _), Self::Symbol(e2)) => {
                UncertainBool::Unknown
            }
            (Self::Symbol(e1), Self::Symbol(e2)) => {
                if e1 == e2 { UncertainBool::False } else { UncertainBool::Unknown }
            }
            (Self::Symbol(e1), Self::Number(n2, _)) => {
                UncertainBool::Unknown
            }
        }
    }

    fn gt(&self, other: &Self) -> UncertainBool {
        match (self, other) {
            (Self::NegInfinity, _) => {
                false.into()
            }
            (_, Self::NegInfinity) => {
                true.into()
            }
            (_, Self::Infinity) => {
                false.into()
            }
            (Self::Infinity, _) => {
                true.into()
            }
            (Self::Number(n1, _), Self::Number(n2, _)) => {
                (n1 > n2).into()
            }
            (Self::Number(n1, _), Self::Symbol(e2)) => {
                UncertainBool::Unknown
            }
            (Self::Symbol(e1), Self::Symbol(e2)) => {
                if e1 == e2 { UncertainBool::False } else { UncertainBool::Unknown }
            }
            (Self::Symbol(e1), Self::Number(n2, _)) => {
                UncertainBool::Unknown
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
            (Self::Symbol(e1), Self::Symbol(e2)) => {
                if e1 == e2 { UncertainBool::True } else { UncertainBool::Unknown }
            }
            (_, Self::Symbol(e2)) => {
                UncertainBool::Unknown
            }
            (Self::Symbol(e1), _) => {
                UncertainBool::Unknown
            }
            (Self::Infinity, Self::Infinity) => {
                true.into()
            }
            _ => {
                UncertainBool::False
            }
        }
    }

    /*
    unary ops
     */
    fn negate(&self) -> Self {
        match self {
            Self::NegInfinity => { Self::Infinity }
            Self::Number(n, _) => {
                n.neg().into()
            }
            Self::Symbol(s) => {
                Expression::new_unop(UnaryOperator::Negate, Box::new(s.clone())).into()
            }
            Self::Infinity => { Self::NegInfinity }
        }
    }
}

impl<F: FiniteFieldDef> SymbolicInfiniteBigInt<F> {
    fn symbol(expr: Expression) -> Self {
        Self::Symbol(expr)
    }

    fn numeric_binop(&self, other: &Self, expr_op: BinaryOperator, op: fn(&BigInt, &BigInt) -> BigInt) -> Self {
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
                op(n1, n2).into()
            }
            (Self::Number(n1, _), Self::Symbol(s2)) => {
                let n1_expr = Expression::new_number(n1.clone());
                let symbolic_val = Expression::new_binop(Box::new(n1_expr.clone()), expr_op, Box::new(s2.clone()));
                symbolic_val.into()
            }
            (Self::Symbol(s1), Self::Number(n2, _)) => {
                let n2_expr = Expression::new_number(n2.clone());
                let symbolic_val = Expression::new_binop(Box::new(s1.clone()), expr_op, Box::new(n2_expr.clone()));
                symbolic_val.into()
            }
            (Self::Symbol(s1), Self::Symbol(s2)) => {
                let symbolic_val = Expression::new_binop(Box::new(s1.clone()), expr_op, Box::new(s2.clone()));
                symbolic_val.into()
            }
        }
    }
}