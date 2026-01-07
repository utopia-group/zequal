use std::fmt::{Display, Formatter};
use num_bigint_dig::BigInt;
use crate::analysis::DomainValue;
use num_traits::identities::Zero;
use num_traits::One;
use cfg::expr::expression::Expression;
use cfg::finite_fields::FiniteFieldDef;
use crate::domains::interval::infinite_number::infinite_bigint::InfiniteBigInt;
use crate::domains::interval::infinite_number::infinite_number::InfiniteNumber;
use crate::domains::interval::infinite_number::symbolic_infinite_bigint::SymbolicInfiniteBigInt;


pub type Interval<F: FiniteFieldDef> = IntervalValue<InfiniteBigInt<F>>;
pub type SymbolicInterval<F: FiniteFieldDef> = IntervalValue<SymbolicInfiniteBigInt<F>>;

#[derive(Hash, PartialEq, Eq, Clone)]
pub struct IntervalValue<N: InfiniteNumber> {
    lower: N,
    upper: N
}

impl<N: InfiniteNumber> Display for IntervalValue<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}, {}]", self.lower, self.upper)
    }
}

impl<N: InfiniteNumber> From<BigInt> for IntervalValue<N> {
    fn from(value: BigInt) -> Self {
        Self::number(value)
    }
}

impl<N: InfiniteNumber> From<&BigInt> for IntervalValue<N> {
    fn from(value: &BigInt) -> Self {
        Self::number(value.clone())
    }
}

impl<N: InfiniteNumber> DomainValue for IntervalValue<N> {
    fn top() -> Self {
        return Self {lower: N::neg_infinity(), upper: N::infinity()}
    }

    fn bottom() -> Self {
        return Self {lower: N::infinity(), upper: N::neg_infinity()}
    }

    fn is_bottom(&self) -> bool {
        self.lower.gt(&self.upper).is_true()
    }

    fn join(&self, other: &Self) -> Self {
        let lower = self.lower.min(&other.lower);
        let upper = self.upper.max(&other.upper);
        Self{ lower, upper }
    }

    fn widen(&self, other: &Self) -> Self {
        if self.is_bottom() {
            return other.clone()
        }
        if other.is_bottom() {
            return self.clone()
        }
        let lower = if !other.lower.lt(&self.lower).is_false() { N::neg_infinity() } else { self.lower.clone() };
        let upper = if !other.upper.gt(&self.upper).is_false() { N::infinity() } else { self.upper.clone() };
        Self { lower, upper }
    }

    fn narrow(&self, other: &Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return Self::bottom()
        }
        let lower = if self.lower.is_neg_infinity() { other.lower.clone() } else { self.lower.clone() };
        let upper = if self.upper.is_infinity() { other.upper.clone() } else { self.upper.clone() };
        Self { lower, upper }
    }

    fn should_narrow() -> bool {
        true
    }

    fn meet(&self, other: &Self) -> Self {
        if self.upper.lt(other.lower()).is_true() || self.lower.gt(other.upper()).is_true() {
            return Self::bottom()
        }

        //If we can't determine ordering, default to self as we can only further constrain an interval
        let lower = if self.lower.lt(&other.lower).is_unknown() {self.lower.clone()} else {self.lower.max(&other.lower)};
        let upper = if self.upper.lt(&other.upper).is_unknown() {self.upper.clone()} else {self.upper.min(&other.upper)};

        if lower.gt(&upper).is_true() {
            return Self::bottom()
        }
        else {
            Self{ lower, upper }
        }
    }
}

impl<N: InfiniteNumber> IntervalValue<N> {
    pub fn new(lower: N, upper: N) -> Self {
        Self {lower, upper}
    }
    pub fn number(value: BigInt) -> Self {
        let val: N = value.into();
        Self { lower: val.clone(), upper: val }
    }

    pub fn expr_bounds(expr: &Expression) -> Self {
        let lower = N::expr_min(expr);
        let upper = N::expr_max(expr);
        Self { lower, upper }
    }

    pub fn lower(&self) -> &N {
        &self.lower
    }

    pub fn upper(&self) -> &N {
        &self.upper
    }

    pub fn relax_lower(&self) -> Self {
        Self { lower: N::neg_infinity(), upper: self.upper.clone() }
    }

    pub fn relax_upper(&self) -> Self {
        Self { lower: self.lower.clone(), upper: N::infinity() }
    }

    pub fn add(&self, other: &Self) -> Self {
        let lower = self.lower.add(&other.lower);
        let upper = self.upper.add(&other.upper);
        Self { lower, upper }
    }

    pub fn sub(&self, other: &Self) -> Self {
        let lower = self.lower.sub(&other.upper);
        let upper = self.upper.sub(&other.lower);
        Self { lower, upper }
    }

    pub fn mul(&self, other: &Self) -> Self {
        let lower = self.lower.mul(&other.lower);
        let upper = self.upper.mul(&other.upper);
        Self { lower, upper }
    }

    pub fn div(&self, other: &Self) -> Self {
        let lower = self.lower.div(&other.upper);
        let upper = self.upper.div(&other.lower);
        Self { lower, upper }
    }

    pub fn pow(&self, other: &Self) -> Self {
        let lower = self.lower.pow(&other.lower);
        let upper = self.upper.pow(&other.upper);
        Self { lower, upper }
    }

    pub fn modulus(&self, other: &Self) -> Self {
        //assume that we can take on any value in modulus
        Self { lower: BigInt::zero().into(), upper: other.upper.clone() }
    }

    pub fn shr(&self, other: &Self) -> Self {
        let two: Self = BigInt::from(2).into();
        let rhs = two.pow(other);
        self.mul(&rhs)
    }

    pub fn shl(&self, other: &Self) -> Self {
        let two: Self = BigInt::from(2).into();
        let rhs = two.pow(other);
        self.div(&rhs)
    }

    pub fn lt(&self, other: &Self) -> Self {
        if self.upper.lt(&other.lower).is_true() {
            return BigInt::one().into()
        }
        else if other.upper.lt(&self.lower).is_true() {
            return BigInt::zero().into()
        }

        Self {lower: BigInt::zero().into(), upper: BigInt::one().into()}
    }

    pub fn lte(&self, other: &Self) -> Self {
        if self.upper.lt(&other.lower).is_true() {
            return BigInt::one().into()
        }
        else if other.upper.lt(&self.lower).is_true() {
            return BigInt::zero().into()
        }
        else if self.upper.maybe_eq(&self.lower).is_true() && other.upper.maybe_eq(&other.lower).is_true() && self.lower.maybe_eq(&other.lower).is_true() {
            return BigInt::one().into()
        }

        Self {lower: BigInt::zero().into(), upper: BigInt::one().into()}
    }

    pub fn gt(&self, other: &Self) -> Self {
        if self.upper.gt(&other.lower).is_true() {
            return BigInt::one().into()
        }
        else if other.upper.gt(&self.lower).is_true() {
            return BigInt::zero().into()
        }

        Self {lower: BigInt::zero().into(), upper: BigInt::one().into()}
    }

    pub fn gte(&self, other: &Self) -> Self {
        if self.upper.gt(&other.lower).is_true() {
            return BigInt::one().into()
        }
        else if other.upper.gt(&self.lower).is_true() {
            return BigInt::zero().into()
        }
        else if self.upper.maybe_eq(&self.lower).is_true() && other.upper.maybe_eq(&other.lower).is_true() && self.lower.maybe_eq(&other.lower).is_true() {
            return BigInt::one().into()
        }

        Self {lower: BigInt::zero().into(), upper: BigInt::one().into()}
    }

    pub fn eq(&self, other: &Self) -> Self {
        if self.upper.maybe_eq(&self.lower).is_true() && other.upper.maybe_eq(&other.lower).is_true() && self.lower.maybe_eq(&other.lower).is_true() {
            return BigInt::one().into()
        }
        else if self.upper.gt(&other.lower).is_true() {
            return BigInt::zero().into()
        }
        else if other.upper.gt(&self.lower).is_true() {
            return BigInt::zero().into()
        }

        Self {lower: BigInt::zero().into(), upper: BigInt::one().into()}
    }

    pub fn neq(&self, other: &Self) -> Self {
        if self.upper.maybe_eq(&self.lower).is_true() && other.upper.maybe_eq(&other.lower).is_true() && self.lower.maybe_eq(&other.lower).is_true() {
            return BigInt::zero().into()
        }
        else if self.upper.gt(&other.lower).is_true() {
            return BigInt::one().into()
        }
        else if other.upper.gt(&self.lower).is_true() {
            return BigInt::one().into()
        }

        Self {lower: BigInt::zero().into(), upper: BigInt::one().into()}
    }

    pub fn and(&self, other: &Self) -> Self {
        if self.lower.maybe_eq(&self.upper).is_true() {
            if other.lower.maybe_eq(&other.upper).is_true() && self.lower.maybe_eq(&BigInt::one().into()).is_true() && other.lower.maybe_eq(&BigInt::one().into()).is_true() {
                return BigInt::one().into()
            }
            else if self.lower.maybe_eq(&BigInt::zero().into()).is_true() {
                return BigInt::zero().into()
            }
        }
        else if other.lower.maybe_eq(&other.upper).is_true() && other.lower.maybe_eq(&BigInt::zero().into()).is_true() {
            return BigInt::zero().into()
        }

        Self {lower: BigInt::zero().into(), upper: BigInt::one().into()}
    }

    pub fn or(&self, other: &Self) -> Self {
        if self.lower.maybe_eq(&self.upper).is_true() {
            if other.lower.maybe_eq(&other.upper).is_true() && self.lower.maybe_eq(&BigInt::zero().into()).is_true() && other.lower.maybe_eq(&BigInt::zero().into()).is_true() {
                return BigInt::zero().into()
            }
            else if self.lower.maybe_eq(&BigInt::one().into()).is_true() {
                return BigInt::one().into()
            }
        }
        else if other.lower.maybe_eq(&other.upper).is_true() && other.lower.maybe_eq(&BigInt::one().into()).is_true() {
            return BigInt::one().into()
        }

        Self {lower: BigInt::zero().into(), upper: BigInt::one().into()}
    }

    pub fn negate(&self) -> Self {
        Self { lower: self.upper.negate(), upper: self.lower.negate() }
    }

    pub fn not(&self) -> Self {
        if self.lower.maybe_eq(&self.upper).is_true() {
            if self.lower.maybe_eq(&BigInt::zero().into()).is_true() {
                return BigInt::one().into()
            }
            else {
                return BigInt::zero().into()
            }
        }

        Self { lower: self.upper.negate(), upper: self.lower.negate() }
    }
}