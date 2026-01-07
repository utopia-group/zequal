use std::fmt::{Display, Formatter};
use crate::analysis::{DomainValue};

// can possibly make more efficient abstract state by storing sets of equivalent signals along with
//  the universe
#[derive(Hash, PartialEq, Eq, Clone)]
pub struct EquivalenceValue {
    is_equivalent: bool
}

impl Display for EquivalenceValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", if self.is_equivalent { "equiv" } else { "not equiv" })
    }
}

impl DomainValue for EquivalenceValue {
    fn top() -> Self {
        EquivalenceValue { is_equivalent: false }
    }

    fn bottom() -> Self {
        EquivalenceValue { is_equivalent: true }
    }

    fn is_bottom(&self) -> bool {
        self.is_equivalent
    }

    fn join(&self, other: &Self) -> Self {
        EquivalenceValue{ is_equivalent: self.is_equivalent && other.is_equivalent }
    }

    fn widen(&self, other: &Self) -> Self {
        self.join(other)
    }

    fn narrow(&self, other: &Self) -> Self {
        self.widen(other)
    }

    fn should_narrow() -> bool {
        false
    }

    fn meet(&self, other: &Self) -> Self {
        EquivalenceValue { is_equivalent: self.is_equivalent || other.is_equivalent }
    }
}

impl EquivalenceValue {
    pub fn is_equivalent(&self) -> bool  {
        self.is_equivalent
    }
}
