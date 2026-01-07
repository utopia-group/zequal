use std::fmt::{Display, Formatter};
use crate::smt::error::SmtError;
use crate::utils::error::VerificationError;
use crate::utils::wrapped_smt_term::{LazyTerm, VCTerm};

#[derive(Clone)]
pub(crate) struct ConditionTerm<T> {
    pub(crate) assumes: Option<T>,
    pub(crate) asserts: T
}

impl<T: VCTerm + LazyTerm> Display for ConditionTerm<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.assumes {
            None => {
                write!(f, "{}", self.asserts)
            }
            Some(a) => {
                write!(f, "{} -> {}", a, self.asserts)
            }
        }
    }
}

impl<T: VCTerm + LazyTerm> ConditionTerm<T> {
    pub fn new(assumes: Option<T>, asserts: T) -> Self {
        Self {assumes, asserts}
    }

    pub fn to_term(self) -> Result<T, VerificationError> {
        match self.assumes {
            None => { Ok(self.asserts) }
            Some(a) => { Ok(a.implies(self.asserts)?) }
        }
    }

    pub fn transform<F: Fn(T) -> Result<T, SmtError>>(self, default_assume: Option<T>, op: F) -> Result<Self, VerificationError> {
        let new_assumes = match self.assumes {
            None => { default_assume }
            Some(a) => { Some(op(a)?) }
        };

        let new_asserts = op(self.asserts)?;
        Ok(Self::new(new_assumes, new_asserts))
    }

    pub fn add_assume(self, new_assume: T) -> Result<Self, VerificationError> {
        let new_assumes = match self.assumes {
            None => { new_assume }
            Some(a) => { a.and(new_assume)? }
        };

        Ok(Self::new(Some(new_assumes), self.asserts))
    }

    pub fn add_assert(self, new_assert: T) -> Result<Self, VerificationError> {
        Ok(Self::new(self.assumes, self.asserts.and(new_assert)?))
    }

    pub fn join(all: &Vec<Self>) -> Result<Self, VerificationError> {
        if all.len() == 0 {
            Err(VerificationError::InsufficientArgumentCnt("join", 1))
        }
        else if all.len() == 1 {
            Ok(all.get(0).unwrap().clone())
        }
        else {
            let mut terms = vec![];
            for condition in all {
                terms.push(condition.clone().to_term()?);
            }
            Ok(ConditionTerm::new(None, T::and_all(terms)?))
        }
    }
}