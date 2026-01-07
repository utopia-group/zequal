use std::fmt::{Display, Formatter};
use thiserror::Error;
use crate::smt::smt::TermSort;

#[derive(Error, Debug)]
pub enum SmtError {
    IncorrectSort(&'static str, TermSort, TermSort),
    IncorrectType(&'static str, &'static str, Option<TermSort>),
    MismatchedSort(&'static str, TermSort, TermSort),
    MismatchedTypes(&'static str, &'static str, Option<&'static str>),
    UnsupportedSort(&'static str, TermSort),
    UnsupportedType(&'static str, &'static str, Option<TermSort>),
    CannotParseInt(String),
    NotQuantified(&'static str, String),
    IncorrectArgumentCount(&'static str, usize, usize)
}

impl Display for SmtError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SmtError::IncorrectSort(loc, expected, actual) => { write!(f, "{} expected Smt Sort {} but found {}", loc, expected, actual) }
            SmtError::IncorrectType(loc, expected, maybe_actual) => {
                match maybe_actual {
                    None => { write!(f, "{} expected a {} type", loc, expected)  }
                    Some(actual) => { write!(f, "{} expected a {} type but found {}", loc, expected, actual)  }
                }
            }
            SmtError::MismatchedSort(loc, s1, s2) => { write!(f, "{} expects matching sorts but received {} and {}", loc, s1, s2) }
            SmtError::MismatchedTypes(loc, t1, t2_option) => {
                match t2_option {
                    None => { write!(f, "{} expects matching arguments of type {}", loc, t1) }
                    Some(t2) => { write!(f, "{} expects matching arguments of type {} but received {}", loc, t1, t2)  }
                }
            }
            SmtError::UnsupportedSort(loc, sort) => { write!(f, "{} does not support sort {}", loc, sort) }
            SmtError::UnsupportedType(loc, ty, maybe_sort) => {
                match maybe_sort {
                    None => { write!(f, "{} does not support sort of type {}", loc, ty) }
                    Some(sort) => { write!(f, "{} does not support sort of type {} and found {}", loc, ty, sort) }
                }
            }
            SmtError::CannotParseInt(str) => { write!(f, "Cannot parse integer from {}", str) }
            SmtError::NotQuantified(loc, term) => { write!(f, "{} expected {} to be quantified", loc, term) }
            SmtError::IncorrectArgumentCount(loc, expected, actual) => { write!(f, "{loc} expected {expected} arguments but received {actual}")}
        }
    }
}