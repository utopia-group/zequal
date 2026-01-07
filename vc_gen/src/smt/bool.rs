use smtlib_lowlevel::ast::{Term};
use crate::smt::error::SmtError;
use crate::smt::smt::{BuildableTerm, CoreTerm, SmtUtils, StaticTypedTerm, TermSort, TypedTerm};

pub struct BoolTermSort {}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct BoolTerm {
    term: Term
}

impl Into<Term> for BoolTerm {
    fn into(self) -> Term {
        self.term
    }
}

impl From<bool> for BoolTerm {
    fn from(value: bool) -> Self {
        Self::new_unchecked(SmtUtils::constant(if value { "true" } else { "false" } ))
    }
}

impl TypedTerm for BoolTerm {
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

impl BuildableTerm for BoolTerm {
    fn new(sort: TermSort, term: Term) -> Result<Self, SmtError> {
        if sort != TermSort::Bool {
            return Err(SmtError::IncorrectSort("BoolTerm", TermSort::Bool, sort))
        }
        Ok(Self::new_unchecked(term))
    }
}

impl BoolTerm {
    fn get_args_if(self, app_name: &str) -> Vec<Term> {
        match &self.term {
            Term::Application(app, args) => {
                if app.to_string() == app_name {
                    args.to_owned()
                }
                else {
                    vec![self.term]
                }
            }
            _ => { vec![self.term] }
        }
    }

    fn new_unchecked(term: Term) -> Self {
        BoolTerm { term }
    }
    pub fn and_all(conjuncts: Vec<Self>) -> Self {
        Self::new_unchecked(SmtUtils::fn_application("and", conjuncts.into_iter().flat_map(|c| Self::get_args_if(c, "and")).collect()))
    }

    pub fn or_all(disjuncts: Vec<Self>) -> Self {
        Self::new_unchecked(SmtUtils::fn_application("or", disjuncts.into_iter().flat_map(|d| Self::get_args_if(d, "or")).collect()))
    }

    pub fn and(self, other: Self) -> Self {
        let mut args = Self::get_args_if(self, "and");
        args.append(&mut Self::get_args_if(other, "and"));
        Self::new_unchecked(SmtUtils::fn_application("and", args))
    }

    pub fn or(self, other: Self) -> Self {
        let mut args = Self::get_args_if(self, "or");
        args.append(&mut Self::get_args_if(other, "or"));
        Self::new_unchecked(SmtUtils::fn_application("or", args))
    }

    pub fn implies(self, other: Self) -> Self {
        Self::new_unchecked(SmtUtils::fn_application("=>", vec![self.term, other.term]))
    }

    pub fn xor(self, other: Self) -> Self {
        Self::new_unchecked(SmtUtils::fn_application("xor", vec![self.term, other.term]))
    }

    pub fn ite<T: TypedTerm + BuildableTerm>(self, if_true: T, if_false: T) -> Result<T, SmtError> {
        if if_true.sort() != if_false.sort() {
            return Err(SmtError::MismatchedSort("ite", if_true.sort(), if_false.sort()))
        }
        T::new(if_true.sort(), SmtUtils::fn_application("ite", vec![self.term, if_true.into(), if_false.into()]))
    }

    pub fn not(self) -> Self {
        Self::new_unchecked(SmtUtils::fn_application("not", vec![self.term]))
    }
}

impl CoreTerm for BoolTerm {}

impl StaticTypedTerm for BoolTerm {
    fn underlying_sort() -> TermSort {
        TermSort::Bool
    }
    fn variable(name: &str) -> Self {
        Self::new_unchecked(SmtUtils::variable(name))
    }
}