use std::marker::PhantomData;
use std::ops::Deref;
use smtlib_lowlevel::ast::{Term};
use crate::smt::error::SmtError;
use crate::smt::error::SmtError::IncorrectSort;
use crate::smt::smt::{BuildableTerm, CoreTerm, SmtUtils, TermSort, TypedTerm};

#[derive(Clone, PartialEq, Eq)]
pub struct ArrayTerm<I: TypedTerm + BuildableTerm, V: TypedTerm + BuildableTerm> {
    term: Term,
    index_sort: TermSort,
    value_sort: TermSort,
    i_phantom: PhantomData<I>,
    v_phantom: PhantomData<V>
}

impl<I: TypedTerm + BuildableTerm, V: TypedTerm + BuildableTerm> TypedTerm for ArrayTerm<I, V> {
    fn term(&self) -> &Term {
        &self.term
    }

    fn term_mut(&mut self) -> &mut Term {
        &mut self.term
    }

    fn sort(&self) -> TermSort {
        TermSort::array(&self.index_sort, &self.value_sort)
    }
}

impl<I: TypedTerm + BuildableTerm, V: TypedTerm + BuildableTerm> Into<Term> for ArrayTerm<I, V> {
    fn into(self) -> Term {
        self.term
    }
}

impl<I: TypedTerm + BuildableTerm, V: TypedTerm + BuildableTerm> BuildableTerm for ArrayTerm<I, V> {
    fn new(sort: TermSort, term: Term) -> Result<Self, SmtError> {
        if let TermSort::Array(index_sort, value_sort) = sort {
            Ok(Self::new_unchecked(term, index_sort.deref().clone(), value_sort.deref().clone()))
        }
        else {
            Err(SmtError::IncorrectType("ArrayTerm", "Array", Some(sort)))
        }
    }
}

impl<I: TypedTerm + BuildableTerm, V: TypedTerm + BuildableTerm> CoreTerm for ArrayTerm<I, V> {}

impl<I: TypedTerm + BuildableTerm, V: TypedTerm + BuildableTerm> ArrayTerm<I, V> {
    fn new_unchecked(term: Term, index_sort: TermSort, value_sort: TermSort) -> Self {
        ArrayTerm { term, index_sort: index_sort, value_sort: value_sort, i_phantom: Default::default(), v_phantom: Default::default() }
    }

    pub fn select(self, index: I) -> Result<V, SmtError> {
        if index.sort() != self.index_sort {
            return Err(IncorrectSort("Array select", self.index_sort, index.sort()))
        }
        V::new(self.value_sort, SmtUtils::fn_application("select", vec![self.term, index.into()]))
    }

    pub fn store(self, index: I, value: V) -> Result<Self, SmtError> {
        if &index.sort() != &self.index_sort {
            return Err(IncorrectSort("Array store index", self.index_sort, index.sort()))
        }
        if &value.sort() != &self.value_sort {
            return Err(IncorrectSort("Array store value", self.value_sort, value.sort()))
        }

        Ok(Self::new_unchecked(SmtUtils::fn_application("store", vec![self.term, index.into(), value.into()]), self.index_sort, self.value_sort))
    }

    pub fn const_arr(index_sort: TermSort, const_val: V) -> Result<Self, SmtError> {
        let val_sort = const_val.sort();
        let const_term = SmtUtils::const_array(index_sort.sort(), val_sort.sort(), const_val.into());
        Ok(Self::new_unchecked(const_term, index_sort, val_sort))
    }
}