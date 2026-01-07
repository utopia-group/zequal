use std::marker::PhantomData;
use std::ops::Deref;
use smtlib_lowlevel::ast::Term;
use crate::smt::array::ArrayTerm;
use crate::smt::error::SmtError;
use crate::smt::smt::{BuildableTerm, CoreTerm, SmtUtils, TermSort, TypedTerm};

#[derive(Clone, PartialEq, Eq)]
pub struct UFTerm<O: TypedTerm + BuildableTerm> {
    name: String,
    term: Term,
    input_sorts: Vec<TermSort>,
    output_sort: TermSort,
    v_phantom: PhantomData<O>
}

// This is a bit easier to interact with if all inputs have the same term type
#[derive(Clone, PartialEq, Eq)]
pub struct UniformUFTerm<I: TypedTerm + BuildableTerm, O: TypedTerm + BuildableTerm> {
    name: String,
    term: Term,
    input_sorts: Vec<TermSort>,
    output_sort: TermSort,
    v_phantom: PhantomData<I>,
    v_phantom1: PhantomData<O>
}

pub trait UFOps<I,O> {
    fn call(self, inputs: Vec<I>) -> Result<O, SmtError>;
    fn arity(&self) -> usize;
    fn name(&self) -> &str;
    fn input_sorts(&self) -> &Vec<TermSort>;
    fn output_sort(&self) -> &TermSort;
}

impl<O: TypedTerm + BuildableTerm> UFOps<(TermSort, Term), O> for UFTerm<O> {
    fn call(self, inputs: Vec<(TermSort, Term)>) -> Result<O, SmtError> {
        if inputs.len() != self.input_sorts.len() {
            return Err(SmtError::IncorrectArgumentCount("call", self.input_sorts.len(), inputs.len()))
        }

        let mut input_terms = vec![];
        for i in 0..inputs.len() {
            let (input_sort, input) = &inputs[i];
            let expected_sort = &self.input_sorts[i];
            if input_sort != expected_sort {
                return Err(SmtError::IncorrectSort("call", expected_sort.clone(), input_sort.clone()))
            }
            input_terms.push(input.clone());
        }

        let name = self.name();
        O::new(self.output_sort.clone(), SmtUtils::fn_application(name, input_terms))
    }

    fn arity(&self) -> usize {
        self.input_sorts.len()
    }

    fn name(&self) -> &str {
        self.name.as_str()
    }

    fn input_sorts(&self) -> &Vec<TermSort> {
        &self.input_sorts
    }

    fn output_sort(&self) -> &TermSort {
        &self.output_sort
    }
}

impl<I: TypedTerm + BuildableTerm, O: TypedTerm + BuildableTerm> UFOps<I,O> for UniformUFTerm<I,O> {
    fn call(self, inputs: Vec<I>) -> Result<O, SmtError> {
        if inputs.len() != self.input_sorts.len() {
            return Err(SmtError::IncorrectArgumentCount("call", self.input_sorts.len(), inputs.len()))
        }

        let mut input_terms = vec![];
        for i in 0..inputs.len() {
            let input = &inputs[i];
            let input_sort = input.sort();
            let expected_sort = &self.input_sorts[i];
            if &input_sort != expected_sort {
                return Err(SmtError::IncorrectSort("call", expected_sort.clone(), input_sort))
            }
            input_terms.push(input.term().clone());
        }

        let name = self.name();
        O::new(self.output_sort.clone(), SmtUtils::fn_application(name, input_terms))
    }

    fn arity(&self) -> usize {
        self.input_sorts.len()
    }

    fn name(&self) -> &str {
        self.name.as_str()
    }

    fn input_sorts(&self) -> &Vec<TermSort> {
        &self.input_sorts
    }

    fn output_sort(&self) -> &TermSort {
        &self.output_sort
    }
}

impl<O: TypedTerm + BuildableTerm> TypedTerm for UFTerm<O> {
    fn term(&self) -> &Term {
        &self.term
    }

    fn term_mut(&mut self) -> &mut Term {
        &mut self.term
    }

    fn sort(&self) -> TermSort {
        TermSort::UninterpretedFn(self.input_sorts.clone(), Box::new(self.output_sort.clone()))
    }
}

impl<O: TypedTerm + BuildableTerm> Into<Term> for UFTerm<O> {
    fn into(self) -> Term {
        self.term
    }
}

impl<O: TypedTerm + BuildableTerm> BuildableTerm for UFTerm<O> {
    fn new(sort: TermSort, term: Term) -> Result<Self, SmtError> {
        if let TermSort::UninterpretedFn(input_sort, output_sort) = sort {
            Ok(Self::new_unchecked(term, input_sort, *output_sort))
        }
        else {
            Err(SmtError::IncorrectType("UFTerm", "UninterpretedFn", Some(sort)))
        }
    }
}

impl<O: TypedTerm + BuildableTerm> CoreTerm for UFTerm<O> {}

impl<O: TypedTerm + BuildableTerm> UFTerm<O> {
    fn new_unchecked(term: Term, input_sorts: Vec<TermSort>,  output_sort: TermSort) -> Self {
        UFTerm { name: term.to_string(), term, input_sorts, output_sort, v_phantom: Default::default() }
    }
}

impl<I: TypedTerm + BuildableTerm, O: TypedTerm + BuildableTerm> TypedTerm for UniformUFTerm<I, O> {
    fn term(&self) -> &Term {
        &self.term
    }

    fn term_mut(&mut self) -> &mut Term {
        &mut self.term
    }

    fn sort(&self) -> TermSort {
        TermSort::UninterpretedFn(self.input_sorts.clone(), Box::new(self.output_sort.clone()))
    }
}

impl<I: TypedTerm + BuildableTerm, O: TypedTerm + BuildableTerm> Into<Term> for UniformUFTerm<I, O> {
    fn into(self) -> Term {
        self.term
    }
}

impl<I: TypedTerm + BuildableTerm, O: TypedTerm + BuildableTerm> BuildableTerm for UniformUFTerm<I, O> {
    fn new(sort: TermSort, term: Term) -> Result<Self, SmtError> {
        if let TermSort::UninterpretedFn(input_sort, output_sort) = sort {
            Ok(Self::new_unchecked(term, input_sort, *output_sort))
        }
        else {
            Err(SmtError::IncorrectType("UFTerm", "UninterpretedFn", Some(sort)))
        }
    }
}

impl<I: TypedTerm + BuildableTerm, O: TypedTerm + BuildableTerm> CoreTerm for UniformUFTerm<I, O> {}

impl<I: TypedTerm + BuildableTerm, O: TypedTerm + BuildableTerm> UniformUFTerm<I,O> {
    fn new_unchecked(term: Term, input_sorts: Vec<TermSort>,  output_sort: TermSort) -> Self {
        UniformUFTerm { name: term.to_string(), term, input_sorts, output_sort, v_phantom: Default::default(), v_phantom1: Default::default() }
    }
}