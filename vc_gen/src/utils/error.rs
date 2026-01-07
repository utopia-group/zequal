use std::fmt::{Display, Formatter};
use itertools::Itertools;
use smtlib_lowlevel::ast::ModelResponse;
use thiserror::Error;
use cfg::error::CFGError;
use cfg::expr::invariant::InvariantExpr;
use static_analysis::analysis::StateError;
use crate::smt::error::SmtError;

#[derive(Error, Debug)]
pub enum VerificationError  {
    Msg(&'static str),
    CFGError(#[from] CFGError),
    SmtError(#[from] SmtError),
    StateError(#[from] StateError),
    NoInvariant,
    UnsupportedFeature(&'static str, &'static str),
    InvariantNotInductive(InvariantExpr, Result<Vec<ModelResponse>, &'static str>),
    InvariantDoesNotImplyPost(InvariantExpr, String, Result<Vec<ModelResponse>, &'static str>),
    PostconditionNotImplied(String, String, Result<Vec<ModelResponse>, &'static str>),
    InsufficientArgumentCnt(&'static str, usize),
    AliasedQuantifiedVar(String),
    EmptyCallstack(&'static str),
    TemplateSummarizationFailed(&'static str, String, Result<Vec<ModelResponse>, &'static str>),
    ReferenceNotFound(&'static str, String),
    NoUnqiueLoopIterator(usize, Vec<String>),
    NoLoopIterator(usize),
    UnsatHoudiniCandidates,
    SolverReturnedUnknown(&'static str),
    SolverReturnedSat(&'static str)
}

/*impl<T: VCTerm> From<SmtError> for VerificationError<T> {
    fn from(value: SmtError) -> Self {
        Self::SmtError(value)
    }
}*/

impl From<&'static str> for VerificationError {
    fn from(value: &'static str) -> Self {
        VerificationError::Msg(value)
    }
}

fn get_model_str(model_res: &Result<Vec<ModelResponse>, &'static str>) -> String {
    match model_res {
        Ok(model) => {
            let sorted_response: Vec<&ModelResponse> = model.iter()
                .sorted_by(|a, b| a.to_string().cmp(&b.to_string()))
                .collect();

            sorted_response.iter().map(|r| format!("{}", r)).join("\n")
        }
        Err(err) => {
            format!("Could not fetch model: {}", err)
        }
    }
}

impl Display for VerificationError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            VerificationError::Msg(msg) => { write!(f, "{}", msg) }
            VerificationError::NoInvariant => { write!(f, "Could not find loop invariant") }
            VerificationError::InvariantNotInductive(inv, _) => {
                write!(f, "Invariant is not inductive\nInvariant: {}", inv)
            }
            VerificationError::InvariantDoesNotImplyPost(inv, p, _) => {
                write!(f, "Invariant does not imply postcondition \nInvariant: {}\nPost: {}", inv, p)
            }
            VerificationError::PostconditionNotImplied(expr, post, _) => {
                write!(f, "Expression does not imply postcondition \nExpression: {}\nPost: {}", expr, post)
            }
            VerificationError::CFGError(err) => {
                write!(f, "Error thrown when accessing CFG: {}", err)
            }
            VerificationError::SmtError(err) => {
                write!(f, "Error thrown when generating SMT: {}", err)
            }
            VerificationError::InsufficientArgumentCnt(loc, cnt) => {
                write!(f, "{} expected {} arguments to be provided", loc, cnt)
            }
            VerificationError::UnsupportedFeature(loc, feature) => {
                write!(f, "{} does not support {}", loc, feature)
            }
            VerificationError::AliasedQuantifiedVar(v) => {
                write!(f, "Attempted to create quantified variable {} but it aliases another variable", v)
            }
            VerificationError::EmptyCallstack(loc) => {
                write!(f, "{} requires the callstack not to be empty", loc)
            }
            VerificationError::TemplateSummarizationFailed(loc, name, model) => {
                write!(f, "{}\n{} failed to generate a summary for template {}", get_model_str(model), loc, name)
            }
            VerificationError::ReferenceNotFound(loc, name) => {
                write!(f, "Could not resolve reference to {} in {}", name, loc)
            }
            VerificationError::NoUnqiueLoopIterator(id, vars) => {
                write!(f, "Could not unique identify a loop iterator for loop {}. Found: {}", id, vars.iter().join(", "))
            }
            VerificationError::NoLoopIterator(id) => {
                write!(f, "Could not identify a loop iterator for loop {}", id)
            }
            VerificationError::UnsatHoudiniCandidates => {
                write!(f, "Houdini candidates must be sat")
            }
            VerificationError::SolverReturnedUnknown(msg) => {
                write!(f, "Solver returned UNKNOWN when {}", msg)
            }
            VerificationError::StateError(e) => {
                write!(f, "{}", e)
            }
            VerificationError::SolverReturnedSat(fn_name) => {
                write!(f, "{} unexpectedly returned sat", fn_name)
            }
        }
    }
}