use smtlib_lowlevel::ast::ModelResponse;
use crate::utils::error::VerificationError;
use crate::utils::wrapped_smt_term::VCTerm;

#[derive(Clone, PartialEq, Eq)]
pub enum SatResult {
    Sat(Result<Vec<ModelResponse>, &'static str>),
    Unsat,
    Unknown
}

impl SatResult {
    pub fn is_sat(&self) -> bool {
        match self {
            SatResult::Sat(_) => { true }
            _ => { false }
        }
    }

    pub fn is_unsat(&self) -> bool {
        match self {
            SatResult::Unsat => { true }
            _ => { false }
        }
    }

    pub fn is_unknown(&self) -> bool {
        match self {
            SatResult::Unknown => { true }
            _ => { false }
        }
    }
}
#[derive(Clone, PartialEq, Eq)]
pub enum ValidityResult {
    Valid,
    Invalid(Result<Vec<ModelResponse>, &'static str>),
    Unknown
}

impl ValidityResult {
    pub fn is_valid(&self) -> bool {
        match self {
            ValidityResult::Valid => { true }
            _ => { false }
        }
    }

    pub fn is_invalid(&self) -> bool {
        match self {
            ValidityResult::Invalid(_) => { true }
            _ => { false }
        }
    }

    pub fn is_unknown(&self) -> bool {
        match self {
            ValidityResult::Unknown => { true }
            _ => { false }
        }
    }
}



pub trait SmtUtils<T: VCTerm> {
    fn find_required_preds(&mut self, query: Vec<T>) -> Result<Vec<T>, VerificationError>;
    fn check_sat(&mut self, query: T, get_model: bool) -> Result<SatResult, VerificationError>;
    fn check_validity(&mut self, query: T, get_model: bool) -> Result<ValidityResult, VerificationError>;
}