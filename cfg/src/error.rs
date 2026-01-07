use std::fmt::{Display, Formatter};
use thiserror::Error;
use crate::named_storage::Component;

#[derive(Error, Debug)]
pub enum CFGError {
    UnsupportedStmt(&'static str),
    UnsupportedExpr(&'static str),
    UninterpretableLog(Option<String>),
    NotALValue,
    UnknownComponentType(Component),
    TemplateNotFound(String),
    BlockNotFound(usize),
    ComponentInitializationNotFound(String),
    VariableAlreadyDeclared(String),
    VariableNotFound(String, String),
    InvalidComponentAccess(String),
    MissingComponentAccess(String),
    MismatchedComponentType(String, String, String),
    IncorrectTemplate(String, String),
    MultipleComponentAccess(String, usize),
    TypeError(String, String, String)
}

impl Display for CFGError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            CFGError::UnsupportedStmt(s) => { write!(f, "Tried to convert unsupported statement type: {}", s) }
            CFGError::UnsupportedExpr(s) => { write!(f, "Tried to convert unsupported expression type: {}", s) }
            CFGError::UninterpretableLog(s) => {
                match s {
                    None => { write!(f, "Can not interpret log string") }
                    Some(log) => { write!(f, "Can not interpret log string: {}", log) }
                }
            }
            CFGError::NotALValue => { write!(f, "Found an expression on the left hand side of an assignment that is not a LValue")}
            CFGError::UnknownComponentType(c) => { write!(f, "Could not infer the type of component {} in template {}", c.name(), c.declaring_template()) }
            CFGError::TemplateNotFound(n) => { write!(f, "Could not find template with name '{}'", n) }
            CFGError::BlockNotFound(id) => { write!(f, "Could not find block {}", id) }
            CFGError::ComponentInitializationNotFound(name) => { write!(f, "Could not find initialization for component {}", name) }
            CFGError::VariableAlreadyDeclared(name) => { write!(f, "Variable {} was declared more than once", name) }
            CFGError::VariableNotFound(template, name) => { write!(f, "Variable {} not found in template {}", name, template) }
            CFGError::InvalidComponentAccess(name) => { write!(f, "Invalid component access on variable {}", name)}
            CFGError::MissingComponentAccess(name) => { write!(f, "Component {} used without accessing component", name) }
            CFGError::MismatchedComponentType(name, t1, t2) => { write!(f, "Component {} is declared with type {} and {}", name, t1, t2) }
            CFGError::IncorrectTemplate(expected, found) => { write!(f, "Incorrect template found. Expected {} but found {}", expected, found) }
            CFGError::MultipleComponentAccess(name, cnt) => { write!(f, "There may only be one component access per component, but {} was accessed {} times", name, cnt) }
            CFGError::TypeError(name, expected, actual) => { write!(f, "{} was expected to be a {} but was actually {}", name, expected, actual) }
        }
    }
}