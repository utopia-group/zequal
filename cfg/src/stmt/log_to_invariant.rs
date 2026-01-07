use std::collections::HashMap;

use program_structure::ast;
use program_structure::ast::LogArgument;

use crate::error::CFGError;
use crate::expr::expression::Expression;
use crate::expr::invariant::InvariantExpr;
use crate::expr::variable_ref::{ComponentRef, Ref};
use crate::named_storage::NamedStorage;
use crate::storage_type::TypeInference;

pub struct LogToInvariant {}

impl LogToInvariant {
    pub fn is_inv(log_body: &Vec<LogArgument>) -> bool {
        if let Some(LogArgument::LogStr(str)) = log_body.get(0) {
            str == "invariant"
        }
        else {
            false
        }
    }

    pub fn is_assume(log_body: &Vec<LogArgument>) -> bool {
        if let Some(LogArgument::LogStr(str)) = log_body.get(0) {
            str == "assume"
        }
        else {
            false
        }
    }

    pub fn is_assert(log_body: &Vec<LogArgument>) -> bool {
        if let Some(LogArgument::LogStr(str)) = log_body.get(0) {
            str == "assert"
        }
        else {
            false
        }
    }

    pub fn is_requires(log_body: &Vec<LogArgument>) -> bool {
        if let Some(LogArgument::LogStr(str)) = log_body.get(0) {
            str == "requires"
        }
        else {
            false
        }
    }

    pub fn is_ensures(log_body: &Vec<LogArgument>) -> bool {
        if let Some(LogArgument::LogStr(str)) = log_body.get(0) {
            str == "ensures"
        }
        else {
            false
        }
    }

    pub fn is_invoke(log_body: &Vec<LogArgument>) -> bool {
        if let Some(LogArgument::LogStr(str)) = log_body.get(0) {
            if str == "invoke" {
                if let Some(LogArgument::LogExp(_)) = log_body.get(1) {
                    return log_body.len() == 2
                }
            }
        }

        false
    }

    pub fn is_assume_consistent(log_body: &Vec<LogArgument>) -> bool {
        if log_body.len() != 1 {
            false
        }
        else if let Some(LogArgument::LogStr(str)) = log_body.get(0) {
            str == "assume_consistent"
        }
        else {
            false
        }
    }

    fn extract_quantifier_vars(str: &str) -> Vec<String> {
        str.split(",").map(|s| String::from(s.trim())).collect()
    }

    pub fn extract_template_invocation(type_inference: &TypeInference, vars_and_signals: &HashMap<String, (usize, NamedStorage)>, template_params: &HashMap<String, Vec<String>>, parent: &String, var_versions: &HashMap<String, usize>, log_body: &Vec<LogArgument>) -> Result<ComponentRef, CFGError> {
        if !Self::is_invoke(log_body) {
            return Err(CFGError::UninterpretableLog(None));
        }

        let LogArgument::LogExp(invoke_expr) = log_body.get(1).unwrap() else { unreachable!("Already checked if this is a long invariant, should not fail") };
        let invoked = match invoke_expr {
            ast::Expression::Variable { name, access, .. } => {
                Ref::from_ast(type_inference, vars_and_signals, template_params, parent, var_versions, name.clone(), access, true)?
            }
            _ => {
                panic!("An explicit invoke must specify a component as the expression")
            }
        };

        if let Ref::Comp(invoked_component) = invoked {
            Ok(invoked_component)
        }
        else {
            panic!("Explicit invoke must reference a component");
        }
    }

    pub fn extract_log_invariant(type_inference: &TypeInference, vars_and_signals: &HashMap<String, (usize, NamedStorage)>, template_params: &HashMap<String, Vec<String>>, parent: &String, log_body: &[LogArgument], var_versions: &HashMap<String, usize>) -> Result<InvariantExpr, CFGError> {
        if log_body.len() == 0 {
            return Err(CFGError::UninterpretableLog(None));
        }

        match &log_body[0] {
            LogArgument::LogStr(str) => {
                if str == "invariant" || str == "assume" || str == "assert" || str == "requires" || str == "ensures" {
                    Self::extract_log_invariant(type_inference, vars_and_signals, template_params, parent, &log_body[1..], var_versions)
                }
                else if str.starts_with("forall") {
                    let mut quantified_vars_and_signals: HashMap<String, (usize, NamedStorage)> = vars_and_signals.clone();
                    let mut quantified_var_versions = var_versions.clone();
                    let var_names = Self::extract_quantifier_vars(&str[6..]);
                    for v in &var_names {
                        quantified_var_versions.insert(v.clone(), 0);
                        quantified_vars_and_signals.insert(v.clone(), (quantified_vars_and_signals.len(), NamedStorage::new_variable(v.clone(), parent.clone(), false)));
                    };
                    let expr = Self::extract_log_invariant(type_inference, &quantified_vars_and_signals, template_params, parent, &log_body[1..], &quantified_var_versions)?;
                    Ok(expr.forall(var_names))
                }
                else if str.starts_with("exists") {
                    let mut quantified_vars_and_signals: HashMap<String, (usize, NamedStorage)> = vars_and_signals.clone();
                    let mut quantified_var_versions = var_versions.clone();
                    let var_names = Self::extract_quantifier_vars(&str[6..]);
                    for v in &var_names {
                        quantified_var_versions.insert(v.clone(), 0);
                        quantified_vars_and_signals.insert(v.clone(), (quantified_vars_and_signals.len(), NamedStorage::new_variable(v.clone(), parent.clone(), false)));
                    };
                    let expr = Self::extract_log_invariant(type_inference, &quantified_vars_and_signals, template_params, parent, &log_body[1..], &quantified_var_versions)?;
                    Ok(expr.exists(var_names))
                }
                else {
                    Err(CFGError::UninterpretableLog(Some(str.clone())))
                }
            }
            LogArgument::LogExp(expr) => {
                Ok(Expression::from_ast(type_inference, vars_and_signals, template_params, parent, expr, var_versions)?.into())
            }
        }
    }
}