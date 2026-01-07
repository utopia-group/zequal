use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};

use program_structure::ast;
use serde::Serialize;

use crate::error::CFGError;
use crate::expr::expression::Expression;
use crate::expr::invariant::InvariantExpr;
use crate::expr::var_access::{Access, AccessList};
use crate::expr::variable_ref::Ref;
use crate::named_storage::NamedStorage;
use crate::stmt::assert::Assertion;
use crate::stmt::assign_sig::AssignSig;
use crate::stmt::assign_var::AssignVar;
use crate::stmt::assume::Assumption;
use crate::stmt::constrain::Constrain;
use crate::stmt::declaration::{Declaration, VType};
use crate::stmt::log_to_invariant::LogToInvariant;
use crate::storage_type::{CircomType, TypeInference};

pub trait Stmt {
    fn reads(&self) -> HashSet<&Ref>;
    fn writes(&self) -> Option<&Ref>;
}

#[derive(Clone, Serialize, Debug, PartialEq, Eq)]
pub enum Statement {
    Declare(Declaration),
    Assert(Assertion),
    Assume(Assumption),
    AssignVar(AssignVar),
    Constrain(Constrain),
    AssignSig(AssignSig)
}

impl Display for Statement {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Declare(s) => { write!(f, "{s}") }
            Statement::Assert(s) => { write!(f, "{s}") }
            Statement::Assume(s) => { write!(f, "{s}") }
            Statement::AssignVar(s) => { write!(f, "{s}") }
            Statement::Constrain(s) => { write!(f, "{s}") }
            Statement::AssignSig(s) => { write!(f, "{s}") }
        }
    }
}

impl Stmt for Statement {
    fn reads(&self) -> HashSet<&Ref> {
        match self {
            Statement::Declare(s) => { s.reads() }
            Statement::Assert(s) => { s.reads() }
            Statement::Assume(s) => { s.reads() }
            Statement::AssignVar(s) => { s.reads() }
            Statement::Constrain(s) => { s.reads() }
            Statement::AssignSig(s) => { s.reads() }
        }
    }

    fn writes(&self) -> Option<&Ref> {
        match self {
            Statement::Declare(s) => { s.writes() }
            Statement::Assert(s) => { s.writes() }
            Statement::Assume(s) => { s.writes() }
            Statement::AssignVar(s) => { s.writes() }
            Statement::Constrain(s) => { s.writes() }
            Statement::AssignSig(s) => { s.writes() }
        }
    }
}

impl Statement {
    pub fn from_ast(type_inference: &TypeInference, vars_and_signals: &mut HashMap<String, (usize, NamedStorage)>, template_params: &HashMap<String, Vec<String>>, parent: &String, ast_stmt: &ast::Statement, var_versions: &mut HashMap<String, usize>, next_version: &mut HashMap<String, usize>) -> Result<Self, CFGError> {
        match ast_stmt {
            ast::Statement::IfThenElse { .. } => {
                Err(CFGError::UnsupportedStmt("IfThenElse"))
            }
            ast::Statement::While { .. } => {
                Err(CFGError::UnsupportedStmt("While"))
            }
            ast::Statement::Block { .. } => {
                Err(CFGError::UnsupportedStmt("Block"))
            }
            ast::Statement::InitializationBlock { .. } => {
                Err(CFGError::UnsupportedStmt("InitializationBlock"))
            }
            ast::Statement::Return { .. } => {
                Err(CFGError::UnsupportedStmt("Return"))
            }
            ast::Statement::UnderscoreSubstitution { .. } => {
                Err(CFGError::UnsupportedStmt("UnderscoreSubstitution"))
            }
            ast::Statement::Declaration { xtype, is_constant, name, dimensions, meta } => {
                let dims = dimensions.iter().map(|d| Expression::from_ast(type_inference, vars_and_signals, template_params, parent, d, var_versions)).collect::<Result<Vec<Expression>, CFGError>>()?;
                let inferred_type = type_inference.get_template_store_type(parent, name);
                let vtype = match xtype {
                    ast::VariableType::Var => {
                        assert!(inferred_type.is_var());
                        assert_eq!(dims.len(), inferred_type.dims().len());
                        let next_id = *next_version.get(name).unwrap_or(&0);
                        next_version.insert(name.clone(), next_id + 1);
                        var_versions.insert(name.clone(), next_id);
                        VType::Var {is_input: false}
                    }
                    ast::VariableType::Component => {
                        assert!(inferred_type.is_component());
                        assert_eq!(dims.len(), inferred_type.dims().len());
                        let impl_template = match inferred_type {
                            CircomType::Component { implements, .. } => { implements }
                            _ => {unreachable!("How?")}
                        };

                        VType::Component(impl_template)
                    }
                    ast::VariableType::Signal(sig_type, tag_list) => {
                        assert!(inferred_type.is_signal());
                        assert_eq!(dims.len(), inferred_type.dims().len());
                        let tags = tag_list.iter().map(|t| t.clone()).collect();
                        VType::Sig { sig_type: sig_type.into(), tags }
                    }
                    ast::VariableType::AnonymousComponent => {
                        assert!(inferred_type.is_component());
                        assert_eq!(dims.len(), inferred_type.dims().len());
                        let impl_template = match inferred_type {
                            CircomType::Component { implements, .. } => { implements }
                            _ => {unreachable!("How?")}
                        };

                        VType::Component(impl_template)
                    }
                };
                let var = NamedStorage::new_named_storage(name.clone(), parent.clone(), dims.clone(), vtype.clone());
                vars_and_signals.insert(name.clone(), (vars_and_signals.len(), var));
                /*let prev_var = vars_and_signals.insert(name.clone(), (vars_and_signals.len(), var));
                if prev_var.is_some() {
                    return Err(CFGError::VariableAlreadyDeclared(name.clone()))
                }*/
                Ok(Self::new_declaration(vtype, *is_constant, name.clone(), dims))
            }
            ast::Statement::Substitution { var, access, op, rhe, .. } => {
                let access_list = AccessList::<Access>::from_ast(type_inference, vars_and_signals, template_params, parent, access, var_versions)?;
                let rhs = Expression::from_ast(type_inference, vars_and_signals, template_params, parent, rhe, var_versions)?;
                match op {
                    ast::AssignOp::AssignVar => {
                        let lhs = if let Expression::Instantiate(i) = &rhs {
                            let (_, NamedStorage::Component(c)) = vars_and_signals.get_mut(var)
                                .ok_or(CFGError::VariableNotFound(parent.clone(), var.clone()))? else { unreachable!("{} mismatched type in {}", var, parent) };
                            Ref::build_comp_ref(template_params, var.clone(), access_list, String::from(i.name()), var_versions, next_version)?
                        }
                        else {
                            let id = Ref::identifier(var, &access_list);
                            let next = *next_version.get(&id).unwrap_or(&0);
                            var_versions.insert(id.clone(), next);
                            next_version.insert(id, next + 1);
                            Ref::new_var_ref(var.clone(), access_list, next, true, true)
                        };

                        Ok(Self::new_assign_var(lhs, rhs))
                    }
                    ast::AssignOp::AssignSignal => {
                        let lhs = Ref::new_sig_ref(var.clone(), access_list, true, false);
                        Ok(Self::new_assign_sig(lhs, false, rhs))
                    }
                    ast::AssignOp::AssignConstraintSignal => {
                        let lhs = Ref::new_sig_ref(var.clone(), access_list, true, true);
                        Ok(Self::new_assign_sig(lhs, true, rhs))
                    }
                }
            }
            ast::Statement::MultSubstitution { lhe, op, rhe, .. } => {
                let rhs = Expression::from_ast(type_inference, vars_and_signals, template_params, parent, rhe, var_versions)?;
                if let ast::Expression::Variable{ name, access, .. } = lhe {
                    let access_list = AccessList::<Access>::from_ast(type_inference, vars_and_signals, template_params, parent, access, var_versions)?;
                    match op {
                        ast::AssignOp::AssignVar => {
                            let lhs = if let Expression::Instantiate(i) = &rhs {
                                let (_, NamedStorage::Component(c)) = vars_and_signals.get_mut(name)
                                    .ok_or(CFGError::VariableNotFound(parent.clone(), name.clone()))? else { unreachable!("Mismatched type") };
                                Ref::build_comp_ref(template_params, name.clone(), access_list, String::from(i.name()), var_versions, next_version)?
                            }
                            else {
                                let id = Ref::identifier(name, &access_list);
                                let next = *next_version.get(&id).unwrap_or(&0);
                                var_versions.insert(id.clone(), next);
                                next_version.insert(id, next + 1);
                                Ref::new_var_ref(name.clone(), access_list, next, true, true)
                            };

                            Ok(Self::new_assign_var(lhs, rhs))
                        }
                        ast::AssignOp::AssignSignal => {
                            let lhs = Ref::new_sig_ref(name.clone(), access_list, true, false);
                            Ok(Self::new_assign_sig(lhs, true, rhs))
                        }
                        ast::AssignOp::AssignConstraintSignal => {
                            let lhs = Ref::new_sig_ref(name.clone(), access_list, true, true);
                            Ok(Self::new_assign_sig(lhs, true, rhs))
                        }
                    }
                }
                else {
                    Err(CFGError::NotALValue)
                }
            }
            ast::Statement::ConstraintEquality { lhe, rhe, .. } => {
                Ok(Self::new_constraint(Expression::from_ast(type_inference, vars_and_signals, template_params, parent, lhe, var_versions)?, Expression::from_ast(type_inference, vars_and_signals, template_params, parent, rhe, var_versions)?))
            }
            ast::Statement::LogCall { args, .. } => {
                if LogToInvariant::is_assert(args) {
                    let assertion = LogToInvariant::extract_log_invariant(type_inference, vars_and_signals, template_params, parent, args, var_versions)?;
                    Ok(Self::new_assertion(assertion))
                }
                else if LogToInvariant::is_assume(args) {
                    let assumption = LogToInvariant::extract_log_invariant(type_inference, vars_and_signals, template_params, parent, args, var_versions)?;
                    Ok(Self::new_assumption(assumption))
                }
                else {
                    Err(CFGError::UninterpretableLog(None))
                }
            }
            ast::Statement::Assert { arg, .. } => {
                //The circom "asserts" actually act more like assumes because compilation fails if they do not hold
                Ok(Self::new_assumption(Expression::from_ast(type_inference, vars_and_signals, template_params, parent, arg, var_versions)?.into()))
            }
        }
    }

    pub fn new_declaration(v_type: VType, is_const: bool, name: String, dims: Vec<Expression>) -> Self {
        Self::Declare(Declaration::new(v_type, is_const, name, dims))
    }

    pub fn new_assign_var(lhs: Ref, rhs: Expression) -> Self {
        Self::AssignVar(AssignVar::new(lhs, rhs))
    }

    pub fn new_assign_sig(lhs: Ref, constrain: bool, rhs: Expression) -> Self {
        Self::AssignSig(AssignSig::new(lhs, constrain, rhs))
    }

    pub fn new_constraint(lhs: Expression, rhs: Expression) -> Self {
        Self::Constrain(Constrain::new(lhs, rhs))
    }

    pub fn new_assertion(expr: InvariantExpr) -> Self {
        Self::Assert(Assertion::new(expr))
    }

    pub fn new_assumption(expr: InvariantExpr) -> Self {
        Self::Assume(Assumption::new(expr))
    }
}