use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};
use itertools::Itertools;
use program_structure::ast;
use serde::{Serialize};
use crate::error::CFGError;
use crate::expr::expression::{Expr, Expression};
use crate::expr::variable_ref::Ref;
use crate::named_storage::NamedStorage;
use crate::storage_type::TypeInference;

#[derive(Clone, PartialEq, Eq, Serialize, Debug)]
pub enum Access {
    Array{ ind: Expression },
    Component{ name: String }
}

pub trait StorageAccess: Sized + Clone + Display {
    fn is_array_access(&self) -> bool;
    fn is_component_access(&self) -> bool;
    fn get_array_access(&self) -> Option<&Expression>;
    fn get_component_access(&self) -> Option<&String>;
    fn rename(&self, from: &Ref, to: &Ref) -> Result<Self, CFGError>;
    fn variable_refs(&self) -> HashSet<&Ref>;
}

#[derive(Clone, PartialEq, Eq, Serialize, Debug)]
pub struct AccessList<A: StorageAccess> {
    access: Vec<A>
}

impl StorageAccess for Access {
    fn is_component_access(&self) -> bool {
        if let Access::Component { .. } = self {
            true
        }
        else {
            false
        }
    }

    fn is_array_access(&self) -> bool {
        if let Access::Array { .. } = self {
            true
        }
        else {
            false
        }
    }

    fn get_array_access(&self) -> Option<&Expression> {
        match self {
            Access::Array { ind } => { Some(ind) }
            Access::Component { .. } => { None }
        }
    }

    fn get_component_access(&self) -> Option<&String> {
        match self {
            Access::Array { .. } => { None }
            Access::Component { name } => { Some(name) }
        }
    }

    fn rename(&self, from: &Ref, to: &Ref) -> Result<Self, CFGError> {
        match self {
            Access::Array { ind } => {
                Ok(Self::Array { ind: ind.rename(from, to)? })
            }
            Access::Component { .. } => {
                Ok(self.clone())
            }
        }
    }

    fn variable_refs(&self) -> HashSet<&Ref> {
        match self {
            Access::Array { ind } => {
                ind.variable_refs()
            }

            Access::Component { .. } => {
                HashSet::new()
            }
        }
    }
}

impl Access {

    pub fn from_ast(type_inference: &TypeInference, vars_and_signals: & HashMap<String, (usize, NamedStorage)>, template_params: &HashMap<String, Vec<String>>, parent: &String, access: &ast::Access, var_versions: &HashMap<String, usize>) -> Result<Self, CFGError> {
        match access {
            ast::Access::ComponentAccess(name) => {
                Ok(Self::Component { name: name.clone() })
            }
            ast::Access::ArrayAccess(ind) => {
                Ok(Self::Array { ind: Expression::from_ast(type_inference, vars_and_signals, template_params, parent, ind, var_versions)? } )
            }
        }
    }

    pub fn new_component_access(name: String) -> Access {
        Access::Component { name }
    }

    pub fn new_array_access(ind: Expression) -> Access {
        Access::Array { ind }
    }
}

impl<A: StorageAccess> AccessList<A> {
    pub fn variable_refs(&self) -> HashSet<&Ref> {
        let mut refs = HashSet::new();
        for acc in &self.access {
            refs.extend(acc.variable_refs());
        }

        refs
    }

    pub fn len(&self) -> usize {
        self.access.len()
    }

    pub fn list(&self) -> &Vec<A> {
        &self.access
    }

    pub fn from_ast(type_inference: &TypeInference, vars_and_signals: &HashMap<String, (usize, NamedStorage)>, template_params: &HashMap<String, Vec<String>>, parent: &String, access: &Vec<ast::Access>, var_versions: &HashMap<String, usize>) -> Result<AccessList<Access>, CFGError> {
        let access_list: Vec<Access> = access.iter().map(|a| Access::from_ast(type_inference, vars_and_signals, template_params, parent, a, var_versions)).collect::<Result<Vec<Access>, CFGError>>()?;
        AccessList::<Access>::new(access_list)
    }

    pub fn new(access: Vec<A>) -> Result<AccessList<A>, CFGError> {
        let count = access.iter().filter(|a| a.is_component_access()).count();
        if count > 1 {
            return Err(CFGError::MultipleComponentAccess(String::default(), count));
        }

        Ok(Self { access })
    }

    pub fn empty() -> AccessList<A> {
        Self { access: vec![] }
    }

    pub fn push(&mut self, access: A) -> Result<(), CFGError> {
        if access.is_component_access() {
            let component_access = self.get_component_access();
            match component_access {
                None => {
                    self.access.push(access);
                    Ok(())
                }
                Some(_) => { Err(CFGError::MultipleComponentAccess(String::default(), 2)) }
            }
        }
        else {
            self.access.push(access);
            Ok(())
        }
    }

    pub fn slice(&self, start: usize, end: usize) -> AccessList<A> {
        Self { access: self.access[start..end].to_vec() }
    }

    pub fn get(&self, ind: usize) -> &A {
        &self.access[ind]
    }

    pub fn iter(&self) -> impl Iterator<Item=&A> {
        self.access.iter()
    }

    // There should only be a single component access unless this is an invariant
    pub fn get_component_access(&self) -> Option<&String> {
        for a in &self.access {
            if a.is_component_access() {
                return a.get_component_access()
            }
        }

        None
    }

    pub fn get_component_access_ind(&self) -> Option<usize> {
        for i in 0..self.access.len() {
            if self.access[i].is_component_access() {
                return Some(i);
            }
        }
        None
    }

    pub fn rename(&self, from: &Ref, to: &Ref) -> Result<Self, CFGError> {
        let access_list = self.access.iter().map(|a| a.rename(from, to)).collect::<Result<Vec<_>, _>>()?;
        Ok(Self { access: access_list })
    }

    pub fn rename_all(&self, renamings: &HashMap<Ref, Ref>) -> Result<Self, CFGError> {
        let mut ret: Self = self.clone();
        for (from, to) in renamings {
            ret = ret.rename(from, to)?;
        }

        Ok(ret)
    }
}

impl Display for Access {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Access::Array { ind, .. } => { write!(f, "[{}]", ind) }
            Access::Component { name, .. } => { write!(f, ".{}", name) }
        }
    }
}

impl<A: StorageAccess> Display for AccessList<A> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.access.iter().join(""))
    }
}