use std::collections::{HashMap, HashSet};
use program_structure::ast::{Expression, Statement};
use program_structure::program_archive::ProgramArchive;
use typed_arena::Arena;
use serde::{Serialize};
use crate::error::CFGError;
use crate::named_storage::NamedStorage;
use crate::storage_type::TypeInference;
use crate::template::{Template};

pub struct Storage {
    pub(crate) var_arena: Arena<NamedStorage>,
}

#[derive(Serialize)]
pub struct CFG<'glob> {
    //pub ast: &'glob ProgramArchive,
    pub templates: HashMap<String, Template<'glob>>,
    pub entry: String
}

pub trait DotSerialize {
    fn to_dot(&self) -> String;
    fn to_dot_interproc(&self) -> String;
}

impl Storage {
    pub fn new() -> Storage {
        Storage {
            var_arena: Arena::new(),
        }
    }
}

impl<'glob> CFG<'glob> {
    pub fn get_template(&self, name: &String) -> Result<&'glob Template, CFGError>{
        self.templates.get(name).ok_or(CFGError::TemplateNotFound(name.clone()))
    }

    pub fn to_json(&self) -> serde_json::Result<String> {
        serde_json::to_string_pretty(self)
    }

    fn find_calls(expr: &Expression) -> HashSet<String> {
        let mut worklist = Vec::new();
        let mut calls: HashSet<String> = HashSet::new();
        worklist.push(expr);
        while !worklist.is_empty() {
            let cur = worklist.pop().unwrap();
            match cur {
                Expression::InfixOp { lhe, rhe, .. } => {
                    worklist.push(lhe.as_ref());
                    worklist.push(rhe.as_ref());
                }
                Expression::PrefixOp { rhe, .. } => {
                    worklist.push(rhe.as_ref());
                }
                Expression::InlineSwitchOp { cond, if_true, if_false, .. } => {
                    worklist.push(cond.as_ref());
                    worklist.push(if_true.as_ref());
                    worklist.push(if_false.as_ref());
                }
                Expression::ParallelOp { rhe, .. } => {
                    worklist.push(rhe.as_ref());
                }
                Expression::Call { id, args, .. } => {
                    args.iter().for_each(|a| worklist.push(a));
                    calls.insert(id.clone());
                }
                Expression::AnonymousComp { params, signals, .. } => {
                    params.iter().for_each(|p| worklist.push(p));
                    signals.iter().for_each(|s| worklist.push(s));
                }
                Expression::ArrayInLine { values, .. } => {
                    values.iter().for_each(|v| worklist.push(v));
                }
                Expression::Tuple { values, .. } => {
                    values.iter().for_each(|v| worklist.push(v));
                }
                Expression::UniformArray { value, dimension, .. } => {
                    worklist.push(value.as_ref());
                    worklist.push(dimension.as_ref());
                }
                _ => {}
            }
        };

        calls
    }

    fn find_templates_and_fns(_ast: &ProgramArchive, cur: &Statement) -> HashSet<String> {
        let mut worklist = Vec::new();
        let mut calls: HashSet<String> = HashSet::new();
        worklist.push(cur);
        while !worklist.is_empty() {
            let stmt = worklist.pop().unwrap();
            match stmt {
                Statement::IfThenElse { if_case, else_case, cond, .. } => {
                    worklist.push(if_case.as_ref());
                    if let Some(b) = else_case { worklist.push(b.as_ref())};
                    let expr_calls = CFG::find_calls(cond);
                    calls.extend(expr_calls);
                }
                Statement::While { cond, stmt, .. } => {
                    worklist.push(stmt.as_ref());
                    let expr_calls = CFG::find_calls(cond);
                    calls.extend(expr_calls);
                }
                Statement::Return { value, .. } => {
                    let expr_calls = CFG::find_calls(value);
                    calls.extend(expr_calls);
                }
                Statement::InitializationBlock { initializations, .. } => {
                    initializations.iter().for_each(|s| worklist.push(s));
                }
                Statement::Declaration { dimensions, .. } => {
                    for e in dimensions {
                        let expr_calls = CFG::find_calls(e);
                        calls.extend(expr_calls);
                    }
                }
                Statement::Substitution { rhe, .. } => {
                    let expr_calls = CFG::find_calls(rhe);
                    calls.extend(expr_calls);
                }
                Statement::MultSubstitution { lhe, rhe, .. } => {
                    let expr_calls = CFG::find_calls(lhe);
                    calls.extend(expr_calls);
                    let expr_calls = CFG::find_calls(rhe);
                    calls.extend(expr_calls);
                }
                Statement::UnderscoreSubstitution { rhe, .. } => {
                    let expr_calls = CFG::find_calls(rhe);
                    calls.extend(expr_calls);
                }
                Statement::ConstraintEquality { lhe, rhe, .. } => {
                    let expr_calls = CFG::find_calls(lhe);
                    calls.extend(expr_calls);
                    let expr_calls = CFG::find_calls(rhe);
                    calls.extend(expr_calls);
                }
                Statement::LogCall { .. } => {}
                Statement::Block { stmts, .. } => {
                    stmts.iter().for_each(|s| worklist.push(s));
                }
                Statement::Assert { arg, .. } => {
                    let expr_calls = CFG::find_calls(arg);
                    calls.extend(expr_calls);
                }
            }
        }

        calls
    }
    pub fn new(storage: &'glob Storage, ast: &'glob ProgramArchive) -> Result<CFG<'glob>, CFGError> {
        let type_inference = TypeInference::infer_types(ast);
        let entry;
        let mut template_params: HashMap<String, Vec<String>> = HashMap::new();
        for (name, template) in &ast.templates {
            template_params.insert(name.clone(), template.get_name_of_params().clone());
        }

        if let Expression::Call { id, ..} = &ast.get_main_expression() {
            entry = id.clone();
        } else {
            unreachable!("The main expression should be a call.");
        };

        let mut worklist = Vec::new();
        let mut next_id = 0;

        let mut templates = HashMap::new();
        let mut seen = HashSet::new();
        seen.insert(entry.clone());
        worklist.push(entry.clone());
        while !worklist.is_empty() {
            let name = worklist.pop().unwrap();
            if ast.contains_template(&*name) {
                let template_data = ast.get_template_data(&*name);
                let template = Template::new(&type_inference, storage, &template_params, template_data, next_id)?;
                next_id = template.body.keys().fold(next_id, |max, id| if *id > max {*id} else {max}) + 1;
                templates.insert(name.clone(), template);
                let body = template_data.get_body();
                let mut calls = CFG::find_templates_and_fns(&ast, body);
                calls.retain(|c| !seen.contains(c));
                seen.extend(calls.clone());
                worklist.extend(calls);
            }
            else if ast.contains_function(&*name) {
                /* Skip functions as we currently assume function invocations are correct and treat them as uninterpreted functions */
            }
            else {
                unreachable!("Couldn't find name");
            };
        }

        let mut template_entries = HashMap::new();
        for (t_name, t) in &templates {
            template_entries.insert(t_name.clone(), t.entry_id);
        }

        for t in templates.values_mut() {
            next_id = t.build_inter(&template_entries, next_id)?;
            t.finalize();
        }

        Ok(CFG {
            //ast,
            templates,
            entry
        })
    }
}

impl<'glob> DotSerialize for CFG<'glob> {
    fn to_dot(&self) -> String {
        let mut dot = String::from("digraph G {");

        for template in self.templates.values() {
            dot = format!("{}\n{}", dot, template.to_dot());
        };

        dot = format!("{}\n}}", dot);
        dot
    }

    fn to_dot_interproc(&self) -> String {
        let mut dot = String::from("digraph G {");

        for template in self.templates.values() {
            dot = format!("{}\n{}", dot, template.to_dot());
        };

        //for formatting reasons, do interproc after all clusters have been printed
        for template in self.templates.values() {
            dot = String::from(format!("{}\n{}", dot, template.to_dot_interproc()).trim());
        };

        dot = format!("{}\n}}", dot);
        dot
    }
}


