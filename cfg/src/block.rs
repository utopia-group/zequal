use std::cmp::max;
use std::collections::{HashMap, HashSet, VecDeque};
use program_structure::ast;
use program_structure::ast::{LogArgument};
use crate::cfg::{CFG, DotSerialize};
use crate::edge::{Edge};
use crate::expr::invariant::InvariantExpr;
use crate::stmt::log_to_invariant::LogToInvariant;
use crate::stmt::statement::{Statement, Stmt};
use itertools::Itertools;
use serde::{Serialize};
use crate::error::CFGError;
use crate::expr::expression::{Expr, Expression};
use crate::expr::var_access::{Access, AccessList};
use crate::expr::variable_ref::{ComponentRef, Ref};
use crate::named_storage::{Component, NamedStorage, Signal, Var};
use crate::storage_type::{CircomType, TypeInference};

#[derive(Serialize, Debug)]
pub struct Block {
    pub id: usize,
    pub parent: String,
    entry_versions: HashMap<String, usize>,
    pub stmts: VecDeque<Statement>,
    pub prev: Vec<Edge>,
    pub next: Vec<Edge>
}

impl Block {
    fn new(id: usize, parent: String, entry_versions: HashMap<String, usize>) -> Self {
        Block {
            id,
            parent,
            entry_versions,
            stmts: VecDeque::new(),
            prev: vec![],
            next: vec![]
        }
    }

    fn store_block(self, blocks: &mut HashMap<usize, Self>) {
        let prev = blocks.insert(self.id, self);
        assert!(prev.is_none());
    }

    fn extract_log_invariant(type_inference: &TypeInference, vars_and_signals: & HashMap<String, (usize, NamedStorage)>, template_params: &HashMap<String, Vec<String>>, parent: &String, log_body: &Vec<LogArgument>, var_versions: &HashMap<String, usize>) -> Option<InvariantExpr> {
        if LogToInvariant::is_inv(log_body) {
            let inv = LogToInvariant::extract_log_invariant(type_inference, vars_and_signals, template_params, parent, log_body, var_versions);
            if let Ok(i) = inv {
                Some(i)
            }
            else {
                println!("Could not extract invariant: {}", inv.err().unwrap());
                Option::None
            }
        }
        else {
            Option::None
        }
    }

    fn extract_invariant(type_inference: &TypeInference, vars_and_signals: & HashMap<String, (usize, NamedStorage)>, template_params: &HashMap<String, Vec<String>>, parent: &String, while_body: &ast::Statement, var_versions: &HashMap<String, usize>) -> Option<InvariantExpr> {
        match while_body {
            ast::Statement::LogCall { args, .. } => {
                Self::extract_log_invariant(type_inference, vars_and_signals, template_params, parent, args, var_versions)
            }
            ast::Statement::Block { stmts, .. } => {
                if let Some(s) = stmts.get(0) {
                    Self::extract_invariant(type_inference, vars_and_signals, template_params, parent, s, var_versions)
                }
                else {
                    Option::None
                }
            }
            //_ => {Option::None}
            ast::Statement::IfThenElse { .. } => {Option::None}
            ast::Statement::While { .. } => {Option::None}
            ast::Statement::Return { .. } => {Option::None}
            ast::Statement::InitializationBlock { .. } => {Option::None}
            ast::Statement::Declaration { .. } => {Option::None}
            ast::Statement::Substitution { .. } => {Option::None}
            ast::Statement::MultSubstitution { .. } => {Option::None}
            ast::Statement::UnderscoreSubstitution { .. } => {Option::None}
            ast::Statement::ConstraintEquality { .. } => {Option::None}
            ast::Statement::Assert { .. } => {Option::None}
        }
    }

    fn combine_var_versions(v1: HashMap<String, usize>, v2: HashMap<String, usize>, next_version: &mut HashMap<String, usize>) -> HashMap<String, usize> {
        let mut result = v1;
        for (var, v2_version) in v2 {
            if let Some(v1_version) = result.get(&var) {
                if v1_version != &v2_version {
                    let next = *next_version.get(&var).unwrap_or(&0);
                    result.insert(var.clone(), max(v1_version, &v2_version) + 1);
                    next_version.insert(var, next + 1);
                }
            }
            /*else {
                result.insert(var, v2_version + 1);
            }*/
        }

        result
    }

    fn get_modified_vars(body: &ast::Statement) -> HashSet<String> {
        let mut result = HashSet::new();
        let mut worklist = VecDeque::new();
        worklist.push_back(body);

        while let Some(cur_stmt) = worklist.pop_back() {
            match cur_stmt {
                ast::Statement::IfThenElse { if_case, else_case, .. } => {
                    worklist.push_back(if_case);
                    if let Some(else_stmt) = else_case {
                        worklist.push_back(else_stmt);
                    }
                }
                ast::Statement::While { stmt, .. } => {
                    worklist.push_back(stmt);
                }
                ast::Statement::InitializationBlock { initializations, .. } => {
                    initializations.iter().for_each(|s| worklist.push_back(s));
                }
                ast::Statement::Declaration { xtype, name, .. } => {
                    if xtype == &ast::VariableType::Var {
                        result.insert(name.clone());
                    }
                }
                ast::Statement::Substitution { var, op, access, .. } => {
                    if op == &ast::AssignOp::AssignVar {
                        result.insert(var.clone());
                    }
                    /*if op == &ast::AssignOp::AssignVar {
                        if let Some((_, store)) = vars_and_signals.get(var) {
                            match store {
                                NamedStorage::Variable(v) => {
                                    result.insert(var.clone());
                                }
                                NamedStorage::Component(c) => {
                                    let c_access = access.iter().find(|a| if let ast::Access::ComponentAccess(_) = a { true } else { false });
                                    let new_access = AccessList::from_ast(vars_and_signals, template_params, access, var_versions)?;
                                    let Some(params) = template_params.get(c.instance_of()) else { return Err(CFGError::TemplateNotFound(c.declaring_template().into())) };
                                    if let Some(ast::Access::ComponentAccess(c_name)) = c_access {
                                        let found = params.iter().find(|p| *p == c_name);
                                        if found.is_some() {
                                            let id = Ref::identifier(&c.name().into(), &new_access);
                                            result.insert(id);
                                        }
                                    }
                                    else {
                                        for p in params {
                                            let mut param_access = new_access.clone();
                                            param_access.push(Access::new_component_access(p.clone()))?;
                                            let id = Ref::identifier(&c.name().into(), &param_access);
                                            result.insert(id);
                                        }
                                    }
                                }
                                _ => {  }
                            }
                        }
                    }*/
                }
                ast::Statement::MultSubstitution { lhe, op, .. } => {
                    if let ast::Expression::Variable {name, ..} = lhe {
                        if op == &ast::AssignOp::AssignVar {
                            result.insert(name.clone());
                        }
                    }
                }
                ast::Statement::Block { stmts, .. } => {
                    stmts.iter().for_each(|s| worklist.push_back(s));
                }
                _ => {}
            }
        }

        result
    }

    fn inc_modified_vars(type_inference: &TypeInference, template_params: &HashMap<String, Vec<String>>, parent: &String, mut versions: HashMap<String, usize>, modified: HashSet<String>, next_version: &mut HashMap<String, usize>) -> HashMap<String, usize> {
        for var in modified {
            let circom_type = type_inference.get_template_store_type(parent, &var);
            match circom_type {
                CircomType::Var { .. } => {
                    let next = *next_version.get(&var).unwrap_or(&0);
                    versions.insert(var.clone(), next);
                    next_version.insert(var, next + 1);
                }
                CircomType::Signal { .. } => {/*Do not need to track SSA form for signals*/}
                CircomType::Component { implements, .. } => {
                    /* Components are immutable so variable values cannot be overwritten*/
                }
            }
        }

        versions
    }

    fn build_invoke_edge(vars_and_signals: &mut HashMap<String, (usize, NamedStorage)>, parent: &String, invoke_component: &ComponentRef, local_next: usize, local_prev: usize) -> Result<Edge, CFGError> {
        let store_opt = vars_and_signals.get(invoke_component.name());
        match store_opt {
            None => {Err(CFGError::VariableNotFound(parent.clone(), invoke_component.name().into()))}
            Some((_, NamedStorage::Component(component))) => {
                Edge::new_call(parent.clone(), invoke_component.invoked().into(), component.name().into(), invoke_component.access().clone(), 0, local_next, local_prev)
            }
            _ => {
                Err(CFGError::InvalidComponentAccess(invoke_component.name().into()))
            }
        }
    }

    fn build_intra_helper(type_inference: &TypeInference, vars_and_signals: &mut HashMap<String, (usize, NamedStorage)>, template_params: &HashMap<String, Vec<String>>, parent: &String, blocks: &mut HashMap<usize, Self>, mut id: usize, body: &ast::Statement, mut var_versions: HashMap<String, usize>, next_version: &mut HashMap<String, usize>) -> Result<(usize, Self, usize, HashMap<String, usize>, Option<InvariantExpr>, Option<InvariantExpr>, bool), CFGError> {
        let mut worklist = VecDeque::new();
        worklist.push_back(body);

        let mut requires = None;
        let mut ensures = None;
        let mut assume_invocation_consistent = false;

        let entry_id = id;
        let mut cur_block = Block::new(entry_id, parent.clone(), var_versions.clone());
        id += 1;

        while let Some(cur_stmt) = worklist.pop_front() {
            match cur_stmt {
                ast::Statement::IfThenElse { if_case, else_case: maybe_else, cond: ast_cond, .. } => {
                    // Translate conditional
                    let cond = Expression::from_ast(type_inference, vars_and_signals, template_params, parent, ast_cond, &var_versions)?;

                    // Allocate ID for after the conditional
                    let post_id = id;
                    id += 1;

                    // create if body
                    let (if_entry_id, mut if_exit_block, next_id, if_branch_versions, block_requires, block_ensures, ensure_consistent) = Block::build_intra_helper(type_inference, vars_and_signals, template_params, parent, blocks, id, if_case, var_versions.clone(), next_version)?;
                    assume_invocation_consistent = assume_invocation_consistent || ensure_consistent;
                    if !block_requires.is_none() {
                        panic!("Error: requires statement cannot be in a conditional block");
                    }

                    if !block_ensures.is_none() {
                        panic!("Error: requires statement cannot be in a conditional block");
                    }
                    id = next_id;

                    // Connect if body and store
                    cur_block.next.push(Edge::new_if(parent.clone(), cur_block.id, cond.clone(), if_entry_id)?);
                    if_exit_block.next.push(Edge::new_if_exit(parent.clone(), if_exit_block.id, cond.clone(), post_id)?);
                    if_exit_block.store_block(blocks);

                    let else_branch_versions = if let Some(else_case) = maybe_else {
                        // create else body
                        let (else_entry_id  , mut else_exit_block, next_id, else_branch_versions, block_requires, block_ensures, ensure_consistent) = Block::build_intra_helper(type_inference, vars_and_signals, template_params, parent, blocks, id, else_case, var_versions.clone(), next_version)?;
                        assume_invocation_consistent = assume_invocation_consistent || ensure_consistent;
                        if !block_requires.is_none() {
                            panic!("Error: requires statement cannot be in a conditional block");
                        }

                        if !block_ensures.is_none() {
                            panic!("Error: requires statement cannot be in a conditional block");
                        }
                        id = next_id;

                        // Connect else body and store
                        cur_block.next.push(Edge::new_else(parent.clone(), cur_block.id, cond.clone(), else_entry_id)?);
                        else_exit_block.next.push(Edge::new_else_exit(parent.clone(), else_exit_block.id, cond, post_id)?);
                        else_exit_block.store_block(blocks);

                        else_branch_versions
                    }
                    else {
                        // if there is no else, still go through a dummy block so we still have else entry and exit edges
                        let mut dummy_block = Block::new(id, parent.clone(), var_versions.clone());
                        id += 1;

                        // Connect dummy block and store
                        cur_block.next.push(Edge::new_else(parent.clone(), cur_block.id, cond.clone(), dummy_block.id)?);
                        dummy_block.next.push(Edge::new_else_exit(parent.clone(), dummy_block.id, cond, post_id)?);
                        dummy_block.store_block(blocks);

                        var_versions
                    };

                    // Store block before if statement
                    cur_block.store_block(blocks);

                    // Combine variables in the conditionals
                    var_versions = Self::combine_var_versions(if_branch_versions, else_branch_versions, next_version);

                    // Create the block that follows the if-statement
                    cur_block = Block::new(post_id, parent.clone(), var_versions.clone());
                }
                ast::Statement::While { stmt, cond: ast_cond, .. } => {
                    // get modified vars
                    let modified_vars = Self::get_modified_vars(stmt);
                    var_versions = Self::inc_modified_vars(type_inference, template_params, parent, var_versions, modified_vars, next_version);

                    // Translate Conditional and extract invariant
                    let cond = Expression::from_ast(type_inference, vars_and_signals, template_params, parent, ast_cond, &var_versions)?;
                    let invariant_expr = Self::extract_invariant(type_inference, vars_and_signals, template_params, parent, stmt, &var_versions);

                    // Create Loop Head and loop exit
                    let mut loop_head = Block::new(id, parent.clone(), var_versions.clone());
                    let loop_exit = Block::new(id + 1, parent.clone(), var_versions.clone());
                    id += 2;

                    // Create loop body
                    let (loop_entry_id, mut loop_exit_block, next_id, _, block_requires, block_ensures, ensure_consistent) = Block::build_intra_helper(type_inference, vars_and_signals, template_params, parent, blocks, id, stmt, var_versions.clone(), next_version)?;
                    assume_invocation_consistent = assume_invocation_consistent || ensure_consistent;
                    id = next_id;

                    if !block_requires.is_none() {
                        panic!("Error: requires statement cannot be in a while loop");
                    }

                    if !block_ensures.is_none() {
                        panic!("Error: requires statement cannot be in a while loop");
                    }

                    // Connect loop head and store pre-loop block
                    cur_block.next.push(Edge::new_continue(parent.clone(), cur_block.id, loop_head.id)?);
                    cur_block.store_block(blocks);

                    // Connect back-edge and store
                    loop_exit_block.next.push(Edge::new_backedge(parent.clone(), loop_exit_block.id, loop_head.id)?);
                    loop_exit_block.store_block(blocks);

                    // Connect loop body and exit, then store
                    loop_head.next.push(Edge::new_loop_entry(parent.clone(), loop_head.id, cond.clone(), invariant_expr.clone(), loop_entry_id)?);
                    loop_head.next.push(Edge::new_loop_exit(parent.clone(), loop_head.id, cond, invariant_expr.clone(), loop_exit.id)?);
                    loop_head.store_block(blocks);
                    cur_block = loop_exit;
                }
                ast::Statement::Return { .. } => {
                    return Err(CFGError::UnsupportedStmt("Return"))
                }
                ast::Statement::InitializationBlock { initializations, .. } => {
                    initializations.iter().rev().for_each(|s| worklist.push_front(s));
                }
                ast::Statement::Block { stmts, .. } => {
                    stmts.iter().rev().for_each(|s| worklist.push_front(s));
                }
                ast::Statement::LogCall { args, ..} => {
                    if LogToInvariant::is_assume_consistent(args) {
                        assume_invocation_consistent = true;
                    }
                    if LogToInvariant::is_invoke(args) {
                        let component_ref = LogToInvariant::extract_template_invocation(type_inference, vars_and_signals, template_params, parent, &var_versions, args)?;
                        let next_id = id;
                        id += 1;
                        let call_edge = Self::build_invoke_edge(vars_and_signals, parent, &component_ref, next_id, cur_block.id.clone())?;
                        cur_block.next.push(call_edge);
                        cur_block.store_block(blocks);
                        cur_block = Block::new(next_id, parent.clone(), var_versions.clone());
                    }
                    else if LogToInvariant::is_ensures(args) {
                        if !ensures.is_none() {
                            panic!("Error: Found multiple ensures declarations for template {}", parent);
                        }
                        let ensures_expr = LogToInvariant::extract_log_invariant(type_inference, vars_and_signals, template_params, parent, args, &var_versions)?;
                        for v_ref in ensures_expr.variable_refs() {
                            match type_inference.get_template_store_type(parent, &String::from(v_ref.name())) {
                                CircomType::Var { is_input, .. } => {
                                    if !is_input {
                                        panic!("Ensures declaration in {} must only use inputs and outputs, found non-input variable {}", parent, v_ref.name())
                                    }
                                }
                                CircomType::Signal { is_input, is_output, .. } => {
                                    if !is_input && !is_output {
                                        panic!("Ensures declaration in {} must only use inputs and outputs, found intermediate signal {}", parent, v_ref.name())
                                    }
                                }
                                CircomType::Component { .. } => {
                                    panic!("Ensures declaration in {} must only use inputs and outputs, found component {}", parent, v_ref.name())
                                }
                            }
                        }
                        ensures = Some(ensures_expr)
                    }
                    else if LogToInvariant::is_requires(args) {
                        if !requires.is_none() {
                            panic!("Error: Found multiple ensures declarations for template {}", parent);
                        }
                        let requires_expr = LogToInvariant::extract_log_invariant(type_inference, vars_and_signals, template_params, parent, args, &var_versions)?;
                        for v_ref in requires_expr.variable_refs() {
                            match type_inference.get_template_store_type(parent, &String::from(v_ref.name())) {
                                CircomType::Var { is_input, .. } => {
                                    if !is_input {
                                        panic!("Requires declaration in {} must only use inputs, found non-input variable {}", parent, v_ref.name())
                                    }
                                }
                                CircomType::Signal { is_input, is_output, .. } => {
                                    if !is_input {
                                        panic!("Ensures declaration in {} must only use inputs, found intermediate or input signal {}", parent, v_ref.name())
                                    }
                                }
                                CircomType::Component { .. } => {
                                    panic!("Ensures declaration in {} must only use inputs, found component {}", parent, v_ref.name())
                                }
                            }
                        }
                        requires = Some(requires_expr)
                    }
                    else {
                        let stmt_res = Statement::from_ast(type_inference, vars_and_signals, template_params, parent, cur_stmt, &mut var_versions, next_version);
                        match stmt_res {
                            Ok(stmt) => {cur_block.stmts.push_back(stmt);}
                            Err(e) => {
                                match e {
                                    CFGError::UninterpretableLog(_) => {
                                        println!("Warning: Could not interpret log as an invariant")
                                    }
                                    _ => { return Err(e) }
                                }
                            }
                        }
                    }
                }
                _ => {
                    let stmt = Statement::from_ast(type_inference, vars_and_signals, template_params, parent, cur_stmt, &mut var_versions, next_version)?;
                    cur_block.stmts.push_back(stmt);
                }
            }
        }

        Ok((entry_id, cur_block, id, var_versions, requires, ensures, assume_invocation_consistent))
    }

    pub(crate) fn build_intra(type_inference: &TypeInference, vars_and_signals: &mut HashMap<String, (usize, NamedStorage)>, template_params: &HashMap<String, Vec<String>>, parent: &String, blocks: &mut HashMap<usize, Self>, id: usize, body: &ast::Statement, var_versions: HashMap<String, usize>, next_version: &mut HashMap<String, usize>) -> Result<(usize, usize, usize, Option<InvariantExpr>, Option<InvariantExpr>, bool), CFGError> {
        let (entry_id, exit_block, id, _, requires, ensures, assume_invocation_consistent) = Block::build_intra_helper(type_inference, vars_and_signals, template_params, parent, blocks, id, body, var_versions, next_version)?;
        let exit_id = exit_block.id;
        exit_block.store_block(blocks);
        Ok((entry_id, exit_id, id, requires, ensures, assume_invocation_consistent))
    }

    pub fn is_loop_head(&self) -> bool {
        for e in &self.next {
            if let Edge::LoopEntry(_) = e {
                return true;
            }
        }

        return false;
    }

    pub fn var_versions_at(&self, loc: usize) -> HashMap<String, usize> {
        let mut new_versions = self.entry_versions.clone();
        for i in 0..loc {
            let stmt = self.stmts.get(i).unwrap();
            match stmt {
                Statement::AssignVar(assignment) => {
                    let assigned = assignment.writes();
                    for a in assigned {
                        match a {
                            Ref::Var(v) => {
                                new_versions.insert(v.var_id().clone(), v.version());
                            }
                            Ref::Comp(c) => {
                                for param in c.params() {
                                    new_versions.insert(param.var_id().clone(), param.version());
                                }
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }

        new_versions
    }

    pub fn ref_var_before(&self, var: &Var, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool, at: usize) -> Result<Ref, CFGError> {
        let var_versions = self.var_versions_at(at);
        Ref::create_var_ref(&var_versions, &self.parent, var, access, ref_witness, ref_constraint)
    }

    pub fn ref_sig_before(&self, sig: &Signal, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool, at: usize) -> Result<Ref, CFGError> {
        //signals will always be same
        Ref::create_sig_ref(sig, access, ref_witness, ref_constraint)
    }

    pub fn ref_component_before(&self, cfg: &CFG, comp: &Component, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool, at: usize) -> Result<Ref, CFGError> {
        let var_versions = self.var_versions_at(at);
        Ref::create_component_ref(cfg, &self.parent, &var_versions, comp, access, ref_witness, ref_constraint)
    }

    pub fn pre_ref_var(&self, var: &Var, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError>  {
        Ref::create_var_ref(self.entry_versions(), &self.parent, var, access, ref_witness, ref_constraint)
    }

    pub fn pre_ref_sig(&self, sig: &Signal, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        Ref::create_sig_ref(sig, access, ref_witness, ref_constraint)
    }

    pub fn pre_ref_component(&self, cfg: &CFG, comp: &Component, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        Ref::create_component_ref(cfg, &self.parent, self.entry_versions(), comp, access, ref_witness, ref_constraint)
    }

    pub fn pre_ref(&self, cfg: &CFG, store: &NamedStorage, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        Ref::create_ref(cfg, &self.parent, self.entry_versions(), store, access, ref_witness, ref_constraint)
    }

    pub fn post_ref_var(&self, var: &Var, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        Ref::create_var_ref(&self.exit_versions(), &self.parent, var, access, ref_witness, ref_constraint)
    }

    pub fn post_ref_sig(&self, sig: &Signal, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        Ref::create_sig_ref(sig, access, ref_witness, ref_constraint)
    }

    pub fn post_ref_component(&self, cfg: &CFG, comp: &Component, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        Ref::create_component_ref(cfg, &self.parent, &self.exit_versions(), comp, access, ref_witness, ref_constraint)
    }

    pub fn post_ref(&self, cfg: &CFG, store: &NamedStorage, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        Ref::create_ref(cfg, &self.parent, &self.exit_versions(), store, access, ref_witness, ref_constraint)
    }

    pub fn exit_versions(&self) -> HashMap<String, usize> {
        self.var_versions_at(self.stmts.len())
    }

    pub fn entry_versions(&self) -> &HashMap<String, usize> {
        &self.entry_versions
    }

    pub fn split(&mut self, loc: usize, new_id: usize) -> Self {
        let mut blk = Block::new(new_id, self.parent.clone(), self.var_versions_at(loc));
        blk.stmts = self.stmts.split_off(loc);
        while !self.next.is_empty() {
            let mut edge = self.next.pop().unwrap();
            edge.set_source(new_id);
            blk.next.push(edge);
        }
        blk
    }

    pub fn add_edge(&mut self, edge: Edge) {
        self.next.push(edge);
    }

    pub fn reads(&self) -> HashSet<&Ref> {
        let mut reads = HashSet::new();
        for stmt in &self.stmts {
            reads.extend(stmt.reads());
        }

        reads
    }

    pub fn writes(&self) -> HashSet<&Ref> {
        let mut writes = HashSet::new();
        for stmt in &self.stmts {
            match stmt.writes() {
                None => { /* Skip */ }
                Some(r) => { writes.insert(r); }
            }
        }

        writes
    }

    pub fn reads_and_writes(&self) -> (HashSet<&Ref>, HashSet<&Ref>) {
        let mut reads = HashSet::new();
        let mut writes = HashSet::new();
        for stmt in &self.stmts {
            reads.extend(stmt.reads());
            writes.extend(stmt.writes());
        }

        (reads, writes)
    }
}

impl DotSerialize for Block {
    fn to_dot(&self) -> String {
        let body_str =  self.stmts.iter().join(" \\n ");
        let mut dot = format!("    B{} [label=\"{}\"];", self.id, body_str);
        for edge in &self.prev {
            dot = format!("{}\n{}", dot, edge.to_dot());
        };

        dot
    }

    fn to_dot_interproc(&self) -> String {
        let mut dot= String::default();
        for edge in &self.prev {
            dot = String::from(format!("{}\n{}", dot, edge.to_dot_interproc()).trim());
        };

        dot
    }
}