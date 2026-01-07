use std::cmp::{max, min};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::str::FromStr;
use itertools::Itertools;
use num_bigint_dig::BigInt;
use program_structure::template_data::TemplateData;
use serde::{Serialize};
use crate::block::{Block};
use crate::cfg::{Storage, DotSerialize, CFG};
use crate::edge::Edge;
use crate::error::CFGError;
use crate::expr::var_access::{Access, AccessList};
use crate::expr::expression::{Expr, Expression};
use crate::expr::invariant::InvariantExpr;
use crate::expr::variable_ref::{ComponentRef, Ref, SignalRef, VarRef};
use crate::named_storage::{Component, NamedStorage, Signal, Var};
use crate::stmt::declaration::VType;
use crate::stmt::statement::Statement;
use crate::storage_type::TypeInference;

#[derive(Serialize, Debug)]
pub struct Template<'cfg> {
    pub name: String,
    pub input_vars: Vec<&'cfg Var>,
    pub input_signals: Vec<&'cfg Signal>,
    pub output_signals: Vec<&'cfg Signal>,
    //components: Vec<&'glob Component>,
    pub components: HashMap<String, &'cfg Component>,
    pub vars_and_signals: HashMap<String, &'cfg NamedStorage>,
    pub entry_id: usize,
    pub exit_id: usize,
    pub body: HashMap<usize, Block>,
    requires: Option<InvariantExpr>,
    ensures: Option<InvariantExpr>,
    assume_invocation_consistent: bool
}

impl<'glob> Hash for Template<'glob> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state)
    }
}

impl<'glob> PartialEq for Template<'glob> {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl<'glob> Eq for Template<'glob> {}

impl<'glob> Template<'glob> {
    pub fn name(&self) -> String {
        self.name.clone()
    }

    pub fn has_requires(&self) -> bool {
        self.requires.is_some()
    }

    pub fn requires(&self) -> &Option<InvariantExpr> {
        &self.requires
    }

    pub fn has_ensures(&self) -> bool {
        self.ensures.is_some()
    }

    pub fn ensures(&self) -> &Option<InvariantExpr> {
        &self.ensures
    }

    pub fn assume_invocation_is_consistent(&self) -> bool {
        self.assume_invocation_consistent
    }

    pub fn alloc_vars(storage: &'glob Storage, all_storage: HashMap<String, (usize, NamedStorage)>) -> Result<(HashMap<String, &'glob NamedStorage>, Vec<&'glob Var>, Vec<&'glob Signal>, Vec<&'glob Signal>, HashMap<String, &'glob Component>), CFGError> {
        let mut vars_and_signals = HashMap::new();
        let mut input_vars = vec![];
        let mut input_sigs = vec![];
        let mut output_sigs = vec![];
        let mut components = HashMap::new();

        for (name, (_, store)) in all_storage.into_iter().sorted_by(|(_, (i1, _)), (_, (i2, _))| i1.cmp(i2)) {
            let alloc_store: &NamedStorage = storage.var_arena.alloc(store);
            match alloc_store {
                NamedStorage::Variable(v) => {
                    if v.is_input() {
                        input_vars.push(v);
                    }
                }
                NamedStorage::Signal(s) => {
                    if s.is_input() {
                        input_sigs.push(s);
                    }
                    if s.is_output() {
                        output_sigs.push(s);
                    }
                }
                NamedStorage::Component(c) => {
                    components.insert(name.clone(), c);
                }
            }

            vars_and_signals.insert(name, alloc_store);
        }

        Ok((vars_and_signals, input_vars, input_sigs, output_sigs, components))
    }

    pub fn new(type_inference: &TypeInference, storage: &'glob Storage, template_params: &HashMap<String, Vec<String>>, ast_template: &'glob TemplateData, start_id: usize) -> Result<Template<'glob>, CFGError> {
        let template_name = String::from(ast_template.get_name());
        let mut var_versions = HashMap::new();
        let mut next_version = HashMap::new();
        let mut all_storage: HashMap<String, (usize, NamedStorage)> = HashMap::new();
        for var in ast_template.get_name_of_params() {
            let inferred_type = type_inference.get_template_store_type(&template_name, var);
            // We don't trust the actual size of the dimension as it may be related to main's input. It shouldn't matter as we don't use variable dimensions
            // anywhere (pretty sure) but just in case we will set this to an arbitrairly large number
            let mut dims = vec![];
            for _ in inferred_type.dims() {
                dims.push(Expression::new_number(BigInt::from_str("100000000000000000000000000000000000").unwrap()));
            }
            all_storage.insert(var.clone(), (all_storage.len(), NamedStorage::new_named_storage(var.clone(), template_name.clone(), dims, VType::Var {is_input: true} )));
            var_versions.insert(var.clone(), 0);
            next_version.insert(var.clone(), 1);
        }

        let mut body = HashMap::new();
        let (entry_id, exit_id, _, requires, ensures, assume_invocation_consistent) = Block::build_intra(type_inference, &mut all_storage, template_params, &template_name, &mut body, start_id, ast_template.get_body(), var_versions, &mut next_version)?;
        let (vars_and_signals, input_vars, input_signals, output_signals, components) = Template::alloc_vars(storage, all_storage)?;

        Ok(Template {
            name: template_name,
            input_vars,
            input_signals,
            output_signals,
            components,
            vars_and_signals,
            entry_id,
            exit_id,
            body,
            requires,
            ensures,
            assume_invocation_consistent
        })
    }

    pub fn get_dominators(&self) -> Result<HashMap<usize, HashSet<usize>>, CFGError> {
        let mut tree = HashMap::new();
        let mut prev_edges: HashMap<usize, Vec<usize>> = HashMap::new();

        for (bid, blk) in &self.body {
            let dominators = if bid == &self.entry_id {
                let mut dominators = HashSet::new();
                dominators.insert(*bid);
                dominators
            }
            else {
                self.body.keys().map(|v| *v).collect()
            };

            for next in &blk.next {
                let next_node = next.local_next();
                if let Some(prev_nodes) = prev_edges.get_mut(&next_node) {
                    prev_nodes.push(*bid)
                }
                else {
                    prev_edges.insert(next_node, vec![*bid]);
                }
            }

            tree.insert(*bid, dominators);
        }

        let mut changed = true;
        while changed {
            changed = false;
            for (bid, _) in &self.body {
                let mut pre_doms: Option<HashSet<usize>> = None;

                for prev in prev_edges.get(bid).unwrap_or(&Vec::<usize>::default()) {
                    let destination_doms = tree.get(prev).ok_or(CFGError::BlockNotFound(*prev))?;
                    pre_doms = match pre_doms {
                        Some(doms) => {
                            Some(doms.intersection(destination_doms).map(|v| *v).collect())
                        }
                        None => {
                            Some(destination_doms.clone())
                        }
                    }
                }

                let cur_doms = tree.get(&bid).ok_or(CFGError::BlockNotFound(*bid))?;
                if let Some(mut doms) = pre_doms {
                    doms.insert(*bid);
                    if &doms != cur_doms {
                        tree.insert(*bid, doms);
                        changed = true;
                    }
                }
            }
        }

        Ok(tree)
    }

    pub fn get_post_dominators(&self) -> Result<HashMap<usize, HashSet<usize>>, CFGError> {
        let mut tree = HashMap::new();

        for bid in self.body.keys() {
            let dominators = if bid == &self.exit_id {
                let mut dominators = HashSet::new();
                dominators.insert(*bid);
                dominators
            }
            else {
                self.body.keys().map(|v| *v).collect()
            };

            tree.insert(*bid, dominators);
        }

        let mut changed = true;
        while changed {
            changed = false;
            for (bid, blk) in &self.body {
                let edges = &blk.next;
                let mut post_doms: Option<HashSet<usize>> = None;

                for edge in edges {
                    let destination = edge.local_next();
                    let destination_doms = tree.get(&destination).ok_or(CFGError::BlockNotFound(destination))?;
                    post_doms = match post_doms {
                        Some(doms) => {
                            Some(doms.intersection(destination_doms).map(|v| *v).collect())
                        }
                        None => {
                            Some(destination_doms.clone())
                        }
                    }
                }

                let cur_doms = tree.get(&bid).ok_or(CFGError::BlockNotFound(*bid))?;
                if let Some(mut doms) = post_doms {
                    doms.insert(*bid);
                    if &doms != cur_doms {
                        tree.insert(*bid, doms);
                        changed = true;
                    }
                }
            }
        }

        Ok(tree)
    }

    fn get_component_access(&self, name: &str, access: &AccessList<Access>) -> (String, AccessList<Access>) {
        let c = self.components.get(name).unwrap();
        let maybe_access = access.get_component_access();
        if let Some(component_access) = maybe_access {
            (component_access.clone(), access.slice(0, c.dims().len()))
        }
        else {
            if c.dims().len() == access.len() {
                (String::default(), access.clone())
            }
            else {
                unreachable!("components do not match")
            }
        }
    }

    fn find_invocation_site(&self, manually_invoked: HashSet<String>) -> Result<HashMap<usize, BTreeMap<usize, Vec<(String, AccessList<Access>)>>>, CFGError> {
        let post_dominators = self.get_post_dominators()?;
        let dominators = self.get_dominators()?;
        let mut input_locs: HashMap<String, HashMap<String, Vec<(usize, usize, &Statement, AccessList<Access>)>>> = HashMap::new();
        let mut output_locs: HashMap<String, HashMap<String, Vec<(usize, usize, &Statement, AccessList<Access>)>>> = HashMap::new();
        let mut components: HashSet<&str> = HashSet::new();

        for c in self.components.values() {
            if !manually_invoked.contains(c.name()) {
                input_locs.insert(c.name().into(), HashMap::new());
                output_locs.insert(c.name().into(), HashMap::new());
                components.insert(c.name());
            }
        }

        // find input/output locations
        for (bid, blk) in &self.body {
            for (i, stmt) in blk.stmts.iter().enumerate() {
                match stmt {
                    Statement::AssignVar(a) => {
                        if components.contains(a.lhs().name()) {
                            let (accessed, template_access) = self.get_component_access(a.lhs().name(), a.lhs().access());
                            let mut locs = input_locs.get_mut(a.lhs().name()).unwrap().remove(&accessed).unwrap_or(vec![]);
                            locs.push((*bid, i, stmt, template_access));
                            input_locs.get_mut(a.lhs().name()).unwrap().insert(accessed, locs);
                        }
                        let rhs_components: Vec<&Ref> = a.rhs()
                            .variable_refs()
                            .into_iter()
                            .filter(|v| components.contains(v.name()))
                            .collect();
                        //let rhs_components = NamedStorage::get_accesses(a.rhs(), &components);
                        for var in rhs_components {
                            let (accessed, template_access) = self.get_component_access(var.name(), var.access());
                            let mut locs = output_locs.get_mut(var.name()).unwrap().remove(&accessed).unwrap_or(vec![]);
                            locs.push((*bid, i, stmt, template_access));
                            output_locs.get_mut(var.name()).unwrap().insert(accessed, locs);
                        }
                    }
                    Statement::AssignSig(a) => {
                        if components.contains(a.lhs().name()) {
                            let (accessed, template_access) = self.get_component_access(&a.lhs().name(), a.lhs().access());
                            let mut locs = input_locs.get_mut(a.lhs().name()).unwrap().remove(&accessed).unwrap_or(vec![]);
                            locs.push((*bid, i, stmt, template_access));
                            input_locs.get_mut(a.lhs().name()).unwrap().insert(accessed, locs);
                        }
                        let rhs_components: Vec<&Ref> = a.rhs()
                            .variable_refs()
                            .into_iter()
                            .filter(|v| components.contains(v.name()))
                            .collect();
                        //let rhs_components = NamedStorage::get_accesses(a.rhs(), &components);
                        for var in rhs_components {
                            let (accessed, template_access) = self.get_component_access(var.name(), var.access());
                            let mut locs = output_locs.get_mut(var.name()).unwrap().remove(&accessed).unwrap_or(vec![]);
                            locs.push((*bid, i, stmt, template_access));
                            output_locs.get_mut(var.name()).unwrap().insert(accessed, locs);
                        }
                    }
                    Statement::Constrain(c) => {
                        let lhs_components: Vec<&Ref> = c.lhs()
                            .variable_refs()
                            .into_iter()
                            .filter(|v| components.contains(v.name()))
                            .collect();
                        //let lhs_components = NamedStorage::get_accesses(c.lhs(), &components);
                        for var in lhs_components {
                            let (accessed, template_access) = self.get_component_access(var.name(), var.access());
                            let mut locs = output_locs.get_mut(var.name()).unwrap().remove(&accessed).unwrap_or(vec![]);
                            locs.push((*bid, i, stmt, template_access));
                            output_locs.get_mut(var.name()).unwrap().insert(accessed, locs);
                        }

                        let rhs_components: Vec<&Ref> = c.rhs()
                            .variable_refs()
                            .into_iter()
                            .filter(|v| components.contains(v.name()))
                            .collect();
                        //let rhs_components = NamedStorage::get_accesses(c.rhs(), &components);
                        for var in rhs_components {
                            let (accessed, template_access) = self.get_component_access(var.name(), var.access());
                            let mut locs = output_locs.get_mut(var.name()).unwrap().remove(&accessed).unwrap_or(vec![]);
                            locs.push((*bid, i, stmt, template_access));
                            output_locs.get_mut(var.name()).unwrap().insert(accessed, locs);
                        }
                    }
                    //skip
                    _ => {}
                }
            }
        }

        // use dominators to determine appropriate call locations
        let mut call_locs: HashMap<usize, BTreeMap<usize, Vec<(String, AccessList<Access>)>>> = HashMap::new();
        for c_name in components {
            let c_inputs = input_locs.get(c_name).ok_or(CFGError::ComponentInitializationNotFound(String::from(c_name)))?;
            let mut c_outputs = output_locs.get_mut(c_name);

            if let Some(c_outs) = &mut c_outputs {
                for input in c_inputs.keys() {
                    c_outs.remove(input);
                }

                if c_outs.is_empty() {
                    c_outputs = None;
                }
            }

            let mut placement_locs = HashSet::new();
            let mut placement_candidates = HashMap::new();
            let mut input_doms: HashSet<usize> = self.body.keys().map(|v| *v).collect();
            for (_, locs) in c_inputs {
                for loc in locs {
                    let loc_doms = post_dominators.get(&loc.0).ok_or(CFGError::BlockNotFound(loc.0))?;
                    input_doms = input_doms.intersection(loc_doms).map(|v| *v).collect();
                    let cur_last = *placement_candidates.get(&loc.0).unwrap_or(&0);
                    placement_candidates.insert(&loc.0, max(cur_last, loc.1 + 1));
                    placement_locs.insert(loc.0);
                }
            }

            for (bid, blk) in &self.body {
                if blk.is_loop_head() {
                    input_doms.remove(bid);
                }
            }

            let candidates = if let Some(c_outs) = c_outputs {
                let mut output_doms: HashSet<usize> = self.body.keys().map(|v| *v).collect();
                for (_, locs) in c_outs {
                    for loc in locs {
                        let loc_doms = dominators.get(&loc.0).ok_or(CFGError::BlockNotFound(loc.0))?;
                        output_doms = output_doms.intersection(loc_doms).map(|v| *v).collect();
                        let blk = self.body.get(&loc.0).ok_or(CFGError::BlockNotFound(loc.0))?;
                        let cur_last = *placement_candidates.get(&loc.0).unwrap_or(&blk.stmts.len());
                        placement_candidates.insert(&loc.0, min(cur_last, loc.1));
                        placement_locs.insert(loc.0);
                    }
                }

                input_doms.intersection(&output_doms).map(|v| *v).collect()
            }
            else {
                input_doms
            };

            let val = c_inputs.get(&String::default()).ok_or(CFGError::ComponentInitializationNotFound(String::from(c_name)))?.get(0).ok_or(CFGError::ComponentInitializationNotFound(String::from(c_name)))?;
            let placement_blks: Vec<usize> = candidates.intersection(&placement_locs).map(|v| *v).sorted().collect();
            let placement = if let Some(bid) = placement_blks.get(0) {
                (*bid, *placement_candidates.get(bid).ok_or(CFGError::BlockNotFound(*bid))?)
            }
            else if let Some(bid) = candidates.iter().next() {
                if val.3.len() != 0 {
                    unreachable!("Cannot infer a location in {} to place the component array {}", self.name, c_name);
                }
                (*bid, 0)
            }
            else {
                unreachable!("Cannot find a location in {} that dominates all reads of {} and is dominated by all writes", self.name, c_name);
            };

            let blk_locs = if let Some(b) = call_locs.get_mut(&placement.0) {
                b
            }
            else {
                call_locs.insert(placement.0, BTreeMap::new());
                call_locs.get_mut(&placement.0).unwrap()
            };

            let calls = if let Some(l) = blk_locs.get_mut(&placement.1) {
                l
            }
            else {
                blk_locs.insert(placement.1, Vec::new());
                blk_locs.get_mut(&placement.1).unwrap()
            };

            calls.push((c_name.into(), val.3.clone()))
        }

        Ok(call_locs)
    }

    /*
     * Sub-Circuit Invocation:
     * The component instantiation will not be triggered until all its input signals are assigned to
     * concrete values. Therefore the instantiation might be delayed and hence the component creation
     * instruction does not imply the execution of the component object, but the creation of the
     * instantiation process that will be completed when all the inputs are set.
     *
     * Function Invocation
     * We might replace functions with additional inputs
     *
     * Signal Mutability
     * Component inputs must be assigned to once.
     *
     * Approach: Note this won't always work.
     */
    pub fn build_inter(&mut self, template_entries: &HashMap<String, usize>, mut id: usize) -> Result<usize, CFGError> {
        let mut manually_invoked = HashSet::new();
        for blk in self.body.values_mut() {
            for edge in &mut blk.next {
                match edge {
                    Edge::Call(call) => {
                        manually_invoked.insert(call.component_name.clone());
                        let tgt_id_opt = template_entries.get(&call.to);
                        match tgt_id_opt {
                            None => { return Err(CFGError::TemplateNotFound(call.to.clone()))}
                            Some(tgt_id) => {
                                call.to_blk = *tgt_id;
                            }
                        }
                    }
                    _ => { /* Skip */ }
                }
            }
        }

        let sites = self.find_invocation_site(manually_invoked)?;
        let mut new_blocks = vec![];

        for (bid, locs) in sites {
            for (loc, calls) in locs.iter().rev() {
                for (c_name, access) in calls {
                    let component = self.components.get(c_name).unwrap();
                    let template_name = component.instance_of();
                    let blk = self.body.get_mut(&bid).unwrap();
                    let new_blk = blk.split(*loc, id);
                    id += 1;
                    let call = Edge::new_call(self.name.clone(), template_name.into(), c_name.clone(), access.clone(), template_entries.get(template_name).unwrap().clone(), new_blk.id, blk.id)?;
                    blk.add_edge(call);
                    if blk.id == self.exit_id {
                        self.exit_id = new_blk.id;
                    }
                    new_blocks.push(new_blk);
                }
            }
        }

        while !new_blocks.is_empty() {
            let blk = new_blocks.pop().unwrap();
            self.body.insert(blk.id, blk);
        }

        Ok(id)
    }

    pub fn finalize(&mut self) {
        let mut prev_edges = Vec::new();

        for blk in self.body.values() {
            for e in &blk.next {
                prev_edges.push(e.clone())
            }
        }

        while !prev_edges.is_empty() {
            let prev = prev_edges.pop().unwrap();
            self.body.get_mut(&prev.local_next()).unwrap().prev.push(prev);
        }
    }

    pub fn extract_local_lvals(&self, start_blk: usize, go_forward: bool, include_vars: bool) -> Result<Vec<&Ref>, &'static str> {
        let mut lvals = vec![];
        let mut seen = HashSet::new();
        seen.insert(start_blk);
        let start = self.body.get(&start_blk).ok_or("Could not find requested start block")?;
        let mut worklist = vec![start];
        while let Some(blk) = worklist.pop() {
            for stmt in &blk.stmts {
                match stmt {
                    Statement::AssignVar(a) => {
                        if include_vars {
                            lvals.push(a.lhs());
                        }
                    }
                    Statement::AssignSig(a) => {
                        lvals.push(a.lhs());
                    }
                    //skip
                    _ => { }
                }
            }
            let edges = if go_forward {&blk.next} else {&blk.prev};
            for e in edges {
                let next_step = if go_forward {e.local_next()} else {e.local_prev()};
                if !seen.contains(&next_step) {
                    seen.insert(next_step);
                    let next_blk = self.body.get(&next_step).ok_or("Template is malformed, could not find next block")?;
                    worklist.push(next_blk);
                }
            }
        }

        Ok(lvals)
    }

    pub fn get_entry_block(&self) -> Result<&Block, CFGError> {
        self.body.get(&self.entry_id).ok_or(CFGError::BlockNotFound(self.entry_id))
    }

    pub fn get_exit_block(&self) -> Result<&Block, CFGError> {
        self.body.get(&self.exit_id).ok_or(CFGError::BlockNotFound(self.exit_id))
    }

    pub fn get_block(&self, id: &usize) -> Result<&Block, CFGError> {
        self.body.get(id).ok_or(CFGError::BlockNotFound(*id))
    }

    pub fn pre_ref_var(&self, var: &Var, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        let entry = self.get_block(&self.entry_id)?;
        entry.pre_ref_var(var, access, ref_witness, ref_constraint)
    }

    pub fn pre_ref_sig(&self, sig: &Signal, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        let entry = self.get_block(&self.entry_id)?;
        entry.pre_ref_sig(sig, access, ref_witness, ref_constraint)
    }

    pub fn pre_ref_component(&self, cfg: &CFG, comp: &Component, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        let entry = self.get_block(&self.entry_id)?;
        entry.pre_ref_component(cfg, comp, access, ref_witness, ref_constraint)
    }

    pub fn pre_ref(&self, cfg: &CFG, store: &NamedStorage, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        let entry = self.get_block(&self.entry_id)?;
        entry.pre_ref(cfg, store, access, ref_witness, ref_constraint)
    }

    pub fn post_ref_var(&self, var: &Var, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        let exit = self.get_block(&self.exit_id)?;
        exit.post_ref_var(var, access, ref_witness, ref_constraint)
    }

    pub fn post_ref_sig(&self, sig: &Signal, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        let exit = self.get_block(&self.exit_id)?;
        exit.post_ref_sig(sig, access, ref_witness, ref_constraint)
    }

    pub fn post_ref_component(&self, cfg: &CFG, comp: &Component, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        let exit = self.get_block(&self.exit_id)?;
        exit.post_ref_component(cfg, comp, access, ref_witness, ref_constraint)
    }

    pub fn post_ref(&self, cfg: &CFG, store: &NamedStorage, access: AccessList<Access>, ref_witness: bool, ref_constraint: bool) -> Result<Ref, CFGError> {
        let exit = self.get_block(&self.exit_id)?;
        exit.post_ref(cfg, store, access, ref_witness, ref_constraint)
    }

    pub fn get_store_from_name(&self, name: &str) -> Result<&'glob NamedStorage, CFGError> {
        if let Some(store) = self.vars_and_signals.get(name) {
            Ok(*store)
        }
        else {
            Err(CFGError::VariableNotFound(self.name.clone(), String::from(name)))
        }
    }

    pub fn get_referenced_var(&self, cfg: &'glob CFG, var_ref: &VarRef) -> Result<(Option<&'glob Component>, &'glob Var), CFGError> {
        let field_access = var_ref.access().get_component_access();
        match field_access {
            None => {
                let accessed_var = self.vars_and_signals.get(var_ref.name()).ok_or(CFGError::VariableNotFound(self.name.clone(), String::from(var_ref.name())))?;
                match accessed_var {
                    NamedStorage::Signal(_) => {
                        Err(CFGError::TypeError(accessed_var.name().to_string(), "Variable".to_string(), "Signal".to_string()))
                    }
                    NamedStorage::Variable(v) => {
                        Ok((None, v))
                    }
                    NamedStorage::Component(_) => {
                        Err(CFGError::TypeError(accessed_var.name().to_string(), "Variable".to_string(), "Component".to_string()))
                    }
                }
            }
            Some(var_access) => {
                let component = self.components.get(var_ref.name()).ok_or(CFGError::VariableNotFound(self.name.clone(), String::from(var_ref.name())))?;
                let invoked_template = cfg.get_template(&component.instance_of().to_string())?;
                let accessed_var = invoked_template.vars_and_signals.get(var_access).ok_or(CFGError::VariableNotFound(self.name.clone(), var_access.clone()))?;
                match accessed_var {
                    NamedStorage::Signal(_) => {
                        Err(CFGError::TypeError(accessed_var.name().to_string(), "Variable".to_string(), "Signal".to_string()))
                    }
                    NamedStorage::Variable(v) => {
                        Ok((Some(*component), v))
                    }
                    NamedStorage::Component(_) => {
                        Err(CFGError::TypeError(accessed_var.name().to_string(), "Variable".to_string(), "Component".to_string()))
                    }
                }
            }
        }
    }

    pub fn get_referenced_sig(&self, cfg: &'glob CFG, sig_ref: &SignalRef) -> Result<(Option<&'glob Component>, &'glob Signal), CFGError>  {
        let field_access = sig_ref.access().get_component_access();
        match field_access {
            None => {
                let accessed_var = self.vars_and_signals.get(sig_ref.name()).ok_or(CFGError::VariableNotFound(self.name.clone(), String::from(sig_ref.name())))?;
                match accessed_var {
                    NamedStorage::Signal(s) => {
                        Ok((None, s))
                    }
                    NamedStorage::Variable(_) => {
                        Err(CFGError::TypeError(accessed_var.name().to_string(), "Signal".to_string(), "Variable".to_string()))
                    }
                    NamedStorage::Component(_) => {
                        Err(CFGError::TypeError(accessed_var.name().to_string(), "Signal".to_string(), "Component".to_string()))
                    }
                }
            }
            Some(sig_access) => {
                let component = self.components.get(sig_ref.name()).ok_or(CFGError::VariableNotFound(self.name.clone(), String::from(sig_ref.name())))?;
                let invoked_template = cfg.get_template(&component.instance_of().to_string())?;
                let accessed_var = invoked_template.vars_and_signals.get(sig_access).ok_or(CFGError::VariableNotFound(self.name.clone(), sig_access.clone()))?;
                match accessed_var {
                    NamedStorage::Signal(s) => {
                        Ok((Some(*component), s))
                    }
                    NamedStorage::Variable(_) => {
                        Err(CFGError::TypeError(accessed_var.name().to_string(), "Signal".to_string(), "Variable".to_string()))
                    }
                    NamedStorage::Component(_) => {
                        Err(CFGError::TypeError(accessed_var.name().to_string(), "Signal".to_string(), "Component".to_string()))
                    }
                }
            }
        }
    }

    pub fn get_referenced_component(&self, _cfg: &'glob CFG, comp_ref: &ComponentRef) -> Result<&'glob Component, CFGError>  {
        let accessed_comp = self.components.get(comp_ref.name()).ok_or(CFGError::VariableNotFound(self.name.clone(), String::from(comp_ref.name())))?;
        Ok(*accessed_comp)
    }

    pub fn get_referenced(&self, cfg: &'glob CFG, reference: &Ref) -> Result<(Option<&'glob  Component>, &'glob  NamedStorage), CFGError> {
        match reference {
            Ref::Var(v) => {
                let field_access = v.access().get_component_access();
                match field_access {
                    None => {
                        let accessed_var = self.vars_and_signals.get(v.name()).ok_or(CFGError::VariableNotFound(self.name.clone(), String::from(v.name())))?;
                        Ok((None, *accessed_var))
                    }
                    Some(var_access) => {
                        let component = self.components.get(v.name()).ok_or(CFGError::VariableNotFound(self.name.clone(), String::from(v.name())))?;
                        let invoked_template = cfg.get_template(&component.instance_of().to_string())?;
                        let accessed_var = invoked_template.vars_and_signals.get(var_access).ok_or(CFGError::VariableNotFound(self.name.clone(), var_access.clone()))?;
                        Ok((Some(*component), *accessed_var))
                    }
                }
            }
            Ref::Sig(s) => {
                let field_access = s.access().get_component_access();
                match field_access {
                    None => {
                        let accessed_var = self.vars_and_signals.get(s.name()).ok_or(CFGError::VariableNotFound(self.name.clone(), String::from(s.name())))?;
                        Ok((None, *accessed_var))
                    }
                    Some(sig_access) => {
                        let component = self.components.get(s.name()).ok_or(CFGError::VariableNotFound(self.name.clone(), String::from(s.name())))?;
                        let invoked_template = cfg.get_template(&component.instance_of().to_string())?;
                        let accessed_var = invoked_template.vars_and_signals.get(sig_access).ok_or(CFGError::VariableNotFound(self.name.clone(), sig_access.clone()))?;
                        Ok((Some(*component), *accessed_var))
                    }
                }
            }
            Ref::Comp(c) => {
                let accessed_comp = self.vars_and_signals.get(c.name()).ok_or(CFGError::VariableNotFound(self.name.clone(), String::from(c.name())))?;
                Ok((None, *accessed_comp))
            }
        }
    }
}

impl<'glob> DotSerialize for Template<'glob> {
    fn to_dot(&self) -> String {
        let mut dot = format!("  subgraph cluster_{} {{\n    label=\"{}\";\n    node [shape=box];\n    color=blue;", self.name, self.name);
        for block in self.body.values() {
            dot = format!("{}\n{}", dot, block.to_dot());
        };

        dot = format!("{}\n  }}", dot);
        dot
    }

    fn to_dot_interproc(&self) -> String {
        let mut dot = String::default();
        for block in self.body.values() {
            dot = String::from(format!("{}\n{}", dot, block.to_dot_interproc()).trim());
        };

        dot
    }
}
