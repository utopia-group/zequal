use std::collections::{HashMap, HashSet};
use std::ops::Sub;
use std::path::PathBuf;
use std::process::exit;
use std::str::FromStr;

use itertools::Itertools;
use num_bigint_dig::BigInt;
use num_traits::{One, Zero};
use smtlib_lowlevel::ast::CheckSatResponse;
use smtlib_lowlevel::backend::Backend;

use cfg::block::Block;
use cfg::cfg::CFG;
use cfg::edge::{Call, NegInvariantCondition};
use cfg::expr::expression::{Expr, Expression};
use cfg::expr::function_call::{FunctionCall, FunctionReturnType};
use cfg::expr::invariant::InvariantExpr;
use cfg::expr::literal::Literal;
use cfg::expr::var_access::{Access, AccessList};
use cfg::expr::variable_ref::{ComponentRef, Ref, SignalRef, VarRef};
use cfg::finite_fields::{BN128Prime, FiniteFieldDef};
use cfg::named_storage::{NamedStorage, Signal};
use cfg::stmt::statement::Statement;
use cfg::template::Template;
use static_analysis::domains::equivalence::equivalence_analysis::DefaultEquivalenceAnalysis;
use static_analysis::domains::interval::interval_analysis::{DefaultIntervalAnalysis, SymbolicIntervalAnalysis};
use crate::hoare_logic::vc_generator::VCGenerator;

use crate::interpreter::expression_interpreter::ExpressionInterpreter;
use crate::interpreter::invariant_interpreter::InvariantInterpreter;
use crate::inv_gen::candidate_gen::CandidateGenerator;
use crate::inv_gen::houdini::Houdini;
use crate::inv_gen::loop_summary::LoopSummary;
use crate::smt::smt::{Quantifier, TermSort, TypedTerm, UninterpretedFunction};
use crate::solver::solver::{InteractiveSolver, Solver, SolverUtils};
use crate::solver::solver_utils::{SatResult, SmtUtils, ValidityResult};
use crate::utils::callstack_entry::CallstackEntry;
use crate::utils::condition_term::ConditionTerm;
use crate::utils::error::VerificationError;
use crate::utils::template_context::TemplateContext;
use crate::utils::var_utils::VarUtils;
use crate::utils::wrapped_smt_term::{AuxVarDef, LazyTerm, VCTerm, VCVarTerm};

pub struct BasicVCGenerator<FF: FiniteFieldDef, B: Backend, T: VCTerm + VCVarTerm> {
    solver: Solver<B>,
    callstack: Vec<CallstackEntry<T>>,
    equiv_analysis: Option<DefaultEquivalenceAnalysis>,
    loop_summaries: HashMap<usize, Box<LoopSummary<FF>>>,
    interval_analyses: HashMap<String, SymbolicIntervalAnalysis<FF>>,
    cached_invariants: HashMap<usize, Vec<InvariantExpr>>,
    assume_safe_invocations: bool
}

impl<FF: FiniteFieldDef, B: Backend, T: VCTerm + VCVarTerm + LazyTerm> VarUtils<T> for BasicVCGenerator<FF, B, T> {
    fn read_var(&mut self, ctx: &TemplateContext, reference: &Ref, is_constraint: bool) -> Result<T, VerificationError> {
        let callstack_entry = self.callstack.last().ok_or(VerificationError::EmptyCallstack("read var"))?;
        if !callstack_entry.contains(reference) {
            self.declare(ctx, reference)?;
        }

        let callstack_entry = self.callstack.last().ok_or(VerificationError::EmptyCallstack("read var"))?;
        let var_terms_op = callstack_entry.get(reference, is_constraint);
        if let Ok(var_term) = var_terms_op {
            let mut var = var_term;
            for a in reference.access().iter() {
                match a {
                    Access::Component{..} => {}
                    Access::Array{ind} => {
                        var = var.select(self.interpret_expr(ctx, &ind, is_constraint)?)?;
                    }
                }
            }

            return Ok(var)
        }
        else {
            unreachable!("Could not find var {} even after declaration", reference.id())
        }
    }

    fn declare_sig(&mut self, ctx: &TemplateContext, sig_ref: &SignalRef) -> Result<(T, T), VerificationError> {
        let callstack = self.callstack.last_mut().ok_or(VerificationError::EmptyCallstack("declare sig"))?;
        callstack.declare_sig(ctx, &self.equiv_analysis, sig_ref)
    }

    fn declare_var(&mut self, ctx: &TemplateContext, var_ref: &VarRef) -> Result<(T, T), VerificationError> {
        let callstack = self.callstack.last_mut().ok_or(VerificationError::EmptyCallstack("declare var"))?;
        callstack.declare_var(ctx, &self.equiv_analysis, var_ref)
    }

    fn declare_comp(&mut self, ctx: &TemplateContext, comp_ref: &ComponentRef) -> Result<(), VerificationError> {
        let callstack = self.callstack.last_mut().ok_or(VerificationError::EmptyCallstack("declare comp"))?;
        callstack.declare_component(ctx, &self.equiv_analysis, comp_ref)
    }

    fn declare(&mut self, ctx: &TemplateContext, reference: &Ref) -> Result<(), VerificationError> {
        match reference {
            Ref::Var(v) => { self.declare_var(ctx, v); }
            Ref::Sig(s) => { self.declare_sig(ctx, s); }
            Ref::Comp(c) => { self.declare_comp(ctx, c); }
        }

        Ok(())
    }

    fn add_quantified_var(&mut self, _ctx: &TemplateContext, var_name: &str, sort: TermSort) -> Result<(), VerificationError> {
        let var_term = T::variable(sort, var_name)?;
        let callstackEntry = self.callstack.last_mut().ok_or(VerificationError::EmptyCallstack("add_quantified_var"))?;
        let is_aliased = !callstackEntry.force_declare(var_name.into(), (var_term.clone(), var_term)).is_none();
        if is_aliased {
            Err(VerificationError::AliasedQuantifiedVar(String::from(var_name)))
        }
        else {
            Ok(())
        }
    }

    fn remove_quantified_var(&mut self, _ctx: &TemplateContext, var_name: &str) -> Result<(), VerificationError> {
        let callstackEntry = self.callstack.last_mut().ok_or(VerificationError::EmptyCallstack("remove_quantified_var"))?;
        callstackEntry.remove(&var_name.into());
        Ok(())
    }

    fn push_callstack(&mut self) {
        self.callstack.push(CallstackEntry::new());
    }

    fn pop_callstack(&mut self)  {
        self.callstack.pop();
    }

    fn declare_callstack(&mut self) -> Result<(), VerificationError> {
        let callstackEntry = self.callstack.last().ok_or(VerificationError::EmptyCallstack("declare_callstack_vars"))?;
        let highest_val = T::get_prime().sub(BigInt::one());
        for (_, (term_c, term_w)) in callstackEntry.var_terms() {
            if !term_c.is_struct() {
                self.solver.declare_const(&term_c.sort(), &term_c.to_string())?;
                let bounds_c_opt = self.get_term_bounds(term_c.clone())?;
                if let Some(bounds_c) = bounds_c_opt {
                    self.solver.assert(bounds_c)?;
                }
                if term_c != term_w {
                    self.solver.declare_const(&term_w.sort(), &term_w.to_string())?;
                    let bounds_w_opt = self.get_term_bounds(term_w.clone())?;
                    if let Some(bounds_w) = bounds_w_opt {
                        self.solver.assert(bounds_w)?;
                    }
                }

                /*if term_c.sort() == T::signal_sort() || term_c.sort() == T::variable_sort() {
                    let lower_bound_c = term_c.clone().gte(T::from(&BigInt::zero()))?;
                    let upper_bound_c = term_c.clone().lte(T::from(&highest_val))?;
                    self.solver.assert(lower_bound_c)?;
                    self.solver.assert(upper_bound_c)?;
                }
                if term_w != term_c {
                    self.solver.declare_const(&term_w.sort(), &term_w.to_string())?;
                    if term_w.sort() == T::signal_sort() || term_w.sort() == T::variable_sort() {
                        let lower_bound_w = term_w.clone().gte(T::from(&BigInt::zero()))?;
                        let upper_bound_w = term_w.clone().lte(T::from(&highest_val))?;
                        self.solver.assert(lower_bound_w)?;
                        self.solver.assert(upper_bound_w)?;
                    }
                }*/
            }
        }

        for (_, uninterpreted_fn) in callstackEntry.uninterpreted_fns() {
            self.solver.declare_fn(&uninterpreted_fn.args, &uninterpreted_fn.ret, &uninterpreted_fn.name);
        }

        Ok(())
    }

    fn create_equality_constraint(&mut self, ctx: &TemplateContext, loc: &Block, reference: &Ref, is_pre_block: bool) -> Result<T, VerificationError> {
        let eq_constraints = reference.create_equality_constraint(ctx.cfg, ctx.template, loc, is_pre_block)?;
        let eq_constraint = InvariantExpr::and_all(eq_constraints)?;
        let expr = self.interpret_inv(ctx, &eq_constraint)?;
        Ok(expr)
    }

    fn create_any_equality_constraint(&mut self, ctx: &TemplateContext, loc: &Block, reference: &Ref, is_pre_block: bool) -> Result<T, VerificationError> {
        let eq_constraints = reference.create_any_equality_constraint(ctx.cfg, ctx.template, loc, is_pre_block)?;
        let eq_terms = eq_constraints.into_iter().map(|e| self.interpret_inv(ctx, &e)).collect::<Result<Vec<T>, _>>()?;
        let expr = T::or_all(eq_terms)?;
        Ok(expr)
    }
}

impl<FF: FiniteFieldDef, B: Backend, T: VCTerm + VCVarTerm + LazyTerm> ExpressionInterpreter<T> for BasicVCGenerator<FF, B, T> {
    fn get_function(&mut self, ctx: &TemplateContext, fn_call: &FunctionCall, is_constraint: bool) -> Result<T, VerificationError> {
        let mut smt_args = vec![];
        for arg in fn_call.args() {
            smt_args.push(self.interpret_expr(ctx, arg, is_constraint)?);
        }

        let callstack = self.callstack.last_mut().ok_or(VerificationError::EmptyCallstack("declare comp"))?;

        let fn_def = if callstack.contains_fn(fn_call.name()) {
            callstack.get_uninterpreted_fn(fn_call.name())?
        }
        else {
            let arg_types: Vec<TermSort> = smt_args.iter().map(|arg| arg.sort()).collect();
            let fn_ret_type = fn_call.ret_type();
            let ret_sort = match fn_ret_type {
                FunctionReturnType::Var => { T::variable_sort() }
                FunctionReturnType::VarArray(dims) => {
                    let mut var_sort = T::variable_sort();
                    for _ in dims {
                        var_sort = TermSort::Array(Box::new(T::variable_sort()), Box::new(var_sort));
                    }
                    var_sort
                }
            };
            callstack.declare_uninterpreted_fn(fn_call.name().clone(), arg_types, ret_sort)
        };

        Ok(T::create_fn_application(fn_def, smt_args)?)
    }
}

impl<FF: FiniteFieldDef, B: Backend, T: VCTerm + VCVarTerm + LazyTerm> InvariantInterpreter<T> for BasicVCGenerator<FF, B, T> {}

impl<FF: FiniteFieldDef, B: Backend, T: VCTerm + VCVarTerm + LazyTerm> Houdini<T> for BasicVCGenerator<FF, B, T> {}
impl<FF: FiniteFieldDef, B: Backend, T: VCTerm + VCVarTerm + LazyTerm> CandidateGenerator<FF, T> for BasicVCGenerator<FF, B, T> {
    fn get_loop_summary(&mut self, ctx: &TemplateContext, loop_head_id: usize) -> Result<Box<LoopSummary<FF>>, VerificationError> {
        match self.loop_summaries.get(&loop_head_id) {
            None => {
                let template_interval_analysis = match self.interval_analyses.get(&ctx.template.name()) {
                    None => {
                        let new_interval_analysis = SymbolicIntervalAnalysis::new(ctx.cfg, ctx.template);
                        self.interval_analyses.insert(ctx.template.name(), new_interval_analysis);
                        self.interval_analyses.get(&ctx.template.name).unwrap()
                    }
                    Some(analysis) => {
                        analysis
                    }
                };

                let new_summary = LoopSummary::new(ctx, loop_head_id, template_interval_analysis)?;
                self.loop_summaries.insert(loop_head_id, Box::new(new_summary.clone()));
                Ok(Box::new(new_summary))
            }
            Some(summary) => {
                Ok(summary.clone())
            }
        }
    }

    fn get_interval_analysis(&self, ctx: &TemplateContext) -> Result<&SymbolicIntervalAnalysis<FF>, VerificationError> {
        match self.interval_analyses.get(&ctx.template.name()) {
            None => {
                return Err(VerificationError::Msg("Interval analysis not found"))
            }
            Some(analysis) => {
                Ok(analysis)
            }
        }
    }
}

impl<FF: FiniteFieldDef, B: Backend, T: VCTerm + VCVarTerm + LazyTerm> SmtUtils<T> for BasicVCGenerator<FF, B, T> {
    fn find_required_preds(&mut self, query: Vec<T>) -> Result<Vec<T>, VerificationError> {
        self.solver.push(1)?;
        self.declare_callstack()?;
        let all = T::and_all(query.clone())?;
        self.declare_axioms(&all)?;
        for (ind, term) in query.iter().cloned().enumerate() {
            let label = format!("t{}", ind.to_string());
            let labeled = term.label(&label)?;
            self.solver.assert(labeled)?;
        }

        let result = self.solver.check_sat()?;
        let res = match result {
            CheckSatResponse::Sat => {
                Err(VerificationError::SolverReturnedSat("find_required_preds"))
            }
            CheckSatResponse::Unsat => {
                let mut required = vec![];
                let core = self.solver.get_unsat_core()?;
                for name in core {
                    let id = usize::from_str(&name[1..]).unwrap();
                    required.push(query[id].clone());
                }
                Ok(required)
            }
            CheckSatResponse::Unknown => {
                Err(VerificationError::SolverReturnedUnknown("find_required_preds"))
            }
        };

        self.solver.pop(1)?;
        res
    }

    fn check_sat(&mut self, query: T, get_model: bool) -> Result<SatResult, VerificationError> {
        self.solver.push(1)?;
        self.declare_callstack()?;
        self.declare_axioms(&query)?;
        self.solver.assert(query)?;
        let result = self.solver.check_sat()?;
        let res = match result {
            CheckSatResponse::Sat => {
                if get_model {
                    SatResult::Sat(self.solver.get_model())
                }
                else {
                    SatResult::Sat(Err("Model Not Requested"))
                }
            }
            CheckSatResponse::Unsat => { SatResult::Unsat }
            CheckSatResponse::Unknown => { SatResult::Unknown }
        };
        self.solver.pop(1)?;
        Ok(res)
    }

    fn check_validity(&mut self, query: T, get_model: bool) -> Result<ValidityResult, VerificationError> {
        self.solver.push(1)?;
        self.declare_callstack()?;
        let validity_query = query.not()?;
        self.declare_axioms(&validity_query)?;
        self.solver.assert(validity_query)?;
        let result = self.solver.check_sat()?;
        let res = match result {
            CheckSatResponse::Sat => {
                if get_model {
                    ValidityResult::Invalid(self.solver.get_model())
                }
                else {
                    ValidityResult::Invalid(Err("Model Not Requested"))
                }
            }
            CheckSatResponse::Unsat => { ValidityResult::Valid }
            CheckSatResponse::Unknown => { ValidityResult::Unknown }
        };
        self.solver.pop(1)?;
        Ok(res)
    }
}

impl<FF: FiniteFieldDef, B: Backend, T: VCTerm + VCVarTerm + LazyTerm> VCGenerator<T> for BasicVCGenerator<FF, B, T> {
    fn is_equivalent(&self, ctx: &TemplateContext, v_ref: &Ref) -> bool {
        if let Some(equiv) = &self.equiv_analysis {
            equiv.is_equivalent(&ctx.template.name, ctx.template, v_ref)
        }
        else {
            false
        }
    }
    /*fn infer_strengthenings(&mut self, ctx: &TemplateContext, exit_edge: &NegInvariantCondition, post: &ConditionTerm<T>) -> Result<Vec<T>, VerificationError> {
        let mut calls = vec![];
        self.push_callstack();
        let mut prev_lvals = HashSet::new();
        let to_blk = ctx.template.get_block(&exit_edge.next)?;

        for call in &ctx.callstack {
            let cur_template = ctx.cfg.templates
                .get(&call.template)
                .ok_or("Could not find template")?;
            let cur_ctx = TemplateContext::new(ctx.cfg, cur_template, calls);
            for sig in &cur_template.input_signals {
                let sig_ref = cur_template.pre_ref_sig(sig, AccessList::empty(), true, true)?;
                prev_lvals.insert((self.read_var(&cur_ctx, &sig_ref, true)?, self.read_var(&cur_ctx, &sig_ref, false)?));
            }
            for lval in cur_template.extract_local_lvals(call.prev, false, false)? {
                prev_lvals.insert((self.interpret_ref(&cur_ctx, &lval, true)?, self.interpret_ref(&cur_ctx, &lval, false)?));
            }

            let caller_stack = self.callstack.pop().ok_or("Callstack empty")?;
            let mut callee_stack = CallstackEntry::new();
            let mut call_renaming = HashMap::new();
            let mut ret_renaming = HashMap::new();

            let mut new_lvals = HashSet::new();
            for (lval_c, lval_w) in prev_lvals {
                let new_lval_c = Self::to_expr_in_callee(&caller_stack, &mut callee_stack, call, &mut call_renaming, &mut ret_renaming, lval_c)?;
                let new_lval_w = Self::to_expr_in_callee(&caller_stack, &mut callee_stack, call, &mut call_renaming, &mut ret_renaming, lval_w)?;
                new_lvals.insert((new_lval_c, new_lval_w));
            }

            prev_lvals = new_lvals;
            self.callstack.push(callee_stack);
            calls = cur_ctx.callstack;
            calls.push(call.clone());
        }

        for sig in &ctx.template.input_signals {
            let sig_ref = ctx.template.pre_ref_sig(sig, AccessList::empty(), true, true)?;
            prev_lvals.insert((self.read_var(ctx, &sig_ref, true)?, self.read_var(ctx, &sig_ref, false)?));
        }
        for lval in ctx.template.extract_local_lvals(exit_edge.prev, false, false)? {
            prev_lvals.insert((self.interpret_ref(ctx, &lval, true)?, self.interpret_ref(ctx, &lval, false)?));
        }

        self.pop_callstack();
        let callstackEntry = self.callstack.last().ok_or("Callstack is empty!")?;
        let mut post_vars = HashSet::new();
        for (_, (var_c, _)) in callstackEntry.iter() {
            post_vars.insert(var_c);
        }
        let mut strengthenings = vec![];
        for (lval_c, lval_w) in &prev_lvals {
            let mut var_set = HashSet::new();
            var_set.insert(lval_c);
            var_set.insert(lval_w);
            if lval_c.count_vars() == 1 && lval_c != lval_w && lval_c.contains_only(&post_vars) && post.clone().to_term()?.contains(&var_set) {
                strengthenings.push(lval_c.clone().eq(lval_w.clone())?);
            }
        }

        Ok(strengthenings)
    }*/

    fn gen_loop_inv(&mut self, ctx: &TemplateContext, exit_edge: &NegInvariantCondition, post: &ConditionTerm<T>) -> Result<InvariantExpr, VerificationError> {
        let (required, possible, loop_it_eqs, has_nested_loops) = self.generate_candidates(ctx, exit_edge, post)?;
        println!("required candidates: {}", required.iter().join(", "));
        println!("possible candidates: {}", possible.iter().join(", "));
        let inv = self.infer_loop_invariant(ctx, required, possible, loop_it_eqs, exit_edge, has_nested_loops)?;
        println!("{}", inv);
        Ok(inv)
    }

    fn get_cached_inv(&self, ctx: &TemplateContext, exit_edge: &NegInvariantCondition) -> Vec<InvariantExpr> {
        let head_id = exit_edge.prev;
        if let Some(invariants) = self.cached_invariants.get(&head_id) {
            invariants.clone()
        }
        else {
            vec![]
        }
    }

    fn cache_inv(&mut self, ctx: &TemplateContext, exit_edge: &NegInvariantCondition, inv: InvariantExpr) {
        let head_id = exit_edge.prev;
        if let Some(invariants) = self.cached_invariants.get_mut(&head_id) {
            invariants.push(inv);
        }
        else {
            self.cached_invariants.insert(head_id, vec![inv]);
        }
    }

    /*fn verify_call_inline(&mut self, ctx: &TemplateContext, call: &Call, post: &ConditionTerm<T>) -> Result<ConditionTerm<T>, VerificationError> {
        let callee_template = ctx.cfg.get_template(&call.to)?;
        let mut new_stack = ctx.callstack.clone();
        new_stack.push(call.clone());
        let callee_ctx = TemplateContext::new(ctx.cfg, callee_template, new_stack); //(ctx.cfg, caller_template);
        let mut new_stack = CallstackEntry::<T>::new();
        let mut call_renaming = HashMap::new();
        let mut ret_renaming = HashMap::new();
        let to_blk = ctx.template.get_block(&call.ret)?;

        for var in &callee_template.input_vars {
            let mut var_access = call.access.clone();
            var_access.push(Access::Component{name: var.name().into()})?;
            let caller_var_ref = to_blk.pre_ref_component(ctx.cfg, call.component, var_access, true, true)?;
            let callee_var = self.read_var(ctx, &caller_var_ref, false)?;
            let Ref::Var(callee_var_ref) = callee_template.post_ref_var(var, AccessList::empty())? else { unreachable!("non-var returned") };
            let new_var = new_stack.declare_var(&callee_ctx, &callee_var_ref)?;
            call_renaming.insert(callee_var.clone(), new_var.clone());
            ret_renaming.insert(new_var, callee_var);
        }

        for sig in &callee_template.input_signals {
            let mut sig_access = call.access.clone();
            sig_access.push(Access::Component{name: sig.name().into()})?;
            let sig_ref = to_blk.pre_ref_component(ctx.cfg, call.component, sig_access, true, true)?;
            let caller_sig_c = self.read_var(ctx, &sig_ref, true)?;
            let caller_sig_w = self.read_var(ctx, &sig_ref, false)?;
            let Ref::Sig(callee_sig_ref) = callee_template.post_ref_sig(sig, AccessList::empty(), true, true)? else { unreachable!("non-signal returned") };
            let (callee_sig_c, callee_sig_w) = new_stack.declare_sig(&callee_ctx, &self.equiv_analysis, &callee_sig_ref)?;
            call_renaming.insert(caller_sig_c.clone(), callee_sig_c.clone());
            call_renaming.insert(caller_sig_w.clone(), callee_sig_w.clone());
            ret_renaming.insert(callee_sig_c, caller_sig_c);
            ret_renaming.insert(callee_sig_w, caller_sig_w);
        }

        for sig in &callee_template.output_signals {
            let mut sig_access = call.access.clone();
            sig_access.push(Access::Component{name: sig.name().into()})?;
            let sig_ref = to_blk.pre_ref_component(ctx.cfg, call.component, sig_access, true, true)?;
            let caller_sig_c = self.read_var(ctx, &sig_ref, true)?;
            let caller_sig_w = self.read_var(ctx, &sig_ref, false)?;
            let Ref::Sig(callee_sig_ref) = callee_template.post_ref_sig(sig, AccessList::empty(), true, true)? else { unreachable!("non-signal returned") };
            let (callee_sig_c, callee_sig_w) = new_stack.declare_sig(&callee_ctx, &self.equiv_analysis, &callee_sig_ref)?;
            call_renaming.insert(caller_sig_c.clone(), callee_sig_c.clone());
            call_renaming.insert(caller_sig_w.clone(), callee_sig_w.clone());
            ret_renaming.insert(callee_sig_c, caller_sig_c);
            ret_renaming.insert(callee_sig_w, caller_sig_w);
        }

        let mut caller_stack = self.callstack.pop().ok_or(VerificationError::EmptyCallstack("verify_call_inline"))?;
        //let call_post_assumes = Self::to_expr_in_callee(&caller_stack, &mut new_stack, call, &mut call_renaming, &mut ret_renaming, post.clone())?;
        let callee_post_assumes = match &post.assumes {
            None => {None}
            Some(a) => {Some(Self::to_expr_in_callee(&caller_stack, &mut new_stack, call, &mut call_renaming, &mut ret_renaming, a.clone())?)}
        };
        let callee_post_asserts = Self::to_expr_in_callee(&caller_stack, &mut new_stack, call, &mut call_renaming, &mut ret_renaming, post.asserts.clone())?;
        self.callstack.push(new_stack);
        let inline_wp = self.verify_template(&callee_ctx, ConditionTerm::new(callee_post_assumes, callee_post_asserts))?;

        // rename caller vars as aux vars
        let callee_stack = self.callstack.pop().ok_or(VerificationError::EmptyCallstack("verify_call_inline"))?;
        //let callee_renamed_wp = Self::to_expr_in_caller(&mut caller_stack, &callee_stack, call, &mut ret_renaming, inline_wp)?;
        let caller_wp_assumes = match inline_wp.assumes {
            None => {None}
            Some(a) => {Some(Self::to_expr_in_caller(&mut caller_stack, &callee_stack, call, &mut ret_renaming, a)?)}
        };
        let caller_wp_asserts = Self::to_expr_in_caller(&mut caller_stack, &callee_stack, call, &mut ret_renaming, inline_wp.asserts)?;
        self.callstack.push(caller_stack);
        Ok(ConditionTerm::new(caller_wp_assumes, caller_wp_asserts))
    }*/

    fn verify_call_summary(&mut self, ctx: &TemplateContext, call: &Call, post: &ConditionTerm<T>) -> Result<ConditionTerm<T>, VerificationError> {
        let invoked_template = ctx.cfg.get_template(&call.to)?;
        if invoked_template.has_ensures() || invoked_template.has_requires() {
            // get input and output replacements. Ensures and requires have already been checked to make sure they're well-formed
            let prev_blk = ctx.template.get_block(&call.prev)?;
            let mut renaming = HashMap::new();
            let component = call.component(ctx.cfg)?;
            for input in &invoked_template.input_vars {
                let var_ref = invoked_template.pre_ref_var(input, AccessList::empty(), true, true)?;
                let mut component_access = call.access.clone();
                component_access.push(Access::new_component_access(String::from(input.name())))?;
                let component_ref = prev_blk.post_ref_component(ctx.cfg, component, component_access, true, true)?;
                renaming.insert(var_ref, component_ref);
            }

            for input in &invoked_template.input_signals {
                let sig_ref = invoked_template.pre_ref_sig(input, AccessList::empty(), true, true)?;
                let mut component_access = call.access.clone();
                component_access.push(Access::new_component_access(String::from(input.name())))?;
                let component_ref = prev_blk.post_ref_component(ctx.cfg, component, component_access, true, true)?;
                renaming.insert(sig_ref, component_ref);
            }

            for output in &invoked_template.output_signals {
                let sig_ref = invoked_template.pre_ref_sig(output, AccessList::empty(), true, true)?;
                let mut component_access = call.access.clone();
                component_access.push(Access::new_component_access(String::from(output.name())))?;
                let component_ref = prev_blk.post_ref_component(ctx.cfg, component, component_access, true, true)?;
                renaming.insert(sig_ref, component_ref);
            }

            let var_assignments = self.get_component_var_assignments(ctx, call)?;
            let mut new_post = post.clone();
            if let Some(ensures) = invoked_template.ensures() {
                let renamed_ensures = ensures.rename_all(&renaming)?;
                println!("Using ensures for template {}: {}", invoked_template.name, renamed_ensures);
                let ensures_term = self.interpret_inv(ctx, &renamed_ensures)?;
                println!("Ensures Term: {}", ensures_term);
                new_post = new_post.add_assume(ensures_term)?.add_assume(var_assignments.clone())?;
            }

            if let Some(requires) = invoked_template.requires() {
                let renamed_requires = requires.rename_all(&renaming)?;
                println!("Using requires for template {}: {}", invoked_template.name, renamed_requires);
                let requires_term = self.interpret_inv(ctx, &renamed_requires)?;
                println!("Requires Term: {}", requires_term);
                new_post = new_post.add_assert(requires_term)?.add_assume(var_assignments)?;
            }

            Ok(new_post)
        }
        else if self.assume_safe_invocations || invoked_template.assume_invocation_is_consistent() {
            let to_blk = ctx.template.get_block(&call.ret)?;
            let callee_template: &Template = ctx.cfg.get_template(&call.to)?;
            let var_assignments = self.get_component_var_assignments(ctx, call)?;

            let mut caller_post_preds = vec![];
            for sig in &callee_template.output_signals {
                let mut sig_access = call.access.clone();
                sig_access.push(Access::Component{name: sig.name().into()})?;
                let sig_ref = to_blk.pre_ref_component(ctx.cfg, call.component(ctx.cfg)?, sig_access, true, true)?;
                let caller_eq = self.create_equality_constraint(ctx, to_blk, &sig_ref, true)?;
                caller_post_preds.push(caller_eq);
            }

            let mut input_names = vec![];
            for sig in &callee_template.input_signals {
                input_names.push(sig.name().to_string())
            }

            for var in &callee_template.input_vars {
                input_names.push(var.name().to_string())
            }

            let mut caller_pre_preds = vec![];
            for input_name in input_names {
                let mut new_access = call.access.clone();
                new_access.push(Access::Component{name: input_name})?;
                let component_ref = to_blk.pre_ref_component(ctx.cfg, call.component(ctx.cfg)?, new_access, true, true)?;
                let caller_eq = self.create_equality_constraint(ctx, to_blk, &component_ref, true)?;
                caller_pre_preds.push(caller_eq);
            }

            let invoke_pre = T::and_all(caller_pre_preds)?;
            let invoke_post = T::and_all(caller_post_preds)?;

            println!("Assumed summary for {}: (=> (and {} {}) {})", &call.to, invoke_pre.to_string(), var_assignments.to_string(), invoke_post.to_string());

            let call_wp = post.clone()
                .add_assume(invoke_post)?
                .add_assume(var_assignments)?
                .add_assert(invoke_pre)?;

            Ok(call_wp)
        }
        else {
            self.infer_call_summary(ctx, call, post)
        }
    }
}

impl<FF: FiniteFieldDef, B: Backend, T: VCTerm + VCVarTerm + LazyTerm> BasicVCGenerator<FF, B, T> {
    fn infer_call_summary(&mut self, ctx: &TemplateContext, call: &Call, post: &ConditionTerm<T>) -> Result<ConditionTerm<T>, VerificationError> {
        let callee_template: &Template = ctx.cfg.get_template(&call.to)?;
        let mut required_eqs = vec![];
        let var_assignments = self.get_component_var_assignments(ctx, call)?;
        println!("var assignments: {}", var_assignments);
        let to_blk = ctx.template.get_block(&call.ret)?;
        for sig in &callee_template.output_signals {
            let mut sig_access = call.access.clone();
            sig_access.push(Access::Component{name: sig.name().into()})?;
            let sig_ref = to_blk.pre_ref_component(ctx.cfg, call.component(ctx.cfg)?, sig_access, true, true)?;
            let caller_sig_c = self.read_var(ctx, &sig_ref, true)?;
            let caller_sig_w = self.read_var(ctx, &sig_ref, false)?;
            if caller_sig_c != caller_sig_w {
                let mut vars = HashSet::new();
                vars.insert(&caller_sig_c);
                vars.insert(&caller_sig_w);
                if post.clone().to_term()?.contains(&vars) {
                    required_eqs.push(sig);
                }


                /*compiler enforces that only valid indices can be accessed
                let mut post_check = post.clone();
                for (ind, access) in call.access.iter().enumerate() {
                    let Access::Array{ind: expr} = access else { unreachable!("An output signal cannot be a component") };
                    let ind_term = self.interpret_expr(ctx, expr, false)?;
                    let size_term = self.interpret_expr(ctx, &call.component(ctx.cfg)?.dims()[ind], false)?;
                    let geq_zero = ind_term.clone().gte(T::from(&BigInt::zero()))?;
                    let lt_size = ind_term.lt(size_term)?;
                    post_check = post_check.add_assume(geq_zero)?;
                    post_check = post_check.add_assume(lt_size)?;
                }

                let (component_dims, sig_dims) = sig_ref.get_dimensions(ctx.cfg, ctx.template)?;
                for dim in sig_dims {
                    let dim_size_c = self.interpret_expr(ctx, &dim, true)?;
                    let gt_zero_c = dim_size_c.gt(T::from(&BigInt::zero()))?;
                    post_check = post_check.add_assume(gt_zero_c)?;
                    let dim_size_w = self.interpret_expr(ctx, &dim, false)?;
                    let gt_zero_w = dim_size_w.gt(T::from(&BigInt::zero()))?;
                    post_check = post_check.add_assume(gt_zero_w)?;
                }

                //let sig_eq = caller_sig_w.eq(caller_sig_c)?;
                let any_sig_eq = self.create_any_equality_constraint(ctx, to_blk, &sig_ref, true)?;
                let mut assume_check = ConditionTerm::new(post_check.assumes.clone(), any_sig_eq.clone());
                assume_check = assume_check.add_assume(var_assignments.clone())?;
                let implied_by_assumes = self.check_validity(assume_check.to_term()?, false)?;
                if let ValidityResult::Invalid(_) = implied_by_assumes {
                    let pre = match &post_check.assumes {
                        None => {post_check.asserts.clone()}
                        Some(a) => {a.clone().and(post_check.asserts.clone())?}
                    };
                    let query = pre.and(var_assignments.clone())?.implies(any_sig_eq.clone())?;
                    let implied_by_asserts = self.check_validity(query, false)?;
                    if implied_by_asserts == ValidityResult::Valid {
                        required_eqs.push(sig);
                    }
                }
                else {
                    println!("{}", post);
                    unreachable!("Implied by asserts in {} to {}?", call.template, call.to);
                }*/
            }
        }

        let mut caller_post_preds = vec![];
        for sig in &required_eqs {
            let mut sig_access = call.access.clone();
            sig_access.push(Access::Component{name: sig.name().into()})?;
            let sig_ref = to_blk.pre_ref_component(ctx.cfg, call.component(ctx.cfg)?, sig_access, true, true)?;
            let caller_eq = self.create_equality_constraint(ctx, to_blk, &sig_ref, true)?;
            caller_post_preds.push(caller_eq);
        }

        let mut new_call_stack = ctx.callstack.clone();
        new_call_stack.push(call.clone());
        let callee_ctx = TemplateContext::new(ctx.cfg, callee_template, new_call_stack);
        self.callstack.push(CallstackEntry::<T>::new());
        let required_sigs_opt = self.infer_call_summary_helper(&callee_ctx, required_eqs, post);
        self.callstack.pop();
        let required_refs = required_sigs_opt?;
        let mut caller_pre_preds = vec![];
        for input in required_refs {
            let mut new_access = call.access.clone();
            new_access.push(Access::Component{name: input.name().into()})?;
            let component_ref = to_blk.pre_ref_component(ctx.cfg, call.component(ctx.cfg)?, new_access, true, true)?;
            let caller_eq = self.create_equality_constraint(ctx, to_blk, &component_ref, true)?;
            caller_pre_preds.push(caller_eq);
        }

        let invoke_pre = T::and_all(caller_pre_preds)?;
        let invoke_post = T::and_all(caller_post_preds)?;

        println!("Inferred summary for {}: (=> (and {} {}) {})", &call.to, invoke_pre.to_string(), var_assignments.to_string(), invoke_post.to_string());

        let call_wp = post.clone()
            .add_assume(invoke_post)?
            .add_assume(var_assignments)?
            .add_assert(invoke_pre)?;

        println!("call wp: {}", call_wp);
        Ok(call_wp)
    }

    fn infer_call_summary_helper<'glob, 'vc>(&mut self, callee_ctx: &'vc TemplateContext<'glob>, required_eqs: Vec<&'vc &'glob Signal>, post: &ConditionTerm<T>) -> Result<Vec<Ref>, VerificationError> {
        let callee_template: &Template = callee_ctx.template;
        let mut callee_post_preds = vec![];
        for sig in &required_eqs {
            let callee_sig = callee_template.post_ref_sig(sig, AccessList::empty(), true, true)?;
            let callee_eq = self.create_equality_constraint(&callee_ctx, callee_template.get_exit_block()?, &callee_sig, true)?;
            callee_post_preds.push(callee_eq);
        }

        let callee_post = T::and_all(callee_post_preds)?;
        println!("caller post: {}", post);
        println!("callee post: {}", callee_post);
        let call_wp = self.verify_template(&callee_ctx, ConditionTerm::new(None, callee_post))?;
        println!("callee wp: {}", call_wp);

        let mut input_eqs = vec![];
        for sig in &callee_template.input_signals {
            let callee_sig = callee_template.pre_ref_sig(sig, AccessList::empty(), true, true)?;
            let input_eq = self.create_equality_constraint(&callee_ctx, callee_template.get_entry_block()?, &callee_sig, true)?;
            input_eqs.push((callee_sig, input_eq));
        }

        for var in &callee_template.input_vars {
            let callee_var = callee_template.pre_ref_var(var, AccessList::empty(), true, true)?;
            let input_eq = self.create_equality_constraint(&callee_ctx, callee_template.get_entry_block()?, &callee_var, true)?;
            input_eqs.push((callee_var, input_eq));
        }

        let inputs = T::and_all(input_eqs.iter().map(|v| v.1.clone()).collect())?;
        let wp_with_pre = call_wp.clone().add_assume(inputs)?;
        let strongest_res = self.check_validity(wp_with_pre.to_term()?, true)?;
        if let ValidityResult::Invalid(m) = strongest_res {
            return Err(VerificationError::TemplateSummarizationFailed("verify_call_summary", callee_template.name.clone(), m))
        }
        else if let ValidityResult::Unknown = strongest_res {
            return Err(VerificationError::SolverReturnedUnknown("verify_call_summary"))
        }

        let mut required_refs = vec![];
        let mut required_eqs = vec![];
        while let Some((sig, eq)) = input_eqs.pop() {
            let required_inputs = T::and_all(required_eqs.clone())?;
            let unchecked_inputs = T::and_all(input_eqs.iter().map(|v| v.1.clone()).collect())?;
            let input_check = call_wp.clone().add_assume(required_inputs.and(unchecked_inputs)?)?;
            let res = self.check_validity(input_check.to_term()?, false)?;
            match res {
                ValidityResult::Invalid(_) => {
                    required_eqs.push(eq);
                    required_refs.push(sig);
                }
                ValidityResult::Unknown => { unreachable!("Returned unknown!") }
                ValidityResult::Valid => {}
            }
        }

        Ok(required_refs)
    }

    fn get_var_assignments(&self, ctx: &TemplateContext, call: &Call, rhs: &Expression) -> Result<HashMap<String, Expression>, VerificationError> {
        let mut var_assignment = HashMap::new();
        let template = ctx.cfg.get_template(&call.component(ctx.cfg)?.instance_of().to_string())?;
        match rhs {
            Expression::Instantiate(instantiation) => {
                if instantiation.name() != call.component(ctx.cfg)?.instance_of() {
                    unreachable!("CFG is malformed");
                }

                let mut i = 0;
                for arg in instantiation.args() {
                    let var = template.input_vars.get(i).unwrap();
                    var_assignment.insert(var.name().into(), arg.clone());
                    i += 1;
                }
            }
            _ => {}
        }

        Ok(var_assignment)
    }

    fn get_component_var_assignments(&mut self, ctx: &TemplateContext, call: &Call) -> Result<T, VerificationError>{
        let mut worklist = vec![call.prev];
        let mut seen = HashSet::new();
        let component = call.component(ctx.cfg)?;
        let mut var_assignments: HashMap<String, Vec<Expression>> = HashMap::new();
        seen.insert(call.prev);
        let mut singleton = HashSet::new();
        singleton.insert(component.name());
        let to_blk = ctx.template.get_block(&call.ret)?;

        while let Some(bid) = worklist.pop() {
            let blk = ctx.template.body.get(&bid)
                .ok_or("Could not find block")?;

            for stmt in &blk.stmts {
                match stmt {
                    Statement::AssignVar(a) => {
                        let lhs = a.lhs();
                        if component.name() != lhs.name() || lhs.access().len() != component.dims().len() {
                            continue;
                        }
                        let assignment = self.get_var_assignments(ctx, call, a.rhs())?;
                        for (var, expr) in assignment {
                            if let Some(exprs) = var_assignments.get_mut(&var) {
                                exprs.push(expr);
                            }
                            else {
                                var_assignments.insert(var.clone(), vec![expr]);
                            }
                        }
                    }
                    _ => {}
                }
            }

            for prev_edge in &blk.prev {
                let prev_id = prev_edge.local_prev();
                if !seen.contains(&prev_id) {
                    seen.insert(prev_id);
                    worklist.push(prev_id);
                }
            }
        }

        let mut assignments = vec![];
        for (var, exprs) in var_assignments {
            let mut access = call.access.clone();
            access.push(Access::Component{name: var})?;
            let var_ref = to_blk.pre_ref_component(ctx.cfg, call.component(ctx.cfg)?, access, true, true)?;
            let var_term_w = self.read_var(ctx, &var_ref, false)?;
            let var_term_c = self.read_var(ctx, &var_ref, true)?;
            let mut disjuncts = vec![];

            for expr in exprs {
                let eq_w = var_term_w.clone().eq(self.interpret_expr(ctx, &expr, false)?)?;
                let eq_c = var_term_c.clone().eq(self.interpret_expr(ctx, &expr, true)?)?;
                disjuncts.push(T::and_all(vec![eq_w, eq_c])?);
            }

            assignments.push(T::or_all(disjuncts)?);
        }

        Ok(T::and_all(assignments)?)
    }

    fn get_term_bounds(&self, term: T) -> Result<Option<T>, VerificationError> {
        if term.is_variable() || term.is_signal() {
            let highest_val = T::get_prime().sub(BigInt::one());
            let lower_bound = term.clone().gte(T::from(&BigInt::zero()))?;
            let upper_bound = term.clone().lte(T::from(&highest_val))?;
            Ok(Some(lower_bound.and(upper_bound)?))
        }
        else if term.is_array() {
            let num_quantifiers = if term.is_quantified() {term.get_quantified_vars()?.len()} else {0};
            let q_name = format!("x{}", num_quantifiers);
            let q = T::variable(T::variable_sort(), q_name.as_str())?;
            let accessed = term.select(q)?;
            let bounds_opt = self.get_term_bounds(accessed)?;
            if let Some(bounds) = bounds_opt {
                Ok(Some(bounds.quantify(Quantifier::Forall, vec![(q_name, T::variable_sort())])?))
            }
            else {
                Ok(None)
            }
        }
        else {
            Ok(None)
        }
    }

    fn declare_aux_vars(&mut self, aux_vars: &HashSet<AuxVarDef>) -> Result<(), VerificationError> {
        let highest_val = T::get_prime().sub(BigInt::one());

        let mut worklist: Vec<_> = aux_vars.iter().cloned().collect();
        while let Some(aux_var) = worklist.pop() {
            let axiom_str = aux_var.axiom.term().to_string();
            if worklist.iter().any(|v| axiom_str.contains(&v.name)) {
                //move to end of worklist, there shouldn't be a circular axiom but later
                // might want to double check
                worklist.push(aux_var);
            }
            else {
                self.solver.declare_const(&aux_var.sort, &aux_var.name)?;
                let tmp_term = T::variable(aux_var.sort.clone(), aux_var.name.as_str())?;
                let lower_bound_c = tmp_term.clone().gte(T::from(&BigInt::zero()))?;
                let upper_bound_c = tmp_term.clone().lte(T::from(&highest_val))?;
                self.solver.assert(lower_bound_c)?;
                self.solver.assert(upper_bound_c)?;
                self.solver.assert(aux_var.axiom.clone())?;
            }
        }

        Ok(())
    }

    fn declare_axioms(&mut self, assertion: &T) -> Result<(), VerificationError> {
        let mut op_axioms = HashSet::new();
        for op in assertion.var_ops() {
            let op_axiom = T::get_var_axiom(op);
            if let Some(axiom) = op_axiom {
                if !op_axioms.contains(&axiom.name) {
                    self.solver.declare_fn(&axiom.args, &axiom.ret, &axiom.name)?;
                    for axiom_term in axiom.axioms {
                        self.solver.assert(axiom_term)?;
                    }

                    op_axioms.insert(axiom.name);
                }
            }
        }

        for op in assertion.sig_ops() {
            let op_axiom = T::get_sig_axiom(op);
            if let Some(axiom) = op_axiom {
                if !op_axioms.contains(&axiom.name) {
                    self.solver.declare_fn(&axiom.args, &axiom.ret, &axiom.name)?;
                    for axiom_term in axiom.axioms {
                        self.solver.assert(axiom_term)?;
                    }

                    op_axioms.insert(axiom.name);
                }
            }
        }

        self.declare_aux_vars(assertion.aux_vars())?;

        Ok(())
    }

    fn to_expr_in_callee(caller_stack: &CallstackEntry<T>, callee_stack: &mut CallstackEntry<T>, call: &Call, call_renaming: &mut HashMap<T, T>, ret_renaming: &mut HashMap<T, T>, expr: T) -> Result<T, VerificationError> {
        /*
         * Simple variable renaming from component to input won't work in cases where we have arrays
         * of components. In that case we will need to express an equality constraint. In that case we
         * should just leave it to the caller to handle the assignments to the template inputs/outputs
         */
        for (var, (constraint_term, witness_term)) in caller_stack.var_terms() {
            if !call_renaming.contains_key(constraint_term) && !constraint_term.is_struct() {
                let callee_name = format!("i.{}.{}", call.prev, var);
                let callee_c_name = format!("{}.c", callee_name);
                let callee_c = T::variable(constraint_term.sort(), &callee_c_name)?;
                call_renaming.insert(constraint_term.clone(), callee_c.clone());
                ret_renaming.insert(callee_c.clone(), constraint_term.clone());
                let var_pair = if constraint_term != witness_term {
                    let callee_w_name = format!("{}.w", callee_name);
                    let callee_w = T::variable(witness_term.sort(), &callee_w_name)?;
                    call_renaming.insert(witness_term.clone(), callee_w.clone());
                    ret_renaming.insert(callee_w.clone(), witness_term.clone());
                    (callee_c, callee_w)
                }
                else {
                    (callee_c.clone(), callee_c)
                };

                callee_stack.force_declare(callee_name, var_pair);
            }
        }

        Ok(expr.substitute_vars(&call_renaming)?)
    }

    fn to_expr_in_caller(caller_stack: &mut CallstackEntry<T>, callee_stack: &CallstackEntry<T>, call: &Call, ret_renaming: &mut HashMap<T, T>, expr: T) -> Result<T, VerificationError> {
        for (var, (constraint_term, witness_term)) in callee_stack.var_terms() {
            if !ret_renaming.contains_key(constraint_term) && !constraint_term.is_struct() {
                let caller_name = format!("r.{}.{}", call.prev, var);
                let caller_c_name = format!("{}.c", caller_name);
                let caller_c = T::variable(constraint_term.sort(), &caller_c_name)?;
                ret_renaming.insert(constraint_term.clone(), caller_c.clone());
                let var_pair = if constraint_term != witness_term {
                    let caller_w_name = format!("{}.w", caller_name);
                    let caller_w = T::variable(witness_term.sort(), &caller_w_name)?;
                    ret_renaming.insert(witness_term.clone(), caller_w.clone());
                    (caller_c, caller_w)
                }
                else {
                    (caller_c.clone(), caller_c)
                };

                caller_stack.force_declare(caller_name, var_pair);
            }
        }

        Ok(expr.substitute_vars(&ret_renaming)?)
    }

    pub fn new(backend: B, output_dir: &PathBuf, cfg: &CFG, equiv_analysis: Option<DefaultEquivalenceAnalysis>, assume_safe_invocations: bool) -> Result<Self, VerificationError> {
        let mut solver = Solver::new(backend, output_dir)?;
        solver.enable_unsat_cores()?;
        Ok(Self { solver, callstack: vec![], equiv_analysis, interval_analyses: HashMap::new(), loop_summaries: HashMap::new(), cached_invariants: HashMap::new(), assume_safe_invocations })
    }
}

