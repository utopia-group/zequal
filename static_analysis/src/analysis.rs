use std::collections::{HashSet};
use std::fmt::Display;
use itertools::Itertools;
use thiserror::Error;
use cfg::block::{Block};
use cfg::cfg::CFG;
use cfg::edge::{Call, Edge};
use cfg::error::CFGError;
use cfg::expr::expression::Expression;
use cfg::expr::var_access::{Access, AccessList};
use cfg::expr::variable_ref::{Ref, VarRef};
use cfg::stmt::statement::Statement;
use cfg::template::Template;

//maybe remove later
pub trait DomainValue: Eq + Clone + Display {
    fn top() -> Self;
    fn bottom() -> Self;
    fn is_bottom(&self) -> bool;
    fn join(&self, other: &Self) -> Self;
    fn widen(&self, other: &Self) -> Self;
    fn narrow(&self, other: &Self) -> Self;
    fn should_narrow() -> bool;
    fn meet(&self, other: &Self) -> Self;
}

pub trait AbstractState<D: DomainValue>: Eq + Clone + Display {
    fn empty() -> Self;
    fn join(&self, other: &Self) -> Self;
    fn widen(&self, other: &Self) -> Self;
    fn narrow(&self, other: &Self) -> Self;
    fn join_value(&mut self, cfg: &CFG, template: &Template, var_ref: &Ref, val: &D);
    fn apply_to_value(&mut self, cfg: &CFG, template: &Template, var_ref: &Ref, val: &D, op: fn(&D, &D) -> D);
    /*fn join_component_value(&mut self, component: &Component, sig: &Signal, val: &D);
    fn join_signal_value(&mut self, signal: &Signal, val: &D);*/
    fn contains_value(&self, var_ref: &Ref) -> bool;
    // TODO: consider switching this to optional rather than selecting bottom by default
    fn get_value(&self, var_ref: &Ref) -> D;
    /*fn get_component_value(&self, component: &Component, sig: &Signal) -> D;
    fn get_signal_value(&self, signal: &Signal) -> D;*/
    fn set_value(&mut self, cfg: &CFG, template: &Template, var_ref: &Ref, val: &D);
    fn is_superset_of(&self, other: &Self) -> bool;
    fn lock_var(&mut self, v_ref: &Ref);
}

pub trait AbstractTransformer<D: DomainValue, A: AbstractState<D>> {
    fn interpret_expr(start: &A, cfg: &CFG, template: &Template, expr: &Expression) -> D;
    //fn join_expr(start: &mut A, cfg: &CFG, template: &Template, expr: &Expression, val: &D);
    fn assume_expr(start: &mut A, cfg: &CFG, template: &Template, expr: &Expression, negate: bool);
    fn interpret_stmt_in_place(start: &mut A, cfg: &CFG, template: &Template, stmt: &Statement);
    fn interpret_stmt(start: &A, cfg: &CFG, template: &Template, stmt: &Statement) -> A {
        let mut new_state = start.clone();
        Self::interpret_stmt_in_place(&mut new_state, cfg, template, stmt);
        new_state
    }
    fn interpret_blk(start: &A, cfg: &CFG, template: &Template, blk: &Block) -> A {
        let mut new_state = start.clone();
        for stmt in &blk.stmts {
            Self::interpret_stmt_in_place(&mut new_state, cfg, template, stmt);
        }
        new_state
    }
    fn localize_to(cfg: &CFG, caller_template: &Template, caller: &A, callee: &A, call: &Call) -> A {
        let mut localized = callee.clone();
        let callee_template = cfg.templates.get(&call.to).unwrap();
        let next_caller_blk = caller_template.body.get(&call.ret).unwrap();

        for input_var in &callee_template.input_vars {
            let mut var_access = call.access.clone();
            match var_access.push(Access::new_component_access(input_var.name().into())) {
                Err(_) => unreachable!("could not push which shouldn't happen"),
                Ok(()) => { /* skip */ }
            }
            let component_var_ref = next_caller_blk.pre_ref_component(cfg, call.component(cfg).unwrap(), var_access, true, true).unwrap();
            let abstract_val = caller.get_value(&component_var_ref);
            let input_var_ref = callee_template.pre_ref_var(input_var, AccessList::empty(), true, true).unwrap();
            localized.join_value(cfg, callee_template, &input_var_ref, &abstract_val);
        }

        for input_sig in &callee_template.input_signals {
            let mut sig_access = call.access.clone();
            match sig_access.push(Access::new_component_access(input_sig.name().into())) {
                Err(_) => unreachable!("could not push which shouldn't happen"),
                Ok(()) => { /* skip */ }
            }
            let component_sig_ref = next_caller_blk.pre_ref_component(cfg, call.component(cfg).unwrap(), sig_access.clone(), true, true).unwrap();
            let abstract_val = caller.get_value(&component_sig_ref);
            let input_sig_ref = callee_template.pre_ref_sig(input_sig, AccessList::empty(), true, true).unwrap();
            localized.join_value(cfg, callee_template, &input_sig_ref, &abstract_val);
        }
        localized
    }
    fn localize_from(cfg: &CFG, caller_template: &Template, caller: &A, callee: &A, call: &Call) -> A {
        let mut localized = caller.clone();
        let callee_template = cfg.templates.get(&call.to).unwrap();
        let next_caller_blk = caller_template.body.get(&call.ret).unwrap();

        for output_sig in &callee_template.output_signals {
            let mut sig_access = call.access.clone();
            match sig_access.push(Access::new_component_access(output_sig.name().into())) {
                Err(_) => unreachable!("could not push which shouldn't happen"),
                Ok(()) => { /* skip */ }
            }
            let component_sig_ref = next_caller_blk.pre_ref_component(cfg, call.component(cfg).unwrap(), sig_access.clone(), true, true).unwrap();
            let output_sig_ref = callee_template.post_ref_sig(output_sig, AccessList::empty(), true, true).unwrap();
            let abstract_val = callee.get_value(&output_sig_ref);
            localized.join_value(cfg, caller_template, &component_sig_ref, &abstract_val);
        }
        localized
    }
}
#[derive(Error, Debug)]
pub enum StateError {
    #[error("Specified context does not exist")]
    ContextDoesNotExist,
    #[error("Could not find block")]
    BlockNotFound
}

//maybe turn this into a trait later and use functions to get transformer or to get result
/*pub struct AbstractInterpretation<D: DomainValue, T: Transformer<D>> {
    transformer: T,
    results: HashMap<usize, D>
}*/

pub trait AbstractInterpretation<D: DomainValue, A: AbstractState<D>, T: AbstractTransformer<D, A>> {
    // For dealing with cases where the analysis is context sensitive
    type Context;

    fn new() -> Self;
    // configurable behavior
    fn init_context(cfg: &CFG, template: &Template) -> Self::Context;
    fn all_contexts(&self) -> Vec<Self::Context>;
    fn get_context_template<'c>(cfg: &'c CFG, ctx: &Self::Context) -> Result<&'c Template<'c>, CFGError>;
    fn update_context(ctx: &Self::Context, call: &Call) -> Self::Context;
    //fn analyze_template(&mut self, ctx: &Self::Context, cfg: &cfg, template: &Template, state: &A) -> &A;

    // getters
    //fn transformer(&self) -> &T;
    fn join_start_state(&mut self, ctx: &Self::Context, template: &Template, new_state: &A) -> bool {
        self.join_state(&ctx, Option::Some(template.body.get(&template.entry_id).unwrap()), new_state)
    }
    fn get_start_state(&self, ctx: &Self::Context, template: &Template) -> Result<&A, StateError> {
        self.get_state(ctx, Option::Some(template.body.get(&template.entry_id).unwrap()))
    }
    fn get_end_state(&self, ctx: &Self::Context, _template: &Template) -> Result<&A, StateError> {
        self.get_state(ctx, Option::None)
    }

    //fn has_state(&self, ctx: &Self::Context, blk: Option<&Block>) -> bool;
    fn get_state(&self, ctx: &Self::Context, blk: Option<&Block>) -> Result<&A, StateError>;
    //fn get_state_ref(&mut self, ctx: &Self::Context, blk: Option<&Block>) -> &A;
    fn join_state(&mut self, ctx: &Self::Context, blk: Option<&Block>, new_state: &A) -> bool;
    fn widen_state(&mut self, ctx: &Self::Context, blk: Option<&Block>, new_state: &A) -> bool;
    fn narrow_state(&mut self, ctx: &Self::Context, blk: Option<&Block>, new_state: &A) -> bool;

    // setters
    //fn set_result(&mut self, blk: &Block, new_result: D);

    // Actually performs
    fn analyze_template(&mut self, cfg: &CFG, ctx: &Self::Context, template: &Template) -> bool {
        let mut worklist = vec![template.entry_id];
        let mut in_worklist = HashSet::new();
        in_worklist.insert(template.entry_id);
        let mut modified = false;

        while !worklist.is_empty() {
            let cur_id = worklist.pop().unwrap();
            in_worklist.remove(&cur_id);
            let cur_blk = template.body.get(&cur_id).unwrap();
            let cur_state = self.get_state(ctx, Option::Some(cur_blk)).unwrap();
            let new_state = T::interpret_blk(cur_state, cfg, template, cur_blk);
            if cur_blk.next.is_empty() {
                modified = self.join_state(ctx, Option::None, &new_state) || modified;
            }
            else {
                for e in &cur_blk.next {
                    let next_id = e.local_next();
                    let next_blk = template.body.get(&next_id).unwrap();
                    let mut next_state = new_state.clone();
                    for (_, (before_ref, after_ref)) in e.ssa_local_renaming(template).unwrap() {
                        let before_state = next_state.get_value(&before_ref);
                        next_state.set_value(cfg, template, &after_ref, &before_state);
                    }

                    let modifies_next = match e {
                        Edge::Call(call) => {
                            let callee_template = cfg.templates.get(&call.to).unwrap();
                            let callee_start_state = self.get_start_state(ctx, callee_template);
                            let is_empty = callee_start_state.is_err();
                            let empty_state = A::empty();
                            let callee_localized = T::localize_to(cfg, template, &next_state, &callee_start_state.as_ref().unwrap_or(&&empty_state), call);
                            let callee_ctx = Self::update_context(ctx, call);
                            if self.join_start_state(&callee_ctx, callee_template, &callee_localized) || is_empty {
                                modified = true;
                                self.analyze_template(cfg, &callee_ctx, callee_template);
                                let callee_end_state = self.get_end_state(&callee_ctx, callee_template).unwrap();
                                let caller_localized = T::localize_from(cfg, template, &next_state, &callee_end_state, call);
                                self.join_state(ctx, Option::Some(next_blk), &caller_localized)
                            }
                            else {
                                false
                            }
                        }
                        Edge::LoopEntry(entry) => {
                            T::assume_expr(&mut next_state, cfg, template, &entry.cond, false);
                            self.join_state(ctx, Option::Some(next_blk), &next_state)
                        }
                        Edge::LoopExit(exit) => {
                            T::assume_expr(&mut next_state, cfg, template, &exit.cond, true);
                            self.join_state(ctx, Option::Some(next_blk), &next_state)
                        }
                        Edge::If(entry) => {
                            T::assume_expr(&mut next_state, cfg, template, &entry.cond, false);
                            self.join_state(ctx, Option::Some(next_blk), &next_state)
                        }
                        Edge::Else(entry) => {
                            T::assume_expr(&mut next_state, cfg, template, &entry.cond, true);
                            self.join_state(ctx, Option::Some(next_blk), &next_state)
                        }
                        Edge::Backedge(_) => {
                            self.widen_state(ctx, Option::Some(next_blk), &next_state)
                        }
                        _ => {
                            self.join_state(ctx, Option::Some(next_blk), &next_state)
                        }
                    };

                    modified = modifies_next || modified;

                    if modifies_next && !in_worklist.contains(&next_id) {
                        in_worklist.insert(next_id);
                        worklist.push(next_id);
                    }
                }
            }
        }

        false
    }

    fn narrow_template(&mut self, cfg: &CFG, ctx: &Self::Context, template: &Template) -> bool {
        /*let mut worklist: Vec<usize> = template.body.values()
            .filter(|blk| blk.next.iter().any(|e| if let Edge::LoopEntry(_) = e {true} else {false})).map(|blk| blk.id).collect();
        let mut in_worklist = HashSet::new();*/
        let mut worklist: Vec<usize> = template.body.keys().cloned().sorted().rev().collect();
        let mut in_worklist: HashSet<usize> = worklist.iter().cloned().collect();
        let mut modified = false;

        while !worklist.is_empty() {
            let cur_id = worklist.pop().unwrap();
            println!("narrowing {}", cur_id);
            in_worklist.remove(&cur_id);
            let cur_blk = template.body.get(&cur_id).unwrap();

            let mut new_state = A::empty();
            for e in &cur_blk.prev {
                let prev_id = e.local_prev();
                let prev_blk = template.body.get(&prev_id).unwrap();
                let mut prev_state = self.get_state(ctx, Option::Some(prev_blk)).unwrap();
                let mut next_state = T::interpret_blk(prev_state, cfg, template, prev_blk);

                match e {
                    Edge::Call(call) => {
                        let callee_template = cfg.templates.get(&call.to).unwrap();
                        let callee_start_state = self.get_start_state(ctx, callee_template);
                        let is_empty = callee_start_state.is_err();
                        let empty_state = A::empty();
                        let callee_localized = T::localize_to(cfg, template, &next_state, &callee_start_state.as_ref().unwrap_or(&&empty_state), call);
                        let callee_ctx = Self::update_context(ctx, call);
                        if self.join_start_state(&callee_ctx, callee_template, &callee_localized) || is_empty {
                            self.analyze_template(cfg, &callee_ctx, callee_template);
                        }

                        let callee_end_state = self.get_end_state(&callee_ctx, callee_template).unwrap();
                        next_state = T::localize_from(cfg, template, &next_state, &callee_end_state, call);
                    }
                    Edge::LoopEntry(entry) => {
                        T::assume_expr(&mut next_state, cfg, template, &entry.cond, false);
                    }
                    Edge::LoopExit(exit) => {
                        T::assume_expr(&mut next_state, cfg, template, &exit.cond, true);
                    }
                    Edge::If(entry) => {
                        T::assume_expr(&mut next_state, cfg, template, &entry.cond, false);
                    }
                    Edge::Else(entry) => {
                        T::assume_expr(&mut next_state, cfg, template, &entry.cond, true);
                    }
                    _ => {
                        /* Skip */
                    }
                };

                for (_, (before_ref, after_ref)) in e.ssa_local_renaming(template).unwrap() {
                    let before_state = next_state.get_value(&before_ref);
                    next_state.set_value(cfg, template, &after_ref, &before_state);
                }

                new_state = new_state.join(&next_state);
            }

            if self.narrow_state(ctx, Some(cur_blk), &new_state) {
                modified = true;
                for next in &cur_blk.next {
                    let next_id = next.local_next();
                    if !in_worklist.contains(&next_id) {
                        in_worklist.insert(next_id);
                        worklist.push(next_id);
                    }
                }
            }
        }

        let end_blk = template.body.get(&template.exit_id).unwrap();
        let mut prev_state = self.get_state(ctx, Option::Some(end_blk)).unwrap();
        let mut next_state = T::interpret_blk(prev_state, cfg, template, end_blk);
        self.narrow_state(ctx, Option::None, &next_state) || modified
    }

    fn analyze(&mut self, cfg: &CFG, start_template: &Template, init_state: A) {
        let ctx = Self::init_context(cfg, start_template);
        self.join_start_state(&ctx, start_template, &init_state);
        while self.analyze_template(cfg, &ctx, start_template) {}

        for ctx in self.all_contexts() {
            let template = Self::get_context_template(cfg, &ctx).unwrap();
            println!("===== {} widening state =====", template.name);
            let result = self.get_end_state(&ctx, template).unwrap();
            println!("{}", result);

            for (bid, blk) in &template.body {
                println!("Block: {}", bid);
                let result = self.get_state(&ctx, Some(blk)).unwrap();
                println!("{}", result);
            }
        }

        if(D::should_narrow()) {
            //identify join starting points
            println!("===== start narrowing =====");
            while self.narrow_template(cfg, &ctx, start_template) {}
            for ctx in self.all_contexts() {
                let template = Self::get_context_template(cfg, &ctx).unwrap();
                println!("===== {} narrowing state =====", template.name);
                let result = self.get_end_state(&ctx, template).unwrap();
                println!("{}", result);

                for (bid, blk) in &template.body {
                    println!("Block: {}", bid);
                    let result = self.get_state(&ctx, Some(blk)).unwrap();
                    println!("{}", result);
                }
                println!("===== Done =====");
            }
        }
    }
}