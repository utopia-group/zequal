use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::ops::Neg;
use itertools::Itertools;

use cfg::block::Block;
use cfg::cfg::CFG;
use cfg::edge::{Call, Edge, NegInvariantCondition};
use cfg::expr::expression::Expr;
use cfg::expr::invariant::InvariantExpr;
use cfg::expr::var_access::AccessList;
use cfg::expr::variable_ref::{Ref, VarRef};
use cfg::named_storage::{Component, NamedStorage};
use cfg::stmt::statement::{Statement, Stmt};
use cfg::template::Template;

use crate::interpreter::expression_interpreter::ExpressionInterpreter;
use crate::interpreter::invariant_interpreter::InvariantInterpreter;
use crate::solver::solver_utils::{SmtUtils, ValidityResult};
use crate::utils::condition_term::ConditionTerm;
use crate::utils::error::VerificationError;
use crate::utils::template_context::TemplateContext;
use crate::utils::wrapped_smt_term::{LazyTerm, VCTerm};

//pub(crate) type TemplateContext<'glob> = (&'glob CFG<'glob>, &'glob Template<'glob>);

pub trait VCGenerator<T: VCTerm + LazyTerm> : ExpressionInterpreter<T> + InvariantInterpreter<T> + SmtUtils<T> {
    /*fn wp_stmt_without_assume(&mut self, ctx: &TemplateContext, stmt: &Statement, post: ConditionTerm<T>) -> Result<ConditionTerm<T>, VerificationError> {
        match stmt {
            Statement::Declare(_) => {
                Ok(post)
            }
            Statement::Assert(s) => {
                let assert = self.interpret_inv(ctx, s.expr())?;
                post.add_assert(assert)
            }
            Statement::Assume(s) => {
                let assume = self.interpret_inv(ctx, s.expr())?;
                post.add_assume(assume)
            }
            Statement::AssignVar(s) => {
                let rhs_expr_w = self.interpret_expr(ctx, s.rhs(), false)?;
                let lhs_expr_w = self.read_var(ctx, s.lhs(), false)?;
                let (lhs_sub, rhs_sub) = lhs_expr_w.to_sub_val(rhs_expr_w)?;
                post.transform(None, |t: T| t.substitute(lhs_sub.clone(), rhs_sub.clone()))
            }
            Statement::AssignSig(s) => {
                let rhs_expr_w = self.interpret_expr(ctx, s.rhs(), false)?;
                let lhs_expr_w = self.read_var(ctx, s.lhs(), false)?;

                /*Rather than modeling as an assignment, we will model this as an assumption since the solver seems
                      to perform better this way. It is sound since all signals can only be assigned to once and it may
                      only be constrained after assigned*/
                let (lhs_sub, rhs_sub) = lhs_expr_w.to_sub_val(rhs_expr_w)?;
                let mut sub_post = post.transform(None, |t: T| t.substitute(lhs_sub.clone(), rhs_sub.clone()))?;
                if s.constrain() {
                    let lhs_expr_c = self.read_var(ctx, s.lhs(), true)?;
                    let rhs_expr_c = self.interpret_expr(ctx, s.rhs(), true)?;
                    sub_post = sub_post.add_assume(lhs_expr_c.eq(rhs_expr_c)?)?;
                };

                //Ok(ConditionTerm::new(post.assumes.and(eq)?, post.asserts))
                Ok(sub_post)
            }
            Statement::Constrain(s) => {
                let lhs_expr_w = self.interpret_expr(ctx, s.lhs(), false)?;
                let rhs_expr_w = self.interpret_expr(ctx, s.rhs(), false)?;
                let lhs_expr_c = self.interpret_expr(ctx, s.lhs(), true)?;
                let rhs_expr_c = self.interpret_expr(ctx, s.rhs(), true)?;
                let eq_w = lhs_expr_w.eq(rhs_expr_w)?;
                let eq_c = lhs_expr_c.eq(rhs_expr_c)?;
                let new_post = if eq_c == eq_w {
                    post
                }
                else {
                    post.add_assert(eq_w)?
                };
                //Ok(ConditionTerm::new(new_post.assumes.and(eq_c)?, new_post.asserts))
                new_post.add_assume(eq_c)
            }
        }
    }

    fn wp_block_without_assume(&mut self, ctx: &TemplateContext, blk: &Block, post: ConditionTerm<T>) -> Result<ConditionTerm<T>, VerificationError> {
        let mut blk_wp = post;
        for stmt in blk.stmts.iter().rev() {
            blk_wp = self.wp_stmt_without_assume(ctx, stmt, blk_wp)?;
        }

        Ok(blk_wp)
    }

    fn verify_body_without_assume(&mut self, ctx: &TemplateContext, start: usize, target: usize, post: ConditionTerm<T>) -> Result<ConditionTerm<T>, VerificationError> {
        let template = ctx.template;
        let mut wp_ins = HashMap::new();
        wp_ins.insert(start, vec![post]);
        let empty = vec![];

        let mut worklist = vec![start];
        while !worklist.is_empty() {
            let blk_id = worklist.pop().unwrap();
            let blk = template.body.get(&blk_id).unwrap();
            let blk_posts = wp_ins.get(&blk_id).unwrap_or(&empty);

            // only visit one of the loop edges (either entry or exit)
            if blk_id != start && blk.next.iter().filter(|e| if let Edge::LoopEntry(_) = e {false} else {true}).count() != blk_posts.len() {
                continue;
            }

            let blk_post = ConditionTerm::join(blk_posts)?;
            let cur_wp = self.wp_block_without_assume(ctx, blk, blk_post)?;

            if blk_id == target {
                return Ok(cur_wp)
            }

            for edge in &blk.prev {
                if let Edge::Backedge(_) = edge {
                    continue;
                }
                let prev_wp = self.verify_edge(ctx, edge, &cur_wp)?;
                let local_prev = edge.local_prev();
                if let Some(wps) = wp_ins.get_mut(&local_prev) {
                    wps.push(prev_wp);
                }
                else {
                    wp_ins.insert(local_prev, vec![prev_wp]);
                }

                worklist.push(local_prev);
            }
        }

        Err("Never found target")?
    }*/

    fn is_equivalent(&self, ctx: &TemplateContext, v_ref: &Ref,) -> bool;

    fn rename_to_prev_version(&mut self, ctx: &TemplateContext, block: &Block, ind: usize, v_ref: &Ref, expr: T) -> Result<T, VerificationError> {
        let (component_opt, store) = ctx.template.get_referenced(ctx.cfg, v_ref)?;
        match (component_opt, store) {
            (None, NamedStorage::Variable(var)) => {
                let mut v = HashSet::new();
                let cur = block.ref_var_before(var, AccessList::empty(), true, true, ind + 1)?;
                let cur_term_c = self.read_var(ctx, &cur, false)?;
                let cur_term_w = self.read_var(ctx, &cur, true)?;
                v.insert(&cur_term_c);
                v.insert(&cur_term_w);
                if expr.contains(&v) {
                    let prev = block.ref_var_before(var, AccessList::empty(), true, true, ind)?;
                    let prev_term_w = self.read_var(ctx, &prev, true)?;
                    let prev_term_c = self.read_var(ctx, &prev, false)?;
                    let expr_w_sub = expr.substitute(cur_term_w, prev_term_w)?;
                    Ok(expr_w_sub.substitute(cur_term_c, prev_term_c)?)
                }
                else {
                    Ok(expr)
                }
            }
            _ => {
                Ok(expr)
            }
        }
    }

    fn wp_stmt_with_assume(&mut self, ctx: &TemplateContext, block: &Block, ind: usize, stmt: &Statement, post: ConditionTerm<T>) -> Result<ConditionTerm<T>, VerificationError> {
        match stmt {
            Statement::Declare(_) => {
                Ok(post)
            }
            Statement::Assert(s) => {
                let assert = self.interpret_inv(ctx, s.expr())?;
                post.add_assert(assert)
            }
            Statement::Assume(s) => {
                let assume = self.interpret_inv(ctx, s.expr())?;
                post.add_assume(assume)
            }
            Statement::AssignVar(s) => {
                let rhs_expr_w = self.interpret_expr(ctx, s.rhs(), false)?;
                let rhs_ind_w = self.get_all_array_access_bounds(ctx, s.rhs(), false)?;
                let lhs_expr_w = self.read_var(ctx, s.lhs(), false)?;
                let lhs_ind_w = self.get_array_access_bounds(ctx, s.lhs(), false)?;
                let lhs_expr_c = self.read_var(ctx, s.lhs(), true)?;

                if lhs_expr_c == lhs_expr_w {
                    for rhs_var in s.rhs().variable_refs() {
                        //changing to this check because aux vars might cause the rhs expression not to look equivalent
                        let rhs_var_w = self.read_var(ctx, rhs_var, false)?;
                        let rhs_var_c = self.read_var(ctx, rhs_var, true)?;
                        if rhs_var_w != rhs_var_c {
                            let rhs_expr_c = self.interpret_expr(ctx, s.rhs(), true)?;
                            println!("lhs: {lhs_expr_c}");
                            println!("rhs_w: {rhs_expr_w}");
                            println!("rhs_c: {rhs_expr_c}");
                            panic!("Found a case where the lhs is supposed to be equiv but rhs is not")
                        }
                    }

                    let (lhs_sub, rhs_sub) = lhs_expr_w.to_sub_val(rhs_expr_w)?;
                    let rhs_renamed = self.rename_to_prev_version(ctx, block, ind, s.lhs(), rhs_sub)?;
                    post.transform(None, |t: T| t.substitute(lhs_sub.clone(), rhs_renamed.clone()))?
                        .add_assume(rhs_ind_w)?
                        .add_assume(lhs_ind_w)
                }
                else {
                    let rhs_ind_c = self.get_all_array_access_bounds(ctx, s.rhs(), true)?;
                    let lhs_ind_c = self.get_array_access_bounds(ctx, s.lhs(), true)?;
                    let rhs_expr_c = self.interpret_expr(ctx, s.rhs(), true)?;
                    let (lhs_sub_w, rhs_sub_w) = lhs_expr_w.to_sub_val(rhs_expr_w)?;
                    let rhs_renamed_w = self.rename_to_prev_version(ctx, block, ind, s.lhs(), rhs_sub_w)?;
                    let post_w_sub = post.transform(None, |t: T| t.substitute(lhs_sub_w.clone(), rhs_renamed_w.clone()))?;
                    let (lhs_sub_c, rhs_sub_c) = lhs_expr_c.to_sub_val(rhs_expr_c)?;
                    let rhs_renamed_c = self.rename_to_prev_version(ctx, block, ind, s.lhs(), rhs_sub_c)?;
                    post_w_sub.transform(None, |t: T| t.substitute(lhs_sub_c.clone(), rhs_renamed_c.clone()))?
                        .add_assume(rhs_ind_w)?
                        .add_assume(lhs_ind_w)?
                        .add_assume(rhs_ind_c)?
                        .add_assume(lhs_ind_c)
                }
            }
            Statement::AssignSig(s) => {
                let rhs_expr_w = self.interpret_expr(ctx, s.rhs(), false)?;
                let mut rhs_ind = self.get_all_array_access_bounds(ctx, s.rhs(), false)?;
                let lhs_expr_w = self.read_var(ctx, s.lhs(), false)?;
                let mut lhs_ind = self.get_array_access_bounds(ctx, s.lhs(), false)?;

                /*Rather than modeling as an assignment, we will model this as an assumption since the solver seems
                      to perform better this way. It is sound since all signals can only be assigned to once and it may
                      only be constrained after assigned*/
                let mut eq = lhs_expr_w.eq(rhs_expr_w)?;
                if s.constrain() {
                    let lhs_expr_c = self.read_var(ctx, s.lhs(), true)?;
                    let rhs_expr_c = self.interpret_expr(ctx, s.rhs(), true)?;
                    let rhs_ind_c = self.get_all_array_access_bounds(ctx, s.rhs(), true)?;
                    let lhs_ind_c = self.get_array_access_bounds(ctx, s.lhs(), true)?;
                    rhs_ind = rhs_ind.and(rhs_ind_c)?;
                    lhs_ind = lhs_ind.and(lhs_ind_c)?;
                    let eq_c = lhs_expr_c.eq(rhs_expr_c)?;
                    if eq != eq_c {
                        eq = eq.and(eq_c)?;
                    }
                }

                //Ok(ConditionTerm::new(post.assumes.and(eq)?, post.asserts))
                post.add_assume(eq)?
                    .add_assume(rhs_ind)?
                    .add_assume(lhs_ind)
            }
            Statement::Constrain(s) => {
                let lhs_expr_w = self.interpret_expr(ctx, s.lhs(), false)?;
                let lhs_ind_w = self.get_all_array_access_bounds(ctx, s.lhs(), false)?;
                let rhs_expr_w = self.interpret_expr(ctx, s.rhs(), false)?;
                let rhs_ind_w = self.get_all_array_access_bounds(ctx, s.rhs(), false)?;
                let lhs_expr_c = self.interpret_expr(ctx, s.lhs(), true)?;
                let lhs_ind_c = self.get_all_array_access_bounds(ctx, s.lhs(), true)?;
                let rhs_expr_c = self.interpret_expr(ctx, s.rhs(), true)?;
                let rhs_ind_c = self.get_all_array_access_bounds(ctx, s.rhs(), true)?;
                let eq_w = lhs_expr_w.eq(rhs_expr_w)?;
                let eq_c = lhs_expr_c.eq(rhs_expr_c)?;
                let new_post = if eq_c == eq_w {
                    post
                        .add_assume(lhs_ind_w)?
                        .add_assume(rhs_ind_w)?
                }
                else {
                    post.add_assert(eq_w)?
                        .add_assume(lhs_ind_c)?
                        .add_assume(lhs_ind_w)?
                        .add_assume(rhs_ind_c)?
                        .add_assume(rhs_ind_w)?
                };
                //Ok(ConditionTerm::new(new_post.assumes.and(eq_c)?, new_post.asserts))
                new_post.add_assume(eq_c)
            }
        }
    }

    fn wp_block(&mut self, ctx: &TemplateContext, blk: &Block, post: ConditionTerm<T>) -> Result<ConditionTerm<T>, VerificationError> {
        let mut blk_wp = post;
        for (ind, stmt) in blk.stmts.iter().enumerate().rev() {
            blk_wp = self.wp_stmt_with_assume(ctx, blk, ind, stmt, blk_wp)?;
        }

        Ok(blk_wp)
    }

    //fn infer_strengthenings(&mut self, ctx: &TemplateContext, exit_edge: &NegInvariantCondition, post: &ConditionTerm<T>) -> Result<Vec<T>, VerificationError>;

    fn verify_loop_inductiveness_with_inv(&mut self, ctx: &TemplateContext, exit_edge: &NegInvariantCondition, initial_inv: &InvariantExpr, post: &ConditionTerm<T>, strengthening: &Option<T>) -> Result<T, VerificationError> {
        let template = ctx.template;
        let cond = self.interpret_expr(ctx, &exit_edge.cond, false)?;
        let mut inv = self.interpret_inv(ctx, initial_inv)?;
        if let Some(strengthen_pred) = &strengthening {
            inv = inv.and(strengthen_pred.clone())?;
        }

        let loop_head = template.body.get(&exit_edge.prev).unwrap();
        let backedge = loop_head.prev.iter()
            .find(|e|
                if let Edge::Backedge(_) = e {true} else {false}
            ).ok_or("Could not find backedge")?;

        let inv_condition = ConditionTerm::new(None, inv.clone());
        let loop_body_inv = self.rename_ssa_vars(ctx, backedge, inv_condition)?;
        let body_wp = self.verify_body(ctx, backedge.local_prev(), backedge.local_next(), loop_body_inv)?;
        let ind_check = body_wp.clone().add_assume(cond.clone().and(inv.clone())?)?;
        let result = self.check_validity(ind_check.to_term()?, true)?;

        match result {
            ValidityResult::Invalid(model) => {
                /*if strengthening.is_none() {
                    let mut strengthenings = self.infer_strengthenings(ctx, exit_edge, &body_wp)?;
                    let strongest = T::and_all(strengthenings.clone())?;
                    println!("checking {}", strongest);
                    let strongest_res = self.verify_loop_inductiveness_with_inv(ctx, exit_edge, initial_inv, post, &Some(strongest));
                    if strongest_res.is_err() {
                        return strongest_res
                    }
                    else {
                        let mut required_strengthenings = vec![];
                        while !strengthenings.is_empty() {
                            let pred = strengthenings.pop().unwrap();

                            let mut cur_strengthenings = strengthenings.clone();
                            cur_strengthenings.append(&mut required_strengthenings.clone());
                            let strengthen_pred = T::and_all(cur_strengthenings)?;
                            println!("Attempting {}", strengthen_pred.to_string());
                            let result = self.verify_loop_inductiveness_with_inv(ctx, exit_edge, initial_inv, post, &Some(strengthen_pred));
                            if result.is_err() {
                                required_strengthenings.push(pred)
                            }
                        }
                        let strengthening_term = T::and_all(required_strengthenings)?;
                        println!("Found Strengthening {}", strengthening_term.to_string());
                        //Ok(inv.and(strengthening_term)?)
                        Ok(inv.and(strengthening_term)?)
                    }
                }
                else {*/
                    Err(VerificationError::InvariantNotInductive(initial_inv.clone(), model))
                //}
            }
            ValidityResult::Valid => {
                Ok(inv)
            }
            ValidityResult::Unknown => {
                Err("Solver returned unknown when checking invariant VC")?
            }
        }
    }

    fn verify_loop_vc_with_inv(&mut self, ctx: &TemplateContext, exit_edge: &NegInvariantCondition, initial_inv: &InvariantExpr, post: &ConditionTerm<T>, strengthening: &Option<T>) -> Result<ConditionTerm<T>, VerificationError> {
        let cond = self.interpret_expr(ctx, &exit_edge.cond, false)?;
        let inv = self.verify_loop_inductiveness_with_inv(ctx, exit_edge, initial_inv, post, strengthening)?;

        let post_check = post.clone().add_assume(cond.not()?.and(inv.clone())?)?;
        let result = self.check_validity(post_check.to_term()?, true)?;

        match result {
            ValidityResult::Invalid(model) => {
                /*if strengthening.is_none() {
                    //need to also consider the strengthening made with respect to inductiveness
                    //let post_wp = inv.clone().and(post.clone())?;
                    let post_wp = post.clone().add_assert(inv.clone())?;
                    let mut strengthenings = self.infer_strengthenings(ctx, exit_edge, &post_wp)?;
                    let strongest = T::and_all(strengthenings.clone())?;
                    println!("checking {}", strongest);
                    let strongest_res = self.verify_loop_vc_with_inv(ctx, exit_edge, initial_inv, post, &Some(strongest));
                    if strongest_res.is_err() {
                        strongest_res
                        //Err(VerificationError::InvariantDoesNotImplyPost(exit_edge.inv.as_ref().unwrap().clone(), post.clone(), model))
                    }
                    else {
                        let mut required_strengthenings = vec![];
                        while !strengthenings.is_empty() {
                            let pred = strengthenings.pop().unwrap();

                            let mut cur_strengthenings = strengthenings.clone();
                            cur_strengthenings.append(&mut required_strengthenings.clone());
                            let strengthen_pred = T::and_all(cur_strengthenings)?;
                            println!("Attempting {}", strengthen_pred.to_string());
                            let result = self.verify_loop_vc_with_inv(ctx, exit_edge, initial_inv, post, &Some(strengthen_pred));
                            if result.is_err() {
                                required_strengthenings.push(pred)
                            }
                        }
                        let strengthening_term = T::and_all(required_strengthenings)?;
                        println!("Found Strengthening {}", strengthening_term.to_string());
                        Ok(ConditionTerm::new(None, inv.and(strengthening_term)?))
                    }
                }
                else {*/
                    Err(VerificationError::InvariantDoesNotImplyPost(initial_inv.clone(), post.clone().to_term()?.to_string(), model))
                //}
            }
            ValidityResult::Valid => {
                Ok(ConditionTerm::new(None, inv))
            }
            ValidityResult::Unknown => {
                Err("Solver returned unknown when checking if invariant implies postcondition")?
            }
        }
    }

    fn gen_loop_inv(&mut self, ctx: &TemplateContext, exit_edge: &NegInvariantCondition, post: &ConditionTerm<T>) -> Result<InvariantExpr, VerificationError>;
    fn get_cached_inv(&self, ctx: &TemplateContext, exit_edge: &NegInvariantCondition) -> Vec<InvariantExpr>;
    fn cache_inv(&mut self, ctx: &TemplateContext, exit_edge: &NegInvariantCondition, inv: InvariantExpr);

    fn find_cached_inv(&mut self, ctx: &TemplateContext, exit_edge: &NegInvariantCondition, post: &ConditionTerm<T>) -> Result<ConditionTerm<T>, VerificationError> {
        let cached_invs = self.get_cached_inv(ctx, exit_edge);
        for cached_inv in cached_invs {
            let cond = self.verify_loop_vc_with_inv(ctx, exit_edge, &cached_inv, post, &None);
            match cond {
                Ok(cond) => {
                    return Ok(cond)
                }
                Err(_) => {/* Skip */}
            }
        }

        Err(VerificationError::Msg("Could not find a cached invariant that holds"))
    }

    fn verify_loop_vc(&mut self, ctx: &TemplateContext, exit_edge: &NegInvariantCondition, post: &ConditionTerm<T>) -> Result<ConditionTerm<T>, VerificationError> {
        match &exit_edge.declared_inv {
            None => {
                let cached_inv = self.find_cached_inv(ctx, exit_edge, post);
                match cached_inv {
                    Ok(i) => {
                        println!("Using cached invariant");
                        return Ok(i)
                    }
                    Err(_) => {
                        let inferred_inv = self.gen_loop_inv(ctx, exit_edge, post)?;
                        let cond = self.verify_loop_vc_with_inv(ctx, exit_edge, &inferred_inv, post, &None)?;
                        println!("THIS IS THE LOOP INVARIANT: {}", inferred_inv);
                        self.cache_inv(ctx, exit_edge, inferred_inv);
                        Ok(cond)
                    }
                }
            }
            Some(i) => {
                self.verify_loop_vc_with_inv(ctx, exit_edge, &i, post, &None)
            }
        }

        /*let inv = match &exit_edge.declared_inv {
            Some(i) => { i.clone() }
            None => {

                self.gen_loop_inv(ctx, exit_edge, post)?
            }
        };

        //let inv = self.gen_loop_inv(ctx, exit_edge, post)?;
        let cond = self.verify_loop_vc_with_inv(ctx, exit_edge, &inv, post, &None)?;
        println!("{}", cond);
        Ok(cond)*/
    }

    //fn verify_call_inline(&mut self, ctx: &TemplateContext, call: &Call, post: &ConditionTerm<T>) -> Result<ConditionTerm<T>, VerificationError>;
    fn verify_call_summary(&mut self, ctx: &TemplateContext, call: &Call, post: &ConditionTerm<T>) -> Result<ConditionTerm<T>, VerificationError>;

    fn rename_ssa_vars(&mut self, ctx: &TemplateContext, edge: &Edge, post: ConditionTerm<T>) -> Result<ConditionTerm<T>, VerificationError> {
        let renaming = edge.ssa_local_renaming(ctx.template)?;
        if renaming.is_empty() {
            return Ok(post)
        }

        let mut sub = HashMap::new();
        for (prev_version, next_version) in renaming.values() {
            sub.insert(self.interpret_ref(ctx, next_version, false)?, self.interpret_ref(ctx, prev_version, false)?);
            sub.insert(self.interpret_ref(ctx, next_version, true)?, self.interpret_ref(ctx, prev_version, true)?);
        }

        Ok(post.transform(None, |t| t.substitute_vars(&sub))?)
    }

    fn verify_edge(&mut self, ctx: &TemplateContext, edge: &Edge, post: &ConditionTerm<T>) -> Result<ConditionTerm<T>, VerificationError> {
        let edge_post = match edge {
            Edge::LoopExit(l) => {
                println!("Loop {} Post Condition: {}", edge.local_prev(), post.clone().to_term()?);
                self.verify_loop_vc(ctx, l, post)?
            }
            Edge::If(c) => {
                let cond = self.interpret_expr(ctx, &c.cond, false)?;
                ConditionTerm::new(None, post.clone().add_assume(cond)?.to_term()?)
            }
            Edge::Else(c) => {
                let cond = self.interpret_expr(ctx, &c.cond, false)?;
                ConditionTerm::new(None, post.clone().add_assume(cond.not()?)?.to_term()?)
            }
            Edge::Call(c) => {
                self.verify_call_summary(ctx, c, post)?
            }
            Edge::Backedge(_) => {
                unreachable!("A backedge should not be verified")
            }
            _ => {
                post.clone()
            }
        };

        self.rename_ssa_vars(ctx, edge, edge_post)
    }

    fn verify_body(&mut self, ctx: &TemplateContext, start: usize, target: usize, post: ConditionTerm<T>) -> Result<ConditionTerm<T>, VerificationError> {
        let template = ctx.template;
        let mut wp_ins = HashMap::new();
        wp_ins.insert(start, vec![post]);
        let empty = vec![];

        let mut worklist = vec![start];
        while !worklist.is_empty() {
            let blk_id = worklist.pop().unwrap();
            let blk = template.body.get(&blk_id).unwrap();
            let blk_posts = wp_ins.get(&blk_id).unwrap_or(&empty);

            // only visit one of the loop edges (either entry or exit)
            if blk_id != start && blk.next.iter().filter(|e| if let Edge::LoopEntry(_) = e {false} else {true}).count() != blk_posts.len() {
                continue;
            }

            let blk_post = ConditionTerm::join(blk_posts)?;
            let cur_wp = self.wp_block(ctx, blk, blk_post)?;

            if blk_id == target {
                return Ok(cur_wp)
            }

            for edge in &blk.prev {
                if let Edge::Backedge(_) = edge {
                    continue;
                }
                let prev_wp = self.verify_edge(ctx, edge, &cur_wp)?;
                let local_prev = edge.local_prev();
                if let Some(wps) = wp_ins.get_mut(&local_prev) {
                    wps.push(prev_wp);
                }
                else {
                    wp_ins.insert(local_prev, vec![prev_wp]);
                }

                worklist.push(local_prev);
            }
        }

        Err("Never found target")?
    }

    fn verify_template(&mut self, ctx: &TemplateContext, post: ConditionTerm<T>) -> Result<ConditionTerm<T>, VerificationError> {
        self.verify_body(ctx, ctx.template.exit_id, ctx.template.entry_id, post)
    }

    fn verify_cfg(&mut self, cfg: &CFG, pre: T, post: T) -> Result<(), VerificationError> {
        let entry_template = cfg.templates.get(&cfg.entry).unwrap();
        let ctx = TemplateContext::new(cfg, entry_template, vec![]);
        let wp = self.verify_template(&ctx, ConditionTerm::new(None, post.clone()))?;
        let validity_check = wp.clone().add_assume(pre.clone())?;
        let result = self.check_validity(validity_check.to_term()?, true)?;
        match result {
            ValidityResult::Invalid(model) => {
                Err(VerificationError::PostconditionNotImplied(pre.to_string(), wp.to_string(), model))
            }
            ValidityResult::Valid => {
                Ok(())
            }
            ValidityResult::Unknown => {
                Err("Sovler returned unknown when checking if invariant implies postcondition")?
            }
        }?;
        Ok(())
    }
}
