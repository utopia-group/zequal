use std::collections::{HashMap, HashSet};

use cfg::edge::{Edge, NegInvariantCondition};
use cfg::expr::expression::Expression;
use cfg::expr::invariant::InvariantExpr;
use cfg::expr::literal::Literal;
use crate::hoare_logic::vc_generator::VCGenerator;

use crate::utils::condition_term::ConditionTerm;
use crate::utils::error::VerificationError;
use crate::utils::template_context::TemplateContext;
use crate::utils::wrapped_smt_term::{LazyTerm, VCTerm};

pub trait Houdini<T: VCTerm + LazyTerm>: VCGenerator<T> {
    fn infer_loop_invariant(&mut self, ctx: &TemplateContext, required_candidates: Vec<InvariantExpr>, possible_candidates: Vec<InvariantExpr>, loop_it_eqs: Vec<InvariantExpr>, loop_exit: &NegInvariantCondition, minimize: bool) -> Result<InvariantExpr, VerificationError> {
        let it_eq = InvariantExpr::and_all(loop_it_eqs)?;
        let it_eq_term = self.interpret_inv(ctx, &it_eq)?;
        let it_knowledge = it_eq_term;
        let mut smt_to_expr = HashMap::new();
        let mut required_preds = HashSet::new();
        for candidate in &required_candidates {
            let smt_candidate = self.interpret_inv(ctx, candidate)?;
            required_preds.insert(smt_candidate.clone());
            smt_to_expr.insert(smt_candidate, candidate.clone());
        }

        let mut candidate_preds = vec![];
        for candidate in possible_candidates {
            let smt_candidate = self.interpret_inv(ctx, &candidate)?;
            candidate_preds.push(smt_candidate.clone());
            smt_to_expr.insert(smt_candidate, candidate);
        }

        let mut inv_preds: Vec<T> = required_preds.iter().cloned().collect();
        inv_preds.extend(candidate_preds);

        let cond = self.interpret_expr(ctx, &loop_exit.cond, false)?;
        let loop_head = ctx.template.get_block(&loop_exit.prev)?;
        let backedge = loop_head.prev.iter()
            .find(|e|
            if let Edge::Backedge(_) = e {true} else {false}
            ).ok_or("Could not find backedge")?;

        let mut inv = T::and_all(inv_preds.clone())?;
        if self.check_sat(inv.clone(), false)?.is_unsat() {
            return Err(VerificationError::UnsatHoudiniCandidates)
        }

        loop {
            let mut cur_preds= vec![];

            for pred in &inv_preds {
                println!("pred: {}", pred);
                let pred_str = pred.to_string();
                let pred_condition = ConditionTerm::new(Some(it_knowledge.clone()), pred.clone());
                let loop_body_inv = self.rename_ssa_vars(ctx, backedge, pred_condition)?;
                println!("renamed loop inv: {}", loop_body_inv);
                let body_wp_opt = self.verify_body(ctx, backedge.local_prev(), backedge.local_next(), loop_body_inv);
                match body_wp_opt {
                    Ok(body_wp) => {
                        let ind_check = body_wp.clone().add_assume(cond.clone().and(inv.clone())?.and(it_knowledge.clone())?)?;
                        let result = self.check_validity(ind_check.to_term()?, true)?;
                        if result.is_valid() {
                            println!("adding: {}", pred);
                            cur_preds.push(pred.clone());
                        }
                        else {
                            println!("Couldn't prove inductiveness of predicate {}", pred);
                        }
                    }
                    Err(e) => { println!("Pred {} terminated because {}", pred, e) }
                }
            }

            if cur_preds.len() == inv_preds.len() {
                break;
            }

            inv_preds = cur_preds;
            inv = T::and_all(inv_preds.clone())?;
        }

        let mut inferred_inv= vec![it_eq.clone()];
        for pred in inv_preds {
            if let Some(pred_expr) = smt_to_expr.get(&pred) {
                inferred_inv.push(pred_expr.clone());
            }
            else {
                return Err(VerificationError::Msg("Could not map smt back to Expression"))
            }
        }

        /*minimize is expensive when there are nested loops
        if minimize {
            loop {
                let mut cur_inv = vec![];
                let prev_inv_size = inferred_inv.len();

                while let Some(pred) = inferred_inv.pop() {
                    if required_candidates.contains(&pred) || pred == it_eq || pred == it_bounds {
                        cur_inv.push(pred);
                    } else {
                        println!("Attempting to remove {}", pred);
                        let new_inv = InvariantExpr::and_all(inferred_inv.clone())?.and(&InvariantExpr::and_all(cur_inv.clone())?)?;
                        let res = self.verify_loop_inductiveness_with_inv(ctx, loop_exit, &new_inv, &ConditionTerm::new(None, true.into()), &None);
                        if let Err(e) = res {
                            println!("Could not remove {}", pred);
                            cur_inv.push(pred);
                        } else {
                            println!("Removed {}", pred);
                        }
                    }
                }

                inferred_inv = cur_inv;
                if inferred_inv.len() == prev_inv_size {
                    break;
                }
            }
        }*/

        Ok(InvariantExpr::and_all(inferred_inv)?)
    }
}
