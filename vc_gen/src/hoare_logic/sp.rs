use std::collections::HashMap;
use cfg::block::Block;
use cfg::cfg::CFG;
use cfg::edge::{Call, Edge, NegInvariantCondition};
use cfg::expr::invariant::InvariantExpr;
use cfg::stmt::statement::Statement;
use crate::interpreter::expression_interpreter::ExpressionInterpreter;
use crate::interpreter::invariant_interpreter::InvariantInterpreter;
use crate::solver::solver_utils::{SmtUtils, ValidityResult};
use crate::utils::condition_term::ConditionTerm;
use crate::utils::error::VerificationError;
use crate::utils::template_context::TemplateContext;
use crate::utils::wrapped_smt_term::{LazyTerm, VCTerm};

pub trait Sp<T: VCTerm + LazyTerm> : ExpressionInterpreter<T> + InvariantInterpreter<T> + SmtUtils<T> {
    fn sp_stmt(&mut self, ctx: &TemplateContext, stmt: &Statement, pre: T) -> Result<T, VerificationError> {
        match stmt {
            Statement::Declare(_) => {
                Ok(pre)
            }
            Statement::Assert(s) => {
                let assert_expr = self.interpret_inv(ctx, s.expr())?;
                let check = pre.clone().implies(assert_expr.clone())?;
                let res = self.check_validity(check, true)?;
                match res {
                    ValidityResult::Valid => { /* Everything is good, continue */ }
                    ValidityResult::Invalid(_) => { return Err(VerificationError::Msg("Could not prove assertion")) }
                    ValidityResult::Unknown => { return Err(VerificationError::Msg("Solver returned unknown when checking assertion")) }
                }
                Ok(pre.and(assert_expr)?)
            }
            Statement::Assume(s) => {
                let assumption = self.interpret_inv(ctx, s.expr())?;
                Ok(pre.and(assumption)?)
            }
            Statement::AssignVar(s) => {
                let rhs_expr_w = self.interpret_expr(ctx, s.rhs(), false)?;
                let lhs_expr_w = self.read_var(ctx, s.lhs(), false)?;
                // This is in SSA
                Ok(pre.and(lhs_expr_w.eq(rhs_expr_w)?)?)
            }
            Statement::Constrain(s) => {
                let lhs_expr_w = self.interpret_expr(ctx, s.lhs(), false)?;
                let rhs_expr_w = self.interpret_expr(ctx, s.rhs(), false)?;
                let lhs_expr_c = self.interpret_expr(ctx, s.lhs(), true)?;
                let rhs_expr_c = self.interpret_expr(ctx, s.rhs(), true)?;
                let eq_w = lhs_expr_w.eq(rhs_expr_w)?;
                let eq_c = lhs_expr_c.eq(rhs_expr_c)?;
                todo!("finish this");
            }
            Statement::AssignSig(_) => {
                todo!("finish this");
            }
        }
    }
    fn sp_block(&mut self, ctx: &TemplateContext, blk: &Block, pre: T) -> Result<T, VerificationError> {
        let mut blk_sp = pre;
        for stmt in &blk.stmts {
            blk_sp = self.sp_stmt(ctx, stmt, blk_sp)?;
        }

        Ok(blk_sp)
    }

    fn sp_edge(&mut self, ctx: &TemplateContext, edge: &Edge, pre: T) -> Result<T, VerificationError> {
        let edge_post = match edge {
            Edge::LoopExit(l) => {
                todo!("do exit")
            }
            Edge::If(c) => {
                todo!("merge previous version of variable with the next one and imply")
            }
            Edge::Else(c) => {
                todo!("merge previous version of variable with the next one and imply")
            }
            Edge::Call(c) => {
                todo!("Have to create summary")
            }
            Edge::Backedge(_) => {
                unreachable!("A backedge should not be verified")
            }
            _ => {
                todo!("Merge any variables")
            }
        };

        todo!("maybe do renaming");
    }

    fn sp_body(&mut self, ctx: &TemplateContext, start: usize, target: usize, pre: T) -> Result<T, VerificationError> {
        todo!("have to write this")
    }

    fn sp_template(&mut self, ctx: &TemplateContext, pre: T) -> Result<T, VerificationError> {
        self.sp_body(ctx, ctx.template.entry_id, ctx.template.exit_id, pre)
    }
}