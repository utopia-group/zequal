use cfg::expr::invariant::InvariantExpr;
use crate::interpreter::expression_interpreter::{ExpressionInterpreter};
use crate::smt::smt::Quantifier;
use crate::utils::error::VerificationError;
use crate::utils::template_context::TemplateContext;
use crate::utils::wrapped_smt_term::VCTerm;

pub trait InvariantInterpreter<T: VCTerm>: ExpressionInterpreter<T> {

    fn interpret_inv(&mut self, ctx: &TemplateContext, expr: &InvariantExpr) -> Result<T, VerificationError> {
        match expr {
            InvariantExpr::Forall(vars, e) => {
                for v in vars {
                    let adjusted_name = format!("v_{}.0", v);
                    self.add_quantified_var(ctx, &adjusted_name, T::variable_sort())?;
                }
                let nested_inv = self.interpret_inv(ctx, e)?;
                let sort_vars = vars.iter().map(|n| (format!("v_{}.0", n), T::variable_sort())).collect();
                let inv = nested_inv.quantify(Quantifier::Forall, sort_vars);
                for v in vars {
                    let adjusted_name = format!("v_{}.0", v);
                    self.remove_quantified_var(ctx, &adjusted_name)?
                }
                Ok(inv?)
            }
            InvariantExpr::Exists(vars, e) => {
                for v in vars {
                    let adjusted_name = format!("v_{}.0", v);
                    self.add_quantified_var(ctx, &adjusted_name, T::variable_sort())?;
                }
                let nested_inv = self.interpret_inv(ctx, e)?;
                let sort_vars = vars.iter().map(|n| (format!("v_{}.0", n), T::variable_sort())).collect();
                let inv = nested_inv.quantify(Quantifier::Exists, sort_vars);
                for v in vars {
                    let adjusted_name = format!("v_{}.0", v);
                    self.remove_quantified_var(ctx, &adjusted_name)?
                }
                Ok(inv?)
            }
            InvariantExpr::Expr(e) => {
                let expr_w = self.interpret_expr(ctx, e, false)?;
                let expr_c = self.interpret_expr(ctx, e, true)?;

                let inv = if expr_w.term() == expr_c.term() {
                    expr_c
                }
                else {
                    expr_w.and(expr_c)?
                };

                Ok(inv)
            }
        }
    }
}

