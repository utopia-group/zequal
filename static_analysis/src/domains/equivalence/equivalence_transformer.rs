use std::marker::PhantomData;

use cfg::cfg::CFG;
use cfg::expr::expression::Expression;
use cfg::expr::literal::Literal;
use cfg::stmt::statement::Statement;
use cfg::template::Template;

use crate::analysis::{AbstractState, AbstractTransformer};
use crate::analysis::DomainValue;
use crate::domains::equivalence::equivalence_value::EquivalenceValue;

pub struct EquivalenceTransformer<A: AbstractState<EquivalenceValue>> {
    phantom: PhantomData<A>
}

impl<A: AbstractState<EquivalenceValue>> AbstractTransformer<EquivalenceValue, A> for EquivalenceTransformer<A> {
    fn interpret_expr(start: &A, cfg: &CFG, template: &Template, expr: &Expression) -> EquivalenceValue {
        match expr {
            Expression::BinOp(e) => {
                Self::interpret_expr(start, cfg, template, e.lhs())
                    .join(&Self::interpret_expr(start, cfg, template, e.rhs()))
            }
            Expression::UnOp(e) => {
                Self::interpret_expr(start, cfg, template, e.expr())
            }
            Expression::Ternary(e) => {
                Self::interpret_expr(start, cfg, template, e.cond())
                    .join(&Self::interpret_expr(start, cfg, template, e.true_case()))
                    .join(&Self::interpret_expr(start, cfg, template, e.false_case()))
            }
            Expression::Variable(e) => {
                start.get_value(e).clone()
            }
            Expression::Literal(e) => {
                 match e {
                     Literal::UniformArray(a) => {
                         Self::interpret_expr(start, cfg, template, a.val())
                     }
                     Literal::InlineArray(a) => {
                         a.entries()
                             .iter()
                             .fold(EquivalenceValue::bottom(), |acc, e| acc.join(&Self::interpret_expr(start, cfg, template, e)))
                     }
                     _ => {
                         EquivalenceValue::bottom()
                     }
                 }
            }
            Expression::Instantiate(i) => {
                let mut ret_equiv = EquivalenceValue::bottom();
                for arg in i.args() {
                    ret_equiv = ret_equiv.join(&Self::interpret_expr(start, cfg, template, arg));
                }
                ret_equiv
            }
            Expression::FunctionCall(c) => {
                let mut ret_equiv = EquivalenceValue::bottom();
                for arg in c.args() {
                    ret_equiv = ret_equiv.join(&Self::interpret_expr(start, cfg, template, arg));
                }
                ret_equiv
            }
        }
    }

    fn assume_expr(_start: &mut A, _cfg: &CFG, _template: &Template, _expr: &Expression, _negate: bool) {
        /* Assumptions will only further constrain a statement, so we can conservatively just skip them */
    }

    /*fn join_expr(start: &mut A, cfg: &CFG, template: &Template, expr: &Expression, val: &EquivalenceValue) {
        match expr {
            Expression::BinOp(e) => {
                Self::join_expr(start, cfg, template, e.lhs(), val);
                Self::join_expr(start, cfg, template, e.rhs(), val);
            }
            Expression::UnOp(e) => {
                Self::join_expr(start, cfg, template, e.expr(), val);
            }
            Expression::Ternary(e) => {
                Self::join_expr(start, cfg, template, e.cond(), val);
                Self::join_expr(start, cfg, template, e.true_case(), val);
                Self::join_expr(start, cfg, template, e.false_case(), val);
            }
            Expression::Variable(e) => {
                start.join_value(cfg, template, e, val);
            }
            Expression::Literal(e) => {
                match e {
                    Literal::UniformArray(a) => {
                        Self::join_expr(start, cfg, template, a.val(), val)
                    }
                    Literal::InlineArray(a) => {
                        a.entries()
                            .iter()
                            .for_each(|v| Self::join_expr(start, cfg, template, v, val))
                    }
                    // Skip
                    _ => {}
                }
            }
            // Skip
            Expression::Instantiate(_) => {}
        }
    }*/

    fn interpret_stmt_in_place(start: &mut A, cfg: &CFG, template: &Template, stmt: &Statement) {
        let bot = EquivalenceValue::bottom();
        let top = EquivalenceValue::top();

        match stmt {
            Statement::Declare(s) => {
                /* Skip, Abstract State defaults to bottom */
            }
            Statement::Assert(_) => {
                println!("Warning: assertions are not interpreted by static analysis")
            }
            Statement::Assume(_) => {
                println!("Warning: assumptions are not interpreted by static analysis")
            }
            Statement::AssignVar(s) => {
                let rhs_equiv = Self::interpret_expr(start, cfg, template, s.rhs());
                start.join_value(cfg, template, s.lhs(), &rhs_equiv);
            }
            Statement::Constrain(_) => {
                //constraints are added in both
            }
            Statement::AssignSig(s) => {
                if s.constrain() {
                    let rhs_equiv = Self::interpret_expr(start, cfg, template, s.rhs());
                    start.join_value(cfg, template, s.lhs(), &rhs_equiv);
                }
                else {
                    //for now we assume that the lhs of <-- will not be equivalent
                    start.set_value(cfg, template, s.lhs(), &top);
                }
            }
        }
    }
}