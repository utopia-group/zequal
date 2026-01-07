use std::collections::BTreeMap;
use std::marker::PhantomData;

use num_bigint_dig::BigInt;
use num_traits::{One, Zero};

use cfg::cfg::CFG;
use cfg::expr::binop::BinaryOperator;
use cfg::expr::expression::Expression;
use cfg::expr::literal::Literal;
use cfg::expr::unop::UnaryOperator;
use cfg::finite_fields::FiniteFieldDef;
use cfg::stmt::statement::Statement;
use cfg::template::Template;

use crate::analysis::{AbstractState, AbstractTransformer, DomainValue};
use crate::domains::interval::infinite_number::infinite_number::InfiniteNumber;
use crate::domains::interval::interval_value::IntervalValue;
use crate::utils::circom_value::CircomValue;

pub struct IntervalTransformer<N: InfiniteNumber, A: AbstractState<CircomValue<IntervalValue<N>>>> {
    phantom: PhantomData<A>,
    phantom1: PhantomData<N>
}

impl<N: InfiniteNumber, A: AbstractState<CircomValue<IntervalValue<N>>>> AbstractTransformer<CircomValue<IntervalValue<N>>, A> for IntervalTransformer<N, A> {
    fn interpret_expr(start: &A, cfg: &CFG, template: &Template, expr: &Expression) -> CircomValue<IntervalValue<N>> {
        match expr {
            Expression::BinOp(binop) => {
                let lhs = Self::interpret_expr(start, cfg, template, binop.lhs());
                let rhs = Self::interpret_expr(start, cfg, template, binop.rhs());
                match binop.op() {
                    BinaryOperator::Mul => { lhs.apply_binop(&rhs, IntervalValue::mul) }
                    BinaryOperator::MulInv => { IntervalValue::top().into() }
                    BinaryOperator::Add => { lhs.apply_binop(&rhs, IntervalValue::add) }
                    BinaryOperator::Sub => { lhs.apply_binop(&rhs, IntervalValue::sub) }
                    BinaryOperator::Pow => { lhs.apply_binop(&rhs, IntervalValue::pow) }
                    BinaryOperator::IntDiv => { lhs.apply_binop(&rhs, IntervalValue::div) }
                    BinaryOperator::Mod => { lhs.apply_binop(&rhs, IntervalValue::modulus) }
                    BinaryOperator::Shl => { lhs.apply_binop(&rhs, IntervalValue::shl) }
                    BinaryOperator::Shr => { lhs.apply_binop(&rhs, IntervalValue::shr) }
                    BinaryOperator::BitOr => { IntervalValue::top().into() }
                    BinaryOperator::BitAnd => { IntervalValue::top().into() }
                    BinaryOperator::BitXor => { IntervalValue::top().into() }
                    BinaryOperator::Lt => { lhs.apply_binop(&rhs, IntervalValue::lt) }
                    BinaryOperator::Lte => { lhs.apply_binop(&rhs, IntervalValue::lte) }
                    BinaryOperator::Gt => { lhs.apply_binop(&rhs, IntervalValue::gt) }
                    BinaryOperator::Gte => { lhs.apply_binop(&rhs, IntervalValue::gte) }
                    BinaryOperator::Eq => { lhs.apply_binop(&rhs, IntervalValue::eq) }
                    BinaryOperator::Neq => { lhs.apply_binop(&rhs, IntervalValue::neq) }
                    BinaryOperator::And => { lhs.apply_binop(&rhs, IntervalValue::and) }
                    BinaryOperator::Or => { lhs.apply_binop(&rhs, IntervalValue::or) }
                }
            }
            Expression::UnOp(unop) => {
                let expr_val = Self::interpret_expr(start, cfg, template, unop.expr());
                match unop.op() {
                    UnaryOperator::Negate => { expr_val.apply_unop(IntervalValue::negate) }
                    UnaryOperator::Not => { expr_val.apply_unop(IntervalValue::not) }
                    UnaryOperator::Complement => { IntervalValue::top().into() }
                }
            }
            Expression::Ternary(ternary) => {
                let true_case = Self::interpret_expr(start, cfg, template, ternary.true_case());
                let false_case = Self::interpret_expr(start, cfg, template, ternary.false_case());
                true_case.join(&false_case)
            }
            Expression::Variable(var) => {
                start.get_value(var)
            }
            Expression::Literal(literal) => {
                match literal {
                    Literal::Number(n) => {
                        <&BigInt as Into<IntervalValue<N>>>::into(n.val()).into()
                    }
                    Literal::UniformArray(arr) => {
                        Self::interpret_expr(start, cfg, template, arr.val())
                    }
                    Literal::InlineArray(arr) => {
                        let mut array_val: CircomValue<IntervalValue<N>> = IntervalValue::bottom().into();
                        for entry in arr.entries() {
                            let entry_val = Self::interpret_expr(start, cfg, template, entry);
                            array_val = array_val.join(&entry_val);
                        }
                        array_val
                    }
                    Literal::Boolean(b) => {
                        if b.val() { <BigInt as Into<IntervalValue<N>>>::into(BigInt::one()).into() } else { <BigInt as Into<IntervalValue<N>>>::into(BigInt::zero()).into() }
                    }
                }
            }
            Expression::Instantiate(instantiate) => {
                let to = cfg.templates.get(instantiate.name()).unwrap();
                let mut entries = BTreeMap::new();
                assert_eq!(to.input_vars.len(), instantiate.args().len());
                for i in 0..to.input_vars.len() {
                    let var = to.input_vars.get(i).unwrap();
                    let expr = instantiate.args().get(i).unwrap();
                    let abstract_val = Self::interpret_expr(start, cfg, template, expr);
                    entries.insert(var.name().into(), abstract_val);
                }

                CircomValue::new_component(entries)
            }
            Expression::FunctionCall(_) => {
                //function calls are being treated as uninterpreted functions
                CircomValue::top()
            }
        }
    }

    fn assume_expr(start: &mut A, cfg: &CFG, template: &Template, expr: &Expression, negate: bool) {
        match expr {
            Expression::BinOp(binop) => {
                let effective_op = match binop.op() {
                    BinaryOperator::Lt => {
                        if negate { BinaryOperator::Gte } else { BinaryOperator::Lt }
                    }
                    BinaryOperator::Lte => {
                        if negate { BinaryOperator::Gt } else { BinaryOperator::Lte }
                    }
                    BinaryOperator::Gt => {
                        if negate { BinaryOperator::Lte } else { BinaryOperator::Gt }
                    }
                    BinaryOperator::Gte => {
                        if negate { BinaryOperator::Lt } else { BinaryOperator::Gte }
                    }
                    BinaryOperator::Eq => {
                        if negate { BinaryOperator::Neq } else { BinaryOperator::Eq }
                    }
                    BinaryOperator::Neq => {
                        if negate { BinaryOperator::Eq } else { BinaryOperator::Neq }
                    }
                    _ => {
                        //select unsupported operator
                        BinaryOperator::BitXor
                    }
                };

                match effective_op {
                    BinaryOperator::Lt => {
                        if let Expression::Variable(v_ref) = binop.lhs() {
                            let effective_state = Self::enforce_lt(start, cfg, template, binop.lhs(), binop.rhs());
                            start.set_value(cfg, template, v_ref, &effective_state);
                        }
                        if let Expression::Variable(v_ref) = binop.rhs() {
                            let effective_state = Self::enforce_gte(start, cfg, template, binop.rhs(), binop.lhs());
                            start.set_value(cfg, template, v_ref, &effective_state);
                        }
                    }
                    BinaryOperator::Lte => {
                        if let Expression::Variable(v_ref) = binop.lhs() {
                            let effective_state = Self::enforce_lte(start, cfg, template, binop.lhs(), binop.rhs());
                            start.set_value(cfg, template, v_ref, &effective_state);
                        }
                        if let Expression::Variable(v_ref) = binop.rhs() {
                            let effective_state = Self::enforce_gt(start, cfg, template, binop.rhs(), binop.lhs());
                            start.set_value(cfg, template, v_ref, &effective_state);
                        }
                    }
                    BinaryOperator::Gt => {
                        if let Expression::Variable(v_ref) = binop.lhs() {
                            let effective_state = Self::enforce_gt(start, cfg, template, binop.lhs(), binop.rhs());
                            start.set_value(cfg, template, v_ref, &effective_state);
                        }
                        if let Expression::Variable(v_ref) = binop.rhs() {
                            let effective_state = Self::enforce_lte(start, cfg, template, binop.rhs(), binop.lhs());
                            start.set_value(cfg, template, v_ref, &effective_state);
                        }
                    }
                    BinaryOperator::Gte => {
                        if let Expression::Variable(v_ref) = binop.lhs() {
                            let effective_state = Self::enforce_gte(start, cfg, template, binop.lhs(), binop.rhs());
                            start.set_value(cfg, template, v_ref, &effective_state);
                        }
                        if let Expression::Variable(v_ref) = binop.rhs() {
                            let effective_state = Self::enforce_lt(start, cfg, template, binop.rhs(), binop.lhs());
                            start.set_value(cfg, template, v_ref, &effective_state);
                        }
                    }
                    BinaryOperator::Eq => {
                        if let Expression::Variable(v_ref) = binop.lhs() {
                            let effective_state = Self::enforce_eq(start, cfg, template, binop.lhs(), binop.rhs());
                            start.set_value(cfg, template, v_ref, &effective_state);
                        }
                        if let Expression::Variable(v_ref) = binop.rhs() {
                            let effective_state = Self::enforce_eq(start, cfg, template, binop.rhs(), binop.lhs());
                            start.set_value(cfg, template, v_ref, &effective_state);
                        }
                    }
                    BinaryOperator::Neq => {
                        if let Expression::Variable(v_ref) = binop.lhs() {
                            let lt_state = Self::enforce_lt(start, cfg, template, binop.lhs(), binop.rhs());
                            let gt_state = Self::enforce_gt(start, cfg, template, binop.lhs(), binop.rhs());
                            let effective_state = lt_state.join(&gt_state);
                            start.set_value(cfg, template, v_ref, &effective_state);
                        }
                    }
                    _ => { /* Skip */ }
                }
            }
            Expression::UnOp(unop) => {
                match unop.op() {
                    UnaryOperator::Not => {
                        Self::assume_expr(start, cfg, template, expr, !negate)
                    }
                    _ => { /* Skip */ }
                }
            }
            _ => {
                /* Skip */
            }
        }
    }

    fn interpret_stmt_in_place(start: &mut A, cfg: &CFG, template: &Template, stmt: &Statement) {
        match stmt {
            Statement::Declare(declare) => {
                /* Skip, Abstract State defaults to bottom */
            }
            Statement::Assert(assert) => {
                /* Skip, Abstract State defaults to bottom */
            }
            Statement::Assume(assume) => {
                /* Skip, Abstract State defaults to bottom */
            }
            Statement::AssignVar(assign) => {
                //variables are inlined and so they are guaranteed to be equivalent.
                let val = Self::interpret_expr(start, cfg, template, assign.rhs());
                start.set_value(cfg, template, assign.lhs(), &val);
            }
            Statement::Constrain(constrain) => {
                let constraint_expr = Expression::new_binop(Box::new(constrain.lhs().clone()), BinaryOperator::Eq, Box::new(constrain.rhs().clone()));
                Self::assume_expr(start, cfg, template, &constraint_expr, false);
                /* Skip, Abstract State defaults to bottom */
            }
            Statement::AssignSig(assign) => {
                let val = Self::interpret_expr(start, cfg, template, assign.rhs());
                start.set_value(cfg, template, assign.lhs(), &val);
            }
        }
    }
}

impl<N: InfiniteNumber, A: AbstractState<CircomValue<IntervalValue<N>>>> IntervalTransformer<N, A> {

    fn enforce_lt(state: &A, cfg: &CFG, template: &Template, expr: &Expression, other: &Expression) -> CircomValue<IntervalValue<N>> {
        let new_rhs = Expression::new_binop(Box::new(other.clone()), BinaryOperator::Sub, Box::new(Expression::Literal(Literal::new_number(BigInt::one()))));
        Self::enforce_lte(state, cfg, template, expr, &new_rhs)
    }

    fn enforce_lte(state: &A, cfg: &CFG, template: &Template, expr: &Expression, other: &Expression) -> CircomValue<IntervalValue<N>> {
        let lhs_state = Self::interpret_expr(state, cfg, template, expr);
        let mut rhs_state = Self::interpret_expr(state, cfg, template, other);
        rhs_state = rhs_state.apply_unop(IntervalValue::relax_lower);
        lhs_state.meet(&rhs_state)
    }

    fn enforce_gt(state: &A, cfg: &CFG, template: &Template, expr: &Expression, other: &Expression) -> CircomValue<IntervalValue<N>> {
        let new_rhs = Expression::new_binop(Box::new(other.clone()), BinaryOperator::Add, Box::new(Expression::Literal(Literal::new_number(BigInt::one()))));
        Self::enforce_gte(state, cfg, template, expr, &new_rhs)
    }

    fn enforce_gte(state: &A, cfg: &CFG, template: &Template, expr: &Expression, other: &Expression) -> CircomValue<IntervalValue<N>> {
        let lhs_state = Self::interpret_expr(state, cfg, template, expr);
        let mut rhs_state = Self::interpret_expr(state, cfg, template, other);
        rhs_state = rhs_state.apply_unop(IntervalValue::relax_upper);
        lhs_state.meet(&rhs_state)
    }

    fn enforce_eq(state: &A, cfg: &CFG, template: &Template, expr: &Expression, other: &Expression) -> CircomValue<IntervalValue<N>> {
        let lhs_state = Self::interpret_expr(state, cfg, template, expr);
        let rhs_state = Self::interpret_expr(state, cfg, template, expr);
        lhs_state.meet(&rhs_state)
    }
}