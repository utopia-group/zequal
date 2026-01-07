use std::cmp::min;
use std::collections::{HashMap, VecDeque};
use std::ops::{Add, BitAnd, Shl};

use num_bigint_dig::BigInt;
use num_traits::{ToPrimitive, Zero};
use num_traits::identities::One;

use cfg::expr::binop::BinaryOperator;
use cfg::expr::expression::{Expr, Expression};
use cfg::expr::function_call::FunctionCall;
use cfg::expr::literal::Literal;
use cfg::expr::unop::UnaryOperator;
use cfg::expr::var_access::Access;
use cfg::expr::variable_ref::Ref;
use crate::smt::smt::UninterpretedFunction;

use crate::utils::error::VerificationError;
use crate::utils::template_context::TemplateContext;
use crate::utils::var_utils::VarUtils;
use crate::utils::wrapped_smt_term::VCTerm;

pub trait ExpressionInterpreter<T: VCTerm>: VarUtils<T> {
    fn interpret_binop(&mut self, ctx: &TemplateContext, lhs: &Expression, op: BinaryOperator, rhs: &Expression, is_constraint: bool) -> Result<T, VerificationError> {
        let lhs_expr = self.interpret_expr(ctx, lhs, is_constraint)?;
        let rhs_expr = self.interpret_expr(ctx, rhs, is_constraint)?;

        match op {
            BinaryOperator::Mul => { Ok(lhs_expr.mul(rhs_expr)?) }
            BinaryOperator::MulInv => { Ok(lhs_expr.mul_by_inverse(rhs_expr)?) }
            BinaryOperator::Add => { Ok(lhs_expr.add(rhs_expr)?) }
            BinaryOperator::Sub => { Ok(lhs_expr.sub(rhs_expr)?) }
            BinaryOperator::Pow => { Ok(lhs_expr.pow(rhs_expr)?) }
            BinaryOperator::IntDiv => { Ok(lhs_expr.div(rhs_expr)?) }
            BinaryOperator::Mod => { Ok(lhs_expr.modulus(rhs_expr)?) }
            BinaryOperator::Shl => {
                let extracted = rhs_expr.extract_integer();
                if let Ok(number) = extracted {
                    let mul_amt = BigInt::one().shl(number.to_usize().ok_or("Could not convert BigInt to usize")?);
                    Ok(lhs_expr.mul((&mul_amt).into())?)
                }
                else {
                    Ok(lhs_expr.shl(rhs_expr)?)
                }
            }
            BinaryOperator::Shr => {
                let extracted = rhs_expr.extract_integer();
                if let Ok(number) = extracted {
                    let mul_amt = BigInt::one().shl(number.to_usize().ok_or("Could not convert BigInt to usize")?);
                    Ok(lhs_expr.div((&mul_amt).into())?)
                }
                else {
                    Ok(lhs_expr.shr(rhs_expr)?)
                }
            }
            BinaryOperator::BitOr => { Ok(lhs_expr.bit_or(rhs_expr)?) }
            BinaryOperator::BitAnd => {
                let extracted = rhs_expr.extract_integer();
                if let Ok(number) = extracted {
                    let num_plus_one = number.clone().add(BigInt::one());
                    if number.bitand(&num_plus_one) == BigInt::zero() {
                        Ok(lhs_expr.modulus((&num_plus_one).into())?)
                    }
                    else {
                        Ok(lhs_expr.bit_and(rhs_expr)?)
                    }
                }
                else {
                    Ok(lhs_expr.bit_and(rhs_expr)?)
                }
            }
            BinaryOperator::BitXor => { Ok(lhs_expr.bit_xor(rhs_expr)?) }
            BinaryOperator::Lt => { Ok(lhs_expr.lt(rhs_expr)?) }
            BinaryOperator::Lte => { Ok(lhs_expr.lte(rhs_expr)?) }
            BinaryOperator::Gt => { Ok(lhs_expr.gt(rhs_expr)?) }
            BinaryOperator::Gte => { Ok(lhs_expr.gte(rhs_expr)?) }
            BinaryOperator::Eq => { Ok(lhs_expr.eq(rhs_expr)?) }
            BinaryOperator::Neq => { Ok(lhs_expr.neq(rhs_expr)?) }
            BinaryOperator::And => { Ok(lhs_expr.and(rhs_expr)?) }
            BinaryOperator::Or => { Ok(lhs_expr.or(rhs_expr)?) }
        }
    }

    fn interpret_unop(&mut self, ctx: &TemplateContext, op: UnaryOperator, rhs: &Expression, is_constraint: bool) -> Result<T, VerificationError> {
        let rhs_expr = self.interpret_expr(ctx, rhs, is_constraint)?;
        match op {
            UnaryOperator::Negate => { Ok(rhs_expr.negate()?) }
            UnaryOperator::Not => { Ok(rhs_expr.not()?) }
            UnaryOperator::Complement => { Ok(rhs_expr.complement()?) }
        }
    }

    fn interpret_ref(&mut self, ctx: &TemplateContext, referenced: &Ref, is_constraint: bool) -> Result<T, VerificationError> {
        let mut is_constraint_override = is_constraint;
        if is_constraint && !referenced.ref_constraint() || !is_constraint && !referenced.ref_witness() {
            is_constraint_override = !is_constraint_override;
        }
        /*if let Ref::Sig(s) = referenced {
            if is_constraint && !s.ref_constraint() || !is_constraint && !s.ref_witness() {
                is_constraint_override = !is_constraint_override;
            }
        }*/
        self.read_var(ctx, referenced, is_constraint_override)
    }

    fn get_all_array_access_bounds(&mut self, ctx: &TemplateContext, expr: &Expression, is_constraint: bool) -> Result<T, VerificationError> {
        let mut all_bounds = vec![];
        for v_ref in expr.variable_refs() {
            all_bounds.push(self.get_array_access_bounds(ctx, v_ref, is_constraint)?);
        }

        Ok(T::and_all(all_bounds)?)
    }

    fn get_array_access_bounds(&mut self, ctx: &TemplateContext, referenced: &Ref, is_constraint: bool) -> Result<T, VerificationError> {
        let mut bounds = vec![];
        let (component_dims_opt, store_dims) = referenced.get_dimensions(ctx.cfg, ctx.template)?;
        let ref_access = referenced.access();
        let offset = if let Some(component_dims) = component_dims_opt {
            for i in 0..min(component_dims.len(), ref_access.len()) {
                let dim = component_dims.get(i).unwrap();
                let dim_term = self.interpret_expr(ctx, dim, is_constraint)?;
                let access = ref_access.get(i);
                let ind_expr = match access {
                    Access::Array { ind } => {
                        self.interpret_expr(ctx, ind, is_constraint)?
                    }
                    Access::Component { .. } => { unreachable!("Invalid access") }
                };
                let zero_check = ind_expr.clone().gte((&BigInt::zero()).into())?;
                let dim_check = ind_expr.lt(dim_term)?;
                bounds.push(zero_check);
                bounds.push(dim_check);
            }

            ref_access.get_component_access_ind().unwrap() + 1
        }
        else {
            0
        };

        for i in 0..min(store_dims.len(), ref_access.len() - offset) {
            let dim = store_dims.get(i).unwrap();
            let dim_term = self.interpret_expr(ctx, dim, is_constraint)?;
            let access = ref_access.get(offset + i);
            let ind_expr = match access {
                Access::Array { ind } => {
                    self.interpret_expr(ctx, ind, is_constraint)?
                }
                Access::Component { .. } => { unreachable!("Invalid access") }
            };
            let zero_check = ind_expr.clone().gte((&BigInt::zero()).into())?;
            let dim_check = ind_expr.lt(dim_term)?;
            bounds.push(zero_check);
            bounds.push(dim_check);
        }

        Ok(T::and_all(bounds)?)
    }

    fn get_function(&mut self, ctx: &TemplateContext, fn_call: &FunctionCall, is_constraint: bool) -> Result<T, VerificationError>;

    fn interpret_expr(&mut self, ctx: &TemplateContext, expr: &Expression, is_constraint: bool) -> Result<T, VerificationError> {
        match expr {
            Expression::BinOp(e) => {
                Ok(self.interpret_binop(ctx, e.lhs(), e.op(), e.rhs(), is_constraint)?)
            }
            Expression::UnOp(e) => {
                Ok(self.interpret_unop(ctx, e.op(), e.expr(), is_constraint)?)
            }
            Expression::Ternary(e) => {
                let cond_expr = self.interpret_expr(ctx, e.cond(), is_constraint)?;
                let true_expr = self.interpret_expr(ctx, e.true_case(), is_constraint)?;
                let false_expr = self.interpret_expr(ctx, e.false_case(), is_constraint)?;
                Ok(cond_expr.ite(true_expr, false_expr)?)
            }
            Expression::Variable(e) => {
                Ok(self.interpret_ref(ctx, e, is_constraint)?)
            }
            Expression::Literal(e) => {
                match e {
                    Literal::Number(n) => {
                        Ok(n.val().into())
                    }
                    Literal::UniformArray(a) => {
                        let uniform_val = self.interpret_expr(ctx, a.val(), is_constraint)?;
                        Ok(T::const_array(uniform_val)?)
                    }
                    Literal::InlineArray(a) => {
                        let entries = a.entries();

                        let mut arr_terms = VecDeque::new();
                        let mut val_sort = T::variable_sort();
                        for entry in entries {
                            let expr_term = self.interpret_expr(ctx, entry, is_constraint)?;
                            let sort = expr_term.sort();
                            arr_terms.push_back(expr_term);
                            if val_sort == T::variable_sort() {
                                val_sort = sort;
                            }
                        }

                        let mut arr = T::const_array(arr_terms.pop_front().unwrap().cast(val_sort.clone())?)?;
                        let mut i = 1;
                        while let Some(entry_term) = arr_terms.pop_front() {
                            let ind = BigInt::from(i);
                            arr = arr.store((&ind).into(), entry_term.cast(val_sort.clone())?)?;
                            i += 1;
                        }

                        Ok(arr)
                    }
                    Literal::Boolean(b) => {
                        Ok(b.val().into())
                    }
                }
            }
            Expression::Instantiate(e) => {
                if let Some(template) = ctx.cfg.templates.get(e.name()) {
                    assert_eq!(e.args().len(), template.input_vars.len());
                    let mut template_struct = HashMap::new();
                    for i in 0..e.args().len() {
                        let var_name: String = template.input_vars.get(i).unwrap().name().into();
                        let arg_term = self.interpret_expr(ctx, e.args().get(i).unwrap(), is_constraint)?;
                        template_struct.insert(var_name, arg_term);
                    }
                    Ok(T::create_struct(template_struct)?)

                    /*assert_eq!(args.len(), template.input_vars.len());
                    let mut vars = vec![];
                    let mut conjuncts = vec![];
                    for i in 0..args.len() {
                        let var_name = format!(".{}", &template.input_vars.get(i).unwrap().name);
                        self.add_quantified_var(ctx, &var_name, T::variable_sort())?;
                        let q_term = self.read_var(ctx, &var_name, &vec![], false)?;
                        let val_term = self.interpret_expr(ctx, args.get(i).unwrap(), false)?;
                        conjuncts.push(q_term.eq(val_term)?);
                        vars.push((var_name, T::variable_sort()));
                    }
                    let var_assignment = T::and_all(conjuncts)?;
                    var_assignment.quantify(Quantifier::Exists, vars)*/
                }
                else {
                    Err(VerificationError::UnsupportedFeature("interpret_expr", "function calls"))
                }
            }
            Expression::FunctionCall(f) => {
                self.get_function(ctx, f, is_constraint)
            }
        }
    }
}
