use static_analysis::domains::interval::bounded_ref::{BoundedAccess, BoundedArrayAccess, SymbolicBoundedRef};
use std::collections::{HashMap, HashSet, VecDeque};
use itertools::Itertools;
use num_bigint_dig::BigInt;
use num_traits::Zero;
use smtlib_lowlevel::ast::ModelResponse;
use smtlib_lowlevel::lexicon::Symbol;
use cfg::block::Block;
use cfg::edge::{Edge, NegInvariantCondition};
use cfg::expr::binop::BinaryOperator;
use cfg::expr::expression::{Expr, Expression};
use cfg::expr::invariant::InvariantExpr;
use cfg::expr::literal::Literal;
use cfg::expr::unop::UnaryOperator;
use cfg::expr::var_access::{Access, AccessList};
use cfg::expr::variable_ref::{Ref, VarRef};
use cfg::finite_fields::FiniteFieldDef;
use cfg::named_storage::{Component, NamedStorage, Signal, Var};
use cfg::stmt::statement::{Statement, Stmt};
use cfg::template::Template;
use static_analysis::analysis::AbstractInterpretation;
use static_analysis::domains::interval::bounded_ref::BoundedRef;
use static_analysis::domains::interval::infinite_number::infinite_number::InfiniteNumber;
use static_analysis::domains::interval::infinite_number::symbolic_infinite_bigint::SymbolicInfiniteBigInt;
use static_analysis::domains::interval::interval_analysis::SymbolicIntervalAnalysis;
use static_analysis::domains::interval::interval_value::SymbolicInterval;
use crate::hoare_logic::vc_generator::VCGenerator;
use crate::interpreter::expression_interpreter::ExpressionInterpreter;
use crate::interpreter::invariant_interpreter::InvariantInterpreter;
use crate::inv_gen::loop_summary::LoopSummary;
use crate::solver::solver::SolverUtils;
use crate::solver::solver_utils::{SatResult, SmtUtils, ValidityResult};
use crate::utils::condition_term::ConditionTerm;
use crate::utils::error::VerificationError;
use crate::utils::template_context::TemplateContext;
use crate::utils::var_utils::VarUtils;
use crate::utils::wrapped_smt_term::{LazyTerm, VCTerm};

pub trait CandidateGenerator<FF: FiniteFieldDef, T: VCTerm + LazyTerm>: VarUtils<T> + SmtUtils<T> + InvariantInterpreter<T> + VCGenerator<T> {
    fn get_loop_summary(&mut self, ctx: &TemplateContext, loop_head_id: usize) -> Result<Box<LoopSummary<FF>>, VerificationError>;

    fn get_interval_analysis(&self, ctx: &TemplateContext) -> Result<&SymbolicIntervalAnalysis<FF>, VerificationError>;

    fn to_loop_head(loop_head: &Block, bounded_ref: &SymbolicBoundedRef<FF>) -> SymbolicBoundedRef<FF> {
        match bounded_ref.get_ref() {
            Ref::Var(_) => {
                let version = *loop_head.exit_versions().get(bounded_ref.name()).unwrap();
                let mut new_ref = bounded_ref.clone();
                new_ref.overwrite_version(version);
                new_ref
            }
            _ => {
                bounded_ref.clone()
            }
        }
    }

    fn mine_assumes(template: &Template) -> Vec<InvariantExpr> {
        let mut assumes = vec![];
        for blk in template.body.values() {
            for stmt in &blk.stmts {
                match stmt {
                    Statement::Assume(a) => {
                        assumes.push(a.expr().clone())
                    }
                    _ => { /* Skip */ }
                }
            }
        }

        assumes
    }

    fn find_required_equivalences(&mut self, ctx: &TemplateContext, summary: &LoopSummary<FF>, post: &ConditionTerm<T>, it_eqs: &Vec<InvariantExpr>) -> Result<(HashSet<SymbolicBoundedRef<FF>>, Vec<InvariantExpr>), VerificationError> {
        let loop_head = summary.get_loop_head(ctx)?;
        let backedge = loop_head.prev.iter()
            .find(|e|
            if let Edge::Backedge(_) = e {true} else {false}
            ).ok_or("Could not find backedge")?;

        let decls = summary.get_decls(ctx)?;
        let it_eqs = InvariantExpr::and_all(it_eqs.clone())?;
        let it_constraints = self.interpret_inv(ctx, &it_eqs)?;
        //loop iterators will be assumed to be equivalent so for performance purposes we can ignore them
        let mut iterators = HashSet::new();
        for loop_id in Some(summary.id()).iter().chain(summary.outer_loops()) {
            // We currently assume that the loop iterator accesses each index in a reference and that the loop
            // has a step of 1
            let cur_loop = self.get_loop_summary(ctx, *loop_id)?;
            iterators.insert(String::from(cur_loop.loop_iterator().name()));
        }

        for loop_id in summary.nested_loops() {
            let cur_loop = self.get_loop_summary(ctx, *loop_id)?;
            iterators.insert(String::from(cur_loop.loop_iterator().name()));
        }

        let loop_writes: HashSet<SymbolicBoundedRef<FF>> = summary.bounded_loop_writes().into_iter()
            .filter(|r| !iterators.contains(r.name()) && !decls.contains(r.name()) && !self.is_equivalent(ctx, r.get_ref()))
            .map(|r| Self::to_loop_head(loop_head, r))
            .collect();
        let pre_loop_writes: HashSet<SymbolicBoundedRef<FF>> = summary.bounded_pre_loop_writes().into_iter()
            .filter(|r| !iterators.contains(r.name()) && !self.is_equivalent(ctx, r.get_ref()))
            .map(|r| Self::to_loop_head(loop_head, r))
            .collect();

        let mut worklist = vec![];
        worklist.extend(loop_writes.clone());
        worklist.extend(pre_loop_writes.clone());
        worklist = worklist.into_iter().filter(|r| !self.is_equivalent(ctx, r.get_ref())).collect();
        //worklist.extend(self.find_transitive_equivalences(ctx, summary, &worklist.iter().cloned().collect())?);

        println!("post: {}", post);
        let mut candidate_eqs = HashMap::new();
        let mut eq_to_ref = HashMap::new();
        let mut zero_checks = HashSet::new();
        for candidate in &worklist {
            let candidate_eq = candidate.create_equality_constraint()?;
            let zero_check = candidate.get_ref().get_nonempty_array_assumption(ctx.cfg, ctx.template)?;
            zero_checks.insert(zero_check);
            candidate_eqs.insert(candidate.clone(), self.interpret_inv(ctx, &candidate_eq)?);
            eq_to_ref.insert(self.interpret_inv(ctx, &candidate_eq)?, candidate.clone());
            let transitive_candidates = self.find_transitive_equivalences(ctx, summary, &HashSet::from([candidate.clone()]))?;
            for transitive_candidate in transitive_candidates {
                if !candidate_eqs.contains_key(&transitive_candidate) {
                    let transitive_eq = transitive_candidate.create_equality_constraint()?;
                    println!("transitive thing: {}, {}", transitive_candidate.name(), transitive_eq);
                    let zero_check = candidate.get_ref().get_nonempty_array_assumption(ctx.cfg, ctx.template)?;
                    zero_checks.insert(zero_check);
                    candidate_eqs.insert(transitive_candidate, self.interpret_inv(ctx, &transitive_eq)?);
                    eq_to_ref.insert(self.interpret_inv(ctx, &candidate_eq)?, candidate.clone());
                }
            }

            /*let transitive_eqs = transitive_candidates.into_iter().map(|e| self.interpret_inv(ctx, &e.create_equality_constraint()?)).collect::<Result<Vec<_>, _>>()?;
            let and_all = self.interpret_inv(ctx, &candidate_eq)?.and(T::and_all(transitive_eqs)?)?;

            println!("check: {}", candidate_eq);
            candidate_eqs.insert(candidate.clone(), and_all);*/
        }

        let mut term_to_assume = HashMap::new();
        for assume in Self::mine_assumes(ctx.template) {
            term_to_assume.insert(self.interpret_inv(ctx, &assume)?, assume);
        }

        let all_zero_checks = Expression::and_all(zero_checks.into_iter().collect());
        let nonempty_assumption_c = self.interpret_expr(ctx, &all_zero_checks, true)?;
        let nonempty_assumption_w = self.interpret_expr(ctx, &all_zero_checks, false)?;
        let nonempty_post = post.clone().add_assume(nonempty_assumption_c)?.add_assume(nonempty_assumption_w)?;
        let mut all_terms: Vec<T> = eq_to_ref.keys().cloned().collect();
        all_terms.extend(term_to_assume.keys().cloned().collect::<Vec<_>>());
        all_terms.push(it_constraints.clone());
        let negated_post = nonempty_post.to_term()?.not()?;
        all_terms.push(negated_post.clone());
        let req = self.find_required_preds(all_terms);
        let mut required_candidates = HashSet::new();
        let mut required_assumes = vec![];
        match req {
            Ok(terms) => {
                for term in &terms {
                    if let Some(val) = eq_to_ref.get(&term) {
                        //manual minimization
                        //let query = T::and_all(terms.iter().filter(|t| t != &term).cloned().collect())?;
                        //let sat = self.check_sat(query, false)?;
                        //if let SatResult::Sat(_) = sat {
                            println!("required {}", val);
                            required_candidates.insert(val.clone());
                        //}
                    }
                    else if let Some(val) = term_to_assume.get(&term) {
                        println!("required {}", val);
                        required_assumes.push(val.clone());
                    }
                }
            }
            Err(VerificationError::SolverReturnedSat(_)) => { return Err(VerificationError::Msg("Could not identify predicates necessary to imply postcondition")) }
            Err(VerificationError::SolverReturnedUnknown(e)) => { return Err(VerificationError::SolverReturnedUnknown("find_required_equivalences")) }
            Err(e) => { return Err(e) }
        }

        Ok((required_candidates, required_assumes))

        /*let all_eqs = T::and_all(candidate_eqs.values().cloned().collect())?.and(it_constraints.clone())?;
        let mut all_eqs_post_check = post.clone().add_assume(all_eqs)?;
        let all_eqs_res = self.check_validity(all_eqs_post_check.to_term()?, true)?;
        match all_eqs_res {
            ValidityResult::Valid => { /* continue */ }
            ValidityResult::Invalid(_) => {
                return Err(VerificationError::Msg("Could not identify predicates necessary to imply postcondition"))
            }
            ValidityResult::Unknown => { return Err(VerificationError::SolverReturnedUnknown("When checking output satisfiability")) }
        }

        let mut required_outputs = HashSet::new();
        while let Some(output) = worklist.pop() {
            let mut eqs: Vec<T> = required_outputs.iter().map(|o| candidate_eqs.get(o).unwrap().clone()).collect();
            eqs.extend(worklist.iter().map(|o| candidate_eqs.get(o).unwrap().clone()).collect::<Vec<_>>());
            eqs.push(it_constraints.clone());
            let mut post_check = post.clone().add_assume(T::and_all(eqs)?)?;
            let res = self.check_validity(post_check.to_term()?, false)?;
            match res {
                ValidityResult::Valid => { /* continue, not required */ println!("Not required: {}", output); }
                ValidityResult::Invalid(_) => { println!("required: {}", output); required_outputs.insert(output.clone()); }
                ValidityResult::Unknown => { return Err(VerificationError::SolverReturnedUnknown("When checking output satisfiability")) }
            }
        }

        Ok(required_outputs)*/
    }

    fn get_loop_it_equalities(&mut self, ctx: &TemplateContext, summary: &LoopSummary<FF>) -> Result<HashSet<InvariantExpr>, VerificationError> {
        let mut iterators = HashSet::new();
        for loop_id in Some(summary.id()).iter().chain(summary.outer_loops()) {
            let cur_loop = self.get_loop_summary(ctx, *loop_id)?;
            let loop_head = cur_loop.get_loop_head(ctx)?;
            let loop_entry = loop_head.next.iter()
                .find_map(|e|
                if let Edge::LoopEntry(le) = e {Some(le)} else {None}
                ).ok_or("Could not find loop entry")?;
            // according to circom documentation, condition cannot be "unknown" meaning it has to be
            // equivalent
            for var in loop_entry.cond.variable_refs() {
                iterators.extend(var.create_equality_constraint(ctx.cfg, ctx.template, cur_loop.get_loop_head(ctx)?, false)?);
            }
            //iterators.extend(cur_loop.loop_iterator_ref().create_equality_constraint(ctx.cfg, ctx.template, cur_loop.get_loop_head(ctx)?, false)?);
        }

        Ok(iterators)
    }

    fn get_loop_bounds(&mut self, ctx: &TemplateContext, summary: &LoopSummary<FF>) -> Result<Vec<InvariantExpr>, VerificationError> {
        let outer_summaries = summary.outer_loops().iter().map(|id| self.get_loop_summary(ctx, *id)).collect::<Result<Vec<_>,_>>()?;
        let interval_analysis = self.get_interval_analysis(ctx)?;
        let loop_head = summary.get_loop_head(ctx)?;
        let mut loop_bounds = vec![];

        let loop_it_expr = Expression::new_variable(summary.loop_iterator_ref().clone());
        let (lower_bound, upper_bound) = summary.bounds();
        let loop_lower_bounds = Expression::new_binop(Box::new(loop_it_expr.clone()), BinaryOperator::Gte, Box::new(lower_bound.clone()));
        loop_bounds.push(loop_lower_bounds.into());
        for cur_loop in outer_summaries {
            // We currently assume that the loop iterator accesses each index in a reference and that the loop
            // has a step of 1
            let iterator = cur_loop.loop_iterator();
            let it_ref = loop_head.post_ref_var(iterator, AccessList::empty(), true, true)?;
            let it_expr = Expression::new_variable(it_ref.clone());
            let bounds = interval_analysis.get_interval_at_block(ctx.cfg, ctx.template, loop_head, &it_ref);
            let lower_res = bounds.lower().to_expr();
            if let Ok(lower) = lower_res {
                let loop_lower_bounds = Expression::new_binop(Box::new(it_expr.clone()), BinaryOperator::Gte, Box::new(lower));
                loop_bounds.push(loop_lower_bounds.into())
            }

            let upper_res = bounds.upper().to_expr();
            if let Ok(upper) = upper_res {
                let loop_upper_bounds = Expression::new_binop(Box::new(it_expr.clone()), BinaryOperator::Lte, Box::new(upper));
                loop_bounds.push(loop_upper_bounds.into())
            }
        }

        Ok(loop_bounds)
    }

    fn find_transitive_equivalences<'l>(&mut self, ctx: &TemplateContext, summary: &LoopSummary<FF>, required_preds: &HashSet<SymbolicBoundedRef<FF>>) -> Result<HashSet<SymbolicBoundedRef<FF>>, VerificationError> {
        let mut iterators = HashSet::new();
        let decls = summary.get_decls(ctx)?;
        for loop_id in Some(summary.id()).iter().chain(summary.outer_loops()) {
            // We currently assume that the loop iterator accesses each index in a reference and that the loop
            // has a step of 1
            let cur_loop = self.get_loop_summary(ctx, *loop_id)?;
            iterators.insert(String::from(cur_loop.loop_iterator().name()));
        }

        for loop_id in summary.nested_loops() {
            let cur_loop = self.get_loop_summary(ctx, *loop_id)?;
            iterators.insert(String::from(cur_loop.loop_iterator().name()));
        }

        let loop_head = summary.get_loop_head(ctx)?;
        let var_versions = loop_head.exit_versions();
        let mut transitive_deps = HashSet::new();
        for pred in required_preds {
            //let pred_deps: Vec<_> = summary.get_transitive_loop_dependencies(pred)?.into_iter().filter(|r| Self::versions_match(&var_versions, r)).collect();
            let pred_deps: Vec<_> = summary.get_transitive_loop_dependencies(pred)?.into_iter()
                .map(|r| Self::to_loop_head(loop_head, &r))
                .filter(|r| !iterators.contains(r.name()) && !decls.contains(r.name()) && !self.is_equivalent(ctx, r.get_ref()))
                .collect();
            println!("pred: {}", pred);
            println!("deps: {}", pred_deps.iter().join(", "));
            transitive_deps.extend(pred_deps);
        }

        Ok(transitive_deps)
    }

    fn generate_guard(&self, summaries: &HashMap<usize, Box<LoopSummary<FF>>>, loop_to_quantifier: &HashMap<usize, Ref>, used_quantifiers: &HashSet<&Ref>, loop_id: usize, is_before_loop: bool, is_in_loop: bool) -> Expression {
        let loop_summary = summaries.get(&loop_id).unwrap();
        let mut worklist = vec![];
        worklist.push(loop_summary.id());
        worklist.extend(loop_summary.outer_loops());
        let mut seen_quantifiers = HashSet::new();

        //let mut loop_bounds = vec![];
        let mut guards = vec![];
        for cur_loop in worklist {
            let quantifier = loop_to_quantifier.get(&cur_loop).unwrap();


            /*let loop_lower_bounds = Expression::new_binop(Box::new(loop_it_expr.clone()), BinaryOperator::Gte, Box::new(lower_bound.clone()));
            let loop_upper_bounds = Expression::new_binop(Box::new(loop_it_expr.clone()), BinaryOperator::Lt, Box::new(upper_bound.clone()));
            loop_bounds.push(Expression::and_all(vec![loop_lower_bounds, loop_upper_bounds]));*/
            if used_quantifiers.contains(quantifier) {
                seen_quantifiers.insert(quantifier);
                let quant_expr = Expression::new_variable(quantifier.clone());

                let cur_summary = summaries.get(&cur_loop).unwrap();
                let (lower_bound, upper_bound) = cur_summary.bounds();
                let loop_it_expr = Expression::new_variable(cur_summary.loop_iterator_ref().clone());
                let lower_bound_check = Expression::new_binop(Box::new(quant_expr.clone()), BinaryOperator::Gte, Box::new(lower_bound.clone()));
                let upper_bound_check = Expression::new_binop(Box::new(quant_expr.clone()), BinaryOperator::Lt, Box::new(upper_bound.clone()));
                let iterator_upper_bound_check = Expression::new_binop(Box::new(quant_expr.clone()), if is_before_loop {BinaryOperator::Lte} else {BinaryOperator::Lt}, Box::new(loop_it_expr.clone()));

                let prev_iterated_guard_opt = guards.pop();

                //create current iteration guard
                let eq_it = Expression::new_binop(Box::new(loop_it_expr.clone()), BinaryOperator::Eq, Box::new(quant_expr));
                let cur_it_bound = Expression::new_binop(Box::new(loop_it_expr), BinaryOperator::Lt, Box::new(upper_bound.clone()));
                let cur_it_check = Expression::and_all(vec![eq_it, cur_it_bound]);
                guards = guards.into_iter()
                    .map(|g| Expression::new_binop(Box::new(cur_it_check.clone()), BinaryOperator::And, Box::new(g)))
                    .collect();

                //create iterating guard
                let it_bounds_check = Expression::and_all(vec![lower_bound_check.clone(), iterator_upper_bound_check, upper_bound_check.clone()]);
                if let Some(prev_iterated_guard) = &prev_iterated_guard_opt {
                    guards.push(Expression::new_binop(Box::new(it_bounds_check), BinaryOperator::And, Box::new(prev_iterated_guard.clone())))
                }
                else {
                    //first iteration just push
                    guards.push(it_bounds_check);
                }

                //create iterated guard (i.e. already performed the work)
                let loop_bounds_check = Expression::and_all(vec![lower_bound_check, upper_bound_check]);
                if let Some(prev_iterated_guard) = prev_iterated_guard_opt {
                    guards.push(Expression::new_binop(Box::new(loop_bounds_check), BinaryOperator::And, Box::new(prev_iterated_guard)))
                }
                else {
                    //first iteration just push
                    guards.push(loop_bounds_check);
                }
            }
            else if seen_quantifiers.len() != used_quantifiers.len() && is_in_loop {
                // if the predicate is written within the loop and we are in a nested loop, after the loop iteration
                // it will be the case that we wrote to the element in the current iteration and so is equivalent

                let cur_summary = summaries.get(&cur_loop).unwrap();
                let (_, upper_bound) = cur_summary.bounds();
                let loop_it_expr = Expression::new_variable(cur_summary.loop_iterator_ref().clone());
                let upper_bound_check = Expression::new_binop(Box::new(loop_it_expr), BinaryOperator::Gte, Box::new(upper_bound.clone()));
                let prev_iterated_guard_opt = guards.pop();
                if let Some(prev_iterated_guard) = prev_iterated_guard_opt {
                    guards.push(Expression::and_all(vec![upper_bound_check, prev_iterated_guard]))
                }
                else {
                    guards.push(upper_bound_check);
                }
                //guards.push(Expression::new_literal(Literal::new_boolean(true)));
            }
        }

        //Do not need the last "fully iterated" predicate
        guards.pop();
        let guard = Expression::or_all(guards);
        //Expression::new_binop(Box::new(guard), BinaryOperator::And, Box::new(Expression::and_all(loop_bounds)))
        guard
    }

    fn generate_guarded_equality(&self, renamings: &HashMap<Ref, Ref>, loop_to_quantifier: &HashMap<usize, Ref>, summaries: &HashMap<usize, Box<LoopSummary<FF>>>, loop_head: usize, candidate: &SymbolicBoundedRef<FF>) -> Result<InvariantExpr, VerificationError> {
        let loop_summary = summaries.get(&loop_head).unwrap();
        let outer_quantifiers: HashSet<&Ref> = loop_to_quantifier.iter()
            .filter_map(|(l, r)| if loop_summary.outer_loops().contains(l) || loop_summary.id() == *l { Some(r) } else {None} )
            .collect();

        let renamed_ref = candidate.rename_all(&renamings)?;
        let mut new_access = AccessList::empty();
        let mut guards: Vec<Expression> = vec![];
        let mut quantifiers: Vec<String> = vec![];
        let mut used_loop_quantifiers = HashSet::new();
        for (arr_ind, access) in renamed_ref.access().iter().enumerate() {
            match access {
                BoundedAccess::Array { ind } => {
                    let loop_quantifiers: HashSet<&Ref> = ind.get_access_expr().variable_refs().into_iter()
                        .filter(|r| outer_quantifiers.contains(r))
                        .collect();

                    if loop_quantifiers.is_empty() {
                        let (quantifier_opt, guard_opt, ind_expr) = ind.get_ind_bounds(arr_ind);
                        if let Some(quantifier_ref) = quantifier_opt {
                            quantifiers.push(quantifier_ref.name().into());
                        }
                        if let Some(guard) = guard_opt {
                            guards.push(guard);
                        }
                        new_access.push(Access::new_array_access(ind_expr))?;
                    }
                    else {
                        new_access.push(Access::new_array_access(ind.get_access_expr().clone()))?;
                        used_loop_quantifiers.extend(loop_quantifiers.into_iter());
                    }
                }
                BoundedAccess::Component { name } => {
                    new_access.push(Access::new_component_access(name.clone()))?;
                }
                BoundedAccess::UnknownAccess { ind } => {
                    let (quantifier_ref, guard, ind_expr) = ind.get_ind_bounds(arr_ind);
                    quantifiers.push(quantifier_ref.name().into());
                    guards.push(guard);
                    new_access.push(Access::new_array_access(ind_expr))?;
                }
            }
        }

        if !used_loop_quantifiers.is_empty() {
            let is_in_loop = loop_summary.is_written_in_loop(candidate);
            let is_before_loop = !is_in_loop && !loop_summary.is_written_after_loop(candidate);

            guards.push(self.generate_guard(summaries, loop_to_quantifier, &used_loop_quantifiers, loop_head, is_before_loop, is_in_loop));
            quantifiers.extend(used_loop_quantifiers.into_iter().map(|r| r.name().into()));
        }

        let (ref_w, ref_c) = match candidate.get_ref() {
            Ref::Var(v) => {
                let w = Ref::new_var_ref(candidate.name().into(), new_access.clone(), v.version(), true, false);
                let c = Ref::new_var_ref(candidate.name().into(), new_access, v.version(), false, true);
                (w, c)
            }
            Ref::Sig(s) => {
                let w = Ref::new_sig_ref(candidate.name().into(), new_access.clone(), true, false);
                let c = Ref::new_sig_ref(candidate.name().into(), new_access, false, true);
                (w, c)
            }
            Ref::Comp(c) => {
                panic!("Candidate should not be a component");
            }
        };

        let ref_w_expr = Expression::new_variable(ref_w);
        let ref_c_expr = Expression::new_variable(ref_c);
        let eq_check = Expression::new_binop(Box::new(ref_c_expr), BinaryOperator::Eq, Box::new(ref_w_expr));
        let guard = Expression::new_unop(UnaryOperator::Not, Box::new(Expression::and_all(guards)));
        let eq_pred = Expression::new_binop(Box::new(guard), BinaryOperator::Or, Box::new(eq_check));
        Ok(InvariantExpr::from(eq_pred).forall(quantifiers))
    }

    fn generate_invariant_candiates(&mut self, ctx: &TemplateContext, summary: &LoopSummary<FF>, candidate_refs: &HashSet<SymbolicBoundedRef<FF>>) -> Result<Vec<InvariantExpr>, VerificationError> {
        let mut renamings: HashMap<Ref, Ref> = HashMap::new();
        let mut summaries = HashMap::new();
        let mut loop_to_quantifier = HashMap::new();
        for loop_id in Some(summary.id()).iter().chain(summary.outer_loops()) {
            // We currently assume that the loop iterator accesses each index in a reference and that the loop
            // has a step of 1
            let cur_loop = self.get_loop_summary(ctx, *loop_id)?;
            let quantifier_name = format!("uq{}", loop_id);
            let quantifier_ref = Ref::new_var_ref(quantifier_name.clone(), AccessList::empty(), 0, true, true);

            renamings.insert(cur_loop.loop_iterator_ref().clone(), quantifier_ref.clone());
            loop_to_quantifier.insert(*loop_id, quantifier_ref);
            summaries.insert(*loop_id, cur_loop);
        }

        let mut candidates = vec![];
        let outer_summary = self.get_loop_summary(ctx, summary.get_outermost_loop())?;
        for candidate in candidate_refs {
            let guarded_candidate = if outer_summary.is_written_in_loop(candidate) {
                self.generate_guarded_equality(&renamings, &loop_to_quantifier, &summaries, summary.id(), candidate)?
            }
            else {
                candidate.create_equality_constraint()?
            };

            candidates.push(guarded_candidate);
        };

        Ok(candidates)
    }


    fn generate_candidates(&mut self, ctx: &TemplateContext, loop_exit: &NegInvariantCondition, post: &ConditionTerm<T>) -> Result<(Vec<InvariantExpr>, Vec<InvariantExpr>, Vec<InvariantExpr>, bool), VerificationError> {
        let loop_summary = self.get_loop_summary(ctx, loop_exit.prev)?;
        let loop_iterator_eqs = self.get_loop_it_equalities(ctx, &loop_summary)?.into_iter().collect();
        let outermost_summary = self.get_loop_summary(ctx, loop_summary.get_outermost_loop())?;
        let (required_post_strengthening, required_assumes) = self.find_required_equivalences(ctx, &loop_summary, post, &loop_iterator_eqs)?;
        let mut transitive_deps = self.find_transitive_equivalences(ctx, &loop_summary, &required_post_strengthening)?;
        for s in &required_post_strengthening {
            transitive_deps.remove(s);
        }
        let mut required_preds = self.generate_invariant_candiates(ctx, &loop_summary, &required_post_strengthening)?;
        required_preds.extend(required_assumes);
        let possible_candidates: Vec<InvariantExpr> = self.generate_invariant_candiates(ctx, &loop_summary, &transitive_deps)?.into_iter()
            .filter(|c| !required_preds.contains(c))
            .collect();
        println!("required preds: {}", required_preds.iter().join(", "));
        println!("possible candidates: {}", possible_candidates.iter().join(", "));

        //required_preds.extend(possible_candidates);
        //let all = InvariantExpr::and_all(required_preds)?;
        //Ok((vec![all], vec![]))
        Ok((required_preds, possible_candidates, loop_iterator_eqs, loop_summary.nested_loops().is_empty() && loop_summary.outer_loops().is_empty()))
    }
}