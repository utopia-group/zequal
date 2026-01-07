use std::collections::{HashSet, VecDeque};
use std::marker::PhantomData;
use itertools::Itertools;
use cfg::block::Block;
use cfg::cfg::CFG;
use cfg::edge::Edge;
use cfg::error::CFGError;
use cfg::expr::expression::Expression;
use cfg::expr::var_access::{Access, AccessList};
use cfg::expr::variable_ref::Ref;
use cfg::finite_fields::FiniteFieldDef;
use cfg::template::Template;
use crate::analysis::{AbstractInterpretation, AbstractState, AbstractTransformer, DomainValue, StateError};
use crate::context_sensitivity::context_insensitive_analysis::ContextInsensitiveAnalysis;
use crate::domains::interval::bounded_ref::BoundedRef;
use crate::domains::interval::infinite_number::infinite_bigint::InfiniteBigInt;
use crate::domains::interval::infinite_number::infinite_number::InfiniteNumber;
use crate::domains::interval::infinite_number::symbolic_infinite_bigint::SymbolicInfiniteBigInt;
use crate::domains::interval::interval_transformer::IntervalTransformer;
use crate::domains::interval::interval_value::{Interval, IntervalValue, SymbolicInterval};
use crate::utils::circom_abstract_state::CircomAbstractState;
use crate::utils::circom_value::CircomValue;

pub type ContextInsensitiveIntervalAnalysis<FF: FiniteFieldDef> = ContextInsensitiveAnalysis<CircomValue<Interval<FF>>, CircomAbstractState<Interval<FF>>, IntervalTransformer<InfiniteBigInt<FF>, CircomAbstractState<Interval<FF>>>>;
pub type DefaultIntervalAnalysis<FF: FiniteFieldDef> = IntervalAnalysis<InfiniteBigInt<FF>, CircomAbstractState<Interval<FF>>, ContextInsensitiveIntervalAnalysis<FF>>;

pub type ContextInsensitiveSymbolicIntervalAnalysis<FF: FiniteFieldDef> = ContextInsensitiveAnalysis<CircomValue<SymbolicInterval<FF>>, CircomAbstractState<SymbolicInterval<FF>>, IntervalTransformer<SymbolicInfiniteBigInt<FF>, CircomAbstractState<SymbolicInterval<FF>>>>;
pub type SymbolicIntervalAnalysis<FF: FiniteFieldDef> = IntervalAnalysis<SymbolicInfiniteBigInt<FF>, CircomAbstractState<SymbolicInterval<FF>>, ContextInsensitiveSymbolicIntervalAnalysis<FF>>;

pub struct IntervalAnalysis<N: InfiniteNumber, A: AbstractState<CircomValue<IntervalValue<N>>>, AI: AbstractInterpretation<CircomValue<IntervalValue<N>>, A, IntervalTransformer<N, A>>> {
    analysis: AI,
    phantom: PhantomData<A>,
    phantom1: PhantomData<N>
}

impl<N: InfiniteNumber, A: AbstractState<CircomValue<IntervalValue<N>>>, AI: AbstractInterpretation<CircomValue<IntervalValue<N>>, A, IntervalTransformer<N, A>>> IntervalAnalysis<N, A, AI> {
    pub fn new(cfg: &CFG, template: &Template) -> Self {
        let mut analysis = AI::new();
        let mut start_state = A::empty();
        for input_var in &template.input_vars {
            let input_ref = template.pre_ref_var(input_var, AccessList::empty(), true, true).unwrap();
            let input_expr = Expression::new_variable(input_ref.clone());
            start_state.set_value(cfg, template, &input_ref, &IntervalValue::expr_bounds(&input_expr).into());
            start_state.lock_var(&input_ref);
        }

        for input_sig in &template.input_signals {
            let input_ref = template.pre_ref_sig(input_sig, AccessList::empty(), true, true).unwrap();
            let input_expr = Expression::new_variable(input_ref.clone());
            start_state.set_value(cfg, template, &input_ref, &IntervalValue::expr_bounds(&input_expr).into());
            start_state.lock_var(&input_ref)
        }

        analysis.analyze(cfg, template, start_state);

        let interval_analysis = Self {analysis, phantom: PhantomData::default(), phantom1: PhantomData::default() };

        for blk in template.body.values() {
            let end_blk_state = interval_analysis.get_state(cfg, template, blk, false).unwrap();
            let (reads, writes) = blk.reads_and_writes();
            println!("----- Block {} Reads -----", blk.id);
            interval_analysis.print_ref_bounds(cfg, template, &end_blk_state, &reads);
            println!("----- Block {} Writes -----", blk.id);
            interval_analysis.print_ref_bounds(cfg, template, &end_blk_state, &writes);
        }

        interval_analysis
    }

    fn print_ref_bounds(&self, cfg: &CFG, template: &Template, state: &A, refs: &HashSet<&Ref>) -> Result<(), CFGError> {
        for v_ref in refs {
            let bounded_ref = self.get_bounded_ref(cfg, template, state, v_ref)?;
            println!("{}", bounded_ref)
        }

        Ok(())
    }

    pub fn get_state(&self, cfg: &CFG, template: &Template, at: &Block, at_start: bool) -> Result<A, StateError>  {
        let ctx = AI::init_context(cfg, template);
        let blk_state = self.analysis.get_state(&ctx, Some(at))?;

        if at_start {
            Ok(blk_state.clone())
        }
        else {
            Ok(IntervalTransformer::interpret_blk(blk_state, cfg, template, at))
        }
    }

    pub fn evaluate_expression(&self, cfg: &CFG, template: &Template, state: &A, expr: &Expression) -> CircomValue<IntervalValue<N>> {
        IntervalTransformer::interpret_expr(state, cfg, template, expr)
    }

    pub fn get_bounded_ref(&self, cfg: &CFG, template: &Template, state: &A, v_ref: &Ref) -> Result<BoundedRef<N>, CFGError> {
        let mut access_intervals = VecDeque::new();
        for access in v_ref.access().iter() {
            match &access {
                Access::Array { ind } => {
                    let abstract_val = self.evaluate_expression(cfg, template, state, ind).join_into_nested_value();
                    access_intervals.push_back(abstract_val)
                }
                _ => { /* Skip */ }
            }
        }

        BoundedRef::new(cfg, template, v_ref.clone(), access_intervals)
    }

    pub fn get_interval_at_post(&self, cfg: &CFG, template: &Template, var_ref: &Ref) -> IntervalValue<N> {
        let ctx = AI::init_context(cfg, template);
        let result = self.analysis.get_end_state(&ctx, template);

        if let Ok(state) = result {
            if state.contains_value(var_ref) {
                state.get_value(var_ref).join_into_nested_value()
            }
            else {
                IntervalValue::bottom()
            }
        }
        else {
            IntervalValue::bottom()
        }
    }

    pub fn get_interval_at_block(&self, cfg: &CFG, template: &Template, blk: &Block, var_ref: &Ref) -> IntervalValue<N> {
        let ctx = AI::init_context(cfg, template);
        let result = self.analysis.get_state(&ctx, Some(blk));

        if let Ok(state) = result {
            if state.contains_value(var_ref) {
                state.get_value(var_ref).join_into_nested_value()
            }
            else {
                IntervalValue::bottom()
            }
        }
        else {
            IntervalValue::bottom()
        }
    }
}