use std::marker::PhantomData;
use cfg::cfg::CFG;
use cfg::expr::var_access::AccessList;
use cfg::expr::variable_ref::Ref;
use cfg::template::Template;
use crate::analysis::{AbstractInterpretation, AbstractState, DomainValue};
use crate::context_sensitivity::context_insensitive_analysis::ContextInsensitiveAnalysis;
use crate::domains::equivalence::equivalence_transformer::EquivalenceTransformer;
use crate::domains::equivalence::equivalence_value::EquivalenceValue;
use crate::utils::generic_abstract_state::GenericAbstractState;

pub type ContextInsensitiveEquivalenceAnalysis = ContextInsensitiveAnalysis<EquivalenceValue, GenericAbstractState<EquivalenceValue>, EquivalenceTransformer<GenericAbstractState<EquivalenceValue>>>;
pub type DefaultEquivalenceAnalysis = EquivalenceAnalysis<GenericAbstractState<EquivalenceValue>, ContextInsensitiveEquivalenceAnalysis>;

pub struct EquivalenceAnalysis<A: AbstractState<EquivalenceValue>, AI: AbstractInterpretation<EquivalenceValue, A, EquivalenceTransformer<A>>> {
    analysis: AI,
    phantom: PhantomData<A>
}

impl<A: AbstractState<EquivalenceValue>, AI: AbstractInterpretation<EquivalenceValue, A, EquivalenceTransformer<A>>> EquivalenceAnalysis<A, AI> {
    pub fn new(cfg: &CFG) -> Self {
        let mut analysis = AI::new();
        let entry_template = cfg.get_template(&cfg.entry).unwrap();

        let mut analysis_state = A::empty();
        for input_var in &entry_template.input_vars {
            let var_ref = entry_template.pre_ref_var(input_var, AccessList::empty(), true, true).unwrap();
            analysis_state.set_value(cfg, entry_template, &var_ref, &EquivalenceValue::bottom())
        }

        for input_sig in &entry_template.input_signals {
            let sig_ref = entry_template.pre_ref_sig(input_sig, AccessList::empty(), true, true).unwrap();
            analysis_state.set_value(cfg, entry_template, &sig_ref, &EquivalenceValue::bottom())
        }

        analysis.analyze(cfg, entry_template, analysis_state);

        Self {analysis, phantom: PhantomData::default() }
    }

    pub fn is_equivalent(&self, ctx: &AI::Context, template: &Template, var_ref: &Ref) -> bool {
        let result = self.analysis.get_end_state(ctx, template);

        if let Ok(state) = result {
            if state.contains_value(var_ref) {
                state.get_value(var_ref).is_equivalent()
            }
            else {
                false
            }
        }
        else {
            false
        }
    }
}