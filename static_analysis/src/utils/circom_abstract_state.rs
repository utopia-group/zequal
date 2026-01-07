use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::{Display, Formatter};
use itertools::Itertools;

use cfg::cfg::CFG;
use cfg::expr::variable_ref::Ref;
use cfg::named_storage::NamedStorage;
use cfg::template::Template;

use crate::analysis::{AbstractState, DomainValue};
use crate::utils::circom_value::CircomValue;
use crate::utils::generic_abstract_state::GenericAbstractState;

#[derive(PartialEq, Eq, Clone)]
pub struct CircomAbstractState<D: DomainValue> {
    state: HashMap<String, CircomValue<D>>,
    locked_vars: HashSet<String>
}

impl<D: DomainValue> Display for CircomAbstractState<D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let entry_str = self.state.iter().map(|(name, val)| format!("{}: {}", name, val)).join("\n");
        write!(f, "{}", entry_str)
    }
}

impl<D: DomainValue> AbstractState<CircomValue<D>> for CircomAbstractState<D> {
    fn empty() -> Self {
        Self::new()
    }

    fn join(&self, other: &Self) -> Self {
        let mut new_map = other.state.clone();
        for e in &self.state {
            if self.locked_vars.contains(e.0) {
                new_map.insert(e.0.clone(), e.1.clone());
            }
            else {
                if let Some(v) = new_map.get(e.0) {
                    new_map.insert(e.0.clone(), e.1.join(v));
                }
                else {
                    new_map.insert(e.0.clone(), e.1.clone());
                }
            }
        }

        CircomAbstractState { state: new_map, locked_vars: self.locked_vars.clone()}
    }

    fn widen(&self, other: &Self) -> Self {
        let mut new_map = other.state.clone();
        for e in &self.state {
            if self.locked_vars.contains(e.0) {
                new_map.insert(e.0.clone(), e.1.clone());
            }
            else {
                if let Some(v) = new_map.get(e.0) {
                    new_map.insert(e.0.clone(), e.1.widen(v));
                }
                else {
                    new_map.insert(e.0.clone(), e.1.clone());
                }
            }
        }

        CircomAbstractState { state: new_map, locked_vars: self.locked_vars.clone() }
    }

    fn narrow(&self, other: &Self) -> Self {
        let mut new_map = other.state.clone();
        for e in &self.state {
            if self.locked_vars.contains(e.0) {
                new_map.insert(e.0.clone(), e.1.clone());
            }
            else {
                if let Some(v) = new_map.get(e.0) {
                    new_map.insert(e.0.clone(), e.1.narrow(v));
                } else {
                    new_map.insert(e.0.clone(), e.1.clone());
                }
            }
        }

        CircomAbstractState { state: new_map, locked_vars: self.locked_vars.clone() }
    }

    fn join_value(&mut self, cfg: &CFG, template: &Template, v_ref: &Ref, other: &CircomValue<D>) {
        if self.locked_vars.contains(v_ref.id()) {
            return;
        }

        let abstract_val = self.state.get(v_ref.id());
        let new_val = match abstract_val {
            None => {
                let default = Self::ref_bottom(cfg, template, v_ref);
                default.join_ref(other, v_ref)
            }
            Some(val) => {
                val.join_ref(other, v_ref)
            }
        };
        self.state.insert(v_ref.id().clone(), new_val);
    }

    fn apply_to_value(&mut self, cfg: &CFG, template: &Template, v_ref: &Ref, other: &CircomValue<D>, op: fn(&CircomValue<D>, &CircomValue<D>) -> CircomValue<D>) {
        if self.locked_vars.contains(v_ref.id()) {
            return;
        }

        let abstract_val = self.state.get(v_ref.id());
        let current_val = match abstract_val {
            None => {
                Self::ref_bottom(cfg, template, v_ref)
            }
            Some(val) => {
                val.clone()
            }
        };

        let lhs = current_val.get_ref(v_ref);
        let rhs = other.get_ref(v_ref);
        let new_ref_val = op(&lhs, &rhs);
        current_val.set_ref(&new_ref_val, v_ref);
        self.state.insert(v_ref.id().clone(), current_val);
    }

    fn contains_value(&self, var_ref: &Ref) -> bool {
        //if name is contained in store, then we can assume all entries in "struct" are present
        self.state.contains_key(var_ref.id())
    }

    fn get_value(&self, var_ref: &Ref) -> CircomValue<D> {
        let maybe_val = self.state.get(var_ref.id());

        match maybe_val {
            None => {
                D::bottom().into()
            }
            Some(circom_val) => {
                circom_val.get_ref(var_ref)
            }
        }
    }

    fn set_value(&mut self, cfg: &CFG, template: &Template, v_ref: &Ref, to: &CircomValue<D>) {
        if self.locked_vars.contains(v_ref.id()) {
            return;
        }

        let abstract_val = self.state.get(v_ref.id());
        let new_val = match abstract_val {
            None => {
                let default = Self::ref_bottom(cfg, template, v_ref);
                default.set_ref(to, v_ref)
            }
            Some(val) => {
                val.set_ref(to, v_ref)
            }
        };

        self.state.insert(v_ref.id().clone(), new_val);
    }

    fn lock_var(&mut self, v_ref: &Ref) {
        self.locked_vars.insert(v_ref.id().clone());
    }

    fn is_superset_of(&self, other: &Self) -> bool {
        for e in &other.state {
            if let Some(self_val) = self.state.get(e.0) {
                let joined = self_val.join(e.1);
                if self_val != &joined {
                    return false;
                }
            } else {
                return false
            }
        }

        true
    }
}

impl<D: DomainValue> CircomAbstractState<D> {
    pub fn new() -> Self {
        CircomAbstractState {
            state: HashMap::new(), locked_vars: HashSet::new()
        }
    }

    fn ref_bottom(cfg: &CFG, template: &Template, v_ref: &Ref) -> CircomValue<D> {
        let (component, store) = template.get_referenced(cfg, v_ref).unwrap();
        match component {
            None => {
                match store {
                    NamedStorage::Variable(var) => {
                        CircomValue::new_value(D::bottom())
                    }
                    NamedStorage::Signal(sig) => {
                        CircomValue::new_signal(D::bottom(), D::bottom())
                    }
                    NamedStorage::Component(comp) => {
                        let invoked = comp.instance_of();
                        let invoked_template = cfg.get_template(&invoked.into()).unwrap();
                        let mut component_entries: BTreeMap<String, CircomValue<D>> = BTreeMap::new();

                        for input_var in &invoked_template.input_vars {
                            component_entries.insert(input_var.name().into(), CircomValue::new_value(D::bottom()));
                        }

                        for input_sig in &invoked_template.input_signals {
                            component_entries.insert(input_sig.name().into(), CircomValue::new_signal(D::bottom(), D::bottom()));
                        }

                        for output_sig in &invoked_template.output_signals {
                            component_entries.insert(output_sig.name().into(), CircomValue::new_signal(D::bottom(), D::bottom()));
                        }

                        CircomValue::new_component(component_entries)
                    }
                }
            }
            Some(comp) => {
                let invoked = comp.instance_of();
                let invoked_template = cfg.get_template(&invoked.into()).unwrap();
                let mut component_entries: BTreeMap<String, CircomValue<D>> = BTreeMap::new();

                for input_var in &invoked_template.input_vars {
                    component_entries.insert(input_var.name().into(), CircomValue::new_value(D::bottom()));
                }

                for input_sig in &invoked_template.input_signals {
                    component_entries.insert(input_sig.name().into(), CircomValue::new_signal(D::bottom(), D::bottom()));
                }

                for output_sig in &invoked_template.output_signals {
                    component_entries.insert(output_sig.name().into(), CircomValue::new_signal(D::bottom(), D::bottom()));
                }

                CircomValue::new_component(component_entries)
            }
        }
    }
}