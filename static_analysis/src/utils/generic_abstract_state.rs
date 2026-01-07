use cfg::expr::var_access::{Access, AccessList};
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use itertools::Itertools;
use cfg::cfg::CFG;
use cfg::expr::variable_ref::Ref;
use cfg::named_storage::{Component, Signal};
use cfg::template::Template;
use crate::analysis::{AbstractState, DomainValue};
use crate::utils::circom_abstract_state::CircomAbstractState;

#[derive(PartialEq, Eq, Clone)]
pub struct GenericAbstractState<D: DomainValue> {
    state: HashMap<String, D>
}

impl<D: DomainValue> Display for GenericAbstractState<D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let entry_str = self.state.iter().map(|(name, val)| format!("{}: {}", name, val)).join("\n");
        write!(f, "{}", entry_str)
    }
}

impl<D: DomainValue> GenericAbstractState<D> {
    fn new() -> Self {
        GenericAbstractState {
            state: HashMap::new()
        }
    }

    fn get_identifier(name: &str, access: &AccessList<Access>) -> String {
        match access.get_component_access() {
            None => { String::from(name) }
            Some(component) => {format!("{}.{}", name, component)}
        }
    }

    fn get_component_identifier(component: &Component, val: &Signal) -> String {
        format!("{}.{}", component.name(), val.name())
    }
}

impl<D: DomainValue> AbstractState<D> for GenericAbstractState<D> {
    fn empty() -> Self {
        Self::new()
    }

    fn join(&self, other: &Self) -> Self {
        let mut new_map = other.state.clone();
        for e in &self.state {
            if let Some(v) = new_map.get(e.0) {
                new_map.insert(e.0.clone(), e.1.join(v));
            }
            else {
                new_map.insert(e.0.clone(), e.1.clone());
            }
        }

        GenericAbstractState { state: new_map}
    }

    fn widen(&self, other: &Self) -> Self {
        let mut new_map = other.state.clone();
        for e in &self.state {
            if let Some(v) = new_map.get(e.0) {
                new_map.insert(e.0.clone(), e.1.widen(v));
            }
            else {
                new_map.insert(e.0.clone(), e.1.clone());
            }
        }

        GenericAbstractState { state: new_map}
    }

    fn narrow(&self, other: &Self) -> Self {
        let mut new_map = other.state.clone();
        for e in &self.state {
            if let Some(v) = new_map.get(e.0) {
                new_map.insert(e.0.clone(), e.1.narrow(v));
            }
            else {
                new_map.insert(e.0.clone(), e.1.clone());
            }
        }

        GenericAbstractState { state: new_map}
    }

    fn join_value(&mut self, _cfg: &CFG, _template: &Template, var_ref: &Ref, val: &D) {
        let id = var_ref.id().clone();
        let cur_val = if let Some(v) = self.state.get(&id) { v.clone() } else { D::bottom() };
        self.state.insert(id, cur_val.join(val));
    }

    fn apply_to_value(&mut self, cfg: &CFG, template: &Template, var_ref: &Ref, val: &D, op: fn(&D, &D) -> D) {
        let id = var_ref.id().clone();
        let cur_val = if let Some(v) = self.state.get(&id) { v.clone() } else { D::bottom() };
        self.state.insert(id, op(&cur_val, val));
    }

    fn contains_value(&self, var_ref: &Ref) -> bool {
        let id = var_ref.id();
        if let Some(_) = self.state.get(id) { true } else { false }
    }

    fn get_value(&self, var_ref: &Ref) -> D {
        // only scalar values are supported, if we implement disjunctive domains will need to re-adjust
        // treating arrays as scalars and since they can only be indexed by variables, they should be
        // equivalent as they will be inlined/expanded at instantiation
        let id = var_ref.id();
        if let Some(v) = self.state.get(id) { v.clone() } else { D::bottom() }
    }

    fn set_value(&mut self, _cfg: &CFG, _template: &Template, var_ref: &Ref, val: &D) {
        let id = var_ref.id().clone();
        self.state.insert(id, val.clone());
    }

    fn is_superset_of(&self, other: &Self) -> bool {
        for e in &other.state {
            if let Some(self_val) = self.state.get(e.0) {
                /*if(self_val == e.1) {
                    return false
                }*/
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

    fn lock_var(&mut self, v_ref: &Ref) {
        // skip for now
    }
}