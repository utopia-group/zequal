use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};

use cfg::expr::variable_ref::{ComponentRef, Ref, SignalRef, VarRef};
use itertools::Itertools;

use crate::analysis::DomainValue;

#[derive(Hash, PartialEq, Eq, Clone)]
pub enum CircomValue<AbstractValue: DomainValue> {
    Component(BTreeMap<String, CircomValue<AbstractValue>>),
    Signal{ w: AbstractValue, c: AbstractValue },
    Value(AbstractValue)
}

impl<AbstractValue: DomainValue> Display for CircomValue<AbstractValue> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            CircomValue::Component(entries) => {
                let entry_str = entries.iter().map(|(name, val)| format!("{}: {}", name, val)).join(", ");
                write!(f, "{}{}{}", "{", entry_str, "}")
            }
            CircomValue::Signal { w, c } => {
                write!(f, "(w: {}, c: {})", w, c)
            }
            CircomValue::Value(val) => {
                write!(f, "({})", val)
            }
        }
    }
}

impl<AbstractValue: DomainValue> From<AbstractValue> for CircomValue<AbstractValue> {
    fn from(value: AbstractValue) -> Self {
        Self::new_value(value)
    }
}

impl<AbstractValue: DomainValue> DomainValue for CircomValue<AbstractValue> {
    fn top() -> Self {
        Self::Value(AbstractValue::top())
    }

    fn bottom() -> Self {
        Self::Value(AbstractValue::bottom())
    }

    fn is_bottom(&self) -> bool {
        match self {
            CircomValue::Component(entries) => {
                let mut is_bottom = true;
                for (name, val) in entries {
                    is_bottom = val.is_bottom() && is_bottom;
                }
                is_bottom
            }
            CircomValue::Signal { w, c } => {
                w.is_bottom() && c.is_bottom()
            }
            CircomValue::Value(val) => {
                val.is_bottom()
            }
        }
    }

    fn join(&self, other: &Self) -> Self {
        self.apply_binop(other, AbstractValue::join)
    }

    fn widen(&self, other: &Self) -> Self {
        self.apply_binop(other, AbstractValue::widen)
    }

    fn narrow(&self, other: &Self) -> Self {
        self.apply_binop(other, AbstractValue::narrow)
    }

    fn should_narrow() -> bool {
        AbstractValue::should_narrow()
    }

    fn meet(&self, other: &Self) -> Self {
        self.apply_binop(other, AbstractValue::meet)
    }
}

impl<AbstractValue: DomainValue> CircomValue<AbstractValue> {
    pub fn new_value(val: AbstractValue) -> Self {
        Self::Value(val)
    }

    pub fn new_signal(w: AbstractValue, c: AbstractValue) -> Self {
        Self::Signal{w, c}
    }

    pub fn new_component(entries: BTreeMap<String, CircomValue<AbstractValue>>) -> Self {
        Self::Component(entries)
    }

    pub fn get_ref(&self, v_ref: &Ref) -> Self {
        match v_ref {
            Ref::Var(var_ref) => {
                self.get_var_ref(var_ref)
            }
            Ref::Sig(sig_ref) => {
                self.get_sig_ref(sig_ref)
            }
            Ref::Comp(comp_ref) => {
                self.get_comp_ref(comp_ref)
            }
        }
    }

    pub fn get_var_ref(&self, var_ref: &VarRef) -> Self {
        match self {
            CircomValue::Component(entries) => {
                let component_ref = var_ref.access().get_component_access();
                match component_ref {
                    None => {
                        unreachable!("Incompatible types")
                    }
                    Some(component_name) => {
                        let res = entries.get(component_name);
                        match res {
                            None => {
                                Self::bottom()
                            }
                            Some(abstract_val) => {
                                abstract_val.get_var_ref(var_ref)
                            }
                        }
                    }
                }
            }
            CircomValue::Value(_) => {
                self.clone()
            }
            // the variable is an accumulator
            CircomValue::Signal { .. } => {
                self.clone()
            }
            _ => {
                unreachable!("Invalid Type: Expected variable but found signal abstract value")
            }
        }
    }

    pub fn get_sig_ref(&self, sig_ref: &SignalRef) -> Self {
        match self {
            CircomValue::Component(entries) => {
                let component_ref = sig_ref.access().get_component_access();
                match component_ref {
                    None => {
                        unreachable!("Incompatible types")
                    }
                    Some(component_name) => {
                        let res = entries.get(component_name);
                        match res {
                            None => {
                                Self::bottom()
                            }
                            Some(abstract_val) => {
                                abstract_val.get_sig_ref(sig_ref)
                            }
                        }
                    }
                }
            }
            CircomValue::Signal { w, c } => {
                if sig_ref.ref_constraint() && sig_ref.ref_witness() {
                    self.clone()
                }
                else if sig_ref.ref_constraint() {
                    c.clone().into()
                }
                else if sig_ref.ref_witness() {
                    w.clone().into()
                }
                else {
                    CircomValue::bottom()
                }
            }
            CircomValue::Value(val) => {
                if sig_ref.ref_constraint() && sig_ref.ref_witness() {
                    Self::new_signal(val.clone(), val.clone())
                }
                else if sig_ref.ref_constraint() || sig_ref.ref_witness() {
                    self.clone()
                }
                else {
                    CircomValue::bottom()
                }
            }
        }
    }

    pub fn get_comp_ref(&self, var_ref: &ComponentRef) -> Self {
        match self {
            CircomValue::Component(_) => {
                self.clone()
            }
            CircomValue::Value(_) => {
                self.clone()
            }
            _ => {
                unreachable!("Invalid Type: Expected component but found signal abstract value")
            }
        }
    }

    pub fn join_ref(&self, other: &Self, v_ref: &Ref) -> Self {
        match v_ref {
            Ref::Var(var_ref) => {
                self.join_var_ref(other, var_ref)
            }
            Ref::Sig(sig_ref) => {
                self.join_sig_ref(other, sig_ref)
            }
            Ref::Comp(comp_ref) => {
                self.join_component_ref(other, comp_ref)
            }
        }
    }

    pub fn join_var_ref(&self, other: &Self, var_ref: &VarRef) -> Self {
        match (self, other) {
            (Self::Value(_), Self::Value(_)) => {
                self.join(other)
            }
            (Self::Component(c1), Self::Value(v2)) => {
                let component_ref = var_ref.access().get_component_access();
                match component_ref {
                    None => {
                        unreachable!("Found component abstract val but there is no component reference in signal")
                    }
                    Some(component_name) => {
                        let maybe_component_val = c1.get(component_name);
                        let mut ret_component = c1.clone();
                        match maybe_component_val {
                            None => {
                                ret_component.insert(component_name.clone(), other.clone());
                            }
                            Some(component_val) => {
                                ret_component.insert(component_name.clone(), component_val.join_var_ref(other, var_ref));
                            }
                        }
                        Self::new_component(ret_component)
                    }
                }
            }
            (_, Self::Component(c2)) => {
                let component_ref = var_ref.access().get_component_access();
                match component_ref {
                    None => {
                        unreachable!("Found component abstract val but there is no component reference in signal")
                    }
                    Some(component_name) => {
                        let maybe_component_val = c2.get(component_name);
                        match maybe_component_val {
                            None => {
                                self.clone()
                            }
                            Some(component_val) => {
                                self.join_var_ref(component_val, var_ref)
                            }
                        }
                    }
                }
            }
            (_, _) => {
                unreachable!("Invalid Type: Expected variable but found signal abstract value")
            }
        }
    }

    pub fn join_sig_ref(&self, other: &Self, sig_ref: &SignalRef) -> Self {
        match (self, other) {
            (Self::Value(v1), Self::Value(v2)) => {
                Self::join_signal_by_ref(sig_ref, v1, v1, v2, v2)
            }
            (Self::Value(v1), Self::Signal{c: c2, w: w2}) => {
                Self::join_signal_by_ref(sig_ref, v1, v1, w2, c2)
            }
            (Self::Signal{c: c1, w: w1}, Self::Value(v2)) => {
                Self::join_signal_by_ref(sig_ref, w1, c1, v2, v2)
            }
            (Self::Signal{c: c1, w: w1}, Self::Signal{c: c2, w: w2}) => {
                Self::join_signal_by_ref(sig_ref, w1, c1, w2, c2)
            }
            (Self::Component(c1), Self::Value(v2)) => {
                let component_ref = sig_ref.access().get_component_access();
                match component_ref {
                    None => {
                        unreachable!("Found component abstract val but there is no component reference in signal")
                    }
                    Some(component_name) => {
                        let maybe_component_val = c1.get(component_name);
                        let mut ret_component = c1.clone();
                        match maybe_component_val {
                            None => {
                                let bot = AbstractValue::bottom();
                                ret_component.insert(component_name.clone(), Self::join_signal_by_ref(sig_ref, &bot, &bot, v2, v2));
                            }
                            Some(component_val) => {
                                ret_component.insert(component_name.clone(), component_val.join_sig_ref(other, sig_ref));
                            }
                        }
                        Self::new_component(ret_component)
                    }
                }
            }
            (Self::Component(c1), Self::Signal{c: c2, w: w2}) => {
                let component_ref = sig_ref.access().get_component_access();
                match component_ref {
                    None => {
                        unreachable!("Found component abstract val but there is no component reference in signal")
                    }
                    Some(component_name) => {
                        let maybe_component_val = c1.get(component_name);
                        let mut ret_component = c1.clone();
                        match maybe_component_val {
                            None => {
                                let bot = AbstractValue::bottom();
                                ret_component.insert(component_name.clone(), Self::join_signal_by_ref(sig_ref, &bot, &bot, w2, c2));
                            }
                            Some(component_val) => {
                                ret_component.insert(component_name.clone(), component_val.join_sig_ref(other, sig_ref));
                            }
                        }
                        Self::new_component(ret_component)
                    }
                }
            }
            (_, Self::Component(c2)) => {
                let component_ref = sig_ref.access().get_component_access();
                match component_ref {
                    None => {
                        unreachable!("Found component abstract val but there is no component reference in signal")
                    }
                    Some(component_name) => {
                        let maybe_component_val = c2.get(component_name);
                        match maybe_component_val {
                            None => {
                                self.clone()
                            }
                            Some(component_val) => {
                                self.join_sig_ref(component_val, sig_ref)
                            }
                        }
                    }
                }
            }
        }
    }

    pub fn join_component_ref(&self, other: &Self, component_ref: &ComponentRef) -> Self {
        match (self, other) {
            (Self::Value(_), Self::Value(_)) => {
                self.join(other)
            }
            (Self::Value(v1), Self::Component(c2)) => {
                self.join(other)
            }
            (Self::Component(c1), Self::Value(v2)) => {
                self.join(other)
            }
            (Self::Component(_), Self::Component(_)) => {
                self.join(other)
            }
            (_, _) => {
                unreachable!("Invalid Type: Expected component but found signal abstract value")
            }
        }
    }

    pub fn set_ref(&self, to: &Self, v_ref: &Ref) -> Self {
        match v_ref {
            Ref::Var(var_ref) => {
                self.set_var_ref(to, var_ref)
            }
            Ref::Sig(sig_ref) => {
                self.set_sig_ref(to, sig_ref)
            }
            Ref::Comp(comp_ref) => {
                self.set_component_ref(to, comp_ref)
            }
        }
    }

    pub fn set_var_ref(&self, to: &Self, var_ref: &VarRef) -> Self {
        // note variables can act as accumulators, so allow var to be set to sig abstract val
        match (self, to) {
            (Self::Value(_), Self::Value(_)) => {
                to.clone()
            }
            (Self::Value(_), Self::Signal{ .. }) => {
                to.clone()
            }
            (Self::Signal{ .. }, Self::Value(_)) => {
                to.clone()
            }
            (Self::Signal{ .. }, Self::Signal { .. }) => {
                to.clone()
            }
            (Self::Component(c1), Self::Value(v2)) => {
                let component_ref = var_ref.access().get_component_access();
                match component_ref {
                    None => {
                        unreachable!("Found component abstract val but there is no component reference in signal")
                    }
                    Some(component_name) => {
                        let mut ret_component = c1.clone();
                        ret_component.insert(component_name.clone(), to.clone());
                        Self::new_component(ret_component)
                    }
                }
            }
            (_, Self::Component(c2)) => {
                let component_ref = var_ref.access().get_component_access();
                match component_ref {
                    None => {
                        unreachable!("Found component abstract val but there is no component reference in signal")
                    }
                    Some(component_name) => {
                        let maybe_component_val = c2.get(component_name);
                        match maybe_component_val {
                            None => {
                                self.clone()
                            }
                            Some(component_val) => {
                                self.set_var_ref(component_val, var_ref)
                            }
                        }
                    }
                }
            }
            (_, _) => {
                match self {
                    CircomValue::Component(_) => {
                        println!("component")
                    }
                    CircomValue::Signal { w, c } => {
                        println!("signal")
                    }
                    CircomValue::Value(v) => {
                        println!("variable")
                    }
                }

                match to {
                    CircomValue::Component(_) => {
                        println!("component")
                    }
                    CircomValue::Signal { w, c } => {
                        println!("signal")
                    }
                    CircomValue::Value(v) => {
                        println!("variable")
                    }
                }
                unreachable!("Invalid Type: Expected variable but found signal abstract value")
            }
        }
    }

    pub fn set_sig_ref(&self, to: &Self, sig_ref: &SignalRef) -> Self {
        match (self, to) {
            (Self::Value(v1), Self::Value(v2)) => {
                Self::new_signal(if sig_ref.ref_witness() {v2.clone()} else {v1.clone()}, if sig_ref.ref_constraint() {v2.clone()} else {v1.clone()})
            }
            (Self::Value(v1), Self::Signal{c: c2, w: w2}) => {
                Self::new_signal(if sig_ref.ref_witness() {w2.clone()} else {v1.clone()}, if sig_ref.ref_constraint() {c2.clone()} else {v1.clone()})
            }
            (Self::Signal{c: c1, w: w1}, Self::Value(v2)) => {
                Self::new_signal(if sig_ref.ref_witness() {v2.clone()} else {w1.clone()}, if sig_ref.ref_constraint() {v2.clone()} else {c1.clone()})
            }
            (Self::Signal{c: c1, w: w1}, Self::Signal{c: c2, w: w2}) => {
                Self::new_signal(if sig_ref.ref_witness() {w2.clone()} else {w1.clone()}, if sig_ref.ref_constraint() {c2.clone()} else {c1.clone()})
            }
            (_, Self::Component(c2)) => {
                let component_ref = sig_ref.access().get_component_access();
                match component_ref {
                    None => {
                        unreachable!("Found component abstract val but there is no component reference in signal")
                    }
                    Some(component_name) => {
                        let maybe_component_val = c2.get(component_name);
                        match maybe_component_val {
                            None => {
                                self.clone()
                            }
                            Some(component_val) => {
                                self.set_sig_ref(component_val, sig_ref)
                            }
                        }
                    }
                }
            }
            (Self::Component(c1), _) => {
                let component_ref = sig_ref.access().get_component_access();
                match component_ref {
                    None => {
                        unreachable!("Found component abstract val but there is no component reference in signal")
                    }
                    Some(component_name) => {
                        let maybe_component_val = c1.get(component_name);
                        let mut ret_component = c1.clone();
                        match maybe_component_val {
                            None => {
                                let bot = CircomValue::bottom();
                                ret_component.insert(component_name.clone(), bot.set_sig_ref(to, sig_ref));
                            }
                            Some(component_val) => {
                                ret_component.insert(component_name.clone(), component_val.set_sig_ref(to, sig_ref));
                            }
                        }
                        Self::new_component(ret_component)
                    }
                }
            }
        }
    }

    pub fn set_component_ref(&self, to: &Self, component_ref: &ComponentRef) -> Self {
        match (self, to) {
            (Self::Value(_), Self::Value(_)) => {
                to.clone()
            }
            (Self::Value(v1), Self::Component(c2)) => {
                to.clone()
            }
            (Self::Component(c1), Self::Value(v2)) => {
                to.clone()
            }
            (Self::Component(_), Self::Component(_)) => {
                to.clone()
            }
            (_, _) => {
                unreachable!("Invalid Type: Expected component but found signal abstract value")
            }
        }
    }


    pub fn apply_binop(&self, other: &Self, binop: fn(&AbstractValue, &AbstractValue) -> AbstractValue) -> Self {
        match (self, other) {
            (Self::Component(c1), Self::Component(c2)) => {
                let mut entries = BTreeMap::new();
                for (name, v1) in c1 {
                    match c2.get(name) {
                        None => {
                            entries.insert(name.clone(), v1.clone());
                        }
                        Some(v2) => {
                            let res = v1.apply_binop(v2, binop);
                            entries.insert(name.clone(), res);
                        }
                    }
                }

                for (name, val) in c2 {
                    if !c1.contains_key(name) {
                        entries.insert(name.clone(), val.clone());
                    }
                }

                Self::Component(entries)
            }
            (Self::Component(c1), Self::Value(_v2)) => {
                let mut entries = BTreeMap::new();
                for (name, v1) in c1 {
                    let ret = v1.apply_binop(other, binop);
                    entries.insert(name.clone(), ret);
                }

                Self::Component(entries)
            }
            (Self::Value(_v1), Self::Component(c2)) => {
                let mut entries = BTreeMap::new();
                for (name, v2) in c2 {
                    let ret = self.apply_binop(v2, binop);
                    entries.insert(name.clone(), ret);
                }

                Self::Component(entries)
            }
            (Self::Signal {w: w1, c: c1}, Self::Signal {w: w2, c: c2}) => {
                let ret_w = binop(w1, w2);
                let ret_c = binop(c1, c2);
                Self::Signal { w: ret_w, c: ret_c }
            }
            (Self::Signal {w: w1, c: c1}, Self::Value(v2)) => {
                let ret_w = binop(w1, v2);
                let ret_c = binop(c1, v2);
                Self::Signal { w: ret_w, c: ret_c }
            }
            (Self::Value(v1), Self::Signal {w: w2, c: c2}) => {
                let ret_w = binop(v1, w2);
                let ret_c = binop(v1, c2);
                Self::Signal { w: ret_w, c: ret_c }
            }
            (Self::Value(v1), Self::Value(v2)) => {
                let ret = binop(v1, v2);
                Self::Value(ret)
            }
            (_, _) => {
                unreachable!("Cannot apply illegal binop")
            }
        }
    }

    pub fn apply_unop(&self, unop: fn(&AbstractValue) -> AbstractValue) -> Self {
        match self {
            Self::Component(c) => {
                let mut entries = BTreeMap::new();
                for (name, v) in c {
                    let ret = v.apply_unop(unop);
                    entries.insert(name.clone(), ret);
                }

                Self::Component(entries)
            }
            Self::Signal { w, c } => {
                Self::Signal { w: unop(w), c: unop(c) }
            }
            Self::Value(v) => {
                Self::Value(unop(v))
            }
            _ => {
                unreachable!("Cannot apply illegal unop")
            }
        }
    }

    fn join_signal_by_ref(sig_ref: &SignalRef, w1: &AbstractValue, c1: &AbstractValue, w2: &AbstractValue, c2: &AbstractValue) -> Self {
        let res_c = if sig_ref.ref_constraint() {
            c1.join(c2)
        }
        else {
            c1.clone()
        };

        let res_w = if sig_ref.ref_witness() {
            w1.join(w2)
        }
        else {
            w1.clone()
        };

        Self::Signal { c: res_c, w: res_w }
    }

    pub fn join_into_nested_value(&self) -> AbstractValue {
        match self {
            CircomValue::Component(entries) => {
                let mut joined = AbstractValue::bottom();
                for (_, val) in entries {
                    joined = joined.join(&val.join_into_nested_value())
                }
                joined
            }
            CircomValue::Signal { c, w } => {
                c.join(w)
            }
            CircomValue::Value(val) => {
                val.clone()
            }
        }
    }
}

