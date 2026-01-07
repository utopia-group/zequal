use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use serde::{Serialize};
use crate::cfg::{CFG, DotSerialize};
use crate::error::CFGError;
use crate::expr::var_access::{Access, AccessList};
use crate::expr::expression::Expression;
use crate::expr::invariant::InvariantExpr;
use crate::named_storage::{Component, NamedStorage};
use crate::template::Template;
use crate::block::Block;
use crate::expr::variable_ref::{Ref};

#[derive(Clone, Serialize, Debug)]
pub struct Condition{
    pub template: String,
    pub cond: Expression,
    pub prev: usize,
    pub next: usize
}
#[derive(Clone, Serialize, Debug)]
pub struct InvariantCondition {
    pub template: String,
    pub cond: Expression,
    //pub stmt: &'ast Statement,
    pub declared_inv: Option<InvariantExpr>,
    pub prev: usize,
    pub next: usize
}

#[derive(Clone, Serialize, Debug)]
pub struct NegCondition {
    pub template: String,
    pub cond: Expression,
    //pub stmt: &'ast Statement,
    pub prev: usize,
    pub next: usize
}
#[derive(Clone, Serialize, Debug)]
pub struct NegInvariantCondition {
    pub template: String,
    pub cond: Expression,
    pub declared_inv: Option<InvariantExpr>,
    pub prev: usize,
    pub next: usize
}

#[derive(Clone, Serialize, Debug)]
pub struct Continue {
    pub template: String,
    pub prev: usize,
    pub next: usize
}

#[derive(Clone, Serialize, Debug)]
pub struct Call {
    pub template: String,
    pub to: String,
    pub component_name: String,
    pub access: AccessList<Access>,
    pub prev: usize,
    pub to_blk: usize,
    pub ret: usize
}

impl Call {
    pub fn component<'cfg>(&self, cfg: &'cfg CFG) -> Result<&'cfg Component, CFGError> {
        let template = cfg.get_template(&self.template)?;
        match template.get_store_from_name(&self.component_name)? {
            NamedStorage::Component(c) => { Ok(c) }
            _ => { Err(CFGError::InvalidComponentAccess(self.component_name.clone())) }
        }
    }
}

#[derive(Clone, Serialize, Debug)]
pub enum Edge {
    LoopEntry(InvariantCondition),
    LoopExit(NegInvariantCondition),
    Backedge(Continue),
    If(Condition),
    IfExit(Condition),
    Else(NegCondition),
    ElseExit(NegCondition),
    Continue(Continue),
    Call(Call),
}

impl Hash for Edge {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let type_id = match self {
            Edge::LoopEntry(_) => { 1 }
            Edge::LoopExit(_) => { 2 }
            Edge::Backedge(_) => { 3 }
            Edge::If(_) => { 4 }
            Edge::IfExit(_) => { 5 }
            Edge::Else(_) => { 6 }
            Edge::ElseExit(_) => { 7 }
            Edge::Continue(_) => { 8 }
            Edge::Call(_) => { 9 }
        };
        let hash_tuple = (type_id, self.template(), self.local_prev(), self.local_next());
        hash_tuple.hash(state)
    }
}

impl<'ast> Eq for Edge {}

impl<'ast> PartialEq for Edge {
    fn eq(&self, other: &Self) -> bool {
        let type_match = match (self, other) {
            (Edge::LoopEntry(_), Edge::LoopEntry(_)) => { true }
            (Edge::LoopExit(_), Edge::LoopExit(_)) => { true }
            (Edge::Backedge(_), Edge::Backedge(_)) => { true }
            (Edge::If(_), Edge::If(_)) => { true }
            (Edge::IfExit(_), Edge::IfExit(_)) => { true }
            (Edge::Else(_), Edge::Else(_)) => { true }
            (Edge::ElseExit(_), Edge::ElseExit(_)) => { true }
            (Edge::Continue(_), Edge::Continue(_)) => { true }
            (Edge::Call(_), Edge::Call(_)) => { true }
            _ => { false }
        };
        type_match && self.local_prev() == other.local_prev() && self.local_next() == other.local_next() && self.template() == other.template()
    }
}

impl Edge {
    pub fn new_loop_entry(template_name: String, prev: usize, cond: Expression, declared_inv: Option<InvariantExpr>, next: usize) -> Result<Self, CFGError> {
        /*let cond = match stmt {
            ast::Statement::While{cond,..} => cond,
            _ => unreachable!("Must be a While Statement")
        };*/

        let entry = InvariantCondition {
            template: template_name,
            cond,
            declared_inv,
            prev,
            next,
        };

        Ok(Edge::LoopEntry(entry))
    }

    pub fn new_loop_exit(template_name: String, prev: usize, cond: Expression, declared_inv: Option<InvariantExpr>, next: usize) -> Result<Self, CFGError> {
        let exit = NegInvariantCondition {
            template: template_name,
            cond,
            declared_inv,
            prev,
            next,
        };

        Ok(Edge::LoopExit(exit))
    }

    pub fn new_if(template_name: String, prev: usize, cond: Expression, next: usize) -> Result<Self, CFGError> {
        let entry = Condition {
            template: template_name,
            cond,
            prev,
            next,
        };

        Ok(Edge::If(entry))
    }

    pub fn new_if_exit(template_name: String, prev: usize, cond: Expression, next: usize) -> Result<Self, CFGError> {
        let exit = Condition {
            template: template_name,
            cond,
            prev,
            next,
        };

        Ok(Edge::IfExit(exit))
    }

    pub fn new_else(template_name: String, prev: usize, cond: Expression, next: usize) -> Result<Self, CFGError> {
        let else_case = NegCondition {
            template: template_name,
            cond,
            prev,
            next,
        };

        Ok(Edge::Else(else_case))
    }

    pub fn new_else_exit(template_name: String, prev: usize, cond: Expression, next: usize) -> Result<Self, CFGError> {
        let else_case = NegCondition {
            template: template_name,
            cond,
            prev,
            next,
        };

        Ok(Edge::ElseExit(else_case))
    }

    pub fn new_continue(template_name: String, prev: usize, next: usize) -> Result<Self, CFGError> {
        let e = Continue {
            template: template_name,
            prev,
            next
        };

        Ok(Edge::Continue(e))
    }

    pub fn new_backedge(template_name: String, prev: usize, next: usize) -> Result<Self, CFGError> {
        let e = Continue {
            template: template_name,
            prev,
            next
        };

        Ok(Edge::Backedge(e))
    }

    pub fn new_call(template_name: String, to: String, component_name: String, access: AccessList<Access>, to_blk: usize, ret: usize, prev: usize) -> Result<Self, CFGError> {
        let e = Call {
            template: template_name,
            to,
            component_name,
            access,
            to_blk,
            ret,
            prev
        };

        Ok(Edge::Call(e))
    }

    pub fn template(&self) -> &String {
        match self {
            Edge::LoopEntry(e) => { &e.template }
            Edge::LoopExit(e) => { &e.template }
            Edge::Backedge(e) => { &e.template }
            Edge::If(e) => { &e.template }
            Edge::IfExit(e) => { &e.template }
            Edge::Else(e) => { &e.template }
            Edge::ElseExit(e) => { &e.template }
            Edge::Continue(e) => { &e.template }
            Edge::Call(e) => { &e.template }
        }
    }

    pub fn local_prev(&self) -> usize {
        match self {
            Edge::LoopEntry(e) => { e.prev }
            Edge::LoopExit(e) => { e.prev }
            Edge::Backedge(e) => { e.prev }
            Edge::If(e) => { e.prev }
            Edge::Else(e) => { e.prev }
            Edge::Continue(e) => { e.prev }
            Edge::Call(e) => { e.prev }
            Edge::IfExit(e) => { e.prev }
            Edge::ElseExit(e) => { e.prev }
        }
    }

    pub fn local_next(&self) -> usize {
        match self {
            Edge::LoopEntry(e) => { e.next }
            Edge::LoopExit(e) => { e.next }
            Edge::Backedge(e) => { e.next }
            Edge::If(e) => { e.next }
            Edge::Else(e) => { e.next }
            Edge::Continue(e) => { e.next }
            Edge::Call(e) => { e.ret }
            Edge::IfExit(e) => { e.next }
            Edge::ElseExit(e) => { e.next }
        }
    }

    pub fn set_target(&mut self, new_target: usize) {
        match self {
            Edge::LoopEntry(s, ..) => { s.next = new_target; }
            Edge::LoopExit(s, ..) => { s.next = new_target; }
            Edge::Backedge(s, ..) => { s.next = new_target; }
            Edge::If(s, ..) => { s.next = new_target; }
            Edge::Else(s, ..) => { s.next = new_target; }
            Edge::Continue(s, ..) => { s.next = new_target; }
            Edge::Call(..) => { unreachable!() }
            Edge::IfExit(s) => { s.next = new_target }
            Edge::ElseExit(s) => { s.next = new_target }
        };
    }

    pub fn set_source(&mut self, new_source: usize) {
        match self {
            Edge::LoopEntry(s, ..) => { s.prev = new_source; }
            Edge::LoopExit(s, ..) => { s.prev = new_source; }
            Edge::Backedge(s, ..) => { s.prev = new_source; }
            Edge::If(s, ..) => { s.prev = new_source; }
            Edge::Else(s, ..) => { s.prev = new_source; }
            Edge::Continue(s, ..) => { s.prev = new_source; }
            Edge::Call(s, ..) => { s.prev = new_source; }
            Edge::IfExit(s) => { s.prev = new_source }
            Edge::ElseExit(s) => { s.prev = new_source }
        };
    }

    pub fn ssa_local_renaming(&self, template: &Template) -> Result<HashMap<String, (Ref, Ref)>, CFGError> {
        if &template.name != self.template() {
            return Err(CFGError::IncorrectTemplate(self.template().clone(), template.name.clone()))
        }

        let prev: &Block = template.get_block(&self.local_prev())?;
        let next: &Block = template.get_block(&self.local_next())?;

        let prev_versions = prev.exit_versions();
        let next_versions = next.entry_versions();
        let mut renaming = HashMap::new();

        for (var, next_version) in next_versions {
            if let Some(prev_version) = prev_versions.get(var) {
                if next_version != prev_version {
                    let prev_ref = Ref::new_var_ref(var.clone(), AccessList::empty(), *prev_version, true, true);
                    let next_ref = Ref::new_var_ref(var.clone(), AccessList::empty(), *next_version, true, true);
                    renaming.insert(var.clone(), (prev_ref, next_ref));
                }
            }
        }

        Ok(renaming)
    }
}

impl DotSerialize for Edge {
    fn to_dot(&self) -> String {
        match self {
            Edge::LoopEntry(e) => {
                format!("    B{} -> B{} [label=\"{}\"];", e.prev, e.next, e.cond)
            }
            Edge::LoopExit(e) => {
                format!("    B{} -> B{} [label=\"!{}\", style=\"dashed\"];", e.prev, e.next, e.cond)
            }
            Edge::Backedge(e) => {
                format!("    B{} -> B{};", e.prev, e.next)
            }
            Edge::If(e) => {
                format!("    B{} -> B{} [label=\"{}\"];", e.prev, e.next, e.cond)
            }
            Edge::Else(e) => {
                format!("    B{} -> B{} [label=\"!{}\"];", e.prev, e.next, e.cond)
            }
            Edge::Continue(e) => {
                format!("    B{} -> B{};", e.prev, e.next)
            }
            Edge::Call(e) => {
                format!("    B{} -> B{} [style=\"dotted\"];",e.prev, e.ret)
            }
            Edge::IfExit(e) => {
                format!("    B{} -> B{} [label=\"{}\", style=\"dashed\"];", e.prev, e.next, e.cond)
            }
            Edge::ElseExit(e) => {
                format!("    B{} -> B{} [label=\"!{}\", style=\"dashed\"];", e.prev, e.next, e.cond)
            }
        }
    }

    fn to_dot_interproc(&self) -> String {
        //    B{} -> B{} [label=\"{}\"];\n
        match self {
            Edge::Call(e) => {
                format!("  B{} -> B{} [label=\"{}\"];", e.prev, e.to_blk, e.to)
            }
            _ => {
                String::default()
            }
        }
    }
}