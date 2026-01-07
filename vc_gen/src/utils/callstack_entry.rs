use std::collections::HashMap;
use cfg::expr::expression::Expression;
use cfg::expr::var_access::{Access, AccessList};
use cfg::expr::variable_ref::{ComponentRef, Ref, SignalRef, VarRef};
use static_analysis::domains::equivalence::equivalence_analysis::DefaultEquivalenceAnalysis;
use crate::smt::smt::{TermSort, UninterpretedFunction};
use crate::utils::error::VerificationError;
use crate::utils::template_context::TemplateContext;
use crate::utils::wrapped_smt_term::{VCTerm, VCVarTerm};

struct SmtIdent;
impl SmtIdent {
    fn sig_to_name(sig_ref: &SignalRef, is_constraint: bool) -> String {
        format!("{}.{}", sig_ref.id(), if is_constraint { "c" } else { "w" })
    }

    fn var_to_name(var_ref: &VarRef, is_constraint: bool) -> String {
        format!("{}.{}", var_ref.id(), if is_constraint { "c" } else { "w" })
    }

    fn component_to_name(component_ref: &ComponentRef) -> String {
        component_ref.id().clone()
    }

    fn ref_to_name(s_ref: &Ref, is_constraint: bool) -> String {
        match s_ref {
            Ref::Var(v) => { Self::var_to_name(v, is_constraint) }
            Ref::Sig(s) => { Self::sig_to_name(s, is_constraint) }
            Ref::Comp(c) => { Self::component_to_name(c) }
        }
    }
}

pub struct CallstackEntry<T: VCTerm + VCVarTerm> {
    var_to_term: HashMap<String, (T, T)>,
    uninterpreted_fns: HashMap<String, UninterpretedFunction>
}

impl<T: VCTerm + VCVarTerm> CallstackEntry<T> {
    pub(crate) fn var_terms(&self) -> &HashMap<String, (T, T)> {
        &self.var_to_term
    }

    pub(crate) fn uninterpreted_fns(&self) -> &HashMap<String, UninterpretedFunction> {
        &self.uninterpreted_fns
    }

    pub(crate) fn force_declare(&mut self, name: String, terms: (T, T)) -> Option<(T, T)> {
        self.var_to_term.insert(name, terms)
    }

    pub(crate) fn remove(&mut self, name: &String) -> Option<(T, T)> {
        self.var_to_term.remove(name)
    }

    pub(crate) fn declare_uninterpreted_fn(&mut self, name: String, args: Vec<TermSort>, ret_type: TermSort) -> &UninterpretedFunction {
        let fn_def = UninterpretedFunction { name: name.clone(), args, ret: ret_type, axioms: vec![] };
        self.uninterpreted_fns.insert(name.clone(), fn_def);
        self.uninterpreted_fns.get(&name).unwrap()
    }

    pub(crate) fn get_uninterpreted_fn(&self, name: &String) -> Result<&UninterpretedFunction, VerificationError> {
        self.uninterpreted_fns.get(name).ok_or(VerificationError::Msg("Could not find uninterpreted function"))
    }

    pub(crate) fn declare_var(&mut self, ctx: &TemplateContext, equiv_analysis: &Option<DefaultEquivalenceAnalysis>, var_ref: &VarRef) -> Result<(T, T), VerificationError> {
        let is_equiv = if let Some(a) = equiv_analysis {
            let v_ref = Ref::Var(var_ref.clone());
            a.is_equivalent(&ctx.template.name, ctx.template, &v_ref)
        }
        else {
            false
        };

        let (parent_comp, sig) = ctx.template.get_referenced_var(ctx.cfg, var_ref)?;
        let num_dims = match parent_comp {
            Some(comp) => { comp.dims().len() + sig.dims().len() }
            None => { sig.dims().len() }
        };

        let mut var_sort = T::variable_sort();
        for _ in 0..num_dims {
            var_sort = TermSort::Array(Box::new(T::variable_sort()), Box::new(var_sort))
        }

        let term_c_name = SmtIdent::var_to_name(var_ref, true);
        let term_c = T::variable(var_sort.clone(), &term_c_name)?;
        let var_defs = if is_equiv {
            self.var_to_term.insert(var_ref.id().to_string(), (term_c.clone(), term_c.clone()));
            (term_c.clone(), term_c)
        }
        else {
            let term_w_name = SmtIdent::var_to_name(var_ref, false);
            let term_w = T::variable(var_sort.clone(), &term_w_name)?;
            self.var_to_term.insert(var_ref.id().to_string(), (term_c.clone(), term_w.clone()));
            (term_c, term_w)
        };

        Ok(var_defs)
    }

    pub(crate) fn declare_sig(&mut self, ctx: &TemplateContext, equiv_analysis: &Option<DefaultEquivalenceAnalysis>, sig_ref: &SignalRef) -> Result<(T, T), VerificationError> {
        let is_equiv = if let Some(a) = equiv_analysis {
            let s_ref = Ref::Sig(sig_ref.clone());
            a.is_equivalent(&ctx.template.name, ctx.template, &s_ref)
        }
        else {
            false
        };

        let (parent_comp, sig) = ctx.template.get_referenced_sig(ctx.cfg, sig_ref)?;
        let num_dims = match parent_comp {
            Some(comp) => { comp.dims().len() + sig.dims().len() }
            None => { sig.dims().len() }
        };

        let mut sig_sort = T::signal_sort();
        for i in 0..num_dims {
            sig_sort = TermSort::Array(Box::new(T::variable_sort()), Box::new(sig_sort))
        }

        let term_c_name = SmtIdent::sig_to_name(sig_ref, true);
        let term_c = T::variable(sig_sort.clone(), &term_c_name)?;

        let sig_defs = if is_equiv {
            self.var_to_term.insert(sig_ref.id().to_string(), (term_c.clone(), term_c.clone()));
            (term_c.clone(), term_c)
        }
        else {
            let term_w_name = SmtIdent::sig_to_name(sig_ref, is_equiv);
            let term_w = T::variable(sig_sort.clone(), &term_w_name)?;
            //self.declare_const(&sig_sort, &term_w_name)?;
            self.var_to_term.insert(sig_ref.id().to_string(), (term_c.clone(), term_w.clone()));
            (term_c, term_w)
        };

        Ok(sig_defs)
    }

    pub(crate) fn declare_component(&mut self, ctx: &TemplateContext, equiv_analysis: &Option<DefaultEquivalenceAnalysis>, component_ref: &ComponentRef) -> Result<(), VerificationError> {
        let component = ctx.template.get_referenced_component(ctx.cfg, component_ref)?;
        let ref_template_name = component.instance_of();
        let ref_template = ctx.cfg.get_template(&ref_template_name.to_string())?;
        let mut template_struct_c = HashMap::new();
        let mut template_struct_w = HashMap::new();

        for var_ref in component_ref.params() {
            let (var_term_c, var_term_w) = self.declare_var(ctx, equiv_analysis, var_ref)?;
            template_struct_c.insert(var_ref.access().get_component_access().unwrap().clone(), var_term_c);
            template_struct_w.insert(var_ref.access().get_component_access().unwrap().clone(), var_term_w);
        }

        for input_sig_ref in &ref_template.input_signals {
            let access = Self::to_access_list(component.dims(), Some((input_sig_ref.name(), input_sig_ref.dims())))?;
            let Ref::Sig(sig_ref) = ctx.template.pre_ref_component(ctx.cfg, component, access, true, true)? else { unreachable!("non-signal returned") };
            self.declare_sig(ctx, equiv_analysis, &sig_ref)?;
        }

        for output_sig_ref in &ref_template.output_signals {
            let access = Self::to_access_list(component.dims(), Some((output_sig_ref.name(), output_sig_ref.dims())))?;
            let Ref::Sig(sig_ref) = ctx.template.post_ref_component(ctx.cfg, component, access, true, true)? else { unreachable!("non-signal returned") };
            self.declare_sig(ctx, equiv_analysis, &sig_ref)?;
        }

        let template_term_c = T::create_struct(template_struct_c)?;
        let template_term_w = T::create_struct(template_struct_w)?;
        self.var_to_term.insert(component_ref.id().to_string(), (template_term_c, template_term_w));

        Ok(())
    }

    fn declare(&mut self, ctx: &TemplateContext, equiv_analysis: &Option<DefaultEquivalenceAnalysis>, reference: &Ref) -> Result<(), VerificationError> {
        match reference {
            Ref::Var(v) => { self.declare_var(ctx, equiv_analysis, v)?; }
            Ref::Sig(s) => { self.declare_sig(ctx, equiv_analysis, s)?; }
            Ref::Comp(c) => { self.declare_component(ctx, equiv_analysis, c)?; }
        };

        Ok(())
    }

    pub(crate) fn num_vars(&self) -> usize {
        self.var_to_term.len()
    }

    pub(crate) fn contains(&self, reference: &Ref) -> bool {
        self.var_to_term.contains_key(reference.id())
    }

    pub(crate) fn contains_fn(&self, name: &String) -> bool {
        self.uninterpreted_fns.contains_key(name)
    }

    fn select_term(var_tuple: &(T, T), is_constraint: bool) -> T {
        if is_constraint { var_tuple.0.clone() } else { var_tuple.1.clone() }
    }

    pub(crate) fn get(&self, reference: &Ref, is_constraint: bool) -> Result<T, VerificationError> {
        if let Some(term_pair) = self.var_to_term.get(reference.id()) {
            Ok(Self::select_term(term_pair, is_constraint))
        }
        else {
            return Err(VerificationError::ReferenceNotFound("get", reference.name().to_string()))
        }
    }

    fn to_access_list(exprs: &Vec<Expression>, component_sig: Option<(&str, &Vec<Expression>)>) -> Result<AccessList<Access>, VerificationError> {
        let mut access = vec![];
        for expr in exprs {
            access.push(Access::Array{ind: expr.clone() })
        }

        if let Some(c_info) = component_sig {
            access.push(Access::Component{ name: c_info.0.into() });
            for expr in c_info.1 {
                access.push(Access::Array { ind: expr.clone() });
            }
        }

        Ok(AccessList::new(access)?)
    }

    pub fn new() -> Self {
        Self { var_to_term: HashMap::new(), uninterpreted_fns: HashMap::new() }
    }
}