use cfg::block::Block;
use cfg::expr::variable_ref::{ComponentRef, Ref, SignalRef, VarRef};
use crate::smt::smt::TermSort;
use crate::utils::error::VerificationError;
use crate::utils::template_context::TemplateContext;
use crate::utils::wrapped_smt_term::VCTerm;

pub trait VarUtils<T: VCTerm> {
    fn read_var(&mut self, ctx: &TemplateContext, reference: &Ref, is_constraint: bool) -> Result<T, VerificationError>;
    fn declare_sig(&mut self, ctx: &TemplateContext, sig_ref: &SignalRef) -> Result<(T, T), VerificationError>;
    fn declare_var(&mut self, ctx: &TemplateContext, var_ref: &VarRef) -> Result<(T, T), VerificationError>;
    fn declare_comp(&mut self, ctx: &TemplateContext, comp_ref: &ComponentRef) -> Result<(), VerificationError>;
    fn declare(&mut self, ctx: &TemplateContext, reference: &Ref) -> Result<(), VerificationError>;
    /*fn declare_sig(&mut self, ctx: &TemplateContext, var_name: &str, dimensions: &Vec<Expression>) -> Result<(), &'static str>;
    fn declare_var(&mut self, ctx: &TemplateContext, var_name: &str, dimensions: &Vec<Expression>) -> Result<(), &'static str>;
    fn declare_comp(&mut self, ctx: &TemplateContext, var_name: &str, dimensions: &Vec<Expression>) -> Result<(), &'static str>;*/
    fn add_quantified_var(&mut self, ctx: &TemplateContext, var_name: &str, sort: TermSort) -> Result<(), VerificationError>;
    fn remove_quantified_var(&mut self, ctx: &TemplateContext, var_name: &str) -> Result<(), VerificationError>;
    //fn signal_term(&mut self, ctx: &TemplateContext, sig: &Signal, is_constraint: bool) -> Result<T, &'static str>;
    fn push_callstack(&mut self);
    fn pop_callstack(&mut self);
    fn declare_callstack(&mut self) -> Result<(), VerificationError>;
    fn create_equality_constraint(&mut self, ctx: &TemplateContext, loc: &Block, reference: &Ref, is_pre_block: bool) -> Result<T, VerificationError>;
    fn create_any_equality_constraint(&mut self, ctx: &TemplateContext, loc: &Block, reference: &Ref, is_pre_block: bool) -> Result<T, VerificationError>;
}