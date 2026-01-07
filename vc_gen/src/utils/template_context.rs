use cfg::cfg::CFG;
use cfg::edge::Call;
use cfg::template::Template;

pub struct TemplateContext<'glob> {
    pub(crate) cfg: &'glob CFG<'glob>,
    pub(crate) template: &'glob Template<'glob>,
    pub(crate) callstack: Vec<Call>
}

impl<'glob> TemplateContext<'glob> {
    pub fn new(cfg: &'glob CFG<'glob>, template: &'glob Template<'glob>, callstack: Vec<Call>) -> Self {
        TemplateContext { cfg, template, callstack }
    }
}
