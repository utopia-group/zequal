use cfg::template::Template;
use cfg::edge::Call;
use cfg::cfg::CFG;

/*
Not used right now, but will likely be useful in the future so that we can coordinate contexts between VC Gen and static analysis
 */
trait Context<'ctx> {
    fn identifier(&self) -> String;
    fn empty() -> Self;
    fn add_to_context<'a: 'ctx>(&self, cfg: &'a CFG<'a>, call: &Call) -> Self;
}

#[derive(Eq, PartialEq, Hash)]
pub struct InsensitiveContext<'ctx> {
    template: Option<&'ctx Template<'ctx>>
}

impl<'ctx> Context<'ctx> for InsensitiveContext<'ctx> {
    fn identifier(&self) -> String {
        match self.template {
            None => {String::new()}
            Some(t) => { t.name() }
        }
    }

    fn empty() -> Self {
        InsensitiveContext {
            template: None
        }
    }

    fn add_to_context<'a: 'ctx>(&self, cfg: &'a CFG<'a>, call: &Call) -> Self {
        match cfg.templates.get(&call.to) {
            None => { unreachable!("Couldn't find call target") }
            Some(t) => { Self::new(Some(t)) }
        }
    }
}

impl<'a> InsensitiveContext<'a> {
    fn new(template: Option<&'a Template<'a>>) -> Self {
        InsensitiveContext {
            template
        }
    }
}