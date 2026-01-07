use std::collections::HashMap;
use std::marker::PhantomData;
use cfg::block::Block;
use cfg::cfg::CFG;
use cfg::edge::Call;
use cfg::error::CFGError;
use cfg::template::Template;
use crate::analysis::{AbstractInterpretation, AbstractState, AbstractTransformer, DomainValue, StateError};

pub struct ContextInsensitiveAnalysis<D: DomainValue, A: AbstractState<D>, T: AbstractTransformer<D, A>> {
    results: HashMap<String, HashMap<Option<usize>, A>>,
    phantom1: PhantomData<D>,
    phantom2: PhantomData<T>
}

impl<D: DomainValue, A: AbstractState<D>, T: AbstractTransformer<D, A>>  ContextInsensitiveAnalysis<D, A, T> {
    fn get_identifier(blk_option: Option<&Block>) -> Option<usize> {
        blk_option.map(|v| v.id)
    }
}

impl<D: DomainValue, A: AbstractState<D>, T: AbstractTransformer<D, A>> AbstractInterpretation<D, A, T> for ContextInsensitiveAnalysis<D, A, T> {
    type Context = String;

    fn new() -> Self {
        Self {
            results: HashMap::new(),
            phantom1: Default::default(),
            phantom2: Default::default()
        }
    }

    fn init_context(_cfg: &CFG, template: &Template) -> Self::Context {
        template.name()
    }

    fn update_context(_ctx: &Self::Context, call: &Call) -> Self::Context {
        call.to.clone()
    }

    fn all_contexts(&self) -> Vec<Self::Context> {
        self.results.keys().map(String::clone).collect()
    }

    fn get_context_template<'c>(cfg: &'c CFG, ctx: &Self::Context) -> Result<&'c Template<'c>, CFGError> {
        cfg.get_template(&ctx)
    }

    fn get_state(&self, ctx: &Self::Context, blk: Option<&Block>) -> Result<&A, StateError> {
        if let Some(template_state) = self.results.get(ctx) {
            let id = Self::get_identifier(blk);
            if let Some(state) = template_state.get(&id) {
                Result::Ok(state)
            }
            else {
                Result::Err(StateError::BlockNotFound)
            }
        }
        else {
            Result::Err(StateError::ContextDoesNotExist)
        }
    }

    /*fn has_state(&self, ctx: &Self::Context, blk: Option<&Block>) -> bool {
        let id = Self::get_identifier(blk);
        return self.results.contains_key(ctx) && self.results.get(ctx).unwrap().get(&id).is_some();
    }

    fn get_state(&self, ctx: &Self::Context, blk: Option<&Block>) -> A {
        let id = Self::get_identifier(blk);
        if let Some(template_state) = self.results.get(ctx) {
            if let Some(state) = template_state.get(&id) {
                state.clone()
            }
            else {
                A::empty()
            }
        }
        else {
            A::empty()
        }
    }

    fn get_state_ref(&mut self, ctx: &Self::Context, blk: Option<&Block>) -> &A {
        let id = Self::get_identifier(blk);
        if let Some(template_state) = self.results.get_mut(ctx) {
            if let None = template_state.get(&id) {
                template_state.insert(id.clone(), A::empty());
                template_state.get(&id).unwrap();
            }
        }
        else {
            let mut template_state: HashMap<Option<usize>, A> = HashMap::new();
            template_state.insert(id.clone(), A::empty());
            self.results.insert(ctx.clone(), template_state);
        }

        self.results.get(ctx).unwrap().get(&id).unwrap()
    }*/

    fn join_state(&mut self, ctx: &Self::Context, blk: Option<&Block>, new_state: &A) -> bool {
        let id = Self::get_identifier(blk);
        if let Some(template_state) = self.results.get_mut(ctx) {
            if let Some(state) = template_state.get(&id) {
                if state.is_superset_of(new_state) {
                    false
                }
                else {
                    template_state.insert(id.clone(), state.join(new_state));
                    true
                }
            }
            else {
                template_state.insert(id.clone(), new_state.clone());
                true
            }
        }
        else {
            let mut template_state: HashMap<Option<usize>, A> = HashMap::new();
            template_state.insert(id.clone(), new_state.clone());
            self.results.insert(ctx.clone(), template_state);
            true
        }
    }

    fn widen_state(&mut self, ctx: &Self::Context, blk: Option<&Block>, new_state: &A) -> bool {
        let id = Self::get_identifier(blk);
        if let Some(template_state) = self.results.get_mut(ctx) {
            if let Some(state) = template_state.get(&id) {
                if state.is_superset_of(new_state) {
                    false
                }
                else {
                    template_state.insert(id.clone(), state.widen(new_state));
                    true
                }
            }
            else {
                template_state.insert(id.clone(), new_state.clone());
                true
            }
        }
        else {
            let mut template_state: HashMap<Option<usize>, A> = HashMap::new();
            template_state.insert(id.clone(), new_state.clone());
            self.results.insert(ctx.clone(), template_state);
            true
        }
    }

    fn narrow_state(&mut self, ctx: &Self::Context, blk: Option<&Block>, new_state: &A) -> bool {
        let id = Self::get_identifier(blk);
        if let Some(template_state) = self.results.get_mut(ctx) {
            if let Some(state) = template_state.get(&id) {
                let narrowed = state.narrow(new_state);
                if state != &narrowed {
                    template_state.insert(id.clone(), narrowed);
                    true
                }
                else {
                    false
                }
            }
            else {
                template_state.insert(id.clone(), new_state.clone());
                true
            }
        }
        else {
            let mut template_state: HashMap<Option<usize>, A> = HashMap::new();
            template_state.insert(id.clone(), new_state.clone());
            self.results.insert(ctx.clone(), template_state);
            true
        }
    }
}