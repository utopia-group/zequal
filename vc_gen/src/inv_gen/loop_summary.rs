use cfg::error::CFGError;
use static_analysis::domains::interval::bounded_ref::SymbolicBoundedRef;
use std::collections::{HashMap, HashSet, VecDeque};

use itertools::Itertools;
use num_bigint_dig::BigInt;
use num_traits::{One, Zero};
use smtlib_lowlevel::lexicon::Symbol;
use cfg::block::Block;

use cfg::edge::{Edge, NegInvariantCondition};
use cfg::expr::binop::BinaryOperator;
use cfg::expr::expression::{Expr, Expression};
use cfg::expr::var_access::{Access, AccessList};
use cfg::expr::variable_ref::Ref;
use cfg::finite_fields::FiniteFieldDef;
use cfg::named_storage::{Component, Var};
use cfg::stmt::statement::{Statement, Stmt};
use static_analysis::domains::interval::bounded_ref::BoundedRef;
use static_analysis::domains::interval::infinite_number::infinite_number::InfiniteNumber;
use static_analysis::domains::interval::infinite_number::symbolic_infinite_bigint::SymbolicInfiniteBigInt;
use static_analysis::domains::interval::interval_analysis::SymbolicIntervalAnalysis;
use static_analysis::domains::interval::interval_value::SymbolicInterval;

use crate::utils::error::VerificationError;
use crate::utils::template_context::TemplateContext;

#[derive(Clone)]
pub struct LoopSummary<FF: FiniteFieldDef> {
    id: usize,
    loop_iterator: Var,
    loop_iterator_ref: Ref,
    bounds: (Expression, Expression),
    outer_loops: Vec<usize>,
    nested_loops: Vec<usize>,
    pre_loop_reads: HashSet<SymbolicBoundedRef<FF>>,
    pre_loop_writes: HashSet<SymbolicBoundedRef<FF>>,
    //pre_loop_writes: HashSet<SymbolicBoundedRef<FF>>,
    loop_reads: HashSet<SymbolicBoundedRef<FF>>,
    loop_writes: HashSet<SymbolicBoundedRef<FF>>,
    //loop_writes: HashSet<SymbolicBoundedRef<FF>>,
    post_loop_reads: HashSet<SymbolicBoundedRef<FF>>,
    post_loop_writes: HashSet<SymbolicBoundedRef<FF>>,
    happens_after_writes: HashSet<SymbolicBoundedRef<FF>>,
    //post_loop_writes: HashSet<SymbolicBoundedRef<FF>>,
    all_dependencies: HashMap<String, HashMap<SymbolicBoundedRef<FF>, HashSet<SymbolicBoundedRef<FF>>>>,
}

impl<FF: FiniteFieldDef> LoopSummary<FF> {
    pub fn id(&self) -> usize {
        self.id
    }

    pub fn outer_loops(&self) -> &Vec<usize> {
        &self.outer_loops
    }

    pub fn nested_loops(&self) -> &Vec<usize> {
        &self.nested_loops
    }

    pub fn loop_iterator(&self) -> &Var {
        &self.loop_iterator
    }

    pub fn loop_iterator_ref(&self) -> &Ref {
        &self.loop_iterator_ref
    }

    pub fn bounds(&self) -> (&Expression, &Expression) {
        (&self.bounds.0, &self.bounds.1)
    }

    pub fn pre_loop_reads(&self) -> HashSet<&Ref> {
        self.pre_loop_reads.iter().map(|r| r.get_ref()).collect()
    }

    pub fn pre_loop_writes(&self) -> HashSet<&Ref> {
        self.pre_loop_writes.iter().map(|r| r.get_ref()).collect()
    }

    pub fn loop_reads(&self) -> HashSet<&Ref> {
        self.loop_reads.iter().map(|r| r.get_ref()).collect()
    }

    pub fn loop_writes(&self) -> HashSet<&Ref> {
        self.loop_writes.iter().map(|r| r.get_ref()).collect()
    }

    pub fn post_loop_reads(&self) -> HashSet<&Ref> {
        self.post_loop_reads.iter().map(|r| r.get_ref()).collect()
    }

    pub fn post_loop_writes(&self) -> HashSet<&Ref> {
        self.post_loop_writes.iter().map(|r| r.get_ref()).collect()
    }

    pub fn bounded_pre_loop_writes(&self) -> HashSet<&SymbolicBoundedRef<FF>> {
        self.pre_loop_writes.iter().collect()
    }

    pub fn bounded_loop_writes(&self) -> HashSet<&SymbolicBoundedRef<FF>> {
        self.loop_writes.iter().collect()
    }

    pub fn bounded_post_loop_writes(&self) -> HashSet<&SymbolicBoundedRef<FF>> {
        self.post_loop_writes.iter().collect()
    }

    pub fn get_decls(&self, ctx: &TemplateContext) -> Result<HashSet<String>, VerificationError> {
        let loop_head = ctx.template.get_block(&self.id)?;
        let loop_entry = loop_head.next.iter()
            .find(|e|
            if let Edge::LoopEntry(_) = e {true} else {false}
            ).ok_or("Could not find loop entry")?;

        let mut decls = HashSet::new();
        let mut seen = HashSet::from([loop_entry.local_prev(), loop_entry.local_next()]);
        let mut worklist = VecDeque::from([loop_entry.local_next()]);

        while let Some(cur_id) = worklist.pop_front() {
            let cur = ctx.template.get_block(&cur_id)?;
            for stmt in &cur.stmts {
                match stmt {
                    Statement::Declare(d) => { decls.insert(d.name().to_string()); }
                    _ => { /* Skip */ }
                }
            }

            for next in &cur.next {
                let next_id = next.local_next();
                if !seen.contains(&next_id) {
                    seen.insert(next_id);
                    worklist.push_back(next_id);
                }
            }
        }

        Ok(decls)
    }

    pub fn get_dependencies(&self, bounded_ref: &SymbolicBoundedRef<FF>) -> HashMap<&SymbolicBoundedRef<FF>, &HashSet<SymbolicBoundedRef<FF>>> {
        let id: String = bounded_ref.name().into();
        let mut write_deps = HashMap::new();

        match self.all_dependencies.get(&id) {
            None => {
                /* Should only hit this if we have an input, which won't have dependencies */
                //unreachable!("I don't think this case will ever be hit unless this is called on an item that is never written to as a symbolic bounded ref should be conservative")
            }
            Some(id_deps) => {
                for (write_ref, deps) in id_deps {
                    if bounded_ref.may_alias(write_ref) {
                        write_deps.insert(write_ref, deps);
                    }
                }
            }
        }

        write_deps
    }

    pub fn is_written_after_loop(&self, candidate: &SymbolicBoundedRef<FF>) -> bool {
        if self.happens_after_writes.contains(candidate) {
            return true;
        }

        for write in &self.happens_after_writes {
            if candidate.may_alias(write) {
                return true;
            }
        }

        false
    }

    pub fn is_written_in_loop(&self, candidate: &SymbolicBoundedRef<FF>) -> bool {
        if self.loop_writes.contains(candidate) {
            return true;
        }

        for write in &self.loop_writes {
            if candidate.may_alias(write) {
                return true;
            }
        }

        false
    }

    /*
     * Fetches only the depenencies from within the loop boundry to outside the loop boundry
     */
    pub fn get_transitive_loop_dependencies(&self, bounded_ref: &SymbolicBoundedRef<FF>) -> Result<HashSet<SymbolicBoundedRef<FF>>, CFGError> {
        let mut transitive_deps = HashSet::new();
        let mut seen = HashSet::new();
        let mut worklist: Vec<(&SymbolicBoundedRef<FF>, &SymbolicBoundedRef<FF>)> = vec![ (bounded_ref, bounded_ref) ];

        while let Some((b_write, b_read)) = worklist.pop() {
            let associated_write_deps = self.get_dependencies(b_read);
            for (associated_write, deps) in associated_write_deps {
                if self.is_written_in_loop(associated_write) {
                    if associated_write.get_ref().variable_refs().iter().find(|r| r.name() == self.loop_iterator.name()).is_some() || associated_write.is_var_ref() {
                        transitive_deps.insert(associated_write.constrain_with(b_read)?);
                    }
                }
                else if !self.is_written_after_loop(associated_write) {
                    transitive_deps.insert(associated_write.constrain_with(b_read)?);
                }

                /*
                if !self.is_written_after_loop(associated_write) && !self.is_written_in_loop(associated_write) {
                    transitive_deps.insert(associated_write.constrain_with(b_read)?);
                }
                 */

                /*if self.is_written_in_loop(b_write) && !self.is_written_in_loop(associated_write) {
                    transitive_deps.insert(associated_write.constrain_with(b_read)?);
                }
                else if self.is_written_after_loop(b_write) && !self.is_written_after_loop(associated_write) {
                    transitive_deps.insert(associated_write.constrain_with(b_read)?);
                }*/

                if !seen.contains(associated_write) {
                    seen.insert(associated_write);
                    worklist.extend(deps.iter().map(|d| (associated_write, d)));
                }
            }
        }

        Ok(transitive_deps)
    }

    pub fn get_transitive_dependencies(&self, bounded_ref: &SymbolicBoundedRef<FF>) -> HashSet<&SymbolicBoundedRef<FF>> {
        let mut transitive_deps = HashSet::new();
        let mut worklist: Vec<&SymbolicBoundedRef<FF>> = vec![ bounded_ref ];

        while let Some(b_ref) =  worklist.pop() {
            let new_deps = self.get_dependencies(b_ref);
            for (write, deps) in new_deps {
                if !transitive_deps.contains(write) {
                    transitive_deps.insert(write);
                    worklist.extend(deps)
                }
            }
        }

        transitive_deps
    }

    pub fn get_loop_head<'glob>(&self, ctx: &TemplateContext<'glob>) -> Result<&'glob Block, VerificationError> {
        Ok(ctx.template.get_block(&self.id)?)
    }

    pub fn new(ctx: &TemplateContext, loop_head_id: usize, interval_analysis: &SymbolicIntervalAnalysis<FF>) -> Result<Self, VerificationError> {
        let loop_head = ctx.template.get_block(&loop_head_id)?;

        let id = loop_head_id;
        let (pre_loop_reads, pre_loop_writes_with_deps) = Self::pre_loop_rws(ctx, interval_analysis, loop_head)?;
        let (loop_reads, loop_writes_with_deps) = Self::loop_rws(ctx, interval_analysis, loop_head)?;
        let (post_loop_reads, post_loop_writes_with_deps) = Self::post_loop_rws(ctx, interval_analysis, loop_head)?;

        let mut all_dependencies = HashMap::new();
        let mut pre_loop_writes = HashSet::new();
        for (b_ref, ref_deps) in pre_loop_writes_with_deps {
            let id: String = b_ref.name().into();
            match all_dependencies.get_mut(&id) {
                None => {
                    let ref_deps = HashMap::from([(b_ref.clone(), ref_deps.clone())]);
                    all_dependencies.insert(id, ref_deps);
                }
                Some(id_deps) => {
                    id_deps.insert(b_ref.clone(), ref_deps.clone());
                }
            }
            pre_loop_writes.insert(b_ref);
        }

        let mut loop_writes = HashSet::new();
        for (b_ref, ref_deps) in loop_writes_with_deps {
            let id: String = b_ref.name().into();
            match all_dependencies.get_mut(&id) {
                None => {
                    let ref_deps = HashMap::from([(b_ref.clone(), ref_deps.clone())]);
                    all_dependencies.insert(id, ref_deps);
                }
                Some(id_deps) => {
                    id_deps.insert(b_ref.clone(), ref_deps.clone());
                }
            }
            loop_writes.insert(b_ref);
        }

        let mut post_loop_writes = HashSet::new();
        /*for (b_ref, ref_deps) in post_loop_writes_with_deps {
            let id: String = b_ref.name().into();
            match all_dependencies.get_mut(&id) {
                None => {
                    let ref_deps = HashMap::from([(b_ref.clone(), ref_deps.clone())]);
                    all_dependencies.insert(id, ref_deps);
                }
                Some(id_deps) => {
                    id_deps.insert(b_ref.clone(), ref_deps.clone());
                }
            }
            post_loop_writes.insert(b_ref);
        }*/

        let loop_iterator = Self::identify_it_var(ctx, loop_head, &loop_writes)?;
        let loop_iterator_ref = loop_head.post_ref_var(&loop_iterator, AccessList::empty(), true, true)?;

        let nested_loops = Self::identify_nested_loops(ctx, loop_head)?;
        let outer_loops = Self::identify_outer_loops(ctx, loop_head)?;
        let bounds = Self::get_bounds(ctx, interval_analysis, loop_head, &loop_iterator)?;
        let happens_after_writes = Self::calculate_happens_after(ctx, interval_analysis, loop_head)?;

        Ok(Self { id, loop_iterator, loop_iterator_ref, bounds, outer_loops, nested_loops, pre_loop_reads, pre_loop_writes, loop_reads, loop_writes, post_loop_reads, post_loop_writes, happens_after_writes, all_dependencies })
    }

    /*
     * Note, might want to consider using the postcondition to check such queries but thats a problem for later
     */
    fn calculate_happens_after(ctx: &TemplateContext, interval_analysis: &SymbolicIntervalAnalysis<FF>, loop_head: &Block) -> Result<HashSet<SymbolicBoundedRef<FF>>, VerificationError> {
        let loop_exit = loop_head.next.iter()
            .find(|e|
            if let Edge::LoopExit(_) = e {true} else {false}
            ).ok_or("Could not find loop exit")?;
        let mut happens_after = HashSet::new();
        let mut worklist = vec![loop_exit.local_next()];
        let mut seen = HashSet::from([loop_exit.local_next()]);
        while let Some(cur_id) = worklist.pop() {
            let cur_blk = ctx.template.get_block(&cur_id)?;
            let (_, writes) = Self::collect_block_rws(ctx, interval_analysis, cur_blk)?;
            happens_after.extend(writes.iter().map(|(w, _)| w).cloned());

            for next in &cur_blk.next {
                let (_, edge_writes) = Self::collect_edge_rws(ctx, interval_analysis, next)?;
                happens_after.extend(edge_writes.iter().map(|(w, _)| w).cloned());

                let next_id_opt = match next {
                    Edge::Backedge(_) => {
                        // I don't think we'll need information about post-outer-loop
                        None
                    }
                    _ => {
                        Some(next.local_next())
                    }
                };

                if let Some(next_id) = next_id_opt {
                    if !seen.contains(&next_id) {
                        seen.insert(next_id);
                        worklist.push(next_id);
                    }
                }
            }
        }

        Ok(happens_after)
    }


    fn get_bounds(ctx: &TemplateContext, interval_analysis: &SymbolicIntervalAnalysis<FF>, loop_head: &Block, loop_iterator: &Var) -> Result<(Expression, Expression), VerificationError> {
        let loop_it_ref = loop_head.post_ref_var(loop_iterator, AccessList::empty(), true, true)?;
        let val = interval_analysis.get_interval_at_block(ctx.cfg, ctx.template, loop_head, &loop_it_ref);
        let lower = val.lower().to_expr()?;
        let upper_res = val.upper().to_expr();
        let upper = match upper_res {
            Ok(u) => {
                u
            }
            Err(_) => {
                let loop_entry = loop_head.next.iter()
                    .find_map(|e|
                    if let Edge::LoopEntry(l) = e {Some(l)} else {None}
                    ).ok_or("Could not find loop exit")?;
                let loop_it_ref = loop_head.post_ref_var(loop_iterator, AccessList::empty(), true, true)?;
                let cond = &loop_entry.cond;
                match cond {
                    Expression::BinOp(b) => {
                        if b.lhs().variable_refs().contains(&loop_it_ref) {
                            b.rhs().clone()
                        }
                        else if b.rhs().variable_refs().contains(&loop_it_ref) {
                            b.lhs().clone()
                        }
                        else {
                            panic!("Could not find loop iterator")
                        }
                    }
                    _ => {
                        panic!("Could not interpret loop condition")
                    }
                }
            }
        };
        Ok((lower, upper))
    }

    fn collect_block_rws(ctx: &TemplateContext, interval_analysis: &SymbolicIntervalAnalysis<FF>, block: &Block) -> Result<(HashSet<SymbolicBoundedRef<FF>>, HashMap<SymbolicBoundedRef<FF>, HashSet<SymbolicBoundedRef<FF>>>), VerificationError> {
        let blk_state = interval_analysis.get_state(ctx.cfg, ctx.template, block, false)?;
        let mut reads = HashSet::new();
        let mut writes = HashMap::new();

        for stmt in &block.stmts {
            let stmt_reads = stmt.reads();
            let stmt_write_opt = stmt.writes();
            let bounded_reads: HashSet<SymbolicBoundedRef<FF>> = stmt_reads.into_iter()
                .map(|r| interval_analysis.get_bounded_ref(ctx.cfg, ctx.template, &blk_state, r))
                .collect::<Result<HashSet<SymbolicBoundedRef<FF>>, CFGError>>()?;

            match stmt_write_opt {
                None => { /* Skip */ }
                Some(write) => {
                    let bounded_write = interval_analysis.get_bounded_ref(ctx.cfg, ctx.template, &blk_state, write)?;
                    writes.insert(bounded_write, bounded_reads.clone());
                }
            }

            reads.extend(bounded_reads.into_iter());
        }

        Ok((reads, writes))
    }

    fn collect_edge_rws(ctx: &TemplateContext, interval_analysis: &SymbolicIntervalAnalysis<FF>, edge: &Edge) -> Result<(HashSet<SymbolicBoundedRef<FF>>, HashMap<SymbolicBoundedRef<FF>, HashSet<SymbolicBoundedRef<FF>>>), VerificationError> {
        let mut reads = HashSet::new();
        let mut writes = HashMap::new();
        let from_blk = ctx.template.get_block(&edge.local_prev())?;
        let to_blk = ctx.template.get_block(&edge.local_next())?;
        let blk_state = interval_analysis.get_state(ctx.cfg, ctx.template, to_blk, true)?;

        match edge {
            Edge::LoopEntry(e) => {
                let bounded_reads: HashSet<SymbolicBoundedRef<FF>> = e.cond.variable_refs().into_iter()
                    .map(|r| interval_analysis.get_bounded_ref(ctx.cfg, ctx.template, &blk_state, r))
                    .collect::<Result<HashSet<SymbolicBoundedRef<FF>>, CFGError>>()?;
                reads.extend(bounded_reads);
            }
            Edge::LoopExit(e) => {
                let bounded_reads: HashSet<SymbolicBoundedRef<FF>> = e.cond.variable_refs().into_iter()
                    .map(|r| interval_analysis.get_bounded_ref(ctx.cfg, ctx.template, &blk_state, r))
                    .collect::<Result<HashSet<SymbolicBoundedRef<FF>>, CFGError>>()?;
                reads.extend(bounded_reads);
            }
            Edge::If(e) => {
                let bounded_reads: HashSet<SymbolicBoundedRef<FF>> = e.cond.variable_refs().into_iter()
                    .map(|r| interval_analysis.get_bounded_ref(ctx.cfg, ctx.template, &blk_state, r))
                    .collect::<Result<HashSet<SymbolicBoundedRef<FF>>, CFGError>>()?;
                reads.extend(bounded_reads);
            }
            Edge::Else(e) => {
                let bounded_reads: HashSet<SymbolicBoundedRef<FF>> = e.cond.variable_refs().into_iter()
                    .map(|r| interval_analysis.get_bounded_ref(ctx.cfg, ctx.template, &blk_state, r))
                    .collect::<Result<HashSet<SymbolicBoundedRef<FF>>, CFGError>>()?;
                reads.extend(bounded_reads);
            }
            Edge::Call(e) => {
                let call_target = ctx.cfg.get_template(&e.to)?;
                /*
                 * Assume all call outputs refer to vars and sigs
                 */
                let call_access = &e.access;
                for input_var in &call_target.input_vars {
                    let mut sig_access = call_access.clone();
                    sig_access.push(Access::new_component_access(input_var.name().into()))?;
                    let input_ref = from_blk.post_ref_component(ctx.cfg, e.component(ctx.cfg)?, sig_access, true, true)?;
                    let bounded_access = interval_analysis.get_bounded_ref(ctx.cfg, ctx.template, &blk_state, &input_ref)?;
                    reads.insert(bounded_access);
                }

                for input_sig in &call_target.input_signals {
                    let mut sig_access = call_access.clone();
                    sig_access.push(Access::new_component_access(input_sig.name().into()))?;
                    let input_ref = from_blk.post_ref_component(ctx.cfg, e.component(ctx.cfg)?, sig_access, true, true)?;
                    let bounded_access = interval_analysis.get_bounded_ref(ctx.cfg, ctx.template, &blk_state, &input_ref)?;
                    reads.insert(bounded_access);
                }

                for output_sig in &call_target.output_signals {
                    let mut sig_access = call_access.clone();
                    sig_access.push(Access::new_component_access(output_sig.name().into()))?;
                    let output_ref = from_blk.post_ref_component(ctx.cfg, e.component(ctx.cfg)?, sig_access, true, true)?;
                    let bounded_access = interval_analysis.get_bounded_ref(ctx.cfg, ctx.template, &blk_state, &output_ref)?;
                    writes.insert(bounded_access, reads.clone());
                }
            }
            _ => { /* No Reads/Writes */ }
        }

        Ok((reads, writes))
    }

    fn post_loop_rws(ctx: &TemplateContext, interval_analysis: &SymbolicIntervalAnalysis<FF>, loop_head: &Block) -> Result<(HashSet<SymbolicBoundedRef<FF>>, HashMap<SymbolicBoundedRef<FF>, HashSet<SymbolicBoundedRef<FF>>>), VerificationError> {
        let loop_exit = loop_head.next.iter()
            .find(|e|
            if let Edge::LoopExit(_) = e {true} else {false}
            ).ok_or("Could not find loop exit")?;
        let loop_entry = loop_head.next.iter()
            .find(|e|
            if let Edge::LoopEntry(_) = e {true} else {false}
            ).ok_or("Could not find loop entry")?;
        let mut reads = HashSet::new();
        let mut writes = HashMap::new();

        let mut seen = HashSet::from([loop_entry.local_next(), loop_exit.local_next()]);
        let mut worklist = VecDeque::from([loop_exit.local_next()]);

        while let Some(cur_id) = worklist.pop_front() {
            let cur = ctx.template.get_block(&cur_id)?;
            let (blk_reads, blk_writes) = Self::collect_block_rws(ctx, interval_analysis, cur)?;
            reads.extend(blk_reads.into_iter());
            writes.extend(blk_writes.into_iter());

            for next in &cur.next {
                let (edge_reads, edge_writes) = Self::collect_edge_rws(ctx, interval_analysis, next)?;
                reads.extend(edge_reads);
                writes.extend(edge_writes);

                let next_id = next.local_next();
                if !seen.contains(&next_id) {
                    seen.insert(next_id);
                    worklist.push_back(next_id);
                }
            }
        }

        //(reads, writes) = Self::propogate_reads_writes(ctx, reads, writes)?;

        Ok((reads, writes))
    }

    fn loop_rws(ctx: &TemplateContext, interval_analysis: &SymbolicIntervalAnalysis<FF>, loop_head: &Block) -> Result<(HashSet<SymbolicBoundedRef<FF>>, HashMap<SymbolicBoundedRef<FF>, HashSet<SymbolicBoundedRef<FF>>>), VerificationError> {
        let loop_entry = loop_head.next.iter()
            .find(|e|
            if let Edge::LoopEntry(_) = e {true} else {false}
            ).ok_or("Could not find loop entry")?;

        let (mut reads, mut writes) = Self::collect_block_rws(ctx, interval_analysis, loop_head)?;
        let mut seen = HashSet::from([loop_entry.local_prev(), loop_entry.local_next()]);
        let mut worklist = VecDeque::from([loop_entry.local_next()]);

        while let Some(cur_id) = worklist.pop_front() {
            let cur = ctx.template.get_block(&cur_id)?;
            let (blk_reads, blk_writes) = Self::collect_block_rws(ctx, interval_analysis, cur)?;
            reads.extend(blk_reads.into_iter());
            writes.extend(blk_writes.into_iter());

            for next in &cur.next {
                let (edge_reads, edge_writes) = Self::collect_edge_rws(ctx, interval_analysis, next)?;
                reads.extend(edge_reads);
                writes.extend(edge_writes);

                let next_id = next.local_next();
                if !seen.contains(&next_id) {
                    seen.insert(next_id);
                    worklist.push_back(next_id);
                }
            }
        }

        //(reads, writes) = Self::propogate_reads_writes(ctx, reads, writes)?;

        Ok((reads, writes))
    }

    fn pre_loop_rws(ctx: &TemplateContext, interval_analysis: &SymbolicIntervalAnalysis<FF>, loop_head: &Block) -> Result<(HashSet<SymbolicBoundedRef<FF>>, HashMap<SymbolicBoundedRef<FF>, HashSet<SymbolicBoundedRef<FF>>>), VerificationError> {
        let loop_entry = loop_head.next.iter()
            .find(|e|
            if let Edge::LoopEntry(_) = e {true} else {false}
            ).ok_or("Could not find loop entry")?;
        let backedge = loop_head.prev.iter()
            .find(|e|
            if let Edge::Backedge(_) = e {true} else {false}
            ).ok_or("Could not find backedge")?;

        let (mut reads, mut writes) = Self::collect_block_rws(ctx, interval_analysis, loop_head)?;
        let mut seen = HashSet::from([loop_entry.local_next(), backedge.local_prev(), loop_head.id]);
        let mut worklist = VecDeque::from([loop_head.id]);

        while let Some(cur_id) = worklist.pop_front() {
            let cur = ctx.template.get_block(&cur_id)?;
            let (blk_reads, blk_writes) = Self::collect_block_rws(ctx, interval_analysis, cur)?;
            reads.extend(blk_reads.into_iter());
            writes.extend(blk_writes.into_iter());

            for prev in &cur.prev {
                let (edge_reads, edge_writes) = Self::collect_edge_rws(ctx, interval_analysis, prev)?;
                reads.extend(edge_reads);
                writes.extend(edge_writes);

                let prev_id = prev.local_prev();
                if !seen.contains(&prev_id) {
                    seen.insert(prev_id);
                    worklist.push_back(prev_id);
                }
            }
        }

        //(reads, writes) = Self::propogate_reads_writes(ctx, reads, writes)?;

        for input in &ctx.template.input_vars {
            let mut symbolic_dims = VecDeque::new();
            let mut fake_access = AccessList::empty();
            for dim in input.dims() {
                let lower = SymbolicInfiniteBigInt::from(BigInt::zero());
                let inclusive_upper = Expression::new_binop(Box::new(dim.clone()), BinaryOperator::Sub, Box::new(Expression::new_number(BigInt::one())));
                let upper = SymbolicInfiniteBigInt::from(inclusive_upper);
                symbolic_dims.push_back(SymbolicInterval::new(lower, upper));
                //Somewhat hacky but we shouldn't need the array accesses so push a fresh var
                fake_access.push(Access::new_array_access(Expression::new_variable(Ref::new_var_ref(String::from("fresh_var"), AccessList::empty(), 0, true, true))))?;
            }

            let new_ref = ctx.template.pre_ref_var(input, fake_access, true, true)?;
            let bounded_ref = SymbolicBoundedRef::new(ctx.cfg, ctx.template, new_ref, symbolic_dims)?;
            writes.insert(bounded_ref, HashSet::new());
        }

        for input in &ctx.template.input_signals {
            let mut symbolic_dims = VecDeque::new();
            let mut fake_access = AccessList::empty();
            for dim in input.dims() {
                let lower = SymbolicInfiniteBigInt::from(BigInt::zero());
                let inclusive_upper = Expression::new_binop(Box::new(dim.clone()), BinaryOperator::Sub, Box::new(Expression::new_number(BigInt::one())));
                let upper = SymbolicInfiniteBigInt::from(inclusive_upper);
                symbolic_dims.push_back(SymbolicInterval::new(lower, upper));
                //Somewhat hacky but we shouldn't need the array accesses so push a fresh var
                fake_access.push(Access::new_array_access(Expression::new_variable(Ref::new_var_ref(String::from("fresh_var"), AccessList::empty(), 0, true, true))))?;
            }

            let new_ref = Ref::new_sig_ref(input.name().into(), fake_access, true, true);
            let bounded_ref = SymbolicBoundedRef::new(ctx.cfg, ctx.template, new_ref, symbolic_dims)?;
            writes.insert(bounded_ref, HashSet::new());
        }

        Ok((reads, writes))
    }

    fn identify_it_var(ctx: &TemplateContext, loop_head: &Block, loop_writes: &HashSet<SymbolicBoundedRef<FF>>) -> Result<Var, VerificationError> {
        let loop_entry = loop_head.next.iter()
            .find_map(|e|
            if let Edge::LoopEntry(l) = e {Some(l)} else {None}
            ).ok_or("Could not find loop entry")?;
        let cond_reads = loop_entry.cond.variable_refs();
        let mut cond_vars: HashSet<(Option<&Component>, &Var)> = cond_reads
            .into_iter()
            .filter_map(|r| match r {
                Ref::Var(v_ref) => { ctx.template.get_referenced_var(ctx.cfg, v_ref).ok() }
                _ => {None}
            })
            .collect();
        let loop_write_vars: HashSet<(Option<&Component>, &Var)> = loop_writes.iter()
            .filter_map(|r| match r.get_ref() {
                Ref::Var(v_ref) => { ctx.template.get_referenced_var(ctx.cfg, v_ref).ok() }
                _ => {None}
            })
            .collect();

        cond_vars.retain(|v| loop_write_vars.contains(v));

        if let Some((c, v)) = cond_vars.iter().next() {
            if cond_vars.len() == 1 {
                assert_eq!(c, &Option::None);
                return Ok((*v).clone())
            }
            else {
                return Err(VerificationError::NoUnqiueLoopIterator(loop_head.id, cond_vars.iter().map(|v| v.1.name().into()).collect()))
            }
        }

        Err(VerificationError::NoLoopIterator(loop_head.id))
    }

    fn identify_outer_loops(ctx: &TemplateContext, inner_loop_head: &Block) -> Result<Vec<usize>, VerificationError> {
        let mut outer_loops = vec![];
        let mut seen = HashSet::from([inner_loop_head.id]);
        let mut worklist = VecDeque::from([inner_loop_head.id]);

        while let Some(cur_id) = worklist.pop_front() {
            let cur_blk = ctx.template.get_block(&cur_id)?;

            for prev in &cur_blk.prev {
                let local_prev = prev.local_prev();
                let follow = match prev {
                    Edge::LoopEntry(_) => {
                        outer_loops.push(local_prev);
                        true
                    }
                    Edge::Backedge(_) => { false }
                    _ => { true }
                };

                if follow {
                    if !seen.contains(&local_prev) {
                        seen.insert(local_prev);
                        worklist.push_back(local_prev);
                    }
                }
            }
        }

        Ok(outer_loops)
    }

    fn identify_nested_loops(ctx: &TemplateContext, outer_loop_head: &Block) -> Result<Vec<usize>, VerificationError> {
        let mut nested_loops = vec![];
        let loop_entry = outer_loop_head.next.iter()
            .find(|e|
            if let Edge::LoopEntry(_) = e {true} else {false}
            ).ok_or("Could not find loop entry")?;

        let mut seen = HashSet::from([loop_entry.local_next(), outer_loop_head.id]);
        let mut worklist = VecDeque::from([loop_entry.local_next()]);

        while let Some(cur_id) = worklist.pop_front() {
            let cur_blk = ctx.template.get_block(&cur_id)?;

            for next in &cur_blk.next {
                match next {
                    Edge::LoopEntry(_) => {
                        nested_loops.push(cur_id)
                    }
                    _ => { /* Skip */ }
                }

                let local_next = next.local_next();
                if !seen.contains(&local_next) {
                    seen.insert(local_next);
                    worklist.push_back(local_next);
                }
            }
        }

        Ok(nested_loops)
    }

    pub fn get_outermost_loop(&self) -> usize {
        match self.outer_loops.last().cloned() {
            None => {
                self.id
            }
            Some(last) => {
                last
            }
        }
    }

    /*fn identify_nested_loop_it(ctx: &TemplateContext, inner_loop_exit: &NegInvariantCondition) -> Result<Vec<Var>, VerificationError> {
        let mut outer_it_vars = vec![];
        let loop_head = ctx.template.get_block(&inner_loop_exit.prev)?;
        let loop_entry = loop_head.next.iter()
            .find(|e|
            if let Edge::LoopEntry(_) = e {true} else {false}
            ).ok_or("Could not find loop entry")?;
        let backedge = loop_head.prev.iter()
            .find(|e|
            if let Edge::Backedge(_) = e {true} else {false}
            ).ok_or("Could not find backedge")?;

        let mut seen = HashSet::from([loop_entry.local_next(), inner_loop_exit.prev]);
        let mut worklist = VecDeque::from([loop_entry.local_next()]);

        while let Some(cur_id) = worklist.pop_front() {
            let cur = ctx.template.get_block(&cur_id)?;

            for next in &cur.next {
                match next {
                    Edge::LoopEntry(loop_entry) => {
                        let loop_head = ctx.template.get_block(&loop_entry.prev)?;
                        let loop_exit_check = loop_head.next.iter()
                            .filter_map(|e|
                                match e {
                                    Edge::LoopExit(e) => { Some(e) }
                                    _ => { None }
                               }
                            ).exactly_one();
                        match loop_exit_check {
                            Ok(outer_loop_exit) => {
                                let (_, loop_writes) = Self::loop_rws(ctx, outer_loop_exit)?;
                                let loop_it = Self::identify_it_var(ctx, outer_loop_exit, &loop_writes)?;
                                outer_it_vars.push(loop_it);
                            }
                            Err(e) => {
                                return Err(VerificationError::Msg("Could not find loop exit corresponding to loop entry"))
                            }
                        }
                    }
                    _ => { /* Skip */ }
                }

                let local_next = next.local_next();
                if !seen.contains(&local_next) {
                    seen.insert(local_next);
                    worklist.push_back(local_next);
                }
            }
        }

        Ok(outer_it_vars)
    }*/
}