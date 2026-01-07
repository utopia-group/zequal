use std::fmt::{Display, Formatter};
use std::fs;
use std::ops::Sub;
use std::path::PathBuf;

use ansi_term::Colour;
use itertools::Itertools;
use num_bigint_dig::BigInt;
use program_structure::program_archive::ProgramArchive;
use smtlib_lowlevel::ast::ModelResponse;
use smtlib_lowlevel::backend::{Backend, Cvc5Binary, Z3Binary};
use thiserror::Error;

use cfg::cfg::{CFG, DotSerialize, Storage};
use cfg::error::CFGError;
use cfg::expr::var_access::AccessList;
use input_user::Input;
use static_analysis::analysis::{AbstractInterpretation, AbstractState};
use vc_gen::basic_vc_gen::BasicVCGenerator;
use vc_gen::hoare_logic::vc_generator::VCGenerator;
use vc_gen::interpreter::expression_interpreter::ExpressionInterpreter;
use vc_gen::smt::error::SmtError;
use vc_gen::smt::finite_field::ff_impl::FiniteFieldTerm;
use vc_gen::smt::finite_field::int_impl::IntFiniteFieldTerm;
use vc_gen::smt::int::IntTerm;
use vc_gen::smt::smt::Quantifier;
use vc_gen::utils::error::VerificationError;
use vc_gen::utils::template_context::TemplateContext;
use vc_gen::utils::var_utils::VarUtils;
use vc_gen::utils::wrapped_smt_term::{LazyTerm, LazyVCTerm, VCTerm, VCVarTerm};
use num_traits::identities::Zero;
use num_traits::One;
use cfg::finite_fields::{BLS12381Prime, BN128Prime, FiniteFieldDef, GoldilocksPrime, GrumpkinPrime, PallasPrime, SECQ256R1Prime, SmallPrime, VestaPrime};
use cfg::named_storage::NamedStorage;
use cfg::stmt::statement::{Statement, Stmt};
use static_analysis::domains::equivalence::equivalence_analysis::DefaultEquivalenceAnalysis;

use crate::input_user::Prime;

mod input_user;
mod parser_user;
mod type_analysis_user;
mod program_formatter;

const VERSION: &'static str = env!("CARGO_PKG_VERSION");

type IntFFTerm<SZ> = LazyVCTerm<SZ, IntTerm, IntFiniteFieldTerm<SZ>>;
type FFTerm<SZ> = LazyVCTerm<SZ, FiniteFieldTerm<SZ>, FiniteFieldTerm<SZ>>;

#[derive(Error, Debug)]
pub enum EquivError  {
    CFGError(#[from] CFGError),
    SmtError(#[from] SmtError),
    VerificationError(#[from] VerificationError),
    NotVerifiedBySA,
    IOError(#[from] std::io::Error),
    SerdeError(#[from] serde_json::error::Error),
    Msg(&'static str)
}

impl Display for EquivError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            EquivError::CFGError(e) => { write!(f, "{}", e) }
            EquivError::SmtError(e) => { write!(f, "{}", e) }
            EquivError::VerificationError(e) => { write!(f, "{}", e) }
            EquivError::IOError(e) => { write!(f, "{}", e) }
            EquivError::SerdeError(e) => { write!(f, "{}", e) }
            EquivError::Msg(msg) => { write!(f, "{}", msg) }
            EquivError::NotVerifiedBySA => { write!(f, "Not Verified by static analysis")}
        }
    }
}

fn main() {
    let result = start();
    if result.is_err() {
        println!("{}: {}", Colour::Red.paint("Verification Failed"), Colour::Red.paint(result.err().unwrap().to_string()));
        std::process::exit(1);
    } else {
        println!("{}", Colour::Green.paint("Verified Equivalence"));
        std::process::exit(0);
    }
}

fn dump_cfg(output_path: &PathBuf, cfg: &CFG) -> Result<(), EquivError> {
    let mut output_dot = output_path.clone();
    output_dot.push("cfg");
    output_dot.set_extension("dot");
    Ok(fs::write(output_dot, cfg.to_dot_interproc())?)
}

fn dump_json(output_path: &PathBuf, cfg: &CFG) -> Result<(), EquivError> {
    let json = cfg.to_json()?;
    let mut output_json = output_path.clone();
    output_json.push("cfg");
    output_json.set_extension("json");
    fs::write(output_json, json)?;
    Ok(())
}

fn print_model(model_res: &Result<Vec<ModelResponse>, &'static str>) {
    match model_res {
        Ok(model) => {
            let sorted_response: Vec<&ModelResponse> = model.iter()
                .sorted_by(|a, b| a.to_string().cmp(&b.to_string()))
                .collect();
            for response in sorted_response {
                println!("{}", response);
            }
        }
        Err(err) => {
            eprintln!("{} {}", Colour::Red.paint("Could not fetch model:"), err);
        }
    }
}

fn check_equivalence<FF: FiniteFieldDef, B: Backend, T: VCTerm + VCVarTerm + LazyTerm>(args: &Input, backend: B, ast: &ProgramArchive) -> Result<(), EquivError> {
    let storage = Storage::new();
    let cfg = CFG::new(&storage, ast)?;
    let entry_template = cfg.templates.get(&cfg.entry).unwrap();
    if args.dump_dot {
        dump_cfg(&args.output_path, &cfg)?;
    }

    if args.dump_json {
        dump_json(&args.output_path, &cfg)?;
    }

    let equiv_analysis = if args.no_static_analysis {
        None
    }
    else {
        let analysis = DefaultEquivalenceAnalysis::new(&cfg);
        //To check if equivalent, must basically check if all signals are equivalent and not just outputs, for now just removing
        let mut equiv = true;

        for template in cfg.templates.values() {
            for blk in template.body.values() {
                for stmt in &blk.stmts {
                    match stmt {
                        Statement::Constrain(_) => {
                            for v_ref in stmt.reads() {
                                let stmt_equiv = analysis.is_equivalent(&template.name().into(), template, v_ref);
                                equiv = equiv && stmt_equiv
                            }
                        }
                        _ => {/* Skip */}
                    }
                }
            }
        }

        for output in &entry_template.output_signals {
            let output_ref = entry_template.post_ref_sig(output, AccessList::empty(), true, true)?;
            let output_equiv = analysis.is_equivalent(&entry_template.name().into(), entry_template, &output_ref);
            equiv = equiv && output_equiv;
        }

        if equiv {
            return Ok(())
        }

        Some(analysis)
    };

    if args.only_static_analysis {
        return Err(EquivError::NotVerifiedBySA)
    }

    let mut vc_gen = BasicVCGenerator::<FF, B, T>::new(backend, &args.output_path, &cfg, equiv_analysis, args.assume_safe_invocations)?;
    vc_gen.push_callstack();
    let ctx = TemplateContext::new(&cfg, entry_template, vec![]);
    //let succ_c = vc_gen.get_success_var(&ctx, true)?;
    let mut pre_conjuncts = vec![];
    for input in &entry_template.input_vars {
        let var_ref = entry_template.pre_ref_var(input, AccessList::empty(), true, true)?;
        let var_w = vc_gen.read_var(&ctx, &var_ref, true)?;
        let var_c = vc_gen.read_var(&ctx, &var_ref, false)?;
        pre_conjuncts.push(var_w.eq(var_c)?);
    }

    for input in &entry_template.input_signals {
        let sig_ref = entry_template.pre_ref_sig(input, AccessList::empty(), true, true)?;
        let sig_w = vc_gen.read_var(&ctx, &sig_ref, true)?;
        let sig_c = vc_gen.read_var(&ctx, &sig_ref, false)?;
        pre_conjuncts.push(sig_w.eq(sig_c)?);
    }
    let mut post_conjuncts = vec![];
    for output in &entry_template.output_signals {
        let sig_ref = entry_template.pre_ref_sig(output, AccessList::empty(), true, true)?;
        let mut sig_w = vc_gen.read_var(&ctx, &sig_ref, true)?;
        let mut sig_c = vc_gen.read_var(&ctx, &sig_ref, false)?;
        let mut quantified_vars = vec![];
        let mut disjuncts = vec![];
        for i in 0..output.dims().len() {
            let var_name = format!("i{}", i);
            let sort = T::variable_sort();
            let var = T::variable(sort.clone(), &var_name)?;
            let dimensions = var.clone().lt((&BigInt::from(0)).into())?.or(var.clone().gte(vc_gen.interpret_expr(&ctx, output.dims().get(i).unwrap(), false)?)?)?;
            sig_w = sig_w.select(var.clone())?;
            sig_c = sig_c.select(var)?;
            disjuncts.push(dimensions);
            quantified_vars.push((var_name, sort))
        }

        disjuncts.push(sig_w.eq(sig_c)?);
        let eq_check = T::or_all(disjuncts)?.quantify(Quantifier::Forall, quantified_vars)?;
        post_conjuncts.push(eq_check);
    }
    let pre = T::and_all(pre_conjuncts)?;
    let post = T::and_all(post_conjuncts)?;

    let result = vc_gen.verify_cfg(&cfg, pre, post);
    if let Err(ve) = &result {
        match ve {
            VerificationError::InvariantNotInductive(inv, model) => {
                eprintln!("{} {}", Colour::Red.paint("Invariant not inductive:"), inv.to_string());
                println!();
                print_model(model);
            }
            VerificationError::InvariantDoesNotImplyPost(inv, p, model) => {
                eprintln!("{} {}", Colour::Red.paint("Invariant does not imply Postcondition:"), inv.to_string());
                eprintln!("{} {}", Colour::Red.paint("Postcondition:"), p);
                println!();
                print_model(model);
            }
            VerificationError::PostconditionNotImplied(_, _, model) => {
                eprintln!("{}", Colour::Red.paint("Failed to prove postcondition"));
                print_model(model);
            }
            _ => { eprintln!("{}", ve) }
        }
    }

    Ok(result?)
}

fn check_equivalence_with_prime<B: Backend, FF: FiniteFieldDef>(args: &Input, backend: B, ast: &ProgramArchive) -> Result<(), EquivError> {
    if args.use_ff_theory {
        check_equivalence::<FF, B, FFTerm<FF>>(args, backend, ast)
    }
    else {
        check_equivalence::<FF, B, IntFFTerm<FF>>(args, backend, ast)
    }
}

fn check_equivalence_with_backend<B: Backend>(args: &Input, backend: B, ast: &ProgramArchive) -> Result<(), EquivError> {
    match args.prime {
        Prime::BN128 => { check_equivalence_with_prime::<B, BN128Prime>(args, backend, ast) }
        Prime::BLS12381 => { check_equivalence_with_prime::<B, BLS12381Prime>(args, backend, ast) }
        Prime::GOLDILOCKS => { check_equivalence_with_prime::<B, GoldilocksPrime>(args, backend, ast) }
        Prime::GRUMPKIN => { check_equivalence_with_prime::<B, GrumpkinPrime>(args, backend, ast) }
        Prime::PALLAS => { check_equivalence_with_prime::<B, PallasPrime>(args, backend, ast) }
        Prime::VESTA => { check_equivalence_with_prime::<B, VestaPrime>(args, backend, ast) }
        Prime::SECQ256R1 => { check_equivalence_with_prime::<B, SECQ256R1Prime>(args, backend, ast) }
        Prime::SMALL => { check_equivalence_with_prime::<B, SmallPrime>(args, backend, ast) }
    }
}

fn start() -> Result<(), EquivError> {
    let args = Input::new().map_err( |e| EquivError::Msg("Could not read input"))?;
    let mut program_archive = parser_user::parse_project(&args).map_err(|_| EquivError::Msg("Could not create archive"))?;
    /*let typechecking_res = type_analysis_user::analyse_project(&mut program_archive);
    if let Err(err) = typechecking_res {
        panic!("failed to typecheck")
    }*/

    if args.use_z3 {
        assert!(!args.use_ff_theory);
        let driver = Z3Binary::new("z3")?;
        check_equivalence_with_backend(&args, driver, &program_archive)
    }
    else {
        let driver = Cvc5Binary::new("cvc5")?;
        check_equivalence_with_backend(&args, driver, &program_archive)
    }
}
