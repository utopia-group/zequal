use std::fs;
use std::path::PathBuf;
use smtlib_lowlevel::ast;
use smtlib_lowlevel::ast::{Attribute, AttributeValue, CheckSatResponse, Command, GeneralResponse, Logic, ModelResponse, SpecificSuccessResponse};
use smtlib_lowlevel::backend::{Backend};
use smtlib_lowlevel::Driver;
use smtlib_lowlevel::lexicon::{BValue, Keyword, Numeral, Symbol};
use crate::smt::smt::{TermSort, TypedTerm};

pub enum SmtSolver {
    Z3,
    CVC5
}

pub struct Solver<B: Backend> {
    smt_solver: Driver<B>,
    script: Vec<Command>,
    output_script: PathBuf
}

pub(crate) trait SolverInternalUtils {
    fn exec_cmd(&mut self, cmd: Command) -> Result<GeneralResponse, &'static str>;
    fn script(&self) -> &Vec<Command>;
}

pub trait SolverUtils: SolverInternalUtils {
    fn assert<T: TypedTerm>(&mut self, term: T) -> Result<(), &'static str> {
        let response = self.exec_cmd(Command::Assert(term.clone().into()))?;

        match response {
            GeneralResponse::Success => { Ok(()) }
            GeneralResponse::Error(e) => {
                println!("{}", term.term());
                panic!("Solver: Solver generated an error: {}", e)
            }
            _ => {Err("Solver: Unknown Error when asserting")}
        }
    }

    fn check_sat(&mut self) -> Result<CheckSatResponse, &'static str> {
        let response = self.exec_cmd(Command::CheckSat)?;

        match response {
            GeneralResponse::Error(_) => { Err("Solver: Solver generated an error during a check-sat") }
            GeneralResponse::SpecificSuccessResponse(res) => {
                match res {
                    SpecificSuccessResponse::CheckSatResponse(sat) => {
                        Ok(sat)
                    }
                    _ => {
                        Err("Solver: Specific response didn't match sat")
                    }
                }
            }
            _ => {
                Err("Solver: Unknown Response when checking sat")
            }
        }
    }

    fn set_logic(&mut self, logic: Logic) -> Result<(), &'static str> {
        let response = self.exec_cmd(Command::SetLogic(Symbol(logic.to_string())))?;
        match response {
            GeneralResponse::Success => { Ok(()) }
            GeneralResponse::Error(e) => { panic!("Solver: Solver generated an error: {}", e) }
            _ => {Err("Solver: Unknown Error when asserting")}
        }
    }

    fn declare_fn(&mut self, args: &Vec<TermSort>, ret_sort: &TermSort, name: &String) -> Result<(), &'static str> {
        let arg_sorts = args.iter().map(|s| s.sort()).collect();
        let response = self.exec_cmd(Command::DeclareFun(Symbol(name.clone()), arg_sorts, ret_sort.sort()))?;
        match response {
            GeneralResponse::Success => { Ok(()) }
            GeneralResponse::Error(e) => { panic!("Solver: Solver generated an error: {}", e) }
            _ => {Err("Solver: Unknown Error when declaring a function")}
        }
    }

    fn get_unsat_core(&mut self) -> Result<Vec<String>, &'static str> {
        let response = self.exec_cmd(Command::GetUnsatCore)?;
        match response {
            GeneralResponse::SpecificSuccessResponse(res) => {
                match res {
                    SpecificSuccessResponse::GetUnsatCoreResponse(core) => {
                        let mut result = vec![];
                        for symbol in core.0 {
                            result.push(symbol.0);
                        }
                        Ok(result)
                    }
                    _ => {
                        Err("The returned response was not a unsat core response")
                    }
                }
            }
            GeneralResponse::Error(e) => {Err("Solver produced an unknown error when getting the unsat core")}
            _ => {Err("Solver: Unknown error when getting the unsat core")}
        }
    }

    fn declare_const(&mut self, sort: &TermSort, name: &String) -> Result<(), &'static str> {
        let response = self.exec_cmd(Command::DeclareConst(Symbol(name.clone()), sort.sort()))?;
        match response {
            GeneralResponse::Success => { Ok(()) }
            GeneralResponse::Error(e) => { panic!("Solver: Solver generated an error: {}", e) }
            _ => {Err("Solver: Unknown Error when declaring a const")}
        }
    }

    fn dump_script(&self) -> String {
        self.script().iter().map(|c| c.to_string()).collect::<Vec<_>>().join("\n")
    }

    fn get_model(&mut self) -> Result<Vec<ModelResponse>, &'static str> {
        let response = self.exec_cmd(Command::GetModel)?;
        match response {
            GeneralResponse::Error(_) => { Err("Solver: Solver generated an error during a check-sat") }
            GeneralResponse::SpecificSuccessResponse(res) => {
                match res {
                    SpecificSuccessResponse::GetModelResponse(m) => {
                        Ok(m.0)
                    }
                    _ => {
                        Err("Solver: Specific response didn't match model response")
                    }

                }
            }
            _ => {
                Err("Solver: Unknown Response when checking sat")
            }
        }
    }

    fn enable_unsat_cores(&mut self) -> Result<(), &'static str> {
        self.exec_cmd(Command::SetOption(ast::Option::ProduceUnsatCores(true)))?;
        //self.exec_cmd(Command::SetOption(ast::Option::Attribute(Attribute::WithValue(Keyword(String::from(":smt.core.minimize")), AttributeValue::Symbol(Symbol(String::from("true")))))))?;
        Ok(())
    }

    fn reset(&mut self) -> Result<(), &'static str> {
        let response = self.exec_cmd(Command::Reset)?;
        match response {
            GeneralResponse::Success => { Ok(()) }
            GeneralResponse::Error(_) => { Err("Solver: Solver generated an error when resetting") }
            _ => {Err("Solver: Unknown Error when resetting")}
        }
    }
}

pub trait InteractiveSolver: SolverUtils {
    fn push(&mut self, n: usize) -> Result<(), &'static str> {
        let response = self.exec_cmd(Command::Push(Numeral(n.to_string())))?;

        match response {
            GeneralResponse::Success => { Ok(()) }
            GeneralResponse::Error(_) => { Err("Solver: Solver generated an error during a push") }
            _ => {Err("Solver: Unknown Error when pushing")}
        }
    }

    fn pop(&mut self, n: usize) -> Result<(), &'static str> {
        let response = self.exec_cmd(Command::Pop(Numeral(n.to_string())))?;

        match response {
            GeneralResponse::Success => { Ok(()) }
            GeneralResponse::Error(_) => { Err("Solver: Solver generated an error during a pop") }
            _ => {Err("Solver: Unknown Error when popping")}
        }
    }
}

impl<B: Backend> SolverInternalUtils for Solver<B> {
    fn exec_cmd(&mut self, cmd: Command) -> Result<GeneralResponse, &'static str> {
        self.script.push(cmd.clone());
        fs::write(&self.output_script, self.dump_script()).map_err(|_| "Could not write to file")?;
        self.smt_solver
            .exec(&cmd)
            .map_err(|_| "Solver: Could not execute a command")
    }

    fn script(&self) -> &Vec<Command> {
        &self.script
    }
}

impl<B: Backend> SolverUtils for Solver<B> {}
impl<B: Backend> InteractiveSolver for Solver<B> {}

impl<B: Backend> Solver<B> {
    pub fn new(backend: B, output_dir: &PathBuf) -> Result<Self, &'static str> {
        let smt_solver = Driver::new(backend).map_err(|_| "Solver: Could not create an instance of solver")?;
        let script = Vec::new();
        let mut output_script = output_dir.clone();
        output_script.push("check");
        output_script.set_extension("smt2");
        Ok(Self {smt_solver, script, output_script})
    }
}

