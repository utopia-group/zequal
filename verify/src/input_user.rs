use std::path::PathBuf;

#[derive(Clone)]
pub enum Prime {
    BN128,
    BLS12381,
    GOLDILOCKS,
    GRUMPKIN,
    PALLAS,
    VESTA,
    SECQ256R1,
    SMALL
}

pub struct Input {
    pub input_program: PathBuf,
    pub output_path: PathBuf,
    //pub field: &'static str,
    pub use_z3: bool,
    pub use_ff_theory: bool,
    pub no_static_analysis: bool,
    pub only_static_analysis: bool,
    pub dump_dot: bool,
    pub dump_json: bool,
    pub assume_safe_invocations: bool,
    pub use_uf: bool,
    pub prime: Prime,
    pub link_libraries : Vec<PathBuf>,
}

impl Input {
    pub fn new() -> Result<Input, ()> {
        let matches = input_processing::view();
        let input = input_processing::get_input(&matches)?;
        let output_path = input_processing::get_output_path(&matches)?;
        let link_libraries = input_processing::get_link_libraries(&matches);
        Result::Ok(Input {
            input_program: input,
            output_path,
            use_z3: input_processing::use_z3(&matches),
            use_ff_theory: input_processing::use_ff_theory(&matches),
            no_static_analysis: input_processing::no_static_analysis(&matches),
            only_static_analysis: input_processing::only_static_analysis(&matches),
            dump_json: input_processing::dump_json(&matches),
            dump_dot: input_processing::dump_dot(&matches),
            assume_safe_invocations: input_processing::assume_safe_invocations(&matches),
            use_uf: input_processing::use_uf(&matches),
            prime: input_processing::get_prime(&matches)?,
            link_libraries,
        })
    }

    fn build_folder(output_path: &PathBuf, filename: &str, ext: &str) -> PathBuf {
        let mut file = output_path.clone();
	    let folder_name = format!("{}_{}",filename,ext);
	    file.push(folder_name);
	    file
    }
    
    fn build_output(output_path: &PathBuf, filename: &str, ext: &str) -> PathBuf {
        let mut file = output_path.clone();
        file.push(format!("{}.{}",filename,ext));
        file
    }

    pub fn get_link_libraries(&self) -> &Vec<PathBuf> {
        &self.link_libraries
    }

    pub fn input_file(&self) -> &str {
        &self.input_program.to_str().unwrap()
    }
    pub fn use_z3(&self) -> bool {
        self.use_z3
    }
    pub fn use_ff_theory(&self) -> bool {
        self.use_ff_theory
    }
    pub fn prime(&self) -> Prime {
        self.prime.clone()
    }
}
mod input_processing {
    use std::fs;
    use ansi_term::Colour;
    use clap::{App, Arg, ArgMatches};
    use std::path::{Path, PathBuf};
    use crate::input_user::Prime;
    use crate::VERSION;

    pub fn get_input(matches: &ArgMatches) -> Result<PathBuf, ()> {
        let route = Path::new(matches.value_of("input").unwrap()).to_path_buf();
        if route.is_file() {
            Result::Ok(route)
        } else {
            let route = if route.to_str().is_some() { ": ".to_owned() + route.to_str().unwrap()} else { "".to_owned() };
            Result::Err(eprintln!("{}", Colour::Red.paint("Input file does not exist".to_owned() + &route)))
        }
    }

    pub fn get_output_path(matches: &ArgMatches) -> Result<PathBuf, ()> {
        let route = Path::new(matches.value_of("output").unwrap()).to_path_buf();
        if route.is_dir() {
            Ok(route)
        } else {
            let new_dir = fs::create_dir(route.clone());
            if let Err(e) = new_dir {
                Result::Err(eprintln!("{}", Colour::Red.paint(e.to_string())))
            }
            else {
                Ok(route)
            }
        }
    }

    pub fn use_z3(matches: &ArgMatches) -> bool {
        matches.is_present("z3")
    }

    pub fn use_ff_theory(matches: &ArgMatches) -> bool {
        matches.is_present("ff")
    }
    pub fn no_static_analysis(matches: &ArgMatches) -> bool {
        matches.is_present("no_sa")
    }
    pub fn only_static_analysis(matches: &ArgMatches) -> bool {
        matches.is_present("only_sa")
    }
    pub fn dump_dot(matches: &ArgMatches) -> bool {
        matches.is_present("dump_dot")
    }
    pub fn dump_json(matches: &ArgMatches) -> bool {
        matches.is_present("dump_json")
    }

    pub fn assume_safe_invocations(matches: &ArgMatches) -> bool {
        matches.is_present("assume_safe_invocations")
    }

    pub fn use_uf(matches: &ArgMatches) -> bool {
        matches.is_present("use_uf")
    }

    pub fn get_prime(matches: &ArgMatches) -> Result<Prime, ()> {
        
        match matches.is_present("prime"){
            true => 
               {
                   let prime_value = matches.value_of("prime").unwrap();
                   if prime_value == "bn128" {
                       Ok(Prime::BN128)
                   }
                   else if prime_value == "bls12381" {
                       Ok(Prime::BLS12381)
                   }
                   else if prime_value == "goldilocks" {
                       Ok(Prime::GOLDILOCKS)
                   }
                   else if prime_value == "grumpkin" {
                        Ok(Prime::GRUMPKIN)
                   }
                   else if prime_value == "pallas" {
                        Ok(Prime::PALLAS)
                   }
                   else if prime_value == "vesta" {
                        Ok(Prime::VESTA)
                   }
                   else if prime_value == "secq256r1" {
                        Ok(Prime::SECQ256R1)
                   }
                   else if prime_value == "small" {
                       Ok(Prime::SMALL)
                   }
                   else{
                       Err(eprintln!("{}", Colour::Red.paint("invalid prime number")))
                   }
               }
               
            false => Ok(Prime::BN128),
        }
    }

    pub fn view() -> ArgMatches<'static> {
        App::new("equivalence verifier")
            .version(VERSION)
            .author("Utopia Group")
            .about("Equivalence verifier for the circom programming language")
            .arg(
                Arg::with_name("input")
                    .multiple(false)
                    .default_value("./circuit.circom")
                    .help("Path to a circuit with a main component"),
            )
            .arg(
                Arg::with_name("z3")
                    .help("Use z3 solver instead of CVC5")
                    .long("use-z3")
                    .hidden(false)
                    .takes_value(false)
                    .display_order(2)
            )
            .arg(
                Arg::with_name("ff")
                    .help("Uses the finite field theory instead of emulating them with integers")
                    .long("use-ff-theory")
                    .hidden(false)
                    .takes_value(false)
                    .conflicts_with("z3")
                    .display_order(3)
            )
            .arg(
                Arg::with_name("no_sa")
                    .help("Don't use static analysis")
                    .long("no-static-analysis")
                    .hidden(false)
                    .takes_value(false)
                    .display_order(5)
            )
            .arg(
                Arg::with_name("only_sa")
                    .help("Only perform static analysis")
                    .long("only-static-analysis")
                    .hidden(false)
                    .takes_value(false)
                    .display_order(6)
            )
            .arg (
            Arg::with_name("dump_json")
                .short("j")
                .long("dump-json")
                .takes_value(false)
                .display_order(6)
                .help("Dump CFG in JSON format")
            )
            .arg (
                Arg::with_name("dump_dot")
                    .short("d")
                    .long("dump-dot")
                    .takes_value(false)
                    .display_order(4)
                    .help("Dump dot graph of the CFG")
            )
            .arg(
                Arg::with_name("assume_safe_invocations")
                    .help("Assume invocations are safe as long as the inputs are equivalent")
                    .long("assume-safe-invocations")
                    .hidden(false)
                    .takes_value(false)
                    .display_order(6)
            )
            .arg(
                Arg::with_name("use_uf")
                    .help("Prefer uninterpreted functions over arrays")
                    .long("use-uf")
                    .hidden(false)
                    .takes_value(false)
                    .display_order(6)
            )
            .arg (
                Arg::with_name("prime")
                    .short("prime")
                    .long("prime")
                    .takes_value(true)
                    .default_value("bn128")
                    .display_order(300)
                    .help("To choose the prime number to use to generate the circuit. Receives the name of the curve (bn128, bls12381, goldilocks, grumpkin, pallas, vesta, secq256r1)"),
            )
            .arg (
                Arg::with_name("output")
                    .short("o")
                    .long("output")
                    .takes_value(true)
                    .default_value(".")
                    .help("Path to the directory where the output will be written")
                    .display_order(1)
            )
            .get_matches()
    }

    pub fn get_link_libraries(matches: &ArgMatches) -> Vec<PathBuf> {
        let mut link_libraries = Vec::new();
        let m = matches.values_of("link_libraries");
        if let Some(paths) = m {
            for path in paths.into_iter() {
                link_libraries.push(Path::new(path).to_path_buf());
            }
        }
        link_libraries
    }
}

