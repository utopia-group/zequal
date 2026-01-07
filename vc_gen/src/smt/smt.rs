use std::fmt::{Display, Formatter};
use itertools::Itertools;
use num_bigint_dig::BigInt;
use smtlib_lowlevel::ast::{Attribute, AttributeValue, Identifier, Index, QualIdentifier, Script, Sort, SortedVar, SpecConstant, Term};
use smtlib_lowlevel::ast::Identifier::{Indexed, Simple};
use smtlib_lowlevel::lexicon::{Keyword, Symbol};
use crate::smt::bool::{BoolTerm};
use crate::smt::error::SmtError;

/* Sorts */
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum TermSort {
    Bool,
    Int,
    Array(Box<TermSort>, Box<TermSort>),
    UninterpretedFn(Vec<TermSort>, Box<TermSort>),
    FiniteField(BigInt),
    IntFiniteField(BigInt)
}

pub enum Quantifier {
    Forall,
    Exists
}

impl TermSort {
    pub fn sort(&self) -> Sort {
        match self {
            TermSort::Bool => { SmtUtils::sort("Bool") }
            TermSort::Int => { SmtUtils::sort("Int") }
            TermSort::Array(i, v) => {
                SmtUtils::parametric_sort("Array", vec![i.sort(), v.sort()])
            }
            TermSort::FiniteField(sz) => {
                SmtUtils::indexed_sort("FiniteField", sz)
                //SmtUtils::sort("F")
            }
            TermSort::IntFiniteField(_) => { SmtUtils::sort("Int") }
            TermSort::UninterpretedFn(in_sorts, out_sort) => {
                let inputs = in_sorts.iter().map(|i| i.sort()).collect();
                let output = out_sort.sort();
                SmtUtils::parametric_sort("", vec![SmtUtils::parametric_sort("", inputs), output])
            }
        }
    }

    pub fn bool() -> Self {
        TermSort::Bool
    }

    pub fn int() -> Self {
        TermSort::Int
    }

    pub fn array(index: &TermSort, value: &TermSort) -> Self {
        TermSort::Array(Box::new(index.clone()), Box::new(value.clone()))
    }

    pub fn finite_field(size: BigInt) -> Self {
        TermSort::FiniteField(size)
    }

    pub fn int_finite_field(size: BigInt) -> Self {
        TermSort::IntFiniteField(size)
    }

    pub fn init(script: Script) -> Script {
        script
    }
}

impl Display for TermSort {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TermSort::Bool => { write!(f, "Bool") }
            TermSort::Int => { write!(f, "Int") }
            TermSort::Array(ind, val) => { write!(f, "(Array {} {})", ind, val) }
            TermSort::FiniteField(size) => { write!(f, "(FiniteField {})", size) }
            TermSort::IntFiniteField(size) => { write!(f, "(IntFiniteField {})", size) }
            TermSort::UninterpretedFn(inputs, output) => { write!(f, "({}) {}", inputs.iter().map(|i| i.to_string()).join(" "), output) }
        }
    }
}

pub(crate) trait BuildableTerm: Sized + Clone {
    fn new(sort: TermSort, term: Term) -> Result<Self, SmtError>;
}

/* Terms */
pub trait TypedTerm: Into<Term> + Clone + PartialEq + Eq {
    fn term(&self) -> &Term;
    fn term_mut(&mut self) -> &mut Term;
    fn sort(&self) -> TermSort;
}

pub trait CoreTerm: TypedTerm + BuildableTerm {
    fn label(self, label: &String) -> Result<Self, SmtError> {
        let sort = self.sort();
        let labeled = Term::Annotation(Box::new(self.into()), vec![Attribute::WithValue(Keyword(":named".to_string()), AttributeValue::Symbol(Symbol(label.clone())))]);
        Self::new(sort, labeled)
    }

    fn quantify(self, quantifier: Quantifier, vars: Vec<(String, TermSort)>) -> Result<Self, SmtError> {
        if vars.is_empty() {
            return Ok(self)
        }

        Self::new(self.sort(), SmtUtils::quantify(quantifier, vars, self.into()))
    }
    fn eq(self, other: Self) -> Result<BoolTerm, SmtError> {
        let term = SmtUtils::fn_application("=", vec![self.into(), other.into()]);
        BoolTerm::new(TermSort::Bool, term)
    }

    fn neq(self, other: Self) -> Result<BoolTerm, SmtError> {
        let term = SmtUtils::fn_application("not", vec![SmtUtils::fn_application("=", vec![self.into(), other.into()])]);
        BoolTerm::new(TermSort::Bool, term)
    }
}

pub trait StaticTypedTerm: CoreTerm {
    fn underlying_sort() -> TermSort;
    fn variable(name: &str) -> Self;
}

#[derive(Clone, Eq, Hash, PartialEq)]
pub enum NumericOp {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
    Mod,
    Negate,
    Shl,
    Shr,
    BitAnd,
    BitOr,
    BitXor,
    Complement,
    Gt,
    Gte,
    Lt,
    Lte
}

pub struct UninterpretedFunction {
    pub name: String,
    pub args: Vec<TermSort>,
    pub ret: TermSort,
    pub axioms: Vec<BoolTerm>
}

pub trait NumericTerm : StaticTypedTerm + for<'a> From<&'a BigInt> {
    fn get_numeric_op_axiom(op: &NumericOp) -> Option<UninterpretedFunction>;
    fn add(self, other: Self) -> Result<Self, SmtError> {
        Self::new(self.sort(), SmtUtils::fn_application("+", vec![self.into(), other.into()]))
    }
    fn sub(self, other: Self) -> Result<Self, SmtError> {
        Self::new(self.sort(), SmtUtils::fn_application("-", vec![self.into(), other.into()]))
    }
    fn mul(self, other: Self) -> Result<Self, SmtError> {
        Self::new(self.sort(), SmtUtils::fn_application("*", vec![self.into(), other.into()]))
    }
    fn div(self, other: Self) -> Result<Self, SmtError> {
        Self::new(self.sort(), SmtUtils::fn_application("div", vec![self.into(), other.into()]))
    }
    fn pow(self, other: Self) -> Result<Self, SmtError>;
    fn modulus(self, other: Self) -> Result<Self, SmtError> {
        Self::new(self.sort(), SmtUtils::fn_application("mod", vec![self.into(), other.into()]))
    }
    fn negate(self) -> Result<Self, SmtError> {
        Self::new(self.sort(), SmtUtils::fn_application("-", vec![self.into()]))
    }
    fn gt(self, other: Self) -> Result<BoolTerm, SmtError> {
        BoolTerm::new(TermSort::Bool, SmtUtils::fn_application(">", vec![self.into(), other.into()]))
    }
    fn gte(self, other: Self) -> Result<BoolTerm, SmtError> {
        BoolTerm::new(TermSort::Bool, SmtUtils::fn_application(">=", vec![self.into(), other.into()]))
    }
    fn lt(self, other: Self) -> Result<BoolTerm, SmtError> {
        BoolTerm::new(TermSort::Bool, SmtUtils::fn_application("<", vec![self.into(), other.into()]))
    }
    fn lte(self, other: Self) -> Result<BoolTerm, SmtError> {
        BoolTerm::new(TermSort::Bool, SmtUtils::fn_application("<=", vec![self.into(), other.into()]))
    }

    fn shr(self, other: Self) -> Result<Self, SmtError>;
    fn shl(self, other: Self) -> Result<Self, SmtError>;
    fn bit_and(self, other: Self) -> Result<Self, SmtError>;
    fn bit_or(self, other: Self) -> Result<Self, SmtError>;
    fn bit_xor(self, other: Self) -> Result<Self, SmtError>;
    fn complement(self) -> Result<Self, SmtError>;
}

/* Utils */
pub(crate) struct SmtUtils {}
impl SmtUtils {
    pub fn const_array(index_sort: Sort, val_sort: Sort, val: Term) -> Term {
        let arr_term_sort = Self::parametric_sort("Array", vec![index_sort, val_sort]);
        let const_decl = QualIdentifier::Sorted(Simple(Symbol(String::from("const"))), arr_term_sort);
        Term::Application(const_decl, vec![val])
    }
    pub fn fn_application(name: &str, args: Vec<Term>) -> Term {
        if args.is_empty() {
            Self::constant(name)
        }
        else {
            let fn_ident = QualIdentifier::Identifier(Identifier::Simple(Symbol(String::from(name))));
            Term::Application(fn_ident, args)
        }
    }

    pub fn sort(name: &str) -> Sort {
        Sort::Sort(Identifier::Simple(Symbol(String::from(name))))
    }

    pub fn parametric_sort(name: &str, nested_sorts: Vec<Sort>) -> Sort {
        Sort::Parametric(Simple(Symbol(String::from(name))), nested_sorts)
    }

    pub fn indexed_sort(name: &str, index: &BigInt) -> Sort {
        Sort::Sort(Indexed(Symbol(String::from(name)), vec![Index::Symbol(Symbol(index.to_string()))]))
    }

    pub fn constant(val: &str) -> Term {
        Term::SpecConstant(SpecConstant::String(String::from(val)))
    }

    pub fn variable(name: &str) -> Term {
        Term::Identifier(QualIdentifier::Identifier(Simple(Symbol(name.into()))))
    }

    pub fn quantify(quantifier: Quantifier, vars: Vec<(String, TermSort)>, term: Term) -> Term {
        let quantifier_vars = vars.into_iter().map(|(name, sort)| SortedVar(Symbol(name), sort.sort())).collect();
        match quantifier {
            Quantifier::Forall => { Term::Forall(quantifier_vars, Box::new(term)) }
            Quantifier::Exists => { Term::Exists(quantifier_vars, Box::new(term)) }
        }
    }
}
