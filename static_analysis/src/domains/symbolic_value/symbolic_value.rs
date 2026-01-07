use cfg::expr::expression::Expression;

pub enum SymbolicValue {
    Signal {w: Expression, c: Expression},
    Var(Expression),
}