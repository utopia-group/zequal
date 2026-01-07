use serde::Serialize;

use crate::expr::expression::Expression;
use crate::expr::var_access::{Access, AccessList};
use crate::stmt::declaration::{SigType, VType};

#[derive(Clone, PartialEq, Eq, Serialize, Debug, Hash)]
pub struct Var {
    name: String,
    template_name: String,
    dimensions: Vec<Expression>,
    is_input: bool
}
#[derive(Clone, PartialEq, Eq, Serialize, Debug, Hash)]
pub struct Signal {
    name: String,
    template_name: String,
    dimensions: Vec<Expression>,
    is_input: bool,
    is_output: bool
}
#[derive(Clone, PartialEq, Eq, Serialize, Debug, Hash)]
pub struct Component {
    name: String,
    template_name: String,
    dimensions: Vec<Expression>,
    instance_of: String
}
#[derive(Clone, PartialEq, Eq, Serialize, Debug, Hash)]
pub enum NamedStorage {
    Variable(Var),
    Signal(Signal),
    Component(Component)
}

impl Signal {
    pub fn name(&self) -> &str { self.name.as_str() }
    pub fn declaring_template(&self) -> &str { self.template_name.as_str() }
    pub fn dims(&self) -> &Vec<Expression> { &self.dimensions }
    pub fn is_input(&self) -> bool { self.is_input }
    pub fn is_output(&self) -> bool { self.is_output }
    pub fn new(name: String, dimensions: Vec<Expression>, template_name: String, is_input: bool, is_output: bool) -> Signal {
        Signal { name, dimensions, template_name, is_input, is_output }
    }
}

impl Var {
    pub fn name(&self) -> &str { self.name.as_str() }
    pub fn declaring_template(&self) -> &str { self.template_name.as_str() }
    pub fn dims(&self) -> &Vec<Expression> { &self.dimensions }
    pub fn is_input(&self) -> bool { self.is_input }
    pub fn new(name: String, dimensions: Vec<Expression>, template_name: String, is_input: bool) -> Var {
        Var { name, dimensions, template_name, is_input }
    }
}

impl Component {
    pub fn name(&self) -> &str { self.name.as_str() }
    pub fn declaring_template(&self) -> &str { self.template_name.as_str() }
    pub fn dims(&self) -> &Vec<Expression> { &self.dimensions }
    pub fn instance_of(&self) -> &str { self.instance_of.as_str() }
    pub fn new(name: String, dimensions: Vec<Expression>, template_name: String, instance_of: String) -> Component {
        Component { name, dimensions, template_name, instance_of: instance_of }
    }

    pub fn references(&self, name: &str, access: &AccessList<Access>) -> bool {
        self.name() == name && self.dimensions.len() == access.len() &&
            access.iter().fold(true, |acc, v| acc && matches!(v, Access::Array{..}))
    }

    pub fn is_ref(&self, expr: &Expression) -> bool {
        if let Expression::Variable(v) = expr {
            return self.references(v.name(), v.access())
        }
        false
    }

    pub fn find_component_in_expr(expr: &Expression) -> Option<&AccessList<Access>> {
        match expr {
            Expression::Variable (v) =>{
                Some(v.access())
            }
            _ => { Option::None }
        }
    }

    pub fn find_component_access_in_expr<'e>(&self, expr: &'e Expression) -> Option<&'e String> {
        match expr {
            Expression::Variable(v) =>{
                v.access().get_component_access()
            }
            _ => { Option::None }
        }
    }

    /*pub fn set_component_type(&mut self, name: String) -> Result<(), CFGError> {
        if self.instance_of.is_empty() {
            self.instance_of = name;
            Ok(())
        }
        else if self.instance_of != name {
            Err(CFGError::MismatchedComponentType(self.name.clone(), self.instance_of.clone(), name))
        }
        else {
            Ok(())
        }
    }

    fn extract_template_type(expr: &Expression) -> &str {
        match expr {
            Expression::Instantiate(e) => {
                e.name()
            }
            _ => {
                unreachable!("Cannot extract template from any statement besides a call")
            }
        }
    }

    pub fn infer_type(&mut self, stmt: &AssignVar) {
        if self.references(stmt.lhs().name(), stmt.lhs().access()) {
            let new_type = Component::extract_template_type(stmt.rhs());
            if !self.instance_of.is_empty() {
                assert_eq!(new_type, self.instance_of);
            }
            else {
                self.instance_of = String::from(new_type);
            };
        }
    }*/
}

impl NamedStorage {
    pub fn new_variable(name: String, template_name: String, is_input: bool) -> NamedStorage {
        let v = Var::new(name, vec![], template_name, is_input);
        NamedStorage::Variable(v)
    }

    pub fn new_named_storage(name: String, template: String, dimensions: Vec<Expression>, v_type: VType) -> NamedStorage {
        match v_type {
            VType::Var { is_input} => {
                let v = Var::new(name, dimensions, template, is_input);
                NamedStorage::Variable(v)
            }
            VType::Sig{sig_type, ..} => {
                let (is_input, is_output) = match sig_type {
                    SigType::Output => (false, true),
                    SigType::Input => (true, false),
                    SigType::Intermediate => (false, false)
                };
                let s = Signal::new(name, dimensions, template, is_input, is_output);
                NamedStorage::Signal(s)
            }
            VType::Component(invoked) => {
                let c = Component::new(name, dimensions, template, invoked );
                NamedStorage::Component(c)
            }
        }
    }

    pub fn name(&self) -> &str {
        match self {
            NamedStorage::Variable(v) => { v.name() }
            NamedStorage::Signal(s) => { s.name() }
            NamedStorage::Component(c) => { c.name() }
        }
    }

    pub fn dims(&self) -> &Vec<Expression> {
        match self {
            NamedStorage::Variable(v) => { v.dims() }
            NamedStorage::Signal(s) => { s.dims() }
            NamedStorage::Component(c) => { c.dims() }
        }
    }
}