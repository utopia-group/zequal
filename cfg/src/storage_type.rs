use std::collections::HashMap;
use std::fmt::Display;

use num_bigint_dig::BigInt;
use program_structure::ast;
use program_structure::ast::{Access, AssignOp, ExpressionInfixOpcode, Meta, SignalType, Statement, VariableType};
use program_structure::function_data::FunctionData;
use program_structure::program_archive::ProgramArchive;
use program_structure::template_data::TemplateData;

#[derive(Clone)]
pub enum CircomType<DimType> {
    Var { dims: Vec<Option<DimType>>, is_input: bool },
    Signal { dims: Vec<Option<DimType>>, is_input: bool, is_output: bool },
    Component { dims: Vec<Option<DimType>>, implements: String }
}

impl<DimType> CircomType<DimType> {
    pub fn is_var(&self) -> bool {
        match self {
            CircomType::Var { .. } => { true }
            _ => {false }
        }
    }

    pub fn is_signal(&self) -> bool {
        match self {
            CircomType::Signal { .. } => { true }
            _ => { false }
        }
    }

    pub fn is_component(&self) -> bool {
        match self {
            CircomType::Component { .. } => { true }
            _ => { false }
        }
    }

    pub fn dims(&self) -> &Vec<Option<DimType>> {
        match self {
            CircomType::Var { dims, .. } => {
                dims
            }
            CircomType::Signal { dims, .. } => {
                dims
            }
            CircomType::Component { dims, .. } => {
                dims
            }
        }
    }

    pub fn new_var_type(dims: Vec<Option<DimType>>, is_input: bool) -> Self {
        Self::Var { dims, is_input }
    }

    pub fn new_signal_type(dims: Vec<Option<DimType>>, is_input: bool, is_output: bool) -> Self {
        Self::Signal { dims, is_input, is_output }
    }

    pub fn new_component_type(dims: Vec<Option<DimType>>, implements: String) -> Self {
        Self::Component { dims, implements }
    }

    pub fn push_dim(&mut self, dim: Option<DimType>) {
        match self {
            CircomType::Var { dims, .. } => { dims.push(dim); }
            CircomType::Signal { dims, .. } => { dims.push(dim); }
            CircomType::Component { dims, .. } => { dims.push(dim); }
        }
    }
}

pub struct TypeInference {
    template_types: HashMap<String, HashMap<String, CircomType<ast::Expression>>>,
    function_types: HashMap<String, (CircomType<ast::Expression>, HashMap<String, CircomType<ast::Expression>>)>
}

/*
 * Note, we aren't trying to typecheck but rather to infer circom types. We therefore aren't going to perform precise checks to make sure everything
 * typechecks correctly
 */
impl TypeInference {
    pub fn get_fn_ret_type(&self, fn_name: &String) -> CircomType<ast::Expression> {
        if let Some(type_info) = self.function_types.get(fn_name) {
            type_info.0.clone()
        }
        else {
            panic!("Function {} not found", fn_name);
        }
    }

    pub fn get_template_store_type(&self, template: &String, var: &String) -> CircomType<ast::Expression> {
        self.template_types.get(template).unwrap().get(var).unwrap().clone()
    }

    fn infer_expr_types(&mut self, ast: &ProgramArchive, expr: &ast::Expression, types: &mut HashMap<String, CircomType<ast::Expression>>, check_access: bool) -> CircomType<ast::Expression> {
        match expr {
            ast::Expression::InfixOp { lhe, infix_op, rhe, .. } => {
                let lhs_type = self.infer_expr_types(ast, lhe, types, check_access);
                let _ = self.infer_expr_types(ast, rhe, types, check_access);
                match infix_op {
                    ExpressionInfixOpcode::LesserEq => { CircomType::new_var_type(vec![], false) }
                    ExpressionInfixOpcode::GreaterEq => { CircomType::new_var_type(vec![], false) }
                    ExpressionInfixOpcode::Lesser => { CircomType::new_var_type(vec![], false) }
                    ExpressionInfixOpcode::Greater => { CircomType::new_var_type(vec![], false) }
                    ExpressionInfixOpcode::Eq => { CircomType::new_var_type(vec![], false) }
                    ExpressionInfixOpcode::NotEq => { CircomType::new_var_type(vec![], false) }
                    ExpressionInfixOpcode::BoolOr => { CircomType::new_var_type(vec![], false) }
                    ExpressionInfixOpcode::BoolAnd => { CircomType::new_var_type(vec![], false) }
                    _ => { lhs_type }
                }
            }
            ast::Expression::PrefixOp { rhe, .. } => {
                let expr_type = self.infer_expr_types(ast, rhe, types, check_access);
                expr_type
            }
            ast::Expression::InlineSwitchOp { cond, if_true, if_false, .. } => {
                let _ = self.infer_expr_types(ast, cond, types, check_access);
                let if_true_type = self.infer_expr_types(ast, if_true, types, check_access);
                let _ = self.infer_expr_types(ast, if_false, types, check_access);
                if_true_type
            }
            ast::Expression::ParallelOp { rhe, .. } => {
                self.infer_expr_types(ast, rhe, types, check_access)
            }
            ast::Expression::Variable { name, access, .. } => {
                if check_access {
                    self.check_access(ast, access, types);
                }

                if let Some(mut var_type) = types.get_mut(name) {
                    let mut dim = 0;
                    for a in access {
                        match a {
                            Access::ComponentAccess(name) => {
                                match var_type {
                                    CircomType::Component { implements, .. } => {
                                        let new_access = Vec::from(&access[dim + 1..access.len()]);
                                        let accessed_var = ast::Expression::Variable {name: name.clone(), access: new_access, meta: Meta::new(0, 0)};
                                        let mut template_vars = self.template_types.get(implements).unwrap().clone();
                                        let ret_val = self.infer_expr_types(ast, &accessed_var, &mut template_vars, false);
                                        self.template_types.get_mut(implements).unwrap().insert(name.clone(), template_vars.get(name).unwrap().clone());
                                        return ret_val
                                    }
                                    _ => {
                                        panic!("accessed {} which isn't a component", name)
                                    }
                                }
                            }
                            Access::ArrayAccess(_) => {
                                if dim > var_type.dims().len() {
                                    var_type.push_dim(None);
                                }
                                dim += 1;
                            }
                        }
                    }

                    let mut remaining_type = match var_type {
                        CircomType::Var { .. } => { CircomType::new_var_type(vec![], false) }
                        CircomType::Signal { .. } => {  CircomType::new_signal_type(vec![], false, false)  }
                        CircomType::Component { implements, .. } => {  CircomType::new_component_type(vec![], implements.clone()) }
                    };

                    let var_dims = var_type.dims();
                    for i in dim..var_dims.len() {
                        remaining_type.push_dim(var_dims[i].clone())
                    }

                    remaining_type
                }
                else {
                    panic!("unknown variable type for {}", name)
                }
            }
            ast::Expression::Number(_, n) => {
                CircomType::new_var_type(vec![], false)
            }
            ast::Expression::Call { id, args, .. } => {
                if ast.contains_template(id) {
                    let mut arg_types = vec![];
                    for arg in args {
                        arg_types.push(self.infer_expr_types(ast, arg, types, check_access))
                    }

                    let template_def = ast.get_template_data(id);
                    self.infer_template_types(ast, template_def, arg_types);

                    CircomType::new_component_type(vec![], id.clone())
                }
                else if ast.contains_function(id) {
                    let mut arg_types = vec![];
                    for arg in args {
                        arg_types.push(self.infer_expr_types(ast, arg, types, check_access))
                    }

                    let fn_def = ast.get_function_data(id);
                    self.infer_function_types(ast, fn_def, arg_types)
                }
                else {
                    panic!("Unknown call identifier {}", id)
                }
            }
            ast::Expression::AnonymousComp { .. } => {
                panic!("Anonymous components not supported")
            }
            ast::Expression::ArrayInLine { values, meta } => {
                let mut arr_type = CircomType::new_var_type(vec![], false);
                for val in values {
                    let expr_type = self.infer_expr_types(ast, val, types, check_access);
                    let expr_dims = expr_type.dims();
                    if expr_dims.len() > arr_type.dims().len() {
                        for i in arr_type.dims().len()..expr_dims.len() {
                            arr_type.push_dim(expr_dims[i].clone())
                        }
                    }
                }
                arr_type.push_dim(Some(ast::Expression::Number(Meta::new(meta.start, meta.end), BigInt::from(values.len()))));
                arr_type
            }
            ast::Expression::Tuple { .. } => {
                panic!("Tuples are not supported")
            }
            ast::Expression::UniformArray { dimension, .. } => {
                return CircomType::new_var_type(vec![Some(dimension.as_ref().clone())], false)
            }
        }
    }

    fn check_access(&mut self, ast: &ProgramArchive, access_list: &Vec<Access>, types: &mut HashMap<String, CircomType<ast::Expression>>) {
        for access in access_list {
            match access {
                Access::ComponentAccess(_) => { /* skip */ }
                Access::ArrayAccess(ind) => {
                    // eventually might want to actually check the return type. For now I'm skipping that
                    let _ = self.infer_expr_types(ast, ind, types, true);
                }
            }
        }
    }

    fn infer_stmt_types(&mut self, ast: &ProgramArchive, cur_stmt: &ast::Statement, types: &mut HashMap<String, CircomType<ast::Expression>>) {
        match cur_stmt {
            ast::Statement::IfThenElse { cond, if_case, else_case, .. } => {
                self.infer_expr_types(ast, cond, types, true);
                self.infer_stmt_types(ast, if_case, types);
                if let Some(else_case_val) = else_case {
                    self.infer_stmt_types(ast, else_case_val, types);
                }
            }
            ast::Statement::While { cond, stmt, .. } => {
                self.infer_expr_types(ast, cond, types, true);
                self.infer_stmt_types(ast, stmt, types);
            }
            ast::Statement::Return { value, .. } => {
                self.infer_expr_types(ast, value, types, true);
            }
            ast::Statement::InitializationBlock { initializations, .. } => {
                for initialization in initializations {
                    self.infer_stmt_types(ast, initialization, types);
                }
            }
            ast::Statement::Declaration { xtype, name, dimensions, .. } => {
                /* declaration already done */
                for dim in dimensions {
                    let _ = self.infer_expr_types(ast, dim, types, true);
                }
            }
            ast::Statement::Substitution { var, access, rhe, meta, .. } => {
                let lhs_expr = ast::Expression::Variable { name: var.clone(), access: access.clone(), meta: meta.clone() };
                let lhs_type = self.infer_expr_types(ast, &lhs_expr, types, true);
                let rhs_type = self.infer_expr_types(ast, rhe, types, true);

                let contains_component = access.iter()
                    .any(|access|
                        match access {
                            Access::ComponentAccess(_) => { true }
                            Access::ArrayAccess(_) => { false }
                        }
                    );

                if !contains_component {
                    let var_type = types.get_mut(var).unwrap();
                    for _ in lhs_type.dims().len()..rhs_type.dims().len() {
                        var_type.push_dim(None)
                    }
                }

                self.check_access(ast, access, types);
            }
            ast::Statement::MultSubstitution { lhe, op, rhe, .. } => {
                let lhs_type = self.infer_expr_types(ast, lhe, types, true);
                let rhs_type = self.infer_expr_types(ast, rhe, types, true);
                match lhe {
                    ast::Expression::Variable { name, access, .. } => {
                        let contains_component = access.iter()
                            .any(|access|
                                match access {
                                    Access::ComponentAccess(_) => { true }
                                    Access::ArrayAccess(_) => { false }
                                }
                            );

                        if !contains_component {
                            let var_type = types.get_mut(name).unwrap();
                            for _ in lhs_type.dims().len()..rhs_type.dims().len() {
                                var_type.push_dim(None)
                            }
                        }
                    }
                    _ => { /* Skip */ }
                }
            }
            ast::Statement::UnderscoreSubstitution { rhe, .. } => {
                self.infer_expr_types(ast, rhe, types, true);
            }
            ast::Statement::ConstraintEquality { lhe, rhe, .. } => {
                self.infer_expr_types(ast, lhe, types, true);
                self.infer_expr_types(ast, rhe, types, true);
            }
            ast::Statement::LogCall { .. } => {
                /* Skip */
            }
            ast::Statement::Block { stmts, .. } => {
                for stmt in stmts {
                    self.infer_stmt_types(ast, stmt, types);
                }
            }
            ast::Statement::Assert { arg, .. } => {
                self.infer_expr_types(ast, arg, types, true);
            }
        }
    }

    fn preprocess_body(cur_stmt: &ast::Statement, types: &mut HashMap<String, CircomType<ast::Expression>>) {
        match cur_stmt {
            ast::Statement::IfThenElse { cond, if_case, else_case, .. } => {
                Self::preprocess_body(if_case, types);
                if let Some(else_case_val) = else_case {
                    Self::preprocess_body(else_case_val, types);
                }
            }
            ast::Statement::While { cond, stmt, .. } => {
                Self::preprocess_body(stmt, types);
            }
            ast::Statement::InitializationBlock { initializations, .. } => {
                for initialization in initializations {
                    Self::preprocess_body(initialization, types);
                }
            }
            ast::Statement::Declaration { xtype, name, dimensions, .. } => {
                // We can add types in general
                match xtype {
                    ast::VariableType::Var => {
                        let store_dims = dimensions.iter().map(|d| Some(d.clone())).collect();
                        types.insert(name.clone(), CircomType::new_var_type(store_dims, false));
                    }
                    ast::VariableType::Signal(sig_type, _) => {
                        let (is_input, is_output) = match sig_type {
                            SignalType::Output => { (false, true) }
                            SignalType::Input => { (true, false) }
                            SignalType::Intermediate => { (false, false) }
                        };
                        let store_dims = dimensions.iter().map(|d| Some(d.clone())).collect();
                        types.insert(name.clone(), CircomType::new_signal_type(store_dims, is_input, is_output));
                    }
                    ast::VariableType::Component => {
                        let store_dims = dimensions.iter().map(|d| Some(d.clone())).collect();
                        types.insert(name.clone(), CircomType::new_component_type(store_dims, String::new()));
                    }
                    ast::VariableType::AnonymousComponent => {
                        let store_dims = dimensions.iter().map(|d| Some(d.clone())).collect();
                        types.insert(name.clone(), CircomType::new_component_type(store_dims, String::new()));
                    }
                }
            }
            ast::Statement::Substitution { var, access, rhe, meta, op } => {
                let contains_component_access = access.iter()
                    .any(|access|
                    match access {
                        Access::ComponentAccess(_) => { true }
                        Access::ArrayAccess(_) => { false }
                    }
                    );
                if op == &AssignOp::AssignVar && !contains_component_access {
                    let var_type = types.get(var).unwrap();
                    match var_type {
                        CircomType::Component { implements, .. } => {
                            match rhe {
                                ast::Expression::Call { id, .. } => {
                                    types.insert(var.clone(), CircomType::new_component_type(var_type.dims().clone(), id.clone()));
                                }
                                _ => { panic!("Could component assigned to non-template type") }
                            }
                        }
                        _ => { /* Skip */ }
                    }
                }
            }
            ast::Statement::MultSubstitution { lhe, op, rhe, .. } => {
                match lhe {
                    ast::Expression::Variable { name, access, .. } => {
                        let contains_component_access = access.iter()
                            .any(|access|
                            match access {
                                Access::ComponentAccess(_) => { true }
                                Access::ArrayAccess(_) => { false }
                            }
                            );
                        if op == &AssignOp::AssignVar && !contains_component_access {
                            let var_type = types.get(name).unwrap();
                            match var_type {
                                CircomType::Component { implements, .. } => {
                                    match rhe {
                                        ast::Expression::Call { id, .. } => {
                                            types.insert(name.clone(), CircomType::new_component_type(var_type.dims().clone(), id.clone()));
                                        }
                                        _ => { panic!("Could component assigned to non-template type") }
                                    }
                                }
                                _ => { /* Skip */ }
                            }
                        }
                    }
                    _ => { /* Skip */ }
                }
            }
            ast::Statement::Block { stmts, .. } => {
                for stmt in stmts {
                    Self::preprocess_body(stmt, types);
                }
            }
            Statement::Return { .. } => {/* Skip */}
            Statement::UnderscoreSubstitution { .. } => {/* Skip */}
            Statement::ConstraintEquality { .. } => {/* Skip */}
            Statement::LogCall { .. } => {/* Skip */}
            Statement::Assert { .. } => {/* Skip */}
        }
    }

    // Note, there's always a return at the end of a template
    fn find_return_expr(cur_stmt: &ast::Statement) -> Option<ast::Expression> {
        match cur_stmt {
            ast::Statement::Return { value, .. } => {
                Some(value.clone())
            }
            ast::Statement::Block { stmts, .. } => {
                for stmt in stmts {
                    let stmt_ret_opt = Self::find_return_expr(stmt);
                    if let Some(stmt_ret) = stmt_ret_opt {
                        return Some(stmt_ret)
                    }
                }

                None
            }
            ast::Statement::IfThenElse { if_case, else_case, .. } => {
                let if_ret_opt = Self::find_return_expr(if_case);
                if let Some(stmt_ret) = if_ret_opt {
                    return Some(stmt_ret)
                }

                if let Some(else_case_val) = else_case {
                    Self::find_return_expr(if_case)
                }
                else {
                    None
                }
            }
            ast::Statement::While { stmt, .. } => {
                Self::find_return_expr(stmt)
            }
            _ => { None }
        }
    }

    fn infer_template_types(&mut self, ast: &ProgramArchive, ast_template: &TemplateData, template_var_types: Vec<CircomType<ast::Expression>>) {
        let (mut inferred_types, is_new) = if let Some(data) = self.template_types.get(&String::from(ast_template.get_name())) {
            (data.clone(), false)
        }
        else {
            let mut preprocessed_types = HashMap::new();
            Self::preprocess_body(ast_template.get_body(), &mut preprocessed_types);
            self.template_types.insert(ast_template.get_name().into(), preprocessed_types.clone());

            for (name, t) in &preprocessed_types {
                match t {
                    CircomType::Component { implements, .. } => {
                        if implements.is_empty() {
                            panic!("Could not determine instantiated type of component {} in template {}", name, ast_template.get_name());
                        }
                        if !ast.contains_template(implements.as_str()) {
                            panic!("Could not find template {} invoked by {}", implements, ast_template.get_name());
                        }
                        let invoked_template = ast.get_template_data(implements);
                        //when we infer types, we will overwrite these
                        let args = invoked_template.get_name_of_params().iter().map(|_| CircomType::new_var_type(vec![], true)).collect();
                        self.infer_template_types(ast, invoked_template, args)
                    }
                    _ => {/* Skip */ }
                }
            }

            (preprocessed_types, true)
        };

        let mut new_var_types = false;
        let params = ast_template.get_name_of_params();
        assert_eq!(params.len(), template_var_types.len());
        for i in 0..params.len() {
            let name = &params[i];
            let var_type = &template_var_types[i];
            if let Some(known_type) = inferred_types.get_mut(name) {
                let var_dims = var_type.dims();
                for i in known_type.dims().len()..var_dims.len() {
                    new_var_types = true;
                    known_type.push_dim(var_dims[i].clone());
                }
            } else {
                new_var_types = true;
                inferred_types.insert(name.clone(), var_type.clone());
            }
        }

        if new_var_types || is_new {
            self.infer_stmt_types(ast, ast_template.get_body(), &mut inferred_types);
            self.template_types.insert(ast_template.get_name().into(), inferred_types.clone());
        }
    }

    fn infer_function_types(&mut self, ast: &ProgramArchive, fn_def: &FunctionData, fn_arg_types: Vec<CircomType<ast::Expression>>) -> CircomType<ast::Expression> {
        let (mut inferred_types, ret_type, is_new) = if let Some((ret_type, data)) = self.function_types.get(&String::from(fn_def.get_name())) {
            (data.clone(), ret_type.clone(), false)
        }
        else {
            let mut preprocessed_types = HashMap::new();
            Self::preprocess_body(fn_def.get_body(), &mut preprocessed_types);
            (preprocessed_types, CircomType::new_var_type(vec![], false), true)
        };

        let mut new_var_types = false;
        let params = fn_def.get_name_of_params();
        assert_eq!(params.len(), params.len());
        for i in 0..params.len() {
            let name = &params[i];
            let var_type = &fn_arg_types[i];
            if let Some(known_type) = inferred_types.get_mut(name) {
                let var_dims = var_type.dims();
                for i in known_type.dims().len()..var_dims.len() {
                    new_var_types = true;
                    known_type.push_dim(var_dims[i].clone());
                }
            } else {
                new_var_types = true;
                inferred_types.insert(name.clone(), var_type.clone());
            }
        }

        if new_var_types || is_new {
            self.infer_stmt_types(ast, fn_def.get_body(), &mut inferred_types);
            let ret_expr_opt = Self::find_return_expr(fn_def.get_body());
            let new_ret_type = if let Some(ret_expr) = ret_expr_opt {
                self.infer_expr_types(ast, &ret_expr, &mut inferred_types, true)
            }
            else {
                panic!("Couldn't find return in function {}", fn_def.get_name());
            };
            self.function_types.insert(fn_def.get_name().into(), (new_ret_type.clone(), inferred_types));
            new_ret_type
        }
        else {
            ret_type
        }
    }

    pub fn infer_types(ast: &ProgramArchive) -> Self {
        let mut inference = Self { template_types: HashMap::new(), function_types: HashMap::new() };
        let main_component = ast.get_main_expression();
        match main_component {
            ast::Expression::Call { id, args, .. } => {
                let main_template = ast.get_template_data(id);
                let mut main_inputs = vec![];
                let mut types = HashMap::new();
                for arg in args {
                    let inferred = inference.infer_expr_types(ast, arg, &mut types, true);
                    main_inputs.push(CircomType::new_var_type(inferred.dims().clone(), true));
                }

                inference.infer_template_types(ast, main_template, main_inputs);
            }
            _ => {
                panic!("Cannot do the thing")
            }
        }

        inference
    }
}