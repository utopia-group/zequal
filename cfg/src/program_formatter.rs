use itertools::Itertools;
use program_structure::ast::{Access, AssignOp, Expression, ExpressionInfixOpcode, ExpressionPrefixOpcode, LogArgument, SignalType, Statement, TagList, VariableType};
use program_structure::ast::Expression::{Call, InfixOp, PrefixOp, InlineSwitchOp, ParallelOp, Variable, Number, AnonymousComp, ArrayInLine, Tuple, UniformArray};
use program_structure::function_data::FunctionData;
use program_structure::program_archive::ProgramArchive;
use program_structure::template_data::TemplateData;

const VERSION: &str = env!("CARGO_PKG_VERSION");

fn format_infix_opcode(op: &ExpressionInfixOpcode) -> String {
    match op {
        ExpressionInfixOpcode::Mul => String::from("*"),
        ExpressionInfixOpcode::Div => String::from("/"),
        ExpressionInfixOpcode::Add => String::from("+"),
        ExpressionInfixOpcode::Sub => String::from("-"),
        ExpressionInfixOpcode::Pow => String::from("**"),
        ExpressionInfixOpcode::IntDiv => String::from("\\"),
        ExpressionInfixOpcode::Mod => String::from("%"),
        ExpressionInfixOpcode::ShiftL => String::from("<<"),
        ExpressionInfixOpcode::ShiftR => String::from(">>"),
        ExpressionInfixOpcode::LesserEq => String::from("<="),
        ExpressionInfixOpcode::GreaterEq => String::from(">="),
        ExpressionInfixOpcode::Lesser => String::from("<"),
        ExpressionInfixOpcode::Greater => String::from(">"),
        ExpressionInfixOpcode::Eq => String::from("=="),
        ExpressionInfixOpcode::NotEq => String::from("!="),
        ExpressionInfixOpcode::BoolOr => String::from("||"),
        ExpressionInfixOpcode::BoolAnd => String::from("&&"),
        ExpressionInfixOpcode::BitOr => String::from("|"),
        ExpressionInfixOpcode::BitAnd => String::from("&"),
        ExpressionInfixOpcode::BitXor => String::from("^")
    }
}

fn format_prefix_opcode(op: &ExpressionPrefixOpcode) -> String {
    match op {
        ExpressionPrefixOpcode::Sub => String::from("-"),
        ExpressionPrefixOpcode::BoolNot => String::from("!"),
        ExpressionPrefixOpcode::Complement => String::from("~")
    }
}

fn format_access(access: &Access) -> String {
    match access {
        Access::ComponentAccess(acc) => format!(".{}", acc),
        Access::ArrayAccess(expr) => format!("[{}]", format_expr(expr))
    }
}

fn format_access_list(access: &Vec<Access>) -> String {
    access.iter().map(|x| format_access(x)).join("")
}

fn format_expr_list(list: &Vec<Expression>) -> String {
    list.iter().map(|e| format_expr(e)).join(", ")
}

pub fn format_expr(expr: &Expression) -> String {
    match expr {
        InfixOp {lhe, infix_op, rhe, .. } =>
            format!("{} {} {}", format_expr(lhe), format_infix_opcode(infix_op), format_expr(rhe)),
        PrefixOp { prefix_op, rhe, .. } =>
            format!("{}{}", format_prefix_opcode(prefix_op), format_expr(rhe)),
        InlineSwitchOp { cond, if_true, if_false, .. } =>
            format!("{} ? {} : {}", format_expr(cond), format_expr(if_true), format_expr(if_false)),
        ParallelOp { rhe, .. } =>
            format!("parallel {}", format_expr(rhe)),
        Variable { name, access, .. } =>
            format!("{}{}", name, format_access_list(access)),
        Number(_, val) =>
            format!("{}", val),
        Call { id, args, .. } =>
            format!("{}({})", id, format_expr_list(args)),
        AnonymousComp { id, is_parallel, params, signals, .. } =>
            format!("{} {}({})({})", if *is_parallel { String::from("parallel") } else { String::from("") }, id, format_expr_list(params), format_expr_list(signals)),
        ArrayInLine { values, .. } =>
            format!("[{}]", format_expr_list(values)),
        Tuple { values, .. } =>
            format!("({})", format_expr_list(values)),
        UniformArray { value, dimension, .. } => {
            format!("uniform_array({}[{}])", format_expr(value), format_expr(dimension))
        }
    }
}

fn format_tag_list(tag: &TagList) -> String {
    if tag.is_empty() {
        String::from("")
    }
    else {
        format!("{{{}}}", tag.join(", "))
    }
}

fn format_signal_type(ty: &SignalType) -> String {
    match ty {
        SignalType::Output => String::from("output"),
        SignalType::Input => String::from("input"),
        SignalType::Intermediate => String::from("")
    }
}

fn format_variable_type(ty: &VariableType) -> String {
    match ty {
        VariableType::Var => String::from("var"),
        VariableType::Signal(ty, tags) => format!("signal {} {}", format_signal_type(ty), format_tag_list(tags)),
        VariableType::Component => String::from("component"),
        VariableType::AnonymousComponent => String::from("")
    }
}

fn format_assign_op(op: &AssignOp) -> String {
    match op {
        AssignOp::AssignVar => String::from("="),
        AssignOp::AssignSignal => String::from("<--"),
        AssignOp::AssignConstraintSignal => String::from("<==")
    }
}

pub fn format_log_argument(arg: &LogArgument) -> String {
    match arg {
        LogArgument::LogStr(s) => { s.clone() }
        LogArgument::LogExp(e) => { format_expr(&e) }
    }
}

pub fn format_statement(num_levels: usize, stmt: &Statement) -> String {
    match stmt {
        Statement::IfThenElse { cond, if_case, else_case, .. } =>
            format!("{}if({}) {{\n {}\n{}}}{}",
                "  ".repeat(num_levels),
                format_expr(cond),
                format_statement(num_levels + 1, if_case),
                "  ".repeat(num_levels),
                if else_case.is_none() { String::from("") } else { format!("{}else {{\n {}\n {}}}", "  ".repeat(num_levels), format_statement(num_levels + 1,  else_case.as_ref().unwrap()), "  ".repeat(num_levels)) }
            ),
        Statement::While { stmt, .. } =>
            format!("{}while {{\n{}{}}}",
                "  ".repeat(num_levels),
                format_statement(num_levels + 1, stmt),
                "  ".repeat(num_levels)
            ),
        Statement::Return { value, .. } =>
            format!("{}return {};",
                "  ".repeat(num_levels),
                format_expr(value)
            ),
        Statement::InitializationBlock { initializations, ..} =>
            format!("{}", initializations.iter().map(|s| format_statement(num_levels, s)).join("\n")),
        Statement::Declaration { name, xtype, dimensions, .. } =>
            format!("{}{} {}{};",
                "  ".repeat(num_levels),
                format_variable_type(xtype),
                name,
                dimensions.iter().map(|d| format!("[{}]", format_expr(d))).join("")
            ),
        Statement::Substitution { access, var, op, rhe, .. } =>
            format!("{}{}{} {} {};",
                "  ".repeat(num_levels),
                var,
                format_access_list(access),
                format_assign_op(op),
                format_expr(rhe)
            ),
        Statement::MultSubstitution { lhe, op, rhe, .. } =>
            format!("{}{} {} {};",
                "  ".repeat(num_levels),
                format_expr(lhe),
                format_assign_op(op),
                format_expr(rhe)
            ),
        Statement::UnderscoreSubstitution { op, rhe, .. } =>
            format!("{}_ {} {};",
                "  ".repeat(num_levels),
                format_assign_op(op),
                format_expr(rhe)
            ),
        Statement::ConstraintEquality { lhe, rhe, .. } =>
            format!("{}{} === {};",
                "  ".repeat(num_levels),
                format_expr(lhe),
                format_expr(rhe)
            ),
        Statement::LogCall { args, .. } =>
            format!("log({})", args.iter().map(|a| format_log_argument(a)).join(", ")),
        Statement::Block { stmts, .. } =>
            stmts.iter().map(|s| format_statement(num_levels, s)).filter(|s| !s.is_empty()).join("\n") + "\n",
        Statement::Assert { arg, .. } =>
            format!("{}assert({});",
                "  ".repeat(num_levels),
                format_expr(arg)
            ),
    }
}

fn format_function(fun: &FunctionData) -> String {
    let decl = format!("function {}({}) {{",
        fun.get_name(),
        fun.get_name_of_params().join(", ")
    );

    let body = format_statement(1, fun.get_body());

    decl + &*body +  "}"
}

fn format_template(template: &TemplateData) -> String {
    let decl = format!("template {} {}({}) {{\n",
        if template.is_parallel() { String::from("parallel") } else { String::from("") },
        template.get_name(),
        template.get_name_of_params().join(", ")
    );

    let body = format_statement(1, template.get_body());

    decl + &*body + "}"
}

pub fn format_program(program: &ProgramArchive) -> String {
    let mut prog_str = format!("pragma circom {};\n\n", VERSION);

    prog_str += &*program.get_functions().iter().map(|f| format_function(f.1)).join("\n\n");

    prog_str += &*program.templates.iter().map(|t| format_template(t.1)).join("\n\n");

    if let Call { id, args, .. } = program.get_main_expression() {
        prog_str += &*format!("\n\ncomponent main {{public [{}]}} = {}({});",
                              program.public_inputs.join(", "),
                              id,
                              args.iter().map(|x| format_expr(x)).join(", ")
        );

    } else {
        unreachable!("The main expression should be a call.");
    };

    prog_str
}