//! DD-specific physical values and join plans.

use egglog_ast::core::GenericAtomTerm;
use egglog_backend_trait::{
    FunctionId, MergeAction, MergeExpr, MergeProgram, ReadMode, RuleValue, RuleVar,
};
use egglog_numeric_id::NumericId;

/// Variable-width row stored in the host-side relation mirror.
pub type Row = Box<[u32]>;

pub(super) fn validate_merge(merge: &MergeProgram, n_vals: usize, name: &str) {
    let mut available_bindings = 0;
    for action in &merge.actions {
        match action {
            MergeAction::Set { arguments, .. } => {
                for argument in arguments {
                    validate_merge_expr(argument, n_vals, name, available_bindings);
                }
            }
            MergeAction::Let { binding, value } => {
                assert_eq!(
                    binding.index(),
                    available_bindings,
                    "merge for `{name}` declares let binding {}, expected {available_bindings}",
                    binding.index()
                );
                validate_merge_expr(value, n_vals, name, available_bindings);
                available_bindings += 1;
            }
            MergeAction::Union { .. } => panic!(
                "DD backend does not support native union actions inside merge blocks for `{name}`; term encoding must lower equality effects to table writes"
            ),
        }
    }

    assert_eq!(
        merge.results.len(),
        n_vals,
        "merge for `{name}` must produce {n_vals} value column(s), got {}",
        merge.results.len()
    );
    for result in &merge.results {
        validate_merge_expr(result, n_vals, name, available_bindings);
    }
}

fn validate_merge_expr(merge: &MergeExpr, n_vals: usize, name: &str, available_bindings: usize) {
    match merge {
        MergeExpr::AssertEq { column }
        | MergeExpr::UnionId { column }
        | MergeExpr::Input { column, .. } => assert!(
            column.index() < n_vals,
            "merge for `{name}` references value column {} but has only {n_vals} value columns",
            column.index()
        ),
        MergeExpr::Binding(binding) => assert!(
            binding.index() < available_bindings,
            "merge for `{name}` references let binding {} before it is bound",
            binding.index()
        ),
        MergeExpr::Primitive { arguments, .. } | MergeExpr::Function { arguments, .. } => {
            for argument in arguments {
                validate_merge_expr(argument, n_vals, name, available_bindings);
            }
        }
        MergeExpr::Const(_) => {}
    }
}

pub(super) fn visit_merge_read_dependencies(
    merge: &MergeProgram,
    visit: &mut impl FnMut(FunctionId, usize),
) {
    for action in &merge.actions {
        match action {
            MergeAction::Set { arguments, .. } => {
                for argument in arguments {
                    visit_merge_expr_read_dependencies(argument, visit);
                }
            }
            MergeAction::Let { value, .. } => visit_merge_expr_read_dependencies(value, visit),
            MergeAction::Union { left, right } => {
                visit_merge_expr_read_dependencies(left, visit);
                visit_merge_expr_read_dependencies(right, visit);
            }
        }
    }
    for result in &merge.results {
        visit_merge_expr_read_dependencies(result, visit);
    }
}

fn visit_merge_expr_read_dependencies(
    merge: &MergeExpr,
    visit: &mut impl FnMut(FunctionId, usize),
) {
    match merge {
        MergeExpr::Function {
            function,
            arguments,
        } => {
            visit(*function, arguments.len());
            for argument in arguments {
                visit_merge_expr_read_dependencies(argument, visit);
            }
        }
        MergeExpr::Primitive { arguments, .. } => {
            for argument in arguments {
                visit_merge_expr_read_dependencies(argument, visit);
            }
        }
        MergeExpr::AssertEq { .. }
        | MergeExpr::UnionId { .. }
        | MergeExpr::Input { .. }
        | MergeExpr::Binding(_)
        | MergeExpr::Const(_) => {}
    }
}

/// A physical column operand used by a DD join plan.
#[derive(Clone, Debug)]
pub enum Slot {
    Var(u32),
    Const(u32),
}

impl Slot {
    pub fn from_term(term: &GenericAtomTerm<RuleVar, RuleValue>) -> Result<Self, String> {
        match term {
            GenericAtomTerm::Var(_, variable) => Ok(Self::Var(variable.id)),
            GenericAtomTerm::Literal(_, value) => Ok(Self::Const(value.value.rep())),
            GenericAtomTerm::Global(..) => {
                Err("globals must be desugared before DD rule lowering".into())
            }
        }
    }
}

/// A distinct DD input stream for one table read view.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ReadKey {
    pub func: FunctionId,
    pub mode: ReadMode,
}
