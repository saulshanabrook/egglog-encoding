//! DD-specific physical values and join plans.

use egglog_ast::core::GenericAtomTerm;
use egglog_backend_trait::{FunctionId, MergeAction, MergeFn, ReadMode, RuleValue, RuleVar};
use egglog_numeric_id::NumericId;

/// Variable-width row stored in the host-side relation mirror.
pub type Row = Box<[u32]>;

pub(super) fn validate_merge(merge: &MergeFn, n_vals: usize, name: &str) {
    let (actions, result) = match merge {
        MergeFn::Block { actions, result } => (actions.as_slice(), result.as_ref()),
        result => (&[][..], result),
    };

    let mut available_slots = 0;
    for action in actions {
        match action {
            MergeAction::Set(_, arguments) => {
                for argument in arguments {
                    validate_merge_expr(argument, n_vals, name, available_slots);
                }
            }
            MergeAction::Let { slot, value } => {
                assert_eq!(
                    *slot, available_slots,
                    "merge for `{name}` declares let slot {slot}, expected {available_slots}"
                );
                validate_merge_expr(value, n_vals, name, available_slots);
                available_slots += 1;
            }
            MergeAction::Union(..) => panic!(
                "DD backend does not support native union actions inside merge blocks for `{name}`; term encoding must lower equality effects to table writes"
            ),
        }
    }

    let results = match result {
        MergeFn::Columns(columns) => columns.as_slice(),
        result => std::slice::from_ref(result),
    };
    assert_eq!(
        results.len(),
        n_vals,
        "merge for `{name}` must produce {n_vals} value column(s), got {}",
        results.len()
    );
    for result in results {
        validate_merge_expr(result, n_vals, name, available_slots);
    }
}

fn validate_merge_expr(merge: &MergeFn, n_vals: usize, name: &str, available_slots: usize) {
    match merge {
        MergeFn::OldCol(index) => assert!(
            *index < n_vals,
            "merge for `{name}` references OldCol({index}) but has only {n_vals} value columns"
        ),
        MergeFn::NewCol(index) => assert!(
            *index < n_vals,
            "merge for `{name}` references NewCol({index}) but has only {n_vals} value columns"
        ),
        MergeFn::LetVar(slot) => assert!(
            *slot < available_slots,
            "merge for `{name}` references let slot {slot} before it is bound"
        ),
        MergeFn::Primitive(_, arguments)
        | MergeFn::Function(_, arguments)
        | MergeFn::Lookup(_, arguments) => {
            for argument in arguments {
                validate_merge_expr(argument, n_vals, name, available_slots);
            }
        }
        MergeFn::Columns(_) => panic!("nested MergeFn::Columns is not supported for `{name}`"),
        MergeFn::Block { .. } => panic!("nested MergeFn::Block is not supported for `{name}`"),
        MergeFn::AssertEq | MergeFn::UnionId | MergeFn::Old | MergeFn::New | MergeFn::Const(_) => {}
    }
}

pub(super) fn visit_merge_read_dependencies(merge: &MergeFn, visit: &mut impl FnMut(FunctionId)) {
    match merge {
        MergeFn::Function(function, arguments) | MergeFn::Lookup(function, arguments) => {
            visit(*function);
            for argument in arguments {
                visit_merge_read_dependencies(argument, visit);
            }
        }
        MergeFn::Primitive(_, arguments) | MergeFn::Columns(arguments) => {
            for argument in arguments {
                visit_merge_read_dependencies(argument, visit);
            }
        }
        MergeFn::Block { actions, result } => {
            for action in actions {
                match action {
                    MergeAction::Set(_, arguments) => {
                        for argument in arguments {
                            visit_merge_read_dependencies(argument, visit);
                        }
                    }
                    MergeAction::Let { value, .. } => {
                        visit_merge_read_dependencies(value, visit);
                    }
                    MergeAction::Union(lhs, rhs) => {
                        visit_merge_read_dependencies(lhs, visit);
                        visit_merge_read_dependencies(rhs, visit);
                    }
                }
            }
            visit_merge_read_dependencies(result, visit);
        }
        MergeFn::AssertEq
        | MergeFn::UnionId
        | MergeFn::Old
        | MergeFn::New
        | MergeFn::OldCol(_)
        | MergeFn::NewCol(_)
        | MergeFn::LetVar(_)
        | MergeFn::Const(_) => {}
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
