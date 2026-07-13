//! DD-specific physical values and merge plans.

use egglog_ast::core::GenericAtomTerm;
use egglog_backend_trait::{ExternalFunctionId, FunctionId, ReadMode, RuleValue, RuleVar};
use egglog_numeric_id::NumericId;

/// Variable-width row stored in the host-side relation mirror.
pub type Row = Box<[u32]>;

/// How a function resolves a functional-dependency conflict.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MergeMode {
    Relation,
    Old,
    New,
    Min,
    Computed,
}

/// An evaluatable computed merge expression.
#[derive(Clone, Debug)]
pub enum MergeTree {
    Old,
    New,
    Const(u32),
    Prim(ExternalFunctionId, Vec<MergeTree>),
    Func(FunctionId, Vec<MergeTree>),
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
