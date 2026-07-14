//! DD-specific physical values and merge plans.

use egglog_ast::core::GenericAtomTerm;
use egglog_backend_trait::{ExternalFunctionId, FunctionId, ReadMode, RuleValue, RuleVar};
use egglog_numeric_id::NumericId;

/// Variable-width row stored in the host-side relation mirror.
pub type Row = Box<[u32]>;

/// One expression node of a compiled merge program: the `egglog_bridge::MergeFn`
/// received in `FunctionConfig`, flattened by `translate_merge_program` for
/// host-side row evaluation. Variables are already resolved to physical operands
/// (value columns, `let` slots, interned constants); `AssertEq` and `UnionId` are
/// the merge policies of `:no-merge` functions and constructor tables, which have
/// no expression form.
#[derive(Clone, Debug)]
pub enum MergeExpr {
    /// Panic unless the old and new values match (`:no-merge`).
    AssertEq,
    /// Resolve the conflict by congruence (constructor tables).
    UnionId,
    /// The old value of the column being merged.
    Old,
    /// The new value of the column being merged.
    New,
    /// The old value of the `i`th output column (tuple-output merges).
    OldCol(usize),
    /// The new value of the `i`th output column (tuple-output merges).
    NewCol(usize),
    /// A `let`-bound value from the merge block, by environment slot.
    LetVar(usize),
    Const(u32),
    Primitive(ExternalFunctionId, Vec<MergeExpr>),
    /// The value of a function call; a miss is an error unless the target
    /// mints fresh ids.
    Function(FunctionId, Vec<MergeExpr>),
    /// The value of a function call, defaulting on a miss instead of erroring.
    Lookup(FunctionId, Vec<MergeExpr>),
}

impl MergeExpr {
    pub fn visit_read_dependencies(&self, visit: &mut impl FnMut(FunctionId)) {
        match self {
            Self::Function(function, arguments) | Self::Lookup(function, arguments) => {
                visit(*function);
                for argument in arguments {
                    argument.visit_read_dependencies(visit);
                }
            }
            Self::Primitive(_, arguments) => {
                for argument in arguments {
                    argument.visit_read_dependencies(visit);
                }
            }
            Self::AssertEq
            | Self::UnionId
            | Self::Old
            | Self::New
            | Self::OldCol(_)
            | Self::NewCol(_)
            | Self::LetVar(_)
            | Self::Const(_) => {}
        }
    }
}

#[derive(Clone, Debug)]
pub enum MergeActionPlan {
    Set(FunctionId, Vec<MergeExpr>),
    Let { slot: usize, value: MergeExpr },
}

impl MergeActionPlan {
    pub fn visit_read_dependencies(&self, visit: &mut impl FnMut(FunctionId)) {
        match self {
            Self::Set(_, arguments) => {
                for argument in arguments {
                    argument.visit_read_dependencies(visit);
                }
            }
            Self::Let { value, .. } => value.visit_read_dependencies(visit),
        }
    }
}

#[derive(Clone, Debug)]
pub struct MergeProgram {
    pub actions: Box<[MergeActionPlan]>,
    pub results: Box<[MergeExpr]>,
}

impl MergeProgram {
    pub fn visit_read_dependencies(&self, visit: &mut impl FnMut(FunctionId)) {
        for action in &self.actions {
            action.visit_read_dependencies(visit);
        }
        for result in &self.results {
            result.visit_read_dependencies(visit);
        }
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
