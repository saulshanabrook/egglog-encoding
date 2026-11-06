//! Rigid names used by slotted variable constructors and binders.

use egglog::prelude::BaseSort;
use egglog::sort::BaseValues;
use egglog::{BaseValue, TermDag, TermId, Value};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Var(pub i64);

impl BaseValue for Var {}

#[derive(Debug)]
pub(crate) struct VarSort;

impl BaseSort for VarSort {
    type Base = Var;

    fn name(&self) -> &str {
        "Var"
    }

    fn reconstruct_termdag(&self, values: &BaseValues, value: Value, dag: &mut TermDag) -> TermId {
        dag.var(format!("${}", values.unwrap::<Var>(value).0))
    }
}
