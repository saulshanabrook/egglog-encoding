//! The `get-fresh!` mint primitive for the term/proof encoding.
//!
//! With terms and proofs encoded as relations (rather than constructors), an
//! e-node / proof-node id is no longer minted by a constructor call. Instead the
//! encoding mints a fresh id explicitly and asserts the relation row:
//!
//! ```text
//! (let fresh (@get-fresh-Math!))
//! (Add a b fresh)
//! ```
//!
//! `get-fresh!` is registered once per eq-sort (its output type), all drawing
//! from the backend's single eq-class id counter so the ids share one space.

use crate::exec_state::Internal;
use crate::*;
use egglog_backend_trait::CounterId;
use egglog_numeric_id::NumericId;

/// Deterministic name of a sort's mint primitive, e.g. `@get-fresh-Math!`.
/// Both the encoder (emitting mint sites) and the typechecker (registering the
/// primitive) compute it the same way.
pub(crate) fn get_fresh_prim_name(sort_name: &str) -> String {
    format!("@get-fresh-{sort_name}!")
}

/// Register a sort's `get-fresh!` primitive (`() -> <sort>`), minting from the
/// backend's eq-class id counter. A no-op on backends that don't expose a
/// counter (they assign ids deterministically and don't need an explicit mint).
/// Called from the eq-sort's `Sort` command in typechecking so it survives
/// re-parse of the desugared program.
pub(crate) fn register_get_fresh(eg: &mut EGraph, sort_name: &str) {
    let Some(id_counter) = eg.backend.eclass_id_counter() else {
        return;
    };
    let Some(sort) = eg.get_sort_by_name(sort_name).cloned() else {
        return;
    };
    eg.add_write_primitive(
        GetFresh {
            name: get_fresh_prim_name(sort_name),
            sort,
            id_counter,
        },
        None,
    );
}

/// `get-fresh!`: mint a fresh id of its output sort from the shared eq-class id
/// counter. Impure by design — every call returns a new id — so it is a
/// `WritePrim` (action context), never memoized.
#[derive(Clone)]
struct GetFresh {
    name: String,
    sort: ArcSort,
    id_counter: CounterId,
}

impl Primitive for GetFresh {
    fn name(&self) -> &str {
        &self.name
    }
    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        // `() -> sort`: the single signature entry is the output.
        SimpleTypeConstraint::new(&self.name, vec![self.sort.clone()], span.clone()).into_box()
    }
}

impl WritePrim for GetFresh {
    fn apply<'a, 'db>(&self, mut state: WriteState<'a, 'db>, _args: &[Value]) -> Option<Value> {
        Some(Value::from_usize(
            state.raw_exec_state().inc_counter(self.id_counter),
        ))
    }
}
