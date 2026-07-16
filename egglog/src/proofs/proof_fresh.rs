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

use crate::exec_state::{Internal, RegistrySealed};
use crate::*;
use egglog_backend_trait::CounterId;
use egglog_numeric_id::NumericId;

/// Deterministic name of an FD view's `set-if-empty` primitive.
pub(crate) fn set_if_empty_prim_name(view_name: &str) -> String {
    format!("@set-if-empty-{view_name}!")
}

/// Deterministic name of an FD view's proof-column read primitive.
pub(crate) fn view_proof_prim_name(view_name: &str) -> String {
    format!("@view-proof-{view_name}")
}

/// Register an FD view's `set-if-empty` primitive and (in proof mode) its
/// proof-column reader, so the encoding can canonicalize a freshly-built term
/// to the view's canonical e-class at insertion time. `out_sorts` is the view's
/// output tuple `(eclass, proof)` (proof is `Unit` when proofs are off).
pub(crate) fn register_set_if_empty(
    eg: &mut EGraph,
    view_name: &str,
    key_sorts: Vec<ArcSort>,
    out_sorts: Vec<ArcSort>,
) {
    let eclass_sort = out_sorts[0].clone();
    eg.add_write_primitive(
        SetIfEmpty {
            name: set_if_empty_prim_name(view_name),
            view_name: view_name.to_string(),
            key_sorts: key_sorts.clone(),
            out_sorts: out_sorts.clone(),
            eclass_sort: eclass_sort.clone(),
        },
        None,
    );
    // The proof column reader is only meaningful in proof mode (2-output view).
    if out_sorts.len() >= 2 {
        eg.add_write_primitive(
            ViewProof {
                name: view_proof_prim_name(view_name),
                view_name: view_name.to_string(),
                key_sorts,
                proof_sort: out_sorts[1].clone(),
            },
            None,
        );
    }
}

/// `set-if-empty`: get-or-insert-with-default on an FD view. Looks up
/// `(view keys)`; if present returns its e-class (column 0), else inserts
/// `(keys default_eclass default_proof)` and returns `default_eclass`. This lets
/// the encoding thread canonical e-classes through term construction so the view
/// tables stay canonical (nothing to re-key at rebuild).
///
/// It reads the view (an "unsafe-seminaive" read) *and* writes, but is a
/// `WritePrim` — valid in ordinary `Write`-context actions (rule RHS and
/// top-level), not just `Full`-context `:naive`/`:unsafe-seminaive` rules. The
/// read is done directly on the exec state. A stale read is harmless: it just
/// defaults a fresh e-class that the view's congruence `:merge` later reconciles.
#[derive(Clone)]
struct SetIfEmpty {
    name: String,
    view_name: String,
    key_sorts: Vec<ArcSort>,
    out_sorts: Vec<ArcSort>,
    eclass_sort: ArcSort,
}

impl Primitive for SetIfEmpty {
    fn name(&self) -> &str {
        &self.name
    }
    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        // (keys… default_eclass default_proof) -> eclass
        let mut sig = self.key_sorts.clone();
        sig.extend(self.out_sorts.iter().cloned());
        sig.push(self.eclass_sort.clone());
        SimpleTypeConstraint::new(&self.name, sig, span.clone()).into_box()
    }
}

impl WritePrim for SetIfEmpty {
    fn apply<'a, 'db>(&self, mut state: WriteState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let n_keys = self.key_sorts.len();
        let keys = &args[..n_keys];
        let action = state.registry().lookup_table(&self.view_name)?.clone();
        if let Some(vals) = action.lookup_values(state.es(), keys) {
            // Cross-iteration dedup: reuse the committed canonical e-class and
            // skip the insert entirely, so the fresh id never enters a table.
            return Some(vals[0]);
        }
        // Empty: seed the key with the fresh row and return its e-class.
        action.insert(state.raw_exec_state(), args.to_vec().into_iter());
        Some(args[n_keys])
    }
}

/// Reads an FD view's proof column (column 1) by its key, for building the
/// `fresh = canonical` connector proof after `set-if-empty`.
///
/// Signature `(keys… fallback) -> proof`: returns the committed view proof for
/// the key, or `fallback` when the key is absent. The fallback lets the caller
/// build `Trans(term_proof, Sym(view_proof))` uniformly — when the view was just
/// seeded (empty at read time) the caller passes the term proof itself, so the
/// connector collapses to a reflexive `fresh = fresh`. A `WritePrim` (reads the
/// exec state directly) so it is valid in ordinary `Write`-context actions.
#[derive(Clone)]
struct ViewProof {
    name: String,
    view_name: String,
    key_sorts: Vec<ArcSort>,
    proof_sort: ArcSort,
}

impl Primitive for ViewProof {
    fn name(&self) -> &str {
        &self.name
    }
    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        // (keys… fallback_proof) -> proof
        let mut sig = self.key_sorts.clone();
        sig.push(self.proof_sort.clone());
        sig.push(self.proof_sort.clone());
        SimpleTypeConstraint::new(&self.name, sig, span.clone()).into_box()
    }
}

impl WritePrim for ViewProof {
    fn apply<'a, 'db>(&self, state: WriteState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let n_keys = self.key_sorts.len();
        let fallback = args[n_keys];
        let action = state.registry().lookup_table(&self.view_name)?.clone();
        Some(match action.lookup_values(state.es(), &args[..n_keys]) {
            Some(vals) => vals[1],
            None => fallback,
        })
    }
}

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
