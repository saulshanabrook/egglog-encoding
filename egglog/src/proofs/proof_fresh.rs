//! The term/proof encoding's mint + canonicalize primitives.
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
//! These primitives (`get-fresh!`, `set-if-empty`, and its proof-column reader)
//! carry only type constraints here; their runtime behavior is minted by the
//! backend SPI ([`Backend::register_get_fresh`] / [`Backend::register_set_if_empty`]
//! / [`Backend::register_view_proof`]) so each backend services the mint /
//! canonicalize against its own storage — db tables for the reference bridge, a
//! host-side mirror for the Differential Dataflow backend.

use crate::*;

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
/// output tuple `(eclass, proof)` (proof is `Unit` when proofs are off). The
/// runtime entrypoint is minted by the backend so the op reads/writes the
/// backend's own view storage.
pub(crate) fn register_set_if_empty(
    eg: &mut EGraph,
    view_name: &str,
    key_sorts: Vec<ArcSort>,
    out_sorts: Vec<ArcSort>,
) {
    let n_keys = key_sorts.len();
    let out_arity = out_sorts.len();
    let set_if_empty = SetIfEmpty {
        name: set_if_empty_prim_name(view_name),
        key_sorts: key_sorts.clone(),
        out_sorts: out_sorts.clone(),
        eclass_sort: out_sorts[0].clone(),
    };
    let name = view_name.to_string();
    eg.add_backend_op_primitive(
        set_if_empty,
        WriteState::valid_contexts(),
        move |backend, _| backend.register_set_if_empty(name.clone(), n_keys, out_arity),
    );

    // The proof column reader is only meaningful in proof mode (2-output view).
    if out_sorts.len() >= 2 {
        let view_proof = ViewProof {
            name: view_proof_prim_name(view_name),
            key_sorts,
            proof_sort: out_sorts[1].clone(),
        };
        let name = view_name.to_string();
        eg.add_backend_op_primitive(
            view_proof,
            WriteState::valid_contexts(),
            move |backend, _| backend.register_view_proof(name.clone(), n_keys),
        );
    }
}

/// `set-if-empty`: get-or-insert-with-default on an FD view. Looks up
/// `(view keys)`; if present returns its e-class (column 0), else inserts
/// `(keys default_eclass default_proof)` and returns `default_eclass`. This lets
/// the encoding thread canonical e-classes through term construction so the view
/// tables stay canonical (nothing to re-key at rebuild). The lookup/insert is
/// serviced by the backend against its own view storage.
#[derive(Clone)]
struct SetIfEmpty {
    name: String,
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

/// Reads an FD view's proof column (column 1) by its key, for building the
/// `fresh = canonical` connector proof after `set-if-empty`.
///
/// Signature `(keys… fallback) -> proof`: returns the committed view proof for
/// the key, or `fallback` when the key is absent. The fallback lets the caller
/// build `Trans(term_proof, Sym(view_proof))` uniformly — when the view was just
/// seeded (empty at read time) the caller passes the term proof itself, so the
/// connector collapses to a reflexive `fresh = fresh`. Serviced by the backend
/// against its own view storage.
#[derive(Clone)]
struct ViewProof {
    name: String,
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
    // No counter → the backend assigns ids deterministically; nothing to mint.
    if eg.backend.eclass_id_counter().is_none() {
        return;
    }
    let Some(sort) = eg.get_sort_by_name(sort_name).cloned() else {
        return;
    };
    let get_fresh = GetFresh {
        name: get_fresh_prim_name(sort_name),
        sort,
    };
    eg.add_backend_op_primitive(get_fresh, WriteState::valid_contexts(), |backend, _| {
        backend.register_get_fresh()
    });
}

/// `get-fresh!`: mint a fresh id of its output sort from the shared eq-class id
/// counter. Impure by design — every call returns a new id. Carries type
/// constraints only; the mint itself is serviced by the backend.
#[derive(Clone)]
struct GetFresh {
    name: String,
    sort: ArcSort,
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
