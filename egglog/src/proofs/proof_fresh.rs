//! The term/proof encoding's mint + canonicalize primitives.
//!
//! With terms and proofs encoded as relations (rather than constructors), an
//! e-node / proof-node id is no longer minted by a constructor call. Instead the
//! encoding mints a fresh id explicitly and asserts the relation row:
//!
//! ```text
//! (let fresh (get-fresh! "Math"))
//! (Add a b fresh)
//! ```
//!
//! These primitives (`get-fresh!`, `set-if-empty`, and its proof-column reader)
//! carry only type constraints here; their runtime behavior is supplied by the
//! backend SPI ([`Backend::register_get_fresh`] / [`Backend::register_set_if_empty`]
//! / [`Backend::register_view_column_read`]) so each backend services the mint /
//! canonicalize against its own storage — db tables for the reference bridge, a
//! host-side mirror for the Differential Dataflow backend.

use crate::*;

/// Deterministic name of an FD view's `set-if-empty` primitive. The stable
/// `set-if-empty-` prefix carries no internal-symbol marker, so a name-sanitizer
/// leaves it alone; only the embedded `view_name` (a fresh internal symbol) is
/// rewritten, and it is rewritten identically here and at the view's declaration,
/// so the primitive stays resolvable when the desugared program is re-parsed.
pub(crate) fn set_if_empty_prim_name(view_name: &str) -> String {
    format!("set-if-empty-{view_name}!")
}

/// Deterministic name of an FD view's proof-column read primitive. See
/// [`set_if_empty_prim_name`] for why the prefix carries no internal marker.
pub(crate) fn view_proof_prim_name(view_name: &str) -> String {
    format!("view-proof-{view_name}")
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
            // The proof is output column 1 of the FD view `(eclass, proof)`; the
            // backend itself stays proof-agnostic (a generic view-column read).
            move |backend, _| backend.register_view_column_read(name.clone(), n_keys, 1),
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

/// Name of the single generic mint primitive. It takes the target sort as a
/// string literal — `(get-fresh! "Math")` — so one primitive serves every
/// eq-sort and the desugared program references a stable, always-registered name
/// (rather than a per-sort `@`-name a name-sanitizer would mangle on re-parse).
pub(crate) const GET_FRESH_PRIM_NAME: &str = "get-fresh!";

/// Register the generic `get-fresh!` primitive, minting from the backend's
/// id counter. Called from [`EGraph::with_backend`], so the primitive
/// is available both during encoding and when the desugared program is
/// re-parsed. A no-op on backends without an id counter (those assign ids
/// deterministically and need no mint primitive).
pub(crate) fn register_get_fresh(eg: &mut EGraph) {
    // No counter → the backend assigns ids deterministically; nothing to mint.
    if eg.backend.id_counter().is_none() {
        return;
    }
    eg.add_backend_op_primitive(GetFresh, WriteState::valid_contexts(), |backend, _| {
        backend.register_get_fresh()
    });
}

/// `get-fresh! "Sort" -> Sort`: mint a fresh id of the named eq-sort from the
/// shared id counter. Impure — every call returns a new id. The leading
/// string names the output sort (its runtime ignores the arg and just mints); the
/// mint itself is serviced by the backend.
#[derive(Clone)]
struct GetFresh;

impl Primitive for GetFresh {
    fn name(&self) -> &str {
        GET_FRESH_PRIM_NAME
    }
    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        Box::new(GetFreshTypeConstraint { span: span.clone() })
    }
}

/// `(get-fresh! "Sort") -> Sort`: the leading string literal names the output
/// eq-sort; the output is constrained to that sort.
struct GetFreshTypeConstraint {
    span: Span,
}

impl TypeConstraint for GetFreshTypeConstraint {
    fn get(
        &self,
        arguments: &[crate::core::AtomTerm],
        typeinfo: &TypeInfo,
    ) -> Vec<Box<dyn crate::constraint::Constraint<crate::core::AtomTerm, ArcSort>>> {
        // `("Sort") -> out`: two signature entries (the string arg and the output).
        let [arg, out] = arguments else {
            return vec![crate::constraint::impossible(
                crate::constraint::ImpossibleConstraint::ArityMismatch {
                    atom: crate::core::Atom {
                        span: self.span.clone(),
                        head: GET_FRESH_PRIM_NAME.to_string(),
                        args: arguments.to_vec(),
                    },
                    expected: 2,
                },
            )];
        };
        let string_sort = typeinfo.get_sort_by_name("String");
        // At real type-checking time the first arg is the sort-name string literal;
        // resolve the output eq-sort from it. At `accept`/resolution time the
        // constraint is run over placeholder literals (no real string), so fall
        // back to only requiring the first arg to be a `String` — the output sort
        // then comes from the already-resolved types.
        if let crate::core::AtomTerm::Literal(_, crate::ast::Literal::String(sort_name)) = arg
            && let Some(out_sort) = typeinfo.get_sort_by_name(sort_name)
        {
            let mut cs = vec![crate::constraint::assign(out.clone(), out_sort.clone())];
            if let Some(ss) = string_sort {
                cs.push(crate::constraint::assign(arg.clone(), ss.clone()));
            }
            return cs;
        }
        match string_sort {
            Some(ss) => vec![crate::constraint::assign(arg.clone(), ss.clone())],
            None => vec![],
        }
    }
}
