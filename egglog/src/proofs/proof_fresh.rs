//! The term/proof encoding's fresh-id, view-interning, and proof-row primitives.
//!
//! User terms are stored directly in source-named FD views, rather than in
//! separate term relations. In term-only mode, building a term takes a bare
//! fresh e-class and interns it through the view (`()` is the proof-off payload):
//!
//! ```text
//! (let fresh (get-fresh! "Math"))
//! (let canonical (set-if-empty-Add! a b fresh ()))
//! ```
//!
//! Proof nodes remain append-only relations. Their `mint-<Relation>!` primitive
//! mints a proof id and writes its row in one statement.
//!
//! These primitives carry only type constraints here. Their runtime entrypoints
//! operate directly on the e-graph's relational storage.

use crate::*;
use egglog_numeric_id::NumericId;

/// Deterministic name of an FD view's `set-if-empty` primitive. The stable
/// `set-if-empty-` prefix carries no internal-symbol marker, so a name-sanitizer
/// leaves it alone. Any internal-symbol marker already present in the embedded
/// `view_name` is rewritten identically here and at the view's declaration, so
/// the primitive stays resolvable when the desugared program is re-parsed.
pub(crate) fn set_if_empty_prim_name(view_name: &str) -> String {
    format!("set-if-empty-{view_name}!")
}

/// Deterministic name of an FD view's proof-column read primitive. See
/// [`set_if_empty_prim_name`] for why the prefix carries no internal marker.
pub(crate) fn view_proof_prim_name(view_name: &str) -> String {
    format!("view-proof-{view_name}")
}

/// Deterministic name of a proof-node relation's mint primitive. See
/// [`set_if_empty_prim_name`] for why the prefix carries no internal marker.
pub(crate) fn mint_prim_name(relation: &str) -> String {
    format!("mint-{relation}!")
}

/// The relation a [`mint_prim_name`] names, or `None` for any other primitive.
#[cfg(test)]
pub(crate) fn mint_prim_relation(prim: &str) -> Option<&str> {
    prim.strip_prefix("mint-")?.strip_suffix('!')
}

/// Register a proof-node relation's mint primitive. `arg_sorts` is the
/// relation's input columns up to the minted id, whose sort is `id_sort`. The
/// runtime entrypoint writes the e-graph's storage.
pub(crate) fn register_mint(
    eg: &mut EGraph,
    relation: &str,
    arg_sorts: Vec<ArcSort>,
    id_sort: ArcSort,
) {
    let n_args = arg_sorts.len();
    let mint = MintRow {
        name: mint_prim_name(relation),
        arg_sorts,
        id_sort,
    };
    let name = relation.to_string();
    eg.add_internal_primitive(mint, WriteState::valid_contexts(), move |egraph, _| {
        // A proof-node relation's one value column is `Unit`: the row says only
        // that the node exists.
        let unit = egraph.base_values().get(());
        egraph.register_mint_row(name.clone(), n_args, vec![unit])
    });
}

/// `mint-<Relation>!`: mint a fresh id of the relation's id column and assert
/// the row `(relation args… fresh)`. Impure — every call mints a new id, so the
/// row is always new.
#[derive(Clone)]
struct MintRow {
    name: String,
    arg_sorts: Vec<ArcSort>,
    id_sort: ArcSort,
}

impl Primitive for MintRow {
    fn name(&self) -> &str {
        &self.name
    }
    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        // (args…) -> id
        let mut sig = self.arg_sorts.clone();
        sig.push(self.id_sort.clone());
        SimpleTypeConstraint::new(&self.name, sig, span.clone()).into_box()
    }
}

/// Register an FD view's `set-if-empty` primitive and (in proof mode) its
/// proof-column reader, so the encoding can canonicalize a freshly-built term
/// to the view's canonical e-class at insertion time. `out_sorts` is the view's
/// output tuple `(eclass, proof)` (proof is `Unit` when proofs are off). The
/// runtime entrypoint reads and writes the view's storage.
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
    eg.add_internal_primitive(
        set_if_empty,
        WriteState::valid_contexts(),
        move |egraph, _| egraph.register_set_if_empty(name.clone(), n_keys, out_arity),
    );

    // The proof column reader is only meaningful in proof mode (2-output view).
    if out_sorts.len() >= 2 {
        let view_proof = ViewProof {
            name: view_proof_prim_name(view_name),
            key_sorts,
            proof_sort: out_sorts[1].clone(),
        };
        let name = view_name.to_string();
        eg.add_internal_primitive(
            view_proof,
            WriteState::valid_contexts(),
            // The proof is output column 1 of the FD view `(eclass, proof)`; the
            // The e-graph stays proof-agnostic (this is a generic view-column read).
            move |egraph, _| egraph.register_view_column_read(name.clone(), n_keys, 1),
        );
    }
}

/// `set-if-empty`: get-or-insert-with-default on an FD view. Looks up
/// `(view keys)`; if present returns its e-class (column 0), else inserts
/// `(keys default_eclass default_proof)` and returns `default_eclass`. This lets
/// the encoding thread canonical e-classes through term construction so the view
/// tables stay canonical (nothing to re-key at rebuild). The lookup/insert is
/// serviced directly against the view's storage.
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
/// build `Trans(own, Sym(view_proof))` uniformly — when the view was just seeded
/// (empty at read time) the caller passes its own conclusion, so the connector
/// collapses to a reflexive `fresh = fresh`.
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

/// Register the generic `get-fresh!` primitive, minting from the e-graph's id
/// counter. It is available both during encoding and when the desugared program
/// is re-parsed.
pub(crate) fn register_get_fresh(eg: &mut EGraph) {
    eg.add_internal_primitive(GetFresh, WriteState::valid_contexts(), |egraph, _| {
        let counter = egraph.id_counter();
        egraph.register_external_func(Box::new(core_relations::make_external_func(
            move |state: &mut ExecutionState, _args: &[Value]| {
                Some(Value::from_usize(state.inc_counter(counter)))
            },
        )))
    });
}

/// `get-fresh! "Sort" -> Sort`: mint a fresh id of the named eq-sort from the
/// shared id counter. Impure — every call returns a new id. The leading
/// string names the output sort (its runtime ignores the arg and just mints); the
/// mint itself uses the e-graph's shared id counter.
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
