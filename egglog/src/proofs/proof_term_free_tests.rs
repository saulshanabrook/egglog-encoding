//! What the proof relations still name by term.
//!
//! A proof row that carries an eq-sort value is what forces proof extraction to
//! reconstruct user terms, and so what keeps the term relations alive. Every
//! other proof relation states its conclusion out of rule names, body indices,
//! and other proofs, and needs no term.

use crate::EGraph;

/// Containers matched and read in rule bodies, which is what mints the
/// projections, plus a `prove` so the proofs are actually extracted.
const PROGRAM: &str = r#"
    (datatype N (Z) (S N))
    (sort VN (Vec N))
    (sort MN (Map N N))
    (sort PN (Pair N N))
    (relation HasV (VN))
    (relation HasM (MN))
    (relation HasP (PN))
    (relation Got (N))
    (rule ((HasV v) (= e (vec-get v 0))) ((Got e)) :name "read-vec")
    (rule ((HasM m) (= w (map-get m (Z)))) ((Got w)) :name "read-map")
    (rule ((HasP p) (= a (pair-first p))) ((Got a)) :name "read-pair")
    (HasV (vec-of (Z) (S (Z))))
    (HasM (map-insert (map-empty) (Z) (S (Z))))
    (HasP (pair (Z) (S (Z))))
    (run 2)
    (prove (Got (S (Z))))
"#;

/// Only the fiat justifications name a term. Everything else — the rule proofs,
/// the merge justifications, the compositions, and the projection of an element
/// a rule body read out of a container — is stated over other proofs, so
/// nothing else reaches into the term relations.
#[test]
fn fiat_is_the_only_proof_relation_naming_a_term() {
    let mut egraph = EGraph::new_with_proofs();
    egraph.parse_and_run_program(None, PROGRAM).unwrap();

    let names = &egraph.proof_state.proof_names;
    let proof_sort = names.proof_datatype.clone();
    let mut naming_a_term = vec![];
    for function in egraph.functions.values() {
        let is_proof_node = function.decl.internal_term_node
            && function
                .schema
                .input
                .last()
                .is_some_and(|sort| sort.name() == proof_sort);
        if !is_proof_node || names.is_fiat(function.name()) {
            continue;
        }
        if function
            .schema
            .input
            .iter()
            .any(|sort| sort.name() != proof_sort && sort.is_eq_sort())
        {
            naming_a_term.push(function.name().to_string());
        }
    }

    assert!(
        naming_a_term.is_empty(),
        "these proof relations name a term, so proof extraction has to rebuild \
         one for them: {naming_a_term:?}"
    );
}
