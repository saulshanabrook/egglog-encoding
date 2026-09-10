//! What the proof relations still name by term.
//!
//! A proof row that carries an eq-sort value would force proof extraction to
//! reconstruct a user term. Every proof relation states its conclusion out of
//! rule names, positions in the program, and other proofs instead, so none of
//! them needs one.

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

/// No proof relation names a term. Rule proofs, merge justifications and
/// compositions are stated over other proofs; a body element read out of a
/// container is stated over the call that read it; and a fiat is stated over the
/// global action it came from.
#[test]
fn no_proof_relation_names_a_term() {
    let mut egraph = EGraph::new_with_proofs();
    egraph.parse_and_run_program(None, PROGRAM).unwrap();

    let names = &egraph.proof_state.proof_names;
    let proof_sort = names.proof_datatype.clone();
    let mut naming_a_term = vec![];
    for function in egraph.functions.values() {
        if !function.is_proof_node_of(&proof_sort) {
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
