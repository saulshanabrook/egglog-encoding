//! Read-only disequality witnesses, including storage and scope regressions.

use egglog::EGraph;
use egglog_experimental::{DisequalityEncoding, new_experimental_egraph_with_options};

fn for_encodings(program: &str, mut verify: impl FnMut(&mut EGraph, DisequalityEncoding)) {
    for encoding in [DisequalityEncoding::Nee, DisequalityEncoding::Ee] {
        let mut graph = new_experimental_egraph_with_options(false, encoding);
        graph
            .parse_and_run_program(None, program)
            .unwrap_or_else(|error| panic!("{encoding:?}: {error}"));
        verify(&mut graph, encoding);
    }
}

#[test]
fn native_fields_supply_witnesses_without_assertion_tables_or_pair_storage() {
    for_encodings(
        "(datatype Input (A) (B))
         (datatype Output (Num i64 :injective) (Mixed Input i64 Input i64 :injective))
         (Num 1) (Num 2)
         (Mixed (A) 1 (B) 2) (Mixed (A) 9 (B) 2) (Mixed (A) 1 (B) 9)",
        |graph, encoding| {
            let rows = graph.num_tuples();
            let tables = graph.get_function_names();
            assert!(!tables.iter().any(|name| name.starts_with("@disequality")));
            graph
                .parse_and_run_program(
                    None,
                    "(check (known-disequal? (Num 1) (Num 2)))
                     (check (known-disequal? (Num 2) (Num 1)))
                     (check (known-disequal? (Mixed (A) 1 (B) 2) (Mixed (A) 9 (B) 2)))
                     (check (known-disequal? (Mixed (A) 1 (B) 2) (Mixed (A) 1 (B) 9)))
                     (fail (check (known-disequal? (Num 1) (Num 1))))
                     (fail (check (known-disequal? (A) (B))))",
                )
                .unwrap_or_else(|error| panic!("{encoding:?}: {error}"));
            assert_eq!(graph.num_tuples(), rows);
            assert_eq!(graph.get_function_names(), tables);
        },
    );
}

#[test]
fn explicit_eq_fields_propagate_at_each_position_and_respect_opt_in() {
    for_encodings(
        "(datatype Term (A) (B) (C) (Pair Term Term :injective) (Other Term Term))
         (constructor Mixed (i64 Term i64 Term) Term :injective)
         (Pair (A) (C)) (Pair (B) (C)) (Pair (C) (A)) (Pair (C) (B))
         (Other (A) (C)) (Other (B) (C))
         (Mixed 1 (A) 2 (C)) (Mixed 1 (B) 2 (C))
         (Mixed 1 (C) 2 (A)) (Mixed 1 (C) 2 (B))
         (disequal (A) (B))",
        |graph, encoding| {
            let rows = graph.num_tuples();
            graph
                .parse_and_run_program(
                    None,
                    "(check (known-disequal? (Pair (A) (C)) (Pair (B) (C))))
                     (check (known-disequal? (Pair (C) (A)) (Pair (C) (B))))
                     (check (known-disequal? (Mixed 1 (A) 2 (C)) (Mixed 1 (B) 2 (C))))
                     (check (known-disequal? (Mixed 1 (C) 2 (A)) (Mixed 1 (C) 2 (B))))
                     (fail (check (known-disequal? (Other (A) (C)) (Other (B) (C)))))
                     (fail (check (known-disequal? (Pair (A) (C)) (Pair (C) (A)))))
                     (fail (check (known-disequal? (A) (C))))",
                )
                .unwrap_or_else(|error| panic!("{encoding:?}: {error}"));
            assert_eq!(graph.num_tuples(), rows);
        },
    );
}

#[test]
fn reverse_witnesses_are_unary_only_and_cross_sort() {
    for_encodings(
        "(datatype Input (A) (B) (C) (D) (E) (G))
         (datatype Output (F Input :injective) (Pair Input Input :injective) (Other Input))
         (disequal (F (B)) (F (A)))
         (disequal (Pair (C) (E)) (Pair (D) (G)))
         (disequal (Other (C)) (Other (D)))",
        |graph, encoding| {
            let rows = graph.num_tuples();
            graph
                .parse_and_run_program(
                    None,
                    "(check (known-disequal? (A) (B)))
                     (check (known-disequal? (B) (A)))
                     (fail (check (known-disequal? (C) (D))))
                     (fail (check (known-disequal? (E) (G))))",
                )
                .unwrap_or_else(|error| panic!("{encoding:?}: {error}"));
            assert_eq!(graph.num_tuples(), rows);
        },
    );
}

#[test]
fn queries_without_marked_constructors_or_assertion_tables_remain_valid() {
    for_encodings("(datatype Term (A) (B)) (A) (B)", |graph, _| {
        graph
            .parse_and_run_program(
                None,
                "(fail (check (known-disequal? (A) (B))))
                 (disequal (A) (B))
                 (check (known-disequal? (A) (B)))
                 (check (known-disequal? (B) (A)))
                 (disequal (A) (A))
                 (check (known-disequal? (A) (A)))",
            )
            .unwrap();
    });
}

#[test]
fn recursive_search_terminates_without_growing_the_egraph() {
    for_encodings(
        "(datatype Term (A) (B) (Wrap Term :injective) (Num i64 :injective))
         (union (A) (Wrap (A))) (union (B) (Wrap (B)))",
        |graph, _| {
            let rows = graph.num_tuples();
            graph
                .parse_and_run_program(None, "(fail (check (known-disequal? (A) (B))))")
                .unwrap();
            assert_eq!(graph.num_tuples(), rows);
            // The cycle also has a finite native mismatch witness.
            graph
                .parse_and_run_program(
                    None,
                    "(union (A) (Num 1)) (union (B) (Num 2))
                     (check (known-disequal? (A) (B)))",
                )
                .unwrap();
        },
    );
    let depth = 128;
    let left = format!("{}(A){}", "(Wrap ".repeat(depth), ")".repeat(depth));
    let right = format!("{}(B){}", "(Wrap ".repeat(depth), ")".repeat(depth));
    for assertion in [
        "(disequal (A) (B))".into(),
        format!("(disequal {left} {right})"),
    ] {
        for_encodings(
            &format!(
                "(datatype Term (A) (B) (Wrap Term :injective))
                 (let left {left}) (let right {right}) {assertion}"
            ),
            |graph, _| {
                let rows = graph.num_tuples();
                graph
                    .parse_and_run_program(
                        None,
                        "(check (known-disequal? left right))
                         (check (known-disequal? (A) (B)))",
                    )
                    .unwrap();
                assert_eq!(graph.get_size("Wrap"), 2 * depth);
                assert_eq!(graph.num_tuples(), rows);
            },
        );
    }
}

#[test]
fn metadata_and_assertions_follow_pop_and_failed_declarations() {
    for_encodings("(datatype Term (A) (B))", |graph, _| {
        graph
            .parse_and_run_program(
                None,
                "(push)
                 (constructor F (Term) Term :injective)
                 (disequal (F (A)) (F (B)))
                 (check (known-disequal? (A) (B)))
                 (pop)
                 (constructor F (Term) Term)
                 (F (A)) (F (B))
                 (fail (check (known-disequal? (A) (B))))
                 (disequal (A) (B))",
            )
            .unwrap();
        assert!(
            graph
                .parse_and_run_program(None, "(constructor F (Term) Term :injective)")
                .is_err()
        );
        graph
            .parse_and_run_program(None, "(fail (check (known-disequal? (F (A)) (F (B)))))")
            .unwrap();
    });
}

#[test]
fn subsumed_rows_and_current_canonical_ids_supply_witnesses() {
    for assertion in ["(disequal a b)", "(disequal fa fb)"] {
        for_encodings(
            &format!(
                "(datatype Term (A) (B) (C) (D) (F Term :injective))
                 (let a (A)) (let b (B)) (let fa (F a)) (let fb (F b))
                 (subsume (F a)) {assertion}
                 (union a (C)) (union b (D))"
            ),
            |graph, _| {
                let rows = graph.num_tuples();
                graph
                    .parse_and_run_program(
                        None,
                        "(check (known-disequal? fa fb))
                         (check (known-disequal? (C) (D)))",
                    )
                    .unwrap();
                assert_eq!(graph.num_tuples(), rows);
            },
        );
    }
}

#[test]
fn predicate_is_usable_in_a_naive_rule_body() {
    for_encodings(
        "(datatype Term (Num i64 :injective))
         (Num 1) (Num 2)
         (relation Found (Term Term))
         (rule ((= x (Num a)) (= y (Num b)) (known-disequal? x y))
               ((Found x y)) :naive)
         (run 1)
         (check (Found (Num 1) (Num 2)))
         (fail (check (Found (Num 1) (Num 1))))",
        |_, _| {},
    );
}

#[test]
fn predicate_requires_two_values_of_the_same_eq_sort() {
    for encoding in [DisequalityEncoding::Nee, DisequalityEncoding::Ee] {
        for source in [
            "(check (known-disequal? 1 2))",
            "(datatype A (X)) (datatype B (Y)) (check (known-disequal? (X) (Y)))",
            "(datatype A (X)) (check (known-disequal? (X)))",
            "(sort Items (Vec i64)) (check (known-disequal? (vec-of 1) (vec-of 2)))",
        ] {
            assert!(
                new_experimental_egraph_with_options(false, encoding)
                    .parse_and_run_program(None, source)
                    .is_err(),
                "{encoding:?}: {source}"
            );
        }
    }
}

#[test]
fn new_query_is_rejected_by_term_and_proof_encoding() {
    for encoding in [DisequalityEncoding::Nee, DisequalityEncoding::Ee] {
        for proofs in [false, true] {
            let graph = new_experimental_egraph_with_options(false, encoding);
            let mut graph = if proofs {
                graph.with_proofs_enabled().with_proof_testing()
            } else {
                graph.with_term_encoding_enabled()
            };
            let error = graph
                .parse_and_run_program(
                    None,
                    "(datatype Term (Num i64 :injective))
                     (relation Found (Term Term))
                     (rule ((= x (Num a)) (= y (Num b)) (known-disequal? x y))
                           ((Found x y)) :naive)",
                )
                .unwrap_err();
            assert!(
                matches!(&error, egglog::Error::UnsupportedProofCommand { .. })
                    && error.to_string().contains("lacks a validator"),
                "{encoding:?}, proofs={proofs}: {error}"
            );
        }
    }
}

#[test]
fn keep_best_preserves_constructor_annotation_metadata() {
    for_encodings(
        "(datatype Term (Num i64 :injective))
         (Num 1) (Num 2)
         (keep-best \"Num\")
         (check (known-disequal? (Num 1) (Num 2)))",
        |_, _| {},
    );
}
