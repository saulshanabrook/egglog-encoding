//! Read-only disequality witnesses, including storage and scope regressions.

use egglog::EGraph;
use egglog_experimental::{DisequalityEncoding, new_experimental_egraph_with_options};

#[path = "injectivity_disequality/oracle.rs"]
mod oracle;

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
fn unmarked_binary_reverse_congruence_is_cross_sort() {
    for_encodings(
        "(datatype Input (A) (B) (C))
         (datatype Output (F Input Input))
         (disequal (F (A) (B)) (F (A) (C)))",
        |graph, encoding| {
            graph
                .parse_and_run_program(None, "(check (known-disequal? (B) (C)))")
                .unwrap_or_else(|error| panic!("{encoding:?}: {error}"));
        },
    );
}

#[test]
fn reverse_congruence_matches_scalar_siblings_and_preserves_forward_opt_in() {
    for_encodings(
        r#"
        (datatype Input (Leaf i64))
        (datatype Output (U Input) (B Input Input) (T Input Input Input)
                         (M i64 bool String Input) (Other Input))
        (constructor Hidden (Input Input) Output :internal-hidden)
        (disequal (U (Leaf 0)) (U (Leaf 1)))
        (disequal (B (Leaf 2) (Leaf 99)) (B (Leaf 3) (Leaf 99)))
        (disequal (B (Leaf 99) (Leaf 4)) (B (Leaf 99) (Leaf 5)))
        (disequal (T (Leaf 6) (Leaf 99) (Leaf 99)) (T (Leaf 7) (Leaf 99) (Leaf 99)))
        (disequal (T (Leaf 99) (Leaf 8) (Leaf 99)) (T (Leaf 99) (Leaf 9) (Leaf 99)))
        (disequal (T (Leaf 99) (Leaf 99) (Leaf 10)) (T (Leaf 99) (Leaf 99) (Leaf 11)))
        (disequal (M 3 true "tag" (Leaf 12)) (M 3 true "tag" (Leaf 13)))
        (disequal (M 3 true "tag" (Leaf 14)) (M 4 true "tag" (Leaf 15)))
        (disequal (M 3 true "tag" (Leaf 16)) (M 3 false "tag" (Leaf 17)))
        (disequal (M 3 true "tag" (Leaf 18)) (M 3 true "other" (Leaf 19)))
        (disequal (B (Leaf 20) (Leaf 22)) (B (Leaf 21) (Leaf 23)))
        (B (Leaf 0) (Leaf 99)) (B (Leaf 1) (Leaf 99))
        (union (B (Leaf 30) (Leaf 31)) (B (Leaf 32) (Leaf 33)))
        (disequal (U (Leaf 40)) (Other (Leaf 41)))
        (disequal (Hidden (Leaf 42) (Leaf 99)) (Hidden (Leaf 43) (Leaf 99)))
        (disequal (T (Leaf 44) (Leaf 99) (Leaf 44)) (T (Leaf 45) (Leaf 99) (Leaf 45)))
        "#,
        |graph, encoding| {
            let rows = graph.num_tuples();
            let tables = graph.get_function_names();
            graph
                .parse_and_run_program(
                    None,
                    r#"
                    (check (known-disequal? (Leaf 0) (Leaf 1)))
                    (check (known-disequal? (Leaf 3) (Leaf 2)))
                    (check (known-disequal? (Leaf 4) (Leaf 5)))
                    (check (known-disequal? (Leaf 6) (Leaf 7)))
                    (check (known-disequal? (Leaf 8) (Leaf 9)))
                    (check (known-disequal? (Leaf 10) (Leaf 11)))
                    (check (known-disequal? (Leaf 12) (Leaf 13)))
                    (fail (check (known-disequal? (Leaf 14) (Leaf 15))))
                    (fail (check (known-disequal? (Leaf 16) (Leaf 17))))
                    (fail (check (known-disequal? (Leaf 18) (Leaf 19))))
                    (fail (check (known-disequal? (Leaf 20) (Leaf 21))))
                    (fail (check (known-disequal? (Leaf 22) (Leaf 23))))
                    (fail (check (known-disequal? (B (Leaf 0) (Leaf 99)) (B (Leaf 1) (Leaf 99)))))
                    (fail (check (= (Leaf 30) (Leaf 32))))
                    (fail (check (known-disequal? (Leaf 30) (Leaf 32))))
                    (fail (check (known-disequal? (Leaf 40) (Leaf 41))))
                    (check (known-disequal? (Leaf 42) (Leaf 43)))
                    ; The fragment requires every other position already equal;
                    ; it does not simplify repeated disjuncts from two positions.
                    (fail (check (known-disequal? (Leaf 44) (Leaf 45))))
                    "#,
                )
                .unwrap_or_else(|error| panic!("{encoding:?}: {error}"));
            assert_eq!(graph.num_tuples(), rows);
            assert_eq!(graph.get_function_names(), tables);
        },
    );
}

#[test]
fn reverse_congruence_leaves_containers_and_function_tables_outside_the_fragment() {
    for_encodings(
        "(datatype Input (Leaf i64))
         (datatype Output (Result i64))
         (sort Inputs (Vec Input))
         (constructor WithContainer (Input Inputs) Output)
         (relation O ())
         (function Custom (Input Input) Output :merge old)
         (disequal (WithContainer (Leaf 0) (vec-empty)) (WithContainer (Leaf 1) (vec-empty)))
         (set (Custom (Leaf 4) (Leaf 5)) (Result 0))
         (set (Custom (Leaf 4) (Leaf 6)) (Result 1))
         (disequal (Result 0) (Result 1))",
        |graph, encoding| {
            // Relations supply an actual non-unionable equality sort; there is
            // no surface `sort :no-union` declaration in this parser.
            let opaque = graph
                .type_info()
                .get_func_type("O")
                .unwrap()
                .output()
                .name()
                .to_owned();
            graph
                .parse_and_run_program(
                    None,
                    &format!(
                        "(constructor WithOpaque (Input {opaque}) Output)\n\
                         (disequal (WithOpaque (Leaf 2) (O)) (WithOpaque (Leaf 3) (O)))"
                    ),
                )
                .unwrap();
            let rows = graph.num_tuples();
            let tables = graph.get_function_names();
            graph
                .parse_and_run_program(
                    None,
                    "(fail (check (known-disequal? (Leaf 0) (Leaf 1))))
                     (fail (check (known-disequal? (Leaf 2) (Leaf 3))))
                     (fail (check (known-disequal? (Leaf 5) (Leaf 6))))",
                )
                .unwrap_or_else(|error| panic!("{encoding:?}: {error}"));
            assert_eq!(graph.num_tuples(), rows);
            assert_eq!(graph.get_function_names(), tables);
        },
    );
}

#[test]
fn naive_consumers_observe_late_equalities_and_parent_assertions_under_both_schedulers() {
    for extended in [false, true] {
        for encoding in [DisequalityEncoding::Nee, DisequalityEncoding::Ee] {
            let mut graph = new_experimental_egraph_with_options(extended, encoding);
            graph
                .parse_and_run_program(
                    None,
                    "(datatype Input (Leaf i64) (Wrap Input :injective))
                     (datatype Output (Pair Input Input))
                     (relation Request (Input Input))
                     (relation Found (Input Input))
                     (ruleset consume)
                     (rule ((Request left right) (known-disequal? left right))
                           ((Found left right)) :ruleset consume :naive)
                     (disequal (Pair (Leaf 0) (Leaf 1)) (Pair (Leaf 2) (Leaf 3)))
                     (union (Wrap (Leaf 0)) (Wrap (Leaf 2)))
                     (Request (Leaf 1) (Leaf 3))
                     (Pair (Leaf 4) (Leaf 5)) (Pair (Leaf 4) (Leaf 6))
                     (Request (Leaf 5) (Leaf 6))
                     (disequal (Pair (Leaf 7) (Leaf 8)) (Pair (Leaf 9) (Leaf 10)))
                     (fail (check (known-disequal? (Leaf 1) (Leaf 3))))
                     (run-schedule (saturate consume))
                     (fail (check (Found (Leaf 1) (Leaf 3))))
                     (fail (check (Found (Leaf 5) (Leaf 6))))
                     (fail (check-contradiction))
                     (fail (check (= (Leaf 0) (Leaf 2))))
                     (union (Leaf 7) (Leaf 9))
                     (check (known-disequal? (Leaf 8) (Leaf 10)))
                     (run-schedule (saturate injectivity consume))
                     (check (Found (Leaf 1) (Leaf 3)))
                     (fail (check (Found (Leaf 5) (Leaf 6))))
                     (disequal (Pair (Leaf 4) (Leaf 5)) (Pair (Leaf 4) (Leaf 6)))
                     (run-schedule (saturate consume))
                     (check (Found (Leaf 5) (Leaf 6)))
                     (fail (check-contradiction))
                     (union (Leaf 1) (Leaf 3))
                     (check-contradiction)",
                )
                .unwrap_or_else(|error| panic!("{encoding:?}, extended={extended}: {error}"));
        }
    }
}

#[test]
fn unmarked_reverse_rows_follow_subsumption_pop_and_failed_redeclaration() {
    for_encodings(
        "(datatype Input (Leaf i64))
         (datatype Output)
         (push)
         (constructor Scoped (Input Input) Output)
         (disequal (Scoped (Leaf 0) (Leaf 1)) (Scoped (Leaf 0) (Leaf 2)))
         (subsume (Scoped (Leaf 0) (Leaf 1)))
         (union (Leaf 0) (Leaf 10))
         (check (known-disequal? (Leaf 1) (Leaf 2)))
         (pop)
         (constructor Scoped (Input Input) Output)
         (Scoped (Leaf 0) (Leaf 1)) (Scoped (Leaf 0) (Leaf 2))
         (fail (check (known-disequal? (Leaf 1) (Leaf 2))))",
        |graph, encoding| {
            assert!(
                graph
                    .parse_and_run_program(
                        None,
                        "(constructor Scoped (Input Input) Output :injective)"
                    )
                    .is_err()
            );
            graph
                .parse_and_run_program(
                    None,
                    "(disequal (Leaf 1) (Leaf 2))
                     (fail (check (known-disequal? (Scoped (Leaf 0) (Leaf 1)) (Scoped (Leaf 0) (Leaf 2)))))",
                )
                .unwrap_or_else(|error| panic!("{encoding:?}: {error}"));
        },
    );
}

#[test]
fn unmarked_reverse_cycles_terminate_with_and_without_a_finite_witness() {
    for_encodings(
        "(datatype Term (A) (B) (Anchor) (Pair Term Term))
         (datatype Outside (Witness Term))
         (union (A) (Pair (A) (Anchor)))
         (union (B) (Pair (B) (Anchor)))",
        |graph, encoding| {
            let rows = graph.num_tuples();
            graph
                .parse_and_run_program(None, "(fail (check (known-disequal? (A) (B))))")
                .unwrap();
            assert_eq!(graph.num_tuples(), rows);
            graph
                .parse_and_run_program(None, "(disequal (Witness (A)) (Witness (B)))")
                .unwrap();
            let rows = graph.num_tuples();
            let tables = graph.get_function_names();
            graph
                .parse_and_run_program(None, "(check (known-disequal? (A) (B)))")
                .unwrap_or_else(|error| panic!("{encoding:?}: {error}"));
            assert_eq!(graph.num_tuples(), rows);
            assert_eq!(graph.get_function_names(), tables);
        },
    );
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
fn reverse_witnesses_are_annotation_independent_but_do_not_choose_ambiguous_children() {
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
                     (check (known-disequal? (C) (D)))
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
            "(relation O ()) (check (known-disequal? (O) (O)))",
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
