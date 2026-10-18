//! End-to-end contracts shared by the native UF and bulk view maintenance.

use egglog::EGraph;

fn graphs() -> impl Iterator<Item = EGraph> {
    [1, 4, 8, 12].into_iter().flat_map(|threads| {
        [
            EGraph::new_with_term_encoding().with_num_threads(threads),
            EGraph::new_with_proofs()
                .with_proof_testing()
                .with_num_threads(threads),
        ]
    })
}

#[test]
fn multiple_sorts_columns_and_congruence_waves() {
    for mut graph in graphs() {
        graph
            .parse_and_run_program(
                None,
                r#"
                (datatype A (A0) (A1))
                (datatype B (B0) (B1))
                (datatype N (Pair A B) (Wrap N))
                (Wrap (Pair (A0) (B0)))
                (Wrap (Pair (A1) (B1)))
                (union (A0) (A1))
                (union (B0) (B1))
                (run 1)
                (check (= (Wrap (Pair (A0) (B0))) (Wrap (Pair (A1) (B1)))))
                (run 1)
                (check (= (Wrap (Pair (A0) (B0))) (Wrap (Pair (A1) (B1)))))
                "#,
            )
            .unwrap();
    }
}

#[test]
fn output_only_rewrite_does_not_run_the_custom_merge() {
    for mut graph in graphs() {
        graph
            .parse_and_run_program(
                None,
                r#"
                (datatype A (A0) (A1))
                (constructor A2 () A)
                (function value () A :merge (A2))
                (A0)
                (set (value) (A1))
                (union (A0) (A1))
                (run 1)
                (check (= (value) (A0)))
                (fail (check (= (value) (A2))))
                "#,
            )
            .unwrap();
    }
}

#[test]
fn clone_and_pop_restore_independent_maintenance_cursors() {
    for mut graph in graphs() {
        graph
            .parse_and_run_program(
                None,
                r#"
                (datatype A (A0) (A1) (A2) (Wrap A))
                (Wrap (A0))
                (Wrap (A1))
                (Wrap (A2))
                (run 1)
                "#,
            )
            .unwrap();
        let mut cloned = graph.clone();
        graph
            .parse_and_run_program(
                None,
                r#"
                (push)
                (union (A0) (A1))
                (run 1)
                (check (= (Wrap (A0)) (Wrap (A1))))
                (pop)
                (fail (check (= (Wrap (A0)) (Wrap (A1)))))
                (union (A0) (A2))
                (run 1)
                (check (= (Wrap (A0)) (Wrap (A2))))
                (fail (check (= (Wrap (A0)) (Wrap (A1)))))
                "#,
            )
            .unwrap();
        cloned
            .parse_and_run_program(
                None,
                r#"
                (fail (check (= (Wrap (A0)) (Wrap (A2)))))
                (union (A1) (A2))
                (run 1)
                (check (= (Wrap (A1)) (Wrap (A2))))
                (fail (check (= (Wrap (A0)) (Wrap (A1)))))
                "#,
            )
            .unwrap();
    }
}

#[test]
fn parallel_batches_preserve_rebuilt_proofs() {
    // More than one native chunk per view: exercise proof construction on
    // workers, including FD collisions that trigger a second congruence wave.
    for mut graph in graphs() {
        graph
            .parse_and_run_program(
                None,
                r#"
            (datatype A (A0) (A1))
            (datatype N (Item i64 A) (Wrap N))
            (relation Seed (i64))
            (ruleset populate)
            (ruleset fill)
            (Seed 0)
            (rule ((Seed i) (< i 2048))
                  ((Seed (+ (* i 2) 1)) (Seed (+ (* i 2) 2))) :ruleset populate)
            (run populate 11)
            (rule ((Seed i)) ((Wrap (Item i (A0))) (Wrap (Item i (A1)))) :ruleset fill)
            (run fill 1)
            (union (A0) (A1))
            (run 1)
            (check (= (Wrap (Item 0 (A0))) (Wrap (Item 0 (A1)))))
            (check (= (Wrap (Item 1024 (A0))) (Wrap (Item 1024 (A1)))))
            (check (= (Wrap (Item 2047 (A0))) (Wrap (Item 2047 (A1)))))
        "#,
            )
            .unwrap();
    }
}
