use egglog::EGraph;

#[test]
fn flowlog_runs_basic_egg() {
    let backend = Box::new(egglog_experimental_flowlog::EGraph::new_interpret());
    let mut eg = EGraph::with_backend(backend).with_term_encoding();
    eg.parse_and_run_program(
        None,
        "(datatype Math (Num i64) (Add Math Math))\n(Add (Num 1) (Num 2))\n(run 1)\n(print-size Add)",
    )
    .unwrap();
}

#[test]
fn flowlog_runs_proof_mode_pair_container_side_condition() {
    let backend = Box::new(egglog_experimental_flowlog::EGraph::new_interpret());
    let mut eg = egglog_experimental::new_experimental_egraph_with_backend_and_proofs(backend);
    eg.parse_and_run_program(
        None,
        r#"
        (datatype Expr (A))
        (sort Cost (Pair Expr i64))
        (relation Seed (Expr))
        (relation Seen (Cost))

        (Seed (A))

        (rule ((Seed e)
               (= c (pair e 1)))
              ((Seen c))
              :name "pair-side-condition")

        (run 1)
        (prove (Seen (pair (A) 1)))
        "#,
    )
    .unwrap();
}

/// FlowLog has no native union-find, so it must be paired with term encoding.
/// Without it, the frontend refuses to run rather than silently drop `union`s.
#[test]
fn flowlog_without_term_encoding_errors() {
    let backend = Box::new(egglog_experimental_flowlog::EGraph::new_interpret());
    let mut eg = EGraph::with_backend(backend); // no `.with_term_encoding()`
    let err = eg
        .parse_and_run_program(None, "(datatype Math (Num i64))\n(run 1)")
        .unwrap_err();
    assert!(
        err.to_string().contains("term encoding"),
        "expected a term-encoding-required error, got: {err}"
    );
}
