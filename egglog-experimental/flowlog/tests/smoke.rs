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
