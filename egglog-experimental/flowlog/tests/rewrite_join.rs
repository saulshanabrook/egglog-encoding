// Confirms that a real rewrite rule fires through the FlowLog differential-
// dataflow join in Interpret mode: without the rule body join producing a
// match and the head applying it (then congruence closing), the final
// `(check ...)` would fail.
use egglog::EGraph;

fn flowlog_egraph() -> EGraph {
    EGraph::with_backend(Box::new(
        egglog_experimental_flowlog::EGraph::new_interpret(),
    ))
    .with_term_encoding()
}

#[test]
fn commutativity_fires_through_dd_join() {
    let mut eg = flowlog_egraph();
    eg.parse_and_run_program(
        None,
        r#"
        (datatype Math (Num i64) (Add Math Math))
        (rewrite (Add a b) (Add b a))
        (let t (Add (Num 1) (Num 2)))
        (run 3)
        ; only holds if (Add a b) matched on the DD join, the head built
        ; (Add b a), and congruence unified the two:
        (check (= (Add (Num 1) (Num 2)) (Add (Num 2) (Num 1))))
        "#,
    )
    .expect("commutativity rewrite should fire and unify via the DD join");
}

#[test]
fn multi_atom_join_associativity() {
    // A two-atom body join ((Add a b) matched against the rewrite LHS decomposed
    // into view atoms) exercising a wider DD join than a single atom.
    let mut eg = flowlog_egraph();
    eg.parse_and_run_program(
        None,
        r#"
        (datatype Math (Num i64) (Add Math Math) (Mul Math Math))
        (rewrite (Mul a (Add b c)) (Add (Mul a b) (Mul a c)))
        (let e (Mul (Num 2) (Add (Num 3) (Num 4))))
        (run 3)
        (check (= (Mul (Num 2) (Add (Num 3) (Num 4)))
                  (Add (Mul (Num 2) (Num 3)) (Mul (Num 2) (Num 4)))))
        "#,
    )
    .expect("distributivity rewrite should fire via the multi-atom DD join");
}
