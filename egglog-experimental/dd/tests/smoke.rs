use egglog::scheduler::{Matches, Scheduler};
use egglog::EGraph;

#[derive(Clone)]
struct ChooseAllScheduler;

impl Scheduler for ChooseAllScheduler {
    fn filter_matches(&mut self, _rule: &str, _ruleset: &str, matches: &mut Matches) -> bool {
        matches.choose_all();
        true
    }
}

#[test]
fn dd_runs_basic_egg() {
    let backend = Box::new(egglog_experimental_dd::EGraph::new());
    let mut eg = EGraph::with_backend(backend).with_term_encoding();
    eg.parse_and_run_program(
        None,
        "(datatype Math (Num i64) (Add Math Math))\n(Add (Num 1) (Num 2))\n(run 1)\n(print-size Add)",
    )
    .unwrap();
}

#[test]
fn dd_runs_proof_mode_pair_container_side_condition() {
    let backend = Box::new(egglog_experimental_dd::EGraph::new());
    let mut eg = egglog_experimental::new_experimental_egraph_with_backend_and_proofs(backend);
    eg.parse_and_run_program(
        None,
        r#"
        (datatype Expr (A))
        (sort Cost (Pair Expr i64))
        (relation Seed (Expr))
        (relation Seen ())

        (Seed (A))

        (rule ((Seed e)
               (= c (pair e 1)))
              ((Seen))
              :name "pair-side-condition")

        (run 1)
        (prove (Seen))
        "#,
    )
    .unwrap();
}

/// DD has no native union-find, so it must be paired with term encoding.
/// Without it, the frontend refuses to run rather than silently drop `union`s.
#[test]
fn dd_without_term_encoding_errors() {
    let backend = Box::new(egglog_experimental_dd::EGraph::new());
    let mut eg = EGraph::with_backend(backend); // no `.with_term_encoding()`
    let err = eg
        .parse_and_run_program(None, "(datatype Math (Num i64))\n(run 1)")
        .unwrap_err();
    assert!(
        err.to_string().contains("term encoding"),
        "expected a term-encoding-required error, got: {err}"
    );
}

#[test]
fn dd_custom_scheduler_returns_a_backend_capability_error() {
    let backend = Box::new(egglog_experimental_dd::EGraph::new());
    let mut eg = EGraph::with_backend(backend).with_term_encoding();
    eg.parse_and_run_program(
        None,
        r#"
        (ruleset scheduled)
        (relation Input (i64))
        (relation Output (i64))
        (rule ((Input x)) ((Output x)) :ruleset scheduled)
        "#,
    )
    .unwrap();
    let scheduler = eg.add_scheduler(Box::new(ChooseAllScheduler));

    let error = eg
        .step_rules_with_scheduler(scheduler, "scheduled")
        .expect_err("DD cannot instantiate custom-scheduler matches through the bridge");

    assert!(
        error.to_string().contains("reference bridge backend"),
        "unexpected scheduler capability error: {error}"
    );
}
