use egglog::{CommandOutput, EGraph, Error};

const SETUP: &str = r#"
    (datatype Expr (A) (B) (Wrap Expr))
    (relation Fired (Expr))
    (ruleset chosen)
    (rule ((= root (Wrap x)))
          ((Fired x))
          :ruleset chosen
          :name "mark-wrapped")
    (let $wrapped-a (Wrap (A)))
    (let $wrapped-b (Wrap (B)))
"#;

#[test]
fn run_rule_mismatch_is_atomic_and_a_later_run_recovers() {
    let mut egraph = EGraph::default();
    egraph.parse_and_run_program(None, SETUP).unwrap();

    // Exercise the execution-error cleanup path more than once: each attempt
    // compiles a temporary specialization and must release it after the guard
    // rejects the two matches.
    for _ in 0..2 {
        let error = egraph
            .parse_and_run_program(
                None,
                r#"(run-schedule (run-rule "mark-wrapped" :expect 1))"#,
            )
            .unwrap_err();
        match error {
            Error::RunRuleMatchCountMismatch {
                rule,
                expected,
                observed,
                ..
            } => {
                assert_eq!(rule, "mark-wrapped");
                assert_eq!(expected, 1);
                assert_eq!(observed, 2);
            }
            other => panic!("expected a run-rule match-count error, got {other:?}"),
        }
    }

    egraph
        .parse_and_run_program(
            None,
            r#"
                (fail (check (Fired (A))))
                (fail (check (Fired (B))))
            "#,
        )
        .unwrap();

    let outputs = egraph
        .parse_and_run_program(
            None,
            r#"
                (run-schedule
                  (run-rule "mark-wrapped" :bind ((x (A))) :expect 1))
            "#,
        )
        .unwrap();
    let report = outputs
        .iter()
        .find_map(|output| match output {
            CommandOutput::RunSchedule(report) => Some(report),
            _ => None,
        })
        .expect("run-schedule should return its report");

    assert_eq!(report.num_matches_per_rule["mark-wrapped"], 1);
    assert!(report.ruleset_timings.contains_key("chosen"));
    assert_eq!(report.ruleset_timings.len(), 1);

    egraph
        .parse_and_run_program(
            None,
            r#"
                (check (Fired (A)))
                (fail (check (Fired (B))))
            "#,
        )
        .unwrap();
}
