use egglog::{CommandOutput, EGraph, Error, TypeError};

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

#[test]
fn run_rule_binding_follows_canonicalized_variable_equalities() {
    for mut egraph in [EGraph::default(), EGraph::new_with_proofs()] {
        egraph
            .parse_and_run_program(
                None,
                r#"
                (relation Pair (i64 i64))
                (relation FiredInt (i64))
                (rule ((Pair x y) (= x y))
                      ((FiredInt y))
                      :name "equal-pair")
                (Pair 1 1)
                (Pair 2 2)
                (run-schedule
                  (run-rule "equal-pair" :bind ((x 1)) :expect 1))
                (check (FiredInt 1))
                (fail (check (FiredInt 2)))
            "#,
            )
            .unwrap();
    }
}

#[test]
fn run_rule_binding_follows_functional_dependency_substitutions() {
    for mut egraph in [EGraph::default(), EGraph::new_with_proofs()] {
        egraph
            .parse_and_run_program(
                None,
                r#"
                (function Value (i64) i64 :no-merge)
                (relation FiredValue (i64))
                (rule ((= y (Value x)) (= z (Value x)))
                      ((FiredValue y))
                      :name "same-value")
                (set (Value 1) 10)
                (set (Value 2) 20)
                (run-schedule
                  (run-rule "same-value" :bind ((y 10)) :expect 1))
                (check (FiredValue 10))
                (fail (check (FiredValue 20)))
            "#,
            )
            .unwrap();
    }
}

#[test]
fn run_rule_selector_cannot_redefine_a_head_local() {
    let mut egraph = EGraph::default();
    let error = egraph
        .parse_and_run_program(
            None,
            r#"
                (relation R (i64))
                (relation S (i64))
                (relation FiredLocal (i64))
                (rule ((R y))
                      ((let z 1) (FiredLocal z))
                      :name "head-local")
                (R 10)
                (S 20)
                (run-schedule
                  (run-rule "head-local" :internal-select ((S z))))
            "#,
        )
        .unwrap_err();
    assert!(matches!(
        error,
        Error::TypeError(TypeError::AlreadyDefined(variable, _)) if variable == "z"
    ));
}
