use egglog::{CommandOutput, EGraph, Error};

const SETUP: &str = r#"
    (datatype Expr (A) (B) (Wrap Expr))
    (relation Fired (Expr))
    (ruleset chosen)
    (rule ((= root (Wrap x)))
          ((Fired x))
          :ruleset chosen
          :name "mark-wrapped")
    (Wrap (A))
    (Wrap (B))
    (let-check $a (A))
    (let-check $b (B))
    (let-check $wrapped-a (Wrap $a))
    (let-check $wrapped-b (Wrap $b))
"#;

#[test]
fn run_rule_requires_exactly_one_match_and_a_later_list_recovers() {
    let mut egraph = EGraph::default();
    egraph.parse_and_run_program(None, SETUP).unwrap();

    // Exercise temporary-rule cleanup after an impossible complete grounding.
    for _ in 0..2 {
        let error = egraph
            .parse_and_run_program(
                None,
                r#"
                    (run-schedule
                      (run-rule
                        ("mark-wrapped" ((root $wrapped-a) (x $b)))))
                "#,
            )
            .unwrap_err();
        assert!(
            matches!(&error, Error::BackendError(message)
                if message.contains("grounded run-rule wave")
                    && message.contains("mark-wrapped")
                    && message.contains("does not match")),
            "expected a named grounded-premise error, got {error:?}"
        );
    }

    let outputs = egraph
        .parse_and_run_program(
            None,
            r#"
                (run-schedule
                  (run-rule
                    ("mark-wrapped" ((root $wrapped-a) (x $a)))
                    ("mark-wrapped" ((root $wrapped-b) (x $b)))))
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

    assert_eq!(report.num_matches_per_rule["mark-wrapped"], 2);
    assert!(report.ruleset_timings.contains_key("chosen"));
    assert_eq!(report.ruleset_timings.len(), 1);

    egraph
        .parse_and_run_program(
            None,
            r#"
                (check (Fired $a))
                (check (Fired $b))
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
                  (run-rule ("equal-pair" ((x 1) (y 1)))))
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
                  (run-rule ("same-value" ((x 1) (y 10) (z 10)))))
                (check (FiredValue 10))
                (fail (check (FiredValue 20)))
            "#,
            )
            .unwrap();
    }
}

#[test]
fn run_rule_does_not_require_action_local_bindings() {
    let mut egraph = EGraph::default();
    egraph
        .parse_and_run_program(
            None,
            r#"
                (relation R (i64))
                (relation FiredLocal (i64))
                (rule ((R y))
                      ((let z 1) (FiredLocal z))
                      :name "head-local")
                (R 10)
                (run-schedule
                  (run-rule ("head-local" ((y 10)))))
                (check (FiredLocal 1))
            "#,
        )
        .unwrap();
}
