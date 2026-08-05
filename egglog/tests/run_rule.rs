use egglog::{CommandOutput, EGraph, Error, TypeError, ast::Parser};

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

#[test]
fn run_rule_schedule_parser_display_roundtrip() {
    let source = r#"(run-rule ("step" ((x (Node 1)) (y 2))) ("other" ((z 3))))"#;
    let mut parser = Parser::default();
    let schedule = parser.get_schedule_from_string(None, source).unwrap();
    assert_eq!(schedule.to_string(), source);
}

#[test]
fn run_rule_rejects_legacy_scalar_and_options() {
    for source in [
        r#"(run-rule "step")"#,
        r#"(run-rule "step" :bind ((x 1)))"#,
        r#"(run-rule "step" :expect 1)"#,
        r#"(run-rule "step" :internal-select ((= x 1)))"#,
    ] {
        let error = Parser::default()
            .get_schedule_from_string(None, source)
            .unwrap_err();
        assert!(error.to_string().contains("expected run-rule invocation"));
    }
}

#[test]
fn run_rule_requires_a_nonempty_invocation_list() {
    let error = Parser::default()
        .get_schedule_from_string(None, "(run-rule)")
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("run-rule requires at least one rule invocation")
    );
}

#[test]
fn run_rule_requires_a_declared_globally_unique_rule() {
    let mut egraph = EGraph::default();
    let missing = egraph.parse_and_run_program(None, r#"(run-schedule (run-rule ("missing" ())))"#);
    assert!(matches!(
        missing,
        Err(Error::TypeError(TypeError::NoSuchRule(name, _))) if name == "missing"
    ));

    let duplicate = egraph.parse_and_run_program(
        None,
        r#"
            (relation R (i64))
            (ruleset left)
            (ruleset right)
            (rule ((R x)) () :ruleset left :name "same")
            (rule ((R x)) () :ruleset right :name "same")
        "#,
    );
    let Err(Error::TypeError(TypeError::DuplicateRuleName {
        name,
        first,
        duplicate,
    })) = duplicate
    else {
        panic!("expected duplicate rule name, got: {duplicate:?}")
    };
    assert_eq!(name, "same");
    assert!(first.string().contains(":ruleset left"));
    assert!(duplicate.string().contains(":ruleset right"));
}

#[test]
fn run_rule_bindings_are_known_and_closed() {
    let mut egraph = EGraph::default();
    let result = egraph.parse_and_run_program(
        None,
        r#"
            (relation R (i64))
            (rule ((R x)) () :name "r")
            (run-schedule (run-rule ("r" ((x y)))))
        "#,
    );
    assert!(matches!(
        result,
        Err(Error::TypeError(TypeError::RunRuleBindingNotClosed {
            rule,
            variable,
            ..
        })) if rule == "r" && variable == "y"
    ));

    let unknown =
        egraph.parse_and_run_program(None, r#"(run-schedule (run-rule ("r" ((missing 1)))))"#);
    assert!(matches!(
        unknown,
        Err(Error::TypeError(TypeError::UnknownRunRuleBinding {
            rule,
            variable,
            ..
        })) if rule == "r" && variable == "missing"
    ));

    let mismatch =
        egraph.parse_and_run_program(None, r#"(run-schedule (run-rule ("r" ((x "bad")))))"#);
    assert!(matches!(
        mismatch,
        Err(Error::TypeError(TypeError::Mismatch { expected, actual, .. }))
            if expected.name() == "i64" && actual.name() == "String"
    ));
}

#[test]
fn run_rule_requires_every_rule_variable_exactly_once() {
    let mut egraph = EGraph::default();
    let missing = egraph.parse_and_run_program(
        None,
        r#"
            (relation R (i64 i64))
            (rule ((R x y)) () :name "r")
            (run-schedule (run-rule ("r" ((x 1)))))
        "#,
    );
    assert!(matches!(
        missing,
        Err(Error::TypeError(TypeError::MissingRunRuleBinding {
            rule,
            variable,
            ..
        })) if rule == "r" && variable == "y"
    ));

    let duplicate = egraph.parse_and_run_program(
        None,
        r#"(run-schedule (run-rule ("r" ((x 1) (x 1) (y 2)))))"#,
    );
    assert!(matches!(
        duplicate,
        Err(Error::TypeError(TypeError::DuplicateRunRuleBinding {
            rule,
            variable,
            ..
        })) if rule == "r" && variable == "x"
    ));
}

#[test]
fn run_rule_fails_closed_for_occurrence_index_bodies() {
    let mut egraph = EGraph::default();
    egraph
        .parse_and_run_program(
            None,
            r#"
                (function edge (i64 i64) i64 :merge old)
                (index EdgeOcc edge (any 0 1 2))
                (relation trigger (i64))
                (relation SeenIndex (i64 i64 i64 i64))
                (set (edge 1 2) 3)
                (trigger 2)
                (trigger 9)
                (rule ((trigger x) (EdgeOcc x p q r))
                      ((SeenIndex x p q r))
                      :name "from-occurrence-index")
                (run 1)
                (check (SeenIndex 2 1 2 3))
                (fail (check (SeenIndex 9 1 2 3)))
            "#,
        )
        .unwrap();

    let error = egraph
        .parse_and_run_program(
            None,
            r#"
                (run-schedule
                  (run-rule
                    ("from-occurrence-index" ((x 9) (p 1) (q 2) (r 3)))))
            "#,
        )
        .expect_err("occurrence-index rule unexpectedly used grounded execution");
    assert!(
        matches!(&error, Error::BackendError(message)
            if message.contains("cannot use grounded execution")),
        "unexpected occurrence-index run-rule error: {error:?}"
    );
    egraph
        .parse_and_run_program(None, "(fail (check (SeenIndex 9 1 2 3)))")
        .unwrap();
}
