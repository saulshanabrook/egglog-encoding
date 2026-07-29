use super::*;

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
