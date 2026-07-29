use crate::{EGraph, Error, typechecking::TypeError};

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
