use std::sync::Arc;

use egglog::{
    CommandOutput, EGraph, Error, TypeError,
    ast::{Command, Schedule},
};

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
fn packed_run_rule_batch_clones_share_the_fire_tape() {
    fn packed_batch(schedule: &Schedule) -> Option<&egglog::ast::PackedRunRuleBatch> {
        match schedule {
            Schedule::RunRuleBatchPacked(_, batch) => Some(batch),
            Schedule::Sequence(_, schedules) => schedules.iter().find_map(packed_batch),
            _ => None,
        }
    }

    let commands = EGraph::default()
        .parse_program(
            None,
            r#"
                (run-schedule
                  (run-rule-batch
                    :witnesses (1 2)
                    :groups (("copy" (x)))
                    :fires ((0 0) (0 1))))
            "#,
        )
        .unwrap();
    let batch = commands
        .iter()
        .find_map(|command| match command {
            Command::RunSchedule(schedule) => packed_batch(schedule),
            _ => None,
        })
        .expect("expected one packed rule batch");
    let cloned = batch.clone();
    assert!(Arc::ptr_eq(&batch.fires, &cloned.fires));
}

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

#[test]
fn run_rule_batch_queries_every_entry_before_any_head_effect() {
    let program = r#"
        (function F (i64) i64 :merge new)
        (function G (i64) i64 :merge new)
        (relation Trigger ())
        (rule ((Trigger)) ((set (F 1) 1)) :name "write-f" :naive)
        (rule ((Trigger)) ((set (G 1) (F 1))) :name "read-f" :naive)
        (set (F 1) 0)
        (Trigger)
        (run-schedule
          (run-rule-batch
            (run-rule "write-f" :expect 1)
            (run-rule "read-f" :expect 1)))
        (check (= (F 1) 1))
        (check (= (G 1) 0))
    "#;
    EGraph::default()
        .parse_and_run_program(Some("run-rule-batch-prestate.egg".to_owned()), program)
        .unwrap();
}

#[test]
fn run_rule_batch_guard_failure_is_atomic() {
    let mut egraph = EGraph::default();
    let error = egraph
        .parse_and_run_program(
            None,
            r#"
                (relation Seed (i64))
                (relation Left (i64))
                (relation Right (i64))
                (rule ((Seed x)) ((Left x)) :name "left")
                (rule ((Seed x)) ((Right x)) :name "right")
                (Seed 1)
                (run-schedule
                  (run-rule-batch
                    (run-rule "left" :bind ((x 1)) :expect 1)
                    (run-rule "right" :bind ((x 2)) :expect 1)))
            "#,
        )
        .unwrap_err();
    assert!(matches!(
        error,
        Error::RunRuleMatchCountMismatch {
            rule,
            expected: 1,
            observed: 0,
            ..
        } if rule == "right"
    ));
    egraph
        .parse_and_run_program(
            None,
            r#"
                (fail (check (Left 1)))
                (fail (check (Right 1)))
            "#,
        )
        .unwrap();
}

#[test]
fn run_rule_batch_does_not_let_one_body_enable_another() {
    let mut egraph = EGraph::default();
    let error = egraph
        .parse_and_run_program(
            None,
            r#"
                (relation Seed (i64))
                (relation Mid (i64))
                (relation Goal (i64))
                (rule ((Seed x)) ((Mid x)) :name "seed-to-mid")
                (rule ((Mid x)) ((Goal x)) :name "mid-to-goal")
                (Seed 1)
                (run-schedule
                  (run-rule-batch
                    (run-rule "seed-to-mid" :bind ((x 1)) :expect 1)
                    (run-rule "mid-to-goal" :bind ((x 1)) :expect 1)))
            "#,
        )
        .unwrap_err();
    assert!(matches!(
        error,
        Error::RunRuleMatchCountMismatch {
            rule,
            expected: 1,
            observed: 0,
            ..
        } if rule == "mid-to-goal"
    ));
    egraph
        .parse_and_run_program(
            None,
            r#"
                (fail (check (Mid 1)))
                (fail (check (Goal 1)))
            "#,
        )
        .unwrap();
}

#[test]
fn run_rule_batch_uses_one_delete_insert_commit_boundary() {
    EGraph::default()
        .parse_and_run_program(
            None,
            r#"
                (function F (i64) i64 :no-merge)
                (relation Trigger ())
                (rule ((Trigger)) ((delete (F 1))) :name "delete-f")
                (rule ((Trigger)) ((set (F 1) 2)) :name "insert-f")
                (set (F 1) 0)
                (Trigger)
                (run-schedule
                  (run-rule-batch
                    (run-rule "insert-f" :expect 1)
                    (run-rule "delete-f" :expect 1)))
                (check (= (F 1) 2))
            "#,
        )
        .unwrap();
}

#[test]
fn run_rule_batch_queries_live_rows_before_same_wave_subsume() {
    EGraph::default()
        .parse_and_run_program(
            None,
            r#"
                (relation R (i64))
                (relation Seen (i64))
                (relation Trigger ())
                (rule ((Trigger)) ((subsume (R 1))) :name "subsume-r")
                (rule ((Trigger) (R x)) ((Seen x)) :name "read-r")
                (R 1)
                (Trigger)
                (run-schedule
                  (run-rule-batch
                    (run-rule "subsume-r" :expect 1)
                    (run-rule "read-r" :bind ((x 1)) :expect 1)))
                (check (Seen 1))
                (run-schedule
                  (run-rule "read-r" :bind ((x 1)) :expect 0))
            "#,
        )
        .unwrap();
}

#[test]
fn run_rule_batch_preserves_source_rule_proofs() {
    let program = r#"
        (relation Seed (i64))
        (relation Left (i64))
        (relation Right (i64))
        (rule ((Seed x)) ((Left x)) :name "left")
        (rule ((Seed x)) ((Right x)) :name "right")
        (Seed 1)
        (run-schedule
          (run-rule-batch
            (run-rule "left" :bind ((x 1)) :expect 1)
            (run-rule "right" :bind ((x 1)) :expect 1)))
        (check (Left 1))
        (check (Right 1))
    "#;
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(Some("run-rule-batch-proofs.egg".to_owned()), program)
        .unwrap();
}

#[test]
fn run_rule_batch_requires_an_exact_guard_per_entry() {
    let error = EGraph::default()
        .parse_and_run_program(
            None,
            r#"
                (relation Seed (i64))
                (relation Out (i64))
                (rule ((Seed x)) ((Out x)) :name "copy")
                (run-schedule
                  (run-rule-batch
                    (run-rule "copy")))
            "#,
        )
        .unwrap_err();
    assert!(matches!(
        error,
        Error::TypeError(TypeError::RunRuleBatchRequiresExpectOne { rule, .. })
            if rule == "copy"
    ));
}

#[test]
fn packed_run_rule_batch_replays_multiple_groundings_of_one_rule() {
    EGraph::default()
        .parse_and_run_program(
            None,
            r#"
                (relation Seed (i64))
                (relation Out (i64))
                (rule ((Seed x)) ((Out x)) :name "copy")
                (Seed 1)
                (Seed 2)
                (run-schedule
                  (run-rule-batch
                    :witnesses (1 2)
                    :groups (("copy" (x)))
                    :fires ((0 0) (0 1))))
                (check (Out 1))
                (check (Out 2))
            "#,
        )
        .unwrap();
}

#[test]
fn packed_run_rule_batch_partial_key_recovers_complete_head_bindings_strictly() {
    let program = r#"
        (relation Seed (i64 i64))
        (relation Out (i64 i64))
        (rule ((Seed x y)) ((Out x y)) :name "copy")
        (Seed 1 9)
        (Seed 2 9)
        (run-schedule
          (run-rule-batch
            :witnesses (1 2)
            :groups (("copy" (x)))
            :fires ((0 0) (0 1))))
        (check (Out 1 9))
        (check (Out 2 9))
    "#;
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(Some("packed-partial-head.egg".to_owned()), program)
            .unwrap();
    }
}

#[test]
fn packed_run_rule_batch_zero_key_recovers_one_complete_grounding_strictly() {
    let program = r#"
        (relation Seed (i64 i64))
        (relation Out (i64 i64))
        (rule ((Seed x y)) ((Out x y)) :name "copy")
        (Seed 1 10)
        (run-schedule
          (run-rule-batch
            :witnesses ()
            :groups (("copy" ()))
            :fires ((0))))
        (check (Out 1 10))
    "#;
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(Some("packed-zero-key.egg".to_owned()), program)
            .unwrap();
    }
}

#[test]
fn packed_run_rule_batch_partial_key_recovers_query_lookup_bindings_strictly() {
    let program = r#"
        (function F (i64) i64 :no-merge)
        (relation Seed (i64 i64))
        (relation Out (i64 i64))
        (rule ((Seed x y) (= value (F y)))
              ((Out x value))
              :name "copy-lookup")
        (set (F 10) 7)
        (Seed 1 10)
        (Seed 2 10)
        (run-schedule
          (run-rule-batch
            :witnesses (1 2)
            :groups (("copy-lookup" (x)))
            :fires ((0 0) (0 1))))
        (check (Out 1 7))
        (check (Out 2 7))
    "#;
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(Some("packed-partial-lookup.egg".to_owned()), program)
            .unwrap();
    }
}

#[test]
fn packed_run_rule_batch_partial_key_ambiguity_is_atomic() {
    let mut egraph = EGraph::default();
    let error = egraph
        .parse_and_run_program(
            Some("packed-partial-ambiguous.egg".to_owned()),
            r#"
                (relation Seed (i64 i64))
                (relation Out (i64 i64))
                (rule ((Seed x y)) ((Out x y)) :name "copy")
                (Seed 1 10)
                (Seed 1 20)
                (run-schedule
                  (run-rule-batch
                    :witnesses (1)
                    :groups (("copy" (x)))
                    :fires ((0 0))))
            "#,
        )
        .unwrap_err();
    assert!(matches!(
        error,
        Error::RunRuleMatchCountMismatch {
            rule,
            expected: 1,
            observed: 2,
            ..
        } if rule == "copy"
    ));
    egraph
        .parse_and_run_program(None, "(fail (check (Out 1 10))) (fail (check (Out 1 20)))")
        .unwrap();
}

#[test]
fn packed_logical_selector_recovers_one_structural_grounding_strictly() {
    let program = r#"
        (datatype Expr (A) (B))
        (relation Seed (i64 Expr))
        (relation Fired (Expr))
        (rule ((Seed key value))
              ((Fired value))
              :name "copy")
        (Seed 0 (A))
        (Seed 0 (B))
        (run-schedule
          (run-rule-batch
            :witness-dag ((:lit i64 0)
                          (:call Expr A))
            :groups (("copy" (key) :logical (value)))
            :fires ((0 0 1))))
        (check (Fired (A)))
        (fail (check (Fired (B))))
    "#;
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(Some("packed-logical-selector.egg".to_owned()), program)
            .unwrap();
    }
}

#[test]
fn packed_grounded_batch_retains_lhs_only_selector_columns() {
    let program = r#"
        (relation Seed (i64 i64))
        (relation Fired ())
        (rule ((Seed x y)) ((Fired)) :name "copy")
        (Seed 1 10)
        (Seed 2 20)
        (run-schedule
          (run-rule-batch
            :witnesses (2 20)
            :groups (("copy" (x y)))
            :fires ((0 0 1))))
        (check (Fired))
    "#;
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(Some("packed-lhs-only-columns.egg".to_owned()), program)
            .unwrap();
    }
}

#[test]
fn packed_grounded_batch_counts_head_unused_projected_extensions_atomically() {
    let program = r#"
        (relation Seed (i64 i64))
        (relation Fired ())
        (rule ((Seed x y)) ((Fired)) :name "copy")
        (Seed 1 10)
        (Seed 1 20)
        (run-schedule
          (run-rule-batch
            :witnesses (1)
            :groups (("copy" (x)))
            :fires ((0 0))))
    "#;
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        let error = egraph
            .parse_and_run_program(
                Some("packed-head-unused-extensions.egg".to_owned()),
                program,
            )
            .unwrap_err();
        assert!(matches!(
            error,
            Error::RunRuleMatchCountMismatch {
                rule,
                expected: 1,
                observed: 2,
                ..
            } if rule == "copy"
        ));
        egraph
            .parse_and_run_program(None, "(fail (check (Fired)))")
            .unwrap();
    }
}

#[test]
fn packed_logical_selector_retains_aliased_constructor_leaf_strictly() {
    let program = r#"
        (datatype Expr (K i64))
        (relation Seed (Expr))
        (relation Fired ())
        (rule ((Seed x)) ((Fired)) :name "copy")
        (Seed (K 0))
        (union (K 0) (K 2))
        (run-schedule
          (run-rule-batch
            :witness-dag ((:lit i64 2)
                          (:call Expr K 0))
            :groups (("copy" () :logical (x)))
            :fires ((0 1))))
        (check (Fired))
    "#;
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(Some("packed-logical-aliased-leaf.egg".to_owned()), program)
            .unwrap();
    }
}

#[test]
fn packed_logical_selector_reuses_duplicate_roots_as_typed_aliases_strictly() {
    let program = r#"
        (datatype Expr (A) (B))
        (relation Seed (Expr Expr))
        (relation Fired (Expr Expr))
        (rule ((Seed x y)) ((Fired x y)) :name "copy")
        (Seed (A) (A))
        (Seed (A) (B))
        (run-schedule
          (run-rule-batch
            :witness-dag ((:call Expr A))
            :groups (("copy" () :logical (x y)))
            :fires ((0 0 0))))
        (check (Fired (A) (A)))
    "#;
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(Some("packed-logical-alias.egg".to_owned()), program)
            .unwrap();
    }
}

#[test]
fn packed_logical_selector_keeps_aliased_constructor_output_as_a_postfilter() {
    let program = r#"
        (datatype BinOp (Add))
        (datatype Expr (Leaf i64) (Bop BinOp Expr Expr))
        (datatype Type (T))
        (relation HasType (Expr Type))
        (relation Fired (Expr Expr Expr))
        (rule ((= e (Bop bop e1 e2))
               (HasType e1 t)
               (HasType e2 t))
              ((Fired e1 e2 e))
              :name "propagate")
        (HasType (Leaf 1) (T))
        (HasType (Leaf 2) (T))
        (union (Bop (Add) (Leaf 1) (Leaf 2)) (Leaf 1))
        (run-schedule
          (run-rule-batch
            :witness-dag ((:call Type T)
                          (:call BinOp Add)
                          (:lit i64 1)
                          (:call Expr Leaf 2)
                          (:lit i64 2)
                          (:call Expr Leaf 4)
                          (:call Expr Bop 1 3 5))
            :groups (("propagate" (t bop) :logical (e1 e2 e)))
            :fires ((0 0 1 3 5 6))))
        (check (Fired (Leaf 1) (Leaf 2) (Leaf 1)))
    "#;
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(
                Some("packed-logical-aliased-output.egg".to_owned()),
                program,
            )
            .unwrap();
    }
}

#[test]
fn packed_logical_selector_reuses_multiple_shapes_strictly() {
    let program = r#"
        (datatype Expr (A) (B) (Wrap Expr))
        (relation Seed (Expr))
        (relation Fired (Expr))
        (rule ((Seed x)) ((Fired x)) :name "copy")
        (Seed (A))
        (Seed (B))
        (Seed (Wrap (A)))
        (run-schedule
          (run-rule-batch
            :witness-dag ((:call Expr A)
                          (:call Expr B)
                          (:call Expr Wrap 0))
            :groups (("copy" () :logical (x)))
            :fires ((0 0) (0 1) (0 2))))
        (check (Fired (A)))
        (check (Fired (B)))
        (check (Fired (Wrap (A))))
    "#;
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(Some("packed-logical-shapes.egg".to_owned()), program)
            .unwrap();
    }
}

#[test]
fn packed_logical_selector_collapses_primitive_root_to_point_guard_strictly() {
    let program = r#"
        (relation Seed (i64))
        (relation Fired (i64))
        (rule ((Seed x)) ((Fired x)) :name "copy")
        (Seed 2)
        (run-schedule
          (run-rule-batch
            :witness-dag ((:lit i64 1)
                          (:call i64 + 0 0))
            :groups (("copy" () :logical (x)))
            :fires ((0 1))))
        (check (Fired 2))
    "#;
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(Some("packed-logical-primitive.egg".to_owned()), program)
            .unwrap();
    }
}

#[test]
fn packed_logical_selector_rejects_duplicate_original_groundings_atomically() {
    for (filename, program) in [
        (
            "packed-logical-same-shape-duplicate.egg",
            r#"
                (datatype Expr (K i64))
                (relation Seed (Expr))
                (relation Fired (Expr))
                (rule ((Seed x)) ((Fired x)) :name "copy")
                (Seed (K 0))
                (run-schedule
                  (run-rule-batch
                    :witness-dag ((:lit i64 0)
                                  (:call Expr K 0))
                    :groups (("copy" () :logical (x)))
                    :fires ((0 1) (0 1))))
            "#,
        ),
        (
            "packed-logical-cross-shape-duplicate.egg",
            r#"
                (datatype Expr (A) (Wrap Expr))
                (relation Seed (Expr))
                (relation Fired (Expr))
                (rule ((Seed x)) ((Fired x)) :name "copy")
                (Seed (A))
                (union (A) (Wrap (A)))
                (run-schedule
                  (run-rule-batch
                    :witness-dag ((:call Expr A)
                                  (:call Expr Wrap 0))
                    :groups (("copy" () :logical (x)))
                    :fires ((0 0) (0 1))))
            "#,
        ),
    ] {
        for mut egraph in [
            EGraph::default(),
            EGraph::new_with_proofs().with_proof_testing(),
        ] {
            let error = egraph
                .parse_and_run_program(Some(filename.to_owned()), program)
                .unwrap_err();
            assert!(
                error
                    .to_string()
                    .contains("select the same canonical grounding"),
                "{error}"
            );
            egraph
                .parse_and_run_program(None, "(fail (check (Fired x)))")
                .unwrap();
        }
    }
}

#[test]
fn packed_batch_without_logical_selector_remains_ambiguous_and_atomic() {
    let mut egraph = EGraph::default();
    let error = egraph
        .parse_and_run_program(
            Some("packed-without-logical-selector.egg".to_owned()),
            r#"
                (datatype Expr (A) (B))
                (relation Seed (i64 Expr))
                (relation Fired (Expr))
                (rule ((Seed key value))
                      ((Fired value))
                      :name "copy")
                (Seed 0 (A))
                (Seed 0 (B))
                (run-schedule
                  (run-rule-batch
                    :witness-dag ((:lit i64 0))
                    :groups (("copy" (key)))
                    :fires ((0 0))))
            "#,
        )
        .unwrap_err();
    assert!(matches!(
        error,
        Error::RunRuleMatchCountMismatch {
            rule,
            expected: 1,
            observed: 2,
            ..
        } if rule == "copy"
    ));
    egraph
        .parse_and_run_program(
            None,
            "(fail (check (Fired (A)))) (fail (check (Fired (B))))",
        )
        .unwrap();
}

#[test]
fn packed_witness_dag_replays_empty_zero_binding_fires() {
    for dictionary in [":witnesses ()", ":witness-dag ()"] {
        let program = format!(
            r#"
                (relation Trigger ())
                (relation Out ())
                (rule ((Trigger)) ((Out)) :name "copy")
                (Trigger)
                (run-schedule
                  (run-rule-batch
                    {dictionary}
                    :groups (("copy" ()))
                    :fires ((0))))
                (check (Out))
            "#
        );
        EGraph::default()
            .parse_and_run_program(None, &program)
            .unwrap();
    }
}

#[test]
fn packed_witness_dag_shares_globals_and_constructor_diamonds_strictly() {
    let program = r#"
        (datatype Expr (Leaf) (Pair Expr Expr))
        (relation Seed (Expr))
        (relation GlobalSeed (Expr))
        (relation Out (Expr))
        (relation GlobalOut (Expr))
        (rule ((Seed x)) ((Out x)) :name "copy")
        (rule ((GlobalSeed x)) ((GlobalOut x)) :name "copy-global")
        (let $leaf (Leaf))
        (let $diamond (Pair $leaf $leaf))
        (Seed $diamond)
        (GlobalSeed $diamond)
        (run-schedule
          (run-rule-batch
            :witness-dag ((:call Expr $leaf)
                          (:call Expr Pair 0 0)
                          (:call Expr $diamond))
            :groups (("copy" (x)) ("copy-global" (x)))
            :fires ((0 1) (1 2))))
        (check (Out $diamond))
        (check (GlobalOut $diamond))
    "#;
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(Some("packed-witness-diamond.egg".to_owned()), program)
            .unwrap();
    }
}

#[test]
fn packed_witness_dag_rejects_non_topological_and_unreachable_nodes() {
    for (program, expected) in [
        (
            r#"
                (datatype Expr (Leaf) (Pair Expr Expr))
                (relation Seed (Expr))
                (relation Out (Expr))
                (rule ((Seed x)) ((Out x)) :name "copy")
                (Seed (Pair (Leaf) (Leaf)))
                (run-schedule
                  (run-rule-batch
                    :witness-dag ((:call Expr Pair 1 1)
                                  (:call Expr Leaf))
                    :groups (("copy" (x)))
                    :fires ((0 0))))
            "#,
            "references non-prior child",
        ),
        (
            r#"
                (relation Seed (i64))
                (relation Out (i64))
                (rule ((Seed x)) ((Out x)) :name "copy")
                (Seed 1)
                (run-schedule
                  (run-rule-batch
                    :witness-dag ((:lit i64 1) (:lit i64 2))
                    :groups (("copy" (x)))
                    :fires ((0 0))))
            "#,
            "unreachable from every fire",
        ),
    ] {
        let error = EGraph::default()
            .parse_and_run_program(None, program)
            .unwrap_err();
        assert!(error.to_string().contains(expected), "{error}");
    }
}

#[test]
fn packed_witness_dag_guard_failure_is_atomic() {
    let mut egraph = EGraph::default();
    let error = egraph
        .parse_and_run_program(
            None,
            r#"
                (relation Seed (i64))
                (relation Out (i64))
                (rule ((Seed x)) ((Out x)) :name "copy")
                (Seed 1)
                (run-schedule
                  (run-rule-batch
                    :witness-dag ((:lit i64 1) (:lit i64 2))
                    :groups (("copy" (x)))
                    :fires ((0 0) (0 1))))
            "#,
        )
        .unwrap_err();
    assert!(matches!(
        error,
        Error::RunRuleMatchCountMismatch {
            rule,
            expected: 1,
            observed: 0,
            ..
        } if rule == "copy"
    ));
    egraph
        .parse_and_run_program(None, "(fail (check (Out 1)))")
        .unwrap();
}

#[test]
fn packed_run_rule_batch_guard_failure_is_atomic() {
    let mut egraph = EGraph::default();
    let error = egraph
        .parse_and_run_program(
            None,
            r#"
                (relation Seed (i64))
                (relation Out (i64))
                (rule ((Seed x)) ((Out x)) :name "copy")
                (Seed 1)
                (run-schedule
                  (run-rule-batch
                    :witnesses (1 2)
                    :groups (("copy" (x)))
                    :fires ((0 0) (0 1))))
            "#,
        )
        .unwrap_err();
    assert!(matches!(
        error,
        Error::RunRuleMatchCountMismatch {
            rule,
            expected: 1,
            observed: 0,
            ..
        } if rule == "copy"
    ));
    egraph
        .parse_and_run_program(None, "(fail (check (Out 1)))")
        .unwrap();
}

#[test]
fn packed_run_rule_batch_follows_projected_variable_aliases() {
    for mut egraph in [EGraph::default(), EGraph::new_with_proofs()] {
        egraph
            .parse_and_run_program(
                None,
                r#"
                    (relation Pair (i64 i64))
                    (relation Out (i64))
                    (rule ((Pair x y) (= x y)) ((Out y)) :name "equal-pair")
                    (Pair 1 1)
                    (Pair 2 2)
                    (run-schedule
                      (run-rule-batch
                        :witnesses (1)
                        :groups (("equal-pair" (x y)))
                        :fires ((0 0 0))))
                    (check (Out 1))
                    (fail (check (Out 2)))
                "#,
            )
            .unwrap();
    }
}

#[test]
fn packed_run_rule_batch_guards_query_primitive_results() {
    let program = r#"
        (relation Inputs (i64 i64))
        (relation Out (i64))
        (rule ((Inputs a b) (= result (+ a b)))
              ((Out result))
              :name "fold-add")
        (Inputs 2 3)
        (run-schedule
          (run-rule-batch
            :witnesses (2 3 5)
            :groups (("fold-add" (a b result)))
            :fires ((0 0 1 2))))
        (check (Out 5))
    "#;
    for mut egraph in [
        EGraph::default(),
        EGraph::new_with_proofs().with_proof_testing(),
    ] {
        egraph
            .parse_and_run_program(Some("packed-query-result.egg".to_owned()), program)
            .unwrap();
    }
}

#[test]
fn packed_run_rule_batch_guards_bigrat_query_primitive_results_strictly() {
    let program = r#"
        (relation Inputs (BigRat BigRat))
        (relation Expected (BigRat))
        (relation Out (BigRat))
        (rule ((Inputs base exponent) (= result (pow base exponent)))
              ((Out result))
              :name "fold-pow")
        (Inputs (bigrat (bigint 2) (bigint 1))
                (bigrat (bigint 3) (bigint 1)))
        (Expected (bigrat (bigint 8) (bigint 1)))
        (run-schedule
          (run-rule-batch
            :witnesses ((bigrat (bigint 2) (bigint 1))
                        (bigrat (bigint 3) (bigint 1))
                        (bigrat (bigint 8) (bigint 1)))
            :groups (("fold-pow" (base exponent result)))
            :fires ((0 0 1 2))))
        (check (Out (bigrat (bigint 8) (bigint 1))))
    "#;
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(Some("packed-query-pow.egg".to_owned()), program)
        .unwrap();
}

#[test]
fn packed_run_rule_batch_rejects_wrong_query_primitive_result_atomically() {
    let mut egraph = EGraph::default();
    let error = egraph
        .parse_and_run_program(
            None,
            r#"
                (relation Inputs (i64 i64))
                (relation Out (i64))
                (rule ((Inputs a b) (= result (+ a b)))
                      ((Out result))
                      :name "fold-add")
                (Inputs 2 3)
                (run-schedule
                  (run-rule-batch
                    :witnesses (2 3 6)
                    :groups (("fold-add" (a b result)))
                    :fires ((0 0 1 2))))
            "#,
        )
        .unwrap_err();
    assert!(matches!(
        error,
        Error::RunRuleMatchCountMismatch {
            rule,
            expected: 1,
            observed: 0,
            ..
        } if rule == "fold-add"
    ));
    egraph
        .parse_and_run_program(None, "(fail (check (Out 5)))")
        .unwrap();
}

#[test]
fn packed_run_rule_batch_allows_shared_inputs_with_distinct_full_groundings() {
    let mut egraph = EGraph::default();
    let error = egraph
        .parse_and_run_program(
            None,
            r#"
                (relation Inputs (i64 i64))
                (relation Out (i64))
                (rule ((Inputs a b) (= result (+ a b)))
                      ((Out result))
                      :name "fold-add")
                (Inputs 2 3)
                (run-schedule
                  (run-rule-batch
                    :witnesses (2 3 5 6)
                    :groups (("fold-add" (a b result)))
                    :fires ((0 0 1 2) (0 0 1 3))))
            "#,
        )
        .unwrap_err();
    assert!(matches!(
        error,
        Error::RunRuleMatchCountMismatch {
            rule,
            expected: 1,
            observed: 0,
            ..
        } if rule == "fold-add"
    ));
    egraph
        .parse_and_run_program(None, "(fail (check (Out 5)))")
        .unwrap();
}

#[test]
fn packed_run_rule_batch_uses_constructor_views_in_strict_proof_mode() {
    let program = r#"
        (datatype Expr (A) (B))
        (relation Seed (Expr))
        (relation Out (Expr))
        (rule ((Seed x)) ((Out x)) :name "copy")
        (Seed (A))
        (union (A) (B))
        (run-schedule
          (run-rule-batch
            :witnesses ((B))
            :groups (("copy" (x)))
            :fires ((0 0))))
        (check (Out (A)))
        (check (Out (B)))
    "#;
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(Some("packed-run-rule-proof-view.egg".to_owned()), program)
        .unwrap();
}

#[test]
fn packed_witness_dag_uses_constructor_views_in_strict_proof_mode() {
    let program = r#"
        (datatype Expr (A) (B))
        (relation Seed (Expr))
        (relation Out (Expr))
        (rule ((Seed x)) ((Out x)) :name "copy")
        (Seed (A))
        (union (A) (B))
        (run-schedule
          (run-rule-batch
            :witness-dag ((:call Expr B))
            :groups (("copy" (x)))
            :fires ((0 0))))
        (check (Out (A)))
        (check (Out (B)))
    "#;
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(
            Some("packed-witness-dag-proof-view.egg".to_owned()),
            program,
        )
        .unwrap();
}

#[test]
fn packed_witness_dag_rejects_nonglobal_custom_lookup() {
    let error = EGraph::default()
        .parse_and_run_program(
            None,
            r#"
                (function F () i64 :no-merge)
                (relation Seed (i64))
                (relation Out (i64))
                (rule ((Seed x)) ((Out x)) :name "copy")
                (set (F) 1)
                (Seed 1)
                (run-schedule
                  (run-rule-batch
                    :witness-dag ((:call i64 F))
                    :groups (("copy" (x)))
                    :fires ((0 0))))
            "#,
        )
        .unwrap_err();
    assert!(
        error.to_string().contains("is not a constructor"),
        "{error}"
    );
}
