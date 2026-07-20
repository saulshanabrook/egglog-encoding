use egglog::{EGraph, causal_slice::causal_slice_program};

const ORIGINAL: &str = include_str!("../../.codex/causal-slice-v0/bronze.egg");

const FULL_TRANSCRIPT: &str = r#"
    (relation Seed (i64))
    (relation Mid (i64))
    (relation Goal (i64))
    (relation Irrelevant (i64))
    (ruleset derive)
    (rule ((Seed x)) ((Mid x)) :ruleset derive :name "seed-to-mid")
    (rule ((Mid x)) ((Goal x)) :ruleset derive :name "mid-to-goal")
    (rule ((Seed x)) ((Irrelevant x)) :ruleset derive :name "irrelevant")
    (Seed 1)
    (Seed 2)
    (run-schedule
      (run-rule "seed-to-mid" :bind ((x 1)) :expect 1)
      (run-rule "seed-to-mid" :bind ((x 2)) :expect 1)
      (run-rule "irrelevant" :bind ((x 1)) :expect 1)
      (run-rule "irrelevant" :bind ((x 2)) :expect 1)
      (run-rule "mid-to-goal" :bind ((x 1)) :expect 1)
      (run-rule "mid-to-goal" :bind ((x 2)) :expect 1))
    (check (Goal 2))
"#;

#[test]
fn full_manual_transcript_replays_in_normal_and_proof_modes() {
    for make_egraph in [EGraph::default, EGraph::new_with_proofs, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        let mut original = make_egraph();
        original.parse_and_run_program(None, ORIGINAL).unwrap();

        let mut replay = make_egraph();
        replay.parse_and_run_program(None, FULL_TRANSCRIPT).unwrap();
    }
}

#[test]
fn trace_retains_body_variables_that_the_rule_head_does_not_use() {
    let source = r#"
        (relation R (i64 i64))
        (relation Out (i64))
        (rule ((R x y)) ((Out x)) :name "copy")
        (R 1 10)
        (R 1 20)
        (run 1)
        (check (Out 1))
    "#;
    let slice = causal_slice_program(Some("private-variable.egg".to_owned()), source).unwrap();

    assert_eq!(slice.stats.matched_applications, 2);
    assert!(
        slice
            .full_transcript_source
            .contains(":bind ((x 1) (y 10)) :expect 1")
    );
    assert!(
        slice
            .full_transcript_source
            .contains(":bind ((x 1) (y 20)) :expect 1")
    );

    for replay_source in [&slice.full_transcript_source, &slice.source] {
        let mut ordinary = EGraph::default();
        ordinary
            .parse_and_run_program(
                Some("private-variable-replay.egg".to_owned()),
                replay_source,
            )
            .unwrap();

        let mut strict_proofs = EGraph::new_with_proofs().with_proof_testing();
        strict_proofs
            .parse_and_run_program(
                Some("private-variable-replay.egg".to_owned()),
                replay_source,
            )
            .unwrap();
    }
}

#[test]
fn trace_retains_private_variables_in_multi_atom_generic_joins() {
    let source = r#"
        (relation R (i64 i64))
        (relation S (i64))
        (relation Out (i64))
        (rule ((R x y) (S x)) ((Out x)) :name "copy")
        (R 1 10)
        (R 1 20)
        (S 1)
        (run 1)
        (check (Out 1))
    "#;
    let slice = causal_slice_program(Some("private-gj-variable.egg".to_owned()), source).unwrap();

    assert_eq!(slice.stats.pending_firings, 2);
    assert!(
        slice
            .full_transcript_source
            .contains(":bind ((x 1) (y 10)) :expect 1")
    );
    assert!(
        slice
            .full_transcript_source
            .contains(":bind ((x 1) (y 20)) :expect 1")
    );

    for replay_source in [&slice.full_transcript_source, &slice.source] {
        EGraph::new_with_proofs()
            .with_proof_testing()
            .parse_and_run_program(Some("private-gj-replay.egg".to_owned()), replay_source)
            .unwrap();
    }
}

#[test]
fn positive_check_trace_retains_every_variable_in_one_environment() {
    let source = r#"
        (relation R (i64 i64))
        (relation S (i64))
        (relation T (i64))
        (R 1 2)
        (S 1)
        (T 2)
        (run 1)
        (check (R x y) (S x) (T y))
    "#;
    let slice =
        causal_slice_program(Some("private-check-variable.egg".to_owned()), source).unwrap();

    assert_eq!(slice.stats.pending_firings, 0);
    assert_eq!(slice.stats.retained_applications, 0);
    assert_eq!(slice.stats.observation_matches, 1);
    assert_eq!(slice.stats.observation_bindings, 2);
    assert_eq!(slice.stats.witness_nodes, 2);

    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("private-check-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
}

#[test]
fn bronze_slice_traces_once_removes_irrelevant_applications_and_strictly_replays() {
    let slice = causal_slice_program(Some("bronze.egg".to_owned()), ORIGINAL).unwrap();

    assert_eq!(slice.stats.matched_applications, 6);
    assert_eq!(slice.stats.pending_firings, 6);
    assert_eq!(slice.stats.effective_applications, 6);
    assert_eq!(slice.stats.effective_output_rows, 6);
    assert_eq!(slice.stats.promoted_events, 6);
    assert_eq!(slice.stats.no_op_applications, 0);
    assert_eq!(slice.stats.retained_applications, 2);
    assert_eq!(slice.stats.source_events, 2);
    assert!(slice.stats.dependency_nodes >= 9);
    assert_eq!(slice.stats.witness_nodes, 2);
    assert_eq!(slice.stats.equality_edges, 0);
    assert_eq!(slice.stats.prefix_fallbacks, 0);
    assert_eq!(slice.stats.observation_count, 1);
    assert_eq!(slice.stats.waves, 3);
    assert_eq!(slice.stats.captured_bindings, 6);
    assert_eq!(slice.stats.observation_matches, 1);
    assert_eq!(slice.stats.observation_bindings, 0);
    assert_eq!(slice.stats.max_batch_matches, 4);
    assert!(slice.stats.raw_trace_bindings >= slice.stats.captured_bindings);
    assert!(slice.stats.raw_trace_lower_bound_bytes > 0);
    assert!(!slice.source.contains("(saturate"));
    assert!(!slice.source.contains("(run derive"));
    assert!(
        slice
            .source
            .contains("(run-rule \"seed-to-mid\" :bind ((x 2)) :expect 1)")
    );
    assert!(
        slice
            .source
            .contains("(run-rule \"mid-to-goal\" :bind ((x 2)) :expect 1)")
    );
    assert!(
        !slice
            .source
            .contains("(run-rule \"seed-to-mid\" :bind ((x 1))")
    );
    assert!(!slice.source.contains("(run-rule \"irrelevant\""));

    for source in [&slice.full_transcript_source, &slice.source] {
        let mut ordinary = EGraph::default();
        ordinary
            .parse_and_run_program(Some("replay.egg".to_owned()), source)
            .unwrap();

        let mut strict_proofs = EGraph::new_with_proofs().with_proof_testing();
        strict_proofs
            .parse_and_run_program(Some("replay.egg".to_owned()), source)
            .unwrap();
    }

    let second = causal_slice_program(Some("bronze.egg".to_owned()), ORIGINAL).unwrap();
    assert_eq!(slice.source, second.source);
    assert_eq!(slice.full_transcript_source, second.full_transcript_source);
}

#[test]
fn anonymous_rule_names_are_source_based_and_stable() {
    let source = r#"
        (relation A (i64))
        (relation B (i64))
        (rule ((A x)) ((B x)))
        (A 1)
        (run 1)
        (check (B 1))
    "#;
    let first = causal_slice_program(Some("anonymous.egg".to_owned()), source).unwrap();
    let second = causal_slice_program(Some("anonymous.egg".to_owned()), source).unwrap();
    assert_eq!(first.source, second.source);
    let name = &first.rule_mapping[0].registered_name;
    assert!(name.starts_with("__causal_slice_v0_b"));
    assert!(first.source.contains(&format!("(run-rule \"{name}\"")));
}

#[test]
fn duplicate_anonymous_rules_get_distinct_names_and_no_ops_are_separated() {
    let source = r#"
        (relation A (i64))
        (relation B (i64))
        (rule ((A x)) ((B x)))
        (rule ((A x)) ((B x)))
        (A 1)
        (run 1)
        (check (B 1))
    "#;
    let slice = causal_slice_program(Some("duplicates.egg".to_owned()), source).unwrap();
    assert_eq!(slice.rule_mapping.len(), 2);
    assert_ne!(
        slice.rule_mapping[0].registered_name,
        slice.rule_mapping[1].registered_name
    );
    assert_eq!(slice.stats.matched_applications, 2);
    assert_eq!(slice.stats.effective_applications, 1);
    assert_eq!(slice.stats.no_op_applications, 1);
    assert_eq!(slice.stats.retained_applications, 1);
    assert_eq!(slice.full_transcript_source.matches("(run-rule").count(), 2);
    assert_eq!(slice.source.matches("(run-rule").count(), 1);

    let mut replay = EGraph::default();
    replay
        .parse_and_run_program(Some("duplicates-replay.egg".to_owned()), &slice.source)
        .unwrap();
}

#[test]
fn positive_check_selects_one_actual_satisfying_grounding() {
    let source = ORIGINAL.replace("(check (Goal 2))", "(check (Goal x))");
    let slice = causal_slice_program(Some("witness.egg".to_owned()), &source).unwrap();
    assert_eq!(slice.stats.retained_applications, 2);
    assert_eq!(slice.source.matches("(run-rule").count(), 2);
    assert!(!slice.source.contains("(run-rule \"irrelevant\""));

    let mut replay = EGraph::default();
    replay
        .parse_and_run_program(Some("witness-replay.egg".to_owned()), &slice.source)
        .unwrap();
}

#[test]
fn conjunctive_and_multiple_checks_retain_complete_heads_and_both_chains() {
    let source = r#"
        (relation A (i64))
        (relation B (i64))
        (relation Side (i64))
        (relation Goal (i64))
        (relation D (i64))
        (relation Other (i64))
        (relation Irrelevant (i64))
        (ruleset derive)
        (rule ((A x)) ((B x) (Side x)) :ruleset derive :name "fanout")
        (rule ((B x)) ((Goal x)) :ruleset derive :name "finish")
        (rule ((D x)) ((Other x)) :ruleset derive :name "other-root")
        (rule ((A x)) ((Irrelevant x)) :ruleset derive :name "irrelevant")
        (A 1)
        (D 2)
        (run-schedule (saturate derive))
        (check (Goal 1) (Side 1))
        (check (Other 2))
    "#;
    let slice = causal_slice_program(Some("combined-roots.egg".to_owned()), source).unwrap();
    assert_eq!(slice.stats.observation_count, 2);
    assert_eq!(slice.stats.retained_applications, 3);
    assert!(slice.source.contains("(run-rule \"fanout\""));
    assert!(slice.source.contains("(run-rule \"finish\""));
    assert!(slice.source.contains("(run-rule \"other-root\""));
    assert!(!slice.source.contains("(run-rule \"irrelevant\""));
    assert!(slice.source.contains("(B x)"));
    assert!(slice.source.contains("(Side x)"));
    assert_eq!(slice.source.matches("(check").count(), 2);

    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("combined-roots-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
}

#[test]
fn unsupported_observations_and_filters_fail_closed() {
    let negative = r#"
        (relation A (i64))
        (A 1)
        (run 1)
        (fail (check (A 2)))
    "#;
    let error = causal_slice_program(Some("negative.egg".to_owned()), negative).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("negative checks / proof of absence")
    );
    assert!(error.to_string().contains("negative.egg"));

    let equality = r#"
        (relation A (i64))
        (relation B (i64))
        (rule ((A x) (= x 1)) ((B x)) :name "filtered")
        (A 1)
        (run 1)
        (check (B 1))
    "#;
    let error = causal_slice_program(Some("filter.egg".to_owned()), equality).unwrap_err();
    assert!(error.to_string().contains("equality or primitive filters"));
}

#[test]
fn wildcard_bindings_fail_closed_instead_of_emitting_parser_variables() {
    let source = r#"
        (relation A (i64))
        (relation B ())
        (rule ((A _)) ((B)) :name "wildcard")
        (A 1)
        (run 1)
        (check (B))
    "#;
    let error = causal_slice_program(Some("wildcard.egg".to_owned()), source).unwrap_err();
    let message = error.to_string();
    assert!(message.contains("wildcard or parser-generated variables"));
    assert!(message.contains("wildcard.egg"));
}

#[test]
fn non_round_trip_string_witnesses_fail_closed() {
    let source = r#"
        (relation A (String))
        (relation B (String))
        (rule ((A x)) ((B x)) :name "copy")
        (A "a\\nb")
        (run 1)
        (check (B "a\\nb"))
    "#;
    let error = causal_slice_program(Some("escaped-string.egg".to_owned()), source).unwrap_err();
    let message = error.to_string();
    assert!(message.contains("source printer cannot round-trip"));
    assert!(message.contains("escaped-string.egg"));

    let escaped_rule_name = r#"
        (relation A (i64))
        (relation B (i64))
        (rule ((A x)) ((B x)) :name "bad\\nname")
        (A 1)
        (run 1)
        (check (B 1))
    "#;
    let error = causal_slice_program(Some("escaped-rule-name.egg".to_owned()), escaped_rule_name)
        .unwrap_err();
    let message = error.to_string();
    assert!(message.contains("explicit rule name"));
    assert!(message.contains("escaped-rule-name.egg"));
}

#[test]
fn fully_grounded_monotone_replay_preserves_one_shared_wave() {
    let ordinary = r#"
        (relation A (i64))
        (relation B (i64))
        (relation C (i64))
        (ruleset derive)
        (rule ((A x)) ((B x)) :ruleset derive :name "a-to-b")
        (rule ((B y)) ((C y)) :ruleset derive :name "b-to-c")
        (A 1)
        (B 2)
        (run-schedule (run derive))
        (check (B 1))
        (check (C 2))
        (fail (check (C 1)))
    "#;
    let replay = r#"
        (relation A (i64))
        (relation B (i64))
        (relation C (i64))
        (ruleset derive)
        (rule ((A x)) ((B x)) :ruleset derive :name "a-to-b")
        (rule ((B y)) ((C y)) :ruleset derive :name "b-to-c")
        (A 1)
        (B 2)
        (run-schedule (seq
          (run-rule "a-to-b" :bind ((x 1)) :expect 1)
          (run-rule "b-to-c" :bind ((y 2)) :expect 1)))
        (check (B 1))
        (check (C 2))
        (fail (check (C 1)))
    "#;
    for program in [ordinary, replay] {
        EGraph::default()
            .parse_and_run_program(None, program)
            .unwrap();
    }
}

#[test]
fn sequential_replay_is_not_shared_wave_replay_for_delete() {
    let ordinary = r#"
        (function F (i64) i64 :no-merge)
        (relation Del ())
        (relation Seen (i64))
        (ruleset mutate)
        (rule ((Del)) ((delete (F 0))) :ruleset mutate :name "delete-f")
        (rule ((= v (F 0))) ((Seen v)) :ruleset mutate :name "read-f")
        (set (F 0) 9)
        (Del)
        (run-schedule (run mutate))
        (check (Seen 9))
    "#;
    EGraph::default()
        .parse_and_run_program(None, ordinary)
        .unwrap();

    let replay = ordinary.replace(
        "(run-schedule (run mutate))",
        r#"(run-schedule (seq
          (run-rule "delete-f" :expect 1)
          (run-rule "read-f" :bind ((v 9)) :expect 1)))"#,
    );
    let error = EGraph::default()
        .parse_and_run_program(None, &replay)
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("expected 1 match(es), but found 0")
    );
}

#[test]
fn sequential_replay_silently_changes_insert_delete_commit_order() {
    let ordinary = r#"
        (relation Trigger ())
        (relation R (i64))
        (ruleset mutate)
        (rule ((Trigger)) ((R 1)) :ruleset mutate :name "insert-r")
        (rule ((Trigger)) ((delete (R 1))) :ruleset mutate :name "delete-r")
        (Trigger)
        (run-schedule (run mutate))
        (check (R 1))
    "#;
    EGraph::default()
        .parse_and_run_program(None, ordinary)
        .unwrap();

    let sequential = ordinary
        .replace(
            "(run-schedule (run mutate))",
            r#"(run-schedule (seq
              (run-rule "insert-r" :expect 1)
              (run-rule "delete-r" :expect 1)))"#,
        )
        .replace("(check (R 1))", "(fail (check (R 1)))");
    EGraph::default()
        .parse_and_run_program(None, &sequential)
        .unwrap();
}

#[test]
fn sequential_replay_does_not_preserve_subsume_query_prestate() {
    let ordinary = r#"
        (relation Trigger ())
        (relation R (i64))
        (relation Seen (i64))
        (ruleset mutate)
        (rule ((Trigger)) ((subsume (R 1))) :ruleset mutate :name "subsume-r")
        (rule ((R x)) ((Seen x)) :ruleset mutate :name "read-r")
        (Trigger)
        (R 1)
        (run-schedule (run mutate))
        (check (Seen 1))
    "#;
    EGraph::default()
        .parse_and_run_program(None, ordinary)
        .unwrap();

    let sequential = ordinary.replace(
        "(run-schedule (run mutate))",
        r#"(run-schedule (seq
          (run-rule "subsume-r" :expect 1)
          (run-rule "read-r" :bind ((x 1)) :expect 1)))"#,
    );
    let error = EGraph::default()
        .parse_and_run_program(None, &sequential)
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("expected 1 match(es), but found 0")
    );
}

#[test]
fn sequential_replay_changes_dynamic_rhs_lookup_state() {
    let ordinary = r#"
        (function F (i64) i64 :merge new)
        (function G (i64) i64 :merge new)
        (relation Trigger ())
        (ruleset mutate)
        (rule ((Trigger)) ((set (F 1) 1)) :ruleset mutate :name "write-f" :naive)
        (rule ((Trigger)) ((set (G 1) (F 1))) :ruleset mutate :name "read-f" :naive)
        (set (F 1) 0)
        (Trigger)
        (run-schedule (run mutate))
        (check (= (G 1) 0))
    "#;
    EGraph::default()
        .parse_and_run_program(None, ordinary)
        .unwrap();

    let sequential = ordinary
        .replace(
            "(run-schedule (run mutate))",
            r#"(run-schedule (seq
              (run-rule "write-f" :expect 1)
              (run-rule "read-f" :expect 1)))"#,
        )
        .replace("(check (= (G 1) 0))", "(check (= (G 1) 1))");
    EGraph::default()
        .parse_and_run_program(None, &sequential)
        .unwrap();
}

#[test]
fn additive_same_key_writes_happen_to_match_in_both_wave_models() {
    let ordinary = r#"
        (function F (i64) i64 :merge (+ old new))
        (relation Trigger ())
        (ruleset mutate)
        (rule ((Trigger)) ((set (F 1) 1)) :ruleset mutate :name "write-one")
        (rule ((Trigger)) ((set (F 1) 2)) :ruleset mutate :name "write-two")
        (Trigger)
        (run-schedule (run mutate))
        (check (= (F 1) 3))
    "#;
    let sequential = ordinary.replace(
        "(run-schedule (run mutate))",
        r#"(run-schedule (seq
          (run-rule "write-one" :expect 1)
          (run-rule "write-two" :expect 1)))"#,
    );

    for source in [ordinary, sequential.as_str()] {
        EGraph::default()
            .parse_and_run_program(None, source)
            .unwrap();
    }
}

#[test]
fn native_direct_redundant_and_congruence_equalities_pass_strict_proofs() {
    let source = r#"
        (datatype Expr (A i64) (F Expr))
        (let $a1 (A 1))
        (let $a2 (A 2))
        (let $f1 (F $a1))
        (let $f2 (F $a2))
        (union $a1 $a2)
        (union $a1 $a2)
        (run 1)
        (check (= $f1 $f2))
    "#;
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(None, source)
        .unwrap();

    let error = causal_slice_program(Some("equality.egg".to_owned()), source).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("functions, constructors, datatypes, or custom sorts")
    );
}

#[test]
fn expect_count_is_not_a_grounding_guard_with_primitive_filters() {
    let program = r#"
        (relation R (i64))
        (relation Fired (i64))
        (rule ((R y) (= x 1)) ((Fired y)) :name "literal-guard")
        (R 10)
        (run-schedule
          (run-rule "literal-guard" :bind ((x 2) (y 10)) :expect 1))
        (fail (check (Fired 10)))
    "#;
    // The guard currently counts the table candidate before the primitive
    // equality rejects it. Bronze rejects such bodies before tracing.
    EGraph::default()
        .parse_and_run_program(None, program)
        .unwrap();
}
