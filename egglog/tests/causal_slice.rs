use std::sync::atomic::{AtomicU64, Ordering};

use egglog::{
    EGraph,
    causal_slice::{causal_slice_program, causal_slice_program_with_fact_directory},
};

static NEXT_INPUT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

fn input_directory() -> std::path::PathBuf {
    let directory = std::env::temp_dir().join(format!(
        "egglog-causal-slice-input-{}-{}",
        std::process::id(),
        NEXT_INPUT_DIRECTORY.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    directory
}

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
fn scalar_relation_input_is_embedded_as_replayable_source_facts() {
    let directory = input_directory();
    std::fs::write(directory.join("seed.tsv"), "1\n2\n").unwrap();
    let source = r#"
        (relation Seed (i64))
        (relation Goal (i64))
        (relation Irrelevant (i64))
        (rule ((Seed x)) ((Goal x)) :name "goal")
        (rule ((Seed x)) ((Irrelevant x)) :name "irrelevant")
        (input Seed "seed.tsv")
        (run 1)
        (check (Goal 2))
    "#;

    let slice = causal_slice_program_with_fact_directory(
        Some("input.egg".to_owned()),
        source,
        Some(&directory),
    )
    .unwrap();

    assert_eq!(slice.stats.source_facts, 2);
    assert!(!slice.source.contains("(input"));
    assert!(slice.source.contains("(Seed 1)"));
    assert!(slice.source.contains("(Seed 2)"));
    assert!(!slice.source.contains("irrelevant\" :bind"));

    // The replay is self-contained: it must not fall back to the original
    // external fact source after slicing.
    std::fs::remove_dir_all(directory).unwrap();
    for replay_source in [&slice.full_transcript_source, &slice.source] {
        EGraph::default()
            .parse_and_run_program(Some("input-replay.egg".to_owned()), replay_source)
            .unwrap();
        EGraph::new_with_proofs()
            .with_proof_testing()
            .parse_and_run_program(Some("input-replay.egg".to_owned()), replay_source)
            .unwrap();
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
fn projected_generic_join_variable_is_an_explicit_replay_boundary() {
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
    // The ordinary Generic Join plan projects `y`, so both the original run
    // and an unbound run-rule see one logical firing.
    EGraph::default()
        .parse_and_run_program(Some("private-gj-variable.egg".to_owned()), source)
        .unwrap();
    let unbound = source.replace("(run 1)", "(run-schedule (run-rule \"copy\" :expect 1))");
    EGraph::default()
        .parse_and_run_program(Some("private-gj-unbound.egg".to_owned()), &unbound)
        .unwrap();

    // Binding x specializes the query, exposes both y extensions, and makes
    // PR #23's atomic exact-count guard fail. Fully binding y succeeds, but no
    // match-time evidence tells us which extension represents the projected
    // ordinary firing.
    let partial = source.replace(
        "(run 1)",
        "(run-schedule (run-rule \"copy\" :bind ((x 1)) :expect 1))",
    );
    let error = EGraph::default()
        .parse_and_run_program(Some("private-gj-partial.egg".to_owned()), &partial)
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("expected 1 match(es), but found 2")
    );
    let fully_bound = source.replace(
        "(run 1)",
        "(run-schedule (run-rule \"copy\" :bind ((x 1) (y 10)) :expect 1))",
    );
    EGraph::default()
        .parse_and_run_program(Some("private-gj-bound.egg".to_owned()), &fully_bound)
        .unwrap();

    let error =
        causal_slice_program(Some("private-gj-variable.egg".to_owned()), source).unwrap_err();
    let message = error.to_string();
    assert!(message.contains("Generic Join may project"));
    assert!(message.contains("projection-preserving match selector"));
    assert!(message.contains("private-gj-variable.egg"));
}

#[test]
fn positive_check_trace_retains_every_variable_in_one_environment() {
    let source = r#"
        (relation R (i64 i64))
        (R 1 2)
        (run 1)
        (check (R x y))
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
fn projected_check_variable_and_decomposed_check_fail_closed() {
    let projected = r#"
        (relation R (i64 i64))
        (relation S (i64))
        (R 1 2)
        (S 1)
        (run 1)
        (check (R x y) (S x))
    "#;
    let error =
        causal_slice_program(Some("projected-check.egg".to_owned()), projected).unwrap_err();
    assert!(error.to_string().contains("check variable `y`"));
    assert!(error.to_string().contains("Generic Join may project"));

    let decomposed = r#"
        (relation R (i64))
        (relation S (i64))
        (relation T (i64))
        (R 1)
        (S 1)
        (T 1)
        (run 1)
        (check (R x) (S x) (T x))
    "#;
    let error =
        causal_slice_program(Some("decomposed-check.egg".to_owned()), decomposed).unwrap_err();
    assert!(error.to_string().contains("potentially tree-decomposed"));
    assert!(error.to_string().contains("materialized intermediate rows"));
}

#[test]
fn two_body_relation_rule_replays_both_exact_premises() {
    let source = r#"
        (relation A (i64))
        (relation B (i64))
        (relation Goal (i64))
        (rule ((A x) (B x)) ((Goal x)) :name "join")
        (A 1)
        (B 1)
        (run 1)
        (check (Goal 1))
    "#;
    let slice = causal_slice_program(Some("two-body.egg".to_owned()), source).unwrap();

    assert_eq!(slice.stats.pending_firings, 1);
    assert_eq!(slice.stats.retained_applications, 1);
    assert!(
        slice
            .source
            .contains("(run-rule \"join\" :bind ((x 1)) :expect 1)")
    );

    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("two-body-replay.egg".to_owned()), &slice.source)
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
fn rule_created_constructor_witness_drives_sliced_replay_and_strict_proofs() {
    let source = r#"
        (datatype Expr (A i64) (F Expr))
        (relation Seed (i64))
        (relation Mid (Expr))
        (relation Goal (Expr))
        (relation Irrelevant (Expr))
        (rule ((Seed n)) ((Mid (F (A n)))) :name "build")
        (rule ((Mid x)) ((Goal x)) :name "finish")
        (rule ((Mid x)) ((Irrelevant x)) :name "irrelevant")
        (Seed 7)
        (run 3)
        (check (Goal x))
    "#;

    let slice = causal_slice_program(Some("constructor-witness.egg".to_owned()), source).unwrap();
    assert!(!slice.source.contains("(run 3)"));
    assert!(
        slice
            .source
            .contains("(run-rule \"build\" :bind ((n 7)) :expect 1)")
    );
    assert!(
        slice
            .source
            .contains("(run-rule \"finish\" :bind ((x (F (A 7)))) :expect 1)")
    );
    assert!(!slice.source.contains("run-rule \"irrelevant\""));
    assert_eq!(slice.stats.retained_applications, 2);

    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("constructor-witness-replay.egg".to_owned()),
                &slice.source,
            )
            .unwrap();
    }

    let second = causal_slice_program(Some("constructor-witness.egg".to_owned()), source).unwrap();
    assert_eq!(slice.source, second.source);
}

#[test]
fn source_constructor_witness_is_available_to_manual_replay() {
    let source = r#"
        (datatype Expr (A i64))
        (relation Seed (Expr))
        (relation Goal (Expr))
        (rule ((Seed x)) ((Goal x)) :name "copy")
        (Seed (A 7))
        (run 1)
        (check (Goal x))
    "#;

    let slice = causal_slice_program(Some("source-witness.egg".to_owned()), source).unwrap();
    assert!(slice.source.contains("(Seed (A 7))"));
    assert!(
        slice
            .source
            .contains("(run-rule \"copy\" :bind ((x (A 7))) :expect 1)")
    );
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("source-witness-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
}

#[test]
fn standalone_and_constructor_only_head_actions_replay_as_complete_firings() {
    let source = r#"
        (datatype Expr (A String))
        (constructor make (String) Expr)
        (relation Seed (String))
        (relation Goal (Expr))
        (rule ((Seed x))
              ((make x) (Goal (make x)))
              :name "build")
        (Seed "x")
        (run 1)
        (check (Goal y))
    "#;

    let slice =
        causal_slice_program(Some("standalone-constructor.egg".to_owned()), source).unwrap();
    assert!(
        slice
            .source
            .contains("(run-rule \"build\" :bind ((x \"x\")) :expect 1)")
    );
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("standalone-constructor-replay.egg".to_owned()),
                &slice.source,
            )
            .unwrap();
    }
}

#[test]
fn direct_union_slice_retains_applied_edge_and_drops_redundant_firing() {
    let source = r#"
        (datatype Expr (A i64))
        (relation Pair (Expr Expr))
        (rule ((Pair x y)) ((union x y)) :name "unify")
        (rule ((Pair x y)) ((union x x)) :name "redundant")
        (Pair (A 1) (A 2))
        (run 1)
        (check (= (A 1) (A 2)))
    "#;

    let slice = causal_slice_program(Some("direct-union.egg".to_owned()), source).unwrap();
    assert_eq!(slice.stats.equality_edges, 1);
    assert_eq!(slice.stats.retained_applications, 1);
    assert!(
        slice
            .source
            .contains("(run-rule \"unify\" :bind ((x (A 1)) (y (A 2))) :expect 1)")
    );
    assert!(!slice.source.contains("run-rule \"redundant\""));

    for replay_source in [&slice.full_transcript_source, &slice.source] {
        for make_egraph in [EGraph::default, || {
            EGraph::new_with_proofs().with_proof_testing()
        }] {
            make_egraph()
                .parse_and_run_program(Some("direct-union-replay.egg".to_owned()), replay_source)
                .unwrap();
        }
    }
}

#[test]
fn constructor_union_uses_native_application_and_union_causes() {
    let source = r#"
        (datatype Allocation (A String))
        (constructor expr_points_to (String) Allocation)
        (relation Seed (String Allocation))
        (rule ((Seed e a))
              ((union (expr_points_to e) a))
              :name "make-points-to")
        (Seed "e" (A "alloc"))
        (run 1)
        (check (= (expr_points_to "e") (A "alloc")))
    "#;

    let slice = causal_slice_program(Some("constructor-union.egg".to_owned()), source).unwrap();
    assert_eq!(slice.stats.equality_edges, 1);
    assert_eq!(slice.stats.retained_applications, 1);
    assert!(
        slice.source.contains(
            "(run-rule \"make-points-to\" :bind ((e \"e\") (a (A \"alloc\"))) :expect 1)"
        )
    );

    for replay_source in [&slice.full_transcript_source, &slice.source] {
        for make_egraph in [EGraph::default, || {
            EGraph::new_with_proofs().with_proof_testing()
        }] {
            make_egraph()
                .parse_and_run_program(
                    Some("constructor-union-replay.egg".to_owned()),
                    replay_source,
                )
                .unwrap();
        }
    }
}

#[test]
fn equality_rekeyed_relation_rows_fail_closed_without_commit_provenance() {
    let source = r#"
        (datatype Expr (A i64))
        (relation Pair (Expr Expr))
        (rule ((Pair x y)) ((union x y)) :name "unify")
        (Pair (A 1) (A 2))
        (run 2)
        (check (= (A 1) (A 2)))
    "#;

    let error = causal_slice_program(Some("relation-rekey.egg".to_owned()), source).unwrap_err();
    let message = error.to_string();
    assert!(message.contains("equality-canonicalized premise"));
    assert!(message.contains("relation-row rekey provenance"));
    assert!(message.contains("relation-rekey.egg"));
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
fn emitted_rules_preserve_source_no_decomp_flags() {
    let source = r#"
        (relation A (i64))
        (relation B (i64))
        (rule ((A x)) ((B x)) :name "copy")
        (A 1)
        (run 1)
        (check (B 1))
    "#;
    let ordinary = causal_slice_program(Some("ordinary-plan.egg".to_owned()), source).unwrap();
    assert!(!ordinary.source.contains(":no-decomp"));

    let no_decomp_source = source.replace(":name \"copy\")", ":name \"copy\" :no-decomp)");
    let no_decomp =
        causal_slice_program(Some("no-decomp-plan.egg".to_owned()), &no_decomp_source).unwrap();
    assert!(no_decomp.source.contains(":no-decomp"));
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
fn duplicate_head_actions_count_one_output_but_replay_the_complete_head() {
    let source = r#"
        (relation A (i64))
        (relation B (i64))
        (rule ((A x)) ((B x) (B x)) :name "duplicate-head")
        (A 1)
        (run 1)
        (check (B 1))
    "#;
    let slice = causal_slice_program(Some("duplicate-head.egg".to_owned()), source).unwrap();

    assert_eq!(slice.stats.pending_firings, 1);
    assert_eq!(slice.stats.promoted_events, 1);
    assert_eq!(slice.stats.effective_output_rows, 1);
    assert_eq!(slice.source.matches("(B x)").count(), 2);

    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(Some("duplicate-head-replay.egg".to_owned()), &slice.source)
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
            .contains("a non-relation initialization action")
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
