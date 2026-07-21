use std::sync::atomic::{AtomicU64, Ordering};

use egglog::{
    EGraph,
    ast::{Command, Schedule},
    causal_slice::{
        causal_slice_program, causal_slice_program_with_fact_directory, causal_slice_replay_program,
    },
};

fn replay_firings(source: &str) -> Vec<(String, Vec<(String, String)>)> {
    fn visit(schedule: &Schedule, firings: &mut Vec<(String, Vec<(String, String)>)>) {
        match schedule {
            Schedule::RunRule(_, config) => firings.push((
                config.rule.clone(),
                config
                    .bindings
                    .iter()
                    .map(|(variable, witness)| (variable.clone(), witness.to_string()))
                    .collect(),
            )),
            Schedule::RunRuleBatch(_, configs) => {
                for config in configs {
                    firings.push((
                        config.rule.clone(),
                        config
                            .bindings
                            .iter()
                            .map(|(variable, witness)| (variable.clone(), witness.to_string()))
                            .collect(),
                    ));
                }
            }
            Schedule::RunRuleBatchPacked(_, batch) => {
                for fire in batch.fires.iter() {
                    let group = &batch.groups[fire.group as usize];
                    firings.push((
                        group.rule.clone(),
                        group
                            .variables
                            .iter()
                            .zip(fire.witnesses.iter())
                            .map(|(variable, witness)| {
                                (
                                    variable.clone(),
                                    batch.witnesses[*witness as usize].to_string(),
                                )
                            })
                            .collect(),
                    ));
                }
            }
            Schedule::Sequence(_, schedules) => {
                for schedule in schedules {
                    visit(schedule, firings);
                }
            }
            Schedule::Run(..) | Schedule::Repeat(..) | Schedule::Saturate(..) => {
                panic!("generated replay retained an automatic schedule")
            }
        }
    }

    let commands = EGraph::default().parse_program(None, source).unwrap();
    let mut firings = Vec::new();
    for command in commands {
        if let Command::RunSchedule(schedule) = command {
            visit(&schedule, &mut firings);
        }
    }
    firings
}

fn has_replay_firing(source: &str, rule: &str, bindings: &[(&str, &str)]) -> bool {
    replay_firings(source).iter().any(|(candidate, actual)| {
        candidate == rule
            && actual
                == &bindings
                    .iter()
                    .map(|(variable, witness)| ((*variable).to_owned(), (*witness).to_owned()))
                    .collect::<Vec<_>>()
    })
}

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
fn retained_only_api_matches_the_validated_slice_without_a_transcript() {
    let complete = causal_slice_program(Some("bronze.egg".to_owned()), ORIGINAL).unwrap();
    let replay = causal_slice_replay_program(Some("bronze.egg".to_owned()), ORIGINAL).unwrap();

    assert_eq!(replay.source, complete.source);
    assert_eq!(replay.rule_mapping, complete.rule_mapping);
    assert_eq!(replay.stats.full_transcript_bytes, 0);
    assert_eq!(replay.stats.sliced_bytes, complete.stats.sliced_bytes);
    assert_eq!(replay.source.matches("(run-schedule").count(), 2);
    assert!(!replay.source.contains("(seq"));

    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(Some("bronze-retained-only.egg".to_owned()), &replay.source)
        .unwrap();
}

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
    assert!(
        !replay_firings(&slice.source)
            .iter()
            .any(|(rule, _)| rule == "irrelevant")
    );

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
    assert!(has_replay_firing(
        &slice.full_transcript_source,
        "copy",
        &[("x", "1"), ("y", "10")]
    ));
    assert!(has_replay_firing(
        &slice.full_transcript_source,
        "copy",
        &[("x", "1"), ("y", "20")]
    ));

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
fn decomposable_rule_is_traced_without_changing_its_source_definition() {
    let source = r#"
        (relation A (i64))
        (relation B (i64))
        (relation C (i64))
        (relation Goal (i64))
        (rule ((A x) (B x) (C x)) ((Goal x)) :name "three-way")
        (A 1)
        (B 1)
        (C 1)
        (run 1)
        (check (Goal 1))
    "#;

    EGraph::default()
        .parse_and_run_program(Some("decomposable-rule-original.egg".to_owned()), source)
        .unwrap();

    let replay =
        causal_slice_replay_program(Some("decomposable-rule.egg".to_owned()), source).unwrap();
    assert!(has_replay_firing(
        &replay.source,
        "three-way",
        &[("x", "1")]
    ));
    assert!(!replay.source.contains(":no-decomp"));
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("decomposable-rule-replay.egg".to_owned()),
                &replay.source,
            )
            .unwrap();
    }
}

#[test]
fn projected_constructor_inputs_can_be_sliced_away_but_not_retained() {
    let common = r#"
        (datatype Expr (Int i64) (Const Expr i64 i64))
        (relation HasType (Expr i64))
        (relation Seed (i64))
        (relation Goal (i64))
        (rule ((= lhs (Const (Int i) ty ctx)))
              ((HasType lhs ty))
              :name "projected-analysis")
        (rule ((Seed x)) ((Goal x)) :name "goal")
        (Const (Int 7) 2 3)
        (Seed 1)
        (run 1)
    "#;
    let irrelevant = format!("{common}(check (Goal 1))\n");
    let replay = causal_slice_replay_program(
        Some("projected-constructor-irrelevant.egg".to_owned()),
        &irrelevant,
    )
    .unwrap();
    assert!(has_replay_firing(&replay.source, "goal", &[("x", "1")]));
    assert!(
        !replay_firings(&replay.source)
            .iter()
            .any(|(rule, _)| rule == "projected-analysis")
    );
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(
            Some("projected-constructor-replay.egg".to_owned()),
            &replay.source,
        )
        .unwrap();

    let error = causal_slice_program(
        Some("projected-constructor-full-transcript.egg".to_owned()),
        &irrelevant,
    )
    .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("diagnostic full transcript containing opaque rule groundings"),
        "{error}"
    );

    let prefix = format!("{common}(print-size HasType)\n");
    let error =
        causal_slice_replay_program(Some("projected-constructor-prefix.egg".to_owned()), &prefix)
            .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("rule `projected-analysis` was projected away"),
        "{error}"
    );

    let retained = format!("{common}(check (HasType (Const (Int 7) 2 3) 2))\n");
    let error = causal_slice_replay_program(
        Some("projected-constructor-retained.egg".to_owned()),
        &retained,
    )
    .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("rule `projected-analysis` was projected away"),
        "{error}"
    );
}

#[test]
fn projected_union_is_sliced_away_but_rejected_when_equality_depends_on_it() {
    let common = r#"
        (datatype Expr (Int i64) (Const Expr i64 i64) (Alias Expr))
        (relation Seed ())
        (relation Goal ())
        (rule ((= lhs (Const (Int i) ty ctx)))
              ((union lhs (Alias lhs)))
              :name "projected-union")
        (rule ((Seed)) ((Goal)) :name "goal")
        (let $lhs (Const (Int 7) 2 3))
        (Seed)
        (run 1)
    "#;

    let irrelevant = format!("{common}(check (Goal))\n");
    let replay = causal_slice_replay_program(
        Some("projected-union-irrelevant.egg".to_owned()),
        &irrelevant,
    )
    .unwrap();
    assert!(has_replay_firing(&replay.source, "goal", &[]));
    assert!(
        !replay_firings(&replay.source)
            .iter()
            .any(|(rule, _)| rule == "projected-union")
    );
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(
            Some("projected-union-irrelevant-replay.egg".to_owned()),
            &replay.source,
        )
        .unwrap();

    let retained = format!("{common}(check (= $lhs (Alias $lhs)))\n");
    let error =
        causal_slice_replay_program(Some("projected-union-retained.egg".to_owned()), &retained)
            .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("rule `projected-union` was projected away"),
        "{error}"
    );
}

#[test]
fn collapsed_projected_extensions_are_never_emitted_as_a_partial_selector() {
    let source = r#"
        (relation R (i64 i64))
        (relation S (i64))
        (relation Out (i64))
        (relation Seed ())
        (relation Goal ())
        (rule ((R x y) (S x)) ((Out x)) :name "projected-copy")
        (rule ((Seed)) ((Goal)) :name "goal")
        (R 1 10)
        (R 1 20)
        (S 1)
        (Seed)
        (run 1)
        (check (Goal))
    "#;

    let replay = causal_slice_replay_program(
        Some("collapsed-projected-extensions.egg".to_owned()),
        source,
    )
    .unwrap();
    assert_eq!(replay.stats.matched_applications, 2);
    assert!(has_replay_firing(&replay.source, "goal", &[]));
    assert!(
        !replay_firings(&replay.source)
            .iter()
            .any(|(rule, _)| rule == "projected-copy")
    );
}

#[test]
fn decomposed_opaque_rule_can_be_traced_and_sliced_away() {
    let source = r#"
        (datatype Expr (Node i64) (Free Expr Expr))
        (datatype Ty (Pointer i64) (State))
        (relation HasType (Expr Ty))
        (relation Seed ())
        (relation Goal ())
        (rule ((= lhs (Free e state))
               (HasType e (Pointer pointee)))
              ((HasType lhs (State)))
              :name "decomposed-analysis")
        (rule ((Seed)) ((Goal)) :name "goal")
        (let $e (Node 1))
        (let $state (Node 2))
        (HasType $e (Pointer 0))
        (Free $e $state)
        (Seed)
        (run 1)
        (check (Goal))
    "#;

    let replay =
        causal_slice_replay_program(Some("decomposed-opaque.egg".to_owned()), source).unwrap();
    assert!(has_replay_firing(&replay.source, "goal", &[]));
    assert!(
        !replay_firings(&replay.source)
            .iter()
            .any(|(rule, _)| rule == "decomposed-analysis")
    );
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(
            Some("decomposed-opaque-replay.egg".to_owned()),
            &replay.source,
        )
        .unwrap();
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
    assert!(has_replay_firing(&slice.source, "join", &[("x", "1")]));

    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("two-body-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
}

#[test]
fn broad_single_plan_rule_replays_every_grounded_premise() {
    let source = r#"
        (relation A (i64))
        (relation B (i64))
        (relation C (i64))
        (relation Goal (i64))
        (rule ((A x) (B x) (C x)) ((Goal x)) :name "broad")
        (A 1)
        (B 1)
        (C 1)
        (run 1)
        (check (Goal 1))
    "#;

    let slice = causal_slice_program(Some("broad-single-plan.egg".to_owned()), source).unwrap();
    assert_eq!(slice.stats.retained_applications, 1);
    assert!(has_replay_firing(&slice.source, "broad", &[("x", "1")]));
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("broad-single-plan-replay.egg".to_owned()),
                &slice.source,
            )
            .unwrap();
    }
}

#[test]
fn read_only_print_size_is_preserved_without_becoming_a_slice_root() {
    let source = r#"
        (relation Seed (i64))
        (relation Goal (i64))
        (relation Irrelevant (i64))
        (rule ((Seed x)) ((Goal x)) :name "goal")
        (rule ((Seed x)) ((Irrelevant x)) :name "irrelevant")
        (Seed 1)
        (run 1)
        (check (Goal 1))
        (print-size Irrelevant)
    "#;

    let slice = causal_slice_program(Some("print-size.egg".to_owned()), source).unwrap();
    assert!(slice.source.contains("(print-size Irrelevant)"));
    assert!(
        !replay_firings(&slice.source)
            .iter()
            .any(|(rule, _)| rule == "irrelevant")
    );
    EGraph::default()
        .parse_and_run_program(Some("print-size-replay.egg".to_owned()), &slice.source)
        .unwrap();
}

#[test]
fn print_only_program_uses_a_reported_effective_prefix() {
    let source = r#"
        (datatype Expr (A i64) (F Expr))
        (rewrite (F x) x)
        (F (A 1))
        (run 2)
        (print-size F)
        (print-size)
        (print-stats)
    "#;

    let mut original = EGraph::default();
    let original_outputs = original
        .parse_and_run_program(Some("print-prefix-original.egg".to_owned()), source)
        .unwrap();
    let slice = causal_slice_program(Some("print-prefix.egg".to_owned()), source).unwrap();
    let replay = causal_slice_replay_program(Some("print-prefix.egg".to_owned()), source).unwrap();
    assert_eq!(replay.source, slice.source);
    assert_eq!(replay.stats.dependency_nodes, 0);
    assert_eq!(slice.stats.prefix_fallbacks, 2);
    assert!(slice.source.contains("run-rule"));
    assert!(!slice.source.contains("(run 2)"));
    assert!(slice.source.contains("(print-stats)"));

    let mut replay = EGraph::default();
    let replay_outputs = replay
        .parse_and_run_program(Some("print-prefix-replay.egg".to_owned()), &slice.source)
        .unwrap();
    let print_sizes = |outputs: &[egglog::CommandOutput]| {
        outputs
            .iter()
            .filter_map(|output| match output {
                egglog::CommandOutput::PrintFunctionSize(size) => Some(format!("one:{size}")),
                egglog::CommandOutput::PrintAllFunctionsSize(sizes) => {
                    Some(format!("all:{sizes:?}"))
                }
                _ => None,
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(print_sizes(&original_outputs), print_sizes(&replay_outputs));

    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(Some("print-prefix-strict.egg".to_owned()), &slice.source)
        .unwrap();
}

#[test]
fn prefix_replay_rejects_an_opaque_state_effect() {
    let source = r#"
        (function F (i64) i64 :no-merge)
        (relation Trigger ())
        (rule ((Trigger))
              ((set (F 0) 7))
              :name "opaque-write")
        (Trigger)
        (run 1)
        (print-size F)
    "#;

    let error =
        causal_slice_replay_program(Some("opaque-prefix.egg".to_owned()), source).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("non-insert/union head action in rule `opaque-write`"),
        "{error}"
    );
}

#[test]
fn prefix_replay_rejects_an_effective_opaque_delete() {
    let source = r#"
        (relation R (i64))
        (relation Trigger ())
        (rule ((Trigger))
              ((delete (R 1)))
              :name "delete-r")
        (R 1)
        (Trigger)
        (run 1)
        (print-size R)
    "#;

    let outputs = EGraph::default()
        .parse_and_run_program(Some("opaque-delete-native.egg".to_owned()), source)
        .unwrap();
    assert!(
        outputs
            .iter()
            .any(|output| matches!(output, egglog::CommandOutput::PrintFunctionSize(0)))
    );

    let error =
        causal_slice_replay_program(Some("opaque-delete.egg".to_owned()), source).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("non-insert/union head action in rule `delete-r`"),
        "{error}"
    );
}

#[test]
fn prefix_replay_keeps_a_closed_zero_binding_initializer() {
    let source = r#"
        (datatype Expr (A i64))
        (relation Goal (Expr))
        (rule ()
              ((let e (A 7))
               (Goal e))
              :name "initialize")
        (run 1)
        (print-size Goal)
    "#;

    let replay =
        causal_slice_replay_program(Some("initializer-prefix.egg".to_owned()), source).unwrap();
    assert!(has_replay_firing(&replay.source, "initialize", &[]));
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("initializer-prefix-replay.egg".to_owned()),
                &replay.source,
            )
            .unwrap();
    }
}

#[test]
fn one_wave_math_fixture_prefix_replays_ordinary_and_strictly() {
    let source = include_str!("math-microbenchmark.egg").replace("(run 11)", "(run 1)");
    let slice = causal_slice_program(Some("math-one-wave.egg".to_owned()), &source).unwrap();
    assert_eq!(slice.stats.prefix_fallbacks, 3);
    assert_eq!(slice.rule_mapping.len(), 24);
    assert!(!slice.source.contains("(run 1)"));
    assert!(slice.source.contains("run-rule"));

    EGraph::default()
        .parse_and_run_program(Some("math-one-wave-replay.egg".to_owned()), &slice.source)
        .unwrap();
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(Some("math-one-wave-strict.egg".to_owned()), &slice.source)
        .unwrap();
}

#[test]
fn prefix_replay_shares_each_closed_witness_once_per_wave() {
    let term = r#"(Pair (Pair (Leaf "x") (Leaf "y")) (Pair (Leaf "x") (Leaf "y")))"#;
    let mut source = String::from(
        r#"
        (datatype Expr (Leaf String) (Pair Expr Expr))
        (relation Seed (i64 Expr))
        (relation Done (i64))
        (rule ((Seed i e)) ((Done i)) :name "copy")
        "#,
    );
    for index in 0..40 {
        source.push_str(&format!("(Seed {index} {term})\n"));
    }
    source.push_str("(run 1)\n(print-size Done)\n");

    let replay =
        causal_slice_replay_program(Some("shared-witness.egg".to_owned()), &source).unwrap();
    assert_eq!(replay.stats.shared_replay_witnesses, 1);
    let schedule = &replay.source[replay.source.find("(run-schedule").unwrap()..];
    assert_eq!(schedule.matches(term).count(), 1);
    assert!(replay.source.contains(":witnesses ("));
    assert!(replay.source.contains(":groups ((\"copy\" (i e)))"));
    assert!(!replay.source.contains("(let $__csw"));

    EGraph::default()
        .parse_and_run_program(Some("shared-witness-replay.egg".to_owned()), &replay.source)
        .unwrap();
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(
            Some("shared-witness-replay-strict.egg".to_owned()),
            &replay.source,
        )
        .unwrap();
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
    let accounted_time = slice.stats.preparation_time
        + slice.stats.traced_run_time
        + slice.stats.elaboration_time
        + slice.stats.slicing_time
        + slice.stats.emission_time
        + slice.stats.emitted_validation_time;
    assert!(slice.stats.total_time >= accounted_time);
    assert!(!slice.source.contains("(saturate"));
    assert!(!slice.source.contains("(run derive"));
    assert!(has_replay_firing(
        &slice.source,
        "seed-to-mid",
        &[("x", "2")]
    ));
    assert!(has_replay_firing(
        &slice.source,
        "mid-to-goal",
        &[("x", "2")]
    ));
    assert!(!has_replay_firing(
        &slice.source,
        "seed-to-mid",
        &[("x", "1")]
    ));
    assert!(
        !replay_firings(&slice.source)
            .iter()
            .any(|(rule, _)| rule == "irrelevant")
    );

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
fn consecutive_top_level_schedules_replay_in_chronological_waves() {
    let source = r#"
        (relation Seed (i64))
        (relation Mid (i64))
        (relation Goal (i64))
        (ruleset first)
        (ruleset second)
        (rule ((Seed x)) ((Mid x)) :ruleset first :name "seed-to-mid")
        (rule ((Mid x)) ((Goal x)) :ruleset second :name "mid-to-goal")
        (Seed 7)
        (run first 1)
        (run second 1)
        (check (Goal 7))
    "#;

    let slice = causal_slice_program(Some("two-schedules.egg".to_owned()), source).unwrap();
    assert_eq!(slice.stats.waves, 2);
    assert_eq!(slice.stats.retained_applications, 2);
    assert_eq!(
        replay_firings(&slice.source),
        vec![
            (
                "seed-to-mid".to_owned(),
                vec![("x".to_owned(), "7".to_owned())]
            ),
            (
                "mid-to-goal".to_owned(),
                vec![("x".to_owned(), "7".to_owned())]
            ),
        ]
    );
    assert!(!slice.source.contains("(run first 1)"));
    assert!(!slice.source.contains("(run second 1)"));

    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("two-schedules-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
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
    assert!(has_replay_firing(&slice.source, "build", &[("n", "7")]));
    assert!(has_replay_firing(
        &slice.source,
        "finish",
        &[("x", "(F (A 7))")]
    ));
    assert!(
        !replay_firings(&slice.source)
            .iter()
            .any(|(rule, _)| rule == "irrelevant")
    );
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
    assert!(has_replay_firing(&slice.source, "copy", &[("x", "(A 7)")]));
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("source-witness-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
}

#[test]
fn bare_eq_sort_constructor_witness_replays_ordinary_and_strictly() {
    let source = r#"
        (sort Variable)
        (constructor V (String) Variable)
        (relation Seed (String))
        (relation Done (Variable))
        (Seed "x")
        (rule ((Seed x)) ((Done (V x))) :name "build")
        (run 1)
        (check (Done (V "x")))
    "#;

    let slice = causal_slice_program(Some("bare-eq-sort.egg".to_owned()), source).unwrap();
    assert!(slice.source.contains("(sort Variable)"));
    assert!(has_replay_firing(&slice.source, "build", &[("x", "\"x\"")]));

    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("bare-eq-sort-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
}

#[test]
fn immutable_big_number_constructor_sorts_are_preserved() {
    let source = r#"
        (datatype Numeric (Z BigInt) (Q BigRat))
        (relation Seed (i64))
        (relation Done (i64))
        (Seed 1)
        (rule ((Seed x)) ((Done x)) :name "copy")
        (run 1)
        (check (Done 1))
    "#;

    let slice = causal_slice_program(Some("big-number-sorts.egg".to_owned()), source).unwrap();
    assert!(slice.source.contains("(Z BigInt)"));
    assert!(slice.source.contains("(Q BigRat)"));
    assert!(has_replay_firing(&slice.source, "copy", &[("x", "1")]));

    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("big-number-sorts-replay.egg".to_owned()),
                &slice.source,
            )
            .unwrap();
    }
}

#[test]
fn constructor_global_with_bigrat_child_replays_ordinary_and_strictly() {
    let source = r#"
        (datatype Math (Num BigRat) (Neg Math))
        (relation Done (BigRat))
        (let $zero (Num (bigrat (bigint 0) (bigint 1))))
        (let $neg-zero (Neg $zero))
        (rule ((= x (Num n))) ((Done n)) :name "copy-number")
        (run 1)
        (check (Done n))
    "#;

    let slice = causal_slice_program(Some("bigrat-global.egg".to_owned()), source).unwrap();
    assert!(slice.source.contains("(let $zero (Num (bigrat"));
    assert!(slice.source.contains("(let $neg-zero (Neg $zero))"));
    assert!(
        replay_firings(&slice.source)
            .iter()
            .any(|(rule, _)| rule == "copy-number")
    );

    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("bigrat-global-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
}

#[test]
fn constructor_global_rejects_arbitrary_primitives() {
    let source = r#"
        (datatype Math (Num BigRat))
        (let $bad
          (Num (+ (bigrat (bigint 1) (bigint 1))
                  (bigrat (bigint 2) (bigint 1)))))
        (run 1)
        (print-size Math)
    "#;

    let error = causal_slice_program(Some("primitive-global.egg".to_owned()), source).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("primitive or function `+` in a source global expression")
    );
}

#[test]
fn retained_bigrat_add_in_a_complete_head_replays_strictly() {
    let source = r#"
        (datatype Math (Num BigRat))
        (relation Inputs (Math Math))
        (relation Done (Math))
        (let $one (Num (bigrat (bigint 1) (bigint 1))))
        (let $two (Num (bigrat (bigint 2) (bigint 1))))
        (let $three (Num (bigrat (bigint 3) (bigint 1))))
        (Inputs $one $two)
        (rule ((Inputs x y)
               (= x (Num a))
               (= y (Num b)))
              ((Done (Num (+ a b))))
              :name "fold-add"
              :no-decomp)
        (run 1)
        (check (Done $three))
    "#;

    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("bigrat-add-native.egg".to_owned()), source)
            .unwrap();
    }

    let slice = causal_slice_program(Some("bigrat-add.egg".to_owned()), source).unwrap();
    assert!(
        replay_firings(&slice.source)
            .iter()
            .any(|(rule, _)| rule == "fold-add")
    );
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("bigrat-add-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
}

#[test]
fn retained_bigrat_binary_arithmetic_replays_strictly() {
    for (operator, lhs, rhs, result_numerator, result_denominator) in
        [("-", 3, 1, 2, 1), ("*", 2, 3, 6, 1), ("/", 3, 2, 3, 2)]
    {
        let source = format!(
            r#"
                (datatype Math (Num BigRat))
                (relation Inputs (Math Math))
                (relation Done (Math))
                (let $lhs (Num (bigrat (bigint {lhs}) (bigint 1))))
                (let $rhs (Num (bigrat (bigint {rhs}) (bigint 1))))
                (let $result
                  (Num (bigrat (bigint {result_numerator}) (bigint {result_denominator}))))
                (Inputs $lhs $rhs)
                (rule ((Inputs x y)
                       (= x (Num a))
                       (= y (Num b)))
                      ((Done (Num ({operator} a b))))
                      :name "fold-binary"
                      :no-decomp)
                (run 1)
                (check (Done $result))
            "#
        );
        for make_egraph in [EGraph::default, || {
            EGraph::new_with_proofs().with_proof_testing()
        }] {
            make_egraph()
                .parse_and_run_program(Some(format!("bigrat-{operator}-native.egg")), &source)
                .unwrap();
        }

        let slice = causal_slice_program(Some(format!("bigrat-{operator}.egg")), &source).unwrap();
        assert!(
            replay_firings(&slice.source)
                .iter()
                .any(|(rule, _)| rule == "fold-binary")
        );
        for make_egraph in [EGraph::default, || {
            EGraph::new_with_proofs().with_proof_testing()
        }] {
            make_egraph()
                .parse_and_run_program(Some(format!("bigrat-{operator}-replay.egg")), &slice.source)
                .unwrap();
        }
    }
}

#[test]
fn retained_bigrat_unary_arithmetic_replays_strictly() {
    let source = r#"
        (datatype Math (Num BigRat))
        (relation Inputs (Math))
        (relation Done (Math))
        (let $two (Num (bigrat (bigint 2) (bigint 1))))
        (let $negative-two (Num (bigrat (bigint -2) (bigint 1))))
        (Inputs $two)
        (rule ((Inputs x) (= x (Num value)))
              ((Done (Num (neg value))))
              :name "fold-neg"
              :no-decomp)
        (run 1)
        (check (Done $negative-two))
    "#;
    let slice = causal_slice_program(Some("bigrat-neg.egg".to_owned()), source).unwrap();
    assert!(
        replay_firings(&slice.source)
            .iter()
            .any(|(rule, _)| rule == "fold-neg")
    );
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("bigrat-neg-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
}

#[test]
fn pure_i64_query_primitive_replays_its_complete_grounding() {
    let source = r#"
        (datatype Math (Num i64))
        (relation Inputs (Math Math))
        (relation Done (Math))
        (let $two (Num 2))
        (let $three (Num 3))
        (let $five (Num 5))
        (Inputs $two $three)
        (rule ((Inputs x y)
               (= x (Num a))
               (= y (Num b))
               (= result (+ a b)))
              ((Done (Num result)))
              :name "fold-add"
              :no-decomp)
        (run 1)
        (check (Done $five))
    "#;

    let slice = causal_slice_program(Some("i64-query-add.egg".to_owned()), source).unwrap();
    let firing = replay_firings(&slice.source)
        .into_iter()
        .find(|(rule, _)| rule == "fold-add")
        .expect("retained query primitive firing");
    assert!(
        firing
            .1
            .iter()
            .any(|(variable, witness)| variable == "result" && witness == "5")
    );
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("i64-query-add-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
}

#[test]
fn pure_bigrat_query_replays_with_exact_postfilter_grounding() {
    let source = r#"
        (datatype Math (Num BigRat))
        (relation Inputs (Math Math))
        (relation Done (Math))
        (let $two (Num (bigrat (bigint 2) (bigint 1))))
        (let $three (Num (bigrat (bigint 3) (bigint 1))))
        (let $eight (Num (bigrat (bigint 8) (bigint 1))))
        (let $zero (Num (bigrat (bigint 0) (bigint 1))))
        (let $negative-one (Num (bigrat (bigint -1) (bigint 1))))
        (Inputs $two $three)
        (Inputs $zero $negative-one)
        (rule ((Inputs x y)
               (= x (Num a))
               (= y (Num b))
               (= result (pow a b)))
              ((Done (Num result)))
              :name "fold-pow"
              :no-decomp)
        (run 1)
        (check (Done $eight))
    "#;

    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("bigrat-pow-native.egg".to_owned()), source)
            .unwrap();
    }

    let slice = causal_slice_program(Some("bigrat-pow.egg".to_owned()), source).unwrap();
    let firing = replay_firings(&slice.source)
        .into_iter()
        .find(|(rule, _)| rule == "fold-pow")
        .expect("retained query primitive firing");
    assert_eq!(
        replay_firings(&slice.source)
            .iter()
            .filter(|(rule, _)| rule == "fold-pow")
            .count(),
        1,
        "the failed pow candidate must not become a replay firing"
    );
    assert!(firing.1.iter().any(|(variable, _)| variable == "result"));
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("bigrat-pow-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
}

#[test]
fn pure_bigrat_log_query_replays_only_the_successful_grounding() {
    let source = r#"
        (datatype Math (Num BigRat))
        (relation Inputs (Math))
        (relation Done (Math))
        (let $zero (Num (bigrat (bigint 0) (bigint 1))))
        (let $one (Num (bigrat (bigint 1) (bigint 1))))
        (let $two (Num (bigrat (bigint 2) (bigint 1))))
        (Inputs $one)
        (Inputs $two)
        (rule ((Inputs x)
               (= x (Num value))
               (= result (log value)))
              ((Done (Num result)))
              :name "fold-log"
              :no-decomp)
        (run 1)
        (check (Done $zero))
    "#;
    let slice = causal_slice_program(Some("bigrat-log.egg".to_owned()), source).unwrap();
    let firings = replay_firings(&slice.source)
        .into_iter()
        .filter(|(rule, _)| rule == "fold-log")
        .collect::<Vec<_>>();
    assert_eq!(firings.len(), 1);
    assert!(
        firings[0]
            .1
            .iter()
            .any(|(variable, _)| variable == "result")
    );
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("bigrat-log-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
}

#[test]
fn pure_bigrat_predicate_replays_only_the_successful_grounding() {
    let source = r#"
        (datatype Math (Num BigRat))
        (relation Inputs (Math))
        (relation Done (Math))
        (let $zero (Num (bigrat (bigint 0) (bigint 1))))
        (let $one (Num (bigrat (bigint 1) (bigint 1))))
        (let $negative-one (Num (bigrat (bigint -1) (bigint 1))))
        (Inputs $one)
        (Inputs $negative-one)
        (rule ((Inputs x)
               (= x (Num value))
               (> value (bigrat (bigint 0) (bigint 1))))
              ((Done x))
              :name "keep-positive"
              :no-decomp)
        (run 1)
        (check (Done $one))
    "#;
    let slice = causal_slice_program(Some("bigrat-predicate.egg".to_owned()), source).unwrap();
    assert_eq!(
        replay_firings(&slice.source)
            .iter()
            .filter(|(rule, _)| rule == "keep-positive")
            .count(),
        1
    );
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("bigrat-predicate-replay.egg".to_owned()),
                &slice.source,
            )
            .unwrap();
    }
}

#[test]
fn retained_bigrat_add_in_a_union_head_replays_strictly() {
    let source = r#"
        (datatype Math (Num BigRat) (Alias BigRat))
        (relation Inputs (Math Math Math))
        (let $one (Num (bigrat (bigint 1) (bigint 1))))
        (let $two (Num (bigrat (bigint 2) (bigint 1))))
        (let $actual (Num (bigrat (bigint 3) (bigint 1))))
        (let $expected (Alias (bigrat (bigint 3) (bigint 1))))
        (Inputs $one $two $expected)
        (rule ((Inputs x y target)
               (= x (Num a))
               (= y (Num b)))
              ((union (Num (+ a b)) target))
              :name "fold-add-union"
              :no-decomp)
        (run 1)
        (check (= $actual $expected))
    "#;

    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("bigrat-add-union-native.egg".to_owned()), source)
            .unwrap();
    }

    let slice = causal_slice_program(Some("bigrat-add-union.egg".to_owned()), source).unwrap();
    assert!(
        replay_firings(&slice.source)
            .iter()
            .any(|(rule, _)| rule == "fold-add-union")
    );
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("bigrat-add-union-replay.egg".to_owned()),
                &slice.source,
            )
            .unwrap();
    }
}

#[test]
fn integer_add_in_a_rule_head_remains_unsupported() {
    let source = r#"
        (relation Input (i64 i64))
        (relation Output (i64))
        (Input 1 2)
        (rule ((Input a b))
              ((Output (+ a b)))
              :name "integer-add")
        (run 1)
        (check (Output 3))
    "#;

    let error = causal_slice_program(Some("integer-add.egg".to_owned()), source).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("nested non-constructor call `+` in rule head"),
        "{error}"
    );
}

#[test]
fn bigrat_add_result_without_a_preexisting_term_fails_closed() {
    let source = r#"
        (datatype Math (Num BigRat))
        (relation Inputs (Math Math))
        (relation Done (Math))
        (let $one (Num (bigrat (bigint 1) (bigint 1))))
        (let $two (Num (bigrat (bigint 2) (bigint 1))))
        (Inputs $one $two)
        (rule ((Inputs x y)
               (= x (Num a))
               (= y (Num b)))
              ((Done (Num (+ a b))))
              :name "fold-add"
              :no-decomp)
        (run 1)
        (check (Done result))
    "#;

    EGraph::default()
        .parse_and_run_program(Some("bigrat-add-new-result-native.egg".to_owned()), source)
        .unwrap();
    let error =
        causal_slice_program(Some("bigrat-add-new-result.egg".to_owned()), source).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("BigRat `+` result without a preexisting replay witness"),
        "{error}"
    );
}

#[test]
fn constructor_global_rejects_unprintable_bigints() {
    let source = r#"
        (datatype Math (Num BigRat))
        (relation Marker ())
        (let $too-big
          (Num (bigrat (from-string "9223372036854775808") (bigint 1))))
        (Marker)
        (run 1)
        (check (Marker))
    "#;

    let error =
        causal_slice_program(Some("large-bigint-global.egg".to_owned()), source).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("a BigInt witness outside the replayable i64 range"),
        "{error}"
    );
}

#[test]
fn dynamic_global_references_replay_without_becoming_rule_bindings() {
    let source = r#"
        (datatype Math (Num BigRat) (Neg Math))
        (relation Seed (Math i64))
        (relation Done (Math i64))
        (let $zero (Num (bigrat (bigint 0) (bigint 1))))
        (let $neg-zero (Neg $zero))
        (Seed $zero 7)
        (rule ((Seed $zero n))
              ((Done $neg-zero n))
              :name "use-globals"
              :no-decomp)
        (run 1)
        (check (Done $neg-zero 7))
    "#;

    EGraph::default()
        .parse_and_run_program(Some("dynamic-global-native.egg".to_owned()), source)
        .unwrap();

    let slice = causal_slice_program(Some("dynamic-global.egg".to_owned()), source).unwrap();
    assert!(has_replay_firing(
        &slice.source,
        "use-globals",
        &[("n", "7")]
    ));
    assert!(!slice.source.contains("(($zero "));
    assert!(!slice.source.contains("(($neg-zero "));

    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("dynamic-global-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
}

#[test]
fn legacy_unprefixed_global_replays_without_becoming_a_rule_binding() {
    let source = r#"
        (datatype Expr (A))
        (relation Seed (Expr i64))
        (relation Done (Expr i64))
        (let ZERO (A))
        (Seed ZERO 7)
        (rule ((Seed ZERO n)) ((Done ZERO n)) :name "use-global" :no-decomp)
        (run 1)
        (check (Done ZERO 7))
    "#;

    EGraph::default()
        .parse_and_run_program(Some("legacy-global-native.egg".to_owned()), source)
        .unwrap();
    let slice = causal_slice_program(Some("legacy-global.egg".to_owned()), source).unwrap();
    assert!(slice.source.contains("(let ZERO (A))"));
    assert!(has_replay_firing(
        &slice.source,
        "use-global",
        &[("n", "7")]
    ));
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("legacy-global-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
}

#[test]
fn dynamic_global_references_replay_through_rewrite_lookup_and_union() {
    let source = r#"
        (datatype Math (Num BigRat) (Neg Math))
        (let $zero (Num (bigrat (bigint 0) (bigint 1))))
        (Neg $zero)
        (rewrite (Neg $zero) $zero :name "fold-neg-zero")
        (run 1)
        (check (= (Neg $zero) $zero))
    "#;

    let slice =
        causal_slice_program(Some("dynamic-global-rewrite.egg".to_owned()), source).unwrap();
    let firing = replay_firings(&slice.source)
        .into_iter()
        .find(|(rule, _)| rule.starts_with("__causal_slice_v0_rw_b"))
        .expect("the global rewrite should be retained");
    assert!(firing.1.is_empty(), "globals must not become bindings");

    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("dynamic-global-rewrite-replay.egg".to_owned()),
                &slice.source,
            )
            .unwrap();
    }
}

#[test]
fn dynamic_global_references_fail_closed_on_unknown_or_wrong_sort() {
    let unknown = r#"
        (datatype Math (Num i64))
        (relation Seed (Math))
        (Seed $missing)
        (run 1)
        (check (Seed x))
    "#;
    let error = causal_slice_program(Some("unknown-global.egg".to_owned()), unknown).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("non-ground source initialization variable `$missing`"),
        "{error}"
    );

    let wrong_sort = r#"
        (datatype Math (Num i64))
        (relation Seed (i64))
        (let $zero (Num 0))
        (Seed $zero)
        (run 1)
        (check (Seed 0))
    "#;
    let error =
        causal_slice_program(Some("wrong-sort-global.egg".to_owned()), wrong_sort).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("source global `$zero` has sort `Math` instead of `i64`"),
        "{error}"
    );
}

#[test]
fn dollar_prefixed_local_shadowed_by_a_later_global_fails_closed() {
    let source = r#"
        (datatype Math (Num i64))
        (relation Seed (i64))
        (relation Done (i64))
        (rule ((Seed $a)) ((Done $a)) :name "copy")
        (Seed 7)
        (let $a (Num 0))
        (run 1)
        (check (Done 7))
    "#;

    EGraph::default()
        .parse_and_run_program(Some("local-before-global-native.egg".to_owned()), source)
        .unwrap();
    let error =
        causal_slice_program(Some("local-before-global.egg".to_owned()), source).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("source global `$a` shadowing an earlier local rule variable"),
        "{error}"
    );
}

#[test]
fn unprefixed_local_shadowed_by_a_later_global_fails_closed() {
    let source = r#"
        (datatype Expr (A))
        (relation Seed (i64))
        (relation Done (i64))
        (rule ((Seed value)) ((Done value)) :name "copy")
        (Seed 7)
        (let value (A))
        (run 1)
        (check (Done 7))
    "#;

    EGraph::default()
        .parse_and_run_program(Some("legacy-shadow-native.egg".to_owned()), source)
        .unwrap();
    let error = causal_slice_program(Some("legacy-shadow.egg".to_owned()), source).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("source global `value` shadowing an earlier local rule variable"),
        "{error}"
    );
}

#[test]
fn dynamic_global_can_be_a_constructor_lookup_output() {
    let source = r#"
        (datatype Expr (A))
        (relation Seed (i64))
        (relation Done (i64))
        (let $a (A))
        (Seed 7)
        (rule ((Seed n) (= (A) $a))
              ((Done n))
              :name "read-global"
              :no-decomp)
        (run 1)
        (check (Done 7))
    "#;

    let slice = causal_slice_program(Some("global-lookup-output.egg".to_owned()), source).unwrap();
    assert!(has_replay_firing(
        &slice.source,
        "read-global",
        &[("n", "7")]
    ));
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(
            Some("global-lookup-output-replay.egg".to_owned()),
            &slice.source,
        )
        .unwrap();
}

#[test]
fn dynamic_global_uses_the_match_time_endpoint_after_an_earlier_union() {
    let source = r#"
        (datatype Expr (A) (B))
        (relation Tick (i64))
        (B)
        (let $a (A))
        (Tick 0)
        (rule ((Tick n))
              ((union (B) $a))
              :name "merge-global"
              :no-decomp)
        (run 2)
        (check (= (A) (B)))
    "#;

    EGraph::default()
        .parse_and_run_program(Some("global-after-union-native.egg".to_owned()), source)
        .unwrap();
    let slice = causal_slice_program(Some("global-after-union.egg".to_owned()), source).unwrap();
    assert_eq!(
        replay_firings(&slice.source)
            .iter()
            .filter(|(rule, _)| rule == "merge-global")
            .count(),
        1,
        "the redundant second-wave union must not be retained"
    );
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(
            Some("global-after-union-replay.egg".to_owned()),
            &slice.source,
        )
        .unwrap();
}

#[test]
fn dynamic_global_endpoint_change_retains_its_equality_cause() {
    let source = r#"
        (datatype Expr (A) (B))
        (relation Seed (i64))
        (relation Ready (i64))
        (relation Done (Expr))
        (B)
        (let $a (A))
        (Seed 0)
        (rule ((Seed n)) ((union (B) $a)) :name "merge-global")
        (rule ((Seed n)) ((Ready n)) :name "ready")
        (rule ((Ready n)) ((Done $a)) :name "use-global")
        (run 2)
        (check (Done (B)))
    "#;

    let slice =
        causal_slice_program(Some("global-equality-dependency.egg".to_owned()), source).unwrap();
    assert!(
        replay_firings(&slice.source)
            .iter()
            .any(|(rule, _)| rule == "merge-global"),
        "the earlier union is required to reproduce the later global endpoint"
    );
    assert!(has_replay_firing(&slice.source, "ready", &[("n", "0")]));
    assert!(has_replay_firing(
        &slice.source,
        "use-global",
        &[("n", "0")]
    ));

    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("global-equality-dependency-replay.egg".to_owned()),
                &slice.source,
            )
            .unwrap();
    }
}

#[test]
fn inert_container_sort_declaration_is_preserved() {
    let source = r#"
        (sort Values (Vec i64))
        (relation Seed ())
        (Seed)
        (run 1)
        (check (Seed))
    "#;

    let slice = causal_slice_program(Some("container-presort.egg".to_owned()), source).unwrap();
    assert!(slice.source.contains("(sort Values (Vec i64))"));
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("container-presort-replay.egg".to_owned()),
                &slice.source,
            )
            .unwrap();
    }
}

#[test]
fn container_sort_is_allowed_in_inert_table_schemas() {
    let source = r#"
        (sort Values (Vec i64))
        (sort Entry (Pair String i64))
        (datatype Expr (Unused Values))
        (sort Members (Set Expr))
        (constructor UnusedEntry (Entry) Expr)
        (constructor UnusedMembers (Members) Expr)
        (relation Opaque (Values Entry Members))
        (function score (Values) Entry :merge old)
        (function members (i64) Members :merge old)
        (relation Seed ())
        (Seed)
        (run 1)
        (check (Seed))
    "#;

    let slice = causal_slice_program(Some("container-schema.egg".to_owned()), source).unwrap();
    assert!(slice.source.contains("(datatype Expr (Unused Values))"));
    assert!(
        slice
            .source
            .contains("(constructor UnusedEntry (Entry) Expr)")
    );
    assert!(
        slice
            .source
            .contains("(constructor UnusedMembers (Members) Expr)")
    );
    assert!(
        slice
            .source
            .contains("(relation Opaque (Values Entry Members))")
    );
    assert!(
        slice
            .source
            .contains("(function score (Values) Entry :merge old)")
    );
    assert!(
        slice
            .source
            .contains("(function members (i64) Members :merge old)")
    );
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("container-schema-replay.egg".to_owned()),
                &slice.source,
            )
            .unwrap();
    }
}

#[test]
fn unstable_fn_sort_is_preserved_only_in_inert_schemas() {
    let inert_source = r#"
        (sort Callback (UnstableFn (i64) i64))
        (relation Opaque (Callback))
        (relation Seed ())
        (Seed)
        (run 1)
        (check (Seed))
    "#;

    let slice =
        causal_slice_program(Some("inert-unstable-fn.egg".to_owned()), inert_source).unwrap();
    assert!(
        slice
            .source
            .contains("(sort Callback (UnstableFn (i64) i64))")
    );
    assert!(slice.source.contains("(relation Opaque (Callback))"));
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("inert-unstable-fn-replay.egg".to_owned()),
                &slice.source,
            )
            .unwrap();
    }

    let dynamic_source = r#"
        (sort Callback (UnstableFn (i64) i64))
        (relation HasCallback (Callback))
        (relation Seed ())
        (rule ((HasCallback callback)) ((Seed)) :name "read-callback")
        (Seed)
        (run 1)
        (check (Seed))
    "#;
    let replay =
        causal_slice_replay_program(Some("dynamic-unstable-fn.egg".to_owned()), dynamic_source)
            .unwrap();
    assert!(
        !replay_firings(&replay.source)
            .iter()
            .any(|(rule, _)| rule == "read-callback")
    );
}

#[test]
fn container_values_remain_an_explicit_runtime_boundary() {
    let relation_use = r#"
        (sort Values (Vec i64))
        (relation HasValues (Values))
        (relation Seed ())
        (rule ((HasValues items)) ((Seed)) :name "read-values")
        (Seed)
        (run 1)
        (check (Seed))
    "#;
    let replay =
        causal_slice_replay_program(Some("container-relation-use.egg".to_owned()), relation_use)
            .unwrap();
    assert!(
        !replay_firings(&replay.source)
            .iter()
            .any(|(rule, _)| rule == "read-values")
    );

    let constructor_use = r#"
        (sort Values (Vec i64))
        (datatype Expr (Call Values))
        (relation Goal (Expr))
        (Goal (Call (vec-of 1)))
        (run 1)
        (check (Goal value))
    "#;
    let error = causal_slice_program(
        Some("container-constructor-use.egg".to_owned()),
        constructor_use,
    )
    .unwrap_err();
    assert!(
        error.to_string().contains(
            "constructor `Call` with opaque container sort `Values` in source initialization"
        ),
        "{error}"
    );

    let check_use = r#"
        (sort Values (Vec i64))
        (relation HasValues (Values))
        (run 1)
        (check (HasValues item))
    "#;
    let error =
        causal_slice_program(Some("container-check-use.egg".to_owned()), check_use).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("relation `HasValues` with opaque container sort `Values` in positive check"),
        "{error}"
    );
}

#[test]
fn unregistered_container_presorts_remain_an_explicit_boundary() {
    let source = r#"
        (sort Values (UnknownContainer i64 i64))
        (relation Seed ())
        (Seed)
        (run 1)
        (check (Seed))
    "#;

    let error = causal_slice_program(Some("unknown-presort.egg".to_owned()), source).unwrap_err();
    assert!(error.to_string().contains("custom sorts"), "{error}");
}

#[test]
fn inert_custom_function_declaration_is_preserved_without_state_provenance() {
    let source = r#"
        (function hi (i64) i64 :merge (min old new))
        (relation Seed (i64))
        (relation Done (i64))
        (Seed 7)
        (rule ((Seed n)) ((Done n)) :name "copy")
        (run 1)
        (check (Done 7))
    "#;

    let slice = causal_slice_program(Some("inert-function.egg".to_owned()), source).unwrap();
    assert!(
        slice
            .source
            .contains("(function hi (i64) i64 :merge (min old new))")
    );
    assert!(has_replay_firing(&slice.source, "copy", &[("n", "7")]));
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("inert-function-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
}

#[test]
fn combined_ruleset_declarations_are_preserved_for_tracing() {
    let source = r#"
        (ruleset first)
        (ruleset second)
        (relation Seed (i64))
        (relation Middle (i64))
        (relation Goal (i64))
        (rule ((Seed x)) ((Middle x)) :ruleset first :name "first-rule")
        (rule ((Middle x)) ((Goal x)) :ruleset second :name "second-rule")
        (unstable-combined-ruleset both first second)
        (Seed 1)
        (run both 3)
        (check (Goal 1))
    "#;

    let replay =
        causal_slice_replay_program(Some("combined-ruleset.egg".to_owned()), source).unwrap();
    assert!(
        replay
            .source
            .contains("(unstable-combined-ruleset both first second)")
    );
    assert!(has_replay_firing(
        &replay.source,
        "first-rule",
        &[("x", "1")]
    ));
    assert!(has_replay_firing(
        &replay.source,
        "second-rule",
        &[("x", "1")]
    ));
    assert!(!replay.source.contains("(run both 3)"));

    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("combined-ruleset-replay.egg".to_owned()),
                &replay.source,
            )
            .unwrap();
    }
}

#[test]
fn custom_function_state_use_remains_an_explicit_boundary() {
    let source = r#"
        (function hi (i64) i64 :merge (min old new))
        (relation Seed (i64))
        (Seed 7)
        (rule ((Seed n)) ((set (hi 0) n)) :name "write-hi")
        (run 1)
        (check (= (hi 0) 7))
    "#;

    let error = causal_slice_program(Some("dynamic-function.egg".to_owned()), source).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("equality or primitive function lookup `hi` in positive check"),
        "{error}"
    );
}

#[test]
fn irrelevant_unsupported_rule_is_deferred_past_backward_slicing() {
    let source = r#"
        (function F (i64) i64 :no-merge)
        (relation Seed (i64))
        (relation Trigger ())
        (relation Goal (i64))
        (rule ((Seed n)) ((Goal n)) :name "goal")
        (rule ((Trigger)) ((set (F 0) 7)) :name "opaque-write")
        (Seed 7)
        (Trigger)
        (run 1)
        (check (Goal 7))
    "#;

    let replay =
        causal_slice_replay_program(Some("opaque-irrelevant.egg".to_owned()), source).unwrap();
    assert!(has_replay_firing(&replay.source, "goal", &[("n", "7")]));
    assert!(
        !replay_firings(&replay.source)
            .iter()
            .any(|(rule, _)| rule == "opaque-write")
    );
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(
            Some("opaque-irrelevant-replay.egg".to_owned()),
            &replay.source,
        )
        .unwrap();
}

#[test]
fn retained_unsupported_rule_fails_after_backward_slicing() {
    let source = r#"
        (function F (i64) i64 :no-merge)
        (relation Trigger ())
        (relation Goal (i64))
        (rule ((Trigger))
              ((set (F 0) 7) (Goal 7))
              :name "opaque-producer")
        (Trigger)
        (run 1)
        (check (Goal 7))
    "#;

    let error =
        causal_slice_replay_program(Some("opaque-retained.egg".to_owned()), source).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("non-insert/union head action in rule `opaque-producer`"),
        "{error}"
    );
}

#[test]
fn opaque_empty_body_constructor_initializer_replays_with_no_bindings() {
    let source = r#"
        (datatype Expr (A i64))
        (relation Goal (Expr))
        (function Len (Expr) i64 :no-merge)
        (ruleset initialize-rules)
        (ruleset later)
        (rule ()
              ((let e (A 7))
               (Goal e))
              :ruleset initialize-rules
              :name "initialize")
        (rule ()
              ((set (Len (A 7)) 1))
              :ruleset later
              :name "unsupported-later")
        (run initialize-rules 1)
        (run later 1)
        (check (Goal (A 7)))
    "#;

    let replay =
        causal_slice_replay_program(Some("opaque-initializer.egg".to_owned()), source).unwrap();
    assert!(has_replay_firing(&replay.source, "initialize", &[]));
    assert!(
        !replay_firings(&replay.source)
            .iter()
            .any(|(rule, _)| rule == "unsupported-later")
    );
    assert_eq!(replay.stats.retained_applications, 1);
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("opaque-initializer-replay.egg".to_owned()),
                &replay.source,
            )
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
    assert!(has_replay_firing(&slice.source, "build", &[("x", "\"x\"")]));
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
fn unextractable_constructor_witness_replays_without_extraction() {
    let source = r#"
        (sort E)
        (constructor U (i64) E :unextractable)
        (relation Seed (E))
        (relation Goal (E))
        (Seed (U 7))
        (rule ((Seed e)) ((Goal e)) :name "copy" :no-decomp)
        (run 1)
        (check (Goal (U 7)))
    "#;

    let slice =
        causal_slice_program(Some("unextractable-constructor.egg".to_owned()), source).unwrap();
    assert!(
        slice
            .source
            .contains("(constructor U (i64) E :unextractable)")
    );
    assert!(has_replay_firing(&slice.source, "copy", &[("e", "(U 7)")]));
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("unextractable-constructor-replay.egg".to_owned()),
                &slice.source,
            )
            .unwrap();
    }
}

#[test]
fn mutually_recursive_datatype_star_replays_ordinary_and_strictly() {
    let source = r#"
        (datatype*
            (Tree (Leaf i64) (Children Forest))
            (Forest (Nil) (Cons Tree Forest)))
        (relation Seed (Tree))
        (relation Done (Tree))
        (Seed (Children (Cons (Leaf 1) (Nil))))
        (rule ((Seed tree)) ((Done tree)) :name "copy-tree")
        (run 1)
        (check (Done (Children (Cons (Leaf 1) (Nil)))))
    "#;

    let slice = causal_slice_program(Some("datatype-star.egg".to_owned()), source).unwrap();
    assert!(slice.source.contains("(datatype*"));
    assert!(has_replay_firing(
        &slice.source,
        "copy-tree",
        &[("tree", "(Children (Cons (Leaf 1) (Nil)))")]
    ));
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("datatype-star-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
}

#[test]
fn datatype_star_unregistered_presorts_remain_an_explicit_boundary() {
    let source = r#"
        (datatype*
            (Node (Leaf i64))
            (sort Mapping (UnknownContainer i64 i64)))
        (relation Seed ())
        (Seed)
        (run 1)
        (check (Seed))
    "#;

    let error =
        causal_slice_program(Some("datatype-star-unknown.egg".to_owned()), source).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("datatype* sort `Mapping` with unsupported presort `UnknownContainer`"),
        "{error}"
    );
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
    assert!(has_replay_firing(
        &slice.source,
        "unify",
        &[("x", "(A 1)"), ("y", "(A 2)")]
    ));
    assert!(
        !replay_firings(&slice.source)
            .iter()
            .any(|(rule, _)| rule == "redundant")
    );

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
fn retained_constructor_subsume_side_effect_replays_in_one_shared_wave() {
    let source = r#"
        (datatype Expr (A i64) (B i64))
        (relation Peer (i64))
        (ruleset fold)
        (rule ((= e (A x)))
              ((union e (B x)) (subsume (A x)))
              :ruleset fold
              :name "fold-and-hide")
        (rule ((= e (A x)))
              ((Peer x))
              :ruleset fold
              :name "peer")
        (let $a (A 1))
        (run-schedule (run fold))
        (check (= $a (B 1)))
        (check (Peer 1))
    "#;

    let slice = causal_slice_program(Some("subsume-side-effect.egg".to_owned()), source).unwrap();
    assert!(slice.source.contains("(subsume (A x))"));
    assert_eq!(slice.stats.equality_edges, 1);
    assert_eq!(slice.stats.retained_applications, 2);
    assert!(
        has_replay_firing(
            &slice.source,
            "fold-and-hide",
            &[("x", "1"), ("e", "(A 1)")]
        ),
        "{:?}",
        replay_firings(&slice.source)
    );
    assert!(has_replay_firing(
        &slice.source,
        "peer",
        &[("x", "1"), ("e", "(A 1)")]
    ));

    let replay_with_visibility_guard = format!(
        "{}\n(run-schedule (run-rule \"peer\" :bind ((x 1) (e (A 1))) :expect 0))",
        slice.source
    );
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("subsume-side-effect-replay.egg".to_owned()),
                &replay_with_visibility_guard,
            )
            .unwrap();
    }
}

#[test]
fn constructor_subsume_requires_an_exact_alias_when_retained() {
    let non_alias = r#"
        (datatype Expr (A i64) (B i64))
        (rule ((= e (A x)))
              ((union e (B x)) (subsume (B x)))
              :name "non-alias")
        (let $a (A 1))
        (run 1)
        (check (= $a (B 1)))
    "#;
    let error =
        causal_slice_program(Some("subsume-non-alias.egg".to_owned()), non_alias).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("does not exactly alias a live body constructor lookup"),
        "{error}"
    );

    let no_independent_union = r#"
        (datatype Expr (A i64))
        (relation Goal ())
        (rule ((= e (A x)))
              ((subsume (A x)))
              :name "hide-only")
        (rule () ((Goal)) :name "goal")
        (A 1)
        (run 1)
        (check (Goal))
    "#;
    let replay = causal_slice_replay_program(
        Some("subsume-without-union.egg".to_owned()),
        no_independent_union,
    )
    .unwrap();
    assert!(
        !replay_firings(&replay.source)
            .iter()
            .any(|(rule, _)| rule == "hide-only")
    );
    EGraph::new_with_proofs()
        .with_proof_testing()
        .parse_and_run_program(
            Some("subsume-without-union-replay.egg".to_owned()),
            &replay.source,
        )
        .unwrap();
}

#[test]
fn anonymous_rewrite_lowers_to_one_stable_strictly_replayable_rule() {
    let source = r#"
        (datatype Expr (A i64) (F Expr))
        (relation Seed (Expr))
        (Seed (F (A 1)))
        (rewrite (F x) x)
        (run 1)
        (check (= (F (A 1)) (A 1)))
    "#;

    let first = causal_slice_program(Some("rewrite.egg".to_owned()), source).unwrap();
    let second = causal_slice_program(Some("rewrite.egg".to_owned()), source).unwrap();
    assert_eq!(first.source, second.source);
    assert_eq!(first.rule_mapping.len(), 1);
    assert_eq!(first.rule_mapping[0].source_command_index, 3);
    assert!(first.rule_mapping[0].original_name.is_none());
    assert!(
        first.rule_mapping[0]
            .registered_name
            .starts_with("__causal_slice_v0_rw_b")
    );
    assert!(!first.source.contains("(rewrite"));
    let firings = replay_firings(&first.source);
    assert_eq!(firings.len(), 1);
    assert_eq!(firings[0].0, first.rule_mapping[0].registered_name);
    assert!(
        firings[0]
            .1
            .iter()
            .all(|(variable, _)| !variable.contains("__causal_slice_v0_root"))
    );
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("rewrite-replay.egg".to_owned()), &first.source)
            .unwrap();
    }
}

#[test]
fn one_birewrite_maps_to_two_distinct_registered_rules() {
    let source = r#"
        (datatype Expr (A i64) (F Expr) (G Expr))
        (relation Seed (Expr))
        (Seed (F (A 1)))
        (birewrite (F x) (G x))
        (run 1)
        (check (= (F (A 1)) (G (A 1))))
    "#;

    let slice = causal_slice_program(Some("birewrite.egg".to_owned()), source).unwrap();
    assert_eq!(slice.rule_mapping.len(), 2);
    assert_eq!(slice.rule_mapping[0].source_command_index, 3);
    assert_eq!(slice.rule_mapping[1].source_command_index, 3);
    assert_ne!(
        slice.rule_mapping[0].registered_name,
        slice.rule_mapping[1].registered_name
    );
    assert!(!slice.source.contains("(birewrite"));
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("birewrite-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
}

#[test]
fn bare_ground_constructor_initialization_supports_rewrite_replay() {
    let source = r#"
        (datatype Expr (A i64) (F Expr))
        (rewrite (F x) x)
        (F (A 1))
        (run 1)
        (check (= (F (A 1)) (A 1)))
    "#;

    let slice = causal_slice_program(Some("bare-constructor.egg".to_owned()), source).unwrap();
    assert!(slice.source.contains("(F (A 1))"));
    assert_eq!(slice.stats.source_facts, 1);
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("bare-constructor-replay.egg".to_owned()),
                &slice.source,
            )
            .unwrap();
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
    assert!(has_replay_firing(
        &slice.source,
        "make-points-to",
        &[("e", "\"e\""), ("a", "(A \"alloc\")")]
    ));

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
fn constructor_lookup_body_retains_its_application_and_equality_causes() {
    let source = r#"
        (datatype Allocation (A String))
        (constructor expr_points_to (String) Allocation)
        (relation Seed (String Allocation))
        (relation Use (String))
        (relation Goal (Allocation))
        (rule ((Seed e a))
              ((union (expr_points_to e) a))
              :name "make-points-to")
        (rule ((Use e) (= (expr_points_to e) a))
              ((Goal a))
              :name "read-points-to")
        (Seed "e" (A "alloc"))
        (Use "e")
        (run 2)
        (check (Goal (A "alloc")))
    "#;

    let slice = causal_slice_program(Some("constructor-lookup.egg".to_owned()), source).unwrap();
    assert_eq!(slice.stats.equality_edges, 1);
    assert_eq!(slice.stats.retained_applications, 2);
    assert!(
        replay_firings(&slice.source)
            .iter()
            .any(|(rule, _)| rule == "make-points-to")
    );
    assert!(has_replay_firing(
        &slice.source,
        "read-points-to",
        &[("e", "\"e\""), ("a", "(A \"alloc\")")]
    ));

    for replay_source in [&slice.full_transcript_source, &slice.source] {
        for make_egraph in [EGraph::default, || {
            EGraph::new_with_proofs().with_proof_testing()
        }] {
            make_egraph()
                .parse_and_run_program(
                    Some("constructor-lookup-replay.egg".to_owned()),
                    replay_source,
                )
                .unwrap();
        }
    }
}

#[test]
fn chained_constructor_lookup_requires_exact_match_row_provenance() {
    let source = r#"
        (datatype Allocation (A String))
        (constructor expr_points_to (String) Allocation)
        (constructor ptr_points_to (Allocation) Allocation)
        (relation ExprEdge (String String))
        (relation PtrEdge (String String))
        (relation Load (String String))
        (rule ((ExprEdge expr alloc))
              ((union (expr_points_to expr) (A alloc)))
              :name "make-expr")
        (rule ((PtrEdge from to))
              ((union (ptr_points_to (A from)) (A to)))
              :name "make-ptr")
        (rule ((Load expr result)
               (= (expr_points_to expr) alloc)
               (= (ptr_points_to alloc) pointee))
              ((union (expr_points_to result) pointee))
              :name "load")
        (ExprEdge "expr" "alloc")
        (PtrEdge "alloc" "pointee")
        (Load "expr" "result")
        (run 2)
        (check (= (expr_points_to "result") (A "pointee")))
    "#;

    EGraph::default()
        .parse_and_run_program(Some("chained-constructor-lookup.egg".to_owned()), source)
        .unwrap();

    // The first lookup binds `alloc` using `(expr_points_to "expr")`, while
    // the constructor row enabling the second lookup was created with
    // `(A "alloc")`. Those terms are equal, but choosing a historical
    // constructor witness by searching their e-class would guess the body
    // producer rather than capture the exact row used by the native match.
    let error = causal_slice_program(Some("chained-constructor-lookup.egg".to_owned()), source)
        .unwrap_err();
    let message = error.to_string();
    assert!(message.contains("grounded constructor `ptr_points_to`"));
    assert!(message.contains("syntax that was unavailable at the captured firing"));
}

#[test]
fn irrelevant_chained_lookup_does_not_block_a_sound_slice() {
    let source = r#"
        (datatype Allocation (A String))
        (constructor expr_points_to (String) Allocation)
        (constructor ptr_points_to (Allocation) Allocation)
        (relation ExprEdge (String String))
        (relation PtrEdge (String String))
        (relation Load (String String))
        (relation Seed (String))
        (relation Goal (String))
        (rule ((ExprEdge expr alloc))
              ((union (expr_points_to expr) (A alloc)))
              :name "make-expr")
        (rule ((PtrEdge from to))
              ((union (ptr_points_to (A from)) (A to)))
              :name "make-ptr")
        (rule ((Load expr result)
               (= (expr_points_to expr) alloc)
               (= (ptr_points_to alloc) pointee))
              ((union (expr_points_to result) pointee))
              :name "load")
        (rule ((Seed value)) ((Goal value)) :name "keep")
        (ExprEdge "expr" "alloc")
        (PtrEdge "alloc" "pointee")
        (Load "expr" "result")
        (Seed "kept")
        (run 2)
        (check (Goal "kept"))
    "#;

    let slice =
        causal_slice_program(Some("irrelevant-chained-lookup.egg".to_owned()), source).unwrap();
    assert_eq!(slice.stats.retained_applications, 1);
    let firings = replay_firings(&slice.source);
    assert!(firings.iter().any(|(rule, _)| rule == "keep"));
    assert!(!firings.iter().any(|(rule, _)| rule == "load"));
    assert!(!firings.iter().any(|(rule, _)| rule == "make-expr"));
    assert!(!firings.iter().any(|(rule, _)| rule == "make-ptr"));
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("irrelevant-chained-lookup-replay.egg".to_owned()),
                &slice.source,
            )
            .unwrap();
    }
}

#[test]
fn nested_constructor_union_records_the_complete_source_syntax() {
    let source = r#"
        (datatype Allocation (A String))
        (constructor ptr_points_to (Allocation) Allocation)
        (relation Edge (String String))
        (rule ((Edge from to))
              ((union (ptr_points_to (A from)) (A to)))
              :name "make-pointer")
        (Edge "from" "to")
        (run 1)
        (check (= (ptr_points_to (A "from")) (A "to")))
    "#;

    let slice =
        causal_slice_program(Some("nested-constructor-union.egg".to_owned()), source).unwrap();
    assert_eq!(slice.stats.equality_edges, 1);
    assert_eq!(slice.stats.retained_applications, 1);
    assert!(
        replay_firings(&slice.source)
            .iter()
            .any(|(rule, _)| rule == "make-pointer")
    );
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("nested-constructor-union-replay.egg".to_owned()),
                &slice.source,
            )
            .unwrap();
    }
}

#[test]
fn equality_rekeyed_relation_rows_fail_closed_without_commit_provenance() {
    let source = r#"
        (datatype Expr (A i64))
        (relation Pair (Expr Expr))
        (relation Goal ())
        (rule ((Pair x y)) ((union x y)) :name "unify")
        (rule ((Pair x x)) ((Goal)) :name "observe-rekeyed")
        (Pair (A 1) (A 2))
        (run 2)
        (check (Goal))
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
    assert!(
        replay_firings(&first.source)
            .iter()
            .any(|(rule, _)| rule == name)
    );
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
fn pointer_fixture_slices_to_one_strictly_checked_firing() {
    let repository = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap();
    let source_path = repository.join("benchmarks/pointer-analysis-small.egg");
    let fact_directory = repository.join("benchmarks/data/pointer-analysis-small");
    let source = std::fs::read_to_string(&source_path).unwrap();

    let slice = causal_slice_program_with_fact_directory(
        Some(source_path.to_string_lossy().into_owned()),
        &source,
        Some(&fact_directory),
    )
    .unwrap();
    assert_eq!(slice.stats.pending_firings, 706);
    assert_eq!(slice.stats.effective_applications, 600);
    assert_eq!(slice.stats.retained_applications, 1);
    assert!(!slice.source.contains("(run 100000)"));
    assert_eq!(replay_firings(&slice.source).len(), 1);
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(
                Some("pointer-analysis-small-sliced.egg".to_owned()),
                &slice.source,
            )
            .unwrap();
    }
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
    assert_eq!(replay_firings(&slice.full_transcript_source).len(), 2);
    assert_eq!(replay_firings(&slice.source).len(), 1);

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
fn empty_body_rule_replays_one_ground_match_and_its_complete_head() {
    let source = r#"
        (relation Existing (i64))
        (relation Goal (i64))
        (Existing 1)
        (rule ()
              ((Existing 1) (Goal 7))
              :name "initialize")
        (run 2)
        (check (Goal 7))
    "#;

    let slice = causal_slice_program(Some("empty-body.egg".to_owned()), source).unwrap();
    assert_eq!(slice.stats.matched_applications, 1);
    assert_eq!(slice.stats.effective_applications, 1);
    assert_eq!(slice.stats.retained_applications, 1);
    assert!(has_replay_firing(&slice.source, "initialize", &[]));
    for make_egraph in [EGraph::default, || {
        EGraph::new_with_proofs().with_proof_testing()
    }] {
        make_egraph()
            .parse_and_run_program(Some("empty-body-replay.egg".to_owned()), &slice.source)
            .unwrap();
    }
}

#[test]
fn positive_check_selects_one_actual_satisfying_grounding() {
    let source = ORIGINAL.replace("(check (Goal 2))", "(check (Goal x))");
    let slice = causal_slice_program(Some("witness.egg".to_owned()), &source).unwrap();
    assert_eq!(slice.stats.retained_applications, 2);
    assert_eq!(replay_firings(&slice.source).len(), 2);
    assert!(
        !replay_firings(&slice.source)
            .iter()
            .any(|(rule, _)| rule == "irrelevant")
    );

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
    let firings = replay_firings(&slice.source);
    assert!(firings.iter().any(|(rule, _)| rule == "fanout"));
    assert!(firings.iter().any(|(rule, _)| rule == "finish"));
    assert!(firings.iter().any(|(rule, _)| rule == "other-root"));
    assert!(!firings.iter().any(|(rule, _)| rule == "irrelevant"));
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
            .contains("a non-insert initialization action")
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
