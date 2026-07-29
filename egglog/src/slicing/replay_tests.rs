use std::fs;
use std::path::PathBuf;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

use super::*;
use crate::slicing::backward::select_all_checks;

fn serial_pool() -> &'static rayon::ThreadPool {
    static SERIAL_POOL: OnceLock<rayon::ThreadPool> = OnceLock::new();
    SERIAL_POOL.get_or_init(|| {
        rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .unwrap()
    })
}

fn temp_fact_dir() -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let path = std::env::temp_dir().join(format!(
        "egglog-causal-replay-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir_all(&path).unwrap();
    path
}

fn slice_commands(program: &str) -> (Vec<Command>, String) {
    let mut recorder = EGraph::default();
    serial_pool().install(|| recorder.enable_trace()).unwrap();
    recorder.parse_and_run_program(None, program).unwrap();
    let slice = select_all_checks(&recorder).unwrap();
    let ir = build_replay_program(&recorder, &slice).unwrap();
    let commands = ir.to_commands().unwrap();
    let rendered = render_commands_as_source(&commands);

    let mut proof = EGraph::default().with_proofs_enabled().with_proof_testing();
    serial_pool()
        .install(|| proof.parse_and_run_program(None, &rendered))
        .unwrap();
    (commands, rendered)
}

fn endpoint_normalization_program(order: [&str; 3]) -> String {
    let constructors = order
        .into_iter()
        .map(|name| format!("({name})"))
        .collect::<Vec<_>>()
        .join("\n");
    format!(
        "(datatype E (A) (B) (C))\n{constructors}\n(union (A) (B))\n(union (B) (C))\n(check (= (A) (C)))"
    )
}

#[test]
fn applied_equality_distinguishes_proposal_from_native_edge() {
    let mut recorder = EGraph::default();
    serial_pool().install(|| recorder.enable_trace()).unwrap();
    recorder
        .parse_and_run_program(None, &endpoint_normalization_program(["A", "B", "C"]))
        .unwrap();

    recorder
        .with_trace_view(|view| {
            let first =
                view.project_applied_equality(crate::core_relations::AppliedEqualityId::new(1))?;
            let second =
                view.project_applied_equality(crate::core_relations::AppliedEqualityId::new(2))?;
            let first_raw =
                view.applied_equality(crate::core_relations::AppliedEqualityId::new(1))?;
            let second_raw =
                view.applied_equality(crate::core_relations::AppliedEqualityId::new(2))?;

            // The second source action spells its left endpoint as B, but
            // native execution has already canonicalized B to A. Its
            // recorded proposal and applied forest edge therefore carry
            // observably different identities.
            assert_eq!(second.left.term, first.right.term);
            assert_ne!(second.left.raw, first.right.raw);
            assert_eq!(second.left.raw, first.left.raw);
            assert_eq!(second_raw.native_parent, first_raw.native_parent);
            assert_eq!(second_raw.native_parent, second.left.raw);
            assert_eq!(second_raw.native_child, second.right.raw);
            let support = view.explain_equality_denotation_before(
                crate::core_relations::AppliedEqualityId::new(2),
            )?;
            assert_eq!(
                support.applied.as_ref(),
                [crate::core_relations::AppliedEqualityId::new(1)]
            );
            assert!(
                !support
                    .applied
                    .contains(&crate::core_relations::AppliedEqualityId::new(2))
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn slice_replays_precanonicalized_union_endpoints_in_any_allocation_order() {
    for order in [
        ["A", "B", "C"],
        ["A", "C", "B"],
        ["B", "A", "C"],
        ["B", "C", "A"],
        ["C", "A", "B"],
        ["C", "B", "A"],
    ] {
        let mut recorder = EGraph::default();
        serial_pool().install(|| recorder.enable_trace()).unwrap();
        recorder
            .parse_and_run_program(None, &endpoint_normalization_program(order))
            .unwrap();
        let slice = select_all_checks(&recorder).unwrap();
        let ir = build_replay_program(&recorder, &slice).unwrap();
        let rendered = render_commands_as_source(&ir.to_commands().unwrap());

        for (mode, mut replay) in [
            ("native", EGraph::default()),
            ("term", EGraph::default().with_term_encoding_enabled()),
        ] {
            replay
                .parse_and_run_program(None, &rendered)
                .unwrap_or_else(|error| {
                    panic!(
                        "{mode} replay failed for constructor order {order:?}: {error}\n{rendered}"
                    )
                });
        }
    }
}

#[test]
fn carrier_container_denotation_retains_its_historical_anchor() {
    let program = "(sort E)
                       (constructor A () E)
                       (constructor Alias () E)
                       (constructor C () E)
                       (sort Es (Vec E))
                       (constructor Wrap (Es) E)
                       (relation Eq ())
                       (relation Finish ())
                       (ruleset equate)
                       (ruleset finish)
                       (A)
                       (Wrap (vec-of (A)))
                       (C)
                       (Eq)
                       (Finish)
                       (rule ((Eq)) ((union (A) (Alias)))
                         :ruleset equate :name \"equate\")
                       (rule ((Finish)) ((union (Wrap (vec-of (Alias))) (C)))
                         :ruleset finish :name \"finish\")
                       (run equate 1)
                       (run finish 1)
                       (check (= (Wrap (vec-of (A))) (C)))";
    let mut recorder = EGraph::default();
    serial_pool().install(|| recorder.enable_trace()).unwrap();
    serial_pool()
        .install(|| recorder.parse_and_run_program(None, program))
        .unwrap();
    recorder
        .with_trace_view(|view| {
            let mut rule_unions = Vec::new();
            for raw_id in 1..=view.totals().applied_equalities {
                let id = crate::core_relations::AppliedEqualityId::new(raw_id);
                let event = view.project_applied_equality(id)?;
                if matches!(
                    event.reason,
                    crate::core_relations::EqualityReason::RuleUnion(_)
                ) {
                    rule_unions.push((id, event));
                }
            }
            assert_eq!(rule_unions.len(), 2, "expected equate and finish unions");
            let (equate_id, _equate) = &rule_unions[0];
            let (finish_id, _finish) = &rule_unions[1];
            let support = view.explain_equality_denotation_before(*finish_id)?;
            assert!(
                support.facts.iter().copied().any(|fact| {
                    view.fact(fact)
                        .ok()
                        .and_then(|record| match record.cause {
                            crate::core_relations::CauseRef::Cause(cause) => Some(cause),
                            crate::core_relations::CauseRef::Rule(_) => None,
                        })
                        .and_then(|cause| view.cause(cause).ok())
                        .is_some_and(|cause| {
                            matches!(cause, crate::core_relations::RawCause::Source(_))
                        })
                }),
                "container denotation lost its source anchor: got {:?}",
                support.facts
            );
            assert!(support.applied.contains(equate_id));
            assert!(!support.applied.contains(finish_id));
            Ok(())
        })
        .unwrap();
}

#[derive(Clone, Copy, Debug)]
enum EndpointCarrier {
    SourceUnion,
    RuleUnion,
    SourceSet,
    RuleSet,
    DeleteRecreate,
}

#[derive(Clone, Copy, Debug)]
struct EndpointCase {
    carrier: EndpointCarrier,
    order: [&'static str; 5],
}

fn next_endpoint_random(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

fn shuffled_endpoint_order(state: &mut u64) -> [&'static str; 5] {
    let mut order = ["A", "B", "C", "NoiseL", "NoiseR"];
    for index in (1..order.len()).rev() {
        let other = (next_endpoint_random(state) as usize) % (index + 1);
        order.swap(index, other);
    }
    order
}

fn endpoint_case_program(case: EndpointCase) -> String {
    let mut lines = vec!["(datatype E (A) (B) (C) (F E) (NoiseL) (NoiseR))".to_owned()];
    match case.carrier {
        EndpointCarrier::SourceUnion => {}
        EndpointCarrier::RuleUnion => {
            lines.push("(relation Trigger ())".into());
            lines.push("(ruleset bridge)".into());
        }
        EndpointCarrier::SourceSet => {
            lines.push("(function f (E) i64 :no-merge)".into());
            lines.push("(relation Out (i64))".into());
            lines.push("(ruleset read)".into());
        }
        EndpointCarrier::RuleSet => {
            lines.push("(function f (E) i64 :no-merge)".into());
            lines.push("(relation Trigger ())".into());
            lines.push("(relation Out (i64))".into());
            lines.push("(ruleset write)".into());
            lines.push("(ruleset read)".into());
        }
        EndpointCarrier::DeleteRecreate => {
            lines.push("(relation Delete ())".into());
            lines.push("(relation Recreate ())".into());
            lines.push("(relation Before (E))".into());
            lines.push("(relation After (E))".into());
            lines.push("(relation Final ())".into());
            lines.push("(ruleset cleanup)".into());
            lines.push("(ruleset recreate)".into());
            lines.push("(ruleset reconcile)".into());
            lines.push("(ruleset finish)".into());
        }
    }

    for name in case.order {
        lines.push(format!("({name})"));
    }
    lines.push("(union (NoiseL) (NoiseR))".into());
    lines.push("(union (A) (B))".into());

    match case.carrier {
        EndpointCarrier::SourceUnion => {
            lines.push("(union (B) (C))".into());
            lines.push("(check (= (A) (C)))".into());
        }
        EndpointCarrier::RuleUnion => {
            lines.push("(Trigger)".into());
            lines.push(
                "(rule ((Trigger)) ((union (B) (C))) :ruleset bridge :name \"bridge\")".into(),
            );
            lines.push("(run bridge 1)".into());
            lines.push("(check (= (A) (C)))".into());
        }
        EndpointCarrier::SourceSet => {
            lines.push("(set (f (B)) 7)".into());
            lines.push(
                "(rule ((= value (f (A)))) ((Out value)) :ruleset read :name \"read\")".into(),
            );
            lines.push("(run read 1)".into());
            lines.push("(check (Out 7))".into());
        }
        EndpointCarrier::RuleSet => {
            lines.push("(Trigger)".into());
            lines
                .push("(rule ((Trigger)) ((set (f (B)) 7)) :ruleset write :name \"write\")".into());
            lines.push("(run write 1)".into());
            lines.push(
                "(rule ((= value (f (A)))) ((Out value)) :ruleset read :name \"read\")".into(),
            );
            lines.push("(run read 1)".into());
            lines.push("(check (Out 7))".into());
        }
        EndpointCarrier::DeleteRecreate => {
            lines.push("(Before (F (B)))".into());
            lines.push("(Delete)".into());
            lines.push("(Recreate)".into());
            lines.push("(Final)".into());
            lines.push(
                "(rule ((Delete)) ((delete (F (B)))) :ruleset cleanup :name \"delete-f\")".into(),
            );
            lines.push(
                "(rule ((Recreate)) ((After (F (B)))) :ruleset recreate :name \"recreate-f\")"
                    .into(),
            );
            lines.push(
                    "(rule ((Before old) (After new)) ((union old new)) :ruleset reconcile :name \"reconcile\")"
                        .into(),
                );
            lines
                .push("(rule ((Final)) ((union (B) (C))) :ruleset finish :name \"finish\")".into());
            lines.push("(run cleanup 1)".into());
            lines.push("(run recreate 1)".into());
            lines.push("(run reconcile 1)".into());
            lines.push("(run finish 1)".into());
            lines.push("(check (= (A) (C)) (Before x) (After x))".into());
        }
    }
    lines.join("\n")
}

fn run_endpoint_case(case: EndpointCase) -> Result<(), String> {
    let program = endpoint_case_program(case);
    let mut recorder = EGraph::default();
    serial_pool()
        .install(|| recorder.enable_trace())
        .map_err(|error| format!("enable trace: {error}"))?;
    serial_pool()
        .install(|| recorder.parse_and_run_program(None, &program))
        .map_err(|error| format!("capture: {error}"))?;
    let slice = select_all_checks(&recorder).map_err(|error| format!("slice: {error}"))?;
    if matches!(case.carrier, EndpointCarrier::DeleteRecreate) && slice.replay_removals.is_empty() {
        return Err("delete/recreate case lost its selected removal".into());
    }
    let replay = build_replay_program(&recorder, &slice)
        .map_err(|error| format!("build replay: {error}"))?;
    let rendered = render_commands_as_source(
        &replay
            .to_commands()
            .map_err(|error| format!("build commands: {error}"))?,
    );
    if !rendered.contains("(union (A) (B))") {
        return Err("missing denotation anchor `(union (A) (B))`".into());
    }
    if rendered.contains("(union (NoiseL) (NoiseR))") {
        return Err("disconnected noise equality was retained".into());
    }
    for (mode, mut graph) in [
        ("native", EGraph::default()),
        ("term", EGraph::default().with_term_encoding_enabled()),
    ] {
        graph
            .parse_and_run_program(None, &rendered)
            .map_err(|error| format!("{mode} replay: {error}\n{rendered}"))?;
    }
    Ok(())
}

#[test]
fn endpoint_denotation_is_complete_across_carriers_and_allocation_orders() {
    let carriers = [
        EndpointCarrier::SourceUnion,
        EndpointCarrier::RuleUnion,
        EndpointCarrier::SourceSet,
        EndpointCarrier::RuleSet,
        EndpointCarrier::DeleteRecreate,
    ];
    let mut random = 0x6a09_e667_f3bc_c909;
    for index in 0..32 {
        let case = EndpointCase {
            carrier: carriers[index % carriers.len()],
            order: shuffled_endpoint_order(&mut random),
        };
        if let Err(error) = run_endpoint_case(case) {
            panic!(
                "endpoint denotation property failed for {case:?}: {error}\nprogram:\n{}",
                endpoint_case_program(case)
            );
        }
    }
}

#[test]
fn owned_ir_preserves_pre_run_check_and_source_order() {
    let mut egraph = EGraph::default();
    serial_pool().install(|| egraph.enable_trace()).unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(relation R (i64))
                 (R 1)
                 (check (R 1))
                 (R 2)
                 (check (R 2))",
        )
        .unwrap();
    let slice = select_all_checks(&egraph).unwrap();
    let ir = build_replay_program(&egraph, &slice).unwrap();
    assert!(matches!(
        ir.events.as_slice(),
        [
            ReplayEvent::Source(_),
            ReplayEvent::Check(_),
            ReplayEvent::Source(_),
            ReplayEvent::Check(_),
        ]
    ));
}

#[test]
fn owned_ir_records_late_source_boundary_without_retaining_prefix_wave() {
    let mut egraph = EGraph::default();
    serial_pool().install(|| egraph.enable_trace()).unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(relation Seed (i64))
             (relation Dead (i64))
             (relation Late (i64))
             (relation Out (i64))
             (Seed 1)
             (rule ((Seed x)) ((Dead x)) :name \"prefix\")
             (run 1)
             (Late 1)
             (rule ((Late x)) ((Out x)) :name \"selected\")
             (run 1)
             (check (Out 1))",
        )
        .unwrap();

    let slice = select_all_checks(&egraph).unwrap();
    let ir = build_replay_program(&egraph, &slice).unwrap();
    assert!(matches!(
        ir.events.as_slice(),
        [
            ReplayEvent::Source(ReplaySource { after_wave: 1, .. }),
            ReplayEvent::Wave(ReplayWave { wave: 2, .. }),
            ReplayEvent::Check(check),
        ] if check.after_wave == 2
    ));

    let commands = ir.to_commands().unwrap();
    assert_eq!(
        commands
            .iter()
            .filter(|command| matches!(command, Command::RunSchedule(_)))
            .count(),
        1,
        "the unselected prefix wave must not be retained"
    );
    assert!(
        !commands
            .iter()
            .any(|command| command.to_string().contains("prefix")),
        "the unselected prefix rule must not be retained"
    );
}

#[test]
fn replay_preserves_setup_chronology_across_late_global() {
    let mut recorder = EGraph::default();
    serial_pool().install(|| recorder.enable_trace()).unwrap();
    recorder
        .parse_and_run_program(
            None,
            "(datatype E (A i64))
             (relation Seed (i64))
             (relation Mid (i64))
             (relation Out (E))
             (Seed 1)
             (rule ((Seed x)) ((Mid x)) :name \"first\")
             (run 1)
             (check (Mid 1))
             (let $late (A 7))
             (rule ((Mid x)) ((Out $late)) :name \"second\")
             (run 1)
             (check (Out (A 7)))",
        )
        .unwrap();

    let slice = select_all_checks(&recorder).unwrap();
    let ir = build_replay_program(&recorder, &slice).unwrap();
    let commands = ir.to_commands().unwrap();
    let rendered = render_commands_as_source(&commands);

    let first_run = rendered
        .find("(run-schedule (run-rule (\"first\"")
        .unwrap_or_else(|| panic!("first selected wave is absent:\n{rendered}"));
    let first_check = rendered
        .find("(check (Mid 1))")
        .unwrap_or_else(|| panic!("first selected check is absent:\n{rendered}"));
    let late_global = rendered
        .find("(let $late (A 7))")
        .unwrap_or_else(|| panic!("late global is absent:\n{rendered}"));
    let second_rule = rendered
        .find(":name \"second\"")
        .unwrap_or_else(|| panic!("second selected rule is absent:\n{rendered}"));
    let second_run = rendered
        .find("(run-schedule (run-rule (\"second\"")
        .unwrap_or_else(|| panic!("second selected wave is absent:\n{rendered}"));
    assert!(
        first_run < first_check
            && first_check < late_global
            && late_global < second_rule
            && second_rule < second_run,
        "late setup crossed its source chronology:\n{rendered}"
    );

    for (mode, mut replay) in [
        ("native", EGraph::default()),
        ("term", EGraph::default().with_term_encoding_enabled()),
        (
            "proof",
            EGraph::default().with_proofs_enabled().with_proof_testing(),
        ),
    ] {
        serial_pool()
            .install(|| replay.parse_and_run_program(None, &rendered))
            .unwrap_or_else(|error| panic!("{mode} strict replay failed: {error}\n{rendered}"));
    }
}

#[test]
fn rendered_artifact_round_trips_globals_and_grounded_rules_with_proofs() {
    let mut recorder = EGraph::default();
    serial_pool().install(|| recorder.enable_trace()).unwrap();
    recorder
        .parse_and_run_program(
            None,
            "(datatype E (A i64) (B E) (C E))
                 (relation Seed (E))
                 (relation __slice_replay_0 (i64))
                 (Seed (A 1))
                 (let $dead (A 2))
                 (let $seed (A 1))
                 (rule ((Seed x))
                       ((union (B $seed) (C x)))
                       :name \"emit\")
                 (run 1)
                 (check (= (B $seed) (C (A 1))))",
        )
        .unwrap();
    let slice = select_all_checks(&recorder).unwrap();
    let ir = build_replay_program(&recorder, &slice).unwrap();
    let commands = ir.to_commands().unwrap();
    assert!(commands.iter().any(|command| {
        matches!(command, Command::Action(Action::Let(_, name, _)) if name == "$seed")
    }));
    assert!(!commands.iter().any(|command| {
        matches!(command, Command::Action(Action::Let(_, name, _)) if name == "$dead")
    }));
    assert!(!commands.iter().any(|command| {
        matches!(
            command,
            Command::Function {
                let_binding: true,
                ..
            } | Command::Constructor {
                let_binding: true,
                ..
            }
        )
    }));
    let rendered = render_commands_as_source(&commands);
    assert!(rendered.contains("(datatype E"));
    assert!(rendered.contains("(relation Seed"));
    assert!(rendered.contains("(let $seed (A 1))"));
    assert!(!rendered.contains(":internal-let"));
    assert!(!rendered.contains("(relation __slice_replay_0"));
    assert!(rendered.contains("(let-check $__slice_replay_0_1 (A 1) :sort E)"));
    assert!(
        !rendered.contains('@'),
        "rendered replay leaked a parser-reserved internal symbol:\n{rendered}"
    );
    let global = rendered.find("(let $seed").unwrap();
    let rule = rendered.find(":name \"emit\"").unwrap();
    assert!(
        global < rule,
        "retained globals must precede dependent rules"
    );

    let mut direct_proof = EGraph::default().with_proofs_enabled().with_proof_testing();
    serial_pool()
        .install(|| direct_proof.run_program(commands))
        .unwrap();

    let mut proof = EGraph::default().with_proofs_enabled().with_proof_testing();
    serial_pool()
        .install(|| proof.parse_and_run_program(None, &rendered))
        .unwrap();
}

#[test]
fn replay_keeps_only_required_static_declarations() {
    let (commands, rendered) = slice_commands(
        "(datatype Used (U i64))
             (datatype Unused (Z))
             (relation Seed (i64))
             (relation Out (Used))
             (relation Dead (i64))
             (function dead-f (i64) i64 :no-merge)
             (ruleset live)
             (ruleset dead)
             (Seed 1)
             (rule ((Seed x)) ((Out (U x))) :ruleset live :name \"selected\")
             (rule ((Dead x)) ((Dead x)) :ruleset dead :name \"unselected\")
             (run live 1)
             (check (Out (U 1)))",
    );

    assert!(
        commands
            .iter()
            .any(|command| matches!(command, Command::Datatype { name, .. } if name == "Used"))
    );
    assert!(
        !commands
            .iter()
            .any(|command| matches!(command, Command::Datatype { name, .. } if name == "Unused"))
    );
    assert!(
        !commands
            .iter()
            .any(|command| matches!(command, Command::Relation { name, .. } if name == "Dead"))
    );
    assert!(
        !commands
            .iter()
            .any(|command| matches!(command, Command::Function { name, .. } if name == "dead-f"))
    );
    assert!(
        commands
            .iter()
            .any(|command| matches!(command, Command::AddRuleset(_, name) if name == "live"))
    );
    assert!(
        !commands
            .iter()
            .any(|command| matches!(command, Command::AddRuleset(_, name) if name == "dead"))
    );
    assert!(!rendered.contains("unselected"));
}

#[test]
fn replay_retains_declarations_used_only_by_a_merge() {
    let mut egraph = EGraph::default();
    let commands = egraph
        .parse_program(
            None,
            "(datatype E (V i64))
             (function merge-helper (E) i64 :no-merge)
             (function kept (i64) E
               :merge ((set (merge-helper old) 1) new))
             (function dead-helper (E) i64 :no-merge)
             (set (kept 0) (V 1))",
        )
        .unwrap();
    let commands = retain_required_declarations(commands);

    assert!(commands.iter().any(
        |command| matches!(command, Command::Function { name, .. } if name == "merge-helper")
    ));
    assert!(
        commands
            .iter()
            .any(|command| matches!(command, Command::Function { name, .. } if name == "kept"))
    );
    assert!(
        !commands.iter().any(
            |command| matches!(command, Command::Function { name, .. } if name == "dead-helper")
        )
    );
}

#[test]
fn replay_keeps_datatype_groups_atomic() {
    let (commands, _) = slice_commands(
        "(datatype*
               (Used (U i64))
               (Sibling (S i64)))
             (relation Goal (Used))
             (Goal (U 1))
             (check (Goal (U 1)))",
    );
    assert!(commands.iter().any(|command| matches!(
        command,
        Command::Datatypes { datatypes, .. }
            if datatypes.iter().any(|(_, name, _)| name == "Used")
                && datatypes.iter().any(|(_, name, _)| name == "Sibling")
    )));
}

#[test]
fn rendered_artifact_preserves_anonymous_rewrite_and_selected_global() {
    let (commands, rendered) = slice_commands(
        "(datatype E (A i64) (B i64))
             (let $left (A 1))
             (let $target (B 1))
             (rewrite (A x) $target)
             (run 1)
             (check (= $left $target))",
    );
    let rewrites = commands
        .iter()
        .filter_map(|command| match command {
            Command::Rewrite(_, rewrite, _) => Some(rewrite),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(rewrites.len(), 1, "unexpected artifact:\n{rendered}");
    assert!(rewrites[0].name.starts_with("__slice_replay_rule_s"));
    assert!(
        !commands
            .iter()
            .any(|command| matches!(command, Command::Rule { .. })),
        "surface rewrite was lowered back to a rule:\n{rendered}"
    );
    assert!(rendered.contains("(__rewrite_root "));
    assert!(!rendered.contains(crate::util::INTERNAL_SYMBOL_PREFIX));
}

#[test]
fn rendered_artifact_preserves_birewrite_when_both_directions_are_retained() {
    let (commands, rendered) = slice_commands(
        "(datatype E (A i64) (B i64))
             (let $a (A 1))
             (let $b (B 2))
             (birewrite (A x) (B x))
             (run 1)
             (check (= $a (B 1)))
             (check (= (A 2) $b))",
    );
    let birewrites = commands
        .iter()
        .filter_map(|command| match command {
            Command::BiRewrite(_, rewrite) => Some(rewrite),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(birewrites.len(), 1, "unexpected artifact:\n{rendered}");
    assert!(birewrites[0].name.starts_with("__slice_replay_rule_s"));
    assert!(
        !commands
            .iter()
            .any(|command| matches!(command, Command::Rewrite(..) | Command::Rule { .. }))
    );
}

#[test]
fn rendered_artifact_preserves_single_retained_birewrite_direction() {
    let (commands, rendered) = slice_commands(
        "(datatype E (A i64) (B i64))
             (let $a (A 1))
             (birewrite (A x) (B x))
             (run 1)
             (check (= $a (B 1)))",
    );
    assert!(
        commands.iter().any(|command| matches!(
            command,
            Command::BiRewrite(_, rewrite)
                if rewrite.name.starts_with("__slice_replay_rule_s")
        )),
        "single selected direction lost its source birewrite form:\n{rendered}"
    );
    assert!(
        !commands
            .iter()
            .any(|command| matches!(command, Command::Rewrite(..)))
    );

    let (commands, rendered) = slice_commands(
        "(datatype E (A i64) (B i64))
             (let $b (B 2))
             (birewrite (A x) (B x))
             (run 1)
             (check (= (A 2) $b))",
    );
    assert!(
        commands.iter().any(|command| matches!(
            command,
            Command::BiRewrite(_, rewrite)
                if rewrite.name.starts_with("__slice_replay_rule_s")
                    && rewrite.lhs.to_string() == "(A x)"
                    && rewrite.rhs.to_string() == "(B x)"
        )),
        "reverse selected direction lost its original birewrite orientation:\n{rendered}"
    );
}

#[test]
fn owned_ir_embeds_only_selected_input_rows() {
    static NEXT_RELATIVE: AtomicU64 = AtomicU64::new(0);
    let relative_dir = PathBuf::from("target").join(format!(
        "egglog-causal-replay-relative-{}-{}",
        std::process::id(),
        NEXT_RELATIVE.fetch_add(1, Ordering::Relaxed)
    ));
    let dir = std::env::current_dir().unwrap().join(&relative_dir);
    fs::create_dir_all(&dir).unwrap();
    let file = relative_dir.join("rows.tsv");
    fs::write(&file, "drop\t0.0\nkeep\"quoted\\path\t-0.0\n").unwrap();

    let mut egraph = EGraph {
        fact_directory: Some(relative_dir),
        ..EGraph::default()
    };
    serial_pool().install(|| egraph.enable_trace()).unwrap();
    egraph
        .parse_and_run_program(
            None,
            r#"(relation R (String f64))
                 (input R "rows.tsv")
                 (check (R "keep\"quoted\\path" -0.0))"#,
        )
        .unwrap();
    let slice = select_all_checks(&egraph).unwrap();
    fs::remove_dir_all(dir).unwrap();
    let ir = build_replay_program(&egraph, &slice).unwrap();
    assert_eq!(
        ir.events
            .iter()
            .filter(|event| {
                matches!(
                    event,
                    ReplayEvent::Source(ReplaySource {
                        kind: ReplaySourceKind::InputRow { .. },
                        ..
                    })
                )
            })
            .count(),
        1
    );
    let selected = ir.events.iter().find_map(|event| match event {
        ReplayEvent::Source(ReplaySource {
            kind: ReplaySourceKind::InputRow { line, literals, .. },
            ..
        }) => Some((*line, literals.as_ref())),
        _ => None,
    });
    let (line, literals) = selected.expect("selected input row disappeared");
    assert_eq!(line, 2);
    assert_eq!(literals[0], Literal::String("keep\"quoted\\path".into()));
    let Literal::Float(value) = literals[1] else {
        panic!("selected f64 input cell lost its literal type")
    };
    assert_eq!(value.0.to_bits(), (-0.0f64).to_bits());

    let commands = ir.to_commands().unwrap();
    let rendered = render_commands_as_source(&commands);
    for (mode, mut replay) in [
        ("native", EGraph::default()),
        ("term", EGraph::default().with_term_encoding_enabled()),
        (
            "proof",
            EGraph::default().with_proofs_enabled().with_proof_testing(),
        ),
    ] {
        serial_pool()
            .install(|| replay.parse_and_run_program(None, &rendered))
            .unwrap_or_else(|error| panic!("{mode} input replay failed: {error}\n{rendered}"));
    }
}

#[test]
fn capture_rejects_unrepresentable_nan_input_before_staging_rows() {
    let dir = temp_fact_dir();
    fs::write(dir.join("rows.tsv"), "keep\t-NaN\n").unwrap();
    let mut egraph = EGraph {
        fact_directory: Some(dir.clone()),
        ..EGraph::default()
    };
    serial_pool().install(|| egraph.enable_trace()).unwrap();
    let error = egraph
        .parse_and_run_program(None, "(relation R (String f64)) (input R \"rows.tsv\")")
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("trace capture does not support noncanonical f64 NaN literals"),
        "unexpected error: {error}"
    );
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn unsupported_input_fails_only_when_selected() {
    let dir = temp_fact_dir();
    fs::write(dir.join("value.tsv"), "1\t2\n").unwrap();

    let mut selected = EGraph {
        fact_directory: Some(dir.clone()),
        ..EGraph::default()
    };
    serial_pool().install(|| selected.enable_trace()).unwrap();
    selected
        .parse_and_run_program(
            None,
            "(function f (i64) i64 :no-merge)
                 (relation Out (i64))
                 (input f \"value.tsv\")
                 (rule ((= value (f 1))) ((Out value)) :name \"read-f\")
                 (run 1)
                 (check (Out 2))",
        )
        .unwrap();
    let slice = select_all_checks(&selected).unwrap();
    let error = match build_replay_program(&selected, &slice) {
        Err(error) => error,
        Ok(_) => panic!("selected unsupported input unexpectedly lowered"),
    };
    assert!(
        matches!(error, ReplayError::Unsupported(message) if message.contains("value function `f`"))
    );

    let mut unreachable = EGraph {
        fact_directory: Some(dir.clone()),
        ..EGraph::default()
    };
    serial_pool()
        .install(|| unreachable.enable_trace())
        .unwrap();
    unreachable
        .parse_and_run_program(
            None,
            "(function f (i64) i64 :no-merge)
                 (relation R (Unit))
                 (input f \"value.tsv\")
                 (R ())
                 (check (R ()))",
        )
        .unwrap();
    let slice = select_all_checks(&unreachable).unwrap();
    build_replay_program(&unreachable, &slice).unwrap();
    fs::remove_dir_all(dir).unwrap();
}
