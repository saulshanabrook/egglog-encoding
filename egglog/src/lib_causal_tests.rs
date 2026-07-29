use std::sync::OnceLock;

use crate::core_relations::EqualityReason;
use crate::tests::{FullOnly, get_value};
use crate::*;

fn serial_trace_pool() -> &'static rayon::ThreadPool {
    static SERIAL_POOL: OnceLock<rayon::ThreadPool> = OnceLock::new();
    SERIAL_POOL.get_or_init(|| {
        rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .unwrap()
    })
}

fn enable_serial_trace(egraph: &mut EGraph) -> Result<(), Error> {
    serial_trace_pool().install(|| egraph.enable_trace())
}

fn find_container_canonicalization(
    view: &core_relations::TraceView<'_>,
    root: core_relations::CauseId,
) -> Result<
    Option<(
        core_relations::Wave,
        core_relations::EdgeHorizon,
        core_relations::HistoryPosition,
        Vec<core_relations::TypedCellEquality>,
    )>,
    core_relations::TraceViewError,
> {
    let mut pending = vec![core_relations::CauseRef::Cause(root)];
    while let Some(cause) = pending.pop() {
        let core_relations::CauseRef::Cause(cause) = cause else {
            continue;
        };
        match view.cause(cause)? {
            core_relations::RawCause::ContainerCanonicalize {
                wave,
                as_of_edges,
                position,
                equalities,
            } => return Ok(Some((wave, as_of_edges, position, equalities.to_vec()))),
            core_relations::RawCause::Merge { incoming, .. } => {
                pending.push(incoming);
            }
            _ => {}
        }
    }
    Ok(None)
}

#[test]
fn trace_merge_input_choice_opt_in_is_explicit() {
    for name in [
        "min",
        "max",
        "pair-min-by-second-i64",
        "maybe-either-i64-bool-min",
        "maybe-either-i64-bool-max",
    ] {
        assert!(primitive_merge_returns_one_input(name), "{name}");
    }
    for name in ["+", "pair", "unstable-fn", "clamp"] {
        assert!(!primitive_merge_returns_one_input(name), "{name}");
    }
}

#[test]
fn trace_attribute_pair_registry_congruence() {
    serial_trace_pool().install(|| {
        let mut egraph = EGraph::default();
        egraph.enable_trace().unwrap();
        let mut program = String::new();
        // Base literals and container ids share raw Value bits. Crowd the
        // literal and computed-Call sorts so collision selection must use
        // the changed children's typed equality metadata.
        for value in 0..200 {
            program.push_str(&format!("(let $literal-{value} {value})"));
            program.push_str(&format!(
                "(let $computed-{value} (+ 1000 {}))",
                value - 1000
            ));
        }
        program.push_str(
            "(datatype Expr (A i64) (B i64))\
             (sort ExprPair (Pair Expr i64))\
             (datatype Root (Hold ExprPair))\
             (relation Go (Unit))\
             (relation Done (Unit))\
             (Go ())\
             (rule ((Go u))\
               ((Hold (pair (A 1) 7))\
                (Hold (pair (B 2) 7))\
                (Done ())\
                (union (A 1) (B 2))) :name \"merge-child\")\
             (run 1)\
             (check (Done ()))",
        );
        egraph.parse_and_run_program(None, &program).unwrap();

        egraph
            .with_trace_view(|view| {
                let (cause, wave, as_of_edges, position) = (1..=view.totals().applied_equalities)
                    .find_map(|raw| {
                        match view
                            .applied_equality(core_relations::AppliedEqualityId::new(raw))
                            .ok()?
                            .reason
                        {
                            EqualityReason::Congruence {
                                cause,
                                wave,
                                as_of_edges,
                                position,
                            } => Some((cause, wave, as_of_edges, position)),
                            _ => None,
                        }
                    })
                    .expect("Pair collision should retain one exact container-congruence edge");
                let dependency = find_container_canonicalization(view, cause)?
                    .expect("Pair congruence should unfold to its container collision");
                assert_eq!(
                    (dependency.0, dependency.1, dependency.2),
                    (wave, as_of_edges, position)
                );
                assert!(!dependency.3.is_empty());
                for pair in dependency.3 {
                    assert!(
                        !view
                            .explain_equality_support_at(
                                pair.left,
                                pair.right,
                                as_of_edges,
                                position
                            )?
                            .applied
                            .is_empty()
                    );
                }
                Ok(())
            })
            .unwrap();
    });
}

#[test]
fn trace_ignore_raw_colliding_unrelated_set_ancestor() {
    serial_trace_pool().install(|| {
        let mut egraph = EGraph::default();
        egraph.enable_trace().unwrap();
        let mut program = String::from(
            "(datatype Expr (A i64) (B i64))\
             (sort Exprs (Vec Expr))\
             (sort Ints (Set i64))\
             (function Hold (Unit) Exprs :no-merge)\
             (relation Go (Unit))\
             (relation Done (Unit))\
             (let $a (A 1))",
        );
        // Crowd the unsupported Set registry with every likely raw child
        // id. Its i64 elements are not typed Vec children, even when their
        // Value bits collide with the dirty Vec id.
        for value in 0..256 {
            program.push_str(&format!("(let $ints-{value} (set-of {value}))"));
        }
        program.push_str(
            "(Go ())\
             (rule ((Go u))\
               ((set (Hold ()) (vec-of (B 2)))\
                (union (A 1) (B 2))) :name \"merge-child\")\
             (run 1)\
             (rule ((= v (Hold ()))\
                    (= v (vec-of (A 1))))\
               ((Done ())) :name \"observe-refresh\")\
             (run 1)\
             (check (Done ()))",
        );
        egraph.parse_and_run_program(None, &program).unwrap();

        egraph
            .with_trace_view(|view| {
                let mut refreshed = false;
                for raw in 1..=view.totals().facts {
                    let fact = view.fact(core_relations::FactId::new(raw))?;
                    let core_relations::CauseRef::Cause(cause) = fact.cause else {
                        continue;
                    };
                    refreshed |= matches!(
                        view.cause(cause)?,
                        core_relations::RawCause::ContainerRefresh { .. }
                    );
                }
                assert!(refreshed);
                Ok(())
            })
            .unwrap();
    });
}

#[test]
#[should_panic(expected = "multiple exact logical replay sorts")]
fn trace_reject_ambiguous_nominal_container_aliases() {
    serial_trace_pool().install(|| {
        let mut egraph = EGraph::default();
        egraph.enable_trace().unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype Expr (A i64) (B i64))\
                 (sort P1 (Pair Expr i64))\
                 (sort P2 (Pair Expr i64))\
                 (datatype R1 (H1 P1))\
                 (datatype R2 (H2 P2))\
                 (relation Go (Unit))\
                 (relation Done (Unit))\
                 (Go ())\
                 (rule ((Go u))\
                   ((H1 (pair (A 1) 7))\
                    (H1 (pair (B 2) 7))\
                    (H2 (pair (A 1) 7))\
                    (H2 (pair (B 2) 7))\
                    (Done ())\
                    (union (A 1) (B 2))) :name \"merge-child\")\
                 (run 1)\
                 (check (Done ()))",
            )
            .unwrap();
    });
}

#[test]
fn trace_defer_body_primitive_terms_until_all_guards_pass() {
    let mut egraph = EGraph::default();
    enable_serial_trace(&mut egraph).unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(relation Input (i64))\
             (relation Done (i64))\
             (Input 1)\
             (rule ((Input x) (= y (+ x 1)) (< y 0)) ((Done y)) :name \"dead\")\
             (run 1)",
        )
        .unwrap();

    let state = egraph.capture_catalog.as_ref().unwrap();
    let add = state.op_ids[&ReplayOpKey {
        name: "+".to_owned(),
        inputs: vec!["i64".to_owned(), "i64".to_owned()],
        output: "i64".to_owned(),
    }];
    let mut ordinal = 1;
    while let Some(term) = egraph.replay_term(ReplayTermId::new(ordinal)).unwrap() {
        assert!(!matches!(term, ReplayTerm::Call { op, .. } if op == add));
        ordinal += 1;
    }
}

#[test]
fn trace_fail_closed_when_a_pure_call_depends_on_an_unsupported_primitive() {
    let mut egraph = EGraph::default();
    enable_serial_trace(&mut egraph).unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(sort Fn (UnstableFn (i64 i64) i64))\
             (relation Input (i64))\
             (relation Done (i64))\
             (Input 1)\
             (rule ((Input l))\
               ((Done (+ (unstable-app (unstable-fn \"+\") l 1) 1)))\
               :name \"unsupported-child\")\
             (run 1)",
        )
        .unwrap();
    let failure = egraph
        .with_trace_view(|view| {
            for raw in 1..=view.totals().facts {
                view.fact_terms(core_relations::FactId::new(raw))?;
            }
            Ok(())
        })
        .unwrap_err();
    assert!(
        failure
            .to_string()
            .contains("unsupported causal row origin"),
        "unexpected trace failure: {failure}"
    );
}

#[test]
fn failed_relation_declaration_does_not_poison_origin_catalog() {
    let mut egraph = EGraph::default();
    let error = egraph
        .parse_and_run_program(None, "(relation Broken (MissingSort))")
        .unwrap_err();

    assert!(error.to_string().contains("MissingSort"));
    assert!(!egraph.relation_names.contains("Broken"));
}

#[test]
fn trace_subsume_mark_only_transition_records_no_specialized_capture() {
    let mut egraph = EGraph::default();
    enable_serial_trace(&mut egraph).unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(datatype Expr (A))\
             (relation Go ())\
             (let $a (A))\
             (Go)",
        )
        .unwrap();
    let before = egraph
        .with_trace_view(|view| Ok((view.totals().facts, view.totals().removals)))
        .unwrap();

    egraph
        .parse_and_run_program(
            None,
            "(rule ((Go)) ((subsume (A))) :name \"subsume-existing\")\
             (run 1)",
        )
        .unwrap();

    let after = egraph
        .with_trace_view(|view| Ok((view.totals().facts, view.totals().removals)))
        .unwrap();
    assert_eq!(after, before);
}

#[test]
fn trace_refresh_parent_fact_after_stable_vec_rebuild() {
    serial_trace_pool().install(|| {
        let mut egraph = EGraph::default();
        egraph.enable_trace().unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype Expr (A i64) (B i64))\
                 (sort Exprs (Vec Expr))\
                 (function Hold (Unit) Exprs :no-merge)\
                 (relation Go (Unit))\
                 (relation Done (Unit))\
                 (let $a (A 1))\
                 (Go ())\
                 (rule ((Go u))\
                   ((set (Hold ()) (vec-of (B 2)))\
                    (union (A 1) (B 2))) :name \"merge-child\")\
                 (run 1)",
            )
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(rule ((= v (Hold ()))\
                        (= v (vec-of (A 1))))\
                   ((Done ())) :name \"observe-refresh\")\
                 (run 1)\
                 (check (Done ()))",
            )
            .unwrap();

        egraph
            .with_trace_view(|view| {
                let observed = (1..=view.totals().firings)
                    .find_map(|raw| {
                        view.firing(core_relations::FiringId::new(raw))
                            .ok()
                            .filter(|firing| firing.rule == 1)
                    })
                    .expect("the post-refresh observer should fire");
                let (fact, prior_fact, as_of_edges, position, equalities) = observed
                    .premises
                    .iter()
                    .find_map(|fact| {
                        let record = view.fact(*fact).ok()?;
                        let core_relations::CauseRef::Cause(cause) = record.cause else {
                            return None;
                        };
                        match view.cause(cause).ok()? {
                            core_relations::RawCause::ContainerRefresh {
                                prior_fact,
                                as_of_edges,
                                position,
                                equalities,
                                ..
                            } => Some((
                                *fact,
                                prior_fact,
                                as_of_edges,
                                position,
                                equalities.to_vec(),
                            )),
                            _ => None,
                        }
                    })
                    .expect("the successful check should cite a refreshed immutable parent fact");
                assert_ne!(fact, prior_fact);
                assert_eq!(view.fact(prior_fact)?.table, view.fact(fact)?.table);
                assert!(!equalities.is_empty());
                for pair in &equalities {
                    assert!(
                        !view
                            .explain_raw_equality_support_at(
                                core_relations::RawEqualityEndpoint {
                                    sort: pair.left.sort,
                                    raw: pair.left.raw
                                },
                                core_relations::RawEqualityEndpoint {
                                    sort: pair.right.sort,
                                    raw: pair.right.raw
                                },
                                as_of_edges,
                                position
                            )?
                            .applied
                            .is_empty()
                    );
                }
                Ok(())
            })
            .unwrap();
    });
}

#[test]
fn trace_chain_two_stable_vec_refreshes() {
    serial_trace_pool().install(|| {
        let mut egraph = EGraph::default();
        egraph.enable_trace().unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype Expr (A i64) (B i64) (C i64))\
                 (sort Exprs (Vec Expr))\
                 (function Hold (Unit) Exprs :no-merge)\
                 (relation First (Unit))\
                 (let $a (A 1))\
                 (let $b (B 2))\
                 (First ())\
                 (rule ((First u))\
                   ((set (Hold ()) (vec-of (C 3)))\
                    (union (B 2) (C 3))) :name \"first-refresh\")\
                 (run 1)",
            )
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(relation Second (Unit))\
                 (Second ())\
                 (rule ((Second u))\
                   ((union (A 1) (B 2))) :name \"second-refresh\")\
                 (run 1)",
            )
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(relation Done (Unit))\
                 (rule ((= v (Hold ()))\
                        (= v (vec-of (A 1))))\
                   ((Done ())) :name \"observe-refresh-chain\")\
                 (run 1)\
                 (check (Done ()))",
            )
            .unwrap();

        egraph
            .with_trace_view(|view| {
                let mut chain = None;
                for raw in 1..=view.totals().facts {
                    let latest = view.fact(core_relations::FactId::new(raw))?;
                    let core_relations::CauseRef::Cause(latest_cause) = latest.cause else {
                        continue;
                    };
                    let core_relations::RawCause::ContainerRefresh {
                        wave: latest_wave,
                        prior_fact: middle,
                        as_of_edges: latest_edges,
                        position: latest_position,
                        equalities: latest_pairs,
                    } = view.cause(latest_cause)?
                    else {
                        continue;
                    };
                    let middle_record = view.fact(middle)?;
                    let core_relations::CauseRef::Cause(middle_cause) = middle_record.cause else {
                        continue;
                    };
                    let core_relations::RawCause::ContainerRefresh {
                        wave: middle_wave,
                        prior_fact: original,
                        as_of_edges: middle_edges,
                        position: middle_position,
                        equalities: middle_pairs,
                    } = view.cause(middle_cause)?
                    else {
                        continue;
                    };
                    chain = Some((
                        latest.id,
                        middle,
                        original,
                        latest_wave,
                        middle_wave,
                        (latest_edges, latest_position, latest_pairs.to_vec()),
                        (middle_edges, middle_position, middle_pairs.to_vec()),
                    ));
                    break;
                }
                let (
                    latest,
                    middle,
                    original,
                    latest_wave,
                    middle_wave,
                    latest_landmark,
                    middle_landmark,
                ) = chain.expect("latest Vec fact should point to a prior refreshed fact");
                assert_ne!(latest, middle);
                assert_ne!(middle, original);
                assert!(middle_wave < latest_wave);
                assert_ne!(middle_landmark.0, latest_landmark.0);
                for landmark in [middle_landmark, latest_landmark] {
                    for pair in &landmark.2 {
                        assert!(
                            !view
                                .explain_raw_equality_support_at(
                                    core_relations::RawEqualityEndpoint {
                                        sort: pair.left.sort,
                                        raw: pair.left.raw
                                    },
                                    core_relations::RawEqualityEndpoint {
                                        sort: pair.right.sort,
                                        raw: pair.right.raw
                                    },
                                    landmark.0,
                                    landmark.1
                                )?
                                .applied
                                .is_empty()
                        );
                    }
                }
                Ok(())
            })
            .unwrap();
    });
}

#[test]
fn trace_refresh_nested_vec_parent_fact() {
    serial_trace_pool().install(|| {
        let mut egraph = EGraph::default();
        egraph.enable_trace().unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(sort E)\
                 (sort VE (Vec E))\
                 (sort VVE (Vec VE))\
                 (constructor b () E)\
                 (constructor w (E) E)\
                 (constructor p (VVE) E)\
                 (rewrite (w x) x)\
                 (rewrite (p (vec-of (vec-of (b)))) (b))\
                 (let $nested (p (vec-of (vec-of (w (b))))))\
                 (run-schedule (saturate (run)))\
                 (check (= $nested (b)))",
            )
            .unwrap();

        let p = egraph.capture_catalog.as_ref().unwrap().op_ids[&ReplayOpKey {
            name: "p".into(),
            inputs: vec!["VVE".into()],
            output: "E".into(),
        }];
        egraph.with_trace_view(|view| {
        let mut parent = None;
        for raw in 1..=view.totals().facts {
            let fact = view.fact(core_relations::FactId::new(raw))?;
            let core_relations::CauseRef::Cause(cause) = fact.cause else { continue };
            let core_relations::RawCause::ContainerRefresh { as_of_edges, position, equalities, .. } = view.cause(cause)? else { continue };
            let terms = view.fact_terms(fact.id)?;
            if terms.iter().any(|term| matches!(egraph.replay_term(*term).unwrap(), Some(ReplayTerm::Call { op, .. }) if op == p)) {
                parent = Some((as_of_edges, position, equalities.to_vec()));
                break;
            }
        }
        let (as_of_edges, position, equalities) = parent.expect("the outer p fact should receive an exact nested-container refresh");
        assert!(!equalities.is_empty());
        for pair in &equalities {
            assert!(
                !view.explain_raw_equality_support_at(
                    core_relations::RawEqualityEndpoint { sort: pair.left.sort, raw: pair.left.raw },
                    core_relations::RawEqualityEndpoint { sort: pair.right.sort, raw: pair.right.raw },
                    as_of_edges, position)?.applied.is_empty()
            );
        }
        Ok(())
        }).unwrap();
    });
}

#[test]
fn trace_fail_closed_on_unsupported_container_rebuild() {
    serial_trace_pool().install(|| {
        let mut egraph = EGraph::default();
        egraph.enable_trace().unwrap();
        let error = egraph
            .parse_and_run_program(
                None,
                "(datatype Expr (A i64) (B i64))\
                 (sort Exprs (Set Expr))\
                 (datatype Root (Hold Exprs))\
                 (relation Go (Unit))\
                 (Go ())\
                 (rule ((Go u))\
                   ((Hold (set-of (A 1)))\
                    (Hold (set-of (B 2)))\
                    (union (A 1) (B 2))) :name \"merge-child\")\
                 (run 1)",
            )
            .expect_err("unsupported Set rebuild unexpectedly succeeded");
        assert!(
            error.to_string().contains("SetContainer"),
            "unexpected container-rebuild error: {error}"
        );
    });
}

#[test]
fn trace_container_rebuild_restores_registry_on_error() {
    serial_trace_pool().install(|| {
        let mut egraph = EGraph::default();
        egraph.enable_trace().unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype Expr (A i64) (Wrap Expr))\
                 (sort ExprVec (Vec Expr))\
                 (sort ExprSet (Set Expr))\
                 (relation Go (Unit))\
                 (let $low-vec (vec-of (Wrap (A 1))))\
                 (let $high-vec (vec-of (A 1)))\
                 (let $bad-set (set-of (Wrap (A 1))))\
                 (Go ())",
            )
            .unwrap();
        let low_vec = get_value(&egraph, "$low-vec");
        let high_vec = get_value(&egraph, "$high-vec");
        let bad_set = get_value(&egraph, "$bad-set");
        let low_before = egraph
            .value_to_container::<VecContainer>(low_vec)
            .expect("low Vec must exist before the rejected rebuild")
            .clone();
        let high_before = egraph
            .value_to_container::<VecContainer>(high_vec)
            .expect("high Vec must exist before the rejected rebuild")
            .clone();
        let set_before = egraph
            .value_to_container::<SetContainer>(bad_set)
            .expect("Set must exist before the rejected rebuild")
            .clone();
        let term_state_before = egraph.replay_term_counters().unwrap();

        let failed = egraph
            .parse_and_run_program(
                None,
                "(rule ((Go u))\
                   ((union (Wrap (A 1)) (A 1))) :name \"merge-child\")\
                 (run 1)",
            )
            .expect_err("unsupported Set rebuild unexpectedly succeeded");
        let message = failed.to_string();
        assert!(
            message.contains("SetContainer"),
            "unexpected container-rebuild error: {message}"
        );

        let low_after = egraph
            .value_to_container::<VecContainer>(low_vec)
            .expect("caught rebuild panic dropped the low Vec")
            .clone();
        let high_after = egraph
            .value_to_container::<VecContainer>(high_vec)
            .expect("caught rebuild panic dropped the high Vec")
            .clone();
        let set_after = egraph
            .value_to_container::<SetContainer>(bad_set)
            .expect("caught rebuild panic dropped the Set")
            .clone();
        assert_eq!(low_after, low_before);
        assert_eq!(high_after, high_before);
        assert_eq!(set_after, set_before);
        assert_eq!(
            egraph.replay_term_counters().unwrap(),
            term_state_before,
            "rejected rebuild published anchors, first-wins mappings, or term nodes"
        );
        assert!(
            egraph
                .with_trace_view(|_| Ok(()))
                .unwrap_err()
                .to_string()
                .contains("poisoned"),
            "an unwound native command cannot be retried against the same trace capture"
        );
    });
}

#[test]
fn trace_fail_closed_on_unsupported_container_ancestor() {
    serial_trace_pool().install(|| {
        let mut egraph = EGraph::default();
        egraph.enable_trace().unwrap();
        let error = egraph
            .parse_and_run_program(
                None,
                "(datatype Expr (A i64) (B i64))\
                 (sort Exprs (Vec Expr))\
                 (sort ExprSets (Set Exprs))\
                 (function Hold (Unit) ExprSets :no-merge)\
                 (relation Go (Unit))\
                 (let $a (A 1))\
                 (Go ())\
                 (rule ((Go u))\
                   ((set (Hold ()) (set-of (vec-of (B 2))))\
                    (union (A 1) (B 2))) :name \"merge-child\")\
                 (run 1)",
            )
            .expect_err("unsupported Set ancestor unexpectedly succeeded");
        assert!(
            error.to_string().contains("SetContainer"),
            "unexpected container-ancestor error: {error}"
        );
    });
}

#[test]
fn trace_capture_exact_rule_premise_and_wave() {
    let mut egraph = EGraph::default();
    enable_serial_trace(&mut egraph).unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(datatype Node (N i64 i64))\
             (relation Input (i64 i64))\
             (relation Seen (Node))\
             (Input 3 7)\
             (rule ((Input y x) (= x 7)) ((Seen (N y x))) :name \"derive\")\
             (run 1)\
             (check (Seen (N 3 7)))",
        )
        .unwrap();

    egraph
        .with_trace_view(|view| {
            let firing = view.firing(core_relations::FiringId::new(1))?;
            assert_eq!(firing.rule, 0);
            assert_eq!(firing.wave.get(), 1);
            assert_eq!(firing.premises.len(), 1);
            let terms = view.firing_terms(firing.id)?;
            assert_eq!(terms.len(), 2);
            assert_eq!(
                egraph.replay_term(terms[0]).unwrap(),
                Some(ReplayTerm::Literal {
                    sort: egraph.capture_catalog.as_ref().unwrap().sort_ids["i64"],
                    literal: ReplayLiteral::I64(3),
                })
            );
            assert_eq!(
                egraph.replay_term(terms[1]).unwrap(),
                Some(ReplayTerm::Literal {
                    sort: egraph.capture_catalog.as_ref().unwrap().sort_ids["i64"],
                    literal: ReplayLiteral::I64(7),
                })
            );
            let cataloged_rule = &egraph.capture_catalog.as_ref().unwrap().rule_catalog[0];
            assert_eq!(cataloged_rule.ruleset, "");
            assert_eq!(cataloged_rule.replay_name, "derive");
            assert_eq!(
                cataloged_rule
                    .variables
                    .iter()
                    .map(|variable| (
                        variable.name.as_str(),
                        variable.sort.as_str(),
                        variable.role.clone()
                    ))
                    .collect::<Vec<_>>(),
                vec![
                    ("y", "i64", RuleBindingRole::SurfaceVar),
                    ("x", "i64", RuleBindingRole::SurfaceVar),
                ]
            );
            let premise = view.fact(firing.premises[0])?;
            let core_relations::CauseRef::Cause(source) = premise.cause else {
                panic!("premise lost source cause")
            };
            assert!(matches!(
                view.cause(source)?,
                core_relations::RawCause::Source(_)
            ));
            for raw in 1..=view.totals().facts {
                if let core_relations::CauseRef::Rule(id) =
                    view.fact(core_relations::FactId::new(raw))?.cause
                {
                    assert_eq!(id, firing.id);
                }
            }
            let root = view.check_root(0)?;
            assert_eq!(root.check, 0);
            assert_eq!(root.wave.get(), 1);
            assert!(!root.premises.is_empty());
            assert!(root.equalities.is_empty());
            Ok(())
        })
        .unwrap();
}

#[test]
fn trace_preserve_distinct_check_equality_terms() {
    let mut egraph = EGraph::default();
    enable_serial_trace(&mut egraph).unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(datatype Expr (A i64) (B i64))\
             (relation Go (Unit))\
             (let $lhs (A 1))\
             (Go ())\
             (rule ((Go u)) ((union (A 1) (B 2))) :name \"merge\")\
             (run 1)\
             (check (= $lhs (B 2)))",
        )
        .unwrap();

    egraph
        .with_trace_view(|view| {
            let root = view.check_root(0)?;
            assert_eq!(root.premises.len(), 2);
            assert_eq!(root.equalities.len(), 1);
            let (left, right) = root.equalities[0];
            assert_eq!(left.sort, right.sort);
            assert_ne!(
                left.raw, right.raw,
                "the check root preserves each premise's immutable creation occurrence"
            );
            assert_ne!(left.term, right.term);

            let state = egraph.capture_catalog.as_ref().unwrap();
            let a = state.op_ids[&ReplayOpKey {
                name: "A".into(),
                inputs: vec!["i64".into()],
                output: "Expr".into(),
            }];
            let b = state.op_ids[&ReplayOpKey {
                name: "B".into(),
                inputs: vec!["i64".into()],
                output: "Expr".into(),
            }];
            assert!(matches!(
                egraph.replay_term(left.term).unwrap(),
                Some(ReplayTerm::Call { op, .. }) if op == a
            ));
            assert!(matches!(
                egraph.replay_term(right.term).unwrap(),
                Some(ReplayTerm::Call { op, .. }) if op == b
            ));
            let explanation =
                view.explain_equality_support_at(left, right, root.as_of_edges, root.position)?;
            assert_eq!(
                explanation.applied.as_ref(),
                [core_relations::AppliedEqualityId::new(1)]
            );
            assert!(matches!(
                view.applied_equality(core_relations::AppliedEqualityId::new(1))?.reason,
                core_relations::EqualityReason::RuleUnion(rule) if view.firing(rule)?.rule == 0
            ));
            Ok(())
        })
        .unwrap();
}

#[test]
fn trace_waves_are_cumulative_across_run_commands() {
    let mut egraph = EGraph::default();
    enable_serial_trace(&mut egraph).unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(datatype Node (N i64))\
             (relation Seed (i64))\
             (relation Seen (Node))\
             (rule ((Seed x)) ((Seen (N x))) :name \"derive\")\
             (Seed 7)\
             (run 1)\
             (Seed 8)\
             (run 1)",
        )
        .unwrap();

    egraph
        .with_trace_view(|view| {
            let waves = (1..=view.totals().firings)
                .filter_map(|raw| view.firing(core_relations::FiringId::new(raw)).ok())
                .filter(|firing| firing.rule == 0)
                .map(|firing| firing.wave.get())
                .collect::<Vec<_>>();
            assert_eq!(waves, [1, 2]);
            Ok(())
        })
        .unwrap();
}

#[test]
fn parsed_input_digest_is_optional() {
    let directory = std::env::temp_dir().join(format!(
        "egglog-input-digest-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(directory.join("rows.tsv"), "first\nsecond\n").unwrap();

    let mut egraph = EGraph {
        fact_directory: Some(directory.clone()),
        ..Default::default()
    };
    egraph
        .parse_and_run_program(None, "(relation R (String))")
        .unwrap();
    let function_type = egraph.type_info.get_func_type("R").unwrap();
    let uncaptured = EGraph::read_input_file(
        egraph.fact_directory.as_deref(),
        function_type,
        &Span::Panic,
        "rows.tsv",
        false,
    )
    .unwrap();
    assert_eq!(uncaptured.digest, None);

    let captured = EGraph::read_input_file(
        egraph.fact_directory.as_deref(),
        function_type,
        &Span::Panic,
        "rows.tsv",
        true,
    )
    .unwrap();
    let expected: [u8; 32] = Sha256::digest(b"first\nsecond\n").into();
    assert_eq!(captured.digest, Some(expected));
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn trace_batch_tsv_rows_with_exact_physical_sources() {
    let directory = std::env::temp_dir().join(format!(
        "egglog-trace-input-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(directory.join("leaf.tsv"), "7\n7\n9\n").unwrap();
    std::fs::write(directory.join("edge.tsv"), "1\t2\n").unwrap();
    std::fs::write(directory.join("score.tsv"), "1\t10\n").unwrap();

    let mut egraph = EGraph {
        fact_directory: Some(directory.clone()),
        ..Default::default()
    };
    enable_serial_trace(&mut egraph).unwrap();
    let result = egraph.parse_and_run_program(
        None,
        r#"
            (datatype Node (Leaf i64))
            (relation Edge (i64 i64))
            (function Score (i64) i64 :merge old)
            (relation SeenScore (i64))
            (input Leaf "leaf.tsv")
            (input Edge "edge.tsv")
            (input Score "score.tsv")
            (rule ((= value (Score 1))) ((SeenScore value)))
            (run 1)
            (check (Edge 1 2))
            (check (SeenScore 10))
        "#,
    );
    result.unwrap();

    std::fs::write(directory.join("bad.tsv"), "1\nnot-an-integer\n").unwrap();
    let mut rejected = EGraph {
        fact_directory: Some(directory.clone()),
        ..Default::default()
    };
    enable_serial_trace(&mut rejected).unwrap();
    let error = rejected
        .parse_and_run_program(
            None,
            "(datatype BadNode (BadLeaf i64)) (input BadLeaf \"bad.tsv\")",
        )
        .unwrap_err();
    assert!(matches!(error, Error::InputFileFormatError(_)));
    assert!(
        rejected
            .with_trace_view(|_| Ok(()))
            .unwrap_err()
            .to_string()
            .contains("poisoned"),
        "a command that fails after entering trace execution must make the capture unusable instead of reusing reserved identities"
    );
    std::fs::remove_dir_all(&directory).ok();

    egraph
        .with_trace_view(|view| {
            let mut source_facts = Vec::new();
            for raw in 1..=view.totals().facts {
                let fact = view.fact(core_relations::FactId::new(raw))?;
                let core_relations::CauseRef::Cause(cause) = fact.cause else {
                    continue;
                };
                if let core_relations::RawCause::Source(source) = view.cause(cause)? {
                    source_facts.push((source.clone(), fact.id));
                }
            }
            assert_eq!(source_facts.len(), 4);
            for expected in [
                SourceRef::InputRow {
                    command: 0,
                    line: 1,
                },
                SourceRef::InputRow {
                    command: 0,
                    line: 3,
                },
                SourceRef::InputRow {
                    command: 1,
                    line: 1,
                },
                SourceRef::InputRow {
                    command: 2,
                    line: 1,
                },
            ] {
                assert!(source_facts.iter().any(|(source, _)| *source == expected));
            }
            assert!(!source_facts.iter().any(|(source, _)| {
                *source
                    == SourceRef::InputRow {
                        command: 0,
                        line: 2,
                    }
            }));
            for (_, fact) in source_facts
                .iter()
                .filter(|(source, _)| matches!(source, SourceRef::InputRow { command: 0, .. }))
            {
                assert!(view.fact_terms(*fact)?.iter().copied().any(|term| {
                    !term.is_missing()
                        && matches!(
                            egraph.replay_term(term).unwrap(),
                            Some(ReplayTerm::Call { .. })
                        )
                }));
            }
            Ok(())
        })
        .unwrap();
}

#[test]
fn capture_catalog_tracks_expanded_order_and_anonymous_rule_identity() {
    let mut egraph = EGraph::default();
    enable_serial_trace(&mut egraph).unwrap();
    egraph
        .parse_and_run_program(
            None,
            r#"
                (datatype Expr (Num i64))
                (let $seed (Num 1))
                (relation Seen (i64))
                (Seen 1)
                (rule ((Seen x)) ((Seen x)))
                (run 1)
                (check (Seen 1))
            "#,
        )
        .unwrap();

    let catalog = egraph.capture_catalog.as_ref().unwrap();
    let commands = catalog
        .command_catalog
        .iter()
        .map(|entry| entry.command.to_string())
        .collect::<Vec<_>>();
    assert!(
        commands.windows(2).any(
            |pair| pair[0].starts_with("(sort Expr") && pair[1].starts_with("(constructor Num")
        ),
        "datatype expansion must be cataloged in execution order: {commands:#?}"
    );
    let datatype_surface = catalog
        .command_catalog
        .iter()
        .filter(|entry| {
            matches!(
                &entry.command,
                Command::Sort { name, .. } if name == "Expr"
            ) || matches!(
                &entry.command,
                Command::Constructor { name, .. } if name == "Num"
            )
        })
        .map(|entry| entry.surface_command)
        .collect::<HashSet<_>>();
    assert_eq!(datatype_surface.len(), 1);
    let datatype_surface = *datatype_surface.iter().next().unwrap();
    assert!(matches!(
        catalog.surface_command_catalog[datatype_surface],
        Some(Command::Datatype { .. })
    ));
    let global_entries = catalog
        .command_catalog
        .iter()
        .filter(|entry| {
            matches!(
                &entry.command,
                Command::Function { name, .. } if name == "$seed"
            ) || entry.command.to_string().starts_with("(set ($seed)")
        })
        .collect::<Vec<_>>();
    assert_eq!(global_entries.len(), 2);
    assert_eq!(
        global_entries[0].surface_command,
        global_entries[1].surface_command
    );
    assert!(matches!(
        catalog.surface_command_catalog[global_entries[0].surface_command],
        Some(Command::Action(Action::Let(..)))
    ));
    assert_eq!(catalog.rule_catalog.len(), 1);
    let generated_name = format!(
        "@__slice_replay_rule_s{}",
        catalog.command_catalog[catalog.rule_catalog[0].command].surface_command
    );
    assert_eq!(catalog.rule_catalog[0].replay_name, generated_name);
    let rule_command = &catalog.command_catalog[catalog.rule_catalog[0].command].command;
    let Command::Rule { rule } = rule_command else {
        panic!("cataloged captured rule is not a normalized rule: {rule_command}")
    };
    assert_eq!(rule.name, generated_name);
    assert!(
        catalog
            .source_commands
            .contains_key(&SourceRef::Synthetic(0))
    );
    assert!(
        catalog
            .source_commands
            .contains_key(&SourceRef::Synthetic(1))
    );
    assert!(catalog.check_commands.contains_key(&0));
}

#[test]
fn replay_alpha_renames_anonymous_rule_around_user_name_collision() {
    let mut egraph = EGraph::default();
    enable_serial_trace(&mut egraph).unwrap();
    egraph
        .parse_and_run_program(
            None,
            r#"
                (relation Seed (i64))
                (relation Anonymous (i64))
                (relation Named (i64))
                (Seed 1)
                (rule ((Seed x)) ((Anonymous x)))
            "#,
        )
        .unwrap();
    let internal_name = egraph.capture_catalog.as_ref().unwrap().rule_catalog[0]
        .replay_name
        .clone();
    let generated_name = internal_name
        .strip_prefix(crate::util::INTERNAL_SYMBOL_PREFIX)
        .unwrap()
        .to_owned();
    egraph
        .parse_and_run_program(
            None,
            &format!(
                r#"
                    (rule ((Seed x)) ((Named x)) :name "{generated_name}")
                    (run 1)
                    (check (Anonymous 1))
                    (check (Named 1))
                "#
            ),
        )
        .unwrap();

    let rendered = crate::slicing::slice_all_checks(&egraph).unwrap();
    assert!(rendered.contains(&format!(r#":name "{generated_name}""#)));
    assert!(rendered.contains(&format!(r#":name "{generated_name}_1""#)));

    let mut proof = EGraph::default().with_proofs_enabled().with_proof_testing();
    serial_trace_pool()
        .install(|| proof.parse_and_run_program(None, &rendered))
        .unwrap();
}

#[test]
fn capture_catalog_rejects_stateful_command_boundaries_before_mutation() {
    let mut egraph = EGraph::default();
    enable_serial_trace(&mut egraph).unwrap();
    let push = egraph.parse_and_run_program(None, "(push)").unwrap_err();
    assert!(push.to_string().contains("does not support push/pop"));
    assert!(egraph.pushed_egraph.is_none());

    let catalog_len = egraph
        .capture_catalog
        .as_ref()
        .unwrap()
        .command_catalog
        .len();
    let nested = egraph
        .parse_and_run_program(None, "(fail (let $causal_leak 1))")
        .unwrap_err();
    assert!(nested.to_string().contains("nested fail commands"));
    assert_eq!(
        egraph
            .capture_catalog
            .as_ref()
            .unwrap()
            .command_catalog
            .len(),
        catalog_len,
        "fail must be rejected before global lowering can lift a declaration"
    );
    assert!(
        egraph
            .get_function_names()
            .iter()
            .all(|name| !name.contains("causal_leak"))
    );
    let datatype = egraph
        .parse_and_run_program(None, "(fail (datatype CausalLeaked (CausalLeak)))")
        .unwrap_err();
    assert!(datatype.to_string().contains("nested fail commands"));
    assert!(egraph.get_sort_by_name("CausalLeaked").is_none());
    assert!(
        !egraph
            .get_function_names()
            .iter()
            .any(|name| name == "CausalLeak")
    );
    let resolve = egraph
        .resolve_program(None, "(relation CausalHidden (i64))")
        .unwrap_err();
    assert!(resolve.to_string().contains("resolve_program"));
    assert!(egraph.get_function("CausalHidden").is_none());
    let sort = egraph
        .declare_sort("CausalDirectSort", &None, span!())
        .unwrap_err();
    assert!(sort.to_string().contains("registration after capture"));
    assert!(egraph.get_sort_by_name("CausalDirectSort").is_none());
    assert!(egraph.with_trace_view(|_| Ok(())).is_ok());

    let mut proof = EGraph::new_with_proofs();
    let proof_error = enable_serial_trace(&mut proof).unwrap_err();
    assert!(
        proof_error
            .to_string()
            .contains("ordinary, non-proof graph")
    );
}

#[test]
fn trace_user_command_authority_is_not_granted_by_name() {
    struct Impostor(std::sync::Arc<std::sync::atomic::AtomicBool>);

    impl UserDefinedCommand for Impostor {
        fn update(
            &self,
            _egraph: &mut EGraph,
            _args: &[Expr],
        ) -> Result<Vec<CommandOutput>, Error> {
            self.0.store(true, std::sync::atomic::Ordering::SeqCst);
            Ok(Vec::new())
        }
    }

    let called = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let mut egraph = EGraph::default();
    egraph
        .add_command(
            "run-schedule".into(),
            std::sync::Arc::new(Impostor(called.clone())),
        )
        .unwrap();
    enable_serial_trace(&mut egraph).unwrap();
    let error = egraph
        .parse_and_run_program(None, "(run-schedule safe-looking-ruleset)")
        .unwrap_err();
    assert!(error.to_string().contains("does not support user-defined"));
    assert!(!called.load(std::sync::atomic::Ordering::SeqCst));
    assert!(
        egraph
            .with_trace_view(|_| Ok(()))
            .unwrap_err()
            .to_string()
            .contains("poisoned")
    );
}

#[test]
fn trace_direct_mutation_apis_fail_before_effects() {
    struct Noop(std::sync::Arc<std::sync::atomic::AtomicBool>);

    impl UserDefinedCommand for Noop {
        fn update(
            &self,
            _egraph: &mut EGraph,
            _args: &[Expr],
        ) -> Result<Vec<CommandOutput>, Error> {
            self.0.store(true, std::sync::atomic::Ordering::SeqCst);
            Ok(Vec::new())
        }
    }

    let command_called = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let update_called = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let mut egraph = EGraph::default();
    egraph
        .add_command(
            "causal-noop".into(),
            std::sync::Arc::new(Noop(command_called.clone())),
        )
        .unwrap();
    enable_serial_trace(&mut egraph).unwrap();
    egraph
        .parse_and_run_program(None, "(relation R (i64)) (ruleset rs)")
        .unwrap();

    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| egraph.push())).is_err());
    assert!(egraph.pushed_egraph.is_none());
    assert!(
        egraph
            .pop()
            .unwrap_err()
            .to_string()
            .contains("EGraph::pop")
    );
    assert!(
        egraph
            .step_rules("rs")
            .unwrap_err()
            .to_string()
            .contains("cataloged schedule")
    );
    assert!(
        egraph
            .clear_function("R")
            .unwrap_err()
            .to_string()
            .contains("clear_function")
    );
    assert!(
        egraph
            .eval_expr(&Expr::Lit(span!(), Literal::Int(1)))
            .unwrap_err()
            .to_string()
            .contains("eval_expr")
    );
    assert!(
        egraph
            .run_user_defined_command("causal-noop", &[])
            .unwrap_err()
            .to_string()
            .contains("direct user-defined")
    );
    assert!(!command_called.load(std::sync::atomic::Ordering::SeqCst));
    let update_called_in_closure = update_called.clone();
    assert!(
        egraph
            .update(move |_state| {
                update_called_in_closure.store(true, std::sync::atomic::Ordering::SeqCst);
                Ok(())
            })
            .unwrap_err()
            .to_string()
            .contains("EGraph::update")
    );
    assert!(!update_called.load(std::sync::atomic::Ordering::SeqCst));
    assert!(
        egraph
            .query(&[], ast::Facts(Vec::new()))
            .unwrap_err()
            .to_string()
            .contains("EGraph::query")
    );
    assert_eq!(egraph.get_size("R"), 0);
    assert!(egraph.with_trace_view(|_| Ok(())).is_ok());
}

#[test]
fn trace_wave_spans_multiple_native_rebuild_timestamps() {
    let mut egraph = EGraph::default();
    enable_serial_trace(&mut egraph).unwrap();
    egraph
        .parse_and_run_program(
            None,
            "(datatype Expr (A) (B) (F Expr) (G Expr))\
             (relation Go (Unit))\
             (let $ga (G (F (A))))\
             (let $gb (G (F (B))))\
             (Go ())\
             (rule ((Go u)) ((union (A) (B))) :name \"merge-leaves\")\
             (run 1)\
             (check (= $ga $gb))",
        )
        .unwrap();

    egraph
        .with_trace_view(|view| {
            assert!(view.totals().applied_equalities >= 3);
            for raw in 1..=view.totals().applied_equalities {
                assert_eq!(
                    view.applied_equality(core_relations::AppliedEqualityId::new(raw))?
                        .wave
                        .get(),
                    1,
                    "direct and multi-pass congruence edges belong to one replay wave"
                );
            }
            Ok(())
        })
        .unwrap();
}

#[test]
fn trace_reject_late_rule_activation_without_switching_modes() {
    let mut egraph = EGraph::default();
    egraph
        .parse_and_run_program(
            None,
            "(relation A (i64)) (relation B (i64))\
             (rule ((A x)) ((B x)))",
        )
        .unwrap();

    let error = enable_serial_trace(&mut egraph).unwrap_err();
    assert!(error.to_string().contains("replay catalog is complete"));
    egraph
        .parse_and_run_program(None, "(A 1) (run 1) (check (B 1))")
        .unwrap();
}

#[test]
fn query_error_restores_named_rule_metadata() {
    let mut egraph = EGraph::new_with_term_encoding();
    egraph
        .parse_and_run_program(None, "(relation R (i64)) (R 1)")
        .unwrap();
    let main_checkpoint = egraph.type_info.named_rule_checkpoint();
    let original_checkpoint = egraph
        .proof_state
        .original_typechecking
        .as_ref()
        .unwrap()
        .type_info
        .named_rule_checkpoint();

    egraph
        .query(crate::vars![x: i64], crate::facts![(R x)])
        .unwrap_err();

    assert_eq!(egraph.type_info.named_rule_checkpoint(), main_checkpoint);
    assert_eq!(
        egraph
            .proof_state
            .original_typechecking
            .as_ref()
            .unwrap()
            .type_info
            .named_rule_checkpoint(),
        original_checkpoint
    );
}
#[test]
fn unstable_fn_panic_cache_is_persistent_and_bounded_across_rule_specialization() {
    let mut egraph = EGraph::default();
    egraph
        .parse_and_run_program(
            None,
            r#"
            (ruleset owned)
            (sort Fn (UnstableFn (i64) i64))
            (function id (i64) i64 :merge old)
            (function slot () Fn :merge old)
            (rule ()
                ((set (slot) (unstable-fn "id")))
                :ruleset owned
                :name "owns-panic")
            "#,
        )
        .unwrap();

    let panic_id = egraph.unstable_fn_panic_ids["id"];
    assert_eq!(egraph.unstable_fn_panic_ids.len(), 1);

    // Temporary naive specializations reuse the EGraph-lifetime callback;
    // they neither grow the cache nor take rule-owned references.
    for _ in 0..3 {
        egraph
            .parse_and_run_program(None, r#"(run-schedule (run-rule ("owns-panic" ())))"#)
            .unwrap();
        assert_eq!(egraph.unstable_fn_panic_ids.len(), 1);
        assert_eq!(egraph.unstable_fn_panic_ids["id"], panic_id);
    }

    // Freeing the source rule must not invalidate FunctionContainer values
    // already stored in the e-graph.
    let permanent_rule = match &egraph.rulesets["owned"] {
        Ruleset::Rules(rules) => rules["owns-panic"].backend_id,
        Ruleset::Combined(_) => unreachable!(),
    };
    egraph.backend.free_rule(permanent_rule);
    assert_eq!(egraph.unstable_fn_panic_ids.len(), 1);
    assert_eq!(egraph.unstable_fn_panic_ids["id"], panic_id);

    let shared = egraph.backend.new_panic(unstable_fn_panic_message("id"));
    assert_eq!(
        shared, panic_id,
        "the persistent cache must keep the embedded callback registered"
    );
    egraph.backend.free_external_func(shared);
}

#[test]
fn direct_unstable_fn_preparation_uses_the_persistent_cache() {
    let mut egraph = EGraph::default();
    egraph
        .parse_and_run_program(
            None,
            r#"
            (sort Fn (UnstableFn (i64) i64))
            (function id (i64) i64 :merge old)
            "#,
        )
        .unwrap();
    let output = egraph.get_sort_by_name("Fn").unwrap().clone();
    let mut parser = crate::ast::Parser::default();

    for _ in 0..2 {
        let expr = parser
            .get_expr_from_string(None, r#"(unstable-fn "id")"#)
            .unwrap();
        let resolved = egraph
            .typecheck_expr_with_bindings_and_output(&expr, &[], output.clone(), Context::Pure)
            .unwrap();
        let (_, bindings) = egraph
            .prepare_unstable_fn_targets_for_eval(&resolved)
            .unwrap();
        assert_eq!(bindings.len(), 1);
        assert_eq!(egraph.unstable_fn_panic_ids.len(), 1);
    }

    let expr = parser
        .get_expr_from_string(None, r#"(unstable-fn "missing")"#)
        .unwrap();
    let resolved = egraph
        .typecheck_expr_with_bindings_and_output(&expr, &[], output, Context::Pure)
        .unwrap();
    let error = egraph
        .prepare_unstable_fn_targets_for_eval(&resolved)
        .unwrap_err();
    assert!(error.to_string().contains("No resolution for \"missing\""));
    assert_eq!(
        egraph.unstable_fn_panic_ids.len(),
        1,
        "failed direct preparation must not commit its pending panic"
    );
}
#[test]
fn let_check_alias_is_a_constant_in_checks() {
    let mut egraph = EGraph::default();
    egraph
        .parse_and_run_program(
            None,
            r#"
            (datatype E (A i64))
            (A 1)
            (A 2)
            (let-check $a (A 1))
            "#,
        )
        .unwrap();

    egraph
        .parse_and_run_program(None, "(check (= $a (A 1)))")
        .unwrap();
    let error = egraph
        .parse_and_run_program(None, "(check (= $a (A 2)))")
        .expect_err("the checked alias must not act as a free query variable");
    assert!(matches!(error, Error::CheckError(..)));
}

#[test]
fn let_check_constructor_miss_is_atomic() {
    let mut egraph = EGraph::default();
    egraph
        .parse_and_run_program(None, "(datatype E (A i64))")
        .unwrap();
    let before = egraph.num_tuples();

    let error = egraph
        .parse_and_run_program(None, "(let-check $missing (A 1))")
        .unwrap_err();

    assert!(error.to_string().contains("lookup"));
    assert_eq!(egraph.num_tuples(), before);
    assert!(!egraph.checked_aliases.contains_key("$missing"));
    assert!(!egraph.checked_alias_types.contains_key("$missing"));
    assert!(!egraph.names.contains_canonical("missing"));

    // Neither the alias table nor the namespace may retain a ghost name.
    egraph.parse_and_run_program(None, "(A 1)").unwrap();
    egraph
        .parse_and_run_program(None, "(let-check $missing (A 1))")
        .unwrap();
}

#[test]
fn let_check_runs_through_proof_encoding_without_fiat_rows() {
    let mut egraph = EGraph::new_with_proofs();
    egraph
        .parse_and_run_program(
            None,
            r#"
            (datatype E (A i64))
            (A 1)
            "#,
        )
        .unwrap();
    let tuples_before = egraph.num_tuples();
    egraph
        .parse_and_run_program(None, "(let-check $a (A 1))")
        .unwrap();
    assert_eq!(egraph.num_tuples(), tuples_before);
    egraph
        .parse_and_run_program(None, "(check (= $a (A 1)))")
        .unwrap();
}

#[test]
fn let_check_proof_lookup_miss_does_not_publish_proof_or_alias_state() {
    let mut egraph = EGraph::new_with_proofs();
    egraph
        .parse_and_run_program(None, "(datatype E (A i64))")
        .unwrap();
    let tuples_before = egraph.num_tuples();
    let proof_program_before = egraph.proof_check_program.len();

    let error = egraph
        .parse_and_run_program(None, "(let-check $missing (A 1))")
        .unwrap_err();

    assert!(error.to_string().contains("lookup"));
    assert_eq!(egraph.num_tuples(), tuples_before);
    assert_eq!(egraph.proof_check_program.len(), proof_program_before);
    assert!(!egraph.checked_aliases.contains_key("$missing"));
    assert!(!egraph.checked_alias_types.contains_key("$missing"));
    assert!(!egraph.names.contains_canonical("missing"));
}

#[test]
fn let_check_rejects_non_pure_primitives_and_unprefixed_names() {
    let mut egraph = EGraph::default();
    egraph.add_full_primitive(FullOnly, None);
    let error = egraph
        .parse_and_run_program(None, "(let-check $effect (full-only))")
        .unwrap_err();
    assert!(error.to_string().contains("Unbound function full-only"));
    assert!(!egraph.checked_aliases.contains_key("$effect"));

    let error = egraph
        .parse_and_run_program(None, "(let-check plain 1)")
        .unwrap_err();
    assert!(matches!(
        error,
        Error::TypeError(TypeError::CheckedAliasMissingPrefix { .. })
    ));
}
#[test]
fn let_check_allows_only_bounded_container_interning() {
    for mut egraph in [EGraph::default(), EGraph::new_with_proofs()] {
        egraph
            .parse_and_run_program(
                None,
                r#"
                (sort P (Pair i64 i64))
                (sort V (Vec i64))
                (let-check $p (pair 1 2))
                (let-check $v (vec-of (pair-first $p) 3))
                (let-check $n (vec-length $v))
                "#,
            )
            .unwrap();
    }

    let mut egraph = EGraph::default();
    let error = egraph
        .parse_and_run_program(
            None,
            r#"
            (sort S (Set i64))
            (let-check $set (set-of 1))
            "#,
        )
        .unwrap_err();
    assert!(error.to_string().contains("unsupported container"));
    assert!(!egraph.checked_aliases.contains_key("$set"));
}

#[test]
fn let_check_expected_sort_is_enforced_without_ghost_aliases() {
    let mut egraph = EGraph::default();
    let expr = egraph.parser.get_expr_from_string(None, "(+ 1 2)").unwrap();
    let command = Command::LetCheck {
        span: expr.span(),
        name: "$n".to_owned(),
        expr: expr.clone(),
        expected_sort: Some("bool".to_owned()),
    };
    let error = egraph.run_program(vec![command]).unwrap_err();
    assert!(matches!(
        error,
        Error::TypeError(TypeError::Mismatch { .. })
    ));
    assert!(!egraph.checked_alias_types.contains_key("$n"));
    assert!(!egraph.names.contains_canonical("n"));

    egraph
        .run_program(vec![Command::LetCheck {
            span: expr.span(),
            name: "$n".to_owned(),
            expr,
            expected_sort: Some("i64".to_owned()),
        }])
        .unwrap();
}
