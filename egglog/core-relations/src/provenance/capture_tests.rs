use super::*;

#[test]
fn capture_view_rejects_reentrancy_without_poisoning_capture() {
    let trace = Trace::default();
    let error = trace
        .with_view(|_| trace.with_view(|_| Ok(())))
        .unwrap_err();
    assert!(matches!(
        error,
        TraceViewError::Invalid(ref message) if message.contains("not reentrant")
    ));
    trace
        .with_view(|_| {
            std::thread::scope(|scope| {
                let nested = scope.spawn(|| trace.with_view(|_| Ok(()))).join().unwrap();
                assert!(matches!(
                    nested,
                    Err(TraceViewError::Invalid(ref message))
                        if message.contains("not reentrant")
                ));
            });
            Ok(())
        })
        .unwrap();
    assert!(trace.with_view(|_| Ok(())).is_ok());
}

#[test]
fn panicking_capture_view_callback_does_not_poison_capture_locks() {
    let trace = Trace::default();
    let failure = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = trace.with_view(|_| -> Result<(), TraceViewError> { panic!("inspection panic") });
    }));
    assert!(failure.is_err());
    assert!(trace.with_view(|_| Ok(())).is_ok());
}

#[test]
fn physical_rekey_collision_with_same_fact_records_no_logical_transition() {
    let trace = Trace::default();
    let fact = FactId::new(17);
    let sort = ReplaySortId::new(3);
    let pair = TypedCellEquality {
        column: crate::ColumnId::new(0),
        left: EqualityEndpoint {
            sort,
            term: ReplayTermId::MISSING,
            raw: Value::new(20),
        },
        right: EqualityEndpoint {
            sort,
            term: ReplayTermId::MISSING,
            raw: Value::new(10),
        },
    };
    let prepared = || {
        PreparedRekey::from_staged(
            TableId::new(4),
            Wave::new(2),
            fact,
            HistoryPosition::new(9),
            &[pair],
        )
    };

    trace.commit_prepared_rekey(prepared(), RekeyOutcome::Absorbed(fact));
    trace.commit_prepared_rekey(prepared(), RekeyOutcome::Replaced(fact));

    assert!(trace.0.arena.lock().unwrap().rekeys.is_empty());
    assert_eq!(trace.history_boundary(), HistoryPosition::new(0));

    trace.commit_prepared_rekey(prepared(), RekeyOutcome::Absorbed(FactId::new(18)));
    assert_eq!(trace.0.arena.lock().unwrap().rekeys.len(), 1);
    assert_eq!(trace.history_boundary(), HistoryPosition::new(1));
}

#[test]
fn structural_occurrence_rejects_uncertified_non_table_calls() {
    let trace = Trace::default();
    let sort = ReplaySortId::new(1);
    let certified_op = ReplayOpId::new(10);
    let unknown_op = ReplayOpId::new(11);
    let certified_raw = Value::new_const(10);
    let unknown_raw = Value::new_const(11);
    let certified_term = trace
        .intern_call(sort, certified_op, &[], certified_raw)
        .unwrap();
    let unknown_term = trace
        .intern_call(sort, unknown_op, &[], unknown_raw)
        .unwrap();
    trace.register_rule_term_recipe(
        7,
        TermRecipe {
            current_roots: [Some(Arc::new(TermTemplate::Call {
                sort,
                op: certified_op,
                children: Arc::from([]),
            }))]
            .into(),
        },
    );

    trace
        .with_view(|view| {
            let support = view.explain_term_occurrence_at(
                certified_term,
                sort,
                certified_raw,
                HistoryPosition::new(0),
                FactId::MISSING,
            )?;
            assert!(
                support.is_some(),
                "a certified pure call reexecutes in replay"
            );
            Ok(())
        })
        .unwrap();

    let error = trace
        .with_view(|view| {
            view.explain_term_occurrence_at(
                unknown_term,
                sort,
                unknown_raw,
                HistoryPosition::new(0),
                FactId::MISSING,
            )
        })
        .unwrap_err();
    assert!(
        matches!(error, TraceViewError::Invalid(ref message) if message.contains("no registered constructor or certified replay recipe")),
        "unknown non-table calls must fail closed: {error:?}"
    );
}

#[test]
fn derived_fact_owns_the_terms_for_its_committed_row() {
    let trace = Trace::default();
    let table = TableId::new_const(0);
    let value_sort = ReplaySortId::new(1);
    let timestamp_sort = ReplaySortId::new(2);
    trace
        .register_table_layout(table, &[Some(value_sort), Some(timestamp_sort)])
        .unwrap();
    let row = [Value::new_const(7), Value::new_const(0)];
    let terms = [
        trace.intern_literal(value_sort, ReplayLiteral::I64(7), row[0]),
        trace.intern_literal(timestamp_sort, ReplayLiteral::I64(0), row[1]),
    ];
    let origin = trace.install_source_row(table, &row, &terms).unwrap();
    let source_cause = trace.source_draft(SourceRef::Synthetic(0));
    let mut source_batch = trace.new_batch();
    let source = source_batch.record_fact_with_origin(table, source_cause, &row, origin);
    source_batch.publish();
    trace.finalize_wave();
    trace
        .with_view(|view| {
            assert_eq!(view.fact_terms(source)?.as_ref(), &terms);
            Ok(())
        })
        .unwrap();

    let binding_sources = [
        ReplayBindingSource::Premise {
            representative: PremiseOccurrence {
                premise: 0,
                column: 0,
            },
        },
        ReplayBindingSource::Premise {
            representative: PremiseOccurrence {
                premise: 0,
                column: 1,
            },
        },
    ];
    let [(lane, rule_cause)] = trace
        .register_firings(7, Wave::new(1), 1, &binding_sources, &[source], &[0])
        .try_into()
        .unwrap();
    assert_eq!(lane, 0);
    let mut derived_batch = trace.new_batch();
    let derived = derived_batch.record_fact_with_origin(table, rule_cause, &row, origin);
    derived_batch.publish();
    trace.finalize_wave();

    trace
        .with_view(|view| {
            assert_eq!(
                view.fact_terms(derived)?.as_ref(),
                &terms,
                "fact terms belong to the immutable committed row, not its Source cause"
            );
            Ok(())
        })
        .unwrap();

    let [(lane, next_cause)] = trace
        .register_firings(8, Wave::new(2), 1, &binding_sources, &[derived], &[0])
        .try_into()
        .unwrap();
    assert_eq!(lane, 0);
    let mut next_batch = trace.new_batch();
    next_batch.record_fact_with_origin(table, next_cause, &row, origin);
    next_batch.publish();
    trace.finalize_wave();
    let next_firing = next_cause
        .firing()
        .expect("registered firing lost its rule cause");
    trace
        .with_view(|view| {
            assert_eq!(view.firing(next_firing)?.rule, 8);
            assert_eq!(
                view.firing_terms(next_firing)?.as_ref(),
                &terms,
                "a later rule must resolve terms through a derived FactId"
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn promoted_firings_reconstruct_current_terms_from_static_recipes() {
    let trace = Trace::default();
    let table = TableId::new_const(0);
    let sort = ReplaySortId::new(1);
    trace.register_table_layout(table, &[Some(sort)]).unwrap();

    let source_row = [Value::new_const(7)];
    let source_term = trace.intern_literal(sort, ReplayLiteral::I64(7), source_row[0]);
    let source_origin = trace
        .install_source_row(table, &source_row, &[source_term])
        .unwrap();
    let source_cause = trace.source_draft(SourceRef::Synthetic(0));
    let mut source_batch = trace.new_batch();
    let source_fact =
        source_batch.record_fact_with_origin(table, source_cause, &source_row, source_origin);
    source_batch.publish();
    trace.finalize_wave();

    let constant_value = Value::new_const(8);
    let constant_term = trace.intern_literal(sort, ReplayLiteral::I64(8), constant_value);
    let current_value = Value::new_const(9);
    let current_term = trace.intern_literal(sort, ReplayLiteral::I64(9), current_value);
    let derived_row = [Value::new_const(10)];
    let derived_term = trace.intern_literal(sort, ReplayLiteral::I64(10), derived_row[0]);
    let derived_origin = trace
        .install_source_row(table, &derived_row, &[derived_term])
        .unwrap();

    let binding_sources = [
        ReplayBindingSource::Premise {
            representative: PremiseOccurrence {
                premise: 0,
                column: 0,
            },
        },
        ReplayBindingSource::Constant {
            term: constant_term,
        },
        ReplayBindingSource::Current {
            variable: Variable::new(0),
            sort,
            residual: 0,
        },
    ];
    trace.register_rule_term_recipe(
        11,
        TermRecipe {
            current_roots: [Some(Arc::new(TermTemplate::Static { term: current_term }))].into(),
        },
    );
    let [(_, rule_cause)] = trace
        .register_firings(11, Wave::new(1), 1, &binding_sources, &[source_fact], &[0])
        .try_into()
        .unwrap();
    let mut derived_batch = trace.new_batch();
    derived_batch.record_fact_with_origin(table, rule_cause, &derived_row, derived_origin);
    derived_batch.publish();
    trace.finalize_wave();

    trace
        .with_view(|view| {
            assert_eq!(
                view.firing_terms(FiringId::new(1))?.as_ref(),
                &[source_term, constant_term, current_term],
                "lazy expansion must preserve the complete binding layout"
            );
            Ok(())
        })
        .unwrap();
    assert_eq!(
        trace.replay_term(derived_term),
        Some(ReplayTerm::Literal {
            sort,
            literal: ReplayLiteral::I64(10),
        })
    );
}

#[test]
fn container_anchor_projects_only_referenced_bindings_and_memoizes_repeated_leaves() {
    let trace = Trace::default();
    let table = TableId::new_const(0);
    let source_sort = ReplaySortId::new(10);
    let current_sort = ReplaySortId::new(11);
    let container_sort = ReplaySortId::new(12);
    let pure_op = ReplayOpId::new(10);
    let container_op = ReplayOpId::new(11);
    trace
        .register_table_layout(table, &[Some(source_sort)])
        .unwrap();

    let used_value = Value::new_const(10);
    let unused_value = Value::new_const(11);
    let used_term = trace.intern_literal(source_sort, ReplayLiteral::I64(10), used_value);
    let unused_term = trace.intern_literal(source_sort, ReplayLiteral::I64(11), unused_value);
    let used_origin = trace
        .install_source_row(table, &[used_value], &[used_term])
        .unwrap();
    let unused_origin = trace
        .install_source_row(table, &[unused_value], &[unused_term])
        .unwrap();
    let cause = trace.source_draft(SourceRef::Synthetic(10));
    let mut facts = trace.new_batch();
    let used_fact = facts.record_fact_with_origin(table, cause, &[used_value], used_origin);
    let mut unused_fact =
        facts.record_fact_with_origin(table, cause, &[unused_value], unused_origin);
    for _ in 0..32 {
        unused_fact = facts.record_fact_from_prior(table, cause, &[unused_value], unused_fact);
    }
    facts.publish();

    let binding_sources = [
        ReplayBindingSource::Premise {
            representative: PremiseOccurrence {
                premise: 0,
                column: 0,
            },
        },
        ReplayBindingSource::Premise {
            representative: PremiseOccurrence {
                premise: 1,
                column: 0,
            },
        },
        // Production lowering expands this pure Current producer into the
        // nested template below. Keeping the binding here proves that the
        // runtime installer never scans unreferenced residual bindings.
        ReplayBindingSource::Current {
            variable: Variable::new(0),
            sort: current_sort,
            residual: 0,
        },
    ];
    let repeated_current = Arc::new(TermTemplate::Call {
        sort: current_sort,
        op: pure_op,
        children: [Arc::new(TermTemplate::Binding { binding: 0 })].into(),
    });
    let site = trace.register_term_origin(TermOriginSpec {
        sort: container_sort,
        term: Arc::new(TermTemplate::Call {
            sort: container_sort,
            op: container_op,
            children: [Arc::clone(&repeated_current), repeated_current].into(),
        }),
    });
    let replay = ReplayCallSpec::new(container_sort, container_op, [current_sort, current_sort])
        .with_primitive_return_anchor(TypeId::of::<Vec<Value>>());
    let current_value = Value::new_const(12);
    let container_value = Value::new_const(13);

    let installed = trace
        .with_container_anchor_installer(site, &replay, |install| {
            install(
                &binding_sources,
                &[used_fact, unused_fact],
                &[current_value, current_value],
                container_value,
            )
        })
        .unwrap()
        .unwrap();

    let ReplayTerm::Call { children, .. } = trace.replay_term(installed).unwrap() else {
        panic!("container anchor did not produce a structural call")
    };
    assert_eq!(children.len(), 2);
    assert_eq!(
        children[0], children[1],
        "the repeated Current producer diverged"
    );
    assert_eq!(
        trace.lookup_term(current_sort, current_value),
        Some(children[0]),
        "the exact nested Current producer was not installed for its runtime value"
    );
}

#[test]
fn replay_value_lookup_is_scoped_by_stable_sort() {
    let trace = Trace::default();
    let value = Value::new_const(7);
    let left_sort = ReplaySortId::new(40);
    let right_sort = ReplaySortId::new(41);
    let left = trace.intern_literal(left_sort, ReplayLiteral::String("left".into()), value);
    let right = trace.intern_literal(right_sort, ReplayLiteral::String("right".into()), value);

    assert_ne!(left, right);
    assert_eq!(trace.lookup_term(left_sort, value), Some(left));
    assert_eq!(trace.lookup_term(right_sort, value), Some(right));
}
