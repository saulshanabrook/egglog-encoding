use std::{
    any::TypeId,
    iter,
    ops::Range,
    panic::{AssertUnwindSafe, catch_unwind},
    sync::{
        Arc, Mutex,
        atomic::{AtomicUsize, Ordering},
    },
};

use egglog_reports::{PreMergeTiming, ReportLevel};

use crate::numeric_id::NumericId;

use crate::provenance::{RowOriginSpec, TermOriginSpec, TermTemplate};
use crate::{
    CriterionCaptureSpec, CriterionEndpointSource, FactId, FiringCaptureSpec, MergeOriginSelector,
    PlanStrategy, ReplayConstructorSpec, ReplayLiteral, ReplayOpId, ReplaySortId, ReplayTableKind,
    ReplayTerm, RowOriginSiteId, SourceRef, Trace, Wave,
    action::{ExecutionState, Instr, WriteVal},
    common::Value,
    free_join::{
        CounterId, Database, TableId,
        execute::{pending_witness_resolution_count, reset_pending_witness_resolution_count},
        plan::{JoinStage, MatScanMode, Plan},
    },
    make_external_func,
    offsets::RowId,
    query::RuleSetBuilder,
    table::{SortedWritesTable, causal_lookup_counters, reset_causal_lookup_counters},
    table_shortcuts::v,
    table_spec::{ColumnId, Constraint, MutationTransaction, Table},
    uf::DisplacedTable,
};

const TEST_REPLAY_SORT: ReplaySortId = ReplaySortId::new(0);

fn register_test_capture_table(trace: &Trace, table: TableId, columns: usize) {
    register_test_capture_table_kind(trace, table, columns, ReplayTableKind::ValueFunction);
}

fn register_test_capture_table_kind(
    trace: &Trace,
    table: TableId,
    columns: usize,
    kind: ReplayTableKind,
) {
    trace
        .register_table_layout(table, &vec![Some(TEST_REPLAY_SORT); columns])
        .unwrap();
    trace
        .register_table_merge_origins(
            table,
            &(0..columns)
                .map(|column| MergeOriginSelector::Incoming {
                    column: column.try_into().unwrap(),
                })
                .collect::<Vec<_>>(),
        )
        .unwrap();
    trace.register_table_kind(table, kind).unwrap();
}

fn install_test_row_terms(trace: &Trace, row: &[Value]) {
    for value in row {
        trace.intern_literal(
            TEST_REPLAY_SORT,
            ReplayLiteral::I64(value.index() as i64),
            *value,
        );
    }
}

fn install_test_row_origin(
    trace: &Trace,
    table: TableId,
    row: &[Value],
    terms: &[crate::ReplayTermId],
) -> RowOriginSiteId {
    trace.install_source_row(table, row, terms).unwrap()
}

fn certify_test_replay_call(trace: &Trace, rule: u32, sort: ReplaySortId, op: ReplayOpId) {
    trace.register_rule_term_recipe(
        rule,
        crate::provenance::TermRecipe {
            current_roots: [Some(Arc::new(TermTemplate::Call {
                sort,
                op,
                children: Arc::from([]),
            }))]
            .into(),
        },
    );
}

fn register_test_merge_origins(trace: &Trace, table: TableId, origins: &[MergeOriginSelector]) {
    trace.register_table_merge_origins(table, origins).unwrap();
}

fn fact_ids(view: &crate::TraceView<'_>) -> impl Iterator<Item = FactId> {
    (1..=view.totals().facts).map(FactId::new)
}

fn cause_firing(cause: crate::CauseRef) -> Option<crate::FiringId> {
    match cause {
        crate::CauseRef::Rule(id) => Some(id),
        crate::CauseRef::Cause(_) => None,
    }
}

fn equality_firing(reason: &crate::EqualityReason) -> crate::FiringId {
    let crate::EqualityReason::RuleUnion(firing) = reason else {
        panic!("expected a direct rule-union reason")
    };
    *firing
}

fn view_end_position(view: &crate::TraceView<'_>) -> crate::HistoryPosition {
    let totals = view.totals();
    crate::HistoryPosition::new(
        totals.facts
            + totals.applied_equalities
            + totals.rekeys
            + totals.removals
            + totals.check_roots,
    )
}

fn test_rekeys<'a>(
    view: &mut crate::TraceView<'a>,
) -> Result<Vec<crate::RawRekeyRecord<'a>>, crate::TraceViewError> {
    let mut rekeys = Vec::new();
    for position in 1..=view_end_position(view).get() {
        if let Ok(rekey) = view.rekey_at(crate::HistoryPosition::new(position)) {
            rekeys.push(rekey);
        }
    }
    assert_eq!(rekeys.len() as u64, view.totals().rekeys);
    Ok(rekeys)
}

fn fact_for_table<'a>(view: &crate::TraceView<'a>, table: TableId) -> crate::RawFactRecord<'a> {
    fact_ids(view)
        .find_map(|id| view.fact(id).ok().filter(|fact| fact.table == table))
        .expect("expected one durable fact for the table")
}

/// On MacOs the system allocator is vulenrable to contention, causing tests to execute quite
/// slowly without mimalloc.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// Run a test closure both single-threaded and with 4 threads.
fn run_serial_and_parallel(f: impl Fn() + Send + Sync) {
    for num_threads in [1, 32] {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(num_threads)
            .build()
            .unwrap();
        pool.install(&f);
    }
}

#[test]
fn ordinary_four_thread_large_insert_remains_parallel_safe() {
    const ROWS: usize = 20_001;
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(4)
        .build()
        .unwrap();
    pool.install(|| {
        let mut db = Database::default();
        let table = db.add_table(
            SortedWritesTable::new(1, 1, None, vec![], Box::new(|_, _, _, _| false)),
            iter::empty(),
            iter::empty(),
        );
        {
            let mut buffer = db.new_buffer(table);
            for value in 0..ROWS {
                buffer.stage_insert(&[Value::from_usize(value)]);
            }
        }
        assert!(db.merge_all());
        assert_eq!(db.get_table(table).len(), ROWS);
    });
}

#[test]
fn causal_trace_record_only_effective_constructor_and_union_commits() {
    let mut db = Database::default();
    let relation = || {
        SortedWritesTable::new(
            2,
            3,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "relation rows are immutable");
                false
            }),
        )
    };
    let input = db.add_table_named(relation(), "Input".into(), iter::empty(), iter::empty());
    let constructor = db.add_table_named(
        SortedWritesTable::new(
            1,
            3,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "constructor rows are immutable");
                false
            }),
        ),
        "Node".into(),
        iter::empty(),
        iter::empty(),
    );
    let derived = db.add_table_named(
        SortedWritesTable::new(
            2,
            3,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "derived rows are immutable");
                false
            }),
        ),
        "Derived".into(),
        iter::empty(),
        iter::empty(),
    );
    let consumed = db.add_table_named(
        SortedWritesTable::new(
            2,
            3,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "consumed rows are immutable");
                false
            }),
        ),
        "Consumed".into(),
        iter::empty(),
        iter::empty(),
    );
    let uf = db.add_table_named(
        DisplacedTable::default(),
        "UF".into(),
        iter::empty(),
        iter::empty(),
    );
    let fresh = db.add_counter();

    let trace = db.try_enable_trace().unwrap();
    let value_sort = ReplaySortId::new(20);
    let node_sort = ReplaySortId::new(21);
    let node_op = ReplayOpId::new(20);
    trace
        .register_table_layout(input, &[Some(value_sort), Some(node_sort), None])
        .unwrap();
    trace
        .register_table_layout(constructor, &[Some(value_sort), Some(node_sort), None])
        .unwrap();
    for table in [derived, consumed] {
        trace
            .register_table_layout(table, &[Some(value_sort), Some(node_sort), None])
            .unwrap();
    }
    let input_term = trace.intern_literal(value_sort, ReplayLiteral::I64(7), Value::new(7));
    let input_as_node_term = trace.intern_literal(node_sort, ReplayLiteral::I64(7), Value::new(7));
    db.stage_source_row(
        input,
        &[Value::new(7), Value::new(7), Value::new(0)],
        &[input_term, input_as_node_term, crate::ReplayTermId::MISSING],
        SourceRef::Synthetic(0),
    )
    .unwrap();
    assert!(db.merge_all());

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let value = query.new_var_named("value");
    let source_node = query.new_var_named("source_node");
    let input_ts = query.new_var_named("input_ts");
    let input_atom = query
        .add_atom(
            input,
            &[value.into(), source_node.into(), input_ts.into()],
            &[],
        )
        .unwrap();
    let mut action = query.build();
    let node = action
        .lookup_or_insert_with_replay(
            constructor,
            &[value.into()],
            &[WriteVal::IncCounter(fresh), Value::new(1).into()],
            ColumnId::new(1),
            ReplayConstructorSpec::new(node_sort, node_op, [value_sort]),
        )
        .unwrap();
    action
        .insert(derived, &[value.into(), node.into(), Value::new(1).into()])
        .unwrap();
    action
        .union_with_replay(
            uf,
            node.into(),
            source_node.into(),
            Value::new(1).into(),
            node_sort,
        )
        .unwrap();
    action
        .try_build_with_capture(
            "derive-node",
            FiringCaptureSpec::new(
                0,
                [input_atom],
                [
                    crate::RuleBindingSpec::variable(value, value_sort),
                    crate::RuleBindingSpec::variable(source_node, node_sort),
                ],
            ),
        )
        .unwrap();
    let rule_set = rules.build();

    db.set_trace_wave(Wave::new(1));
    let first = db.run_rule_set(&rule_set, ReportLevel::TimeOnly);
    assert!(first.changed);
    db.finalize_trace_wave();

    let (source_id, derived_id, node_term) = trace
        .with_view(|view| {
            let source = fact_for_table(view, input);
            let constructor_fact = fact_for_table(view, constructor);
            let derived_fact = fact_for_table(view, derived);
            assert_ne!(source.id, constructor_fact.id);
            assert_ne!(source.id, derived_fact.id);
            let match_id = cause_firing(constructor_fact.cause).unwrap();
            let match_record = view.firing(match_id)?;
            assert_eq!(match_record.wave, Wave::new(1));
            assert_eq!(match_record.premises, &[source.id]);
            assert_eq!(
                view.firing_terms(match_id)?.as_ref(),
                &[input_term, input_as_node_term]
            );
            assert_eq!(cause_firing(derived_fact.cause), Some(match_id));
            let constructor_terms = view.fact_terms(constructor_fact.id)?;
            let node_term = constructor_terms[1];
            assert_eq!(
                constructor_terms.as_ref(),
                &[input_term, node_term, crate::ReplayTermId::MISSING]
            );
            assert_eq!(
                view.fact_terms(derived_fact.id)?.as_ref(),
                constructor_terms.as_ref()
            );
            let equality = view.project_applied_equality(crate::AppliedEqualityId::new(1))?;
            assert_eq!(equality.wave, Wave::new(1));
            assert_eq!(
                (equality.left.sort, equality.left.term),
                (node_sort, node_term)
            );
            assert_eq!(
                (equality.right.raw, equality.right.sort, equality.right.term),
                (Value::new(7), node_sort, input_as_node_term)
            );
            assert_eq!(
                (equality.native_parent, equality.native_child),
                if equality.left.raw < equality.right.raw {
                    (equality.left.raw, equality.right.raw)
                } else {
                    (equality.right.raw, equality.left.raw)
                }
            );
            assert_eq!(equality.reason, crate::EqualityReason::RuleUnion(match_id));
            assert_eq!(view.totals().firings, 1);
            assert_eq!(view.fact(source.id)?.values, source.values);
            Ok((source.id, derived_fact.id, node_term))
        })
        .unwrap();
    assert_eq!(
        trace.replay_term(node_term).unwrap(),
        ReplayTerm::Call {
            sort: node_sort,
            op: node_op,
            children: [input_term].into(),
        }
    );
    let nodes_before_hit = trace.replay_term_counters().interned_nodes;
    let mut consumers = RuleSetBuilder::new(&mut db);
    let mut query = consumers.new_rule();
    let consumed_value = query.new_var_named("consumed_value");
    let consumed_node = query.new_var_named("consumed_node");
    let derived_ts = query.new_var_named("derived_ts");
    let derived_atom = query
        .add_atom(
            derived,
            &[
                consumed_value.into(),
                consumed_node.into(),
                derived_ts.into(),
            ],
            &[],
        )
        .unwrap();
    let mut action = query.build();
    let node_again = action
        .lookup_or_insert_with_replay(
            constructor,
            &[consumed_value.into()],
            &[WriteVal::IncCounter(fresh), Value::new(2).into()],
            ColumnId::new(1),
            ReplayConstructorSpec::new(node_sort, node_op, [value_sort]),
        )
        .unwrap();
    action
        .insert(
            consumed,
            &[
                consumed_value.into(),
                node_again.into(),
                Value::new(2).into(),
            ],
        )
        .unwrap();
    action
        .try_build_with_capture(
            "consume-derived-node",
            FiringCaptureSpec::new(
                1,
                [derived_atom],
                [
                    crate::RuleBindingSpec::variable(consumed_value, value_sort),
                    crate::RuleBindingSpec::variable(consumed_node, node_sort),
                ],
            ),
        )
        .unwrap();
    let consumers = consumers.build();
    db.set_trace_wave(Wave::new(2));
    let second = db.run_rule_set(&consumers, ReportLevel::TimeOnly);
    assert!(second.changed);
    db.finalize_trace_wave();
    trace
        .with_view(|view| {
            let consumed_fact = fact_for_table(view, consumed);
            assert_eq!(
                view.fact_terms(consumed_fact.id)?.as_ref(),
                &[input_term, node_term, crate::ReplayTermId::MISSING]
            );
            let consumed_match = view.firing(cause_firing(consumed_fact.cause).unwrap())?;
            assert_eq!(consumed_match.premises, &[derived_id]);
            assert_eq!(
                view.firing_terms(consumed_match.id)?.as_ref(),
                &[input_term, node_term]
            );
            assert!(view.fact(source_id).is_ok());
            Ok(())
        })
        .unwrap();
    assert_eq!(
        trace.replay_term_counters().interned_nodes,
        nodes_before_hit,
        "constructor hit must reuse the miss path's typed Call"
    );
}

fn empty_rule_cause(trace: &Trace, rule: u32, wave: Wave) -> crate::CauseRef {
    trace.register_firings(rule, wave, 0, &[], &[], &[0])[0]
        .1
        .into()
}

fn stage_test_union(
    db: &Database,
    table: TableId,
    cause: crate::CauseRef,
    sort: ReplaySortId,
    left: Value,
    right: Value,
    timestamp: Value,
) {
    db.with_execution_state(|state| {
        state.set_active_cause_ref(Some(cause));
        state.stage_union_with_replay(table, left, right, timestamp, sort);
    });
}

fn native_uf_root(db: &Database, table: TableId, value: Value) -> Value {
    db.get_table(table)
        .as_any()
        .downcast_ref::<DisplacedTable>()
        .unwrap()
        .underlying_uf()
        .find_naive(value)
}

#[test]
fn capture_database_clone_and_clear_fail_before_mutation() {
    let mut db = Database::default();
    let table = db.add_table(
        SortedWritesTable::new(1, 1, None, vec![], Box::new(|_, _, _, _| false)),
        iter::empty(),
        iter::empty(),
    );
    let trace = db.try_enable_trace().unwrap();
    register_test_capture_table(&trace, table, 1);
    let value = Value::new(1);
    install_test_row_terms(&trace, &[value]);
    db.stage_source_row(
        table,
        &[value],
        &[trace.lookup_term(TEST_REPLAY_SORT, value).unwrap()],
        SourceRef::Synthetic(1),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_trace_wave();
    assert!(catch_unwind(AssertUnwindSafe(|| db.clone())).is_err());
    assert!(catch_unwind(AssertUnwindSafe(|| db.clear_table(table))).is_err());
    assert!(db.get_table(table).get_row(&[value]).is_some());
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TestLandmark {
    as_of_edges: crate::EdgeHorizon,
    position: crate::HistoryPosition,
    pairs: Box<[crate::TypedCellEquality]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TestRebuildDependency {
    wave: Wave,
    prior_fact: FactId,
    equalities: TestLandmark,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TestContainerDependency {
    wave: Wave,
    equalities: TestLandmark,
}

#[derive(Default)]
struct TestCauseDependencies {
    sources: Vec<SourceRef>,
    rules: Vec<crate::FiringId>,
    facts: Vec<FactId>,
    rebuilds: Vec<TestRebuildDependency>,
    container_canonicalizations: Vec<TestContainerDependency>,
    container_refreshes: Vec<(FactId, TestContainerDependency)>,
}

fn test_cause_dependencies(
    view: &crate::TraceView<'_>,
    root: impl Into<crate::CauseRef>,
) -> Result<TestCauseDependencies, crate::TraceViewError> {
    let mut result = TestCauseDependencies::default();
    let mut stack = vec![root.into()];
    while let Some(dependency) = stack.pop() {
        match dependency {
            crate::CauseRef::Rule(rule) => result.rules.push(rule),
            crate::CauseRef::Cause(cause) => match view.cause(cause)? {
                crate::RawCause::Source(source) => result.sources.push(source.clone()),
                crate::RawCause::Rebuild {
                    wave,
                    prior_fact,
                    as_of_edges,
                    position,
                    equalities,
                } => {
                    result.facts.push(prior_fact);
                    result.rebuilds.push(TestRebuildDependency {
                        wave,
                        prior_fact,
                        equalities: TestLandmark {
                            as_of_edges,
                            position,
                            pairs: equalities.into(),
                        },
                    });
                }
                crate::RawCause::ContainerCanonicalize {
                    wave,
                    as_of_edges,
                    position,
                    equalities,
                } => result
                    .container_canonicalizations
                    .push(TestContainerDependency {
                        wave,
                        equalities: TestLandmark {
                            as_of_edges,
                            position,
                            pairs: equalities.into(),
                        },
                    }),
                crate::RawCause::ContainerRefresh {
                    wave,
                    prior_fact,
                    as_of_edges,
                    position,
                    equalities,
                } => {
                    result.facts.push(prior_fact);
                    result.container_refreshes.push((
                        prior_fact,
                        TestContainerDependency {
                            wave,
                            equalities: TestLandmark {
                                as_of_edges,
                                position,
                                pairs: equalities.into(),
                            },
                        },
                    ));
                }
                crate::RawCause::Merge {
                    incoming,
                    prior_fact,
                } => {
                    stack.push(incoming);
                    result.facts.push(prior_fact);
                }
            },
        }
    }
    Ok(result)
}

fn test_congruence_dependencies(
    view: &crate::TraceView<'_>,
    reason: &crate::EqualityReason,
) -> Result<(TestCauseDependencies, TestLandmark), crate::TraceViewError> {
    let crate::EqualityReason::Congruence {
        cause,
        wave,
        as_of_edges,
        position,
    } = reason
    else {
        panic!("expected a congruence reason, got {reason:?}")
    };
    let dependencies = test_cause_dependencies(view, *cause)?;
    let mut pairs = Vec::new();
    for rebuild in &dependencies.rebuilds {
        assert_eq!(rebuild.wave, *wave);
        assert_eq!(rebuild.equalities.as_of_edges, *as_of_edges);
        pairs.extend_from_slice(&rebuild.equalities.pairs);
    }
    Ok((
        dependencies,
        TestLandmark {
            as_of_edges: *as_of_edges,
            position: *position,
            pairs: pairs.into_boxed_slice(),
        },
    ))
}

#[test]
fn causal_capture_rebuild_rekeys_with_exact_landmark_and_noop_preserves_fact() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let rebuilt = db.add_table(
        SortedWritesTable::new(
            1,
            2,
            Some(ColumnId::new(1)),
            vec![ColumnId::new(0)],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "a pure rekey cannot collide");
                false
            }),
        ),
        iter::once(uf),
        iter::empty(),
    );
    let trace = db.try_enable_trace().unwrap();
    let sort = ReplaySortId::new(79);
    trace
        .register_table_layout(rebuilt, &[Some(sort), None])
        .unwrap();
    let old = Value::new(20);
    let new = Value::new(10);
    let old_term = trace.intern_literal(sort, ReplayLiteral::I64(20), old);
    let new_term = trace.intern_literal(sort, ReplayLiteral::I64(10), new);
    db.stage_source_row(
        rebuilt,
        &[old, Value::new(0)],
        &[old_term, crate::ReplayTermId::MISSING],
        SourceRef::Synthetic(79),
    )
    .unwrap();
    assert!(db.merge_all());
    let prior_fact = committed_fact_id(&db, rebuilt, old);

    db.set_trace_wave(Wave::new(1));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&trace, 79, Wave::new(1)),
        sort,
        old,
        new,
        Value::new(1),
    );
    assert!(db.merge_all());

    db.set_trace_wave(Wave::new(2));
    assert!(db.apply_rebuild(uf, &[rebuilt], Value::new(2)));
    db.finalize_trace_wave();
    let rebuilt_fact = committed_fact_id(&db, rebuilt, new);
    assert_eq!(
        rebuilt_fact, prior_fact,
        "a pure rekey must preserve the immutable logical FactId"
    );
    trace
        .with_view(|view| {
            assert_eq!(
                view.fact_terms(rebuilt_fact)?.as_ref(),
                &[old_term, crate::ReplayTermId::MISSING],
                "a pure rekey cannot rewrite the fact's historical creation syntax"
            );
            assert_eq!(view.totals().facts, 1, "a pure rekey creates no fact");
            let crate::CauseRef::Cause(source) = view.fact(rebuilt_fact)?.cause else {
                panic!("source fact lost its source cause")
            };
            assert!(matches!(
                view.cause(source)?,
                crate::RawCause::Source(SourceRef::Synthetic(79))
            ));
            assert_eq!(view.totals().rekeys, 1);
            let applied = view.applied_equality(crate::AppliedEqualityId::new(1))?;
            let rekey = view.rekey_at(crate::HistoryPosition::new(applied.position.get() + 1))?;
            assert_eq!(rekey.fact, prior_fact);
            assert_eq!(rekey.table, rebuilt);
            assert_eq!(rekey.wave, Wave::new(2));
            assert_eq!(rekey.as_of_edges, crate::EdgeHorizon::new(1));
            assert_eq!(rekey.equality_position, applied.position);
            assert_eq!(
                rekey.equalities,
                &[crate::TypedCellEquality {
                    column: ColumnId::new(0),
                    left: crate::EqualityEndpoint {
                        sort,
                        term: crate::ReplayTermId::MISSING,
                        raw: old,
                    },
                    right: crate::EqualityEndpoint {
                        sort,
                        term: crate::ReplayTermId::MISSING,
                        raw: new,
                    },
                }]
            );
            assert_eq!(rekey.outcome, crate::provenance::RekeyOutcome::Moved);
            let projected = view.project_applied_equality(crate::AppliedEqualityId::new(1))?;
            assert_eq!(
                (projected.left.term, projected.right.term),
                (old_term, new_term)
            );
            assert_eq!(view.totals().rekeys, 1);
            Ok(())
        })
        .unwrap();

    db.set_trace_wave(Wave::new(3));
    assert!(
        !db.apply_rebuild(uf, &[rebuilt], Value::new(3)),
        "an already-canonical row is a rebuild no-op"
    );
    db.finalize_trace_wave();
    assert_eq!(committed_fact_id(&db, rebuilt, new), rebuilt_fact);
    trace
        .with_view(|view| {
            assert_eq!(view.totals().facts, 1);
            assert_eq!(view.totals().rekeys, 1);
            Ok(())
        })
        .unwrap();
    let later_left = Value::new(40);
    let later_right = Value::new(30);
    trace.intern_literal(sort, ReplayLiteral::I64(40), later_left);
    trace.intern_literal(sort, ReplayLiteral::I64(30), later_right);
    db.set_trace_wave(Wave::new(4));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&trace, 80, Wave::new(4)),
        sort,
        later_left,
        later_right,
        Value::new(4),
    );
    assert!(db.merge_all());
    db.finalize_trace_wave();
    trace
        .with_view(|view| {
            let first = view.applied_equality(crate::AppliedEqualityId::new(1))?;
            let rekey = view.rekey_at(crate::HistoryPosition::new(first.position.get() + 1))?;
            assert_eq!(
                rekey.as_of_edges,
                crate::EdgeHorizon::new(1),
                "a later equality edge cannot justify an earlier table rekey"
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn trusted_exact_occurrences_extend_from_both_native_roots() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let trace = db.try_enable_trace().unwrap();
    let child_sort = ReplaySortId::new(7902);
    let sort = ReplaySortId::new(7903);
    let child = trace.intern_literal(child_sort, ReplayLiteral::I64(7), Value::new(7));
    let a = Value::new(50);
    let b = Value::new(40);
    let x = Value::new(30);
    let y = Value::new(20);
    let z = Value::new(10);
    let shared = trace
        .intern_call(sort, ReplayOpId::new(7902), &[child], a)
        .unwrap();
    assert_eq!(
        trace
            .intern_call(sort, ReplayOpId::new(7902), &[child], b)
            .unwrap(),
        shared,
        "the production Call interner certifies the same term at both raw ids"
    );
    for (op, raw) in [(7903, x), (7904, y), (7905, z)] {
        trace
            .intern_call(sort, ReplayOpId::new(op), &[child], raw)
            .unwrap();
    }

    for (wave, left, right) in [(1, a, x), (2, b, y), (3, a, z)] {
        let wave = Wave::new(wave);
        db.set_trace_wave(wave);
        stage_test_union(
            &db,
            uf,
            empty_rule_cause(&trace, 7903 + wave.get() as u32, wave),
            sort,
            left,
            right,
            Value::new(wave.get() as u32),
        );
        assert!(db.merge_all());
    }
    db.finalize_trace_wave();

    trace
        .with_view(|view| {
            let first_root = view.explain_raw_equality_support_at(
                crate::RawEqualityEndpoint { sort, raw: x },
                crate::RawEqualityEndpoint { sort, raw: z },
                crate::EdgeHorizon::new(3),
                view_end_position(view),
            )?;
            assert_eq!(
                first_root.applied.as_ref(),
                &[crate::AppliedEqualityId::new(3)]
            );
            let second_root = view.explain_raw_equality_support_at(
                crate::RawEqualityEndpoint { sort, raw: b },
                crate::RawEqualityEndpoint { sort, raw: y },
                crate::EdgeHorizon::new(3),
                view_end_position(view),
            )?;
            assert_eq!(
                second_root.applied.as_ref(),
                &[crate::AppliedEqualityId::new(2)]
            );
            Ok(())
        })
        .expect("both trusted exact occurrences must remain explainable");
}

#[test]
fn causal_capture_rebuild_collision_records_exact_congruence() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let sort = ReplaySortId::new(82);
    let rebuilt = db.add_table(
        SortedWritesTable::new(
            1,
            3,
            Some(ColumnId::new(2)),
            vec![ColumnId::new(0)],
            Box::new(move |state, prior, incoming, _| {
                state.stage_union_with_replay(uf, prior[1], incoming[1], Value::new(2), sort);
                false
            }),
        ),
        iter::once(uf),
        iter::once(uf),
    );
    let trace = db.try_enable_trace().unwrap();
    trace
        .register_table_layout(rebuilt, &[Some(sort), Some(sort), None])
        .unwrap();
    register_test_merge_origins(
        &trace,
        rebuilt,
        &[
            MergeOriginSelector::Prior { column: 0 },
            MergeOriginSelector::Prior { column: 1 },
            MergeOriginSelector::Unsupported,
        ],
    );

    let old_key = Value::new(30);
    let target_key = Value::new(20);
    let old_output = Value::new(300);
    let target_output = Value::new(200);
    let old_key_term = trace.intern_literal(sort, ReplayLiteral::I64(30), old_key);
    let target_key_term = trace.intern_literal(sort, ReplayLiteral::I64(20), target_key);
    let old_output_term = trace.intern_literal(sort, ReplayLiteral::I64(300), old_output);
    let target_output_term = trace.intern_literal(sort, ReplayLiteral::I64(200), target_output);
    db.stage_source_row(
        rebuilt,
        &[old_key, old_output, Value::new(0)],
        &[old_key_term, old_output_term, crate::ReplayTermId::MISSING],
        SourceRef::Synthetic(82),
    )
    .unwrap();
    db.stage_source_row(
        rebuilt,
        &[target_key, target_output, Value::new(0)],
        &[
            target_key_term,
            target_output_term,
            crate::ReplayTermId::MISSING,
        ],
        SourceRef::Synthetic(83),
    )
    .unwrap();
    assert!(db.merge_all());
    let old_fact = committed_fact_id(&db, rebuilt, old_key);
    let target_fact = committed_fact_id(&db, rebuilt, target_key);

    db.set_trace_wave(Wave::new(1));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&trace, 82, Wave::new(1)),
        sort,
        old_key,
        target_key,
        Value::new(1),
    );
    assert!(db.merge_all());

    db.set_trace_wave(Wave::new(2));
    assert!(db.apply_rebuild(uf, &[rebuilt], Value::new(2)));
    db.finalize_trace_wave();

    assert_eq!(
        committed_fact_id(&db, rebuilt, target_key),
        target_fact,
        "a congruence collision with no row merge keeps the target fact version"
    );
    assert!(
        trace
            .with_view(|view| view.fact(old_fact).map(drop))
            .is_ok()
    );
    assert_eq!(native_uf_root(&db, uf, old_output), target_output);
    trace
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, 2);
            let equality = view.project_applied_equality(crate::AppliedEqualityId::new(2))?;
            let (dependencies, equalities) = test_congruence_dependencies(view, &equality.reason)?;
            assert_eq!(dependencies.facts, [target_fact, old_fact]);
            assert!(dependencies.rules.is_empty());
            assert_eq!(equalities.as_of_edges, crate::EdgeHorizon::new(1));
            assert_eq!(
                equalities.pairs.as_ref(),
                &[crate::TypedCellEquality {
                    column: ColumnId::new(0),
                    left: crate::EqualityEndpoint {
                        sort,
                        term: crate::ReplayTermId::MISSING,
                        raw: old_key,
                    },
                    right: crate::EqualityEndpoint {
                        sort,
                        term: crate::ReplayTermId::MISSING,
                        raw: target_key,
                    },
                }]
            );
            assert_eq!(equality.wave, Wave::new(2));
            assert_eq!(equality.left.term, target_output_term);
            assert_eq!(equality.right.term, old_output_term);
            assert_eq!(
                view.totals().firings,
                1,
                "congruence must not invent a synthetic rule match"
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn causal_capture_rebuild_abort_is_atomic_across_target_tables() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let relation = || {
        SortedWritesTable::new(
            1,
            2,
            Some(ColumnId::new(1)),
            vec![ColumnId::new(0)],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right);
                false
            }),
        )
    };
    let first = db.add_table(relation(), iter::once(uf), iter::empty());
    let second = db.add_table(relation(), iter::once(uf), iter::empty());
    let trace = db.try_enable_trace().unwrap();
    let table_sort = ReplaySortId::new(91);
    let uf_sort = table_sort;
    for table in [first, second] {
        trace
            .register_table_layout(table, &[Some(table_sort), None])
            .unwrap();
    }
    register_test_merge_origins(
        &trace,
        first,
        &[
            MergeOriginSelector::Prior { column: 0 },
            MergeOriginSelector::Unsupported,
        ],
    );
    register_test_merge_origins(
        &trace,
        second,
        &[
            MergeOriginSelector::Unsupported,
            MergeOriginSelector::Unsupported,
        ],
    );

    let first_old = Value::new(120);
    let first_new = Value::new(110);
    let second_old = Value::new(90);
    let second_new = Value::new(80);
    let recovery = Value::new(200);
    for raw in [120, 110, 90, 80, 200] {
        trace.intern_literal(table_sort, ReplayLiteral::I64(raw), Value::new(raw as u32));
    }
    for raw in [120, 110, 90, 80] {
        trace.intern_literal(uf_sort, ReplayLiteral::I64(raw), Value::new(raw as u32));
    }
    for (table, value, source) in [(first, first_old, 910), (second, second_old, 911)] {
        db.stage_source_row(
            table,
            &[value, Value::new(0)],
            &[
                trace.lookup_term(table_sort, value).unwrap(),
                crate::ReplayTermId::MISSING,
            ],
            SourceRef::Synthetic(source),
        )
        .unwrap();
    }
    db.stage_source_row(
        second,
        &[second_new, Value::new(0)],
        &[
            trace.lookup_term(table_sort, second_new).unwrap(),
            crate::ReplayTermId::MISSING,
        ],
        SourceRef::Synthetic(913),
    )
    .unwrap();
    assert!(db.merge_all());
    let first_fact = committed_fact_id(&db, first, first_old);
    let second_fact = committed_fact_id(&db, second, second_old);
    let second_canonical_fact = committed_fact_id(&db, second, second_new);

    db.set_trace_wave(Wave::new(1));
    let union_cause = empty_rule_cause(&trace, 91, Wave::new(1));
    stage_test_union(
        &db,
        uf,
        union_cause,
        uf_sort,
        first_old,
        first_new,
        Value::new(1),
    );
    stage_test_union(
        &db,
        uf,
        union_cause,
        uf_sort,
        second_old,
        second_new,
        Value::new(1),
    );
    assert!(db.merge_all());
    db.set_trace_wave(Wave::new(2));

    let failed = catch_unwind(AssertUnwindSafe(|| {
        db.apply_rebuild(uf, &[first, second], Value::new(2));
    }));
    assert!(failed.is_err());

    db.stage_source_row(
        first,
        &[recovery, Value::new(2)],
        &[
            trace.lookup_term(table_sort, recovery).unwrap(),
            crate::ReplayTermId::MISSING,
        ],
        SourceRef::Synthetic(912),
    )
    .unwrap();
    assert!(db.merge_all());
    assert_eq!(committed_fact_id(&db, first, first_old), first_fact);
    assert_eq!(committed_fact_id(&db, second, second_old), second_fact);
    assert!(db.get_table(first).get_row(&[first_new]).is_none());
    assert_eq!(
        committed_fact_id(&db, second, second_new),
        second_canonical_fact
    );
    assert!(db.get_table(first).get_row(&[recovery]).is_some());

    db.finalize_trace_wave();
    trace
        .with_view(|view| {
            assert_eq!(view.totals().rekeys, 0);
            Ok(())
        })
        .unwrap();
}

#[test]
fn typed_union_forest_is_immutable_across_native_path_compression_and_redundancy() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let trace = db.try_enable_trace().unwrap();
    let sort = ReplaySortId::new(80);
    let a = Value::new(30);
    let b = Value::new(20);
    let c = Value::new(10);
    let a_term = trace.intern_literal(sort, ReplayLiteral::I64(30), a);
    let b_term = trace.intern_literal(sort, ReplayLiteral::I64(20), b);
    let c_term = trace.intern_literal(sort, ReplayLiteral::I64(10), c);

    db.set_trace_wave(Wave::new(1));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&trace, 80, Wave::new(1)),
        sort,
        a,
        b,
        Value::new(1),
    );
    assert!(db.merge_all());

    db.set_trace_wave(Wave::new(2));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&trace, 81, Wave::new(2)),
        sort,
        b,
        c,
        Value::new(2),
    );
    assert!(db.merge_all());

    db.set_trace_wave(Wave::new(3));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&trace, 82, Wave::new(3)),
        sort,
        a,
        c,
        Value::new(3),
    );
    assert!(
        !db.merge_all(),
        "the third proposal is redundant in the native UF"
    );
    db.finalize_trace_wave();

    trace.with_view(|view| {
    assert_eq!(view.totals().applied_equalities, 2);
    assert!(matches!(view.applied_equality(crate::AppliedEqualityId::new(1))?.reason, crate::EqualityReason::RuleUnion(id) if view.firing(id)?.rule == 80));
    assert!(matches!(view.applied_equality(crate::AppliedEqualityId::new(2))?.reason, crate::EqualityReason::RuleUnion(id) if view.firing(id)?.rule == 81));
    let endpoint = |term, raw| crate::EqualityEndpoint { sort, term, raw };
    assert_eq!(
        view
            .explain_equality_support_at(
                endpoint(a_term, a),
                endpoint(c_term, c),
                crate::EdgeHorizon::new(2),
                view_end_position(view),
            )?.applied.as_ref(),
        &[crate::AppliedEqualityId::new(1), crate::AppliedEqualityId::new(2)]
    );
    assert_eq!(
        view
            .explain_equality_support_at(
                endpoint(b_term, b),
                endpoint(c_term, c),
                crate::EdgeHorizon::new(2),
                view_end_position(view),
            )?.applied.as_ref(),
        &[crate::AppliedEqualityId::new(2)]
    );
    assert!(
        view
            .explain_equality_support_at(
                endpoint(a_term, a),
                endpoint(c_term, c),
                crate::EdgeHorizon::new(1),
                view.applied_equality(crate::AppliedEqualityId::new(1))?.position,
            )
            .is_err(),
        "the lazy explanation must not cross its historical cutoff"
    );
    let first = view.project_applied_equality(crate::AppliedEqualityId::new(1))?;
    let second = view.project_applied_equality(crate::AppliedEqualityId::new(2))?;
    assert_eq!((first.left.term, first.right.term), (a_term, b_term));
    assert_eq!((second.left.term, second.right.term), (b_term, c_term));
    assert_eq!(
        (first.wave, first.native_parent, first.native_child),
        (Wave::new(1), b, a)
    );
    assert_eq!(
        (second.wave, second.native_parent, second.native_child),
        (Wave::new(2), c, b)
    );
    Ok(())
    }).unwrap();
    assert_eq!(native_uf_root(&db, uf, a), c);
    assert_eq!(native_uf_root(&db, uf, b), c);
    assert_eq!(native_uf_root(&db, uf, c), c);
}

#[test]
fn invalid_typed_union_staging_fails_before_native_mutation() {
    for case in [
        "raw",
        "raw-with-cause",
        "missing",
        "wrong-sort",
        "token-row-mismatch",
    ] {
        let mut db = Database::default();
        let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
        let trace = db.try_enable_trace().unwrap();
        let sort = ReplaySortId::new(90);
        let left = Value::new(4);
        let right = Value::new(5);
        if case == "wrong-sort" {
            let other = ReplaySortId::new(91);
            trace.intern_literal(other, ReplayLiteral::I64(4), left);
            trace.intern_literal(other, ReplayLiteral::I64(5), right);
        } else if case == "token-row-mismatch" {
            trace.intern_literal(sort, ReplayLiteral::I64(4), left);
            trace.intern_literal(sort, ReplayLiteral::I64(5), right);
        }
        db.set_trace_wave(Wave::new(1));
        let cause = empty_rule_cause(&trace, 90, Wave::new(1));
        let failed = catch_unwind(AssertUnwindSafe(|| {
            if case == "raw" {
                let mut buffer = db.new_buffer(uf);
                buffer.stage_insert(&[left, right, Value::new(1)]);
            } else if case == "raw-with-cause" {
                let mut buffer = db.new_buffer(uf);
                buffer.stage_insert_deferred(
                    &[left, right, Value::new(1)],
                    crate::DeferredEqualityCause::ready(cause),
                );
            } else if case == "token-row-mismatch" {
                let proposal = trace
                    .typed_equality_proposal(Wave::new(1), sort, left, right)
                    .unwrap();
                let mut buffer = db.new_buffer(uf);
                buffer.stage_typed_union(&[right, left, Value::new(1)], cause, proposal);
            } else {
                stage_test_union(&db, uf, cause, sort, left, right, Value::new(1));
            }
        }));
        assert!(failed.is_err(), "{case} staging must fail closed");
        assert!(!db.merge_all(), "{case} staging mutated the native UF");
        db.finalize_trace_wave();
        assert_eq!(native_uf_root(&db, uf, left), left);
        assert_eq!(native_uf_root(&db, uf, right), right);
        trace
            .with_view(|view| {
                assert_eq!(view.totals().applied_equalities, 0);
                Ok(())
            })
            .unwrap();
    }
}

#[test]
fn merge_function_union_cites_one_match_and_immutable_prior_fact() {
    let sort = ReplaySortId::new(100);
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let target = db.add_table_named(
        SortedWritesTable::new(
            1,
            2,
            None,
            vec![],
            Box::new(move |state, prior, incoming, _out| {
                state.stage_union_with_replay(uf, prior[1], incoming[1], Value::new(1), sort);
                false
            }),
        ),
        "MergeUnionTarget".into(),
        iter::empty(),
        iter::once(uf),
    );
    let proposal = db.add_table_named(
        SortedWritesTable::new(
            2,
            2,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right);
                false
            }),
        ),
        "MergeUnionProposal".into(),
        iter::empty(),
        iter::empty(),
    );
    let trace = db.try_enable_trace().unwrap();
    trace
        .register_table_layout(target, &[Some(sort), Some(sort)])
        .unwrap();
    trace
        .register_table_layout(proposal, &[Some(sort), Some(sort)])
        .unwrap();
    register_test_merge_origins(
        &trace,
        target,
        &[
            MergeOriginSelector::Prior { column: 0 },
            MergeOriginSelector::Prior { column: 1 },
        ],
    );
    let key = Value::new(1);
    let prior = Value::new(30);
    let incoming = Value::new(20);
    let key_term = trace.intern_literal(sort, ReplayLiteral::I64(1), key);
    let prior_term = trace.intern_literal(sort, ReplayLiteral::I64(30), prior);
    let incoming_term = trace.intern_literal(sort, ReplayLiteral::I64(20), incoming);
    db.stage_source_row(
        target,
        &[key, prior],
        &[key_term, prior_term],
        SourceRef::Synthetic(100),
    )
    .unwrap();
    db.stage_source_row(
        proposal,
        &[key, incoming],
        &[key_term, incoming_term],
        SourceRef::Synthetic(101),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_trace_wave();
    let prior_fact = committed_fact_id(&db, target, key);
    let proposal_fact = committed_fact_id_for_key(&db, proposal, &[key, incoming]);

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let matched_key = query.new_var_named("key");
    let matched_value = query.new_var_named("incoming");
    let atom = query
        .add_atom(proposal, &[matched_key.into(), matched_value.into()], &[])
        .unwrap();
    let mut action = query.build();
    action
        .insert(target, &[matched_key.into(), matched_value.into()])
        .unwrap();
    action
        .try_build_with_capture(
            "merge-union",
            FiringCaptureSpec::new(
                100,
                [atom],
                [
                    crate::RuleBindingSpec::variable(matched_key, sort),
                    crate::RuleBindingSpec::variable(matched_value, sort),
                ],
            ),
        )
        .unwrap();
    let rules = rules.build();

    db.set_trace_wave(Wave::new(1));
    assert!(db.run_rule_set(&rules, ReportLevel::TimeOnly).changed);
    db.finalize_trace_wave();

    trace
        .with_view(|view| {
            let equality = view.project_applied_equality(crate::AppliedEqualityId::new(1))?;
            let (firing, recorded_prior) = match &equality.reason {
                crate::EqualityReason::MergeFn { cause } => {
                    let dependencies = test_cause_dependencies(view, *cause)?;
                    assert_eq!(dependencies.rules.len(), 1);
                    assert_eq!(dependencies.facts.len(), 1);
                    (dependencies.rules[0], dependencies.facts[0])
                }
                ref other => panic!("expected exact MergeFn reason, got {other:?}"),
            };
            assert_eq!(recorded_prior, prior_fact);
            let matched = view.firing(firing)?;
            assert_eq!(matched.rule, 100);
            assert_eq!(matched.premises, &[proposal_fact]);
            assert_eq!(equality.left.term, prior_term);
            assert_eq!(equality.right.term, incoming_term);
            Ok(())
        })
        .unwrap();
    assert_eq!(
        committed_fact_id(&db, target, key),
        prior_fact,
        "a merge that returns false keeps its original immutable fact"
    );
}

#[test]
fn invalid_merge_function_union_fails_before_replacing_its_parent_row() {
    let sort = ReplaySortId::new(108);
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let target = db.add_table_named(
        SortedWritesTable::new(
            1,
            2,
            None,
            vec![],
            Box::new(move |state, prior, incoming, out| {
                state.stage_union_with_replay(uf, prior[1], incoming[1], Value::new(1), sort);
                out.extend_from_slice(incoming);
                true
            }),
        ),
        "InvalidMergeUnionParent".into(),
        iter::empty(),
        iter::once(uf),
    );
    let trace = db.try_enable_trace().unwrap();
    trace
        .register_table_layout(target, &[Some(sort), Some(sort)])
        .unwrap();
    let key = Value::new(1);
    let prior = Value::new(30);
    let incoming = Value::new(20);
    let key_term = trace.intern_literal(sort, ReplayLiteral::I64(1), key);
    let prior_term = trace.intern_literal(sort, ReplayLiteral::I64(30), prior);
    let incoming_term = trace.intern_literal(sort, ReplayLiteral::I64(20), incoming);

    db.stage_source_row(
        target,
        &[key, prior],
        &[key_term, prior_term],
        SourceRef::Synthetic(108),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_trace_wave();
    let prior_fact = committed_fact_id(&db, target, key);

    db.stage_source_row(
        target,
        &[key, incoming],
        &[key_term, incoming_term],
        SourceRef::Synthetic(109),
    )
    .unwrap();
    let failed = catch_unwind(AssertUnwindSafe(|| db.merge_table(target)));
    assert!(failed.is_err());

    let row = db
        .get_table(target)
        .get_row(&[key])
        .expect("the parent table must be restored after rejection");
    assert_eq!(row.vals[1], prior);
    assert_eq!(committed_fact_id(&db, target, key), prior_fact);
    assert_eq!(native_uf_root(&db, uf, prior), prior);
    assert_eq!(native_uf_root(&db, uf, incoming), incoming);
    assert!(matches!(
        trace.with_view(|_| Ok(())),
        Err(crate::TraceViewError::NotFinalized(
            "a rule execution panicked"
        ))
    ));
    assert!(
        catch_unwind(AssertUnwindSafe(|| db.finalize_trace_wave())).is_err(),
        "a caught capture-enabled merge panic must prevent finalization"
    );
}

#[test]
fn causal_trace_reject_unsupported_merge_before_callback_effects() {
    let mut db = Database::default();
    let callbacks = Arc::new(AtomicUsize::new(0));
    let callback_count = Arc::clone(&callbacks);
    let table = db.add_table(
        SortedWritesTable::new(
            1,
            2,
            None,
            vec![],
            Box::new(move |_, left, right, out| {
                callback_count.fetch_add(1, Ordering::SeqCst);
                if left == right {
                    false
                } else {
                    out.extend_from_slice(&[right[0], Value::new(9)]);
                    true
                }
            }),
        ),
        iter::empty(),
        iter::empty(),
    );
    let trace = db.try_enable_trace().unwrap();
    trace
        .register_table_layout(table, &[Some(TEST_REPLAY_SORT), Some(TEST_REPLAY_SORT)])
        .unwrap();
    trace
        .register_table_merge_origins(
            table,
            &[
                MergeOriginSelector::Incoming { column: 0 },
                MergeOriginSelector::Unsupported,
            ],
        )
        .unwrap();
    let (zero, one, two) = (Value::new(0), Value::new(1), Value::new(2));
    install_test_row_terms(&trace, &[zero, one, two, Value::new(9)]);
    let term = |value| trace.lookup_term(TEST_REPLAY_SORT, value).unwrap();
    db.stage_source_row(
        table,
        &[two, zero],
        &[term(two), term(zero)],
        SourceRef::Synthetic(90),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_trace_wave();

    let wave = Wave::new(1);
    db.set_trace_wave(wave);
    let cause = empty_rule_cause(&trace, 62, wave);
    let origin = |key, value| {
        trace.register_row_origin(RowOriginSpec {
            table,
            cells: [key, value]
                .map(|term| Some(Arc::new(TermTemplate::Static { term })))
                .into(),
        })
    };
    {
        let mut update = db.new_buffer(table);
        for (row, row_origin) in [
            ([one, one], origin(term(one), term(one))),
            ([two, two], origin(term(two), term(two))),
        ] {
            update.stage_insert_deferred_with_origin(
                &row,
                crate::DeferredEqualityCause::ready(cause),
                row_origin,
            );
        }
    }

    let failed = catch_unwind(AssertUnwindSafe(|| db.merge_all()));
    assert!(failed.is_err(), "unsupported merge origin must fail closed");
    assert_eq!(callbacks.load(Ordering::SeqCst), 0);
    assert!(db.get_table(table).get_row(&[one]).is_none());
    assert_eq!(
        db.get_table(table).get_row(&[two]).unwrap().vals.as_slice(),
        &[two, zero]
    );
    assert!(matches!(
        trace.with_view(|_| Ok(())),
        Err(crate::TraceViewError::NotFinalized(
            "a rule execution panicked"
        ))
    ));
}

#[test]
fn causal_trace_record_same_term_native_alias_without_equality_edge() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let trace = db.try_enable_trace().unwrap();
    let child_sort = ReplaySortId::new(109);
    let container_sort = ReplaySortId::new(110);
    let op = ReplayOpId::new(109);
    let child = Value::new(7);
    let left = Value::new(30);
    let right = Value::new(20);
    let child_term = trace.intern_literal(child_sort, ReplayLiteral::I64(7), child);
    certify_test_replay_call(&trace, 10_900, container_sort, op);
    certify_test_replay_call(&trace, 11_000, container_sort, ReplayOpId::new(110));
    let call = trace
        .intern_call(container_sort, op, &[child_term], left)
        .unwrap();
    for value in [left, right] {
        assert_eq!(
            trace
                .install_test_container_anchor(
                    container_sort,
                    TypeId::of::<Vec<Value>>(),
                    &[child_sort],
                    value,
                    call,
                )
                .unwrap(),
            call
        );
    }

    let wave = Wave::new(1);
    db.set_trace_wave(wave);
    let cutoff = trace.equality_edge_count().unwrap();
    let journal = crate::provenance::ContainerAnchorJournal::default();
    let (cause, proposal) = trace
        .container_canonicalization_cause(
            &journal,
            TypeId::of::<Vec<Value>>(),
            wave,
            left,
            right,
            cutoff,
        )
        .unwrap();
    assert_eq!(proposal.left().sort, container_sort);
    {
        let mut buffer = db.new_buffer(uf);
        buffer.stage_typed_union(&[left, right, Value::new(1)], cause.id().into(), proposal);
    }
    assert!(db.merge_all());
    db.finalize_trace_wave();

    let alias_child = trace.with_view(|view| {
        assert_eq!(view.totals().applied_equalities, 1);
        let alias = view.project_applied_equality(crate::AppliedEqualityId::new(1))?;
        assert_eq!(alias.wave, wave);
        assert_eq!((alias.left.term, alias.right.term), (call, call));
        assert_eq!((alias.left.raw, alias.right.raw), (left, right));
        assert_eq!(alias.native_parent, native_uf_root(&db, uf, left));
        assert_eq!(alias.native_parent, native_uf_root(&db, uf, right));
        assert_ne!(alias.native_parent, alias.native_child);
        assert!([left, right].contains(&alias.native_parent) && [left, right].contains(&alias.native_child));
        let crate::EqualityReason::Congruence { cause, wave: reason_wave, as_of_edges, position } = alias.reason else { panic!("container native alias lost its congruence cause") };
        assert_eq!((reason_wave, as_of_edges), (wave, cutoff));
        let dependencies = test_cause_dependencies(view, cause)?;
        assert!(dependencies.facts.is_empty() && dependencies.rules.is_empty());
        assert!(matches!(dependencies.container_canonicalizations.as_slice(), [TestContainerDependency { wave: dependency_wave, equalities }] if *dependency_wave == wave && equalities.as_of_edges == cutoff && equalities.position == position && equalities.pairs.is_empty()));
        Ok(alias.native_child)
    }).unwrap();
    assert_eq!(
        trace.equality_edge_count().unwrap(),
        crate::EdgeHorizon::new(cutoff.get() + 1),
        "the historical cutoff counts every applied native union, including aliases"
    );

    // The component mirror must survive the native-only alias. A later real
    // equality reached through the former child id still joins the shared
    // structural term into the ordinary immutable explanation forest.
    let other = Value::new(10);
    let other_term = trace
        .intern_call(container_sort, ReplayOpId::new(110), &[child_term], other)
        .unwrap();
    trace
        .install_test_container_anchor(
            container_sort,
            TypeId::of::<Vec<Value>>(),
            &[child_sort],
            other,
            other_term,
        )
        .unwrap();
    let wave = Wave::new(2);
    db.set_trace_wave(wave);
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&trace, 110, wave),
        container_sort,
        alias_child,
        other,
        Value::new(2),
    );
    assert!(db.merge_all());
    db.finalize_trace_wave();

    trace
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, 2);
            assert_eq!(
                view.explain_equality_support_at(
                    crate::EqualityEndpoint {
                        sort: container_sort,
                        term: call,
                        raw: alias_child,
                    },
                    crate::EqualityEndpoint {
                        sort: container_sort,
                        term: other_term,
                        raw: other,
                    },
                    crate::EdgeHorizon::new(2),
                    view_end_position(view),
                )?
                .applied
                .as_ref(),
                &[
                    crate::AppliedEqualityId::new(1),
                    crate::AppliedEqualityId::new(2)
                ]
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn same_term_native_bridge_joins_distinct_historical_components() {
    let mut db = Database::default();
    let fact_table = db.add_table(
        SortedWritesTable::new(
            1,
            1,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right);
                false
            }),
        ),
        iter::empty(),
        iter::empty(),
    );
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let trace = db.try_enable_trace().unwrap();
    let sort = ReplaySortId::new(214);
    let child_sort = ReplaySortId::new(215);
    let child = trace.intern_literal(child_sort, ReplayLiteral::I64(1), Value::new(1));
    let left = Value::new(80);
    let right = Value::new(100);
    let other = Value::new(90);
    let prior_right_term = trace
        .intern_call(sort, ReplayOpId::new(214), &[child], right)
        .unwrap();
    let other_term = trace
        .intern_call(sort, ReplayOpId::new(215), &[child], other)
        .unwrap();
    let shared = trace
        .intern_call(sort, ReplayOpId::new(216), &[child], left)
        .unwrap();
    trace
        .register_table_layout(fact_table, &[Some(sort)])
        .unwrap();
    trace
        .register_table_merge_origins(fact_table, &[MergeOriginSelector::Incoming { column: 0 }])
        .unwrap();
    db.stage_source_row(fact_table, &[right], &[shared], SourceRef::Synthetic(214))
        .unwrap();
    assert!(db.merge_all());
    db.finalize_trace_wave();
    let prior_fact = committed_fact_id_for_key(&db, fact_table, &[right]);
    let site = |term| {
        trace.register_term_origin(TermOriginSpec {
            sort,
            term: Arc::new(TermTemplate::Static { term }),
        })
    };
    let prior_right_site = site(prior_right_term);
    let other_site = site(other_term);
    let incoming_origin = trace.register_row_origin(RowOriginSpec {
        table: fact_table,
        cells: [Some(Arc::new(TermTemplate::Static { term: shared }))].into(),
    });

    let first_wave = Wave::new(1);
    db.set_trace_wave(first_wave);
    let first = trace
        .typed_equality_proposal_from_sites(
            first_wave,
            sort,
            right,
            prior_right_site,
            other,
            other_site,
        )
        .unwrap();
    {
        let mut buffer = db.new_buffer(uf);
        buffer.stage_typed_union(
            &[right, other, Value::new(1)],
            empty_rule_cause(&trace, 214, first_wave),
            first,
        );
    }
    assert!(db.merge_all());

    let second_wave = Wave::new(2);
    db.set_trace_wave(second_wave);
    let bridge = trace
        .typed_merge_equality_proposal(
            second_wave,
            sort,
            right,
            left,
            fact_table,
            0,
            prior_fact,
            crate::provenance::RowOriginRef::Site(incoming_origin),
        )
        .unwrap();
    let incoming = empty_rule_cause(&trace, 215, second_wave);
    let merge_cause =
        trace.pending_merge_cause(crate::DeferredEqualityCause::ready(incoming), prior_fact);
    {
        let mut buffer = db.new_buffer(uf);
        buffer.stage_typed_union_deferred(&[right, left, Value::new(2)], merge_cause, bridge);
    }
    assert!(db.merge_all());
    db.finalize_trace_wave();

    trace
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, 2);
            let first = view.project_applied_equality(crate::AppliedEqualityId::new(1))?;
            let second = view.project_applied_equality(crate::AppliedEqualityId::new(2))?;
            assert_eq!((second.left.term, second.right.term), (shared, shared));
            let first_support = view.explain_equality_support_at(
                crate::EqualityEndpoint {
                    sort,
                    term: prior_right_term,
                    raw: right,
                },
                crate::EqualityEndpoint {
                    sort,
                    term: other_term,
                    raw: other,
                },
                crate::EdgeHorizon::new(1),
                first.position,
            )?;
            assert_eq!(
                first_support.applied.as_ref(),
                &[crate::AppliedEqualityId::new(1)]
            );
            assert!(first_support.facts.is_empty());
            let crate::EqualityReason::RuleUnion(first_match) = first.reason else {
                panic!("first equality lost its rule attribution")
            };
            assert_eq!(view.firing(first_match)?.rule, 214);
            let crate::EqualityReason::MergeFn { cause } = second.reason else {
                panic!("same-term bridge lost its merge attribution")
            };
            let dependencies = test_cause_dependencies(view, cause)?;
            assert_eq!(dependencies.facts, [prior_fact]);
            assert_eq!(dependencies.rules.len(), 1);
            assert_eq!(view.firing(dependencies.rules[0])?.rule, 215);
            assert_eq!(
                view.explain_equality_support_at(
                    crate::EqualityEndpoint {
                        sort,
                        term: shared,
                        raw: left,
                    },
                    crate::EqualityEndpoint {
                        sort,
                        term: other_term,
                        raw: other,
                    },
                    crate::EdgeHorizon::new(2),
                    view_end_position(view),
                )?
                .applied
                .as_ref(),
                &[crate::AppliedEqualityId::new(2)]
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn same_batch_native_catch_up_matches_durable_component_behavior() {
    let mut db = Database::default();
    let trace = db.try_enable_trace().unwrap();
    let mut uf = DisplacedTable::default();
    uf.enable_trace();
    let child_sort = ReplaySortId::new(117);
    let sort = ReplaySortId::new(118);
    let child = trace.intern_literal(child_sort, ReplayLiteral::I64(7), Value::new(7));
    let (owner, alias, other) = (Value::new(30), Value::new(20), Value::new(10));
    let shared = trace
        .intern_call(sort, ReplayOpId::new(118), &[child], owner)
        .unwrap();
    assert_eq!(
        trace
            .intern_call(sort, ReplayOpId::new(118), &[child], alias)
            .unwrap(),
        shared
    );
    let other_term = trace
        .intern_call(sort, ReplayOpId::new(119), &[child], other)
        .unwrap();

    let wave = Wave::new(1);
    db.set_trace_wave(wave);
    {
        let mut buffer = uf.new_buffer();
        for (rule, left) in [(118, owner), (119, alias)] {
            buffer.stage_typed_union(
                &[left, other, Value::new(1)],
                empty_rule_cause(&trace, rule, wave),
                trace
                    .typed_equality_proposal(wave, sort, left, other)
                    .unwrap(),
            );
        }
    }
    let mut state = ExecutionState::new(db.read_only_view(), Default::default());
    assert!(uf.merge(&mut state).added);
    db.finalize_trace_wave();

    trace
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, 2);
            let second = view.project_applied_equality(crate::AppliedEqualityId::new(2))?;
            assert_eq!((second.left.term, second.right.term), (shared, other_term));
            Ok(())
        })
        .unwrap();
}

#[test]
fn causal_wave_accepts_monotone_native_equality_timestamps() {
    let mut db = Database::default();
    let trace = db.try_enable_trace().unwrap();
    let wave = Wave::new(1);

    assert!(
        trace
            .validate_equality_wave_timestamp(wave, Value::new(2))
            .is_ok()
    );
    assert!(
        trace
            .validate_equality_wave_timestamp(wave, Value::new(3))
            .is_ok(),
        "native rebuild epochs remain inside one logical replay wave"
    );
    assert_eq!(
        trace
            .validate_equality_wave_timestamp(wave, Value::new(2))
            .unwrap_err(),
        "equality timestamps decreased within one causal wave"
    );
    assert!(
        trace
            .validate_equality_wave_timestamp(Wave::new(2), Value::new(4))
            .is_ok()
    );
}

#[test]
fn causal_trace_capture_exact_rhs_producer_term_not_global_alias() {
    let mut db = Database::default();
    let constructor = db.add_table_named(
        SortedWritesTable::new(
            1,
            3,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "constructor rows are immutable");
                false
            }),
        ),
        "ExactCurrentConstructor".into(),
        iter::empty(),
        iter::empty(),
    );
    let derived = db.add_table_named(
        SortedWritesTable::new(
            1,
            1,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "derived rows are immutable");
                false
            }),
        ),
        "ExactCurrentDerived".into(),
        iter::empty(),
        iter::empty(),
    );
    let trace = db.try_enable_trace().unwrap();
    let child_sort = ReplaySortId::new(197);
    let result_sort = ReplaySortId::new(198);
    let op = ReplayOpId::new(197);
    trace
        .register_table_layout(constructor, &[Some(child_sort), Some(result_sort), None])
        .unwrap();
    trace
        .register_table_constructor(
            constructor,
            ReplayConstructorSpec::new(result_sort, op, [child_sort]),
        )
        .unwrap();
    trace
        .register_table_layout(derived, &[Some(result_sort)])
        .unwrap();

    let wrong_child_value = Value::new(1970);
    let exact_child_value = Value::new(1971);
    let output_value = Value::new(1972);
    let wrong_child = trace.intern_literal(child_sort, ReplayLiteral::I64(1970), wrong_child_value);
    let exact_child = trace.intern_literal(child_sort, ReplayLiteral::I64(1971), exact_child_value);
    let wrong_call = trace
        .intern_call(result_sort, op, &[wrong_child], output_value)
        .unwrap();

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut action = rules.new_rule().build();
    let produced = action
        .lookup_or_insert_with_replay(
            constructor,
            &[exact_child_value.into()],
            &[output_value.into(), Value::new(1).into()],
            ColumnId::new(1),
            ReplayConstructorSpec::new(result_sort, op, [child_sort]),
        )
        .unwrap();
    action.insert(derived, &[produced.into()]).unwrap();
    action
        .try_build_with_capture(
            "exact-rhs-current-term",
            FiringCaptureSpec::new(
                197,
                iter::empty(),
                [crate::RuleBindingSpec::variable(produced, result_sort)],
            ),
        )
        .unwrap();
    let rules = rules.build();
    db.set_trace_wave(Wave::new(1));
    assert!(db.run_rule_set(&rules, ReportLevel::TimeOnly).changed);
    db.finalize_trace_wave();

    trace
        .with_view(|view| {
            let constructor_fact = fact_for_table(view, constructor);
            let exact_call = view.fact_terms(constructor_fact.id)?[1];
            assert_ne!(exact_call, wrong_call);
            assert_eq!(
                trace.lookup_term(result_sort, output_value),
                Some(wrong_call),
                "global lookup deliberately keeps the competing alias"
            );
            let derived_fact = fact_for_table(view, derived);
            let matched = view.firing(cause_firing(derived_fact.cause).unwrap())?;
            assert_eq!(view.firing_terms(matched.id)?.as_ref(), &[exact_call]);
            assert_eq!(
                trace.replay_term(exact_call),
                Some(crate::ReplayTerm::Call {
                    sort: result_sort,
                    op,
                    children: [exact_child].into(),
                })
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn capture_recipe_failure_precedes_catalog_and_rule_set_mutation() {
    const RULE: u32 = 199;

    let mut db = Database::default();
    let trace = db.try_enable_trace().unwrap();
    let sort = ReplaySortId::new(199);
    let op = ReplayOpId::new(199);
    let mut rules = RuleSetBuilder::new(&mut db);

    let mut query = rules.new_rule();
    let valid_before_failure = query.new_var_named("valid-before-failure");
    let destination = query.new_var_named("destination");
    let missing = query.new_var_named("missing");
    let mut action = query.build();
    action.register_replay_call(
        &[],
        valid_before_failure,
        Some(
            ReplayConstructorSpec::new(sort, op, iter::empty::<ReplaySortId>())
                .with_primitive_return_anchor(TypeId::of::<Vec<Value>>()),
        ),
    );
    action.register_replay_call(
        &[missing.into()],
        destination,
        Some(
            ReplayConstructorSpec::new(sort, op, [sort])
                .with_primitive_return_anchor(TypeId::of::<Vec<Value>>()),
        ),
    );
    let error = action
        .try_build_with_capture(
            "missing-producer",
            FiringCaptureSpec::new(
                RULE,
                iter::empty(),
                [crate::RuleBindingSpec::variable(destination, sort)],
            ),
        )
        .unwrap_err();
    assert_eq!(
        error.to_string(),
        "typed equality endpoint has no structural producer"
    );
    trace
        .with_view(|view| {
            assert!(view.rule_equality_layout(RULE).is_err());
            Ok(())
        })
        .unwrap();

    let mut query = rules.new_rule();
    let destination = query.new_var_named("destination");
    let mut action = query.build();
    action.register_replay_call(
        &[],
        destination,
        Some(
            ReplayConstructorSpec::new(sort, op, iter::empty::<ReplaySortId>())
                .with_primitive_return_anchor(TypeId::of::<Vec<Value>>()),
        ),
    );
    let rule = action
        .try_build_with_capture(
            "valid-producer",
            FiringCaptureSpec::new(
                RULE,
                iter::empty(),
                [crate::RuleBindingSpec::variable(destination, sort)],
            ),
        )
        .unwrap();

    let rules = rules.build();
    assert_eq!(rules.plans.len(), 1);
    assert!(rules.plans.get(rule).is_some());
    assert_eq!(rules.actions.len(), 1);
    let action = &rules.actions.iter().next().unwrap().1;
    let Instr::AnchorContainerCall {
        origin: Some(origin),
        ..
    } = action.instrs[0]
    else {
        panic!("valid rule lost its container anchor origin")
    };
    assert_eq!(origin.get(), 1, "failed preflight consumed an origin id");
}

#[test]
fn captureless_static_constructor_miss_fails_before_counter_or_rule_mutation() {
    let mut db = Database::default();
    let constructor = db.add_table_named(
        SortedWritesTable::new(
            0,
            2,
            Some(ColumnId::new(1)),
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "zero-argument constructor rows are immutable");
                false
            }),
        ),
        "StaticConstructor".into(),
        iter::empty(),
        iter::empty(),
    );
    let fresh = db.add_counter();
    let trace = db.try_enable_trace().unwrap();
    let sort = ReplaySortId::new(200);
    let op = ReplayOpId::new(200);
    let replay = ReplayConstructorSpec::new(sort, op, iter::empty::<ReplaySortId>());
    trace
        .register_table_layout(constructor, &[Some(sort), None])
        .unwrap();
    trace
        .register_table_constructor(constructor, replay.clone())
        .unwrap();

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut action = rules.new_rule().build();
    action
        .lookup_or_insert_with_replay(
            constructor,
            &[],
            &[WriteVal::IncCounter(fresh), Value::new(0).into()],
            ColumnId::new(0),
            replay.clone(),
        )
        .unwrap();
    let error = action
        .try_build_with_description("missing-static-constructor")
        .unwrap_err();
    assert_eq!(
        error.to_string(),
        "capture-enabled action requires exact match witnesses"
    );
    let rules = rules.build();
    assert!(rules.actions.is_empty());
    assert!(rules.plans.is_empty());
    assert!(db.get_table(constructor).is_empty());
    assert_eq!(db.read_counter(fresh), 0);

    let value = Value::new(2000);
    let term = trace.intern_call(sort, op, &[], value).unwrap();
    db.stage_source_row(
        constructor,
        &[value, Value::new(0)],
        &[term, crate::ReplayTermId::MISSING],
        SourceRef::Synthetic(200),
    )
    .unwrap();
    assert!(db.merge_all());

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut action = rules.new_rule().build();
    action
        .lookup_or_insert_with_replay(
            constructor,
            &[],
            &[WriteVal::IncCounter(fresh), Value::new(1).into()],
            ColumnId::new(0),
            replay,
        )
        .unwrap();
    action
        .try_build_with_description("existing-static-constructor")
        .unwrap();
    let rules = rules.build();
    assert!(!db.run_rule_set(&rules, ReportLevel::TimeOnly).changed);
    assert_eq!(db.read_counter(fresh), 0);
}

#[test]
fn prior_or_incoming_uses_callback_result_not_opaque_value_order() {
    let mut db = Database::default();
    let table = db.add_table(
        SortedWritesTable::new(
            1,
            2,
            None,
            vec![],
            Box::new(|_, prior, incoming, out| {
                out.extend_from_slice(incoming);
                out.as_slice() != prior
            }),
        ),
        iter::empty(),
        iter::empty(),
    );
    let trace = db.try_enable_trace().unwrap();
    let sort = ReplaySortId::new(216);
    trace
        .register_table_layout(table, &[Some(sort), Some(sort)])
        .unwrap();
    trace
        .register_table_merge_origins(
            table,
            &[
                MergeOriginSelector::Incoming { column: 0 },
                MergeOriginSelector::PriorOrIncoming {
                    incoming_column: 1,
                    prior_column: 1,
                },
            ],
        )
        .unwrap();

    let key = Value::new(2160);
    let prior = Value::new(10);
    let incoming = Value::new(20);
    let key_term = trace.intern_literal(sort, ReplayLiteral::I64(2160), key);
    let prior_term = trace.intern_literal(sort, ReplayLiteral::I64(10), prior);
    let incoming_term = trace.intern_literal(sort, ReplayLiteral::I64(20), incoming);
    db.stage_source_row(
        table,
        &[key, prior],
        &[key_term, prior_term],
        SourceRef::Synthetic(216),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_trace_wave();
    let prior_fact = committed_fact_id_for_key(&db, table, &[key]);

    let incoming_origin = trace.register_row_origin(RowOriginSpec {
        table,
        cells: [
            Some(Arc::new(TermTemplate::Static { term: key_term })),
            Some(Arc::new(TermTemplate::Static {
                term: incoming_term,
            })),
        ]
        .into(),
    });
    db.set_trace_wave(Wave::new(1));
    {
        let mut updates = db.new_buffer(table);
        updates.stage_insert_deferred_with_origin(
            &[key, incoming],
            crate::DeferredEqualityCause::ready(empty_rule_cause(&trace, 216, Wave::new(1))),
            incoming_origin,
        );
    }
    assert!(db.merge_all());
    db.finalize_trace_wave();
    trace
        .with_view(|view| {
            let latest = fact_ids(view)
                .filter_map(|id| view.fact(id).ok())
                .filter(|fact| fact.table == table)
                .max_by_key(|fact| fact.id)
                .unwrap();
            assert_eq!(latest.values, &[key, incoming]);
            assert_eq!(
                view.fact_terms(latest.id)?.as_ref(),
                &[key_term, incoming_term]
            );
            Ok(())
        })
        .unwrap();

    let tie_origin = trace.register_row_origin(RowOriginSpec {
        table,
        cells: [
            Some(Arc::new(TermTemplate::Static { term: key_term })),
            Some(Arc::new(TermTemplate::Call {
                sort,
                op: ReplayOpId::new(217),
                children: Arc::from([]),
            })),
        ]
        .into(),
    });
    let prepared = trace
        .prepare_merged_fact_origin(
            table,
            &[key, prior],
            &[key, prior],
            &[key, prior],
            prior_fact,
            Some(crate::provenance::RowOriginRef::Site(tie_origin)),
        )
        .unwrap();
    assert!(matches!(
        prepared,
        crate::provenance::PreparedFactOrigin::Merge {
            prior: fact,
            cells,
            ..
        } if fact == prior_fact
            && cells.as_slice()
                == [
                    crate::provenance::MergeCellOrigin::Incoming(0),
                    crate::provenance::MergeCellOrigin::Prior(1),
                ]
    ));
}

fn committed_fact_id_for_key(db: &Database, table: TableId, key: &[Value]) -> FactId {
    let table = db.get_table(table);
    let row = table.get_row(key).expect("committed key must exist");
    table
        .fact_id(row.id)
        .expect("capture-enabled row must have an immutable FactId")
}

fn committed_fact_id(db: &Database, table: TableId, key: Value) -> FactId {
    committed_fact_id_for_key(db, table, &[key])
}

fn committed_row_id(db: &Database, table: TableId, key: Value) -> RowId {
    db.get_table(table)
        .get_row(&[key])
        .expect("committed key must exist")
        .id
}

#[test]
fn serial_compaction_preserves_live_and_historical_fact_ids() {
    let mut db = Database::default();
    let table = db.add_table_named(
        SortedWritesTable::new(
            1,
            2,
            None,
            vec![],
            Box::new(|_, left, right, out| {
                if right[1] > left[1] {
                    out.extend_from_slice(right);
                    true
                } else {
                    false
                }
            }),
        ),
        "SerialCompaction".into(),
        iter::empty(),
        iter::empty(),
    );
    let trace = db.try_enable_trace().unwrap();
    register_test_capture_table(&trace, table, 2);
    let zero = trace.intern_test_term("zero");
    for key in 0..20 {
        let key_term = trace.intern_test_term(&format!("key-{key}"));
        db.stage_source_row(
            table,
            &[Value::new(key), Value::new(0)],
            &[key_term, zero],
            SourceRef::Synthetic(key as u64),
        )
        .unwrap();
    }
    assert!(db.merge_all());
    db.finalize_trace_wave();

    let survivor = Value::new(19);
    let survivor_fact = committed_fact_id(&db, table, survivor);
    let survivor_row = committed_row_id(&db, table, survivor);
    let historical = committed_fact_id(&db, table, Value::new(1));
    let version = db.get_table(table).version();

    db.set_trace_wave(Wave::new(1));
    let causes = trace
        .register_firings(30, Wave::new(1), 0, &[], &[], &(0..40).collect::<Vec<_>>())
        .into_iter()
        .map(|(_, cause)| cause);
    let mut updates = db.new_buffer(table);
    for (index, cause) in causes.enumerate() {
        let row = [
            Value::from_usize(1 + index / 4),
            Value::from_usize(1 + index % 4),
        ];
        let terms = row.map(|raw| trace.lookup_term(TEST_REPLAY_SORT, raw).unwrap());
        let origin = trace.install_source_row(table, &row, &terms).unwrap();
        updates.stage_insert_deferred_with_origin(
            &row,
            crate::DeferredEqualityCause::ready(cause),
            origin,
        );
    }
    drop(updates);
    assert!(db.merge_all());
    db.finalize_trace_wave();

    assert_ne!(version.major, db.get_table(table).version().major);
    assert_eq!(committed_fact_id(&db, table, survivor), survivor_fact);
    assert_ne!(committed_row_id(&db, table, survivor), survivor_row);
    assert_ne!(committed_fact_id(&db, table, Value::new(1)), historical);
    trace
        .with_view(|view| {
            view.fact(historical)
                .map(|fact| assert_eq!(fact.id, historical))
        })
        .unwrap();
}

fn decomposed_projected_capture_case(retain_existential: bool) {
    let mut db = Database::default();
    let relation = |arity| {
        SortedWritesTable::new(
            arity,
            arity,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "relation rows are immutable");
                false
            }),
        )
    };
    let r = db.add_table(relation(3), iter::empty(), iter::empty());
    let s = db.add_table(relation(3), iter::empty(), iter::empty());
    let t = db.add_table(relation(2), iter::empty(), iter::empty());
    let u = db.add_table(relation(2), iter::empty(), iter::empty());
    let derived = db.add_table(
        relation(if retain_existential { 5 } else { 4 }),
        iter::empty(),
        iter::empty(),
    );
    let trace = db.try_enable_trace().unwrap();
    for (table, columns) in [
        (r, 3),
        (s, 3),
        (t, 2),
        (u, 2),
        (derived, if retain_existential { 5 } else { 4 }),
    ] {
        register_test_capture_table(&trace, table, columns);
    }
    for (source, (table, row)) in [
        (r, vec![1, 10, 100]),
        (r, vec![1, 10, 101]),
        (s, vec![10, 20, 100]),
        (s, vec![10, 20, 101]),
        (t, vec![20, 30]),
        (u, vec![30, 1]),
    ]
    .into_iter()
    .enumerate()
    {
        let values = row
            .iter()
            .copied()
            .map(Value::from_usize)
            .collect::<Vec<_>>();
        let terms = row
            .iter()
            .map(|value| trace.intern_test_term(&format!("value-{value}")))
            .collect::<Vec<_>>();
        db.stage_source_row(table, &values, &terms, SourceRef::Synthetic(source as u64))
            .unwrap();
    }
    assert!(db.merge_all());
    db.finalize_trace_wave();

    let r_first =
        committed_fact_id_for_key(&db, r, &[Value::new(1), Value::new(10), Value::new(100)]);
    let r_second =
        committed_fact_id_for_key(&db, r, &[Value::new(1), Value::new(10), Value::new(101)]);
    let s_first =
        committed_fact_id_for_key(&db, s, &[Value::new(10), Value::new(20), Value::new(100)]);
    let s_second =
        committed_fact_id_for_key(&db, s, &[Value::new(10), Value::new(20), Value::new(101)]);
    let t_fact = committed_fact_id_for_key(&db, t, &[Value::new(20), Value::new(30)]);
    let u_fact = committed_fact_id_for_key(&db, u, &[Value::new(30), Value::new(1)]);
    let existential_100_term = trace.intern_test_term("value-100");
    let existential_101_term = trace.intern_test_term("value-101");

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    query.set_plan_strategy(PlanStrategy::Gj);
    let x = query.new_var_named("x");
    let y = query.new_var_named("y");
    let z = query.new_var_named("z");
    let w = query.new_var_named("w");
    let existential = query.new_var_named("existential");
    let r_atom = query
        .add_atom(r, &[x.into(), y.into(), existential.into()], &[])
        .unwrap();
    let s_atom = query
        .add_atom(s, &[y.into(), z.into(), existential.into()], &[])
        .unwrap();
    let t_atom = query.add_atom(t, &[z.into(), w.into()], &[]).unwrap();
    let u_atom = query.add_atom(u, &[w.into(), x.into()], &[]).unwrap();
    let mut action = query.build();
    let mut outputs = vec![x.into(), y.into(), z.into(), w.into()];
    let mut ordinary_vars = vec![x, y, z, w];
    if retain_existential {
        outputs.push(existential.into());
        ordinary_vars.push(existential);
    }
    action.insert(derived, &outputs).unwrap();
    action
        .try_build_with_capture(
            "existential-rectangle",
            FiringCaptureSpec::new(
                51,
                [r_atom, s_atom, t_atom, u_atom],
                ordinary_vars
                    .into_iter()
                    .map(|variable| crate::RuleBindingSpec::variable(variable, TEST_REPLAY_SORT)),
            ),
        )
        .unwrap();
    let rule_set = rules.build();
    let (plan, _, _) = rule_set.plans.values().next().unwrap();
    let Plan::DecomposedPlan(plan) = plan else {
        panic!("existential capture canary must exercise decomposed materialization");
    };
    assert!(plan.stages.blocks.len() >= 2);
    if retain_existential {
        let projected = plan
            .stages
            .blocks
            .iter()
            .flat_map(|(stages, _)| stages.instrs.iter())
            .filter_map(|stage| match stage {
                JoinStage::FusedIntersectMat {
                    cover,
                    mode: MatScanMode::KeyOnly | MatScanMode::Lookup(_),
                    ..
                } => Some(*cover),
                _ => None,
            })
            .collect::<Vec<_>>();
        let exact = plan
            .result_block
            .instrs
            .iter()
            .filter_map(|stage| match stage {
                JoinStage::FusedIntersectMat {
                    cover,
                    mode: MatScanMode::Full | MatScanMode::Value(_),
                    ..
                } => Some(*cover),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(
            projected.iter().any(|cover| exact.contains(cover)),
            "the precision canary must use one materialization through both a projected probe and an exact result scan"
        );
    }

    db.set_trace_wave(Wave::new(1));
    reset_pending_witness_resolution_count();
    assert!(db.run_rule_set(&rule_set, ReportLevel::TimeOnly).changed);
    db.finalize_trace_wave();
    assert_eq!(
        pending_witness_resolution_count(),
        2,
        "every normal-return observed lane resolves one exact decomposed witness"
    );
    trace
        .with_view(|view| {
            let derived_facts = fact_ids(view)
                .filter_map(|id| view.fact(id).ok())
                .filter(|fact| fact.table == derived)
                .collect::<Vec<_>>();
            if retain_existential {
                assert_eq!(derived_facts.len(), 2);
                for fact in derived_facts {
                    let matched = view.firing(
                        cause_firing(fact.cause)
                            .expect("each derived row must cite its own exact native match"),
                    )?;
                    let terms = view.fact_terms(fact.id)?;
                    let expected = if terms[4] == existential_100_term {
                        [r_first, s_first, t_fact, u_fact]
                    } else {
                        assert_eq!(terms[4], existential_101_term);
                        [r_second, s_second, t_fact, u_fact]
                    };
                    assert_eq!(matched.premises, expected);
                }
            } else {
                assert_eq!(derived_facts.len(), 1);
                let matched = view.firing(cause_firing(derived_facts[0].cause).unwrap())?;
                assert_eq!(matched.premises, &[r_first, s_first, t_fact, u_fact]);
                assert!(!matched.premises.contains(&r_second));
                assert!(!matched.premises.contains(&s_second));
            }
            Ok(())
        })
        .unwrap();
}

#[test]
fn decomposed_key_only_capture_uses_first_exact_existential_support() {
    decomposed_projected_capture_case(false);
}

#[test]
fn decomposed_exact_result_owner_overrides_nested_projected_support() {
    decomposed_projected_capture_case(true);
}

#[test]
fn capture_disabled_rule_path_uses_no_fact_sidecars_or_witness_reads() {
    let mut db = Database::default();
    let relation = || {
        SortedWritesTable::new(
            1,
            2,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "relation rows are immutable");
                false
            }),
        )
    };
    let input = db.add_table_named(relation(), "Input".into(), iter::empty(), iter::empty());
    let constructor = db.add_table_named(
        SortedWritesTable::new(
            1,
            3,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "constructor rows are immutable");
                false
            }),
        ),
        "OrdinaryConstructor".into(),
        iter::empty(),
        iter::empty(),
    );
    let derived = db.add_table_named(
        SortedWritesTable::new(
            2,
            3,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "derived rows are immutable");
                false
            }),
        ),
        "Derived".into(),
        iter::empty(),
        iter::empty(),
    );
    let fresh = db.add_counter();

    let mut source = db.new_buffer(input);
    source.stage_insert(&[Value::new(7), Value::new(0)]);
    drop(source);
    assert!(db.merge_all());

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let value = query.new_var_named("value");
    let input_ts = query.new_var_named("input_ts");
    query
        .add_atom(input, &[value.into(), input_ts.into()], &[])
        .unwrap();
    let mut action = query.build();
    let node = action
        .lookup_or_insert(
            constructor,
            &[value.into()],
            &[WriteVal::IncCounter(fresh), Value::new(1).into()],
            ColumnId::new(1),
        )
        .unwrap();
    action
        .insert(derived, &[value.into(), node.into(), Value::new(1).into()])
        .unwrap();
    action.build();
    let rule_set = rules.build();
    assert!(
        rule_set.actions.iter().any(|(_, action)| action
            .instrs
            .iter()
            .any(|instr| matches!(instr, Instr::LookupOrInsertDefault { .. }))),
        "ordinary constructor must compile to the non-replay instruction"
    );
    assert!(
        rule_set.actions.iter().all(|(_, action)| action
            .instrs
            .iter()
            .all(|instr| !matches!(instr, Instr::LookupOrInsertDefaultReplay { .. }))),
        "capture-only producer metadata must be absent from ordinary action tapes"
    );

    reset_causal_lookup_counters();
    let report = db.run_rule_set(&rule_set, ReportLevel::TimeOnly);
    assert!(report.changed);
    assert_eq!(
        causal_lookup_counters(),
        (0, 0),
        "ordinary execution must not read capture FactIds or witness rows"
    );
    for table in [input, constructor, derived] {
        let table = db
            .get_table(table)
            .as_any()
            .downcast_ref::<SortedWritesTable>()
            .unwrap();
        assert_eq!(
            table.causal_sidecar_bytes(),
            0,
            "ordinary tables must not allocate causal sidecars"
        );
    }
}

fn activation_test_relation() -> SortedWritesTable {
    SortedWritesTable::new(
        1,
        2,
        None,
        vec![],
        Box::new(|_, left, right, _| {
            assert_eq!(left, right, "relation rows are immutable");
            false
        }),
    )
}

#[test]
fn causal_capture_activation_is_all_or_nothing_across_tables() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let pending = db.add_table(activation_test_relation(), iter::empty(), iter::empty());
    {
        let mut buffer = db.new_buffer(pending);
        buffer.stage_insert(&[Value::new(1), Value::new(0)]);
    }

    assert_eq!(
        db.try_enable_trace().err().unwrap(),
        "table has queued capture-disabled mutations"
    );
    assert!(
        db.trace.is_none(),
        "the database mode must remain disabled after any table fails preflight"
    );
    let raw_uf_staging = catch_unwind(AssertUnwindSafe(|| {
        let mut buffer = db.get_table(uf).new_buffer();
        buffer.stage_insert(&[Value::new(2), Value::new(1), Value::new(0)]);
    }));
    assert!(
        raw_uf_staging.is_ok(),
        "an earlier UF table must not be partially switched to typed capture staging"
    );
}

#[test]
fn causal_presence_relation_remove_is_not_retained() {
    let mut db = Database::default();
    let relation = db.add_table(
        SortedWritesTable::new(1, 1, None, vec![], Box::new(|_, _, _, _| false)),
        iter::empty(),
        iter::empty(),
    );
    let trace = db.try_enable_trace().unwrap();
    register_test_capture_table_kind(&trace, relation, 1, ReplayTableKind::PresenceRelation);
    let key = Value::new(7420);
    install_test_row_terms(&trace, &[key]);
    db.stage_source_row(
        relation,
        &[key],
        &[trace.lookup_term(TEST_REPLAY_SORT, key).unwrap()],
        SourceRef::Synthetic(742),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_trace_wave();

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let matched = query.new_var_named("matched");
    let atom = query.add_atom(relation, &[matched.into()], &[]).unwrap();
    let mut action = query.build();
    action.remove(relation, &[matched.into()]).unwrap();
    action
        .try_build_with_capture(
            "relation-delete",
            FiringCaptureSpec::new(
                742,
                [atom],
                [crate::RuleBindingSpec::variable(matched, TEST_REPLAY_SORT)],
            ),
        )
        .unwrap();
    let rules = rules.build();

    db.set_trace_wave(Wave::new(1));
    db.run_rule_set(&rules, ReportLevel::TimeOnly);
    db.finalize_trace_wave();
    assert!(db.get_table(relation).get_row(&[key]).is_none());
    trace
        .with_view(|view| {
            assert_eq!(view.totals().removals, 0);
            Ok(())
        })
        .unwrap();
}

#[test]
fn causal_remove_batch_preflights_all_causes_before_native_mutation() {
    let mut db = Database::default();
    let table = db.add_table(
        SortedWritesTable::new(1, 1, None, vec![], Box::new(|_, _, _, _| false)),
        iter::empty(),
        iter::empty(),
    );
    let trace = db.try_enable_trace().unwrap();
    register_test_capture_table(&trace, table, 1);
    let first = Value::new(7430);
    let second = Value::new(7431);
    install_test_row_terms(&trace, &[first, second]);
    for (source, value) in [(743, first), (744, second)] {
        db.stage_source_row(
            table,
            &[value],
            &[trace.lookup_term(TEST_REPLAY_SORT, value).unwrap()],
            SourceRef::Synthetic(source),
        )
        .unwrap();
    }
    assert!(db.merge_all());
    db.finalize_trace_wave();

    let wave = Wave::new(1);
    db.set_trace_wave(wave);
    let valid = crate::DeferredEqualityCause::ready(empty_rule_cause(&trace, 743, wave));
    let foreign_trace = Trace::default();
    let foreign_batch = foreign_trace.pending_firing_batch(744, wave, 0, &[], &[], 1);
    let foreign = crate::DeferredEqualityCause::pending(
        foreign_trace.pending_firing_cause(&foreign_batch, 0),
    );
    {
        let mut buffer = db.new_buffer(table);
        buffer.stage_remove_deferred(&[first], valid);
        buffer.stage_remove_deferred(&[second], foreign);
    }

    let failed = catch_unwind(AssertUnwindSafe(|| db.merge_all()));
    assert!(failed.is_err(), "a foreign removal cause must fail closed");
    assert!(db.get_table(table).get_row(&[first]).is_some());
    assert!(db.get_table(table).get_row(&[second]).is_some());
}

#[test]
fn causal_same_wave_remove_precedes_replacement_write() {
    let mut db = Database::default();
    let table = db.add_table(
        SortedWritesTable::new(
            1,
            2,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(
                    left, right,
                    "replacement must not collide with the stale row"
                );
                false
            }),
        ),
        iter::empty(),
        iter::empty(),
    );
    let trace = db.try_enable_trace().unwrap();
    register_test_capture_table(&trace, table, 2);
    let key = Value::new(7450);
    trace.register_table_key_columns(table, 1).unwrap();
    let old_value = Value::new(7451);
    let new_value = Value::new(7452);
    install_test_row_terms(&trace, &[key, old_value, new_value]);
    db.stage_source_row(
        table,
        &[key, old_value],
        &[
            trace.lookup_term(TEST_REPLAY_SORT, key).unwrap(),
            trace.lookup_term(TEST_REPLAY_SORT, old_value).unwrap(),
        ],
        SourceRef::Synthetic(745),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_trace_wave();
    let removed_fact = committed_fact_id(&db, table, key);

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let matched_key = query.new_var_named("key");
    let matched_value = query.new_var_named("value");
    let atom = query
        .add_atom(table, &[matched_key.into(), matched_value.into()], &[])
        .unwrap();
    let mut action = query.build();
    // Intentionally stage the write first. Native publication still applies
    // the common-prestate delete phase before the write phase.
    action
        .insert(table, &[matched_key.into(), new_value.into()])
        .unwrap();
    action.remove(table, &[matched_key.into()]).unwrap();
    action
        .try_build_with_capture(
            "replace-after-delete",
            FiringCaptureSpec::new(
                745,
                [atom],
                [
                    crate::RuleBindingSpec::variable(matched_key, TEST_REPLAY_SORT),
                    crate::RuleBindingSpec::variable(matched_value, TEST_REPLAY_SORT),
                ],
            ),
        )
        .unwrap();
    let rules = rules.build();

    db.set_trace_wave(Wave::new(1));
    db.run_rule_set(&rules, ReportLevel::TimeOnly);
    db.finalize_trace_wave();
    let row = db
        .get_table(table)
        .get_row(&[key])
        .expect("the replacement row must be committed");
    assert_eq!(row.vals.as_slice(), &[key, new_value]);
    // Permanent occurrence-liveness canary. The temporary differential oracle
    // was removed with the owned compatibility model.
    trace
        .with_view(|view| {
            assert_eq!(view.totals().facts, 2);
            assert_eq!(view.totals().removals, 1);
            let removal = view.removal(0)?;
            assert_eq!(removal.removed_fact, removed_fact);
            let replacement = FactId::new(removed_fact.get() + 1);
            assert_eq!(
                removal.cause,
                cause_firing(view.fact(replacement)?.cause).unwrap()
            );
            let original = view.fact(removed_fact)?;
            let old_cell = crate::FactCellRef {
                fact: removed_fact,
                column: ColumnId::new(1),
            };
            assert!(view.fact_cell_at(old_cell, original.position).is_ok());
            let replacement_record = view.fact(replacement)?;
            assert!(replacement_record.position > removal.position);
            assert!(matches!(
                view.fact_cell_at(old_cell, removal.position),
                Err(crate::TraceViewError::FactNoLongerLive {
                    fact,
                    ended_at,
                    successor,
                    ..
                }) if fact == removed_fact
                    && ended_at == removal.position
                    && successor.is_none()
            ));
            let before_removal = crate::HistoryPosition::new(removal.position.get() - 1);
            assert!(view.fact_cell_at(old_cell, before_removal).is_ok());
            assert!(matches!(
                view.fact_cell_at(old_cell, replacement_record.position),
                Err(crate::TraceViewError::FactNoLongerLive { fact, .. })
                    if fact == removed_fact
            ));

            assert_ne!(replacement, removed_fact);
            assert!(
                view.fact_cell_at(
                    crate::FactCellRef {
                        fact: replacement,
                        column: ColumnId::new(1),
                    },
                    replacement_record.position,
                )
                .is_ok()
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn basic_query() {
    run_serial_and_parallel(basic_query_inner);
}

fn basic_query_inner() {
    let MathEgraph {
        num,
        add,
        id_counter,
        mut db,
        ..
    } = basic_math_egraph();

    db.base_values_mut().register_type::<i64>();
    let add_int = db.add_external_function(Box::new(make_external_func(|exec_state, args| {
        let [x, y] = args else { panic!() };
        let x: i64 = exec_state.base_values().unwrap(*x);
        let y: i64 = exec_state.base_values().unwrap(*y);
        let z: i64 = x + y;
        Some(exec_state.base_values().get(z))
    })));

    // Add the numbers 1 through 10 to the num table at timestamp 0.
    let mut ids = Vec::new();
    {
        let mut num_buf = db.new_buffer(num);
        for i in 0..10 {
            let id = db.inc_counter(id_counter);
            let i = db.base_values().get::<i64>(i as i64);
            ids.push(i);
            num_buf.stage_insert(&[i, Value::from_usize(id), Value::new(0)]);
        }
    } // num_buf flushed

    db.merge_all();

    let mut add_ids = Vec::new();
    {
        let mut add_buf = db.new_buffer(add);
        for i in ids.chunks(2) {
            let &[x, y] = i else { unreachable!() };
            // Insert (add x y) into the database with a fresh id at timestamp 0
            let id = Value::from_usize(db.inc_counter(id_counter));
            add_ids.push(id);
            add_buf.stage_insert(&[x, y, id, Value::new(0)]);
        }
    } // add_buf flushed

    db.merge_all();

    let mut rsb = RuleSetBuilder::new(&mut db);
    let mut add_query = rsb.new_rule();
    // Add(x, y, z, t1),
    // Num(a, x, t2),
    // Num(b, y, t3),
    // =>
    // Num(+ a b, z, 1)
    let x = add_query.new_var_named("x");
    let y = add_query.new_var_named("y");
    let z = add_query.new_var_named("z");
    let t1 = add_query.new_var_named("t1");
    let t2 = add_query.new_var_named("t2");
    let t3 = add_query.new_var_named("t3");
    let a = add_query.new_var_named("a");
    let b = add_query.new_var_named("b");

    add_query
        .add_atom(add, &[x.into(), y.into(), z.into(), t1.into()], &[])
        .unwrap();
    add_query
        .add_atom(num, &[a.into(), x.into(), t2.into()], &[])
        .unwrap();
    add_query
        .add_atom(num, &[b.into(), y.into(), t3.into()], &[])
        .unwrap();
    let mut rules = add_query.build();
    let add_a_b = rules.call_external(add_int, &[a.into(), b.into()]).unwrap();
    rules
        .insert(num, &[add_a_b.into(), z.into(), Value::new(1).into()])
        .unwrap();
    rules.build_with_description("add");
    let rule_set = rsb.build();

    let report = db.run_rule_set(&rule_set, ReportLevel::TimeOnly);

    assert!(report.changed, "{report:?}");
    assert_eq!(report.num_matches("add"), 5, "{report:?}");
    let num_table = db.get_table(num);
    let all_num = num_table.all();
    let items = num_table.scan(all_num.as_ref());
    let mut res = Vec::from_iter(
        items
            .iter()
            .map(|(_, row)| db.base_values().unwrap::<i64>(row[0])),
    );
    res.sort();
    assert_eq!(res, Vec::from_iter((0..10).chain([13, 17].into_iter())));
}

#[test]
fn timing_split_separates_inline_batches_and_final_flush() {
    let mut db = Database::default();
    let new_relation = || {
        SortedWritesTable::new(
            1,
            1,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "merge not supported");
                false
            }),
        )
    };
    let input = db.add_table(new_relation(), iter::empty(), iter::empty());
    let output = db.add_table(new_relation(), iter::empty(), iter::empty());
    {
        let mut input_buffer = db.new_buffer(input);
        // One full 128-binding batch runs inline; the remaining 127 bindings
        // run in the final flush. Both sides are deliberately substantial so
        // the duration inequalities remain robust on coarse platform clocks.
        for value in 0..255 {
            input_buffer.stage_insert(&[Value::new(value)]);
        }
    }
    db.merge_all();

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let value = query.new_var_named("value");
    query.add_atom(input, &[value.into()], &[]).unwrap();
    let mut action = query.build();
    action.insert(output, &[value.into()]).unwrap();
    action.build_with_description("copy");
    let rule_set = rules.build();

    let report = db.run_rule_set(&rule_set, ReportLevel::TimeOnly);
    let legacy_plan_time = report.rule_search_and_apply_time("copy");
    let PreMergeTiming::Split {
        search,
        apply,
        unattributed,
    } = report.pre_merge
    else {
        panic!("serial execution must report split timing");
    };

    assert!(search > std::time::Duration::ZERO);
    assert!(apply > std::time::Duration::ZERO);
    assert!(
        search < legacy_plan_time,
        "the inline action batch must be subtracted from search"
    );
    assert!(
        search + apply > legacy_plan_time,
        "the final action flush must be included in apply"
    );
    assert_eq!(report.pre_merge.total(), search + apply + unattributed);
}

#[test]
fn phase_timing_is_available_for_an_empty_ruleset() {
    let mut db = Database::default();
    let rule_set = RuleSetBuilder::new(&mut db).build();

    let report = db.run_rule_set(&rule_set, ReportLevel::TimeOnly);

    assert_eq!(
        report.pre_merge,
        PreMergeTiming::Split {
            search: std::time::Duration::ZERO,
            apply: std::time::Duration::ZERO,
            unattributed: std::time::Duration::ZERO,
        }
    );
}

#[test]
fn parallel_execution_keeps_split_phase_timing_unavailable() {
    rayon::ThreadPoolBuilder::new()
        .num_threads(4)
        .build()
        .unwrap()
        .install(|| {
            let mut db = Database::default();
            let new_relation = || {
                SortedWritesTable::new(
                    1,
                    1,
                    None,
                    vec![],
                    Box::new(|_, left, right, _| {
                        assert_eq!(left, right, "merge not supported");
                        false
                    }),
                )
            };
            let input = db.add_table(new_relation(), iter::empty(), iter::empty());
            let output = db.add_table(new_relation(), iter::empty(), iter::empty());
            {
                let mut input_buffer = db.new_buffer(input);
                for value in 0..10_001 {
                    input_buffer.stage_insert(&[Value::new(value)]);
                }
            }
            db.merge_all();

            let mut rules = RuleSetBuilder::new(&mut db);
            let mut query = rules.new_rule();
            let value = query.new_var_named("value");
            query.add_atom(input, &[value.into()], &[]).unwrap();
            let mut action = query.build();
            action.insert(output, &[value.into()]).unwrap();
            action.build_with_description("copy");
            let rule_set = rules.build();

            let report = db.run_rule_set(&rule_set, ReportLevel::TimeOnly);

            let PreMergeTiming::Combined { elapsed } = report.pre_merge else {
                panic!("parallel execution must report combined timing");
            };
            assert!(elapsed > std::time::Duration::ZERO);
        });
}

#[test]
fn line_graph_1_fj_puresize() {
    run_serial_and_parallel(|| line_graph_1_test(PlanStrategy::PureSize));
}

#[test]
fn line_graph_1_fj_mincover() {
    run_serial_and_parallel(|| line_graph_1_test(PlanStrategy::MinCover));
}

#[test]
fn line_graph_1_gj() {
    run_serial_and_parallel(|| line_graph_1_test(PlanStrategy::Gj));
}

fn line_graph_1_test(strat: PlanStrategy) {
    let mut db = Database::default();
    let edge_impl = SortedWritesTable::new(
        2,
        2,
        None,
        vec![],
        Box::new(move |_, a, b, _| {
            if a != b {
                panic!("merge not supported")
            } else {
                false
            }
        }),
    );
    let edges = db.add_table(edge_impl, iter::empty(), iter::empty());
    let nodes = Vec::from_iter((0..10).map(Value::new));
    {
        let mut edge_buf = db.new_buffer(edges);
        for edge in nodes.windows(2) {
            edge_buf.stage_insert(edge);
        }
    }
    db.merge_all();

    let mut rsb = RuleSetBuilder::new(&mut db);
    let mut query = rsb.new_rule();
    query.set_plan_strategy(strat);
    // edge(x, y), edge(y, z) => edge(x, z)
    let x = query.new_var_named("x");
    let y = query.new_var_named("y");
    let z = query.new_var_named("z");
    query.add_atom(edges, &[x.into(), y.into()], &[]).unwrap();
    query.add_atom(edges, &[y.into(), z.into()], &[]).unwrap();
    let mut rule = query.build();
    rule.insert(edges, &[x.into(), z.into()]).unwrap();
    rule.build();
    let rule_set = rsb.build();

    assert!(db.run_rule_set(&rule_set, ReportLevel::TimeOnly).changed);

    let mut expected = Vec::from_iter(
        nodes
            .windows(2)
            .map(|x| vec![x[0], x[1]])
            .chain(nodes.windows(3).map(|x| vec![x[0], x[2]])),
    );
    expected.sort();

    let edges_table = db.get_table(edges);
    let all = edges_table.all();
    let vals = edges_table.scan(all.as_ref());
    let mut got = Vec::from_iter(vals.iter().map(|(_, row)| row.to_vec()));
    got.sort();
    assert_eq!(expected, got);
}

#[test]
fn line_graph_2_fj_puresize() {
    run_serial_and_parallel(|| line_graph_2_test(PlanStrategy::PureSize));
}

#[test]
fn line_graph_2_fj_mincover() {
    run_serial_and_parallel(|| line_graph_2_test(PlanStrategy::MinCover));
}

#[test]
fn line_graph_2_gj() {
    run_serial_and_parallel(|| line_graph_2_test(PlanStrategy::Gj));
}

fn line_graph_2_test(strat: PlanStrategy) {
    let mut db = Database::default();
    let edge_impl = SortedWritesTable::new(
        2,
        2,
        None,
        vec![],
        Box::new(move |_, a, b, _| {
            if a != b {
                panic!("merge not supported")
            } else {
                false
            }
        }),
    );
    let edges = db.add_table(edge_impl, iter::empty(), iter::empty());
    let nodes = Vec::from_iter((0..10).map(Value::new));
    {
        let mut edge_buf = db.new_buffer(edges);
        for edge in nodes.windows(2) {
            edge_buf.stage_insert(edge);
        }
    }
    db.merge_all();

    let mut rsb = RuleSetBuilder::new(&mut db);
    let mut query = rsb.new_rule();
    query.set_plan_strategy(strat);
    // edge(x, y), edge(y, z) => edge(x, z) :where y > 1
    let x = query.new_var_named("x");
    let y = query.new_var_named("y");
    let z = query.new_var_named("z");
    query
        .add_atom(
            edges,
            &[x.into(), y.into()],
            &[Constraint::GtConst {
                col: ColumnId::new(1),
                val: Value::new(1),
            }],
        )
        .unwrap();
    query.add_atom(edges, &[y.into(), z.into()], &[]).unwrap();
    let mut rule = query.build();
    rule.insert(edges, &[x.into(), z.into()]).unwrap();
    rule.build();
    let rule_set = rsb.build();

    assert!(db.run_rule_set(&rule_set, ReportLevel::TimeOnly).changed);

    let mut expected = Vec::from_iter(
        nodes.windows(2).map(|x| vec![x[0], x[1]]).chain(
            nodes
                .windows(3)
                .filter(|x| x[1] > Value::new(1))
                .map(|x| vec![x[0], x[2]]),
        ),
    );
    expected.sort();

    let edges_table = db.get_table(edges);
    let all = edges_table.all();
    let vals = edges_table.scan(all.as_ref());
    let mut got = Vec::from_iter(vals.iter().map(|(_, row)| row.to_vec()));
    got.sort();
    assert_eq!(expected, got);
}

fn intersection_test(strat: PlanStrategy) {
    let mut db = Database::default();
    let rst = (0..3).map(|_| {
        SortedWritesTable::new(
            2,
            2,
            None,
            vec![],
            Box::new(move |_, a, b, _| {
                if a != b {
                    panic!("merge not supported")
                } else {
                    false
                }
            }),
        )
    });
    let u = SortedWritesTable::new(
        1,
        1,
        None,
        vec![],
        Box::new(move |_, a, b, _| {
            if a != b {
                panic!("merge not supported")
            } else {
                false
            }
        }),
    );
    let rst_ids = rst
        .map(|r| db.add_table(r, iter::empty(), iter::empty()))
        .collect::<Vec<TableId>>();
    let u_id = db.add_table(u, iter::empty(), iter::empty());

    for rel in rst_ids.iter() {
        let mut rel_buf = db.new_buffer(*rel);
        for x in 0..10 {
            rel_buf.stage_insert(&[Value::new(x), Value::new(x)]);
        }
    }
    db.merge_all();

    let mut rsb = RuleSetBuilder::new(&mut db);
    let mut query = rsb.new_rule();
    query.set_plan_strategy(strat);
    // R(x), S(x), T(x), x > 5 => U(X)
    let x = query.new_var_named("x");
    for rel in rst_ids.iter() {
        query
            .add_atom(
                *rel,
                &[x.into(), x.into()],
                &[Constraint::GtConst {
                    col: ColumnId::new(0),
                    val: Value::new(5),
                }],
            )
            .unwrap();
    }
    let mut rule = query.build();
    rule.insert(u_id, &[x.into()]).unwrap();
    rule.build();
    let rule_set = rsb.build();

    assert!(db.run_rule_set(&rule_set, ReportLevel::TimeOnly).changed);

    let expected = Vec::from_iter((6..10).map(|x| vec![Value::new(x)]));

    let u_table = db.get_table(u_id);
    let all = u_table.all();
    let vals = u_table.scan(all.as_ref());
    let mut got = Vec::from_iter(vals.iter().map(|(_, row)| row.to_vec()));
    got.sort();
    assert_eq!(expected, got);
}

#[test]
fn intersection_test_fj_puresize() {
    run_serial_and_parallel(|| intersection_test(PlanStrategy::PureSize));
}

#[test]
fn intersection_test_fj_mincover() {
    run_serial_and_parallel(|| intersection_test(PlanStrategy::MinCover));
}

#[test]
fn intersection_test_gj() {
    run_serial_and_parallel(|| intersection_test(PlanStrategy::Gj));
}

#[test]
fn minimal_ac() {
    run_serial_and_parallel(minimal_ac_inner);
}

fn minimal_ac_inner() {
    let MathEgraph {
        add,
        id_counter,
        mut db,
        ..
    } = basic_math_egraph();
    {
        {
            let mut add_buf = db.new_buffer(add);
            add_buf.stage_insert(&[v(0), v(0), v(1), v(0)]);
            add_buf.stage_insert(&[v(0), v(1), v(2), v(0)]);
            add_buf.stage_insert(&[v(0), v(2), v(3), v(0)]);
        }
        db.merge_all();
        {
            let mut add_buf = db.new_buffer(add);
            add_buf.stage_insert(&[v(1), v(0), v(2), v(1)]);
            add_buf.stage_insert(&[v(1), v(1), v(3), v(1)]);
        }
        db.merge_all();
    }
    let mut rsb = db.new_rule_set();
    let mut add_assoc = rsb.new_rule();
    // Add(x, Add(y, z)) => Add(Add(x, y), z)
    //
    // Add(y, z, i1, t1)
    // Add(x, i1, i2, t2)
    // =>
    // Add(x, y, <res>, cur)
    // Add(<res>, z, i2, cur)

    let x = add_assoc.new_var_named("x");
    let y = add_assoc.new_var_named("y");
    let z = add_assoc.new_var_named("z");
    let i1 = add_assoc.new_var_named("i1");
    let i2 = add_assoc.new_var_named("i2");
    let t1 = add_assoc.new_var_named("t1");
    let t2 = add_assoc.new_var_named("t2");
    add_assoc
        .add_atom(
            add,
            &[y.into(), z.into(), i1.into(), t1.into()],
            &[
                Constraint::GeConst {
                    col: ColumnId::new(3),
                    val: v(0),
                },
                Constraint::LtConst {
                    col: ColumnId::new(3),
                    val: v(1),
                },
            ],
        )
        .unwrap();
    add_assoc
        .add_atom(
            add,
            &[x.into(), i1.into(), i2.into(), t2.into()],
            &[
                Constraint::GeConst {
                    col: ColumnId::new(3),
                    val: v(1),
                },
                Constraint::LtConst {
                    col: ColumnId::new(3),
                    val: v(2),
                },
            ],
        )
        .unwrap();
    let mut rules = add_assoc.build();
    let res = rules
        .lookup_or_insert(
            add,
            &[x.into(), y.into()],
            &[
                WriteVal::IncCounter(id_counter),
                WriteVal::QueryEntry(v(2).into()),
            ],
            ColumnId::new(2),
        )
        .unwrap();
    rules
        .insert(add, &[res.into(), z.into(), i2.into(), v(2).into()])
        .unwrap();
    rules.build();
    let rule_set = rsb.build();

    db.run_rule_set(&rule_set, ReportLevel::TimeOnly);
    let add_table = db.get_table(add);
    let all_add = add_table.all();
    let items = add_table.scan(all_add.as_ref());
    let mut res = Vec::from_iter(items.iter().map(|(_, row)| row.to_vec()));
    res.sort();
    let expected = vec![
        vec![v(0), v(0), v(1), v(0)],
        vec![v(0), v(1), v(2), v(0)],
        vec![v(0), v(2), v(3), v(0)],
        vec![v(1), v(0), v(2), v(1)],
        vec![v(1), v(1), v(3), v(1)],
        vec![v(2), v(0), v(3), v(2)],
    ];
    assert_eq!(res, expected);
}

#[test]
fn ac_gj() {
    run_serial_and_parallel(|| ac_test_inner(PlanStrategy::Gj));
}

#[test]
fn ac_fj_mincover() {
    run_serial_and_parallel(|| ac_test_inner(PlanStrategy::MinCover));
}

#[test]
fn ac_fj_puresize() {
    run_serial_and_parallel(|| ac_test_inner(PlanStrategy::PureSize));
}

fn ac_test_inner(strat: PlanStrategy) {
    // This test is very involved. It reimplements major egglog features on top
    // of this library:
    // 1. rebuilding, including heuristics for incremental vs. nonincremental.
    // 2. seminaive evaluation, using sorted columns.
    // 3. iteration until saturation.
    // It does this using the classic "Assoc / Comm" workload, which is also a
    // solid benchmark for "shallow" / non-selective egglog queries.
    const N: usize = 5;
    let MathEgraph {
        num,
        add,
        id_counter,
        mut db,
        uf,
    } = basic_math_egraph();

    // Add the numbers 1 through 10 to the num table at timestamp 0.
    let mut ids = Vec::new();
    db.base_values_mut().register_type::<i64>();
    for i in 0..N {
        let id = db.inc_counter(id_counter);
        let i = db.base_values().get::<i64>(i as i64);
        ids.push(i);
        db.new_buffer(num)
            .stage_insert(&[i, Value::from_usize(id), Value::new(0)]);
    }

    db.merge_all();

    // construct (0 + ... + N), left-associated, and (N + ... + 0),
    // right-associated. With the assoc and comm rules saturated, these two
    // should be equal.
    let (left_root, right_root) = {
        let mut add_ids = Vec::new();
        let mut prev = ids[0];
        for num in &ids[1..] {
            let id = Value::from_usize(db.inc_counter(id_counter));
            db.new_buffer(add)
                .stage_insert(&[*num, prev, id, Value::new(0)]);
            prev = id;
            add_ids.push(id);
        }
        let left_root = *add_ids.last().unwrap();
        add_ids.clear();
        prev = *ids.last().unwrap();
        for num in ids[0..(N - 1)].iter().rev() {
            let id = Value::from_usize(db.inc_counter(id_counter));
            db.new_buffer(add)
                .stage_insert(&[prev, *num, id, Value::new(0)]);
            prev = id;
            add_ids.push(id);
        }
        let right_root = *add_ids.last().unwrap();
        (left_root, right_root)
    };

    db.merge_all();

    let run_ac_rule = move |db: &mut Database, recent_range: Range<Value>| {
        let old_range = Value::new(0)..recent_range.start;
        let all_range = Value::new(0)..recent_range.end;
        let next_ts = recent_range.end;
        let mut rsb = RuleSetBuilder::new(db);
        for (l_range, r_range) in [
            // NB: this could be all, recent; recent, old
            (all_range, recent_range.clone()),
            (recent_range.clone(), old_range.clone()),
        ] {
            let mut add_assoc = rsb.new_rule();
            add_assoc.set_plan_strategy(strat);
            // Add(x, Add(y, z)) => Add(Add(x, y), z)
            //
            // Add(y, z, i1, t1)
            // Add(x, i1, i2, t2)
            // =>
            // Add(x, y, <res>, cur)
            // Add(<res>, z, i2, cur)

            let x = add_assoc.new_var_named("x");
            let y = add_assoc.new_var_named("y");
            let z = add_assoc.new_var_named("z");
            let i1 = add_assoc.new_var_named("i1");
            let i2 = add_assoc.new_var_named("i2");
            let t1 = add_assoc.new_var_named("t1");
            let t2 = add_assoc.new_var_named("t2");
            add_assoc
                .add_atom(
                    add,
                    &[y.into(), z.into(), i1.into(), t1.into()],
                    &[
                        Constraint::GeConst {
                            col: ColumnId::new(3),
                            val: l_range.start,
                        },
                        Constraint::LtConst {
                            col: ColumnId::new(3),
                            val: l_range.end,
                        },
                    ],
                )
                .unwrap();
            add_assoc
                .add_atom(
                    add,
                    &[x.into(), i1.into(), i2.into(), t2.into()],
                    &[
                        Constraint::GeConst {
                            col: ColumnId::new(3),
                            val: r_range.start,
                        },
                        Constraint::LtConst {
                            col: ColumnId::new(3),
                            val: r_range.end,
                        },
                    ],
                )
                .unwrap();
            let mut rules = add_assoc.build();
            let res = rules
                .lookup_or_insert(
                    add,
                    &[x.into(), y.into()],
                    &[
                        WriteVal::IncCounter(id_counter),
                        WriteVal::QueryEntry(next_ts.into()),
                    ],
                    ColumnId::new(2),
                )
                .unwrap();
            rules
                .insert(add, &[res.into(), z.into(), i2.into(), next_ts.into()])
                .unwrap();
            rules.build();
        }

        // Add(x, y, z, t1),
        // => Add(y, x, z, cur)

        let mut add_comm = rsb.new_rule();
        add_comm.set_plan_strategy(strat);
        let x = add_comm.new_var_named("x");
        let y = add_comm.new_var_named("y");
        let z = add_comm.new_var_named("z");
        let t1 = add_comm.new_var_named("t1");
        // Just look for the current timestamp
        add_comm
            .add_atom(
                add,
                &[x.into(), y.into(), z.into(), t1.into()],
                &[Constraint::EqConst {
                    col: ColumnId::new(3),
                    val: recent_range.start,
                }],
            )
            .unwrap();

        let mut rules = add_comm.build();
        rules
            .insert(add, &[y.into(), x.into(), z.into(), next_ts.into()])
            .unwrap();
        rules.build();
        let rule_set = rsb.build();
        db.run_rule_set(&rule_set, ReportLevel::TimeOnly)
    };

    let rebuild = |db: &mut Database, cur_ts: Value| -> (Value, bool) {
        let next_ts = Value::new(cur_ts.rep() + 1);
        let mut rsb = db.new_rule_set();
        let num_rebuild = |rsb: &mut RuleSetBuilder, cur_ts: Value, next_ts: Value| {
            // num(x, id, t1), displaced(id, id2, t2)
            // =>
            // insert num(x, id2, cur) // rebuilding always picks the new value.
            // Compare the size of the num table to the displaced ids at the current timestamp:
            let num_size = rsb.estimate_size(num, None);
            let uf_size = rsb.estimate_size(
                uf,
                Some(Constraint::EqConst {
                    col: ColumnId::new(2),
                    val: cur_ts,
                }),
            );
            let mut num_rebuild = rsb.new_rule();
            num_rebuild.set_plan_strategy(strat);
            if incremental_rebuild(uf_size, num_size) {
                // nonincremental:
                //  num(x, id, t1) =>
                //  num(x, id', t1) where id' is canonical
                let x = num_rebuild.new_var_named("x");
                let id = num_rebuild.new_var_named("id");
                let t1 = num_rebuild.new_var_named("t1");
                num_rebuild
                    .add_atom(num, &[x.into(), id.into(), t1.into()], &[])
                    .unwrap();
                let mut rules = num_rebuild.build();
                let id_canon = rules
                    .lookup_with_default(uf, &[id.into()], id.into(), ColumnId::new(1))
                    .unwrap();
                rules.assert_ne(id.into(), id_canon.into()).unwrap();
                rules
                    .insert(num, &[x.into(), id_canon.into(), next_ts.into()])
                    .unwrap();
                rules.build();
            } else {
                let x = num_rebuild.new_var_named("x");
                let id = num_rebuild.new_var_named("id");
                let t1 = num_rebuild.new_var_named("t1");
                let id_new = num_rebuild.new_var_named("id_new");
                let t2 = num_rebuild.new_var_named("t2");
                num_rebuild
                    .add_atom(num, &[x.into(), id.into(), t1.into()], &[])
                    .unwrap();
                num_rebuild
                    .add_atom(
                        uf,
                        &[id.into(), id_new.into(), t2.into()],
                        &[Constraint::EqConst {
                            col: ColumnId::new(2),
                            val: cur_ts,
                        }],
                    )
                    .unwrap();
                let mut rules = num_rebuild.build();
                rules
                    .insert(num, &[x.into(), id_new.into(), next_ts.into()])
                    .unwrap();
                rules.build();
            }
        };
        num_rebuild(&mut rsb, cur_ts, next_ts);
        let mut changed = false;
        let add_size = rsb.estimate_size(add, None);
        let uf_size = rsb.estimate_size(
            uf,
            Some(Constraint::EqConst {
                col: ColumnId::new(2),
                val: cur_ts,
            }),
        );
        if incremental_rebuild(uf_size, add_size) {
            let mut add_rebuild_id = rsb.new_rule();
            add_rebuild_id.set_plan_strategy(strat);
            let x = add_rebuild_id.new_var_named("x");
            let y = add_rebuild_id.new_var_named("y");
            let id = add_rebuild_id.new_var_named("id");
            let t1 = add_rebuild_id.new_var_named("t1");
            let id_new = add_rebuild_id.new_var_named("id_new");
            let t2 = add_rebuild_id.new_var_named("t2");
            add_rebuild_id
                .add_atom(add, &[x.into(), y.into(), id.into(), t1.into()], &[])
                .unwrap();
            add_rebuild_id
                .add_atom(
                    uf,
                    &[id.into(), id_new.into(), t2.into()],
                    &[Constraint::EqConst {
                        col: ColumnId::new(2),
                        val: cur_ts,
                    }],
                )
                .unwrap();
            let mut rules = add_rebuild_id.build();
            let x_new = rules
                .lookup_with_default(uf, &[x.into()], x.into(), ColumnId::new(1))
                .unwrap();
            let y_new = rules
                .lookup_with_default(uf, &[y.into()], y.into(), ColumnId::new(1))
                .unwrap();
            rules.remove(add, &[x.into(), y.into()]).unwrap();
            rules
                .insert(
                    add,
                    &[x_new.into(), y_new.into(), id_new.into(), next_ts.into()],
                )
                .unwrap();
            rules.build();
            let rs = rsb.build();
            changed |= db.run_rule_set(&rs, ReportLevel::TimeOnly).changed;
            let mut rsb = db.new_rule_set();
            num_rebuild(&mut rsb, cur_ts, next_ts);
            let mut add_rebuild_l = rsb.new_rule();
            add_rebuild_l.set_plan_strategy(strat);
            let x = add_rebuild_l.new_var_named("x");
            let y = add_rebuild_l.new_var_named("y");
            let id = add_rebuild_l.new_var_named("id");
            let t1 = add_rebuild_l.new_var_named("t1");
            let x_new = add_rebuild_l.new_var_named("x_new");
            let t2 = add_rebuild_l.new_var_named("t2");
            add_rebuild_l
                .add_atom(add, &[x.into(), y.into(), id.into(), t1.into()], &[])
                .unwrap();
            add_rebuild_l
                .add_atom(
                    uf,
                    &[x.into(), x_new.into(), t2.into()],
                    &[Constraint::EqConst {
                        col: ColumnId::new(2),
                        val: cur_ts,
                    }],
                )
                .unwrap();
            let mut rules = add_rebuild_l.build();
            let y_new = rules
                .lookup_with_default(uf, &[y.into()], y.into(), ColumnId::new(1))
                .unwrap();
            let id_new = rules
                .lookup_with_default(uf, &[id.into()], id.into(), ColumnId::new(1))
                .unwrap();
            rules.remove(add, &[x.into(), y.into()]).unwrap();
            rules
                .insert(
                    add,
                    &[x_new.into(), y_new.into(), id_new.into(), next_ts.into()],
                )
                .unwrap();
            rules.build();

            let rs = rsb.build();
            changed |= db.run_rule_set(&rs, ReportLevel::TimeOnly).changed;
            let mut rsb = db.new_rule_set();
            num_rebuild(&mut rsb, cur_ts, next_ts);
            let mut add_rebuild_r = rsb.new_rule();
            add_rebuild_r.set_plan_strategy(strat);
            let x = add_rebuild_r.new_var_named("x");
            let y = add_rebuild_r.new_var_named("y");
            let id = add_rebuild_r.new_var_named("id");
            let t1 = add_rebuild_r.new_var_named("t1");
            let y_new = add_rebuild_r.new_var_named("y_new");
            let t2 = add_rebuild_r.new_var_named("t2");
            add_rebuild_r
                .add_atom(add, &[x.into(), y.into(), id.into(), t1.into()], &[])
                .unwrap();
            add_rebuild_r
                .add_atom(
                    uf,
                    &[y.into(), y_new.into(), t2.into()],
                    &[Constraint::EqConst {
                        col: ColumnId::new(2),
                        val: cur_ts,
                    }],
                )
                .unwrap();
            let mut rules = add_rebuild_r.build();
            let x_new = rules
                .lookup_with_default(uf, &[x.into()], x.into(), ColumnId::new(1))
                .unwrap();
            let id_new = rules
                .lookup_with_default(uf, &[id.into()], id.into(), ColumnId::new(1))
                .unwrap();
            rules.remove(add, &[x.into(), y.into()]).unwrap();
            rules
                .insert(
                    add,
                    &[x_new.into(), y_new.into(), id_new.into(), next_ts.into()],
                )
                .unwrap();
            rules.build();
            let rs = rsb.build();
            changed |= db.run_rule_set(&rs, ReportLevel::TimeOnly).changed;
        } else {
            // nonincremental. Just run one rule and recanonicalize everything.
            // add(x, y, id, t1) =>
            //   let x' = lookup_with_default(uf, x, x')
            //   let y' = lookup_with_default(uf, y, y')
            //   let id' = lookup_with_default(uf, id, id')
            //   assertanyne([x, y, id], [x', y', id'])
            //   delete add(x, y)
            //   insert add(x', y', id', cur)
            let mut rebuild = rsb.new_rule();
            rebuild.set_plan_strategy(strat);
            let x = rebuild.new_var_named("x");
            let y = rebuild.new_var_named("y");
            let id = rebuild.new_var_named("id");
            let t1 = rebuild.new_var_named("t1");
            rebuild
                .add_atom(add, &[x.into(), y.into(), id.into(), t1.into()], &[])
                .unwrap();
            let mut rules = rebuild.build();
            let x_canon = rules
                .lookup_with_default(uf, &[x.into()], x.into(), ColumnId::new(1))
                .unwrap();
            let y_canon = rules
                .lookup_with_default(uf, &[y.into()], y.into(), ColumnId::new(1))
                .unwrap();
            let id_canon = rules
                .lookup_with_default(uf, &[id.into()], id.into(), ColumnId::new(1))
                .unwrap();
            rules
                .assert_any_ne(
                    &[x.into(), y.into(), id.into()],
                    &[x_canon.into(), y_canon.into(), id_canon.into()],
                )
                .unwrap();
            rules.remove(add, &[x.into(), y.into()]).unwrap();
            rules
                .insert(
                    add,
                    &[
                        x_canon.into(),
                        y_canon.into(),
                        id_canon.into(),
                        next_ts.into(),
                    ],
                )
                .unwrap();
            rules.build();
            let rs = rsb.build();
            changed |= db.run_rule_set(&rs, ReportLevel::TimeOnly).changed;
        }
        (next_ts, changed)
    };
    let mut cur_ts = Value::new(0);
    let mut next_ts = Value::new(1);
    loop {
        if !run_ac_rule(&mut db, cur_ts..next_ts).changed {
            break;
        }
        let start = next_ts;
        let mut new_ids_at = start;
        let mut changed = true;
        while changed {
            let (next_ts, rebuild_changed) = rebuild(&mut db, new_ids_at);
            new_ids_at = next_ts;
            changed = rebuild_changed;
        }
        cur_ts = start;
        next_ts = Value::new(new_ids_at.rep() + 1);
    }
    let uf_table = db.get_table(uf);
    let l_canon = uf_table
        .get_row(&[left_root])
        .map(|row| row.vals[1])
        .unwrap_or(left_root);
    let r_canon = uf_table
        .get_row(&[right_root])
        .map(|row| row.vals[1])
        .unwrap_or(right_root);
    assert_eq!(l_canon, r_canon);
}

struct MathEgraph {
    uf: TableId,
    num: TableId,
    add: TableId,
    id_counter: CounterId,
    db: Database,
}

fn basic_math_egraph() -> MathEgraph {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let num_impl = SortedWritesTable::new(
        1,
        3,
        Some(ColumnId::new(2)),
        vec![],
        Box::new(move |state, a, b, res| {
            if a[1] != b[1] {
                // Mark the two ids as equal. Picking b[1] as the 'presumed winner'
                state.stage_insert(uf, &[a[1], b[1], b[2]]);
                res.extend_from_slice(b);
                true
            } else {
                false
            }
        }),
    );

    let id_counter = db.add_counter();
    let num = db.add_table(num_impl, iter::once(uf), iter::empty());
    let add_impl = SortedWritesTable::new(
        2,
        4,
        Some(ColumnId::new(3)),
        vec![],
        Box::new(move |state, a, b, res| {
            // Capture a backtrace as a string
            if a[2] != b[2] {
                // Mark the two ids as equal. Picking b[2] as the 'presumed winner'
                state.stage_insert(uf, &[a[2], b[2], b[3]]);
                res.extend_from_slice(b);
                true
            } else {
                false
            }
        }),
    );

    let add = db.add_table(add_impl, iter::once(uf), iter::empty());

    MathEgraph {
        uf,
        num,
        add,
        id_counter,
        db,
    }
}

fn incremental_rebuild(uf_size: usize, table_size: usize) -> bool {
    uf_size / 4 > table_size
}

#[test]
fn lookup_with_fallback_partial_success() {
    run_serial_and_parallel(lookup_with_fallback_partial_success_inner);
}

fn lookup_with_fallback_partial_success_inner() {
    // Insert (f 1) (f 2), (g 1) (g 3) (g 4).
    // Run a query that iterates over g, binding x to 1, 3, 4.
    // Insert (h (lookup f x, with fallback assert-even))
    // Should get h 1, h 4
    let mut db = Database::default();
    let [f, g, h] = (0..3)
        .map(|_| {
            db.add_table(
                SortedWritesTable::new(
                    1,
                    2,
                    None,
                    vec![],
                    Box::new(move |_, a, b, _| {
                        if a[0] != b[0] {
                            panic!("merge not supported")
                        } else {
                            false
                        }
                    }),
                ),
                iter::empty(),
                iter::empty(),
            )
        })
        .collect::<Vec<_>>()[..]
    else {
        unreachable!()
    };

    {
        let mut buf = db.new_buffer(f);
        buf.stage_insert(&[v(1), v(0)]);
        buf.stage_insert(&[v(2), v(0)]);
    }
    {
        let mut buf = db.new_buffer(g);
        buf.stage_insert(&[v(1), v(0)]);
        buf.stage_insert(&[v(3), v(0)]);
        buf.stage_insert(&[v(4), v(0)]);
        buf.stage_insert(&[v(5), v(0)]);
    }

    db.merge_all();
    let log = Arc::new(Mutex::new(Vec::new()));
    let log_vals = {
        let inner = log.clone();
        db.add_external_function(Box::new(make_external_func(move |_, args| {
            let [x] = args else { panic!() };
            inner.lock().unwrap().push(*x);
            Some(*x)
        })))
    };
    let assert_even = db.add_external_function(Box::new(make_external_func(|_, args| {
        let [x] = args else { panic!() };
        if x.rep().is_multiple_of(2) {
            Some(*x)
        } else {
            None
        }
    })));

    let mut rsb = RuleSetBuilder::new(&mut db);
    let mut query = rsb.new_rule();
    let x = query.new_var_named("x");
    let y = query.new_var_named("y");
    query.add_atom(g, &[x.into(), y.into()], &[]).unwrap();
    let mut rb = query.build();
    let res = rb
        .lookup_with_fallback(f, &[x.into()], ColumnId::new(0), assert_even, &[x.into()])
        .unwrap();
    rb.call_external(log_vals, &[x.into()]).unwrap();
    rb.insert(h, &[res.into(), y.into()]).unwrap();
    rb.build();
    let rs = rsb.build();
    assert!(db.run_rule_set(&rs, ReportLevel::TimeOnly).changed);

    let h = db.get_table(h);
    let all = h.all();
    let mut h_contents = h
        .scan(all.as_ref())
        .iter()
        .map(|(_, row)| row.to_vec())
        .collect::<Vec<_>>();
    h_contents.sort();
    assert_eq!(h_contents, vec![vec![v(1), v(0)], vec![v(4), v(0)],]);
    let sorted_log = {
        let mut log = log.lock().unwrap().clone();
        log.sort();
        log
    };
    assert_eq!(sorted_log, vec![v(1), v(4)]);
}

#[test]
fn call_external_with_fallback() {
    run_serial_and_parallel(call_external_with_fallback_inner);
}

fn call_external_with_fallback_inner() {
    // Insert (f 1) (f 2) (f 3) (f 5).
    // Iterate over f, binding x to 1, 2, 3.
    // Have two external functions:
    // 1. assert_even, which returns None for odd numbers.
    // 2. inc, which increments the input value and only fails on the number 5
    // Insert (h (call assert_even x, with fallback inc x))
    // We should get h 2, h 4.
    let mut db = Database::default();
    let [f, h] = (0..2)
        .map(|_| {
            db.add_table(
                SortedWritesTable::new(
                    1,
                    2,
                    None,
                    vec![],
                    Box::new(move |_, a, b, _| {
                        if a[0] != b[0] {
                            panic!("merge not supported")
                        } else {
                            false
                        }
                    }),
                ),
                iter::empty(),
                iter::empty(),
            )
        })
        .collect::<Vec<_>>()[..]
    else {
        unreachable!()
    };

    {
        let mut buf = db.new_buffer(f);
        buf.stage_insert(&[v(1), v(0)]);
        buf.stage_insert(&[v(2), v(0)]);
        buf.stage_insert(&[v(3), v(0)]);
        buf.stage_insert(&[v(5), v(0)]);
    }
    db.merge_all();
    let assert_even = db.add_external_function(Box::new(make_external_func(|_, args| {
        let [x] = args else { panic!() };
        if x.rep().is_multiple_of(2) {
            Some(*x)
        } else {
            None
        }
    })));

    let inc = db.add_external_function(Box::new(make_external_func(|_, args| {
        let [x] = args else { panic!() };
        if x.rep() == 5 { None } else { Some(x.inc()) }
    })));

    let mut rsb = RuleSetBuilder::new(&mut db);
    let mut query = rsb.new_rule();
    let x = query.new_var_named("x");
    let y = query.new_var_named("y");
    query.add_atom(f, &[x.into(), y.into()], &[]).unwrap();
    let mut rb = query.build();
    let res = rb
        .call_external_with_fallback(assert_even, &[x.into()], inc, &[x.into()])
        .unwrap();
    rb.insert(h, &[res.into(), y.into()]).unwrap();
    rb.build();
    let rs = rsb.build();
    assert!(db.run_rule_set(&rs, ReportLevel::TimeOnly).changed);

    let h = db.get_table(h);
    let all = h.all();
    let mut h_contents = h
        .scan(all.as_ref())
        .iter()
        .map(|(_, row)| row.to_vec())
        .collect::<Vec<_>>();
    h_contents.sort();
    assert_eq!(h_contents, vec![vec![v(2), v(0)], vec![v(4), v(0)],]);
}

#[test]
fn early_stop() {
    run_serial_and_parallel(early_stop_inner);
}

fn early_stop_inner() {
    let mut db = Database::default();

    // Create a table with 1M rows.
    let data_table = db.add_table(
        SortedWritesTable::new(1, 2, None, vec![], Box::new(|_, _, _, _| false)),
        iter::empty(),
        iter::empty(),
    );

    {
        // Populate with 0.5M rows.
        let mut buf = db.new_buffer(data_table);
        for i in 0..500_000 {
            buf.stage_insert(&[Value::from_usize(i), Value::from_usize(i)]);
        }
    }
    db.merge_all();

    // External function that triggers early stop after 1000 calls.
    let call_count = Arc::new(Mutex::new(0usize));
    let call_count_clone = call_count.clone();
    let stop_trigger =
        db.add_external_function(Box::new(make_external_func(move |exec_state, args| {
            let mut count = call_count_clone.lock().unwrap();
            *count += 1;

            if *count >= 1000 {
                exec_state.trigger_early_stop();
            }

            let [x] = args else { panic!() };
            Some(*x)
        })));

    // Build a rule that scans the table and calls the external function.
    let mut rsb = RuleSetBuilder::new(&mut db);
    let mut query = rsb.new_rule();
    let x = query.new_var_named("x");
    let y = query.new_var_named("y");
    query
        .add_atom(data_table, &[x.into(), y.into()], &[])
        .unwrap();
    let mut rb = query.build();
    let _ = rb.call_external(stop_trigger, &[x.into()]).unwrap();
    rb.build_with_description("early_stop_test");
    let rs = rsb.build();

    let report = db.run_rule_set(&rs, ReportLevel::TimeOnly);

    let matches = report.num_matches("early_stop_test");

    // NB: 100K is very loose: this test doesn't appear to flake even with 10K as the upper limit.
    // This is mostly just there to avoid truly unlikely race conditions where there are a huge
    // number of matches in flight at once.
    assert!(
        matches < 100_000,
        "Expected much fewer than 10k matches due to early stopping, got {}, (call_count={})",
        matches,
        call_count.lock().unwrap(),
    );
    assert!(
        matches >= 1000,
        "Expected at least 1000 matches before stopping, got {} (call_count={})",
        matches,
        call_count.lock().unwrap(),
    );

    let final_count = *call_count.lock().unwrap();
    assert!(
        final_count >= 1000,
        "External function called {final_count} times, should be at least 1000"
    );
    assert!(
        final_count < 100_000,
        "External function called {final_count} times, should be much less than 10k"
    );
}

#[test]
#[should_panic(expected = "source capture actions require an empty query")]
fn source_capture_actions_reject_query_derived_facts() {
    let mut db = Database::default();
    let table = db.add_table(
        SortedWritesTable::new(1, 1, None, vec![], Box::new(|_, _, _, _| false)),
        iter::empty(),
        iter::empty(),
    );
    db.try_enable_trace().unwrap();
    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let value = query.new_var_named("value");
    query.add_atom(table, &[value.into()], &[]).unwrap();
    query
        .build()
        .try_build_source_with_capture("invalid-query-source", SourceRef::Synthetic(402))
        .unwrap();
}

#[test]
fn check_trace_keep_distinct_premise_terms_for_the_same_runtime_equality_value() {
    let mut db = Database::default();
    let relation = || {
        SortedWritesTable::new(
            2,
            2,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "check premise rows are immutable");
                false
            }),
        )
    };
    let left_table = db.add_table(relation(), iter::empty(), iter::empty());
    let right_table = db.add_table(relation(), iter::empty(), iter::empty());
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let trace = db.try_enable_trace().unwrap();
    let sort = ReplaySortId::new(401);
    trace
        .register_table_layout(left_table, &[Some(sort), Some(sort)])
        .unwrap();
    trace
        .register_table_layout(right_table, &[Some(sort), Some(sort)])
        .unwrap();
    let join = Value::new(1);
    let first_left = Value::new(20);
    let second_left = Value::new(30);
    let right = Value::new(10);
    for raw in [join, first_left, second_left, right] {
        trace.intern_literal(sort, ReplayLiteral::I64(raw.index() as i64), raw);
    }
    let term = |raw| trace.lookup_term(sort, raw).unwrap();
    // Commit the lexicographically smaller FactId on the row that scans
    // second. A recorder that inspects only the first lane will choose the
    // wrong successful match.
    for (source, table, row) in [
        (411, left_table, [second_left, join]),
        (412, right_table, [join, right]),
    ] {
        db.stage_source_row(
            table,
            &row,
            &[term(row[0]), term(row[1])],
            SourceRef::Synthetic(source),
        )
        .unwrap();
    }
    assert!(db.merge_all());
    db.finalize_trace_wave();
    let second_left_fact = committed_fact_id_for_key(&db, left_table, &[second_left, join]);
    let right_fact = committed_fact_id_for_key(&db, right_table, &[join, right]);
    db.stage_source_row(
        left_table,
        &[first_left, join],
        &[term(first_left), term(join)],
        SourceRef::Synthetic(410),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_trace_wave();
    let first_left_fact = committed_fact_id_for_key(&db, left_table, &[first_left, join]);
    assert!(
        second_left_fact < first_left_fact,
        "test requires FactId order to oppose table scan order"
    );

    db.set_trace_wave(Wave::new(1));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&trace, 500, Wave::new(1)),
        sort,
        first_left,
        right,
        Value::new(1),
    );
    assert!(db.merge_all());
    db.set_trace_wave(Wave::new(2));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&trace, 501, Wave::new(2)),
        sort,
        second_left,
        right,
        Value::new(2),
    );
    assert!(db.merge_all());
    db.set_trace_wave(Wave::new(3));

    let mut rules = RuleSetBuilder::new(&mut db);
    for check in [9, 4] {
        let mut query = rules.new_rule();
        let left = query.new_var_named("left");
        let shared = query.new_var_named("shared");
        let right = query.new_var_named("right");
        let left_atom = query
            .add_atom(left_table, &[left.into(), shared.into()], &[])
            .unwrap();
        let right_atom = query
            .add_atom(right_table, &[shared.into(), right.into()], &[])
            .unwrap();
        let mut action = query.build();
        action.assert_eq(left.into(), left.into());
        action
            .try_build_check_with_capture(
                format!("check-{check}"),
                CriterionCaptureSpec::new(check, [left_atom, right_atom]).with_equalities([(
                    CriterionEndpointSource::premise(0, 0, right.into()),
                    CriterionEndpointSource::premise(1, 1, right.into()),
                )]),
            )
            .unwrap();
    }
    let rules = rules.build();
    assert!(!db.run_rule_set(&rules, ReportLevel::TimeOnly).changed);
    db.finalize_trace_wave();

    trace
        .with_view(|view| {
            let roots = view.check_roots();
            assert_eq!(
                roots.iter().map(|root| root.check).collect::<Vec<_>>(),
                [4, 9],
                "root order must depend only on stable check IDs"
            );
            for root in &roots {
                assert_eq!(root.wave, Wave::new(3));
                assert_eq!(root.premises.as_ref(), &[second_left_fact, right_fact]);
                assert_eq!(root.as_of_edges, crate::EdgeHorizon::new(2));
                assert_eq!(
                    root.equalities.as_ref(),
                    &[crate::CriterionEquality {
                        endpoints: (
                            crate::EqualityEndpoint {
                                sort,
                                term: term(second_left),
                                raw: second_left,
                            },
                            crate::EqualityEndpoint {
                                sort,
                                term: term(right),
                                raw: right,
                            },
                        ),
                        occurrences: (
                            crate::CriterionEndpointOccurrence::FactCell(crate::FactCellRef {
                                fact: second_left_fact,
                                column: ColumnId::new(0),
                            }),
                            crate::CriterionEndpointOccurrence::FactCell(crate::FactCellRef {
                                fact: right_fact,
                                column: ColumnId::new(1),
                            }),
                        ),
                    }]
                );
                assert_ne!(
                    root.equalities[0].endpoints.0.raw, root.equalities[0].endpoints.1.raw,
                    "the root keeps each premise's immutable creation occurrence"
                );
                assert_ne!(
                    root.equalities[0].endpoints.0.term, root.equalities[0].endpoints.1.term,
                    "equal runtime values must retain their distinct premise-owned syntax"
                );
            }
            assert_eq!(roots, view.check_roots());
            assert_eq!(
                view.totals().firings,
                2,
                "only the two effective equality-producing rules should have matches"
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn late_fact_rekey_attachment_is_visible_only_at_the_check_position() {
    late_fact_rekey_attachment_case(false);
}

#[test]
fn late_fact_rekey_attachment_is_independent_of_equality_endpoint_order() {
    late_fact_rekey_attachment_case(true);
}

fn late_fact_rekey_attachment_case(reverse_equality_endpoints: bool) {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let rebuilt = db.add_table(
        SortedWritesTable::new(
            1,
            2,
            Some(ColumnId::new(1)),
            vec![ColumnId::new(0)],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "the chronology canary performs a pure rekey");
                false
            }),
        ),
        iter::once(uf),
        iter::empty(),
    );
    let trace = db.try_enable_trace().unwrap();
    let sort = ReplaySortId::new(7900);
    trace
        .register_table_layout(rebuilt, &[Some(sort), None])
        .unwrap();
    trace.register_table_key_columns(rebuilt, 1).unwrap();
    trace
        .register_table_kind(rebuilt, ReplayTableKind::ValueFunction)
        .unwrap();
    let a = Value::new(20);
    let c = Value::new(10);
    let ta = trace.intern_literal(sort, ReplayLiteral::I64(1), a);
    let tb = trace.intern_literal(sort, ReplayLiteral::I64(2), Value::new(200));
    let tc = trace.intern_literal(sort, ReplayLiteral::I64(3), c);
    let site = |term| {
        trace.register_term_origin(TermOriginSpec {
            sort,
            term: Arc::new(TermTemplate::Static { term }),
        })
    };
    let wave = Wave::new(1);
    db.set_trace_wave(wave);
    let (proposal_left, proposal_left_term, proposal_right, proposal_right_term) =
        if reverse_equality_endpoints {
            (c, tc, a, ta)
        } else {
            (a, ta, c, tc)
        };
    let equality = trace
        .typed_equality_proposal_from_sites(
            wave,
            sort,
            proposal_left,
            site(proposal_left_term),
            proposal_right,
            site(proposal_right_term),
        )
        .unwrap();
    {
        let mut buffer = db.new_buffer(uf);
        buffer.stage_typed_union(
            &[proposal_left, proposal_right, Value::new(1)],
            empty_rule_cause(&trace, 7900, wave),
            equality,
        );
    }
    assert!(db.merge_all());

    db.stage_source_row(
        rebuilt,
        &[a, Value::new(0)],
        &[tb, crate::ReplayTermId::MISSING],
        SourceRef::Synthetic(7900),
    )
    .unwrap();
    assert!(db.merge_all());
    let fact = committed_fact_id(&db, rebuilt, a);
    assert!(db.apply_rebuild(uf, &[rebuilt], Value::new(2)));
    assert_eq!(committed_fact_id(&db, rebuilt, c), fact);

    let cutoff = trace.equality_edge_count().unwrap();
    let left = crate::EqualityEndpoint {
        sort,
        term: tb,
        raw: c,
    };
    let right = crate::EqualityEndpoint {
        sort,
        term: tc,
        raw: c,
    };
    let equality = crate::CriterionEquality {
        endpoints: (left, right),
        occurrences: (
            crate::CriterionEndpointOccurrence::FactCell(crate::FactCellRef {
                fact,
                column: ColumnId::new(0),
            }),
            crate::CriterionEndpointOccurrence::Current,
        ),
    };
    trace
        .record_check_root(7900, wave, &[fact], &[equality], cutoff)
        .unwrap();
    trace
        .record_check_root(7900, Wave::new(99), &[fact], &[equality], cutoff)
        .unwrap();
    db.finalize_trace_wave();

    trace
        .with_view(|view| {
            let equality = view.applied_equality(crate::AppliedEqualityId::new(1))?;
            let fact_record = view.fact(fact)?;
            let root = view.check_root(7900)?;
            let crate::CauseRef::Cause(source) = fact_record.cause else {
                panic!("expected a source cause")
            };
            assert!(matches!(
                view.cause(source)?,
                crate::RawCause::Source(SourceRef::Synthetic(7900))
            ));
            assert_eq!(equality.wave, wave);
            assert_eq!(
                root.wave, wave,
                "a later successful witness must not replace the first native check root"
            );
            assert!(equality.position < fact_record.position);
            assert!(fact_record.position < root.position);
            let occurrence = crate::FactCellRef {
                fact,
                column: ColumnId::new(0),
            };
            let created = view.fact_cell_at(occurrence, fact_record.position)?;
            assert_eq!((created.created.term, created.created.raw), (tb, a));
            assert_eq!(created.endpoint, created.created);
            assert!(created.rekeys.is_empty());
            let rekeys = test_rekeys(view)?;
            let [rekey] = rekeys.as_slice() else {
                panic!("expected one rekey landmark")
            };
            let rekey_position = rekey.position;
            assert_eq!((rekey.fact, rekey.wave), (fact, wave));
            assert_eq!(rekey.as_of_edges, cutoff);
            assert_eq!(rekey.equalities.len(), 1);
            assert!(fact_record.position < rekey_position && rekey_position < root.position);
            let current = view.fact_cell_at(occurrence, root.position)?;
            assert_eq!((current.endpoint.term, current.endpoint.raw), (tb, c));
            assert_eq!(current.rekeys.as_ref(), &[rekey_position]);
            let support =
                view.explain_fact_endpoint_support_at(occurrence, right, cutoff, root.position)?;
            assert_eq!(
                support.applied.as_ref(),
                &[crate::AppliedEqualityId::new(1)]
            );
            assert_eq!(support.facts.as_ref(), &[fact]);
            assert_eq!(support.rekeys.as_ref(), &[rekey_position]);
            assert!(
                view.explain_equality_support_at(
                    left,
                    right,
                    crate::EdgeHorizon::new(0),
                    root.position,
                )
                .is_err(),
                "a mismatched applied-edge high-water mark must fail closed"
            );
            Ok(())
        })
        .unwrap();
}
#[test]
fn effective_constructor_rebuild_inherits_prior_terms_over_competing_alias() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let constructor = db.add_table(
        SortedWritesTable::new(
            1,
            3,
            Some(ColumnId::new(2)),
            vec![ColumnId::new(0)],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "constructor rebuild must not collide");
                false
            }),
        ),
        iter::once(uf),
        iter::empty(),
    );
    let trace = db.try_enable_trace().unwrap();
    let child_sort = ReplaySortId::new(791);
    let result_sort = ReplaySortId::new(792);
    let op = ReplayOpId::new(791);
    trace
        .register_table_layout(constructor, &[Some(child_sort), Some(result_sort), None])
        .unwrap();
    trace
        .register_table_constructor(
            constructor,
            ReplayConstructorSpec::new(result_sort, op, [child_sort]),
        )
        .unwrap();

    let wrong_child = Value::new(7910);
    let exact_child = Value::new(7911);
    let canonical_child = Value::new(7909);
    let output = Value::new(7920);
    let wrong_child_term = trace.intern_literal(child_sort, ReplayLiteral::I64(7910), wrong_child);
    let exact_child_term = trace.intern_literal(child_sort, ReplayLiteral::I64(7911), exact_child);
    trace.intern_literal(child_sort, ReplayLiteral::I64(7909), canonical_child);
    let wrong_call = trace
        .intern_call(result_sort, op, &[wrong_child_term], output)
        .unwrap();
    let exact_call = trace
        .intern_call(result_sort, op, &[exact_child_term], output)
        .unwrap();
    assert_ne!(wrong_call, exact_call);
    assert_eq!(
        trace.lookup_term(result_sort, output),
        Some(wrong_call),
        "the global reverse map must retain the deliberately competing alias"
    );

    let exact_terms = [exact_child_term, exact_call, crate::ReplayTermId::MISSING];
    db.stage_source_row(
        constructor,
        &[exact_child, output, Value::new(0)],
        &exact_terms,
        SourceRef::Synthetic(791),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_trace_wave();
    let prior_fact = committed_fact_id(&db, constructor, exact_child);

    db.set_trace_wave(Wave::new(1));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&trace, 791, Wave::new(1)),
        child_sort,
        exact_child,
        canonical_child,
        Value::new(1),
    );
    assert!(db.merge_all());
    db.set_trace_wave(Wave::new(2));
    assert!(db.apply_rebuild(uf, &[constructor], Value::new(2)));
    db.finalize_trace_wave();

    let rebuilt_fact = committed_fact_id(&db, constructor, canonical_child);
    assert_eq!(rebuilt_fact, prior_fact);
    trace
        .with_view(|view| {
            assert_eq!(
                view.fact_terms(rebuilt_fact)?.as_ref(),
                exact_terms.as_slice()
            );
            let crate::CauseRef::Cause(source) = view.fact(rebuilt_fact)?.cause else {
                panic!("pure rekeying replaced the source creator")
            };
            assert!(matches!(
                view.cause(source)?,
                crate::RawCause::Source(SourceRef::Synthetic(791))
            ));
            let equality = view.applied_equality(crate::AppliedEqualityId::new(1))?;
            let rekey = view.rekey_at(crate::HistoryPosition::new(equality.position.get() + 1))?;
            assert_eq!(rekey.fact, prior_fact);
            assert_eq!(rekey.outcome, crate::provenance::RekeyOutcome::Moved);
            assert_eq!(rekey.equalities.len(), 1);
            assert_eq!(rekey.equalities[0].left.raw, exact_child);
            assert_eq!(rekey.equalities[0].right.raw, canonical_child);
            Ok(())
        })
        .unwrap();
}

#[test]
fn forged_direct_rule_match_fails_before_native_union() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let trace = db.try_enable_trace().unwrap();
    let sort = ReplaySortId::new(901);
    let left = Value::new(9010);
    let right = Value::new(9011);
    trace.intern_literal(sort, ReplayLiteral::I64(9010), left);
    trace.intern_literal(sort, ReplayLiteral::I64(9011), right);

    let wave = Wave::new(1);
    db.set_trace_wave(wave);
    let proposal = trace
        .typed_equality_proposal(wave, sort, left, right)
        .unwrap();
    {
        let mut buffer = db.new_buffer(uf);
        buffer.stage_typed_union(
            &[left, right, Value::new(1)],
            crate::CauseRef::Rule(crate::FiringId::new(999)),
            proposal,
        );
    }

    let failed = catch_unwind(AssertUnwindSafe(|| db.merge_all()));
    assert!(
        failed.is_err(),
        "a direct FiringId without a durable observation must fail preflight"
    );
    assert_eq!(native_uf_root(&db, uf, left), left);
    assert_eq!(native_uf_root(&db, uf, right), right);
}

#[test]
fn direct_rule_match_cannot_cross_a_causal_wave() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let trace = db.try_enable_trace().unwrap();
    let sort = ReplaySortId::new(902);
    let left = Value::new(9020);
    let right = Value::new(9021);
    trace.intern_literal(sort, ReplayLiteral::I64(9020), left);
    trace.intern_literal(sort, ReplayLiteral::I64(9021), right);

    let first_wave = Wave::new(1);
    db.set_trace_wave(first_wave);
    let stale = empty_rule_cause(&trace, 902, first_wave);
    db.finalize_trace_wave();

    let second_wave = Wave::new(2);
    db.set_trace_wave(second_wave);
    let proposal = trace
        .typed_equality_proposal(second_wave, sort, left, right)
        .unwrap();
    {
        let mut buffer = db.new_buffer(uf);
        buffer.stage_typed_union(&[left, right, Value::new(2)], stale, proposal);
    }

    let failed = catch_unwind(AssertUnwindSafe(|| db.merge_all()));
    assert!(
        failed.is_err(),
        "a direct FiringId from an earlier wave must fail preflight"
    );
    assert_eq!(native_uf_root(&db, uf, left), left);
    assert_eq!(native_uf_root(&db, uf, right), right);
}

#[test]
fn pending_rule_cause_cannot_cross_capture_arenas() {
    let foreign = Trace::default();
    let wave = Wave::new(1);
    let observed = foreign.pending_firing_batch(903, wave, 0, &[], &[], 1);
    let foreign_cause =
        crate::DeferredEqualityCause::pending(foreign.pending_firing_cause(&observed, 0));

    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let trace = db.try_enable_trace().unwrap();
    let sort = ReplaySortId::new(903);
    let left = Value::new(9030);
    let right = Value::new(9031);
    trace.intern_literal(sort, ReplayLiteral::I64(9030), left);
    trace.intern_literal(sort, ReplayLiteral::I64(9031), right);
    db.set_trace_wave(wave);
    let proposal = trace
        .typed_equality_proposal(wave, sort, left, right)
        .unwrap();
    {
        let mut buffer = db.new_buffer(uf);
        buffer.stage_typed_union_deferred(&[left, right, Value::new(1)], foreign_cause, proposal);
    }

    let failed = catch_unwind(AssertUnwindSafe(|| db.merge_all()));
    assert!(
        failed.is_err(),
        "a pending rule cause owned by another trace arena must fail preflight"
    );
    assert_eq!(native_uf_root(&db, uf, left), left);
    assert_eq!(native_uf_root(&db, uf, right), right);
}

#[test]
fn pending_rule_cause_rejects_a_missing_same_arena_match() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let trace = db.try_enable_trace().unwrap();
    let wave = Wave::new(1);
    let sort = ReplaySortId::new(904);
    let left = Value::new(9040);
    let right = Value::new(9041);
    trace.intern_literal(sort, ReplayLiteral::I64(9040), left);
    trace.intern_literal(sort, ReplayLiteral::I64(9041), right);
    db.set_trace_wave(wave);
    let forged = trace.observed_firing_batch_for_test(crate::FiringId::new(999), 1, wave);
    let failed = catch_unwind(AssertUnwindSafe(|| trace.pending_firing_cause(&forged, 0)));
    assert!(
        failed.is_err(),
        "a pending cause must not manufacture a missing same-arena match"
    );
    assert_eq!(native_uf_root(&db, uf, left), left);
    assert_eq!(native_uf_root(&db, uf, right), right);
}

#[test]
fn pending_rule_cause_rejects_a_lane_outside_its_observed_batch() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let trace = db.try_enable_trace().unwrap();
    let wave = Wave::new(1);
    let first = trace.pending_firing_batch(905, wave, 0, &[], &[], 1);
    let _adjacent = trace.pending_firing_batch(906, wave, 0, &[], &[], 1);
    let sort = ReplaySortId::new(905);
    let left = Value::new(9050);
    let right = Value::new(9051);
    trace.intern_literal(sort, ReplayLiteral::I64(9050), left);
    trace.intern_literal(sort, ReplayLiteral::I64(9051), right);
    db.set_trace_wave(wave);
    let failed = catch_unwind(AssertUnwindSafe(|| trace.pending_firing_cause(&first, 1)));
    assert!(
        failed.is_err(),
        "a lane beyond its observed batch must not alias an adjacent match"
    );
    assert_eq!(native_uf_root(&db, uf, left), left);
    assert_eq!(native_uf_root(&db, uf, right), right);
}
#[test]
fn observed_match_ids_are_dense_before_effect_reachability() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let trace = db.try_enable_trace().unwrap();
    let sort = ReplaySortId::new(200);
    let left = Value::new(2000);
    let right = Value::new(2001);
    trace.intern_literal(sort, ReplayLiteral::I64(2000), left);
    trace.intern_literal(sort, ReplayLiteral::I64(2001), right);

    let wave = Wave::new(1);
    db.set_trace_wave(wave);
    let observed = trace.pending_firing_batch(200, wave, 0, &[], &[], 4);
    let proposal = trace
        .typed_equality_proposal(wave, sort, left, right)
        .unwrap();
    {
        let mut buffer = db.new_buffer(uf);
        buffer.stage_typed_union_deferred(
            &[left, right, Value::new(1)],
            crate::DeferredEqualityCause::pending(trace.pending_firing_cause(&observed, 3)),
            proposal,
        );
    }
    assert!(db.merge_all());
    db.finalize_trace_wave();

    trace
        .with_view(|view| {
            assert_eq!(
                view.totals().firings,
                4,
                "the borrowed view retains all dense observations"
            );
            let equality = view.applied_equality(crate::AppliedEqualityId::new(1))?;
            assert_eq!(
                equality_firing(&equality.reason),
                crate::FiringId::new(4),
                "only the effective fourth observation should be reachable from an effect"
            );
            Ok(())
        })
        .unwrap();
}
#[test]
fn promoted_match_ids_follow_native_batch_order_not_union_order() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let trace = db.try_enable_trace().unwrap();
    let sort = ReplaySortId::new(194);
    let values = [
        Value::new(1940),
        Value::new(1941),
        Value::new(1942),
        Value::new(1943),
    ];
    for (index, value) in values.into_iter().enumerate() {
        trace.intern_literal(sort, ReplayLiteral::I64(index as i64), value);
    }
    let wave = Wave::new(1);
    db.set_trace_wave(wave);
    let earlier = trace.pending_firing_batch(194, wave, 0, &[], &[], 1);
    let later = trace.pending_firing_batch(195, wave, 0, &[], &[], 1);
    {
        let mut buffer = db.new_buffer(uf);
        for (batch, left, right) in [
            (&later, values[2], values[3]),
            (&earlier, values[0], values[1]),
        ] {
            let proposal = trace
                .typed_equality_proposal(wave, sort, left, right)
                .unwrap();
            buffer.stage_typed_union_deferred(
                &[left, right, Value::new(1)],
                crate::DeferredEqualityCause::pending(trace.pending_firing_cause(batch, 0)),
                proposal,
            );
        }
    }
    assert!(db.merge_all());
    db.finalize_trace_wave();
    trace
        .with_view(|view| {
            let cited = (1..=view.totals().applied_equalities)
                .map(|id| view.applied_equality(crate::AppliedEqualityId::new(id)))
                .map(|event| event.map(|event| equality_firing(&event.reason)))
                .collect::<Result<std::collections::BTreeSet<_>, _>>()?;
            let rules = cited
                .into_iter()
                .map(|id| view.firing(id).map(|matched| matched.rule))
                .collect::<Result<Vec<_>, _>>()?;
            assert_eq!(rules, [194, 195]);
            Ok(())
        })
        .unwrap();
}

#[test]
fn promoted_match_order_follows_full_batch_then_tail_execution() {
    const FULL_BATCH: usize = 128;
    const TAIL_RULE: u32 = 197;
    const FULL_RULE: u32 = 198;
    let mut db = Database::default();
    let relation = || {
        SortedWritesTable::new(
            1,
            1,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right);
                false
            }),
        )
    };
    let tail_input = db.add_table_named(
        relation(),
        "OrdinalTailInput".into(),
        iter::empty(),
        iter::empty(),
    );
    let full_input = db.add_table_named(
        relation(),
        "OrdinalFullInput".into(),
        iter::empty(),
        iter::empty(),
    );
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let trace = db.try_enable_trace().unwrap();
    for table in [tail_input, full_input] {
        trace
            .register_table_layout(table, &[Some(TEST_REPLAY_SORT)])
            .unwrap();
    }
    let endpoints = [
        Value::new(1970),
        Value::new(1971),
        Value::new(1972),
        Value::new(1973),
    ];
    for endpoint in endpoints {
        trace.intern_literal(
            TEST_REPLAY_SORT,
            ReplayLiteral::I64(endpoint.index() as i64),
            endpoint,
        );
    }
    let mut source = 0_u64;
    for (table, count) in [(tail_input, 1), (full_input, FULL_BATCH)] {
        for value in 0..count {
            let raw = Value::from_usize(value);
            let term = trace.intern_literal(
                TEST_REPLAY_SORT,
                ReplayLiteral::I64((10_000 + source) as i64),
                raw,
            );
            db.stage_source_row(
                table,
                &[raw],
                &[term],
                SourceRef::Synthetic(10_000 + source),
            )
            .unwrap();
            source += 1;
        }
    }
    assert!(db.merge_all());
    db.finalize_trace_wave();

    let mut rules = RuleSetBuilder::new(&mut db);
    for (input, rule, left, right, description) in [
        (
            tail_input,
            TAIL_RULE,
            endpoints[2],
            endpoints[3],
            "ordinal-tail",
        ),
        (
            full_input,
            FULL_RULE,
            endpoints[0],
            endpoints[1],
            "ordinal-full",
        ),
    ] {
        let mut query = rules.new_rule();
        let value = query.new_var_named(description);
        let atom = query.add_atom(input, &[value.into()], &[]).unwrap();
        let mut action = query.build();
        action
            .union_with_replay(
                uf,
                left.into(),
                right.into(),
                Value::new(1).into(),
                TEST_REPLAY_SORT,
            )
            .unwrap();
        action
            .try_build_with_capture(
                description,
                FiringCaptureSpec::new(rule, [atom], iter::empty::<crate::RuleBindingSpec>()),
            )
            .unwrap();
    }
    let rules = rules.build();
    db.set_trace_wave(Wave::new(1));
    assert!(db.run_rule_set(&rules, ReportLevel::TimeOnly).changed);
    db.finalize_trace_wave();

    trace
        .with_view(|view| {
            assert_eq!(view.totals().firings, (FULL_BATCH + 1) as u64);
            assert_eq!(view.totals().applied_equalities, 2);
            let effective = (1..=view.totals().applied_equalities)
                .map(|id| view.applied_equality(crate::AppliedEqualityId::new(id)))
                .map(|event| event.and_then(|event| view.firing(equality_firing(&event.reason))))
                .map(|matched| matched.map(|matched| matched.rule))
                .collect::<Result<Vec<_>, _>>()?;
            assert_eq!(
                effective,
                [FULL_RULE, TAIL_RULE],
                "native ordinals are reserved when each action batch actually starts"
            );
            Ok(())
        })
        .unwrap();
}

#[test]
#[should_panic(expected = "selects non-replayable table column")]
fn causal_capture_metadata_rejects_binding_an_ignored_column() {
    let mut db = Database::default();
    let table = db.add_table(
        SortedWritesTable::new(
            1,
            2,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right);
                false
            }),
        ),
        iter::empty(),
        iter::empty(),
    );
    let trace = db.try_enable_trace().unwrap();
    trace
        .register_table_layout(table, &[Some(ReplaySortId::new(12)), None])
        .unwrap();
    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let value = query.new_var();
    let ignored = query.new_var();
    let atom = query
        .add_atom(table, &[value.into(), ignored.into()], &[])
        .unwrap();
    let action = query.build();
    action
        .try_build_with_capture(
            "ignored-column",
            FiringCaptureSpec::new(
                61,
                [atom],
                [crate::RuleBindingSpec::variable(
                    ignored,
                    ReplaySortId::new(12),
                )],
            ),
        )
        .unwrap();
}
#[test]
fn causal_trace_merge_origin_selects_each_cell_without_value_alias_lookup() {
    let mut db = Database::default();
    let table = db.add_table(
        SortedWritesTable::new(
            1,
            3,
            None,
            vec![],
            Box::new(|_, prior, incoming, out| {
                out.extend_from_slice(&[incoming[0], prior[1], incoming[2]]);
                out.as_slice() != prior
            }),
        ),
        iter::empty(),
        iter::empty(),
    );
    let trace = db.try_enable_trace().unwrap();
    let value_sort = ReplaySortId::new(198);
    let alias_sort = ReplaySortId::new(199);
    let alias_op = ReplayOpId::new(198);
    trace
        .register_table_layout(
            table,
            &[Some(value_sort), Some(alias_sort), Some(value_sort)],
        )
        .unwrap();
    trace
        .register_table_merge_origins(
            table,
            &[
                MergeOriginSelector::Incoming { column: 0 },
                MergeOriginSelector::Prior { column: 1 },
                MergeOriginSelector::Incoming { column: 2 },
            ],
        )
        .unwrap();

    let key_value = Value::new(1980);
    let shared_alias_value = Value::new(1981);
    let old_child_value = Value::new(1982);
    let new_child_value = Value::new(1983);
    let old_tail_value = Value::new(1984);
    let new_tail_value = Value::new(1985);
    let key_term = trace.intern_literal(value_sort, ReplayLiteral::I64(1980), key_value);
    let old_child = trace.intern_literal(value_sort, ReplayLiteral::I64(1982), old_child_value);
    let new_child = trace.intern_literal(value_sort, ReplayLiteral::I64(1983), new_child_value);
    let old_alias = trace
        .intern_call(alias_sort, alias_op, &[old_child], shared_alias_value)
        .unwrap();
    let old_tail = trace.intern_literal(value_sort, ReplayLiteral::I64(1984), old_tail_value);
    let new_tail = trace.intern_literal(value_sort, ReplayLiteral::I64(1985), new_tail_value);
    let prior_row = [key_value, shared_alias_value, old_tail_value];
    db.stage_source_row(
        table,
        &prior_row,
        &[key_term, old_alias, old_tail],
        SourceRef::Synthetic(198),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_trace_wave();

    let incoming_origin = trace.register_row_origin(RowOriginSpec {
        table,
        cells: [
            Some(Arc::new(TermTemplate::Static { term: key_term })),
            Some(Arc::new(TermTemplate::Call {
                sort: alias_sort,
                op: alias_op,
                children: [Arc::new(TermTemplate::Static { term: new_child })].into(),
            })),
            Some(Arc::new(TermTemplate::Static { term: new_tail })),
        ]
        .into(),
    });
    db.set_trace_wave(Wave::new(1));
    let cause = empty_rule_cause(&trace, 198, Wave::new(1));
    let incoming_row = [key_value, shared_alias_value, new_tail_value];
    {
        let mut updates = db.new_buffer(table);
        updates.stage_insert_deferred_with_origin(
            &incoming_row,
            crate::DeferredEqualityCause::ready(cause),
            incoming_origin,
        );
    }
    assert!(db.merge_all());
    db.finalize_trace_wave();

    trace.with_view(|view| {
    let latest = fact_ids(view).filter_map(|id| view.fact(id).ok()).filter(|fact| fact.table == table).max_by_key(|fact| fact.id).unwrap();
    let terms = view.fact_terms(latest.id)?;
    assert_eq!(
        latest.values,
        &[key_value, shared_alias_value, new_tail_value]
    );
    assert_eq!(terms[0], key_term);
    assert_eq!(
        terms[1], old_alias,
        "the Prior selector must preserve the exact prior alias even when incoming has the same native value"
    );
    assert_eq!(terms[2], new_tail);
    assert_eq!(
        trace.lookup_term(alias_sort, shared_alias_value),
        Some(old_alias),
        "the canary deliberately leaves global lookup unable to name the incoming alias"
    );
    Ok(())
    }).unwrap();
}
#[test]
fn merge_origin_catalog_rejects_out_of_range_and_cross_sort_sources() {
    let trace = Trace::default();
    let table = TableId::new_const(198);
    let left = ReplaySortId::new(198);
    let right = ReplaySortId::new(199);
    trace
        .register_table_layout(table, &[Some(left), Some(right)])
        .unwrap();
    assert_eq!(
        trace.register_table_merge_origins(
            table,
            &[
                MergeOriginSelector::Incoming { column: 2 },
                MergeOriginSelector::Incoming { column: 1 },
            ],
        ),
        Err("merge-origin source column exceeds the table layout")
    );
    assert_eq!(
        trace.register_table_merge_origins(
            table,
            &[
                MergeOriginSelector::Incoming { column: 0 },
                MergeOriginSelector::Prior { column: 0 },
            ],
        ),
        Err("merge-origin source and destination have different replay sorts")
    );
}
#[test]
fn transactional_native_lease_blocks_wave_finalization_until_queue_drain() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let trace = db.try_enable_trace().unwrap();
    let sort = ReplaySortId::new(143);
    let left = Value::new(1430);
    let right = Value::new(1431);
    trace.intern_literal(sort, ReplayLiteral::I64(1430), left);
    trace.intern_literal(sort, ReplayLiteral::I64(1431), right);
    let wave = Wave::new(1);
    db.set_trace_wave(wave);
    let cause = empty_rule_cause(&trace, 143, wave);
    let proposal = trace
        .typed_equality_proposal(wave, sort, left, right)
        .unwrap();
    let transaction = MutationTransaction::pending_causal(&trace, wave);
    let mut buffer = db.new_buffer(uf);
    buffer.defer_until(transaction.clone());
    buffer.stage_typed_union(&[left, right, Value::new(1)], cause, proposal);
    transaction.commit();
    drop(transaction);

    let before_publication = catch_unwind(AssertUnwindSafe(|| db.finalize_trace_wave()));
    assert!(before_publication.is_err());
    drop(buffer);
    let before_drain = catch_unwind(AssertUnwindSafe(|| db.finalize_trace_wave()));
    assert!(before_drain.is_err());

    assert!(db.merge_all());
    db.finalize_trace_wave();
    trace
        .with_view(|view| {
            let equality = view.applied_equality(crate::AppliedEqualityId::new(1))?;
            assert!(matches!(
                equality.reason,
                crate::EqualityReason::RuleUnion(_)
            ));
            Ok(())
        })
        .unwrap();
}

#[test]
fn transactional_table_lease_survives_buffer_publication_until_queue_drain() {
    let mut db = Database::default();
    let table = db.add_table(
        SortedWritesTable::new(1, 1, None, vec![], Box::new(|_, _, _, _| false)),
        iter::empty(),
        iter::empty(),
    );
    let trace = db.try_enable_trace().unwrap();
    register_test_capture_table(&trace, table, 1);
    let value = Value::new(1432);
    install_test_row_terms(&trace, &[value]);
    let wave = Wave::new(1);
    db.set_trace_wave(wave);
    let cause = empty_rule_cause(&trace, 144, wave);
    let term = trace.lookup_term(TEST_REPLAY_SORT, value).unwrap();
    let origin = install_test_row_origin(&trace, table, &[value], &[term]);
    let transaction = MutationTransaction::pending_causal(&trace, wave);
    let mut buffer = db.new_buffer(table);
    buffer.defer_until(transaction.clone());
    buffer.stage_insert_deferred_with_origin(
        &[value],
        crate::DeferredEqualityCause::ready(cause),
        origin,
    );
    transaction.commit();
    drop(transaction);

    let while_buffer_holds_lease = catch_unwind(AssertUnwindSafe(|| db.finalize_trace_wave()));
    assert!(while_buffer_holds_lease.is_err());
    drop(buffer);
    let while_table_queue_holds_lease = catch_unwind(AssertUnwindSafe(|| db.finalize_trace_wave()));
    assert!(while_table_queue_holds_lease.is_err());

    assert!(db.merge_all());
    db.finalize_trace_wave();
    trace
        .with_view(|view| {
            let fact = view.fact(crate::FactId::new(1))?;
            assert!(matches!(fact.cause, crate::CauseRef::Rule(_)));
            Ok(())
        })
        .unwrap();
}
#[test]
fn causal_trace_reject_activation_after_rows_exist() {
    let mut db = Database::default();
    let table = db.add_table_named(
        SortedWritesTable::new(
            1,
            2,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "relation rows are immutable");
                false
            }),
        ),
        "Preloaded".into(),
        iter::empty(),
        iter::empty(),
    );
    let mut source = db.new_buffer(table);
    source.stage_insert(&[Value::new(1), Value::new(0)]);
    drop(source);
    assert!(db.merge_all());
    assert_eq!(
        db.try_enable_trace().err().unwrap(),
        "table already contains rows without exact source identities"
    );
}
#[test]
fn causal_trace_reject_dropped_unmerged_relation_and_uf_buffers() {
    for is_uf in [false, true] {
        let mut db = Database::default();
        let table = if is_uf {
            db.add_table(DisplacedTable::default(), iter::empty(), iter::empty())
        } else {
            db.add_table(activation_test_relation(), iter::empty(), iter::empty())
        };
        {
            let mut buffer = db.new_buffer(table);
            if is_uf {
                buffer.stage_insert(&[Value::new(2), Value::new(1), Value::new(0)]);
            } else {
                buffer.stage_insert(&[Value::new(1), Value::new(0)]);
            }
        }

        let error = db.try_enable_trace().err().unwrap();
        assert!(
            error.contains("queued capture-disabled mutations"),
            "dropped, unmerged {} mutations must reject capture activation",
            if is_uf { "UF" } else { "relation" }
        );
        assert!(db.trace.is_none());
    }
}

#[test]
fn causal_trace_reject_outstanding_relation_and_uf_buffers() {
    for is_uf in [false, true] {
        let mut db = Database::default();
        let table = if is_uf {
            db.add_table(DisplacedTable::default(), iter::empty(), iter::empty())
        } else {
            db.add_table(activation_test_relation(), iter::empty(), iter::empty())
        };
        let outstanding = db.new_buffer(table);

        let error = db.try_enable_trace().err().unwrap();
        assert!(
            error.contains("outstanding capture-disabled mutation buffer"),
            "an outstanding {} buffer must reject capture activation even before it stages a row",
            if is_uf { "UF" } else { "relation" }
        );
        assert!(db.trace.is_none());
        drop(outstanding);
    }
}

#[test]
fn capture_database_rejects_a_preloaded_table_before_adding_it() {
    let mut ordinary = Database::default();
    let table = ordinary.add_table(activation_test_relation(), iter::empty(), iter::empty());
    {
        let mut buffer = ordinary.new_buffer(table);
        buffer.stage_insert(&[Value::new(1), Value::new(0)]);
    }
    assert!(ordinary.merge_all());
    let preloaded = ordinary
        .get_table(table)
        .as_any()
        .downcast_ref::<SortedWritesTable>()
        .unwrap()
        .clone();

    let mut trace_db = Database::default();
    trace_db.try_enable_trace().unwrap();
    let next_table = trace_db.next_table_id();
    let failed = catch_unwind(AssertUnwindSafe(|| {
        trace_db.add_table(preloaded, iter::empty(), iter::empty())
    }));
    assert!(failed.is_err());
    assert_eq!(
        trace_db.next_table_id(),
        next_table,
        "a rejected preloaded table must not be partially registered"
    );
}
#[test]
fn low_level_remove_fails_before_staging_when_trace_are_enabled() {
    let mut db = Database::default();
    let table = db.add_table_named(
        SortedWritesTable::new(
            1,
            2,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "relation rows are immutable");
                false
            }),
        ),
        "Source".into(),
        iter::empty(),
        iter::empty(),
    );
    let trace = db.try_enable_trace().unwrap();
    register_test_capture_table(&trace, table, 2);
    let mut raw_buffer = db.new_buffer(table);
    let one = trace.intern_test_term("one");
    let zero = trace.intern_test_term("zero");
    db.stage_source_row(
        table,
        &[Value::new(1), Value::new(0)],
        &[one, zero],
        SourceRef::Synthetic(0),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_trace_wave();

    let mut exec_state = ExecutionState::new(db.read_only_view(), Default::default());
    let failure = catch_unwind(AssertUnwindSafe(|| {
        exec_state.stage_remove(table, &[Value::new(1)]);
    }));
    assert!(failure.is_err());
    drop(exec_state);
    assert_eq!(
        db.get_table(table).len(),
        1,
        "unsupported deletion must fail before a mutation buffer is staged"
    );
    let raw_failure = catch_unwind(AssertUnwindSafe(|| {
        raw_buffer.stage_remove(&[Value::new(1)]);
    }));
    assert!(
        raw_failure.is_err(),
        "a raw table buffer must not disguise an unattributed delete as rebuild maintenance"
    );
    assert_eq!(db.get_table(table).len(), 1);
    let clear_failure = catch_unwind(AssertUnwindSafe(|| {
        db.get_table_mut(table).clear();
    }));
    assert!(clear_failure.is_err());
    assert_eq!(db.get_table(table).len(), 1);
}
