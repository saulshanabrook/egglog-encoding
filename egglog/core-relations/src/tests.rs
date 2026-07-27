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

use crate::receipts::{RowOriginSpec, TermOriginSpec, TermTemplate};
use crate::{
    CausalReceipts, CausalWave, CheckEndpointSource, CheckReceiptSpec, FactId, MergeOriginSelector,
    PlanStrategy, ReplayConstructorSpec, ReplayLiteral, ReplayOpId, ReplaySortId, ReplayTableKind,
    ReplayTerm, RowOriginSiteId, RuleReceiptSpec, SourceReceiptSpec, SourceRef,
    action::{ExecutionState, Instr, WriteVal},
    common::Value,
    free_join::{
        CounterId, Database, TableId,
        execute::{
            materialized_witness_test_counts, pending_witness_resolution_count,
            reset_materialized_witness_test_counts, reset_pending_witness_resolution_count,
        },
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

fn register_test_receipt_table(receipts: &CausalReceipts, table: TableId, columns: usize) {
    register_test_receipt_table_kind(receipts, table, columns, ReplayTableKind::ValueFunction);
}

fn register_test_receipt_table_kind(
    receipts: &CausalReceipts,
    table: TableId,
    columns: usize,
    kind: ReplayTableKind,
) {
    receipts
        .register_table_layout(table, &vec![Some(TEST_REPLAY_SORT); columns])
        .unwrap();
    receipts
        .register_table_merge_origins(
            table,
            &(0..columns)
                .map(|column| MergeOriginSelector::Incoming {
                    column: column.try_into().unwrap(),
                })
                .collect::<Vec<_>>(),
        )
        .unwrap();
    receipts.register_table_kind(table, kind).unwrap();
}

fn install_test_row_terms(receipts: &CausalReceipts, row: &[Value]) {
    for value in row {
        receipts.intern_literal(
            TEST_REPLAY_SORT,
            ReplayLiteral::Internal(value.index() as u64),
            *value,
        );
    }
}

fn install_test_row_origin(
    receipts: &CausalReceipts,
    table: TableId,
    row: &[Value],
    terms: &[crate::ReplayTermId],
) -> RowOriginSiteId {
    receipts.install_source_row(table, row, terms).unwrap()
}

fn certify_test_replay_call(
    receipts: &CausalReceipts,
    rule: u32,
    sort: ReplaySortId,
    op: ReplayOpId,
) {
    receipts.register_rule_term_recipe(
        rule,
        crate::receipts::TermRecipe {
            current_roots: [Some(Arc::new(TermTemplate::Call {
                sort,
                op,
                children: Arc::from([]),
            }))]
            .into(),
        },
    );
}

fn register_test_merge_origins(
    receipts: &CausalReceipts,
    table: TableId,
    origins: &[MergeOriginSelector],
) {
    receipts
        .register_table_merge_origins(table, origins)
        .unwrap();
}

fn fact_ids(view: &crate::CausalReceiptView<'_>) -> impl Iterator<Item = FactId> {
    (1..=view.totals().facts).map(FactId::new)
}

fn match_ids(view: &crate::CausalReceiptView<'_>) -> impl Iterator<Item = crate::RuleMatchId> {
    (1..=view.totals().matches).map(crate::RuleMatchId::new)
}

fn cause_rule_match(cause: crate::ReceiptCauseRef) -> Option<crate::RuleMatchId> {
    match cause {
        crate::ReceiptCauseRef::Rule(id) => Some(id),
        crate::ReceiptCauseRef::Cause(_) => None,
    }
}

fn view_end_position(view: &crate::CausalReceiptView<'_>) -> crate::HistoryPosition {
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
    view: &mut crate::CausalReceiptView<'a>,
) -> Result<Vec<crate::RawRekeyRecord<'a>>, crate::ReceiptViewError> {
    let mut rekeys = Vec::new();
    for position in 1..=view_end_position(view).get() {
        if let Ok(rekey) = view.rekey_at(crate::HistoryPosition::new(position)) {
            rekeys.push(rekey);
        }
    }
    assert_eq!(rekeys.len() as u64, view.totals().rekeys);
    Ok(rekeys)
}

fn fact_for_table<'a>(
    view: &crate::CausalReceiptView<'a>,
    table: TableId,
) -> crate::RawFactRecord<'a> {
    fact_ids(view)
        .find_map(|id| view.fact(id).ok().filter(|fact| fact.table == table))
        .expect("expected one durable fact for the table")
}

#[test]
fn source_receipt_actions_publish_source_causes_without_rule_matches() {
    let mut db = Database::default();
    let relation = || {
        SortedWritesTable::new(
            1,
            2,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "source-action rows are immutable");
                false
            }),
        )
    };
    let output = db.add_table(relation(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    register_test_receipt_table(&receipts, output, 2);
    let value = Value::new(7);
    let output_timestamp = Value::new(1);
    for raw in [value, output_timestamp] {
        receipts.intern_literal(
            TEST_REPLAY_SORT,
            ReplayLiteral::Internal(raw.index() as u64),
            raw,
        );
    }

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut action = rules.new_rule().build();
    action
        .insert(output, &[value.into(), output_timestamp.into()])
        .unwrap();
    action.build_source_with_receipts(
        "source-action",
        SourceReceiptSpec::new(SourceRef::Synthetic(401)),
    );
    let rules = rules.build();

    db.set_causal_wave(CausalWave::new(1));
    assert!(db.run_rule_set(&rules, ReportLevel::TimeOnly).changed);
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            let output_fact = fact_for_table(view, output);
            let crate::ReceiptCauseRef::Cause(cause) = output_fact.cause else {
                panic!("source action must retain a source cause")
            };
            assert!(matches!(
                view.cause(cause)?,
                crate::RawReceiptCause::Source(SourceRef::Synthetic(401))
            ));
            assert_eq!(
                view.totals().matches,
                0,
                "source actions must not manufacture rule matches"
            );
            Ok(())
        })
        .unwrap();
}

#[test]
#[should_panic(expected = "source receipt actions require an empty query")]
fn source_receipt_actions_reject_query_derived_facts() {
    let mut db = Database::default();
    let table = db.add_table(
        SortedWritesTable::new(1, 1, None, vec![], Box::new(|_, _, _, _| false)),
        iter::empty(),
        iter::empty(),
    );
    db.enable_causal_receipts();
    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let value = query.new_var_named("value");
    query.add_atom(table, &[value.into()], &[]).unwrap();
    query.build().build_source_with_receipts(
        "invalid-query-source",
        SourceReceiptSpec::new(SourceRef::Synthetic(402)),
    );
}

#[test]
fn check_receipts_keep_distinct_premise_terms_for_the_same_runtime_equality_value() {
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
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(401);
    receipts
        .register_table_layout(left_table, &[Some(sort), Some(sort)])
        .unwrap();
    receipts
        .register_table_layout(right_table, &[Some(sort), Some(sort)])
        .unwrap();
    let join = Value::new(1);
    let first_left = Value::new(20);
    let second_left = Value::new(30);
    let right = Value::new(10);
    for raw in [join, first_left, second_left, right] {
        receipts.intern_literal(sort, ReplayLiteral::Internal(raw.index() as u64), raw);
    }
    let term = |raw| receipts.lookup_term(sort, raw).unwrap();
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
    db.finalize_causal_wave();
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
    db.finalize_causal_wave();
    let first_left_fact = committed_fact_id_for_key(&db, left_table, &[first_left, join]);
    assert!(
        second_left_fact < first_left_fact,
        "test requires FactId order to oppose table scan order"
    );

    db.set_causal_wave(CausalWave::new(1));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&receipts, 500, CausalWave::new(1)),
        sort,
        first_left,
        right,
        Value::new(1),
    );
    assert!(db.merge_all());
    db.set_causal_wave(CausalWave::new(2));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&receipts, 501, CausalWave::new(2)),
        sort,
        second_left,
        right,
        Value::new(2),
    );
    assert!(db.merge_all());
    db.set_causal_wave(CausalWave::new(3));

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
        action.build_check_with_receipts(
            format!("check-{check}"),
            CheckReceiptSpec::new(check, [left_atom, right_atom]).with_equalities([(
                CheckEndpointSource::premise(0, 0, right.into()),
                CheckEndpointSource::premise(1, 1, right.into()),
            )]),
        );
    }
    let rules = rules.build();
    assert!(!db.run_rule_set(&rules, ReportLevel::TimeOnly).changed);
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            let roots = view.check_roots();
            assert_eq!(
                roots.iter().map(|root| root.check).collect::<Vec<_>>(),
                [4, 9],
                "root order must depend only on stable check IDs"
            );
            for root in &roots {
                assert_eq!(root.wave, CausalWave::new(3));
                assert_eq!(root.premises.as_ref(), &[second_left_fact, right_fact]);
                assert_eq!(root.as_of_edges, crate::EqualityEdgeCount::new(2));
                assert_eq!(
                    root.equalities.as_ref(),
                    &[(
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
                    )]
                );
                assert_ne!(
                    root.equalities[0].0.raw, root.equalities[0].1.raw,
                    "the root keeps each premise's immutable creation occurrence"
                );
                assert_ne!(
                    root.equalities[0].0.term, root.equalities[0].1.term,
                    "equal runtime values must retain their distinct premise-owned syntax"
                );
            }
            assert_eq!(roots, view.check_roots());
            assert_eq!(
                view.totals().matches,
                2,
                "only the two effective equality-producing rules should have matches"
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn check_receipt_missing_equality_term_publishes_no_root() {
    let mut db = Database::default();
    let premise = db.add_table(
        SortedWritesTable::new(
            1,
            1,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "check premise rows are immutable");
                false
            }),
        ),
        iter::empty(),
        iter::empty(),
    );
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(402);
    receipts
        .register_table_layout(premise, &[Some(sort)])
        .unwrap();
    let present = Value::new(7);
    let present_term = receipts.intern_literal(sort, ReplayLiteral::Internal(7), present);
    db.stage_source_row(
        premise,
        &[present],
        &[present_term],
        SourceRef::Synthetic(420),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();

    let missing = Value::new(99);
    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let value = query.new_var_named("value");
    let atom = query.add_atom(premise, &[value.into()], &[]).unwrap();
    query.build().build_check_with_receipts(
        "missing-check-term",
        CheckReceiptSpec::new(77, [atom]).with_equalities([(
            CheckEndpointSource::premise(0, 0, value.into()),
            CheckEndpointSource::current(crate::QueryEntry::Const(missing), sort),
        )]),
    );
    let rules = rules.build();

    db.set_causal_wave(CausalWave::new(1));
    let failed = catch_unwind(AssertUnwindSafe(|| {
        db.run_rule_set(&rules, ReportLevel::TimeOnly)
    }));
    assert!(
        failed.is_err(),
        "a check equality without both producer-installed terms must fail"
    );
    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            assert!(
                view.check_roots().is_empty(),
                "term resolution must complete before any check root is published"
            );
            Ok(())
        })
        .unwrap();
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
fn causal_receipts_record_only_effective_constructor_and_union_commits() {
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

    let receipts = db.enable_causal_receipts();
    let value_sort = ReplaySortId::new(20);
    let node_sort = ReplaySortId::new(21);
    let node_op = ReplayOpId::new(20);
    receipts
        .register_table_layout(input, &[Some(value_sort), Some(node_sort), None])
        .unwrap();
    receipts
        .register_table_layout(constructor, &[Some(value_sort), Some(node_sort), None])
        .unwrap();
    for table in [derived, consumed] {
        receipts
            .register_table_layout(table, &[Some(value_sort), Some(node_sort), None])
            .unwrap();
    }
    let input_term = receipts.intern_literal(value_sort, ReplayLiteral::I64(7), Value::new(7));
    let input_as_node_term =
        receipts.intern_literal(node_sort, ReplayLiteral::Internal(7), Value::new(7));
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
    action.build_with_receipts(
        "derive-node",
        RuleReceiptSpec::with_bindings(
            0,
            [input_atom],
            [
                crate::RuleBindingSpec::variable(value, None),
                crate::RuleBindingSpec::variable(source_node, None),
            ],
        ),
    );
    let rule_set = rules.build();

    db.set_causal_wave(CausalWave::new(1));
    let first = db.run_rule_set(&rule_set, ReportLevel::TimeOnly);
    assert!(first.changed);
    db.finalize_causal_wave();

    let (source_id, derived_id, node_term) = receipts
        .with_view(|view| {
            let source = fact_for_table(view, input);
            let constructor_fact = fact_for_table(view, constructor);
            let derived_fact = fact_for_table(view, derived);
            assert_ne!(source.id, constructor_fact.id);
            assert_ne!(source.id, derived_fact.id);
            let match_id = cause_rule_match(constructor_fact.cause).unwrap();
            let match_record = view.matched(match_id)?;
            assert_eq!(match_record.wave, CausalWave::new(1));
            assert_eq!(match_record.premises, &[source.id]);
            assert_eq!(
                view.match_terms(match_id)?.as_ref(),
                &[input_term, input_as_node_term]
            );
            assert_eq!(cause_rule_match(derived_fact.cause), Some(match_id));
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
            assert_eq!(equality.wave, CausalWave::new(1));
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
            let counters = view.counters();
            assert_eq!(view.totals().matches, 1);
            assert_eq!(
                (
                    counters.premise_handles,
                    counters.logical_match_term_handles
                ),
                (1, 2)
            );
            assert_eq!(view.fact(source.id)?.values, source.values);
            Ok((source.id, derived_fact.id, node_term))
        })
        .unwrap();
    assert_eq!(
        receipts.replay_term(node_term).unwrap(),
        ReplayTerm::Call {
            sort: node_sort,
            op: node_op,
            children: [input_term].into(),
        }
    );
    let nodes_before_hit = receipts.replay_term_counters().interned_nodes;
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
    action.build_with_receipts(
        "consume-derived-node",
        RuleReceiptSpec::new(1, [derived_atom], [consumed_value, consumed_node]),
    );
    let consumers = consumers.build();
    db.set_causal_wave(CausalWave::new(2));
    let second = db.run_rule_set(&consumers, ReportLevel::TimeOnly);
    assert!(second.changed);
    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            let consumed_fact = fact_for_table(view, consumed);
            assert_eq!(
                view.fact_terms(consumed_fact.id)?.as_ref(),
                &[input_term, node_term, crate::ReplayTermId::MISSING]
            );
            let consumed_match = view.matched(cause_rule_match(consumed_fact.cause).unwrap())?;
            assert_eq!(consumed_match.premises, &[derived_id]);
            assert_eq!(
                view.match_terms(consumed_match.id)?.as_ref(),
                &[input_term, node_term]
            );
            assert!(view.fact(source_id).is_ok());
            Ok(())
        })
        .unwrap();
    assert_eq!(
        receipts.replay_term_counters().interned_nodes,
        nodes_before_hit,
        "constructor hit must reuse the miss path's typed Call"
    );
}

fn empty_rule_cause(
    receipts: &CausalReceipts,
    rule: u32,
    wave: CausalWave,
) -> crate::ReceiptCauseRef {
    receipts.register_rule_matches(rule, wave, 0, &[], &[], &[0])[0]
        .1
        .into()
}

fn stage_test_union(
    db: &Database,
    table: TableId,
    cause: crate::ReceiptCauseRef,
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

#[derive(Clone, Debug, PartialEq, Eq)]
struct TestLandmark {
    as_of_edges: crate::EqualityEdgeCount,
    position: crate::HistoryPosition,
    pairs: Box<[crate::TypedCellEquality]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TestRebuildDependency {
    wave: CausalWave,
    prior_fact: FactId,
    equalities: TestLandmark,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TestContainerDependency {
    wave: CausalWave,
    equalities: TestLandmark,
}

#[derive(Default)]
struct TestCauseDependencies {
    sources: Vec<SourceRef>,
    rules: Vec<crate::RuleMatchId>,
    facts: Vec<FactId>,
    rebuilds: Vec<TestRebuildDependency>,
    container_canonicalizations: Vec<TestContainerDependency>,
    container_refreshes: Vec<(FactId, TestContainerDependency)>,
}

fn test_cause_dependencies(
    view: &crate::CausalReceiptView<'_>,
    root: impl Into<crate::ReceiptCauseRef>,
) -> Result<TestCauseDependencies, crate::ReceiptViewError> {
    let mut result = TestCauseDependencies::default();
    let mut stack = vec![root.into()];
    while let Some(dependency) = stack.pop() {
        match dependency {
            crate::ReceiptCauseRef::Rule(rule) => result.rules.push(rule),
            crate::ReceiptCauseRef::Cause(cause) => match view.cause(cause)? {
                crate::RawReceiptCause::Source(source) => result.sources.push(source.clone()),
                crate::RawReceiptCause::Rebuild {
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
                crate::RawReceiptCause::ContainerCanonicalize {
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
                crate::RawReceiptCause::ContainerRefresh {
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
                crate::RawReceiptCause::Merge { incoming, prior } => {
                    stack.push(incoming);
                    if let crate::ReceiptCausePrior::Cause(cause) = prior {
                        stack.push(cause);
                    } else if let crate::ReceiptCausePrior::Fact(fact) = prior {
                        result.facts.push(fact);
                    }
                }
            },
        }
    }
    Ok(result)
}

fn test_congruence_dependencies(
    view: &crate::CausalReceiptView<'_>,
    reason: &crate::EqualityReason,
) -> Result<(TestCauseDependencies, TestLandmark), crate::ReceiptViewError> {
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
fn causal_receipt_rebuild_cutoff_failure_preserves_canonicalizer_table() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let rebuilt = db.add_table(
        SortedWritesTable::new(
            1,
            2,
            Some(ColumnId::new(1)),
            vec![ColumnId::new(0)],
            Box::new(|_, _, _, _| false),
        ),
        iter::once(uf),
        iter::empty(),
    );
    let receipts = db.enable_causal_receipts();
    let open_fragment = receipts.new_batch();

    let failed = catch_unwind(AssertUnwindSafe(|| {
        db.apply_rebuild(uf, &[rebuilt], Value::new(1));
    }));
    assert!(failed.is_err());
    assert_eq!(
        db.get_table(uf).len(),
        0,
        "cutoff validation removed the canonicalizer table"
    );
    assert_eq!(db.get_table(rebuilt).len(), 0);

    open_fragment.publish();
    db.finalize_causal_wave();
    assert!(
        receipts
            .with_view(|view| Ok(view.totals().facts == 0))
            .unwrap()
    );
}

#[test]
fn causal_receipt_incremental_rebuild_retry_keeps_uncommitted_subset_cursor() {
    const ROWS: u32 = 10_001;
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let rebuilt = db.add_table(
        SortedWritesTable::new(
            1,
            2,
            Some(ColumnId::new(1)),
            vec![ColumnId::new(0)],
            Box::new(|_, _, _, _| false),
        ),
        iter::once(uf),
        iter::empty(),
    );
    let receipts = db.enable_causal_receipts();
    let table_sort = ReplaySortId::new(113);
    let uf_sort = table_sort;
    receipts
        .register_table_layout(rebuilt, &[Some(table_sort), None])
        .unwrap();

    let old = Value::new(100_000);
    let new = Value::new(50_000);
    let source_cause = receipts.source_draft(SourceRef::Synthetic(113));
    let mut source_rows = db.new_buffer(rebuilt);
    for offset in 0..ROWS {
        let value = Value::new(100_000 + offset);
        let term = receipts.intern_literal(
            table_sort,
            ReplayLiteral::Internal(value.index() as u64),
            value,
        );
        let origin = receipts
            .install_source_row(
                rebuilt,
                &[value, Value::new(0)],
                &[term, crate::ReplayTermId::MISSING],
            )
            .unwrap();
        source_rows.stage_insert_deferred_with_origin(
            &[value, Value::new(0)],
            crate::DeferredEqualityCause::ready(source_cause),
            origin,
        );
    }
    drop(source_rows);
    assert!(db.merge_all());
    let prior_fact = committed_fact_id(&db, rebuilt, old);

    let new_term =
        receipts.intern_literal(table_sort, ReplayLiteral::Internal(new.index() as u64), new);
    db.stage_source_row(
        rebuilt,
        &[new, Value::new(0)],
        &[new_term, crate::ReplayTermId::MISSING],
        SourceRef::Synthetic(114),
    )
    .unwrap();
    assert!(db.merge_all());
    let canonical_fact = committed_fact_id(&db, rebuilt, new);

    receipts.intern_literal(uf_sort, ReplayLiteral::Internal(old.index() as u64), old);
    receipts.intern_literal(uf_sort, ReplayLiteral::Internal(new.index() as u64), new);
    db.set_causal_wave(CausalWave::new(1));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&receipts, 113, CausalWave::new(1)),
        uf_sort,
        old,
        new,
        Value::new(1),
    );
    assert!(db.merge_all());
    db.set_causal_wave(CausalWave::new(2));

    let failed = catch_unwind(AssertUnwindSafe(|| {
        db.apply_rebuild(uf, &[rebuilt], Value::new(2));
    }));
    assert!(failed.is_err());
    assert_eq!(committed_fact_id(&db, rebuilt, old), prior_fact);
    assert_eq!(committed_fact_id(&db, rebuilt, new), canonical_fact);

    register_test_merge_origins(
        &receipts,
        rebuilt,
        &[
            MergeOriginSelector::Prior { column: 0 },
            MergeOriginSelector::Unsupported,
        ],
    );
    db.apply_rebuild(uf, &[rebuilt], Value::new(2));
    db.finalize_causal_wave();
    assert!(db.get_table(rebuilt).get_row(&[old]).is_none());
    assert!(db.get_table(rebuilt).get_row(&[new]).is_some());
    assert_eq!(committed_fact_id(&db, rebuilt, new), canonical_fact);
    assert_eq!(
        receipts
            .with_view(|view| Ok(view.counters()))
            .unwrap()
            .rebuild_causes,
        1
    );
}

#[test]
fn causal_receipt_incremental_rebuild_retry_rolls_back_every_target_cursor() {
    const ROWS: u32 = 10_001;
    rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .build()
        .unwrap()
        .install(|| {
            let mut db = Database::default();
            let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
            let relation = || {
                SortedWritesTable::new(
                    1,
                    2,
                    Some(ColumnId::new(1)),
                    vec![ColumnId::new(0)],
                    Box::new(|_, _, _, _| false),
                )
            };
            let first = db.add_table(relation(), iter::once(uf), iter::empty());
            let second = db.add_table(relation(), iter::once(uf), iter::empty());
            let receipts = db.enable_causal_receipts();
            let table_sort = ReplaySortId::new(115);
            let uf_sort = table_sort;
            for table in [first, second] {
                receipts
                    .register_table_layout(table, &[Some(table_sort), None])
                    .unwrap();
            }

            let first_old = Value::new(100_000);
            let first_new = Value::new(50_000);
            let second_old = Value::new(200_000);
            let second_new = Value::new(150_000);
            let source_cause = receipts.source_draft(SourceRef::Synthetic(115));
            for (table, base) in [(first, 100_000_u32), (second, 200_000_u32)] {
                let mut rows = db.new_buffer(table);
                for offset in 0..ROWS {
                    let value = Value::new(base + offset);
                    let term = receipts.intern_literal(
                        table_sort,
                        ReplayLiteral::Internal(value.index() as u64),
                        value,
                    );
                    let origin = receipts
                        .install_source_row(
                            table,
                            &[value, Value::new(0)],
                            &[term, crate::ReplayTermId::MISSING],
                        )
                        .unwrap();
                    rows.stage_insert_deferred_with_origin(
                        &[value, Value::new(0)],
                        crate::DeferredEqualityCause::ready(source_cause),
                        origin,
                    );
                }
            }
            assert!(db.merge_all());
            let first_fact = committed_fact_id(&db, first, first_old);
            let second_fact = committed_fact_id(&db, second, second_old);

            for value in [first_old, first_new, second_old, second_new] {
                receipts.intern_literal(
                    table_sort,
                    ReplayLiteral::Internal(value.index() as u64),
                    value,
                );
            }
            for (table, value, source) in [(first, first_new, 116), (second, second_new, 117)] {
                db.stage_source_row(
                    table,
                    &[value, Value::new(0)],
                    &[
                        receipts.lookup_term(table_sort, value).unwrap(),
                        crate::ReplayTermId::MISSING,
                    ],
                    SourceRef::Synthetic(source),
                )
                .unwrap();
            }
            assert!(db.merge_all());
            let first_canonical = committed_fact_id(&db, first, first_new);
            let second_canonical = committed_fact_id(&db, second, second_new);
            register_test_merge_origins(
                &receipts,
                first,
                &[
                    MergeOriginSelector::Prior { column: 0 },
                    MergeOriginSelector::Unsupported,
                ],
            );
            db.set_causal_wave(CausalWave::new(1));
            let union_cause = empty_rule_cause(&receipts, 115, CausalWave::new(1));
            for (old, new) in [(first_old, first_new), (second_old, second_new)] {
                stage_test_union(&db, uf, union_cause, uf_sort, old, new, Value::new(1));
            }
            assert!(db.merge_all());
            db.set_causal_wave(CausalWave::new(2));

            let failed = catch_unwind(AssertUnwindSafe(|| {
                db.apply_rebuild(uf, &[first, second], Value::new(2));
            }));
            assert!(failed.is_err());
            assert_eq!(committed_fact_id(&db, first, first_old), first_fact);
            assert_eq!(committed_fact_id(&db, second, second_old), second_fact);
            assert_eq!(committed_fact_id(&db, first, first_new), first_canonical);
            assert_eq!(committed_fact_id(&db, second, second_new), second_canonical);

            register_test_merge_origins(
                &receipts,
                second,
                &[
                    MergeOriginSelector::Prior { column: 0 },
                    MergeOriginSelector::Unsupported,
                ],
            );
            db.apply_rebuild(uf, &[first, second], Value::new(2));
            db.finalize_causal_wave();
            for (table, old, new) in [
                (first, first_old, first_new),
                (second, second_old, second_new),
            ] {
                assert!(db.get_table(table).get_row(&[old]).is_none());
                assert!(db.get_table(table).get_row(&[new]).is_some());
            }
            assert_eq!(committed_fact_id(&db, first, first_new), first_canonical);
            assert_eq!(committed_fact_id(&db, second, second_new), second_canonical);
            assert_eq!(
                receipts
                    .with_view(|view| Ok(view.counters()))
                    .unwrap()
                    .rebuild_causes,
                2
            );
        });
}

fn with_same_wave_rebuild_collision(
    row_count: u32,
    collision_count: u32,
    inspect: impl for<'a> FnOnce(
        &mut crate::CausalReceiptView<'a>,
        &[FactId],
    ) -> Result<(), crate::ReceiptViewError>
    + Send,
) {
    assert!(row_count >= collision_count && collision_count >= 2);
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .build()
        .unwrap();
    pool.install(|| {
        let mut db = Database::default();
        let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
        let sort = ReplaySortId::new(78);
        let rebuilt = db.add_table(
            SortedWritesTable::new(
                1,
                3,
                Some(ColumnId::new(2)),
                vec![ColumnId::new(0)],
                Box::new(move |state, prior, incoming, out| {
                    state.stage_union_with_replay(uf, prior[1], incoming[1], Value::new(2), sort);
                    out.extend_from_slice(incoming);
                    true
                }),
            ),
            iter::once(uf),
            iter::once(uf),
        );
        let receipts = db.enable_causal_receipts();
        receipts
            .register_table_layout(rebuilt, &[Some(sort), Some(sort), None])
            .unwrap();
        register_test_merge_origins(
            &receipts,
            rebuilt,
            &[
                MergeOriginSelector::Incoming { column: 0 },
                MergeOriginSelector::Incoming { column: 1 },
                MergeOriginSelector::Unsupported,
            ],
        );

        let old_key = |index: u32| Value::new(1_000_000 + index);
        let new_key = |index: u32| {
            if index < collision_count {
                Value::new(100_000)
            } else {
                Value::new(100_000 + index)
            }
        };
        let output = |index: u32| Value::new(2_000_000 + index);
        for index in 0..row_count {
            for value in [old_key(index), new_key(index), output(index)] {
                receipts.intern_literal(sort, ReplayLiteral::Internal(value.index() as u64), value);
            }
        }

        let lanes = (0..row_count as usize).collect::<Vec<_>>();
        let causes = receipts.register_rule_matches(780, CausalWave::new(0), 0, &[], &[], &lanes);
        let mut initial = db.new_buffer(rebuilt);
        for (index, (_, cause)) in causes.into_iter().enumerate() {
            let index = index as u32;
            let row = [old_key(index), output(index), Value::new(0)];
            let terms = [
                receipts.lookup_term(sort, row[0]).unwrap(),
                receipts.lookup_term(sort, row[1]).unwrap(),
                crate::ReplayTermId::MISSING,
            ];
            let origin = install_test_row_origin(&receipts, rebuilt, &row, &terms);
            initial.stage_insert_deferred_with_origin(
                &row,
                crate::DeferredEqualityCause::ready(cause),
                origin,
            );
        }
        drop(initial);
        assert!(db.merge_all());
        let old_facts = (0..collision_count)
            .map(|index| committed_fact_id(&db, rebuilt, old_key(index)))
            .collect::<Vec<_>>();

        db.set_causal_wave(CausalWave::new(1));
        let union_cause = empty_rule_cause(&receipts, 781, CausalWave::new(1));
        db.with_execution_state(|state| {
            state.set_active_cause_ref(Some(union_cause));
            for index in 0..row_count {
                state.stage_union_with_replay(
                    uf,
                    old_key(index),
                    new_key(index),
                    Value::new(1),
                    sort,
                );
            }
        });
        assert!(db.merge_all());

        db.set_causal_wave(CausalWave::new(2));
        assert!(db.apply_rebuild(uf, &[rebuilt], Value::new(2)));
        db.finalize_causal_wave();
        receipts
            .with_view(|view| inspect(view, &old_facts))
            .unwrap();
    })
}

fn assert_same_wave_rebuild_collision(
    view: &mut crate::CausalReceiptView<'_>,
    old_facts: &[FactId],
    row_count: u32,
    collision_count: u32,
) -> Result<(), crate::ReceiptViewError> {
    let mut selected = None;
    for raw in 1..=view.totals().applied_equalities {
        let equality = view.applied_equality(crate::AppliedEqualityId::new(raw))?;
        if equality.wave != CausalWave::new(2)
            || !matches!(equality.reason, crate::EqualityReason::Congruence { .. })
        {
            continue;
        }
        let (dependencies, landmark) = test_congruence_dependencies(view, &equality.reason)?;
        if dependencies.facts.len() == 2 {
            selected = Some((dependencies, landmark));
            break;
        }
    }
    let (dependencies, landmark) =
        selected.expect("the applied serial congruence must retain its two causal leaves");
    assert_eq!(
        landmark.as_of_edges,
        crate::EqualityEdgeCount::new(row_count as u64)
    );
    assert_eq!(landmark.pairs.len(), 1);
    assert!(
        dependencies
            .facts
            .iter()
            .all(|fact| old_facts.contains(fact))
    );
    assert_eq!(
        old_facts
            .iter()
            .filter(|fact| !dependencies.facts.contains(fact))
            .count(),
        (collision_count - 2) as usize,
        "redundant collision proposals must not widen the applied cause"
    );

    let rekeys = test_rekeys(view)?;
    let relevant = rekeys
        .iter()
        .filter(|rekey| dependencies.facts.contains(&rekey.fact))
        .collect::<Vec<_>>();
    assert_eq!(relevant.len(), 2);
    assert!(
        relevant
            .iter()
            .any(|rekey| rekey.outcome == crate::receipts::RekeyOutcome::Moved)
    );
    assert!(
        relevant
            .iter()
            .any(|rekey| matches!(rekey.outcome, crate::receipts::RekeyOutcome::Replaced(_)))
    );
    let mut changed_from = Vec::new();
    for rekey in relevant {
        assert_eq!(rekey.as_of_edges, landmark.as_of_edges);
        assert_eq!(rekey.equalities.len(), 1);
        let pair = rekey.equalities[0];
        assert_eq!(pair.column, ColumnId::new(0));
        assert_eq!(
            (pair.left.sort, pair.right.sort),
            (ReplaySortId::new(78), ReplaySortId::new(78))
        );
        assert_eq!(
            (pair.left.term, pair.right.term),
            (crate::ReplayTermId::MISSING, crate::ReplayTermId::MISSING)
        );
        assert_eq!(pair.right.raw, Value::new(100_000));
        changed_from.push(pair.left.raw.index());
        let support = view.explain_raw_equality_support_at(
            crate::RawEqualityEndpoint {
                sort: pair.left.sort,
                raw: pair.left.raw,
            },
            crate::RawEqualityEndpoint {
                sort: pair.right.sort,
                raw: pair.right.raw,
            },
            landmark.as_of_edges,
            rekey.equality_position,
        )?;
        assert!(!support.applied.is_empty());
        assert!(view.fact_terms(rekey.fact)?[0] != crate::ReplayTermId::MISSING);
    }
    changed_from.sort_unstable();
    assert_eq!(changed_from, [1_000_000, 1_000_001]);
    Ok(())
}

#[test]
fn causal_receipt_rebuild_rekeys_with_exact_landmark_and_noop_preserves_fact() {
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
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(79);
    receipts
        .register_table_layout(rebuilt, &[Some(sort), None])
        .unwrap();
    let old = Value::new(20);
    let new = Value::new(10);
    let old_term = receipts.intern_literal(sort, ReplayLiteral::Internal(20), old);
    let new_term = receipts.intern_literal(sort, ReplayLiteral::Internal(10), new);
    db.stage_source_row(
        rebuilt,
        &[old, Value::new(0)],
        &[old_term, crate::ReplayTermId::MISSING],
        SourceRef::Synthetic(79),
    )
    .unwrap();
    assert!(db.merge_all());
    let prior_fact = committed_fact_id(&db, rebuilt, old);

    db.set_causal_wave(CausalWave::new(1));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&receipts, 79, CausalWave::new(1)),
        sort,
        old,
        new,
        Value::new(1),
    );
    assert!(db.merge_all());

    db.set_causal_wave(CausalWave::new(2));
    assert!(db.apply_rebuild(uf, &[rebuilt], Value::new(2)));
    db.finalize_causal_wave();
    let rebuilt_fact = committed_fact_id(&db, rebuilt, new);
    assert_eq!(
        rebuilt_fact, prior_fact,
        "a pure rekey must preserve the immutable logical FactId"
    );
    receipts
        .with_view(|view| {
            assert_eq!(
                view.fact_terms(rebuilt_fact)?.as_ref(),
                &[old_term, crate::ReplayTermId::MISSING],
                "a pure rekey cannot rewrite the fact's historical creation syntax"
            );
            assert_eq!(view.totals().facts, 1, "a pure rekey creates no fact");
            let crate::ReceiptCauseRef::Cause(source) = view.fact(rebuilt_fact)?.cause else {
                panic!("source fact lost its source cause")
            };
            assert!(matches!(
                view.cause(source)?,
                crate::RawReceiptCause::Source(SourceRef::Synthetic(79))
            ));
            assert_eq!(view.totals().rekeys, 1);
            let applied = view.applied_equality(crate::AppliedEqualityId::new(1))?;
            let rekey = view.rekey_at(crate::HistoryPosition::new(applied.position.get() + 1))?;
            assert_eq!(rekey.fact, prior_fact);
            assert_eq!(rekey.table, rebuilt);
            assert_eq!(rekey.wave, CausalWave::new(2));
            assert_eq!(rekey.as_of_edges, crate::EqualityEdgeCount::new(1));
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
            assert_eq!(rekey.outcome, crate::receipts::RekeyOutcome::Moved);
            let projected = view.project_applied_equality(crate::AppliedEqualityId::new(1))?;
            assert_eq!(
                (projected.left.term, projected.right.term),
                (old_term, new_term)
            );
            let counters = view.counters();
            assert_eq!(counters.rebuild_causes, 1);
            assert_eq!(counters.rebuild_equalities, 1);
            assert!(counters.rebuild_bytes > 0);
            Ok(())
        })
        .unwrap();

    db.set_causal_wave(CausalWave::new(3));
    assert!(
        !db.apply_rebuild(uf, &[rebuilt], Value::new(3)),
        "an already-canonical row is a rebuild no-op"
    );
    db.finalize_causal_wave();
    assert_eq!(committed_fact_id(&db, rebuilt, new), rebuilt_fact);
    receipts
        .with_view(|view| {
            assert_eq!(view.totals().facts, 1);
            assert_eq!(view.counters().rebuild_causes, 1);
            assert_eq!(view.counters().rebuild_equalities, 1);
            Ok(())
        })
        .unwrap();
    let later_left = Value::new(40);
    let later_right = Value::new(30);
    receipts.intern_literal(sort, ReplayLiteral::Internal(40), later_left);
    receipts.intern_literal(sort, ReplayLiteral::Internal(30), later_right);
    db.set_causal_wave(CausalWave::new(4));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&receipts, 80, CausalWave::new(4)),
        sort,
        later_left,
        later_right,
        Value::new(4),
    );
    assert!(db.merge_all());
    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            let first = view.applied_equality(crate::AppliedEqualityId::new(1))?;
            let rekey = view.rekey_at(crate::HistoryPosition::new(first.position.get() + 1))?;
            assert_eq!(
                rekey.as_of_edges,
                crate::EqualityEdgeCount::new(1),
                "a later equality edge cannot justify an earlier table rekey"
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
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(7900);
    receipts
        .register_table_layout(rebuilt, &[Some(sort), None])
        .unwrap();
    receipts.register_table_key_columns(rebuilt, 1).unwrap();
    receipts
        .register_table_kind(rebuilt, ReplayTableKind::ValueFunction)
        .unwrap();
    let a = Value::new(20);
    let c = Value::new(10);
    let ta = receipts.intern_literal(sort, ReplayLiteral::Internal(1), a);
    let tb = receipts.intern_literal(sort, ReplayLiteral::Internal(2), Value::new(200));
    let tc = receipts.intern_literal(sort, ReplayLiteral::Internal(3), c);
    let site = |term| {
        receipts.register_term_origin(TermOriginSpec {
            sort,
            term: Arc::new(TermTemplate::Static { term }),
        })
    };
    let wave = CausalWave::new(1);
    db.set_causal_wave(wave);
    let (proposal_left, proposal_left_term, proposal_right, proposal_right_term) =
        if reverse_equality_endpoints {
            (c, tc, a, ta)
        } else {
            (a, ta, c, tc)
        };
    let equality = receipts
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
            empty_rule_cause(&receipts, 7900, wave),
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

    let cutoff = receipts.equality_edge_count().unwrap();
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
    let occurrences = [(
        crate::CheckEndpointOccurrence::FactCell(crate::FactCellRef {
            fact,
            column: ColumnId::new(0),
        }),
        crate::CheckEndpointOccurrence::Current,
    )];
    receipts
        .record_check_root(7900, wave, &[fact], &[(left, right)], &occurrences, cutoff)
        .unwrap();
    receipts
        .record_check_root(
            7900,
            CausalWave::new(99),
            &[fact],
            &[(left, right)],
            &occurrences,
            cutoff,
        )
        .unwrap();
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            let equality = view.applied_equality(crate::AppliedEqualityId::new(1))?;
            let fact_record = view.fact(fact)?;
            let root = view.check_root(7900)?;
            let crate::ReceiptCauseRef::Cause(source) = fact_record.cause else {
                panic!("expected a source cause")
            };
            assert!(matches!(
                view.cause(source)?,
                crate::RawReceiptCause::Source(SourceRef::Synthetic(7900))
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
            assert!(support.causes.is_empty());
            assert_eq!(support.rekeys.as_ref(), &[rekey_position]);
            assert!(
                view.explain_equality_support_at(
                    left,
                    right,
                    crate::EqualityEdgeCount::new(0),
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
fn trusted_exact_occurrences_extend_from_both_native_roots() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let child_sort = ReplaySortId::new(7902);
    let sort = ReplaySortId::new(7903);
    let child = receipts.intern_literal(child_sort, ReplayLiteral::Internal(7), Value::new(7));
    let a = Value::new(50);
    let b = Value::new(40);
    let x = Value::new(30);
    let y = Value::new(20);
    let z = Value::new(10);
    let shared = receipts
        .intern_call(sort, ReplayOpId::new(7902), &[child], a)
        .unwrap();
    assert_eq!(
        receipts
            .intern_call(sort, ReplayOpId::new(7902), &[child], b)
            .unwrap(),
        shared,
        "the production Call interner certifies the same term at both raw ids"
    );
    for (op, raw) in [(7903, x), (7904, y), (7905, z)] {
        receipts
            .intern_call(sort, ReplayOpId::new(op), &[child], raw)
            .unwrap();
    }

    for (wave, left, right) in [(1, a, x), (2, b, y), (3, a, z)] {
        let wave = CausalWave::new(wave);
        db.set_causal_wave(wave);
        stage_test_union(
            &db,
            uf,
            empty_rule_cause(&receipts, 7903 + wave.get() as u32, wave),
            sort,
            left,
            right,
            Value::new(wave.get() as u32),
        );
        assert!(db.merge_all());
    }
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            let first_root = view.explain_raw_equality_support_at(
                crate::RawEqualityEndpoint { sort, raw: x },
                crate::RawEqualityEndpoint { sort, raw: z },
                crate::EqualityEdgeCount::new(3),
                view_end_position(view),
            )?;
            assert_eq!(
                first_root.applied.as_ref(),
                &[crate::AppliedEqualityId::new(3)]
            );
            let second_root = view.explain_raw_equality_support_at(
                crate::RawEqualityEndpoint { sort, raw: b },
                crate::RawEqualityEndpoint { sort, raw: y },
                crate::EqualityEdgeCount::new(3),
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
    let receipts = db.enable_causal_receipts();
    let child_sort = ReplaySortId::new(791);
    let result_sort = ReplaySortId::new(792);
    let op = ReplayOpId::new(791);
    receipts
        .register_table_layout(constructor, &[Some(child_sort), Some(result_sort), None])
        .unwrap();
    receipts
        .register_table_constructor(
            constructor,
            ReplayConstructorSpec::new(result_sort, op, [child_sort]),
        )
        .unwrap();

    let wrong_child = Value::new(7910);
    let exact_child = Value::new(7911);
    let canonical_child = Value::new(7909);
    let output = Value::new(7920);
    let wrong_child_term =
        receipts.intern_literal(child_sort, ReplayLiteral::Internal(7910), wrong_child);
    let exact_child_term =
        receipts.intern_literal(child_sort, ReplayLiteral::Internal(7911), exact_child);
    receipts.intern_literal(child_sort, ReplayLiteral::Internal(7909), canonical_child);
    let wrong_call = receipts
        .intern_call(result_sort, op, &[wrong_child_term], output)
        .unwrap();
    let exact_call = receipts
        .intern_call(result_sort, op, &[exact_child_term], output)
        .unwrap();
    assert_ne!(wrong_call, exact_call);
    assert_eq!(
        receipts.lookup_term(result_sort, output),
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
    db.finalize_causal_wave();
    let prior_fact = committed_fact_id(&db, constructor, exact_child);

    db.set_causal_wave(CausalWave::new(1));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&receipts, 791, CausalWave::new(1)),
        child_sort,
        exact_child,
        canonical_child,
        Value::new(1),
    );
    assert!(db.merge_all());
    db.set_causal_wave(CausalWave::new(2));
    assert!(db.apply_rebuild(uf, &[constructor], Value::new(2)));
    db.finalize_causal_wave();

    let rebuilt_fact = committed_fact_id(&db, constructor, canonical_child);
    assert_eq!(rebuilt_fact, prior_fact);
    receipts
        .with_view(|view| {
            assert_eq!(
                view.fact_terms(rebuilt_fact)?.as_ref(),
                exact_terms.as_slice()
            );
            let crate::ReceiptCauseRef::Cause(source) = view.fact(rebuilt_fact)?.cause else {
                panic!("pure rekeying replaced the source creator")
            };
            assert!(matches!(
                view.cause(source)?,
                crate::RawReceiptCause::Source(SourceRef::Synthetic(791))
            ));
            let equality = view.applied_equality(crate::AppliedEqualityId::new(1))?;
            let rekey = view.rekey_at(crate::HistoryPosition::new(equality.position.get() + 1))?;
            assert_eq!(rekey.fact, prior_fact);
            assert_eq!(rekey.outcome, crate::receipts::RekeyOutcome::Moved);
            assert_eq!(rekey.equalities.len(), 1);
            assert_eq!(rekey.equalities[0].left.raw, exact_child);
            assert_eq!(rekey.equalities[0].right.raw, canonical_child);
            Ok(())
        })
        .unwrap();
}

#[test]
fn causal_receipt_rebuild_collision_records_exact_congruence() {
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
    let receipts = db.enable_causal_receipts();
    receipts
        .register_table_layout(rebuilt, &[Some(sort), Some(sort), None])
        .unwrap();
    register_test_merge_origins(
        &receipts,
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
    let old_key_term = receipts.intern_literal(sort, ReplayLiteral::Internal(30), old_key);
    let target_key_term = receipts.intern_literal(sort, ReplayLiteral::Internal(20), target_key);
    let old_output_term = receipts.intern_literal(sort, ReplayLiteral::Internal(300), old_output);
    let target_output_term =
        receipts.intern_literal(sort, ReplayLiteral::Internal(200), target_output);
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

    db.set_causal_wave(CausalWave::new(1));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&receipts, 82, CausalWave::new(1)),
        sort,
        old_key,
        target_key,
        Value::new(1),
    );
    assert!(db.merge_all());

    db.set_causal_wave(CausalWave::new(2));
    assert!(db.apply_rebuild(uf, &[rebuilt], Value::new(2)));
    db.finalize_causal_wave();

    assert_eq!(
        committed_fact_id(&db, rebuilt, target_key),
        target_fact,
        "a congruence collision with no row merge keeps the target fact version"
    );
    assert!(
        receipts
            .with_view(|view| view.fact(old_fact).map(drop))
            .is_ok()
    );
    assert_eq!(native_uf_root(&db, uf, old_output), target_output);
    receipts
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, 2);
            let equality = view.project_applied_equality(crate::AppliedEqualityId::new(2))?;
            let (dependencies, equalities) = test_congruence_dependencies(view, &equality.reason)?;
            assert_eq!(dependencies.facts, [target_fact, old_fact]);
            assert!(dependencies.rules.is_empty());
            assert_eq!(equalities.as_of_edges, crate::EqualityEdgeCount::new(1));
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
            assert_eq!(equality.wave, CausalWave::new(2));
            assert_eq!(equality.left.term, target_output_term);
            assert_eq!(equality.right.term, old_output_term);
            assert_eq!(
                view.totals().matches,
                1,
                "congruence must not invent a synthetic rule match"
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn causal_receipt_same_wave_rebuild_congruence_is_exact_across_threshold() {
    for row_count in [2, 20_001] {
        with_same_wave_rebuild_collision(row_count, 2, move |view, old_facts| {
            assert_same_wave_rebuild_collision(view, old_facts, row_count, 2)
        });
    }
}

#[test]
fn causal_receipt_serial_rebuild_congruence_keeps_only_applied_leaves() {
    with_same_wave_rebuild_collision(20_001, 3, |view, old_facts| {
        assert_same_wave_rebuild_collision(view, old_facts, 20_001, 3)
    });
}

#[test]
fn causal_receipt_rebuild_records_only_changed_columns_in_table_order() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let rebuilt = db.add_table(
        SortedWritesTable::new(
            3,
            4,
            Some(ColumnId::new(3)),
            vec![ColumnId::new(1), ColumnId::new(0)],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right);
                false
            }),
        ),
        iter::once(uf),
        iter::empty(),
    );
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(84);
    receipts
        .register_table_layout(rebuilt, &[Some(sort), Some(sort), Some(sort), None])
        .unwrap();
    let old_a = Value::new(60);
    let new_a = Value::new(50);
    let old_b = Value::new(40);
    let new_b = Value::new(30);
    let unchanged = Value::new(7);
    let old_a_term = receipts.intern_literal(sort, ReplayLiteral::Internal(60), old_a);
    let new_a_term = receipts.intern_literal(sort, ReplayLiteral::Internal(50), new_a);
    let old_b_term = receipts.intern_literal(sort, ReplayLiteral::Internal(40), old_b);
    let new_b_term = receipts.intern_literal(sort, ReplayLiteral::Internal(30), new_b);
    let unchanged_term = receipts.intern_literal(sort, ReplayLiteral::Internal(7), unchanged);
    db.stage_source_row(
        rebuilt,
        &[old_a, old_b, unchanged, Value::new(0)],
        &[
            old_a_term,
            old_b_term,
            unchanged_term,
            crate::ReplayTermId::MISSING,
        ],
        SourceRef::Synthetic(84),
    )
    .unwrap();
    assert!(db.merge_all());
    let prior_fact = committed_fact_id_for_key(&db, rebuilt, &[old_a, old_b, unchanged]);

    db.set_causal_wave(CausalWave::new(1));
    let cause = empty_rule_cause(&receipts, 84, CausalWave::new(1));
    stage_test_union(&db, uf, cause, sort, old_a, new_a, Value::new(1));
    let cause = empty_rule_cause(&receipts, 85, CausalWave::new(1));
    stage_test_union(&db, uf, cause, sort, old_b, new_b, Value::new(1));
    assert!(db.merge_all());

    db.set_causal_wave(CausalWave::new(2));
    assert!(db.apply_rebuild(uf, &[rebuilt], Value::new(2)));
    db.finalize_causal_wave();
    let rebuilt_fact = committed_fact_id_for_key(&db, rebuilt, &[new_a, new_b, unchanged]);
    assert_eq!(rebuilt_fact, prior_fact);
    receipts
        .with_view(|view| {
            let fact = view.fact(rebuilt_fact)?;
            let crate::ReceiptCauseRef::Cause(source) = fact.cause else {
                panic!("expected source cause")
            };
            assert!(matches!(
                view.cause(source)?,
                crate::RawReceiptCause::Source(SourceRef::Synthetic(84))
            ));
            let second = view.applied_equality(crate::AppliedEqualityId::new(2))?;
            let rekey = view.rekey_at(crate::HistoryPosition::new(second.position.get() + 1))?;
            assert_eq!(rekey.wave, CausalWave::new(2));
            assert_eq!(rekey.outcome, crate::receipts::RekeyOutcome::Moved);
            assert_eq!(rekey.as_of_edges, crate::EqualityEdgeCount::new(2));
            for (id, expected) in [(1, (old_a_term, new_a_term)), (2, (old_b_term, new_b_term))] {
                let projected = view.project_applied_equality(crate::AppliedEqualityId::new(id))?;
                assert_eq!((projected.left.term, projected.right.term), expected);
            }
            assert_eq!(
                rekey.equalities,
                &[
                    crate::TypedCellEquality {
                        column: ColumnId::new(0),
                        left: crate::EqualityEndpoint {
                            sort,
                            term: crate::ReplayTermId::MISSING,
                            raw: old_a,
                        },
                        right: crate::EqualityEndpoint {
                            sort,
                            term: crate::ReplayTermId::MISSING,
                            raw: new_a,
                        },
                    },
                    crate::TypedCellEquality {
                        column: ColumnId::new(1),
                        left: crate::EqualityEndpoint {
                            sort,
                            term: crate::ReplayTermId::MISSING,
                            raw: old_b,
                        },
                        right: crate::EqualityEndpoint {
                            sort,
                            term: crate::ReplayTermId::MISSING,
                            raw: new_b,
                        },
                    },
                ]
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn causal_receipt_rebuild_keeps_raw_typed_rekey_and_projects_fact_occurrence_lazily() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let rebuilt = db.add_table(
        SortedWritesTable::new(
            1,
            2,
            Some(ColumnId::new(1)),
            vec![ColumnId::new(0)],
            Box::new(|_, _, _, _| false),
        ),
        iter::once(uf),
        iter::empty(),
    );
    let receipts = db.enable_causal_receipts();
    let table_sort = ReplaySortId::new(86);
    let uf_sort = ReplaySortId::new(87);
    receipts
        .register_table_layout(rebuilt, &[Some(table_sort), None])
        .unwrap();
    let old = Value::new(90);
    let new = Value::new(80);
    let old_table_term = receipts.intern_literal(table_sort, ReplayLiteral::Internal(90), old);
    receipts.intern_literal(uf_sort, ReplayLiteral::Internal(90), old);
    receipts.intern_literal(uf_sort, ReplayLiteral::Internal(80), new);
    db.stage_source_row(
        rebuilt,
        &[old, Value::new(0)],
        &[old_table_term, crate::ReplayTermId::MISSING],
        SourceRef::Synthetic(86),
    )
    .unwrap();
    assert!(db.merge_all());
    let prior_fact = committed_fact_id(&db, rebuilt, old);

    db.set_causal_wave(CausalWave::new(1));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&receipts, 86, CausalWave::new(1)),
        uf_sort,
        old,
        new,
        Value::new(1),
    );
    assert!(db.merge_all());
    db.set_causal_wave(CausalWave::new(2));
    assert!(db.apply_rebuild(uf, &[rebuilt], Value::new(2)));
    assert_eq!(
        native_uf_root(&db, uf, old),
        new,
        "native rebuilding remains independent of cold receipt projection"
    );
    assert!(db.get_table(rebuilt).get_row(&[old]).is_none());
    assert_eq!(committed_fact_id(&db, rebuilt, new), prior_fact);
    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            assert_eq!(
                view.fact_terms(prior_fact)?.as_ref(),
                &[old_table_term, crate::ReplayTermId::MISSING]
            );
            let rekey = view.rekey_at(view_end_position(view))?;
            assert_eq!(
                (rekey.fact, rekey.outcome, rekey.as_of_edges),
                (
                    prior_fact,
                    crate::receipts::RekeyOutcome::Moved,
                    crate::EqualityEdgeCount::new(1)
                )
            );
            let pair = &rekey.equalities[0];
            assert_eq!(
                (pair.column, pair.left.sort, pair.left.term, pair.left.raw),
                (
                    ColumnId::new(0),
                    table_sort,
                    crate::ReplayTermId::MISSING,
                    old
                )
            );
            assert_eq!(
                (pair.right.sort, pair.right.term, pair.right.raw),
                (table_sort, crate::ReplayTermId::MISSING, new)
            );
            let cell = view.fact_cell_at(
                crate::FactCellRef {
                    fact: prior_fact,
                    column: ColumnId::new(0),
                },
                rekey.position,
            )?;
            assert_eq!(
                cell.created,
                crate::EqualityEndpoint {
                    sort: table_sort,
                    term: old_table_term,
                    raw: old
                }
            );
            assert_eq!(
                cell.endpoint,
                crate::EqualityEndpoint {
                    sort: table_sort,
                    term: old_table_term,
                    raw: new
                }
            );
            assert_eq!(cell.rekeys.as_ref(), &[rekey.position]);
            Ok(())
        })
        .unwrap();
}

#[test]
fn causal_receipt_same_batch_rebuild_collision_is_atomic_and_retryable() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let rebuilt = db.add_table(
        SortedWritesTable::new(
            1,
            2,
            Some(ColumnId::new(1)),
            vec![ColumnId::new(0)],
            Box::new(|_, _, _, _| false),
        ),
        iter::once(uf),
        iter::empty(),
    );
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(89);
    receipts
        .register_table_layout(rebuilt, &[Some(sort), None])
        .unwrap();

    let first_old = Value::new(100);
    let second_old = Value::new(80);
    let target = Value::new(70);
    for value in [first_old, second_old, target] {
        receipts.intern_literal(sort, ReplayLiteral::Internal(value.index() as u64), value);
    }
    let stage_source = |db: &Database, value: Value, source| {
        db.stage_source_row(
            rebuilt,
            &[value, Value::new(0)],
            &[
                receipts.lookup_term(sort, value).unwrap(),
                crate::ReplayTermId::MISSING,
            ],
            SourceRef::Synthetic(source),
        )
        .unwrap();
    };
    stage_source(&db, first_old, 890);
    stage_source(&db, second_old, 891);
    assert!(db.merge_all());
    let first_fact = committed_fact_id(&db, rebuilt, first_old);
    let second_fact = committed_fact_id(&db, rebuilt, second_old);

    db.set_causal_wave(CausalWave::new(1));
    let union_cause = empty_rule_cause(&receipts, 89, CausalWave::new(1));
    for old in [first_old, second_old] {
        stage_test_union(&db, uf, union_cause, sort, old, target, Value::new(1));
    }
    assert!(db.merge_all());
    db.set_causal_wave(CausalWave::new(2));

    let failed = catch_unwind(AssertUnwindSafe(|| {
        db.apply_rebuild(uf, &[rebuilt], Value::new(2));
    }));
    assert!(failed.is_err());
    assert_eq!(committed_fact_id(&db, rebuilt, first_old), first_fact);
    assert_eq!(committed_fact_id(&db, rebuilt, second_old), second_fact);
    assert!(db.get_table(rebuilt).get_row(&[target]).is_none());
    assert!(
        !db.merge_all(),
        "failed preflight published a native mutation"
    );

    register_test_merge_origins(
        &receipts,
        rebuilt,
        &[
            MergeOriginSelector::Prior { column: 0 },
            MergeOriginSelector::Unsupported,
        ],
    );
    assert!(db.apply_rebuild(uf, &[rebuilt], Value::new(2)));
    assert!(db.get_table(rebuilt).get_row(&[first_old]).is_none());
    assert!(db.get_table(rebuilt).get_row(&[second_old]).is_none());
    assert!(db.get_table(rebuilt).get_row(&[target]).is_some());

    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            assert_eq!(view.totals().rekeys, 2);
            let support = view.explain_equality_support_at(
                crate::EqualityEndpoint {
                    sort,
                    term: receipts.lookup_term(sort, first_old).unwrap(),
                    raw: first_old,
                },
                crate::EqualityEndpoint {
                    sort,
                    term: receipts.lookup_term(sort, target).unwrap(),
                    raw: target,
                },
                crate::EqualityEdgeCount::new(2),
                view_end_position(view),
            )?;
            assert!(
                support
                    .facts
                    .iter()
                    .all(|fact| *fact == first_fact || *fact == second_fact)
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn causal_receipt_rebuild_abort_is_atomic_across_target_tables() {
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
    let receipts = db.enable_causal_receipts();
    let table_sort = ReplaySortId::new(91);
    let uf_sort = table_sort;
    for table in [first, second] {
        receipts
            .register_table_layout(table, &[Some(table_sort), None])
            .unwrap();
    }
    register_test_merge_origins(
        &receipts,
        first,
        &[
            MergeOriginSelector::Prior { column: 0 },
            MergeOriginSelector::Unsupported,
        ],
    );
    register_test_merge_origins(
        &receipts,
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
        receipts.intern_literal(
            table_sort,
            ReplayLiteral::Internal(raw),
            Value::new(raw as u32),
        );
    }
    for raw in [120, 110, 90, 80] {
        receipts.intern_literal(
            uf_sort,
            ReplayLiteral::Internal(raw),
            Value::new(raw as u32),
        );
    }
    for (table, value, source) in [(first, first_old, 910), (second, second_old, 911)] {
        db.stage_source_row(
            table,
            &[value, Value::new(0)],
            &[
                receipts.lookup_term(table_sort, value).unwrap(),
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
            receipts.lookup_term(table_sort, second_new).unwrap(),
            crate::ReplayTermId::MISSING,
        ],
        SourceRef::Synthetic(913),
    )
    .unwrap();
    assert!(db.merge_all());
    let first_fact = committed_fact_id(&db, first, first_old);
    let second_fact = committed_fact_id(&db, second, second_old);
    let second_canonical_fact = committed_fact_id(&db, second, second_new);

    db.set_causal_wave(CausalWave::new(1));
    let union_cause = empty_rule_cause(&receipts, 91, CausalWave::new(1));
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
    db.set_causal_wave(CausalWave::new(2));

    let failed = catch_unwind(AssertUnwindSafe(|| {
        db.apply_rebuild(uf, &[first, second], Value::new(2));
    }));
    assert!(failed.is_err());

    db.stage_source_row(
        first,
        &[recovery, Value::new(2)],
        &[
            receipts.lookup_term(table_sort, recovery).unwrap(),
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

    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            assert_eq!(view.counters().rebuild_causes, 0);
            assert_eq!(view.counters().rebuild_equalities, 0);
            Ok(())
        })
        .unwrap();
}

#[test]
fn causal_receipt_same_id_refresh_without_typed_dependency_is_a_noop() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let rebuilt = db.add_table(
        SortedWritesTable::new(
            1,
            2,
            Some(ColumnId::new(1)),
            vec![ColumnId::new(0)],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right);
                false
            }),
        ),
        iter::once(uf),
        iter::empty(),
    );
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(88);
    receipts
        .register_table_layout(rebuilt, &[Some(sort), None])
        .unwrap();
    let key = Value::new(8);
    let key_term = receipts.intern_literal(sort, ReplayLiteral::Internal(8), key);
    db.stage_source_row(
        rebuilt,
        &[key, Value::new(0)],
        &[key_term, crate::ReplayTermId::MISSING],
        SourceRef::Synthetic(88),
    )
    .unwrap();
    assert!(db.merge_all());
    let fact = committed_fact_id(&db, rebuilt, key);

    let mut summary = crate::ContainerRebuildSummary::default();
    summary.note_dirty_id(key);
    assert!(!db.refresh_rows_for_values(&[rebuilt], &summary, Value::new(1)));
    assert_eq!(committed_fact_id(&db, rebuilt, key), fact);
    assert!(!db.merge_all());
}

#[test]
fn ordinary_table_rebuild_uses_no_receipt_sidecars() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let rebuilt = db.add_table(
        SortedWritesTable::new(
            1,
            2,
            Some(ColumnId::new(1)),
            vec![ColumnId::new(0)],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right);
                false
            }),
        ),
        iter::once(uf),
        iter::empty(),
    );
    let old = Value::new(12);
    let new = Value::new(11);
    db.with_execution_state(|state| state.stage_insert(rebuilt, &[old, Value::new(0)]));
    assert!(db.merge_all());
    let mut buffer = db.new_buffer(uf);
    buffer.stage_insert(&[old, new, Value::new(1)]);
    drop(buffer);
    assert!(db.merge_all());
    assert!(db.apply_rebuild(uf, &[rebuilt], Value::new(2)));
    assert!(db.get_table(rebuilt).get_row(&[new]).is_some());
    assert_eq!(
        db.get_table(rebuilt)
            .as_any()
            .downcast_ref::<SortedWritesTable>()
            .unwrap()
            .causal_sidecar_bytes(),
        0
    );
}

#[test]
fn typed_union_forest_is_immutable_across_native_path_compression_and_redundancy() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(80);
    let a = Value::new(30);
    let b = Value::new(20);
    let c = Value::new(10);
    let a_term = receipts.intern_literal(sort, ReplayLiteral::Internal(30), a);
    let b_term = receipts.intern_literal(sort, ReplayLiteral::Internal(20), b);
    let c_term = receipts.intern_literal(sort, ReplayLiteral::Internal(10), c);

    db.set_causal_wave(CausalWave::new(1));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&receipts, 80, CausalWave::new(1)),
        sort,
        a,
        b,
        Value::new(1),
    );
    assert!(db.merge_all());

    db.set_causal_wave(CausalWave::new(2));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&receipts, 81, CausalWave::new(2)),
        sort,
        b,
        c,
        Value::new(2),
    );
    assert!(db.merge_all());

    db.set_causal_wave(CausalWave::new(3));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&receipts, 82, CausalWave::new(3)),
        sort,
        a,
        c,
        Value::new(3),
    );
    assert!(
        !db.merge_all(),
        "the third proposal is redundant in the native UF"
    );
    db.finalize_causal_wave();

    receipts.with_view(|view| {
    assert_eq!(view.totals().applied_equalities, 2);
    assert_eq!(view.counters().redundant_unions, 1);
    assert!(matches!(view.applied_equality(crate::AppliedEqualityId::new(1))?.reason, crate::EqualityReason::RuleUnion(id) if view.matched(id)?.rule == 80));
    assert!(matches!(view.applied_equality(crate::AppliedEqualityId::new(2))?.reason, crate::EqualityReason::RuleUnion(id) if view.matched(id)?.rule == 81));
    let endpoint = |term, raw| crate::EqualityEndpoint { sort, term, raw };
    assert_eq!(
        view
            .explain_equality_support_at(
                endpoint(a_term, a),
                endpoint(c_term, c),
                crate::EqualityEdgeCount::new(2),
                view_end_position(view),
            )?.applied.as_ref(),
        &[crate::AppliedEqualityId::new(1), crate::AppliedEqualityId::new(2)]
    );
    assert_eq!(
        view
            .explain_equality_support_at(
                endpoint(b_term, b),
                endpoint(c_term, c),
                crate::EqualityEdgeCount::new(2),
                view_end_position(view),
            )?.applied.as_ref(),
        &[crate::AppliedEqualityId::new(2)]
    );
    assert!(
        view
            .explain_equality_support_at(
                endpoint(a_term, a),
                endpoint(c_term, c),
                crate::EqualityEdgeCount::new(1),
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
        (CausalWave::new(1), b, a)
    );
    assert_eq!(
        (second.wave, second.native_parent, second.native_child),
        (CausalWave::new(2), c, b)
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
        let receipts = db.enable_causal_receipts();
        let sort = ReplaySortId::new(90);
        let left = Value::new(4);
        let right = Value::new(5);
        if case == "wrong-sort" {
            let other = ReplaySortId::new(91);
            receipts.intern_literal(other, ReplayLiteral::Internal(4), left);
            receipts.intern_literal(other, ReplayLiteral::Internal(5), right);
        } else if case == "token-row-mismatch" {
            receipts.intern_literal(sort, ReplayLiteral::Internal(4), left);
            receipts.intern_literal(sort, ReplayLiteral::Internal(5), right);
        }
        db.set_causal_wave(CausalWave::new(1));
        let cause = empty_rule_cause(&receipts, 90, CausalWave::new(1));
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
                let proposal = receipts
                    .typed_equality_proposal(CausalWave::new(1), sort, left, right)
                    .unwrap();
                let mut buffer = db.new_buffer(uf);
                buffer.stage_typed_union(&[right, left, Value::new(1)], cause, proposal);
            } else {
                stage_test_union(&db, uf, cause, sort, left, right, Value::new(1));
            }
        }));
        assert!(failed.is_err(), "{case} staging must fail closed");
        assert!(!db.merge_all(), "{case} staging mutated the native UF");
        db.finalize_causal_wave();
        assert_eq!(native_uf_root(&db, uf, left), left);
        assert_eq!(native_uf_root(&db, uf, right), right);
        receipts
            .with_view(|view| {
                assert_eq!(view.totals().applied_equalities, 0);
                Ok(())
            })
            .unwrap();
    }
}

#[test]
fn forged_direct_rule_match_fails_before_native_union() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(901);
    let left = Value::new(9010);
    let right = Value::new(9011);
    receipts.intern_literal(sort, ReplayLiteral::Internal(9010), left);
    receipts.intern_literal(sort, ReplayLiteral::Internal(9011), right);

    let wave = CausalWave::new(1);
    db.set_causal_wave(wave);
    let proposal = receipts
        .typed_equality_proposal(wave, sort, left, right)
        .unwrap();
    {
        let mut buffer = db.new_buffer(uf);
        buffer.stage_typed_union(
            &[left, right, Value::new(1)],
            crate::ReceiptCauseRef::Rule(crate::RuleMatchId::new(999)),
            proposal,
        );
    }

    let failed = catch_unwind(AssertUnwindSafe(|| db.merge_all()));
    assert!(
        failed.is_err(),
        "a direct RuleMatchId without a durable observation must fail preflight"
    );
    assert_eq!(native_uf_root(&db, uf, left), left);
    assert_eq!(native_uf_root(&db, uf, right), right);
}

#[test]
fn direct_rule_match_cannot_cross_a_causal_wave() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(902);
    let left = Value::new(9020);
    let right = Value::new(9021);
    receipts.intern_literal(sort, ReplayLiteral::Internal(9020), left);
    receipts.intern_literal(sort, ReplayLiteral::Internal(9021), right);

    let first_wave = CausalWave::new(1);
    db.set_causal_wave(first_wave);
    let stale = empty_rule_cause(&receipts, 902, first_wave);
    db.finalize_causal_wave();

    let second_wave = CausalWave::new(2);
    db.set_causal_wave(second_wave);
    let proposal = receipts
        .typed_equality_proposal(second_wave, sort, left, right)
        .unwrap();
    {
        let mut buffer = db.new_buffer(uf);
        buffer.stage_typed_union(&[left, right, Value::new(2)], stale, proposal);
    }

    let failed = catch_unwind(AssertUnwindSafe(|| db.merge_all()));
    assert!(
        failed.is_err(),
        "a direct RuleMatchId from an earlier wave must fail preflight"
    );
    assert_eq!(native_uf_root(&db, uf, left), left);
    assert_eq!(native_uf_root(&db, uf, right), right);
}

#[test]
fn pending_rule_cause_cannot_cross_receipt_arenas() {
    let foreign = CausalReceipts::default();
    let wave = CausalWave::new(1);
    let observed = foreign.pending_rule_batch(903, wave, 0, &[], &[], 1);
    let foreign_cause =
        crate::DeferredEqualityCause::pending(foreign.pending_rule_cause(&observed, 0));

    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(903);
    let left = Value::new(9030);
    let right = Value::new(9031);
    receipts.intern_literal(sort, ReplayLiteral::Internal(9030), left);
    receipts.intern_literal(sort, ReplayLiteral::Internal(9031), right);
    db.set_causal_wave(wave);
    let proposal = receipts
        .typed_equality_proposal(wave, sort, left, right)
        .unwrap();
    {
        let mut buffer = db.new_buffer(uf);
        buffer.stage_typed_union_deferred(&[left, right, Value::new(1)], foreign_cause, proposal);
    }

    let failed = catch_unwind(AssertUnwindSafe(|| db.merge_all()));
    assert!(
        failed.is_err(),
        "a pending rule cause owned by another receipt arena must fail preflight"
    );
    assert_eq!(native_uf_root(&db, uf, left), left);
    assert_eq!(native_uf_root(&db, uf, right), right);
}

#[test]
fn pending_rule_cause_rejects_a_missing_same_arena_match() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let wave = CausalWave::new(1);
    let sort = ReplaySortId::new(904);
    let left = Value::new(9040);
    let right = Value::new(9041);
    receipts.intern_literal(sort, ReplayLiteral::Internal(9040), left);
    receipts.intern_literal(sort, ReplayLiteral::Internal(9041), right);
    db.set_causal_wave(wave);
    let forged = receipts.observed_match_batch_for_test(crate::RuleMatchId::new(999), 1, wave);
    let failed = catch_unwind(AssertUnwindSafe(|| receipts.pending_rule_cause(&forged, 0)));
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
    let receipts = db.enable_causal_receipts();
    let wave = CausalWave::new(1);
    let first = receipts.pending_rule_batch(905, wave, 0, &[], &[], 1);
    let _adjacent = receipts.pending_rule_batch(906, wave, 0, &[], &[], 1);
    let sort = ReplaySortId::new(905);
    let left = Value::new(9050);
    let right = Value::new(9051);
    receipts.intern_literal(sort, ReplayLiteral::Internal(9050), left);
    receipts.intern_literal(sort, ReplayLiteral::Internal(9051), right);
    db.set_causal_wave(wave);
    let failed = catch_unwind(AssertUnwindSafe(|| receipts.pending_rule_cause(&first, 1)));
    assert!(
        failed.is_err(),
        "a lane beyond its observed batch must not alias an adjacent match"
    );
    assert_eq!(native_uf_root(&db, uf, left), left);
    assert_eq!(native_uf_root(&db, uf, right), right);
}

#[test]
fn redundant_rule_unions_discard_pending_matches_without_promotion() {
    const REDUNDANT: usize = 100_000;
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let marker = db.add_table(
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
    let receipts = db.enable_causal_receipts();
    receipts.register_table_layout(marker, &[None]).unwrap();
    let sort = ReplaySortId::new(191);
    let left = Value::new(1910);
    let right = Value::new(1911);
    receipts.intern_literal(sort, ReplayLiteral::Internal(1910), left);
    receipts.intern_literal(sort, ReplayLiteral::Internal(1911), right);

    let first_wave = CausalWave::new(1);
    db.set_causal_wave(first_wave);
    let first = empty_rule_cause(&receipts, 191, first_wave);
    stage_test_union(&db, uf, first, sort, left, right, Value::new(1));
    assert!(db.merge_all());
    db.finalize_causal_wave();

    let second_wave = CausalWave::new(2);
    db.set_causal_wave(second_wave);
    let pending = receipts.pending_rule_batch(192, second_wave, 0, &[], &[], REDUNDANT);
    let proposal = receipts
        .typed_equality_proposal(second_wave, sort, left, right)
        .unwrap();
    {
        let mut buffer = db.new_buffer(uf);
        for lane in 0..REDUNDANT {
            buffer.stage_typed_union_deferred(
                &[left, right, Value::new(2)],
                crate::DeferredEqualityCause::pending(receipts.pending_rule_cause(&pending, lane)),
                proposal,
            );
        }
    }
    assert!(!db.merge_all());
    db.stage_source_row(
        marker,
        &[Value::new(1920)],
        &[crate::ReplayTermId::MISSING],
        SourceRef::Synthetic(192),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            let applied = view.applied_equality(crate::AppliedEqualityId::new(1))?;
            let effective = applied.reason.rule_match().unwrap();
            assert_eq!(
                view.matched(effective)?.rule,
                191,
                "only the seed observation reaches an applied effect"
            );
            assert_eq!(view.counters().redundant_unions, REDUNDANT as u64);
            assert_eq!(view.totals().facts, 1);
            assert_eq!(
                view.fact(crate::FactId::new(1))?.position.get(),
                view.applied_equality(crate::AppliedEqualityId::new(1))?
                    .position
                    .get()
                    + 1,
                "redundant proposals must allocate no global history positions"
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn observed_match_ids_are_dense_before_effect_reachability() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(200);
    let left = Value::new(2000);
    let right = Value::new(2001);
    receipts.intern_literal(sort, ReplayLiteral::Internal(2000), left);
    receipts.intern_literal(sort, ReplayLiteral::Internal(2001), right);

    let wave = CausalWave::new(1);
    db.set_causal_wave(wave);
    let observed = receipts.pending_rule_batch(200, wave, 0, &[], &[], 4);
    let proposal = receipts
        .typed_equality_proposal(wave, sort, left, right)
        .unwrap();
    {
        let mut buffer = db.new_buffer(uf);
        buffer.stage_typed_union_deferred(
            &[left, right, Value::new(1)],
            crate::DeferredEqualityCause::pending(receipts.pending_rule_cause(&observed, 3)),
            proposal,
        );
    }
    assert!(db.merge_all());
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            assert_eq!(
                view.counters().observed_matches,
                4,
                "every normal-return native input lane must have one dense observation"
            );
            assert_eq!(
                view.totals().matches,
                4,
                "the borrowed view retains all dense observations"
            );
            let equality = view.applied_equality(crate::AppliedEqualityId::new(1))?;
            assert_eq!(
                equality.reason.rule_match(),
                Some(crate::RuleMatchId::new(4)),
                "only the effective fourth observation should be reachable from an effect"
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn one_firing_fact_and_union_share_direct_match_without_rule_cause_node() {
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
    let receipts = db.enable_causal_receipts();
    receipts.register_table_layout(fact_table, &[None]).unwrap();
    let origin = receipts.register_row_origin(RowOriginSpec {
        table: fact_table,
        cells: [None].into(),
    });
    let sort = ReplaySortId::new(201);
    let left = Value::new(2010);
    let right = Value::new(2011);
    receipts.intern_literal(sort, ReplayLiteral::Internal(2010), left);
    receipts.intern_literal(sort, ReplayLiteral::Internal(2011), right);

    let wave = CausalWave::new(1);
    db.set_causal_wave(wave);
    let observed = receipts.pending_rule_batch(201, wave, 0, &[], &[], 1);
    let cause = crate::DeferredEqualityCause::pending(receipts.pending_rule_cause(&observed, 0));
    {
        let mut facts = db.new_buffer(fact_table);
        facts.stage_insert_deferred_with_origin(&[Value::new(2012)], cause.clone(), origin);
    }
    let proposal = receipts
        .typed_equality_proposal(wave, sort, left, right)
        .unwrap();
    {
        let mut unions = db.new_buffer(uf);
        unions.stage_typed_union_deferred(&[left, right, Value::new(1)], cause, proposal);
    }
    assert!(db.merge_all());
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            assert_eq!(view.totals().matches, 1);
            let matched = crate::RuleMatchId::new(1);
            assert_eq!(
                cause_rule_match(view.fact(crate::FactId::new(1))?.cause),
                Some(matched)
            );
            assert_eq!(
                view.applied_equality(crate::AppliedEqualityId::new(1))?
                    .reason
                    .rule_match(),
                Some(matched)
            );
            assert_eq!(
                view.totals().causes,
                0,
                "a direct rule match must not allocate a generic cause node"
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn noop_constructor_collisions_copy_no_prior_terms_or_promote_matches() {
    const COLLISIONS: usize = 100_000;
    let mut db = Database::default();
    let table = db.add_table_named(
        SortedWritesTable::new(
            1,
            3,
            None,
            vec![],
            Box::new(|_, prior, incoming, _| {
                assert_eq!(prior, incoming, "constructor collision changed its row");
                false
            }),
        ),
        "NoopConstructor".into(),
        iter::empty(),
        iter::empty(),
    );
    let receipts = db.enable_causal_receipts();
    let child_sort = ReplaySortId::new(192);
    let result_sort = ReplaySortId::new(193);
    let op = ReplayOpId::new(192);
    receipts
        .register_table_layout(table, &[Some(child_sort), Some(result_sort), None])
        .unwrap();
    receipts
        .register_table_constructor(
            table,
            ReplayConstructorSpec::new(result_sort, op, [child_sort]),
        )
        .unwrap();
    receipts
        .register_table_merge_origins(
            table,
            &[
                MergeOriginSelector::Incoming { column: 0 },
                MergeOriginSelector::NativeMin {
                    incoming_column: 1,
                    prior_column: 1,
                },
                MergeOriginSelector::Unsupported,
            ],
        )
        .unwrap();
    let child_value = Value::new(1920);
    let output_value = Value::new(1921);
    let child = receipts.intern_literal(child_sort, ReplayLiteral::Internal(1920), child_value);
    let output = receipts
        .intern_call(result_sort, op, &[child], output_value)
        .unwrap();
    let row = [child_value, output_value, Value::new(0)];
    let terms = [child, output, crate::ReplayTermId::MISSING];
    db.stage_source_row(table, &row, &terms, SourceRef::Synthetic(192))
        .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();

    let wave = CausalWave::new(1);
    db.set_causal_wave(wave);
    let pending = receipts.pending_rule_batch(192, wave, 0, &[], &[], COLLISIONS);
    let origin = receipts.install_source_row(table, &row, &terms).unwrap();
    {
        let mut updates = db.new_buffer(table);
        for lane in 0..COLLISIONS {
            updates.stage_insert_deferred_with_origin(
                &row,
                crate::DeferredEqualityCause::pending(receipts.pending_rule_cause(&pending, lane)),
                origin,
            );
        }
    }
    assert!(!db.merge_all());
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            assert_eq!(view.totals().facts, 1, "only the source row is effective");
            assert_eq!(view.totals().applied_equalities, 0);
            Ok(())
        })
        .unwrap();
}

#[test]
fn effective_pending_union_effects_share_one_promoted_match() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(193);
    let values = [Value::new(1930), Value::new(1931), Value::new(1932)];
    for (index, value) in values.into_iter().enumerate() {
        receipts.intern_literal(sort, ReplayLiteral::Internal(index as u64), value);
    }
    let wave = CausalWave::new(1);
    db.set_causal_wave(wave);
    let pending = receipts.pending_rule_batch(193, wave, 0, &[], &[], 1);
    {
        let mut buffer = db.new_buffer(uf);
        for (left, right) in [(values[0], values[1]), (values[1], values[2])] {
            let proposal = receipts
                .typed_equality_proposal(wave, sort, left, right)
                .unwrap();
            buffer.stage_typed_union_deferred(
                &[left, right, Value::new(1)],
                crate::DeferredEqualityCause::pending(receipts.pending_rule_cause(&pending, 0)),
                proposal,
            );
        }
    }
    assert!(db.merge_all());
    db.finalize_causal_wave();

    receipts.with_view(|view| {
        assert_eq!(view.totals().matches, 1);
        assert_eq!(view.totals().applied_equalities, 2);
        for id in 1..=2 {
            assert!(matches!(view.applied_equality(crate::AppliedEqualityId::new(id))?.reason, crate::EqualityReason::RuleUnion(rule) if rule == crate::RuleMatchId::new(1)));
        }
        Ok(())
    }).unwrap();
}

#[test]
fn pending_batch_preflight_failure_is_atomic() {
    let mut db = Database::default();
    let premise_table = db.add_table_named(
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
        "AtomicPendingPremise".into(),
        iter::empty(),
        iter::empty(),
    );
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(199);
    receipts
        .register_table_layout(premise_table, &[Some(sort)])
        .unwrap();
    let premise_value = Value::new(1990);
    let premise_term = receipts.intern_literal(sort, ReplayLiteral::Internal(1990), premise_value);
    db.stage_source_row(
        premise_table,
        &[premise_value],
        &[premise_term],
        SourceRef::Synthetic(199),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();
    let valid_fact = committed_fact_id(&db, premise_table, premise_value);
    let missing_fact = FactId::new(valid_fact.get() + 1);
    let before = receipts
        .with_view(|view| Ok((view.totals(), view.counters())))
        .unwrap();

    let values = [
        Value::new(1991),
        Value::new(1992),
        Value::new(1993),
        Value::new(1994),
    ];
    for value in values {
        receipts.intern_literal(sort, ReplayLiteral::Internal(value.index() as u64), value);
    }
    let wave = CausalWave::new(1);
    db.set_causal_wave(wave);
    let sources = [crate::receipts::ReplayBindingSource::Premise {
        representative: crate::receipts::PremiseOccurrence {
            premise: 0,
            column: 0,
        },
        occurrences: [crate::receipts::PremiseOccurrence {
            premise: 0,
            column: 0,
        }]
        .into(),
    }];
    let failed = catch_unwind(AssertUnwindSafe(|| {
        receipts.pending_rule_batch(199, wave, 1, &sources, &[valid_fact, missing_fact], 2)
    }));
    assert!(failed.is_err());
    for value in values {
        assert_eq!(native_uf_root(&db, uf, value), value);
    }

    let after = receipts
        .with_view(|view| Ok((view.totals(), view.counters())))
        .unwrap();
    assert_eq!(after, before);
}

#[test]
fn promoted_match_ids_follow_native_batch_order_not_union_order() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(194);
    let values = [
        Value::new(1940),
        Value::new(1941),
        Value::new(1942),
        Value::new(1943),
    ];
    for (index, value) in values.into_iter().enumerate() {
        receipts.intern_literal(sort, ReplayLiteral::Internal(index as u64), value);
    }
    let wave = CausalWave::new(1);
    db.set_causal_wave(wave);
    let earlier = receipts.pending_rule_batch(194, wave, 0, &[], &[], 1);
    let later = receipts.pending_rule_batch(195, wave, 0, &[], &[], 1);
    {
        let mut buffer = db.new_buffer(uf);
        for (batch, left, right) in [
            (&later, values[2], values[3]),
            (&earlier, values[0], values[1]),
        ] {
            let proposal = receipts
                .typed_equality_proposal(wave, sort, left, right)
                .unwrap();
            buffer.stage_typed_union_deferred(
                &[left, right, Value::new(1)],
                crate::DeferredEqualityCause::pending(receipts.pending_rule_cause(batch, 0)),
                proposal,
            );
        }
    }
    assert!(db.merge_all());
    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            let cited = (1..=view.totals().applied_equalities)
                .map(|id| view.applied_equality(crate::AppliedEqualityId::new(id)))
                .map(|event| event.map(|event| event.reason.rule_match().unwrap()))
                .collect::<Result<std::collections::BTreeSet<_>, _>>()?;
            let rules = cited
                .into_iter()
                .map(|id| view.matched(id).map(|matched| matched.rule))
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
    let receipts = db.enable_causal_receipts();
    for table in [tail_input, full_input] {
        receipts
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
        receipts.intern_literal(
            TEST_REPLAY_SORT,
            ReplayLiteral::Internal(endpoint.index() as u64),
            endpoint,
        );
    }
    let mut source = 0_u64;
    for (table, count) in [(tail_input, 1), (full_input, FULL_BATCH)] {
        for value in 0..count {
            let raw = Value::from_usize(value);
            let term = receipts.intern_literal(
                TEST_REPLAY_SORT,
                ReplayLiteral::Internal(10_000 + source),
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
    db.finalize_causal_wave();

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
        action.build_with_receipts(
            description,
            RuleReceiptSpec::new(rule, [atom], iter::empty::<crate::Variable>()),
        );
    }
    let rules = rules.build();
    db.set_causal_wave(CausalWave::new(1));
    assert!(db.run_rule_set(&rules, ReportLevel::TimeOnly).changed);
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, 2);
            assert_eq!(view.counters().redundant_unions, (FULL_BATCH - 1) as u64);
            let effective = (1..=view.totals().applied_equalities)
                .map(|id| view.applied_equality(crate::AppliedEqualityId::new(id)))
                .map(|event| {
                    event.and_then(|event| view.matched(event.reason.rule_match().unwrap()))
                })
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
    let receipts = db.enable_causal_receipts();
    receipts
        .register_table_layout(target, &[Some(sort), Some(sort)])
        .unwrap();
    receipts
        .register_table_layout(proposal, &[Some(sort), Some(sort)])
        .unwrap();
    register_test_merge_origins(
        &receipts,
        target,
        &[
            MergeOriginSelector::Prior { column: 0 },
            MergeOriginSelector::Prior { column: 1 },
        ],
    );
    let key = Value::new(1);
    let prior = Value::new(30);
    let incoming = Value::new(20);
    let key_term = receipts.intern_literal(sort, ReplayLiteral::Internal(1), key);
    let prior_term = receipts.intern_literal(sort, ReplayLiteral::Internal(30), prior);
    let incoming_term = receipts.intern_literal(sort, ReplayLiteral::Internal(20), incoming);
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
    db.finalize_causal_wave();
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
    action.build_with_receipts(
        "merge-union",
        RuleReceiptSpec::new(100, [atom], [matched_key, matched_value]),
    );
    let rules = rules.build();

    db.set_causal_wave(CausalWave::new(1));
    assert!(db.run_rule_set(&rules, ReportLevel::TimeOnly).changed);
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            let equality = view.project_applied_equality(crate::AppliedEqualityId::new(1))?;
            let (rule_match, recorded_prior) = match &equality.reason {
                crate::EqualityReason::MergeFn { cause } => {
                    let dependencies = test_cause_dependencies(view, *cause)?;
                    assert_eq!(dependencies.rules.len(), 1);
                    assert_eq!(dependencies.facts.len(), 1);
                    (dependencies.rules[0], dependencies.facts[0])
                }
                ref other => panic!("expected exact MergeFn reason, got {other:?}"),
            };
            assert_eq!(recorded_prior, prior_fact);
            let matched = view.matched(rule_match)?;
            assert_eq!(matched.rule, 100);
            assert_eq!(matched.premises.as_ref(), &[proposal_fact]);
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
    let receipts = db.enable_causal_receipts();
    receipts
        .register_table_layout(target, &[Some(sort), Some(sort)])
        .unwrap();
    let key = Value::new(1);
    let prior = Value::new(30);
    let incoming = Value::new(20);
    let key_term = receipts.intern_literal(sort, ReplayLiteral::Internal(1), key);
    let prior_term = receipts.intern_literal(sort, ReplayLiteral::Internal(30), prior);
    let incoming_term = receipts.intern_literal(sort, ReplayLiteral::Internal(20), incoming);

    db.stage_source_row(
        target,
        &[key, prior],
        &[key_term, prior_term],
        SourceRef::Synthetic(108),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();
    let prior_fact = committed_fact_id(&db, target, key);

    db.stage_source_row(
        target,
        &[key, incoming],
        &[key_term, incoming_term],
        SourceRef::Synthetic(109),
    )
    .unwrap();
    let failed = catch_unwind(AssertUnwindSafe(|| db.merge_all()));
    assert!(failed.is_err());

    let row = db
        .get_table(target)
        .get_row(&[key])
        .expect("the parent table must be restored after rejection");
    assert_eq!(row.vals[1], prior);
    assert_eq!(committed_fact_id(&db, target, key), prior_fact);
    assert_eq!(native_uf_root(&db, uf, prior), prior);
    assert_eq!(native_uf_root(&db, uf, incoming), incoming);
}

#[test]
fn causal_receipts_record_same_term_native_alias_without_equality_edge() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let child_sort = ReplaySortId::new(109);
    let container_sort = ReplaySortId::new(110);
    let op = ReplayOpId::new(109);
    let child = Value::new(7);
    let left = Value::new(30);
    let right = Value::new(20);
    let child_term = receipts.intern_literal(child_sort, ReplayLiteral::Internal(7), child);
    certify_test_replay_call(&receipts, 10_900, container_sort, op);
    certify_test_replay_call(&receipts, 11_000, container_sort, ReplayOpId::new(110));
    let call = receipts
        .intern_call(container_sort, op, &[child_term], left)
        .unwrap();
    for value in [left, right] {
        assert_eq!(
            receipts
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

    let wave = CausalWave::new(1);
    db.set_causal_wave(wave);
    let cutoff = receipts.equality_edge_count().unwrap();
    let journal = crate::receipts::ContainerAnchorJournal::default();
    let (cause, proposal) = receipts
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
    db.finalize_causal_wave();

    let alias_child = receipts.with_view(|view| {
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
        receipts.equality_edge_count().unwrap(),
        crate::EqualityEdgeCount::new(cutoff.get() + 1),
        "the historical cutoff counts every applied native union, including aliases"
    );

    // The component mirror must survive the native-only alias. A later real
    // equality reached through the former child id still joins the shared
    // structural term into the ordinary immutable explanation forest.
    let other = Value::new(10);
    let other_term = receipts
        .intern_call(container_sort, ReplayOpId::new(110), &[child_term], other)
        .unwrap();
    receipts
        .install_test_container_anchor(
            container_sort,
            TypeId::of::<Vec<Value>>(),
            &[child_sort],
            other,
            other_term,
        )
        .unwrap();
    let wave = CausalWave::new(2);
    db.set_causal_wave(wave);
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&receipts, 110, wave),
        container_sort,
        alias_child,
        other,
        Value::new(2),
    );
    assert!(db.merge_all());
    db.finalize_causal_wave();

    receipts
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
                    crate::EqualityEdgeCount::new(2),
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
fn trusted_exact_term_catches_up_two_simultaneous_native_occurrences() {
    let mut db = Database::default();
    let receipts = db.enable_causal_receipts();
    let mut uf = DisplacedTable::default();
    uf.enable_causal_receipts();
    let child_sort = ReplaySortId::new(111);
    let container_sort = ReplaySortId::new(112);
    let child = receipts.intern_literal(child_sort, ReplayLiteral::Internal(7), Value::new(7));
    for (rule, op) in [(11_100, 111), (11_200, 112), (11_300, 113)] {
        certify_test_replay_call(&receipts, rule, container_sort, ReplayOpId::new(op));
    }
    let a = Value::new(40);
    let b = Value::new(30);
    let x = Value::new(20);
    let y = Value::new(10);
    let shared = receipts
        .intern_call(container_sort, ReplayOpId::new(111), &[child], a)
        .unwrap();
    receipts
        .install_trusted_value_term(container_sort, b, shared)
        .unwrap();
    receipts
        .intern_call(container_sort, ReplayOpId::new(112), &[child], x)
        .unwrap();
    receipts
        .intern_call(container_sort, ReplayOpId::new(113), &[child], y)
        .unwrap();

    let wave = CausalWave::new(1);
    db.set_causal_wave(wave);
    let ax = receipts
        .typed_equality_proposal(wave, container_sort, a, x)
        .unwrap();
    let by = receipts
        .typed_equality_proposal(wave, container_sort, b, y)
        .unwrap();
    {
        let mut buffer = uf.new_buffer();
        buffer.stage_typed_union(
            &[a, x, Value::new(1)],
            empty_rule_cause(&receipts, 111, wave),
            ax,
        );
        buffer.stage_typed_union(
            &[b, y, Value::new(1)],
            empty_rule_cause(&receipts, 112, wave),
            by,
        );
    }
    let changed = {
        let mut state = ExecutionState::new(db.read_only_view(), Default::default());
        uf.merge(&mut state)
    };
    assert!(changed.added);
    // These endpoints are explicitly staged as Exact current-value aliases,
    // so the recorder may trust the pre-event mapping of the same Call to
    // both raw ids. Fact/Cell terms do not receive this catch-up privilege.
    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, 2);
            assert_eq!(
                view.explain_equality_support_at(
                    crate::EqualityEndpoint {
                        sort: container_sort,
                        term: shared,
                        raw: a,
                    },
                    crate::EqualityEndpoint {
                        sort: container_sort,
                        term: receipts.lookup_term(container_sort, x).unwrap(),
                        raw: x,
                    },
                    crate::EqualityEdgeCount::new(2),
                    view_end_position(view),
                )?
                .applied
                .as_ref(),
                &[crate::AppliedEqualityId::new(1)]
            );
            assert_eq!(
                view.explain_equality_support_at(
                    crate::EqualityEndpoint {
                        sort: container_sort,
                        term: shared,
                        raw: b,
                    },
                    crate::EqualityEndpoint {
                        sort: container_sort,
                        term: receipts.lookup_term(container_sort, y).unwrap(),
                        raw: y,
                    },
                    crate::EqualityEdgeCount::new(2),
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
fn native_alias_preserves_an_existing_logical_component() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let child_sort = ReplaySortId::new(113);
    let container_sort = ReplaySortId::new(114);
    let child = receipts.intern_literal(child_sort, ReplayLiteral::Internal(7), Value::new(7));
    certify_test_replay_call(&receipts, 11_400, container_sort, ReplayOpId::new(114));
    certify_test_replay_call(&receipts, 11_500, container_sort, ReplayOpId::new(115));
    let left = Value::new(30);
    let alias = Value::new(20);
    let other = Value::new(10);
    let shared = receipts
        .intern_call(container_sort, ReplayOpId::new(114), &[child], left)
        .unwrap();
    for value in [left, alias] {
        receipts
            .install_test_container_anchor(
                container_sort,
                TypeId::of::<Vec<Value>>(),
                &[child_sort],
                value,
                shared,
            )
            .unwrap();
    }
    let other_term = receipts
        .intern_call(container_sort, ReplayOpId::new(115), &[child], other)
        .unwrap();
    receipts
        .install_test_container_anchor(
            container_sort,
            TypeId::of::<Vec<Value>>(),
            &[child_sort],
            other,
            other_term,
        )
        .unwrap();

    let first_wave = CausalWave::new(1);
    db.set_causal_wave(first_wave);
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&receipts, 114, first_wave),
        container_sort,
        left,
        other,
        Value::new(1),
    );
    assert!(db.merge_all());

    let second_wave = CausalWave::new(2);
    db.set_causal_wave(second_wave);
    let proposal = receipts
        .typed_equality_proposal(second_wave, container_sort, left, alias)
        .unwrap();
    let cutoff = receipts.equality_edge_count().unwrap();
    let journal = crate::receipts::ContainerAnchorJournal::default();
    let (cause, _) = receipts
        .container_canonicalization_cause(
            &journal,
            TypeId::of::<Vec<Value>>(),
            second_wave,
            left,
            alias,
            cutoff,
        )
        .unwrap();
    {
        let mut buffer = db.new_buffer(uf);
        buffer.stage_typed_union(&[left, alias, Value::new(2)], cause.id().into(), proposal);
    }
    assert!(db.merge_all());
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, 2);
            let alias_event = view.project_applied_equality(crate::AppliedEqualityId::new(2))?;
            assert_eq!(
                (alias_event.left.term, alias_event.right.term),
                (shared, shared)
            );
            let crate::EqualityReason::Congruence { as_of_edges, .. } = alias_event.reason else {
                panic!("native alias lost its causal landmark")
            };
            assert_eq!(as_of_edges, crate::EqualityEdgeCount::new(1));
            assert_eq!(
                view.explain_equality_support_at(
                    crate::EqualityEndpoint {
                        sort: container_sort,
                        term: shared,
                        raw: alias,
                    },
                    crate::EqualityEndpoint {
                        sort: container_sort,
                        term: other_term,
                        raw: other,
                    },
                    crate::EqualityEdgeCount::new(2),
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
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(214);
    let child_sort = ReplaySortId::new(215);
    let child = receipts.intern_literal(child_sort, ReplayLiteral::Internal(1), Value::new(1));
    let left = Value::new(80);
    let right = Value::new(100);
    let other = Value::new(90);
    let prior_right_term = receipts
        .intern_call(sort, ReplayOpId::new(214), &[child], right)
        .unwrap();
    let other_term = receipts
        .intern_call(sort, ReplayOpId::new(215), &[child], other)
        .unwrap();
    let shared = receipts
        .intern_call(sort, ReplayOpId::new(216), &[child], left)
        .unwrap();
    receipts
        .register_table_layout(fact_table, &[Some(sort)])
        .unwrap();
    receipts
        .register_table_merge_origins(fact_table, &[MergeOriginSelector::Incoming { column: 0 }])
        .unwrap();
    db.stage_source_row(fact_table, &[right], &[shared], SourceRef::Synthetic(214))
        .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();
    let prior_fact = committed_fact_id_for_key(&db, fact_table, &[right]);
    let site = |term| {
        receipts.register_term_origin(TermOriginSpec {
            sort,
            term: Arc::new(TermTemplate::Static { term }),
        })
    };
    let prior_right_site = site(prior_right_term);
    let other_site = site(other_term);
    let incoming_origin = receipts.register_row_origin(RowOriginSpec {
        table: fact_table,
        cells: [Some(Arc::new(TermTemplate::Static { term: shared }))].into(),
    });

    let first_wave = CausalWave::new(1);
    db.set_causal_wave(first_wave);
    let first = receipts
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
            empty_rule_cause(&receipts, 214, first_wave),
            first,
        );
    }
    assert!(db.merge_all());

    let second_wave = CausalWave::new(2);
    db.set_causal_wave(second_wave);
    let bridge = receipts
        .typed_merge_equality_proposal(
            second_wave,
            sort,
            right,
            left,
            fact_table,
            0,
            prior_fact,
            crate::receipts::RowOriginRef::Site(incoming_origin),
        )
        .unwrap();
    let incoming = empty_rule_cause(&receipts, 215, second_wave);
    let merge_cause =
        receipts.pending_merge_cause(crate::DeferredEqualityCause::ready(incoming), prior_fact);
    {
        let mut buffer = db.new_buffer(uf);
        buffer.stage_typed_union_deferred(&[right, left, Value::new(2)], merge_cause, bridge);
    }
    assert!(db.merge_all());
    db.finalize_causal_wave();

    receipts
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
                crate::EqualityEdgeCount::new(1),
                first.position,
            )?;
            assert_eq!(
                first_support.applied.as_ref(),
                &[crate::AppliedEqualityId::new(1)]
            );
            assert!(first_support.facts.is_empty() && first_support.causes.is_empty());
            let crate::EqualityReason::RuleUnion(first_match) = first.reason else {
                panic!("first equality lost its rule attribution")
            };
            assert_eq!(view.matched(first_match)?.rule, 214);
            let crate::EqualityReason::MergeFn { cause } = second.reason else {
                panic!("same-term bridge lost its merge attribution")
            };
            let dependencies = test_cause_dependencies(view, cause)?;
            assert_eq!(dependencies.facts, [prior_fact]);
            assert_eq!(dependencies.rules.len(), 1);
            assert_eq!(view.matched(dependencies.rules[0])?.rule, 215);
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
                    crate::EqualityEdgeCount::new(2),
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
fn witnessed_same_term_singletons_remain_distinct_occurrence_leaves() {
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
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(2170);
    let child_sort = ReplaySortId::new(2171);
    let child = receipts.intern_literal(child_sort, ReplayLiteral::Internal(1), Value::new(1));
    let incoming_raw = Value::new(80);
    let prior_raw = Value::new(100);
    let shared = receipts
        .intern_call(sort, ReplayOpId::new(2170), &[child], incoming_raw)
        .unwrap();
    receipts
        .register_table_layout(fact_table, &[Some(sort)])
        .unwrap();
    receipts
        .register_table_merge_origins(fact_table, &[MergeOriginSelector::Incoming { column: 0 }])
        .unwrap();
    db.stage_source_row(
        fact_table,
        &[prior_raw],
        &[shared],
        SourceRef::Synthetic(2170),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();
    let prior_fact = committed_fact_id_for_key(&db, fact_table, &[prior_raw]);
    let incoming_origin = receipts.register_row_origin(RowOriginSpec {
        table: fact_table,
        cells: [Some(Arc::new(TermTemplate::Static { term: shared }))].into(),
    });

    let wave = CausalWave::new(1);
    db.set_causal_wave(wave);
    let proposal = receipts
        .typed_merge_equality_proposal(
            wave,
            sort,
            prior_raw,
            incoming_raw,
            fact_table,
            0,
            prior_fact,
            crate::receipts::RowOriginRef::Site(incoming_origin),
        )
        .unwrap();
    let incoming = empty_rule_cause(&receipts, 2171, wave);
    let cause =
        receipts.pending_merge_cause(crate::DeferredEqualityCause::ready(incoming), prior_fact);
    {
        let mut buffer = db.new_buffer(uf);
        buffer.stage_typed_union_deferred(
            &[prior_raw, incoming_raw, Value::new(1)],
            cause,
            proposal,
        );
    }
    assert!(db.merge_all());
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            let equality = view.project_applied_equality(crate::AppliedEqualityId::new(1))?;
            assert_eq!((equality.left.term, equality.right.term), (shared, shared));
            assert_ne!(equality.left.raw, equality.right.raw);
            let support = view.explain_equality_support_at(
                crate::EqualityEndpoint {
                    sort,
                    term: shared,
                    raw: prior_raw,
                },
                crate::EqualityEndpoint {
                    sort,
                    term: shared,
                    raw: incoming_raw,
                },
                crate::EqualityEdgeCount::new(1),
                equality.position,
            )?;
            assert_eq!(
                support.applied.as_ref(),
                &[crate::AppliedEqualityId::new(1)]
            );
            assert!(support.facts.is_empty());
            let crate::EqualityReason::MergeFn { cause } = equality.reason else {
                panic!("same-term bridge lost its merge attribution")
            };
            assert_eq!(test_cause_dependencies(view, cause)?.facts, [prior_fact]);
            Ok(())
        })
        .unwrap();
}

#[test]
fn same_term_native_bridge_without_fact_rule_witness_remains_raw_and_lazy() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(220);
    let first = Value::new(100);
    let second = Value::new(90);
    let outsider = Value::new(80);
    let first_term = receipts.intern_literal(sort, ReplayLiteral::Internal(1), first);
    let second_term = receipts.intern_literal(sort, ReplayLiteral::Internal(2), second);
    let shared = receipts.intern_literal(sort, ReplayLiteral::Internal(3), outsider);
    let site = |term| {
        receipts.register_term_origin(TermOriginSpec {
            sort,
            term: Arc::new(TermTemplate::Static { term }),
        })
    };

    db.set_causal_wave(CausalWave::new(1));
    let initial = receipts
        .typed_equality_proposal_from_sites(
            CausalWave::new(1),
            sort,
            first,
            site(first_term),
            second,
            site(second_term),
        )
        .unwrap();
    {
        let mut buffer = db.new_buffer(uf);
        buffer.stage_typed_union(
            &[first, second, Value::new(1)],
            empty_rule_cause(&receipts, 220, CausalWave::new(1)),
            initial,
        );
    }
    assert!(db.merge_all());

    db.set_causal_wave(CausalWave::new(2));
    let bridge = receipts
        .typed_equality_proposal_from_sites(
            CausalWave::new(2),
            sort,
            outsider,
            site(shared),
            first,
            site(shared),
        )
        .unwrap();
    {
        let mut buffer = db.new_buffer(uf);
        buffer.stage_typed_union(
            &[outsider, first, Value::new(2)],
            empty_rule_cause(&receipts, 221, CausalWave::new(2)),
            bridge,
        );
    }
    assert!(db.merge_all());
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, 2);
            let bridge = view.project_applied_equality(crate::AppliedEqualityId::new(2))?;
            assert_eq!((bridge.left.term, bridge.right.term), (shared, shared));
            assert_ne!(bridge.left.raw, bridge.right.raw);
            Ok(())
        })
        .unwrap();
}

#[test]
fn container_anchor_preserves_two_calls_for_one_same_sort_value() {
    let receipts = CausalReceipts::default();
    let child_sort = ReplaySortId::new(218);
    let container_sort = ReplaySortId::new(219);
    let op = ReplayOpId::new(218);
    let first_value = Value::new(2180);
    let second_value = Value::new(2181);
    let container_value = Value::new(2182);
    let first = receipts.intern_literal(child_sort, ReplayLiteral::Internal(2180), first_value);
    let second = receipts.intern_literal(child_sort, ReplayLiteral::Internal(2181), second_value);
    let replay = ReplayConstructorSpec::new(container_sort, op, [child_sort])
        .with_immediate_promotion()
        .with_container_type(TypeId::of::<Vec<Value>>());
    let site = |term| {
        receipts.register_term_origin(TermOriginSpec {
            sort: container_sort,
            term: Arc::new(TermTemplate::Call {
                sort: container_sort,
                op,
                children: [Arc::new(TermTemplate::Static { term })].into(),
            }),
        })
    };
    let first_site = site(first);
    let second_site = site(second);
    let first_call = receipts
        .intern_call(container_sort, op, &[first], container_value)
        .unwrap();
    let second_call = receipts
        .intern_call(container_sort, op, &[second], container_value)
        .unwrap();
    receipts
        .with_container_anchor_installer(first_site, &replay, |install| {
            install(&[], &[], &[first_value], container_value)
        })
        .unwrap()
        .unwrap();
    receipts
        .with_container_anchor_installer(second_site, &replay, |install| {
            install(&[], &[], &[second_value], container_value)
        })
        .unwrap()
        .unwrap();
    assert_eq!(
        receipts.lookup_term(container_sort, container_value),
        Some(first_call),
        "ordinary value lookup remains first-wins"
    );
    assert_eq!(
        receipts
            .test_container_anchors(container_sort, container_value)
            .as_slice(),
        &[first_call, second_call],
        "all exact structural versions remain available to container rebuild"
    );
}

#[test]
fn container_anchor_journal_transfers_both_sides_to_either_winner_atomically() {
    let receipts = CausalReceipts::default();
    let container_type = TypeId::of::<Vec<Value>>();

    for (case, incoming_wins) in [false, true].into_iter().enumerate() {
        let case = case as u32;
        let child_sort = ReplaySortId::new(230 + case * 2);
        let container_sort = ReplaySortId::new(231 + case * 2);
        let op = ReplayOpId::new(230 + case);
        let occupied = Value::new(2300 + case * 10);
        let incoming = Value::new(2301 + case * 10);
        let occupied_child = receipts.intern_literal(
            child_sort,
            ReplayLiteral::Internal(2300 + case as u64 * 10),
            Value::new(2310 + case * 10),
        );
        let incoming_child = receipts.intern_literal(
            child_sort,
            ReplayLiteral::Internal(2301 + case as u64 * 10),
            Value::new(2311 + case * 10),
        );
        let occupied_term = receipts
            .intern_call(container_sort, op, &[occupied_child], occupied)
            .unwrap();
        let incoming_term = receipts
            .intern_call(container_sort, op, &[incoming_child], incoming)
            .unwrap();
        receipts
            .install_test_container_anchor(
                container_sort,
                container_type,
                &[child_sort],
                occupied,
                occupied_term,
            )
            .unwrap();
        receipts
            .install_test_container_anchor(
                container_sort,
                container_type,
                &[child_sort],
                incoming,
                incoming_term,
            )
            .unwrap();

        let winner = if incoming_wins { incoming } else { occupied };
        let original_winner_anchors = receipts.test_container_anchors(container_sort, winner);
        let stage = |journal: &mut crate::receipts::ContainerAnchorJournal| {
            for source in [occupied, incoming] {
                receipts
                    .stage_container_anchor_transfer(journal, container_type, source, winner)
                    .unwrap();
            }
        };

        let mut aborted = crate::receipts::ContainerAnchorJournal::default();
        stage(&mut aborted);
        assert_eq!(
            receipts.test_container_anchors(container_sort, winner),
            original_winner_anchors,
            "a staged overlay must not mutate the committed anchor store"
        );
        drop(aborted);
        assert_eq!(
            receipts.test_container_anchors(container_sort, winner),
            original_winner_anchors,
            "dropping an aborted overlay must leave committed anchors unchanged"
        );

        let mut committed = crate::receipts::ContainerAnchorJournal::default();
        stage(&mut committed);
        receipts
            .validate_container_anchor_journal(&committed)
            .unwrap();
        receipts.publish_container_anchor_journal(committed);
        let mut expected = [occupied_term, incoming_term];
        expected.sort_unstable_by_key(|term| term.get());
        assert_eq!(
            receipts
                .test_container_anchors(container_sort, winner)
                .as_slice(),
            expected.as_slice(),
            "the chosen winner must retain both colliding structural histories"
        );
    }
}

#[test]
fn native_catch_up_reuses_existing_component_for_distinct_endpoint_terms() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let child_sort = ReplaySortId::new(115);
    let container_sort = ReplaySortId::new(116);
    let child = receipts.intern_literal(child_sort, ReplayLiteral::Internal(7), Value::new(7));
    let owner = Value::new(30);
    let alias = Value::new(20);
    let other = Value::new(10);
    let shared = receipts
        .intern_call(container_sort, ReplayOpId::new(116), &[child], owner)
        .unwrap();
    receipts
        .install_trusted_value_term(container_sort, alias, shared)
        .unwrap();
    let other_term = receipts
        .intern_call(container_sort, ReplayOpId::new(117), &[child], other)
        .unwrap();

    let first_wave = CausalWave::new(1);
    db.set_causal_wave(first_wave);
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&receipts, 116, first_wave),
        container_sort,
        owner,
        other,
        Value::new(1),
    );
    assert!(db.merge_all());

    // `alias` now presents `shared` from outside the native component that
    // already owns it. Joining it through the component's other endpoint is
    // native catch-up, not a second logical equality edge.
    let second_wave = CausalWave::new(2);
    db.set_causal_wave(second_wave);
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&receipts, 117, second_wave),
        container_sort,
        alias,
        other,
        Value::new(2),
    );
    assert!(db.merge_all());
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, 2);
            let catch_up = view.project_applied_equality(crate::AppliedEqualityId::new(2))?;
            assert_eq!(
                (catch_up.left.term, catch_up.right.term),
                (shared, other_term)
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn same_batch_native_catch_up_matches_durable_component_behavior() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let child_sort = ReplaySortId::new(117);
    let container_sort = ReplaySortId::new(118);
    let child = receipts.intern_literal(child_sort, ReplayLiteral::Internal(7), Value::new(7));
    let owner = Value::new(30);
    let alias = Value::new(20);
    let other = Value::new(10);
    let shared = receipts
        .intern_call(container_sort, ReplayOpId::new(118), &[child], owner)
        .unwrap();
    receipts
        .install_trusted_value_term(container_sort, alias, shared)
        .unwrap();
    let other_term = receipts
        .intern_call(container_sort, ReplayOpId::new(119), &[child], other)
        .unwrap();

    let wave = CausalWave::new(1);
    db.set_causal_wave(wave);
    let mut buffer = db.new_buffer(uf);
    for (rule, left, right) in [(118, owner, other), (119, alias, other)] {
        let proposal = receipts
            .typed_equality_proposal(wave, container_sort, left, right)
            .unwrap();
        buffer.stage_typed_union(
            &[left, right, Value::new(1)],
            empty_rule_cause(&receipts, rule, wave),
            proposal,
        );
    }
    drop(buffer);
    assert!(db.merge_all());
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, 2);
            let catch_up = view.project_applied_equality(crate::AppliedEqualityId::new(2))?;
            assert_eq!(
                (catch_up.left.term, catch_up.right.term),
                (shared, other_term)
            );
            Ok(())
        })
        .unwrap();
    assert_eq!(
        native_uf_root(&db, uf, owner),
        native_uf_root(&db, uf, alias)
    );
    assert_eq!(
        native_uf_root(&db, uf, owner),
        native_uf_root(&db, uf, other)
    );
}

#[test]
fn trusted_exact_term_catches_up_a_later_native_occurrence() {
    let mut db = Database::default();
    let receipts = db.enable_causal_receipts();
    let mut uf = DisplacedTable::default();
    uf.enable_causal_receipts();
    let child_sort = ReplaySortId::new(115);
    let container_sort = ReplaySortId::new(116);
    let child = receipts.intern_literal(child_sort, ReplayLiteral::Internal(7), Value::new(7));
    let a = Value::new(40);
    let b = Value::new(30);
    let x = Value::new(20);
    let y = Value::new(10);
    let shared = receipts
        .intern_call(container_sort, ReplayOpId::new(116), &[child], a)
        .unwrap();
    receipts
        .install_trusted_value_term(container_sort, b, shared)
        .unwrap();
    receipts
        .intern_call(container_sort, ReplayOpId::new(117), &[child], x)
        .unwrap();
    receipts
        .intern_call(container_sort, ReplayOpId::new(118), &[child], y)
        .unwrap();

    let first_wave = CausalWave::new(1);
    db.set_causal_wave(first_wave);
    {
        let mut buffer = uf.new_buffer();
        buffer.stage_typed_union(
            &[a, x, Value::new(1)],
            empty_rule_cause(&receipts, 116, first_wave),
            receipts
                .typed_equality_proposal(first_wave, container_sort, a, x)
                .unwrap(),
        );
    }
    let mut state = ExecutionState::new(db.read_only_view(), Default::default());
    assert!(uf.merge(&mut state).added);

    let second_wave = CausalWave::new(2);
    db.set_causal_wave(second_wave);
    {
        let mut buffer = uf.new_buffer();
        buffer.stage_typed_union(
            &[b, y, Value::new(2)],
            empty_rule_cause(&receipts, 117, second_wave),
            receipts
                .typed_equality_proposal(second_wave, container_sort, b, y)
                .unwrap(),
        );
    }
    let mut state = ExecutionState::new(db.read_only_view(), Default::default());
    assert!(uf.merge(&mut state).added);
    assert_eq!(uf.len(), 2);
    assert_eq!(uf.underlying_uf().find_naive(a), x);
    assert_eq!(uf.underlying_uf().find_naive(x), x);
    assert_eq!(uf.underlying_uf().find_naive(b), y);
    assert_eq!(uf.underlying_uf().find_naive(y), y);
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, 2);
            for id in 1..=2 {
                view.project_applied_equality(crate::AppliedEqualityId::new(id))?;
            }
            Ok(())
        })
        .unwrap();
}

#[test]
fn same_wave_merge_function_union_keeps_every_rule_proposal() {
    let mut db = Database::default();
    let receipts = db.enable_causal_receipts();
    let mut uf = DisplacedTable::default();
    uf.enable_causal_receipts();
    let sort = ReplaySortId::new(109);
    let left = Value::new(30);
    let right = Value::new(20);
    receipts.intern_literal(sort, ReplayLiteral::Internal(30), left);
    receipts.intern_literal(sort, ReplayLiteral::Internal(20), right);
    db.set_causal_wave(CausalWave::new(1));

    let first = empty_rule_cause(&receipts, 109, CausalWave::new(1));
    let second = empty_rule_cause(&receipts, 110, CausalWave::new(1));
    let third = empty_rule_cause(&receipts, 111, CausalWave::new(1));
    let mut causes = receipts.new_batch();
    let first_fold = causes.merge_drafts(second, first);
    let nested_fold = causes.merge_drafts(third, first_fold);
    causes.publish();

    {
        let mut buffer = uf.new_buffer();
        buffer.stage_typed_union(
            &[left, right, Value::new(1)],
            nested_fold,
            receipts
                .typed_equality_proposal(CausalWave::new(1), sort, left, right)
                .unwrap(),
        );
    }
    let mut state = ExecutionState::new(db.read_only_view(), Default::default());
    assert!(uf.merge(&mut state).added);
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            let equality = view.applied_equality(crate::AppliedEqualityId::new(1))?;
            let crate::EqualityReason::MergeFn { cause } = equality.reason else {
                panic!("same-wave merge-function union lost its proposal DAG")
            };
            let dependencies = test_cause_dependencies(view, cause)?;
            assert!(dependencies.facts.is_empty());
            let rules = dependencies
                .rules
                .iter()
                .map(|id| view.matched(*id).unwrap().rule)
                .collect::<Vec<_>>();
            assert_eq!(rules, [109, 110, 111]);
            Ok(())
        })
        .unwrap();
}

#[test]
fn deep_same_wave_merge_union_reuses_one_shared_cause_dag() {
    const PROPOSALS: usize = 512;
    let mut db = Database::default();
    let receipts = db.enable_causal_receipts();
    let mut uf = DisplacedTable::default();
    uf.enable_causal_receipts();
    let sort = ReplaySortId::new(112);
    db.set_causal_wave(CausalWave::new(1));

    let first = empty_rule_cause(&receipts, 0, CausalWave::new(1));
    let mut causes = receipts.new_batch();
    let mut root = first;
    let mut roots = Vec::with_capacity(PROPOSALS - 1);
    for rule in 1..PROPOSALS {
        let incoming = empty_rule_cause(&receipts, rule as u32, CausalWave::new(1));
        root = causes.merge_drafts(incoming, root);
        roots.push(root);
    }
    causes.publish();

    {
        let mut buffer = uf.new_buffer();
        for (index, cause) in roots.iter().copied().enumerate() {
            let left = Value::new((index * 2 + 1) as u32);
            let right = Value::new((index * 2 + 2) as u32);
            receipts.intern_literal(sort, ReplayLiteral::Internal(left.index() as u64), left);
            receipts.intern_literal(sort, ReplayLiteral::Internal(right.index() as u64), right);
            buffer.stage_typed_union(
                &[left, right, Value::new(1)],
                cause,
                receipts
                    .typed_equality_proposal(CausalWave::new(1), sort, left, right)
                    .unwrap(),
            );
        }
    }
    let mut state = ExecutionState::new(db.read_only_view(), Default::default());
    assert!(uf.merge(&mut state).added);
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, (PROPOSALS - 1) as u64);
            assert_eq!(view.totals().matches, PROPOSALS as u64);
            assert_eq!(
                view.totals().causes,
                (PROPOSALS - 1) as u64,
                "direct RuleMatchId causes leave only the shared merge nodes"
            );
            assert!(
                std::mem::size_of::<crate::EqualityReason>() <= 32,
                "each equality reason must retain only a constant-size shared root"
            );
            let crate::EqualityReason::MergeFn { cause } = view
                .applied_equality(crate::AppliedEqualityId::new((PROPOSALS - 1) as u64))?
                .reason
            else {
                panic!("deep merge prefix lost its shared exact cause")
            };
            let dependencies = test_cause_dependencies(view, cause)?;
            assert_eq!(dependencies.rules.len(), PROPOSALS);
            let rules = dependencies
                .rules
                .iter()
                .map(|rule| view.matched(*rule).unwrap().rule)
                .collect::<Vec<_>>();
            assert_eq!(rules, (0..PROPOSALS as u32).collect::<Vec<_>>());
            Ok(())
        })
        .unwrap();
}

#[test]
fn typed_union_rejects_decreasing_timestamp_before_native_mutation() {
    let mut db = Database::default();
    let receipts = db.enable_causal_receipts();
    let mut uf = DisplacedTable::default();
    uf.enable_causal_receipts();
    let sort = ReplaySortId::new(110);
    for raw in [30, 20, 10, 5] {
        receipts.intern_literal(sort, ReplayLiteral::Internal(raw), Value::new(raw as u32));
    }

    db.set_causal_wave(CausalWave::new(1));
    {
        let mut buffer = uf.new_buffer();
        buffer.stage_typed_union(
            &[Value::new(30), Value::new(20), Value::new(2)],
            empty_rule_cause(&receipts, 110, CausalWave::new(1)),
            receipts
                .typed_equality_proposal(CausalWave::new(1), sort, Value::new(30), Value::new(20))
                .unwrap(),
        );
    }
    let mut state = ExecutionState::new(db.read_only_view(), Default::default());
    assert!(uf.merge(&mut state).added);

    db.set_causal_wave(CausalWave::new(2));
    {
        let mut buffer = uf.new_buffer();
        buffer.stage_typed_union(
            &[Value::new(10), Value::new(5), Value::new(1)],
            empty_rule_cause(&receipts, 111, CausalWave::new(2)),
            receipts
                .typed_equality_proposal(CausalWave::new(2), sort, Value::new(10), Value::new(5))
                .unwrap(),
        );
    }
    let failed = catch_unwind(AssertUnwindSafe(|| {
        let mut state = ExecutionState::new(db.read_only_view(), Default::default());
        uf.merge(&mut state)
    }));
    assert!(failed.is_err());
    assert_eq!(
        uf.underlying_uf().find_naive(Value::new(10)),
        Value::new(10)
    );
    assert_eq!(uf.underlying_uf().find_naive(Value::new(5)), Value::new(5));
    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, 1);
            Ok(())
        })
        .unwrap();
}

#[test]
fn causal_wave_accepts_monotone_native_equality_timestamps() {
    let mut db = Database::default();
    let receipts = db.enable_causal_receipts();
    let wave = CausalWave::new(1);

    assert!(
        receipts
            .validate_equality_wave_timestamp(wave, Value::new(2))
            .is_ok()
    );
    assert!(
        receipts
            .validate_equality_wave_timestamp(wave, Value::new(3))
            .is_ok(),
        "native rebuild epochs remain inside one logical replay wave"
    );
    assert_eq!(
        receipts
            .validate_equality_wave_timestamp(wave, Value::new(2))
            .unwrap_err(),
        "equality timestamps decreased within one causal wave"
    );
    assert!(
        receipts
            .validate_equality_wave_timestamp(CausalWave::new(2), Value::new(4))
            .is_ok()
    );
}

#[test]
fn redundant_union_validates_existing_component_sort_before_counting() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let first_sort = ReplaySortId::new(120);
    let second_sort = ReplaySortId::new(121);
    let left = Value::new(30);
    let right = Value::new(20);
    for sort in [first_sort, second_sort] {
        receipts.intern_literal(sort, ReplayLiteral::Internal(30), left);
        receipts.intern_literal(sort, ReplayLiteral::Internal(20), right);
    }

    db.set_causal_wave(CausalWave::new(1));
    stage_test_union(
        &db,
        uf,
        empty_rule_cause(&receipts, 120, CausalWave::new(1)),
        first_sort,
        left,
        right,
        Value::new(1),
    );
    assert!(db.merge_all());

    db.set_causal_wave(CausalWave::new(2));
    let failed = catch_unwind(AssertUnwindSafe(|| {
        stage_test_union(
            &db,
            uf,
            empty_rule_cause(&receipts, 121, CausalWave::new(2)),
            second_sort,
            left,
            right,
            Value::new(2),
        );
    }));
    assert!(failed.is_err());
    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, 1);
            assert_eq!(view.counters().redundant_unions, 0);
            Ok(())
        })
        .unwrap();
}

#[test]
fn one_global_uf_accepts_disjoint_logical_sorts() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let first_sort = ReplaySortId::new(125);
    let second_sort = ReplaySortId::new(126);
    let pairs = [
        (first_sort, Value::new(30), Value::new(20)),
        (second_sort, Value::new(300), Value::new(200)),
    ];
    for (sort, left, right) in pairs {
        receipts.intern_literal(sort, ReplayLiteral::Internal(left.index() as u64), left);
        receipts.intern_literal(sort, ReplayLiteral::Internal(right.index() as u64), right);
    }
    db.set_causal_wave(CausalWave::new(1));
    for (rule, (sort, left, right)) in pairs.into_iter().enumerate() {
        stage_test_union(
            &db,
            uf,
            empty_rule_cause(&receipts, 125 + rule as u32, CausalWave::new(1)),
            sort,
            left,
            right,
            Value::new(1),
        );
    }
    assert!(db.merge_all());
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            let sorts = (1..=2)
                .map(|id| {
                    view.applied_equality(crate::AppliedEqualityId::new(id))
                        .map(|event| event.left.sort)
                })
                .collect::<Result<Vec<_>, _>>()?;
            assert_eq!(sorts, [first_sort, second_sort]);
            Ok(())
        })
        .unwrap();
}

#[test]
fn unsupported_equality_cause_fails_before_native_union() {
    let mut db = Database::default();
    let receipts = db.enable_causal_receipts();
    let mut uf = DisplacedTable::default();
    uf.enable_causal_receipts();
    let sort = ReplaySortId::new(130);
    let left = Value::new(2);
    let right = Value::new(1);
    receipts.intern_literal(sort, ReplayLiteral::Internal(2), left);
    receipts.intern_literal(sort, ReplayLiteral::Internal(1), right);
    db.set_causal_wave(CausalWave::new(1));
    {
        let mut buffer = uf.new_buffer();
        buffer.stage_typed_union(
            &[left, right, Value::new(1)],
            receipts.source_draft(SourceRef::Synthetic(130)).into(),
            receipts
                .typed_equality_proposal(CausalWave::new(1), sort, left, right)
                .unwrap(),
        );
    }
    let failed = catch_unwind(AssertUnwindSafe(|| {
        let mut state = ExecutionState::new(db.read_only_view(), Default::default());
        uf.merge(&mut state)
    }));
    assert!(failed.is_err());
    assert_eq!(uf.underlying_uf().find_naive(left), left);
    assert_eq!(uf.underlying_uf().find_naive(right), right);
    db.finalize_causal_wave();
    assert!(
        receipts
            .with_view(|view| Ok(view.totals().applied_equalities == 0))
            .unwrap()
    );
}

#[test]
fn pending_union_can_make_an_unsupported_cause_redundant() {
    let mut db = Database::default();
    let receipts = db.enable_causal_receipts();
    let mut uf = DisplacedTable::default();
    uf.enable_causal_receipts();
    let sort = ReplaySortId::new(135);
    let left = Value::new(600);
    let right = Value::new(500);
    receipts.intern_literal(sort, ReplayLiteral::Internal(600), left);
    receipts.intern_literal(sort, ReplayLiteral::Internal(500), right);
    db.set_causal_wave(CausalWave::new(1));
    let proposal = receipts
        .typed_equality_proposal(CausalWave::new(1), sort, left, right)
        .unwrap();
    {
        let mut buffer = uf.new_buffer();
        buffer.stage_typed_union(
            &[left, right, Value::new(1)],
            empty_rule_cause(&receipts, 135, CausalWave::new(1)),
            proposal,
        );
        buffer.stage_typed_union(
            &[left, right, Value::new(1)],
            receipts.source_draft(SourceRef::Synthetic(135)).into(),
            proposal,
        );
    }
    let mut state = ExecutionState::new(db.read_only_view(), Default::default());
    assert!(uf.merge(&mut state).added);
    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, 1);
            assert_eq!(view.counters().redundant_unions, 1);
            Ok(())
        })
        .unwrap();
}

#[test]
fn invalid_union_late_in_batch_leaves_native_union_find_untouched() {
    let mut db = Database::default();
    let receipts = db.enable_causal_receipts();
    let mut uf = DisplacedTable::default();
    uf.enable_causal_receipts();
    let sort = ReplaySortId::new(131);
    let values = [
        Value::new(1_000),
        Value::new(900),
        Value::new(800),
        Value::new(700),
    ];
    for value in values {
        receipts.intern_literal(sort, ReplayLiteral::Internal(value.index() as u64), value);
    }
    let native_before = uf.underlying_uf().clone();
    db.set_causal_wave(CausalWave::new(1));
    {
        let mut buffer = uf.new_buffer();
        buffer.stage_typed_union(
            &[values[0], values[1], Value::new(1)],
            empty_rule_cause(&receipts, 131, CausalWave::new(1)),
            receipts
                .typed_equality_proposal(CausalWave::new(1), sort, values[0], values[1])
                .unwrap(),
        );
        buffer.stage_typed_union(
            &[values[2], values[3], Value::new(1)],
            receipts.source_draft(SourceRef::Synthetic(131)).into(),
            receipts
                .typed_equality_proposal(CausalWave::new(1), sort, values[2], values[3])
                .unwrap(),
        );
    }
    let failed = catch_unwind(AssertUnwindSafe(|| {
        let mut state = ExecutionState::new(db.read_only_view(), Default::default());
        uf.merge(&mut state)
    }));
    assert!(failed.is_err());
    assert_eq!(uf.len(), 0, "an earlier valid row leaked from the batch");
    assert!(
        uf.underlying_uf() == &native_before,
        "read-only preflight reserved or rewrote native union-find state"
    );
    for value in values {
        assert_eq!(uf.underlying_uf().find_naive(value), value);
    }
    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, 0);
            Ok(())
        })
        .unwrap();
}

#[test]
fn conflicting_sort_fails_while_constructing_the_later_proposal() {
    let mut db = Database::default();
    let receipts = db.enable_causal_receipts();
    let mut uf = DisplacedTable::default();
    uf.enable_causal_receipts();
    let first_sort = ReplaySortId::new(132);
    let conflicting_sort = ReplaySortId::new(133);
    let left = Value::new(1_200);
    let right = Value::new(1_100);
    for sort in [first_sort, conflicting_sort] {
        receipts.intern_literal(sort, ReplayLiteral::Internal(left.index() as u64), left);
        receipts.intern_literal(sort, ReplayLiteral::Internal(right.index() as u64), right);
    }
    let native_before = uf.underlying_uf().clone();
    db.set_causal_wave(CausalWave::new(1));
    {
        let mut first = uf.new_buffer();
        first.stage_typed_union(
            &[left, right, Value::new(1)],
            empty_rule_cause(&receipts, 132, CausalWave::new(1)),
            receipts
                .typed_equality_proposal(CausalWave::new(1), first_sort, left, right)
                .unwrap(),
        );
    }
    let failed = catch_unwind(AssertUnwindSafe(|| {
        let mut second = uf.new_buffer();
        second.stage_typed_union(
            &[left, right, Value::new(1)],
            empty_rule_cause(&receipts, 133, CausalWave::new(1)),
            receipts
                .typed_equality_proposal(CausalWave::new(1), conflicting_sort, left, right)
                .unwrap(),
        );
    }));
    assert!(failed.is_err());
    assert_eq!(uf.len(), 0);
    assert!(uf.underlying_uf() == &native_before);
    assert_eq!(uf.underlying_uf().find_naive(left), left);
    assert_eq!(uf.underlying_uf().find_naive(right), right);
}

#[test]
fn invalid_union_batch_does_not_compress_existing_native_paths() {
    let mut db = Database::default();
    let receipts = db.enable_causal_receipts();
    let mut uf = DisplacedTable::default();
    uf.enable_causal_receipts();
    let sort = ReplaySortId::new(134);
    for raw in [30, 20, 10, 5, 4, 3] {
        receipts.intern_literal(sort, ReplayLiteral::Internal(raw), Value::new(raw as u32));
    }

    for (wave, left, right) in [(1_u32, 30_u32, 20_u32), (2, 20, 10)] {
        let causal_wave = CausalWave::new(wave.into());
        db.set_causal_wave(causal_wave);
        {
            let mut buffer = uf.new_buffer();
            let left = Value::new(left);
            let right = Value::new(right);
            buffer.stage_typed_union(
                &[left, right, Value::new(wave)],
                empty_rule_cause(&receipts, 134 + wave, causal_wave),
                receipts
                    .typed_equality_proposal(causal_wave, sort, left, right)
                    .unwrap(),
            );
        }
        let mut state = ExecutionState::new(db.read_only_view(), Default::default());
        assert!(uf.merge(&mut state).added);
    }
    let before = uf.underlying_uf().clone();

    db.set_causal_wave(CausalWave::new(3));
    {
        let mut buffer = uf.new_buffer();
        buffer.stage_typed_union(
            &[Value::new(30), Value::new(5), Value::new(3)],
            empty_rule_cause(&receipts, 137, CausalWave::new(3)),
            receipts
                .typed_equality_proposal(CausalWave::new(3), sort, Value::new(30), Value::new(5))
                .unwrap(),
        );
        buffer.stage_typed_union(
            &[Value::new(4), Value::new(3), Value::new(3)],
            receipts.source_draft(SourceRef::Synthetic(134)).into(),
            receipts
                .typed_equality_proposal(CausalWave::new(3), sort, Value::new(4), Value::new(3))
                .unwrap(),
        );
    }
    let failed = catch_unwind(AssertUnwindSafe(|| {
        let mut state = ExecutionState::new(db.read_only_view(), Default::default());
        uf.merge(&mut state)
    }));
    assert!(failed.is_err());
    assert!(
        uf.underlying_uf() == &before,
        "rejected receipt publication compressed an existing native path"
    );
    assert_eq!(uf.len(), 2);

    // The rejected pass must not reserve an equality id or poison the next
    // valid publication in the same wave.
    {
        let mut buffer = uf.new_buffer();
        buffer.stage_typed_union(
            &[Value::new(5), Value::new(4), Value::new(3)],
            empty_rule_cause(&receipts, 138, CausalWave::new(3)),
            receipts
                .typed_equality_proposal(CausalWave::new(3), sort, Value::new(5), Value::new(4))
                .unwrap(),
        );
    }
    let mut state = ExecutionState::new(db.read_only_view(), Default::default());
    assert!(uf.merge(&mut state).added);
    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, 3);
            assert_eq!(
                view.applied_equality(crate::AppliedEqualityId::new(3))?.id,
                crate::AppliedEqualityId::new(3)
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn receipt_database_clone_and_clear_fail_before_mutation() {
    let mut db = Database::default();
    let table = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    db.enable_causal_receipts();
    assert!(catch_unwind(AssertUnwindSafe(|| db.clone())).is_err());
    assert!(catch_unwind(AssertUnwindSafe(|| db.clear_table(table))).is_err());
    assert_eq!(db.get_table(table).len(), 0);
}

#[test]
fn causal_receipts_resolve_primitive_only_current_terms_after_ignored_columns() {
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
    let input = db.add_table_named(
        relation(),
        "CurrentInput".into(),
        iter::empty(),
        iter::empty(),
    );
    let derived = db.add_table_named(
        relation(),
        "CurrentDerived".into(),
        iter::empty(),
        iter::empty(),
    );
    let receipts = db.enable_causal_receipts();
    let value_sort = ReplaySortId::new(10);
    let primitive_sort = ReplaySortId::new(11);
    let primitive_op = ReplayOpId::new(11);
    receipts
        .register_table_layout(input, &[Some(value_sort), None])
        .unwrap();
    receipts
        .register_table_layout(derived, &[Some(value_sort), Some(primitive_sort)])
        .unwrap();
    let value = Value::new(7);
    let primitive = Value::new(0);
    let value_term = receipts.intern_literal(value_sort, ReplayLiteral::I64(7), value);
    db.stage_source_row(
        input,
        &[value, Value::new(0)],
        &[value_term, crate::ReplayTermId::MISSING],
        SourceRef::Synthetic(70),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();
    let primitive_fn =
        db.add_external_function(Box::new(make_external_func(move |_, _| Some(primitive))));

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let x = query.new_var_named("x");
    let timestamp = query.new_var_named("timestamp");
    let input_atom = query
        .add_atom(input, &[x.into(), timestamp.into()], &[])
        .unwrap();
    let mut action = query.build();
    // This instruction represents a replay-safe pure body primitive promoted
    // before the mutating head begins.
    let primitive_var = action
        .call_external_with_replay(
            primitive_fn,
            &[x.into()],
            Some(ReplayConstructorSpec::new(
                primitive_sort,
                primitive_op,
                [value_sort],
            )),
        )
        .unwrap();
    action
        .insert(derived, &[x.into(), primitive_var.into()])
        .unwrap();
    action.build_with_receipts(
        "current-value-receipt",
        RuleReceiptSpec::new(60, [input_atom], [x, primitive_var])
            .with_current_vars([(primitive_var, primitive_sort)]),
    );
    let rules = rules.build();
    let recipe = receipts
        .rule_term_recipe(60)
        .expect("current binding must retain one structural producer");
    let [Some(root)] = recipe.current_roots.as_ref() else {
        panic!("pure body primitive must lower to one Current root")
    };
    let TermTemplate::Call { sort, op, children } = root.as_ref() else {
        panic!("pure body primitive Current root must be a Call")
    };
    assert_eq!((*sort, *op), (primitive_sort, primitive_op));
    assert_eq!(
        children.as_ref(),
        &[Arc::new(TermTemplate::Binding { binding: 0 })]
    );
    let recipe_counters = receipts.with_view(|view| Ok(view.counters())).unwrap();
    assert_eq!(recipe_counters.supported_current_recipe_roots, 1);
    assert_eq!(recipe_counters.missing_current_recipe_roots, 0);
    db.set_causal_wave(CausalWave::new(1));
    assert!(db.run_rule_set(&rules, ReportLevel::TimeOnly).changed);
    db.finalize_causal_wave();

    receipts.with_view(|view| {
    let derived_fact = fact_for_table(view, derived);
    let derived_terms = view.fact_terms(derived_fact.id)?;
    let primitive_term = derived_terms[1];
    assert_eq!(
        receipts.replay_term(primitive_term),
        Some(ReplayTerm::Call {
            sort: primitive_sort,
            op: primitive_op,
            children: [value_term].into(),
        })
    );
    assert_eq!(
        derived_terms.as_ref(),
        &[value_term, primitive_term],
        "ignored source columns stay row-aligned while a primitive-only variable resolves from the typed current-value map"
    );
    let matched = view.matched(cause_rule_match(derived_fact.cause).unwrap())?;
    assert_eq!(view.match_terms(matched.id)?.as_ref(), &[value_term, primitive_term]);
    assert_eq!(view.counters().logical_match_term_handles, 2);
    assert_eq!(
        view.counters().stored_match_term_handles, 0,
        "static Current recipes replace per-match runtime term handles"
    );
    Ok(())
    }).unwrap();
}

#[test]
fn causal_receipts_capture_exact_rhs_producer_term_not_global_alias() {
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
    let receipts = db.enable_causal_receipts();
    let child_sort = ReplaySortId::new(197);
    let result_sort = ReplaySortId::new(198);
    let op = ReplayOpId::new(197);
    receipts
        .register_table_layout(constructor, &[Some(child_sort), Some(result_sort), None])
        .unwrap();
    receipts
        .register_table_constructor(
            constructor,
            ReplayConstructorSpec::new(result_sort, op, [child_sort]),
        )
        .unwrap();
    receipts
        .register_table_layout(derived, &[Some(result_sort)])
        .unwrap();

    let wrong_child_value = Value::new(1970);
    let exact_child_value = Value::new(1971);
    let output_value = Value::new(1972);
    let wrong_child =
        receipts.intern_literal(child_sort, ReplayLiteral::Internal(1970), wrong_child_value);
    let exact_child =
        receipts.intern_literal(child_sort, ReplayLiteral::Internal(1971), exact_child_value);
    let wrong_call = receipts
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
    action.build_with_receipts(
        "exact-rhs-current-term",
        RuleReceiptSpec::new(197, iter::empty(), [produced])
            .with_current_vars([(produced, result_sort)]),
    );
    let rules = rules.build();
    db.set_causal_wave(CausalWave::new(1));
    assert!(db.run_rule_set(&rules, ReportLevel::TimeOnly).changed);
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            let constructor_fact = fact_for_table(view, constructor);
            let exact_call = view.fact_terms(constructor_fact.id)?[1];
            assert_ne!(exact_call, wrong_call);
            assert_eq!(
                receipts.lookup_term(result_sort, output_value),
                Some(wrong_call),
                "global lookup deliberately keeps the competing alias"
            );
            let derived_fact = fact_for_table(view, derived);
            let matched = view.matched(cause_rule_match(derived_fact.cause).unwrap())?;
            assert_eq!(view.match_terms(matched.id)?.as_ref(), &[exact_call]);
            assert_eq!(view.counters().logical_match_term_handles, 1);
            assert_eq!(
                view.counters().stored_match_term_handles,
                0,
                "exact RHS syntax is reconstructed from the static mutation site"
            );
            assert_eq!(
                receipts.replay_term(exact_call),
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
fn promoted_sibling_retains_unchanged_same_wave_merge_read() {
    let mut db = Database::default();
    let relation = |columns| {
        SortedWritesTable::new(
            columns,
            columns,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "relation rows are immutable");
                false
            }),
        )
    };
    let trigger = db.add_table(relation(1), iter::empty(), iter::empty());
    // Keep this table before `merged` and emit its action first. Its effective
    // sibling can therefore provisionally promote the match before the later
    // table executes the unchanged merge callback.
    let sibling = db.add_table(relation(1), iter::empty(), iter::empty());
    let merged = db.add_table(
        SortedWritesTable::new(
            1,
            2,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, ":merge old must keep the prior row");
                false
            }),
        ),
        iter::empty(),
        iter::empty(),
    );
    let receipts = db.enable_causal_receipts();
    for (table, columns) in [(trigger, 1), (sibling, 1), (merged, 2)] {
        register_test_receipt_table(&receipts, table, columns);
    }
    let first = Value::new(2010);
    let second = Value::new(2011);
    let shared_key = Value::new(2012);
    let shared_value = Value::new(2013);
    for value in [first, second, shared_key, shared_value] {
        install_test_row_terms(&receipts, &[value]);
    }
    for (source, value) in [(2010, first), (2011, second)] {
        db.stage_source_row(
            trigger,
            &[value],
            &[receipts.lookup_term(TEST_REPLAY_SORT, value).unwrap()],
            SourceRef::Synthetic(source),
        )
        .unwrap();
    }
    assert!(db.merge_all());
    db.finalize_causal_wave();

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let x = query.new_var_named("x");
    let atom = query.add_atom(trigger, &[x.into()], &[]).unwrap();
    let mut action = query.build();
    action.insert(sibling, &[x.into()]).unwrap();
    action
        .insert(merged, &[shared_key.into(), shared_value.into()])
        .unwrap();
    action.build_with_receipts(
        "same-wave-merge-read",
        RuleReceiptSpec::new(201, [atom], [x]),
    );
    let rules = rules.build();

    db.set_causal_wave(CausalWave::new(1));
    assert!(db.run_rule_set(&rules, ReportLevel::TimeOnly).changed);
    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            let merged_fact = fact_for_table(view, merged);
            let second_term = receipts.lookup_term(TEST_REPLAY_SORT, second).unwrap();
            let second_match = match_ids(view)
                .map(|id| view.matched(id))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .find(|matched| {
                    matched.rule == 201
                        && view
                            .match_terms(matched.id)
                            .is_ok_and(|terms| terms.as_ref() == [second_term])
                })
                .expect("the effective sibling must retain the second firing");
            assert_eq!(
                second_match.merge_reads,
                &[merged_fact.id],
                "the unchanged merge must retain the immutable same-wave predecessor"
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn unchanged_merge_without_effective_sibling_promotes_nothing() {
    let mut db = Database::default();
    let trigger = db.add_table(
        SortedWritesTable::new(1, 1, None, vec![], Box::new(|_, _, _, _| false)),
        iter::empty(),
        iter::empty(),
    );
    let merged = db.add_table(
        SortedWritesTable::new(
            1,
            2,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, ":merge old must keep the prior row");
                false
            }),
        ),
        iter::empty(),
        iter::empty(),
    );
    let receipts = db.enable_causal_receipts();
    register_test_receipt_table(&receipts, trigger, 1);
    register_test_receipt_table(&receipts, merged, 2);
    let trigger_value = Value::new(2020);
    let key = Value::new(2021);
    let value = Value::new(2022);
    for raw in [trigger_value, key, value] {
        install_test_row_terms(&receipts, &[raw]);
    }
    db.stage_source_row(
        trigger,
        &[trigger_value],
        &[receipts
            .lookup_term(TEST_REPLAY_SORT, trigger_value)
            .unwrap()],
        SourceRef::Synthetic(2020),
    )
    .unwrap();
    db.stage_source_row(
        merged,
        &[key, value],
        &[
            receipts.lookup_term(TEST_REPLAY_SORT, key).unwrap(),
            receipts.lookup_term(TEST_REPLAY_SORT, value).unwrap(),
        ],
        SourceRef::Synthetic(2021),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let x = query.new_var_named("x");
    let atom = query.add_atom(trigger, &[x.into()], &[]).unwrap();
    let mut action = query.build();
    action.insert(merged, &[key.into(), value.into()]).unwrap();
    action.build_with_receipts(
        "unchanged-merge-only",
        RuleReceiptSpec::new(202, [atom], [x]),
    );
    let rules = rules.build();

    db.set_causal_wave(CausalWave::new(1));
    db.run_rule_set(&rules, ReportLevel::TimeOnly);
    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            assert_eq!(view.totals().facts, 2, "an unchanged merge creates no fact");
            assert_eq!(view.totals().applied_equalities, 0);
            assert_eq!(view.totals().rekeys, 0);
            Ok(())
        })
        .unwrap();
}

#[test]
#[should_panic(expected = "selects non-replayable table column")]
fn causal_receipt_metadata_rejects_binding_an_ignored_column() {
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
    let receipts = db.enable_causal_receipts();
    receipts
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
    action.build_with_receipts(
        "ignored-column",
        RuleReceiptSpec::new(61, [atom], [ignored]),
    );
}

#[test]
fn causal_receipt_binding_recipe_keeps_every_premise_occurrence() {
    let mut db = Database::default();
    let repeated = db.add_table(
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
        iter::empty(),
        iter::empty(),
    );
    let later = db.add_table(
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
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(212);
    receipts
        .register_table_layout(repeated, &[Some(sort), Some(sort)])
        .unwrap();
    receipts
        .register_table_layout(later, &[Some(sort)])
        .unwrap();

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let x = query.new_var_named("x");
    let repeated_atom = query
        .add_atom(repeated, &[x.into(), x.into()], &[])
        .unwrap();
    let later_atom = query.add_atom(later, &[x.into()], &[]).unwrap();
    query.build().build_with_receipts(
        "all-premise-occurrences",
        RuleReceiptSpec::new(212, [repeated_atom, later_atom], [x]),
    );
    let rules = rules.build();
    let receipt = rules
        .actions
        .iter()
        .next()
        .and_then(|(_, action)| action.receipt.as_ref())
        .expect("rule action must retain its receipt recipe");
    let occurrences = receipt.binding_sources[0]
        .premise_occurrences()
        .expect("body-bound variable must have premise occurrences");
    assert_eq!(
        occurrences
            .iter()
            .map(|occurrence| (occurrence.premise, occurrence.column))
            .collect::<Vec<_>>(),
        [(0, 0), (0, 1), (1, 0)],
        "duplicate columns and later atoms are all part of the static recipe"
    );
}

#[test]
fn duplicate_premise_columns_keep_the_legacy_public_representative() {
    let mut db = Database::default();
    let immutable = |columns| {
        SortedWritesTable::new(
            columns,
            columns,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right);
                false
            }),
        )
    };
    let input = db.add_table(immutable(2), iter::empty(), iter::empty());
    let output = db.add_table(immutable(1), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let child_sort = ReplaySortId::new(213);
    let sort = ReplaySortId::new(214);
    receipts
        .register_table_layout(input, &[Some(sort), Some(sort)])
        .unwrap();
    receipts
        .register_table_layout(output, &[Some(sort)])
        .unwrap();

    let raw = Value::new(2130);
    let first_child =
        receipts.intern_literal(child_sort, ReplayLiteral::Internal(2131), Value::new(2131));
    let last_child =
        receipts.intern_literal(child_sort, ReplayLiteral::Internal(2132), Value::new(2132));
    let first = receipts
        .intern_call(sort, ReplayOpId::new(213), &[first_child], raw)
        .unwrap();
    let last = receipts
        .intern_call(sort, ReplayOpId::new(213), &[last_child], raw)
        .unwrap();
    assert_ne!(first, last, "the canary requires competing exact syntax");
    let row = [raw, raw];
    let terms = [first, last];
    db.stage_source_row(input, &row, &terms, SourceRef::Synthetic(213))
        .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let x = query.new_var_named("x");
    let atom = query.add_atom(input, &[x.into(), x.into()], &[]).unwrap();
    let mut action = query.build();
    action.insert(output, &[x.into()]).unwrap();
    action.build_with_receipts(
        "duplicate-public-representative",
        RuleReceiptSpec::new(213, [atom], [x]),
    );
    let rules = rules.build();
    db.set_causal_wave(CausalWave::new(1));
    assert!(db.run_rule_set(&rules, ReportLevel::TimeOnly).changed);
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            let output_fact = fact_for_table(view, output);
            let matched = view.matched(cause_rule_match(output_fact.cause).unwrap())?;
            assert_eq!(matched.rule, 213);
            assert_eq!(
                view.match_terms(matched.id)?.as_ref(),
                &[last],
                "the binding recipe keeps Atom::get_col's last duplicate column"
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn conditional_insert_records_only_true_effective_lanes() {
    let mut db = Database::default();
    let immutable = || {
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
    let input = db.add_table(
        SortedWritesTable::new(
            2,
            3,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "input rows are immutable");
                false
            }),
        ),
        iter::empty(),
        iter::empty(),
    );
    let output = db.add_table(immutable(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(12);
    receipts
        .register_table_layout(input, &[Some(sort), Some(sort), None])
        .unwrap();
    receipts
        .register_table_layout(output, &[Some(sort), Some(sort)])
        .unwrap();
    register_test_merge_origins(
        &receipts,
        output,
        &[
            MergeOriginSelector::Prior { column: 0 },
            MergeOriginSelector::Prior { column: 1 },
        ],
    );
    let true_value = Value::new(1);
    let false_value = Value::new(0);
    let output_value = Value::new(9);
    for value in [
        Value::new(10),
        Value::new(20),
        true_value,
        false_value,
        output_value,
    ] {
        receipts.intern_literal(sort, ReplayLiteral::Internal(value.index() as u64), value);
    }
    for (ordinal, (key, condition)) in [(Value::new(10), true_value), (Value::new(20), false_value)]
        .into_iter()
        .enumerate()
    {
        let terms = [
            receipts.lookup_term(sort, key).unwrap(),
            receipts.lookup_term(sort, condition).unwrap(),
            crate::ReplayTermId::MISSING,
        ];
        db.stage_source_row(
            input,
            &[key, condition, Value::new(0)],
            &terms,
            SourceRef::Synthetic(900 + ordinal as u64),
        )
        .unwrap();
    }
    assert!(db.merge_all());
    db.finalize_causal_wave();

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let key = query.new_var_named("key");
    let condition = query.new_var_named("condition");
    let timestamp = query.new_var_named("timestamp");
    let atom = query
        .add_atom(
            input,
            &[key.into(), condition.into(), timestamp.into()],
            &[],
        )
        .unwrap();
    let mut action = query.build();
    action
        .insert_if_eq(
            output,
            condition.into(),
            crate::QueryEntry::Const(true_value),
            &[key.into(), crate::QueryEntry::Const(output_value)],
        )
        .unwrap();
    action.build_with_receipts(
        "conditional-insert",
        RuleReceiptSpec::new(91, [atom], [key, condition]),
    );
    let rules = rules.build();

    db.set_causal_wave(CausalWave::new(1));
    assert!(db.run_rule_set(&rules, ReportLevel::TimeOnly).changed);
    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            let outputs = fact_ids(view)
                .filter_map(|id| view.fact(id).ok())
                .filter(|fact| fact.table == output)
                .collect::<Vec<_>>();
            assert_eq!(outputs.len(), 1);
            let matched = view.matched(cause_rule_match(outputs[0].cause).unwrap())?;
            let premise = matched.premises[0];
            let crate::ReceiptCauseRef::Cause(source) = view.fact(premise)?.cause else {
                panic!("the retained premise must be a source fact")
            };
            assert!(matches!(
                view.cause(source)?,
                crate::RawReceiptCause::Source(SourceRef::Synthetic(900))
            ));
            assert_eq!(outputs[0].cause, crate::ReceiptCauseRef::Rule(matched.id));
            Ok(())
        })
        .unwrap();

    db.set_causal_wave(CausalWave::new(2));
    assert!(!db.run_rule_set(&rules, ReportLevel::TimeOnly).changed);
    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            assert_eq!(
                fact_ids(view)
                    .filter_map(|id| view.fact(id).ok())
                    .filter(|fact| fact.table == output)
                    .count(),
                1
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn causal_receipts_reject_unsupported_merge_before_callback_effects() {
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
                if left != right {
                    out.extend_from_slice(&[right[0], Value::new(9)]);
                    true
                } else {
                    false
                }
            }),
        ),
        iter::empty(),
        iter::empty(),
    );
    let receipts = db.enable_causal_receipts();
    receipts
        .register_table_layout(table, &[Some(TEST_REPLAY_SORT), Some(TEST_REPLAY_SORT)])
        .unwrap();
    receipts
        .register_table_merge_origins(
            table,
            &[
                MergeOriginSelector::Incoming { column: 0 },
                MergeOriginSelector::Unsupported,
            ],
        )
        .unwrap();
    for value in [Value::new(0), Value::new(1), Value::new(2), Value::new(9)] {
        install_test_row_terms(&receipts, &[value]);
    }
    let one = receipts
        .lookup_term(TEST_REPLAY_SORT, Value::new(1))
        .unwrap();
    let zero = receipts
        .lookup_term(TEST_REPLAY_SORT, Value::new(0))
        .unwrap();
    let two = receipts
        .lookup_term(TEST_REPLAY_SORT, Value::new(2))
        .unwrap();
    db.stage_source_row(
        table,
        &[Value::new(2), Value::new(0)],
        &[two, zero],
        SourceRef::Synthetic(90),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();

    db.set_causal_wave(CausalWave::new(1));
    let cause = receipts.register_rule_matches(62, CausalWave::new(1), 0, &[], &[], &[0])[0].1;
    let absent_origin = receipts.register_row_origin(RowOriginSpec {
        table,
        cells: [
            Some(Arc::new(TermTemplate::Static { term: one })),
            Some(Arc::new(TermTemplate::Static { term: one })),
        ]
        .into(),
    });
    let collision_origin = receipts.register_row_origin(RowOriginSpec {
        table,
        cells: [
            Some(Arc::new(TermTemplate::Static { term: two })),
            Some(Arc::new(TermTemplate::Static { term: two })),
        ]
        .into(),
    });
    let mut update = db.new_buffer(table);
    update.stage_insert_deferred_with_origin(
        &[Value::new(1), Value::new(1)],
        crate::DeferredEqualityCause::ready(cause),
        absent_origin,
    );
    update.stage_insert_deferred_with_origin(
        &[Value::new(2), Value::new(2)],
        crate::DeferredEqualityCause::ready(cause),
        collision_origin,
    );
    drop(update);
    let error = catch_unwind(AssertUnwindSafe(|| db.merge_all()));
    assert!(error.is_err(), "unsupported merge origin must fail closed");
    assert_eq!(
        callbacks.load(Ordering::SeqCst),
        0,
        "merge support must be validated before the callback can stage effects"
    );
    assert!(
        db.get_table(table).get_row(&[Value::new(1)]).is_none(),
        "a preceding absent-key insert must not leak from a rejected receipt batch"
    );
    assert_eq!(
        db.get_table(table)
            .get_row(&[Value::new(2)])
            .unwrap()
            .vals
            .as_slice(),
        &[Value::new(2), Value::new(0)],
        "the colliding live row must remain unchanged"
    );
}

#[test]
fn causal_receipts_merge_origin_selects_each_cell_without_value_alias_lookup() {
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
    let receipts = db.enable_causal_receipts();
    let value_sort = ReplaySortId::new(198);
    let alias_sort = ReplaySortId::new(199);
    let alias_op = ReplayOpId::new(198);
    receipts
        .register_table_layout(
            table,
            &[Some(value_sort), Some(alias_sort), Some(value_sort)],
        )
        .unwrap();
    receipts
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
    let key_term = receipts.intern_literal(value_sort, ReplayLiteral::Internal(1980), key_value);
    let old_child =
        receipts.intern_literal(value_sort, ReplayLiteral::Internal(1982), old_child_value);
    let new_child =
        receipts.intern_literal(value_sort, ReplayLiteral::Internal(1983), new_child_value);
    let old_alias = receipts
        .intern_call(alias_sort, alias_op, &[old_child], shared_alias_value)
        .unwrap();
    let old_tail =
        receipts.intern_literal(value_sort, ReplayLiteral::Internal(1984), old_tail_value);
    let new_tail =
        receipts.intern_literal(value_sort, ReplayLiteral::Internal(1985), new_tail_value);
    let prior_row = [key_value, shared_alias_value, old_tail_value];
    db.stage_source_row(
        table,
        &prior_row,
        &[key_term, old_alias, old_tail],
        SourceRef::Synthetic(198),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();

    let incoming_origin = receipts.register_row_origin(RowOriginSpec {
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
    db.set_causal_wave(CausalWave::new(1));
    let cause = empty_rule_cause(&receipts, 198, CausalWave::new(1));
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
    db.finalize_causal_wave();

    receipts.with_view(|view| {
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
        receipts.lookup_term(alias_sort, shared_alias_value),
        Some(old_alias),
        "the canary deliberately leaves global lookup unable to name the incoming alias"
    );
    Ok(())
    }).unwrap();
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
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(216);
    receipts
        .register_table_layout(table, &[Some(sort), Some(sort)])
        .unwrap();
    receipts
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
    let key_term = receipts.intern_literal(sort, ReplayLiteral::Internal(2160), key);
    let prior_term = receipts.intern_literal(sort, ReplayLiteral::Internal(10), prior);
    let incoming_term = receipts.intern_literal(sort, ReplayLiteral::Internal(20), incoming);
    db.stage_source_row(
        table,
        &[key, prior],
        &[key_term, prior_term],
        SourceRef::Synthetic(216),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();
    let prior_fact = committed_fact_id_for_key(&db, table, &[key]);

    let incoming_origin = receipts.register_row_origin(RowOriginSpec {
        table,
        cells: [
            Some(Arc::new(TermTemplate::Static { term: key_term })),
            Some(Arc::new(TermTemplate::Static {
                term: incoming_term,
            })),
        ]
        .into(),
    });
    db.set_causal_wave(CausalWave::new(1));
    {
        let mut updates = db.new_buffer(table);
        updates.stage_insert_deferred_with_origin(
            &[key, incoming],
            crate::DeferredEqualityCause::ready(empty_rule_cause(
                &receipts,
                216,
                CausalWave::new(1),
            )),
            incoming_origin,
        );
    }
    assert!(db.merge_all());
    db.finalize_causal_wave();
    receipts
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

    let tie_origin = receipts.register_row_origin(RowOriginSpec {
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
    let prepared = receipts
        .prepare_merged_fact_origin(
            table,
            &[key, prior],
            &[key, prior],
            &[key, prior],
            prior_fact,
            Some(crate::receipts::RowOriginRef::Site(tie_origin)),
        )
        .unwrap();
    assert!(matches!(
        prepared,
        crate::receipts::PreparedFactOrigin::Merge {
            prior: fact,
            cells,
            ..
        } if fact == prior_fact
            && cells.as_slice()
                == [
                    crate::receipts::MergeCellOrigin::Incoming(0),
                    crate::receipts::MergeCellOrigin::Prior(1),
                ]
    ));
}

#[test]
fn merge_origin_catalog_rejects_out_of_range_and_cross_sort_sources() {
    let receipts = CausalReceipts::default();
    let table = TableId::new_const(198);
    let left = ReplaySortId::new(198);
    let right = ReplaySortId::new(199);
    receipts
        .register_table_layout(table, &[Some(left), Some(right)])
        .unwrap();
    assert_eq!(
        receipts.register_table_merge_origins(
            table,
            &[
                MergeOriginSelector::Incoming { column: 2 },
                MergeOriginSelector::Incoming { column: 1 },
            ],
        ),
        Err("merge-origin source column exceeds the table layout")
    );
    assert_eq!(
        receipts.register_table_merge_origins(
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
fn aborted_union_transaction_publishes_no_native_or_receipt_state() {
    let mut db = Database::default();
    let receipts = db.enable_causal_receipts();
    let mut uf = DisplacedTable::default();
    uf.enable_causal_receipts();
    let sort = ReplaySortId::new(142);
    let left = Value::new(20);
    let right = Value::new(10);
    receipts.intern_literal(sort, ReplayLiteral::Internal(20), left);
    receipts.intern_literal(sort, ReplayLiteral::Internal(10), right);
    let wave = CausalWave::new(1);
    db.set_causal_wave(wave);
    let proposal = receipts
        .typed_equality_proposal(wave, sort, left, right)
        .unwrap();
    let cause = empty_rule_cause(&receipts, 142, wave);
    let transaction = MutationTransaction::pending();
    {
        let mut buffer = uf.new_buffer();
        buffer.defer_until(transaction.clone());
        buffer.stage_typed_union(&[left, right, Value::new(1)], cause, proposal);
    }
    transaction.abort();

    db.with_execution_state(|state| {
        let change = uf.merge(state);
        assert!(!change.added && !change.removed);
    });
    db.finalize_causal_wave();
    assert_eq!(uf.underlying_uf().find_naive(left), left);
    assert_eq!(uf.underlying_uf().find_naive(right), right);
    receipts
        .with_view(|view| {
            assert_eq!(view.totals().applied_equalities, 0);
            Ok(())
        })
        .unwrap();
}

#[test]
fn transactional_native_lease_blocks_wave_finalization_until_queue_drain() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let receipts = db.enable_causal_receipts();
    let sort = ReplaySortId::new(143);
    let left = Value::new(1430);
    let right = Value::new(1431);
    receipts.intern_literal(sort, ReplayLiteral::Internal(1430), left);
    receipts.intern_literal(sort, ReplayLiteral::Internal(1431), right);
    let wave = CausalWave::new(1);
    db.set_causal_wave(wave);
    let cause = empty_rule_cause(&receipts, 143, wave);
    let proposal = receipts
        .typed_equality_proposal(wave, sort, left, right)
        .unwrap();
    let transaction = MutationTransaction::pending_causal(&receipts, wave);
    let mut buffer = db.new_buffer(uf);
    buffer.defer_until(transaction.clone());
    buffer.stage_typed_union(&[left, right, Value::new(1)], cause, proposal);
    transaction.commit();
    drop(transaction);

    let before_publication = catch_unwind(AssertUnwindSafe(|| db.finalize_causal_wave()));
    assert!(before_publication.is_err());
    drop(buffer);
    let before_drain = catch_unwind(AssertUnwindSafe(|| db.finalize_causal_wave()));
    assert!(before_drain.is_err());

    assert!(db.merge_all());
    db.finalize_causal_wave();
    receipts
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
    let receipts = db.enable_causal_receipts();
    register_test_receipt_table(&receipts, table, 1);
    let value = Value::new(1432);
    install_test_row_terms(&receipts, &[value]);
    let wave = CausalWave::new(1);
    db.set_causal_wave(wave);
    let cause = empty_rule_cause(&receipts, 144, wave);
    let term = receipts.lookup_term(TEST_REPLAY_SORT, value).unwrap();
    let origin = install_test_row_origin(&receipts, table, &[value], &[term]);
    let transaction = MutationTransaction::pending_causal(&receipts, wave);
    let mut buffer = db.new_buffer(table);
    buffer.defer_until(transaction.clone());
    buffer.stage_insert_deferred_with_origin(
        &[value],
        crate::DeferredEqualityCause::ready(cause),
        origin,
    );
    transaction.commit();
    drop(transaction);

    let while_buffer_holds_lease = catch_unwind(AssertUnwindSafe(|| db.finalize_causal_wave()));
    assert!(while_buffer_holds_lease.is_err());
    drop(buffer);
    let while_table_queue_holds_lease =
        catch_unwind(AssertUnwindSafe(|| db.finalize_causal_wave()));
    assert!(while_table_queue_holds_lease.is_err());

    assert!(db.merge_all());
    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            let fact = view.fact(crate::FactId::new(1))?;
            assert!(matches!(fact.cause, crate::ReceiptCauseRef::Rule(_)));
            Ok(())
        })
        .unwrap();
}

fn committed_fact_id_for_key(db: &Database, table: TableId, key: &[Value]) -> FactId {
    let table = db.get_table(table);
    let row = table.get_row(key).expect("committed key must exist");
    table
        .fact_id(row.id)
        .expect("receipt-enabled row must have an immutable FactId")
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
    let receipts = db.enable_causal_receipts();
    register_test_receipt_table(&receipts, table, 2);
    let zero = receipts.intern_test_term("zero");
    for key in 0..20 {
        let key_term = receipts.intern_test_term(&format!("key-{key}"));
        db.stage_source_row(
            table,
            &[Value::new(key), Value::new(0)],
            &[key_term, zero],
            SourceRef::Synthetic(key as u64),
        )
        .unwrap();
    }
    assert!(db.merge_all());
    db.finalize_causal_wave();

    let survivor = Value::new(19);
    let target_before = committed_fact_id(&db, table, survivor);
    let target_row_before = committed_row_id(&db, table, survivor);
    let historical = committed_fact_id(&db, table, Value::new(1));
    let version_before = db.get_table(table).version();

    db.set_causal_wave(CausalWave::new(1));
    let lanes = (0..40).collect::<Vec<_>>();
    let causes = receipts
        .register_rule_matches(30, CausalWave::new(1), 0, &[], &[], &lanes)
        .into_iter()
        .map(|(_, cause)| cause)
        .collect::<Vec<_>>();
    let mut updates = db.new_buffer(table);
    for (index, cause) in causes.into_iter().enumerate() {
        let key = 1 + index / 4;
        let value = 1 + index % 4;
        let row = [Value::from_usize(key), Value::from_usize(value)];
        let terms = row.map(|raw| receipts.lookup_term(TEST_REPLAY_SORT, raw).unwrap());
        let origin = install_test_row_origin(&receipts, table, &row, &terms);
        updates.stage_insert_deferred_with_origin(
            &row,
            crate::DeferredEqualityCause::ready(cause),
            origin,
        );
    }
    drop(updates);
    assert!(db.merge_all());
    db.finalize_causal_wave();

    let version_after = db.get_table(table).version();
    assert_ne!(
        version_before.major, version_after.major,
        "the canary must cross a physical rekey/compaction boundary"
    );
    assert_eq!(
        committed_fact_id(&db, table, survivor),
        target_before,
        "an untouched live row must keep its FactId while its RowId generation changes"
    );
    assert_ne!(
        committed_row_id(&db, table, survivor),
        target_row_before,
        "the untouched canary row must physically move during serial compaction"
    );
    assert_ne!(
        committed_fact_id(&db, table, Value::new(1)),
        historical,
        "an effective replacement must create a new immutable FactId"
    );
    assert_eq!(
        receipts
            .with_view(|view| view.fact(historical).map(|fact| fact.id))
            .unwrap(),
        historical,
        "a compacted-away historical row must remain addressable in the receipt arena"
    );
}

fn decomposed_receipt_materialization_case(force_scoped_execution: bool) {
    let mut db = Database::default();
    let receipts = db.enable_causal_receipts();
    let immutable_relation = |n_keys, n_columns| {
        SortedWritesTable::new(
            n_keys,
            n_columns,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "relation rows are immutable");
                false
            }),
        )
    };
    if force_scoped_execution {
        let filler = db.add_table_named(
            immutable_relation(1, 1),
            "ParallelThresholdFiller".into(),
            iter::empty(),
            iter::empty(),
        );
        register_test_receipt_table(&receipts, filler, 1);
        for value in 0..10_001 {
            let term = receipts.intern_test_term(&format!("filler-{value}"));
            db.stage_source_row(
                filler,
                &[Value::from_usize(value)],
                &[term],
                SourceRef::Synthetic(1_000_000 + value as u64),
            )
            .unwrap();
        }
        assert!(db.merge_all());
        db.finalize_causal_wave();
    }
    let r = db.add_table_named(
        immutable_relation(2, 2),
        "R".into(),
        iter::empty(),
        iter::empty(),
    );
    let s = db.add_table_named(
        immutable_relation(2, 2),
        "S".into(),
        iter::empty(),
        iter::empty(),
    );
    let t = db.add_table_named(
        immutable_relation(2, 2),
        "T".into(),
        iter::empty(),
        iter::empty(),
    );
    let u = db.add_table_named(
        immutable_relation(2, 2),
        "U".into(),
        iter::empty(),
        iter::empty(),
    );
    let derived = db.add_table_named(
        immutable_relation(4, 4),
        "DerivedRectangle".into(),
        iter::empty(),
        iter::empty(),
    );
    for (table, columns) in [(r, 2), (s, 2), (t, 2), (u, 2), (derived, 4)] {
        register_test_receipt_table(&receipts, table, columns);
    }

    let term = |value: usize| receipts.intern_test_term(&format!("value-{value}"));
    let source_rows = [
        (r, vec![2, 10]),
        (r, vec![1, 10]),
        (s, vec![10, 20]),
        (t, vec![20, 30]),
        (u, vec![30, 1]),
    ];
    for (source, (table, row)) in source_rows.into_iter().enumerate() {
        let values = row
            .iter()
            .copied()
            .map(Value::from_usize)
            .collect::<Vec<_>>();
        let terms = row.iter().copied().map(&term).collect::<Vec<_>>();
        db.stage_source_row(table, &values, &terms, SourceRef::Synthetic(source as u64))
            .unwrap();
    }
    assert!(db.merge_all());
    db.finalize_causal_wave();

    let r_decoy = committed_fact_id_for_key(&db, r, &[Value::new(2), Value::new(10)]);
    let r_first = committed_fact_id_for_key(&db, r, &[Value::new(1), Value::new(10)]);
    let s_fact = committed_fact_id_for_key(&db, s, &[Value::new(10), Value::new(20)]);
    let t_fact = committed_fact_id_for_key(&db, t, &[Value::new(20), Value::new(30)]);
    let u_fact = committed_fact_id_for_key(&db, u, &[Value::new(30), Value::new(1)]);

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    query.set_plan_strategy(PlanStrategy::Gj);
    let x = query.new_var_named("x");
    let y = query.new_var_named("y");
    let z = query.new_var_named("z");
    let w = query.new_var_named("w");
    let r_atom = query.add_atom(r, &[x.into(), y.into()], &[]).unwrap();
    let s_atom = query.add_atom(s, &[y.into(), z.into()], &[]).unwrap();
    let t_atom = query.add_atom(t, &[z.into(), w.into()], &[]).unwrap();
    let u_atom = query.add_atom(u, &[w.into(), x.into()], &[]).unwrap();
    let mut action = query.build();
    action
        .insert(derived, &[x.into(), y.into(), z.into(), w.into()])
        .unwrap();
    action.build_with_receipts(
        "rectangle-receipt",
        RuleReceiptSpec::new(50, [r_atom, s_atom, t_atom, u_atom], [x, y, z, w]),
    );
    let rule_set = rules.build();
    let (plan, _, _) = rule_set
        .plans
        .values()
        .next()
        .expect("rectangle rule must have one plan");
    let Plan::DecomposedPlan(plan) = plan else {
        panic!("the receipt canary must exercise decomposed materialization");
    };
    assert!(
        plan.stages.blocks.len() >= 2,
        "the receipt canary must cross at least two materialized stages"
    );

    db.set_causal_wave(CausalWave::new(1));
    let report = db.run_rule_set(&rule_set, ReportLevel::TimeOnly);
    assert!(report.changed);
    db.finalize_causal_wave();

    receipts
        .with_view(|view| {
            let derived_fact = fact_for_table(view, derived);
            let match_id = cause_rule_match(derived_fact.cause)
                .expect("rectangle result must cite its native match");
            let matched = view.matched(match_id)?;
            assert_eq!(
                matched.premises,
                &[r_first, s_fact, t_fact, u_fact],
                "receipt premise order must follow the source rule"
            );
            assert!(!matched.premises.contains(&r_decoy));
            assert_eq!(view.counters().logical_match_term_handles, 4);
            assert_eq!(
                view.counters().stored_match_term_handles,
                0,
                "decomposed premise-backed bindings need no durable match-term payload"
            );
            Ok(())
        })
        .unwrap();
}

#[test]
fn decomposed_receipts_preserve_exact_ordered_premises_through_materialization() {
    decomposed_receipt_materialization_case(false);
}

#[test]
fn scoped_decomposed_receipts_preserve_exact_ordered_premises() {
    rayon::ThreadPoolBuilder::new()
        .num_threads(4)
        .build()
        .unwrap()
        .install(|| decomposed_receipt_materialization_case(true));
}

fn decomposed_projected_receipt_case(retain_existential: bool) {
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
    let receipts = db.enable_causal_receipts();
    for (table, columns) in [
        (r, 3),
        (s, 3),
        (t, 2),
        (u, 2),
        (derived, if retain_existential { 5 } else { 4 }),
    ] {
        register_test_receipt_table(&receipts, table, columns);
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
            .map(|value| receipts.intern_test_term(&format!("value-{value}")))
            .collect::<Vec<_>>();
        db.stage_source_row(table, &values, &terms, SourceRef::Synthetic(source as u64))
            .unwrap();
    }
    assert!(db.merge_all());
    db.finalize_causal_wave();

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
    let existential_100_term = receipts.intern_test_term("value-100");
    let existential_101_term = receipts.intern_test_term("value-101");

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
    action.build_with_receipts(
        "existential-rectangle",
        RuleReceiptSpec::new(51, [r_atom, s_atom, t_atom, u_atom], ordinary_vars),
    );
    let rule_set = rules.build();
    let (plan, _, _) = rule_set.plans.values().next().unwrap();
    let Plan::DecomposedPlan(plan) = plan else {
        panic!("existential receipt canary must exercise decomposed materialization");
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

    db.set_causal_wave(CausalWave::new(1));
    reset_pending_witness_resolution_count();
    assert!(db.run_rule_set(&rule_set, ReportLevel::TimeOnly).changed);
    db.finalize_causal_wave();
    assert_eq!(
        pending_witness_resolution_count(),
        2,
        "every normal-return observed lane resolves one exact decomposed witness"
    );
    receipts
        .with_view(|view| {
            let derived_facts = fact_ids(view)
                .filter_map(|id| view.fact(id).ok())
                .filter(|fact| fact.table == derived)
                .collect::<Vec<_>>();
            if retain_existential {
                assert_eq!(derived_facts.len(), 2);
                for fact in derived_facts {
                    let matched = view.matched(
                        cause_rule_match(fact.cause)
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
                let matched = view.matched(cause_rule_match(derived_facts[0].cause).unwrap())?;
                assert_eq!(matched.premises, &[r_first, s_first, t_fact, u_fact]);
                assert!(!matched.premises.contains(&r_second));
                assert!(!matched.premises.contains(&s_second));
            }
            Ok(())
        })
        .unwrap();
}

#[test]
fn decomposed_key_only_receipt_uses_first_exact_existential_support() {
    decomposed_projected_receipt_case(false);
}

#[test]
fn decomposed_exact_result_owner_overrides_nested_projected_support() {
    decomposed_projected_receipt_case(true);
}

#[test]
fn ordinary_decomposed_execution_allocates_no_witness_sidecars() {
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
    let r = db.add_table(relation(2), iter::empty(), iter::empty());
    let s = db.add_table(relation(2), iter::empty(), iter::empty());
    let t = db.add_table(relation(2), iter::empty(), iter::empty());
    let u = db.add_table(relation(2), iter::empty(), iter::empty());
    let derived = db.add_table(relation(4), iter::empty(), iter::empty());
    for (table, row) in [
        (r, [Value::new(1), Value::new(10)]),
        (s, [Value::new(10), Value::new(20)]),
        (t, [Value::new(20), Value::new(30)]),
        (u, [Value::new(30), Value::new(1)]),
    ] {
        let mut source = db.new_buffer(table);
        source.stage_insert(&row);
    }
    assert!(db.merge_all());

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    query.set_plan_strategy(PlanStrategy::Gj);
    let x = query.new_var_named("x");
    let y = query.new_var_named("y");
    let z = query.new_var_named("z");
    let w = query.new_var_named("w");
    query.add_atom(r, &[x.into(), y.into()], &[]).unwrap();
    query.add_atom(s, &[y.into(), z.into()], &[]).unwrap();
    query.add_atom(t, &[z.into(), w.into()], &[]).unwrap();
    query.add_atom(u, &[w.into(), x.into()], &[]).unwrap();
    let mut action = query.build();
    action
        .insert(derived, &[x.into(), y.into(), z.into(), w.into()])
        .unwrap();
    action.build();
    let rule_set = rules.build();
    let (plan, _, _) = rule_set.plans.values().next().unwrap();
    assert!(
        matches!(plan, Plan::DecomposedPlan(plan) if plan.stages.blocks.len() >= 2),
        "ordinary control must exercise the same decomposed materialization path"
    );

    reset_causal_lookup_counters();
    reset_materialized_witness_test_counts();
    assert!(db.run_rule_set(&rule_set, ReportLevel::TimeOnly).changed);
    assert_eq!(
        materialized_witness_test_counts(),
        (0, 0),
        "ordinary materialization must allocate and write no witness sidecars"
    );
    assert_eq!(
        causal_lookup_counters(),
        (0, 0),
        "ordinary decomposed execution must perform no receipt witness reads"
    );
}

#[test]
fn receipt_disabled_rule_path_uses_no_fact_sidecars_or_witness_reads() {
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
        "receipt-only producer metadata must be absent from ordinary action tapes"
    );

    reset_causal_lookup_counters();
    let report = db.run_rule_set(&rule_set, ReportLevel::TimeOnly);
    assert!(report.changed);
    assert_eq!(
        causal_lookup_counters(),
        (0, 0),
        "ordinary execution must not read receipt FactIds or witness rows"
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

#[test]
#[should_panic(expected = "cannot enable causal receipts: table already contains rows")]
fn causal_receipts_reject_activation_after_rows_exist() {
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
    db.enable_causal_receipts();
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
fn causal_receipts_reject_dropped_unmerged_relation_and_uf_buffers() {
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

        let failed = catch_unwind(AssertUnwindSafe(|| db.enable_causal_receipts()));
        assert!(
            failed.is_err(),
            "dropped, unmerged {} mutations must reject receipt activation",
            if is_uf { "UF" } else { "relation" }
        );
        assert!(db.causal_receipts.is_none());
    }
}

#[test]
fn causal_receipts_reject_outstanding_relation_and_uf_buffers() {
    for is_uf in [false, true] {
        let mut db = Database::default();
        let table = if is_uf {
            db.add_table(DisplacedTable::default(), iter::empty(), iter::empty())
        } else {
            db.add_table(activation_test_relation(), iter::empty(), iter::empty())
        };
        let outstanding = db.new_buffer(table);

        let failed = catch_unwind(AssertUnwindSafe(|| db.enable_causal_receipts()));
        assert!(
            failed.is_err(),
            "an outstanding {} buffer must reject receipt activation even before it stages a row",
            if is_uf { "UF" } else { "relation" }
        );
        assert!(db.causal_receipts.is_none());
        drop(outstanding);
    }
}

#[test]
fn receipt_database_rejects_a_preloaded_table_before_adding_it() {
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

    let mut receipts_db = Database::default();
    receipts_db.enable_causal_receipts();
    let next_table = receipts_db.next_table_id();
    let failed = catch_unwind(AssertUnwindSafe(|| {
        receipts_db.add_table(preloaded, iter::empty(), iter::empty())
    }));
    assert!(failed.is_err());
    assert_eq!(
        receipts_db.next_table_id(),
        next_table,
        "a rejected preloaded table must not be partially registered"
    );
}

#[test]
fn causal_receipt_activation_is_all_or_nothing_across_tables() {
    let mut db = Database::default();
    let uf = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let pending = db.add_table(activation_test_relation(), iter::empty(), iter::empty());
    {
        let mut buffer = db.new_buffer(pending);
        buffer.stage_insert(&[Value::new(1), Value::new(0)]);
    }

    let failed = catch_unwind(AssertUnwindSafe(|| db.enable_causal_receipts()));
    assert!(failed.is_err());
    assert!(
        db.causal_receipts.is_none(),
        "the database mode must remain disabled after any table fails preflight"
    );
    let raw_uf_staging = catch_unwind(AssertUnwindSafe(|| {
        let mut buffer = db.get_table(uf).new_buffer();
        buffer.stage_insert(&[Value::new(2), Value::new(1), Value::new(0)]);
    }));
    assert!(
        raw_uf_staging.is_ok(),
        "an earlier UF table must not be partially switched to typed receipt staging"
    );
}

#[test]
fn low_level_remove_fails_before_staging_when_receipts_are_enabled() {
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
    let receipts = db.enable_causal_receipts();
    register_test_receipt_table(&receipts, table, 2);
    let mut raw_buffer = db.new_buffer(table);
    let one = receipts.intern_test_term("one");
    let zero = receipts.intern_test_term("zero");
    db.stage_source_row(
        table,
        &[Value::new(1), Value::new(0)],
        &[one, zero],
        SourceRef::Synthetic(0),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();

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

#[test]
fn causal_rule_remove_commits_the_native_delete() {
    let mut db = Database::default();
    let table = db.add_table_named(
        SortedWritesTable::new(
            1,
            2,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "test rows are immutable");
                false
            }),
        ),
        "TrackedDelete".into(),
        iter::empty(),
        iter::empty(),
    );
    let receipts = db.enable_causal_receipts();
    register_test_receipt_table(&receipts, table, 2);
    let key = Value::new(1);
    let timestamp = Value::new(0);
    install_test_row_terms(&receipts, &[key, timestamp]);
    db.stage_source_row(
        table,
        &[key, timestamp],
        &[
            receipts.lookup_term(TEST_REPLAY_SORT, key).unwrap(),
            receipts.lookup_term(TEST_REPLAY_SORT, timestamp).unwrap(),
        ],
        SourceRef::Synthetic(740),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();
    let removed_fact = committed_fact_id(&db, table, key);

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let matched_key = query.new_var_named("key");
    let matched_timestamp = query.new_var_named("timestamp");
    let atom = query
        .add_atom(table, &[matched_key.into(), matched_timestamp.into()], &[])
        .unwrap();
    let mut action = query.build();
    action.remove(table, &[matched_key.into()]).unwrap();
    action.remove(table, &[matched_key.into()]).unwrap();
    action.build_with_receipts(
        "tracked-delete",
        RuleReceiptSpec::new(740, [atom], [matched_key]),
    );
    let rules = rules.build();

    db.set_causal_wave(CausalWave::new(1));
    db.run_rule_set(&rules, ReportLevel::TimeOnly);
    db.finalize_causal_wave();
    assert!(db.get_table(table).get_row(&[key]).is_none());
    receipts
        .with_view(|view| {
            assert_eq!(view.totals().removals, 1);
            let removal = view.removal(0)?;
            assert_eq!(removal.wave, CausalWave::new(1));
            assert_eq!(removal.removed_fact, removed_fact);
            let match_record = view.matched(removal.cause)?;
            assert_eq!(match_record.premises, &[removed_fact]);
            assert_eq!(view.counters().effective_removals, 1);
            assert_eq!(view.counters().relation_removals, 0);
            Ok(())
        })
        .unwrap();
}

#[test]
fn causal_missing_rule_remove_records_nothing() {
    let mut db = Database::default();
    let trigger = db.add_table(
        SortedWritesTable::new(1, 1, None, vec![], Box::new(|_, _, _, _| false)),
        iter::empty(),
        iter::empty(),
    );
    let target = db.add_table(
        SortedWritesTable::new(1, 1, None, vec![], Box::new(|_, _, _, _| false)),
        iter::empty(),
        iter::empty(),
    );
    let receipts = db.enable_causal_receipts();
    register_test_receipt_table(&receipts, trigger, 1);
    register_test_receipt_table(&receipts, target, 1);
    let trigger_value = Value::new(7410);
    let missing_key = Value::new(7411);
    install_test_row_terms(&receipts, &[trigger_value, missing_key]);
    db.stage_source_row(
        trigger,
        &[trigger_value],
        &[receipts
            .lookup_term(TEST_REPLAY_SORT, trigger_value)
            .unwrap()],
        SourceRef::Synthetic(741),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let matched = query.new_var_named("matched");
    let atom = query.add_atom(trigger, &[matched.into()], &[]).unwrap();
    let mut action = query.build();
    action.remove(target, &[missing_key.into()]).unwrap();
    action.build_with_receipts(
        "missing-delete",
        RuleReceiptSpec::new(741, [atom], [matched]),
    );
    let rules = rules.build();

    db.set_causal_wave(CausalWave::new(1));
    db.run_rule_set(&rules, ReportLevel::TimeOnly);
    db.finalize_causal_wave();
    receipts
        .with_view(|view| {
            assert_eq!(view.totals().removals, 0);
            assert_eq!(view.counters().effective_removals, 0);
            assert_eq!(view.counters().relation_removals, 0);
            Ok(())
        })
        .unwrap();
}

#[test]
fn causal_presence_relation_remove_is_diagnostics_only() {
    let mut db = Database::default();
    let relation = db.add_table(
        SortedWritesTable::new(1, 1, None, vec![], Box::new(|_, _, _, _| false)),
        iter::empty(),
        iter::empty(),
    );
    let receipts = db.enable_causal_receipts();
    register_test_receipt_table_kind(&receipts, relation, 1, ReplayTableKind::PresenceRelation);
    let key = Value::new(7420);
    install_test_row_terms(&receipts, &[key]);
    db.stage_source_row(
        relation,
        &[key],
        &[receipts.lookup_term(TEST_REPLAY_SORT, key).unwrap()],
        SourceRef::Synthetic(742),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let matched = query.new_var_named("matched");
    let atom = query.add_atom(relation, &[matched.into()], &[]).unwrap();
    let mut action = query.build();
    action.remove(relation, &[matched.into()]).unwrap();
    action.build_with_receipts(
        "relation-delete",
        RuleReceiptSpec::new(742, [atom], [matched]),
    );
    let rules = rules.build();

    db.set_causal_wave(CausalWave::new(1));
    db.run_rule_set(&rules, ReportLevel::TimeOnly);
    db.finalize_causal_wave();
    assert!(db.get_table(relation).get_row(&[key]).is_none());
    receipts
        .with_view(|view| {
            assert_eq!(view.totals().removals, 0);
            assert_eq!(view.counters().effective_removals, 0);
            assert_eq!(view.counters().relation_removals, 1);
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
    let receipts = db.enable_causal_receipts();
    register_test_receipt_table(&receipts, table, 1);
    let first = Value::new(7430);
    let second = Value::new(7431);
    install_test_row_terms(&receipts, &[first, second]);
    for (source, value) in [(743, first), (744, second)] {
        db.stage_source_row(
            table,
            &[value],
            &[receipts.lookup_term(TEST_REPLAY_SORT, value).unwrap()],
            SourceRef::Synthetic(source),
        )
        .unwrap();
    }
    assert!(db.merge_all());
    db.finalize_causal_wave();

    let wave = CausalWave::new(1);
    db.set_causal_wave(wave);
    let valid = crate::DeferredEqualityCause::ready(empty_rule_cause(&receipts, 743, wave));
    let foreign_receipts = CausalReceipts::default();
    let foreign_batch = foreign_receipts.pending_rule_batch(744, wave, 0, &[], &[], 1);
    let foreign = crate::DeferredEqualityCause::pending(
        foreign_receipts.pending_rule_cause(&foreign_batch, 0),
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
    let receipts = db.enable_causal_receipts();
    register_test_receipt_table(&receipts, table, 2);
    let key = Value::new(7450);
    receipts.register_table_key_columns(table, 1).unwrap();
    let old_value = Value::new(7451);
    let new_value = Value::new(7452);
    install_test_row_terms(&receipts, &[key, old_value, new_value]);
    db.stage_source_row(
        table,
        &[key, old_value],
        &[
            receipts.lookup_term(TEST_REPLAY_SORT, key).unwrap(),
            receipts.lookup_term(TEST_REPLAY_SORT, old_value).unwrap(),
        ],
        SourceRef::Synthetic(745),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();
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
    action.build_with_receipts(
        "replace-after-delete",
        RuleReceiptSpec::new(745, [atom], [matched_key, matched_value]),
    );
    let rules = rules.build();

    db.set_causal_wave(CausalWave::new(1));
    db.run_rule_set(&rules, ReportLevel::TimeOnly);
    db.finalize_causal_wave();
    let row = db
        .get_table(table)
        .get_row(&[key])
        .expect("the replacement row must be committed");
    assert_eq!(row.vals.as_slice(), &[key, new_value]);
    // Permanent occurrence-liveness canary. The temporary differential oracle
    // was removed with the owned compatibility model.
    receipts
        .with_view(|view| {
            assert_eq!(view.totals().facts, 2);
            assert_eq!(view.totals().removals, 1);
            let removal = view.removal(0)?;
            assert_eq!(removal.removed_fact, removed_fact);
            let replacement = FactId::new(removed_fact.get() + 1);
            assert_eq!(
                removal.cause,
                cause_rule_match(view.fact(replacement)?.cause).unwrap()
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
                Err(crate::ReceiptViewError::FactNoLongerLive {
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
            assert!(view.fact_key_at(removed_fact, before_removal).is_ok());
            assert!(matches!(
                view.fact_key_at(removed_fact, removal.position),
                Err(crate::ReceiptViewError::FactNoLongerLive { fact, .. })
                    if fact == removed_fact
            ));
            assert!(matches!(
                view.fact_cell_at(old_cell, replacement_record.position),
                Err(crate::ReceiptViewError::FactNoLongerLive { fact, .. })
                    if fact == removed_fact
            ));
            assert!(matches!(
                view.fact_key_at(removed_fact, replacement_record.position),
                Err(crate::ReceiptViewError::FactNoLongerLive { fact, .. })
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
fn mixed_fallback_does_not_eagerly_install_a_structural_origin() {
    let mut db = Database::default();
    let input = db.add_table(
        SortedWritesTable::new(
            1,
            2,
            None,
            vec![],
            Box::new(|_, left, right, _| {
                assert_eq!(left, right, "input rows are immutable");
                false
            }),
        ),
        iter::empty(),
        iter::empty(),
    );
    let receipts = db.enable_causal_receipts();
    register_test_receipt_table(&receipts, input, 2);
    for (ordinal, value) in [1, 2, 3, 4].into_iter().enumerate() {
        let value = Value::new(value);
        let timestamp = Value::from_usize(ordinal + 10);
        let terms = [value, timestamp].map(|raw| {
            receipts.intern_literal(
                TEST_REPLAY_SORT,
                ReplayLiteral::Internal(raw.index() as u64),
                raw,
            )
        });
        db.stage_source_row(
            input,
            &[value, timestamp],
            &terms,
            SourceRef::Synthetic(ordinal as u64),
        )
        .unwrap();
    }
    assert!(db.merge_all());
    db.finalize_causal_wave();

    let primary = db.add_external_function(Box::new(make_external_func(|_, args| {
        let [value] = args else { panic!() };
        value
            .index()
            .is_multiple_of(2)
            .then(|| Value::from_usize(value.index() + 100))
    })));
    let fallback = db.add_external_function(Box::new(make_external_func(|_, args| {
        let [value] = args else { panic!() };
        Some(Value::from_usize(value.index() + 200))
    })));

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let value = query.new_var_named("value");
    let timestamp = query.new_var_named("timestamp");
    query
        .add_atom(input, &[value.into(), timestamp.into()], &[])
        .unwrap();
    let mut action = query.build();
    action
        .call_external_with_fallback_replay(
            primary,
            &[value.into()],
            fallback,
            &[value.into()],
            Some(ReplayConstructorSpec::new(
                TEST_REPLAY_SORT,
                ReplayOpId::new(700),
                [TEST_REPLAY_SORT],
            )),
        )
        .unwrap();
    action.build();
    let rules = rules.build();
    assert!(!db.run_rule_set(&rules, ReportLevel::TimeOnly).changed);

    for output in [102, 104, 201, 203] {
        assert_eq!(
            receipts.lookup_term(TEST_REPLAY_SORT, Value::new(output)),
            None,
            "mixed fallbacks cannot assign one static producer and must stay lazy"
        );
    }
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
