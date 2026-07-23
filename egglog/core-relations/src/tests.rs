use std::{
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

use crate::{
    CausalReceipts, CausalWave, CheckEndpointSource, CheckReceiptSpec, FactId,
    GuardedRuleSetRunOutcome, PlanStrategy, ReplayConstructorSpec, ReplayLiteral, ReplayOpId,
    ReplaySortId, ReplayTerm, RuleReceiptSpec, SourceReceiptSpec, SourceRef,
    action::{ExecutionState, Instr, WriteVal},
    common::Value,
    free_join::{
        CounterId, Database, TableId,
        execute::{materialized_witness_test_counts, reset_materialized_witness_test_counts},
        plan::{JoinStage, MatScanMode, Plan},
    },
    make_external_func,
    offsets::RowId,
    query::RuleSetBuilder,
    table::{SortedWritesTable, causal_lookup_counters, reset_causal_lookup_counters},
    table_shortcuts::v,
    table_spec::{ColumnId, Constraint, Table},
    uf::DisplacedTable,
};

const TEST_REPLAY_SORT: ReplaySortId = ReplaySortId::new(0);

fn register_test_receipt_table(receipts: &CausalReceipts, table: TableId, columns: usize) {
    receipts
        .register_table_layout(table, &vec![Some(TEST_REPLAY_SORT); columns])
        .unwrap();
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

    let snapshot = receipts.snapshot();
    let output_fact = snapshot
        .facts
        .iter()
        .find(|fact| fact.table == output)
        .expect("the effective source action must publish one fact");
    assert_eq!(
        output_fact.cause,
        crate::FactCause::Source(SourceRef::Synthetic(401))
    );
    assert!(
        snapshot.matches.is_empty(),
        "source actions must not manufacture RuleMatch records"
    );
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

    let snapshot = receipts.snapshot();
    assert_eq!(
        snapshot
            .check_roots
            .iter()
            .map(|root| root.check)
            .collect::<Vec<_>>(),
        [4, 9],
        "snapshot root order must depend only on stable check IDs"
    );
    for root in &snapshot.check_roots {
        assert_eq!(root.wave, CausalWave::new(3));
        assert_eq!(root.premises.as_ref(), &[second_left_fact, right_fact]);
        assert_eq!(root.as_of_edges, crate::EqualityEdgeCount::new(2));
        assert_eq!(
            root.equalities.as_ref(),
            &[(
                crate::EqualityEndpoint {
                    sort,
                    term: term(second_left),
                    raw: right,
                },
                crate::EqualityEndpoint {
                    sort,
                    term: term(right),
                    raw: right,
                },
            )]
        );
        assert_eq!(root.equalities[0].0.raw, root.equalities[0].1.raw);
        assert_ne!(
            root.equalities[0].0.term, root.equalities[0].1.term,
            "equal runtime values must retain their distinct premise-owned syntax"
        );
    }
    assert_eq!(
        snapshot.check_roots,
        receipts.snapshot().check_roots,
        "repeated snapshots must preserve exact root contents and order"
    );
    assert_eq!(
        snapshot.matches.len(),
        2,
        "only the two effective equality-producing rules should have matches"
    );
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
    assert!(
        receipts.snapshot().check_roots.is_empty(),
        "term resolution must complete before any check root is published"
    );
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
fn causal_receipts_record_only_effective_constructor_and_union_commits() {
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
        .register_table_layout(input, &[Some(value_sort), None])
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
        &[Value::new(7), Value::new(0)],
        &[input_term, crate::ReplayTermId::MISSING],
        SourceRef::Synthetic(0),
    )
    .unwrap();
    assert!(db.merge_all());

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let value = query.new_var_named("value");
    let input_ts = query.new_var_named("input_ts");
    let input_atom = query
        .add_atom(input, &[value.into(), input_ts.into()], &[])
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
            value.into(),
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
                crate::RuleBindingSpec::constant(input_term, value_sort),
            ],
        ),
    );
    let rule_set = rules.build();

    db.set_causal_wave(CausalWave::new(1));
    let first = db.run_rule_set(&rule_set, ReportLevel::TimeOnly);
    assert!(first.changed);
    db.finalize_causal_wave();

    let snapshot = receipts.snapshot();
    let source = snapshot
        .facts
        .iter()
        .find(|fact| fact.table == input)
        .expect("source fact must be committed");
    let constructor_fact = snapshot
        .facts
        .iter()
        .find(|fact| fact.table == constructor)
        .expect("constructor fact must be committed");
    let derived_fact = snapshot
        .facts
        .iter()
        .find(|fact| fact.table == derived)
        .expect("derived fact must be committed");
    assert_ne!(source.id, constructor_fact.id);
    assert_ne!(source.id, derived_fact.id);
    let match_record = snapshot
        .matches
        .iter()
        .find(|record| record.id == constructor_fact.cause.rule_match().unwrap())
        .expect("effective constructor must promote its match");
    assert_eq!(match_record.wave, CausalWave::new(1));
    assert_eq!(match_record.premises.as_ref(), &[source.id]);
    assert_eq!(match_record.terms.as_ref(), &[input_term, input_term]);
    assert_eq!(derived_fact.cause.rule_match(), Some(match_record.id));
    let node_term = constructor_fact.terms[1];
    assert_eq!(
        constructor_fact.terms.as_ref(),
        &[input_term, node_term, crate::ReplayTermId::MISSING]
    );
    assert_eq!(derived_fact.terms.as_ref(), constructor_fact.terms.as_ref());
    assert_eq!(
        receipts.replay_term(node_term).unwrap(),
        ReplayTerm::Call {
            sort: node_sort,
            op: node_op,
            children: [input_term].into(),
        }
    );
    assert_eq!(snapshot.equalities.len(), 1);
    assert_eq!(snapshot.equality_nodes.len(), 1);
    let equality = &snapshot.equalities[0];
    assert_eq!(equality.wave, CausalWave::new(1));
    assert_eq!(equality.left.sort, node_sort);
    assert_eq!(equality.left.term, node_term);
    assert_eq!(equality.right.raw, Value::new(7));
    assert_eq!(equality.right.sort, node_sort);
    assert_eq!(equality.right.term, input_as_node_term);
    assert_eq!(
        (equality.native_parent, equality.native_child),
        if equality.left.raw < equality.right.raw {
            (equality.left.raw, equality.right.raw)
        } else {
            (equality.right.raw, equality.left.raw)
        }
    );
    assert_eq!(snapshot.equality_nodes[0].id, equality.id);
    assert_eq!(snapshot.equality_nodes[0].edge, equality.id);
    assert_eq!(
        snapshot.equality_nodes[0].left,
        crate::EqComponentRef::Term(node_term)
    );
    assert_eq!(
        snapshot.equality_nodes[0].right,
        crate::EqComponentRef::Term(input_as_node_term)
    );
    assert_eq!(
        equality.reason,
        crate::EqualityReason::RuleUnion(match_record.id)
    );
    assert_eq!(snapshot.counters.provisional_matches, 0);
    assert_eq!(snapshot.counters.promoted_matches, 1);
    assert_eq!(snapshot.counters.premise_handles, 1);
    assert_eq!(
        snapshot.counters.term_handles, 2,
        "match terms are counted once; fact-owned term ranges are separate storage"
    );
    assert_eq!(snapshot.counters.live_provisional_bytes, 0);
    assert!(snapshot.counters.peak_provisional_bytes > 0);
    assert_eq!(snapshot.counters.promotion_misses, 0);
    assert_eq!(
        receipts.fact_record(source.id).unwrap(),
        source.clone(),
        "FactId must select its dense slot without scanning other facts"
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
    let after_hit = receipts.snapshot();
    let consumed_fact = after_hit
        .facts
        .iter()
        .find(|fact| fact.table == consumed)
        .expect("C must consume the derived B fact");
    assert_eq!(
        consumed_fact.terms.as_ref(),
        &[input_term, node_term, crate::ReplayTermId::MISSING]
    );
    let consumed_match = after_hit
        .matches
        .iter()
        .find(|matched| matched.id == consumed_fact.cause.rule_match().unwrap())
        .unwrap();
    assert_eq!(consumed_match.premises.as_ref(), &[derived_fact.id]);
    assert_eq!(consumed_match.terms.as_ref(), &[input_term, node_term]);
    assert_eq!(
        receipts.replay_term_counters().interned_nodes,
        nodes_before_hit,
        "constructor hit must reuse the miss path's typed Call"
    );
}

fn empty_rule_cause(receipts: &CausalReceipts, rule: u32, wave: CausalWave) -> crate::CauseDraftId {
    receipts.register_rule_matches(rule, wave, 0, &[], &[], &[], &[0])[0].1
}

fn stage_test_union(
    db: &Database,
    table: TableId,
    cause: crate::CauseDraftId,
    sort: ReplaySortId,
    left: Value,
    right: Value,
    timestamp: Value,
) {
    db.with_execution_state(|state| {
        state.set_active_cause(Some(cause));
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

#[derive(Default)]
struct TestCauseDependencies {
    sources: Vec<SourceRef>,
    rules: Vec<crate::RuleMatchId>,
    facts: Vec<FactId>,
    rebuilds: Vec<crate::RebuildDependency>,
}

fn test_cause_dependencies(
    snapshot: &crate::ReceiptSnapshot,
    root: crate::ReceiptCauseId,
) -> TestCauseDependencies {
    let mut result = TestCauseDependencies::default();
    for dependency in snapshot.cause_dependencies(root) {
        match dependency {
            crate::ReceiptCauseDependency::Source(source) => {
                result.sources.push(source.clone());
            }
            crate::ReceiptCauseDependency::Rule(rule) => result.rules.push(rule),
            crate::ReceiptCauseDependency::Fact(fact) => result.facts.push(fact),
            crate::ReceiptCauseDependency::Rebuild {
                wave,
                prior_fact,
                as_of_edges,
                equalities,
            } => {
                result.facts.push(prior_fact);
                result.rebuilds.push(crate::RebuildDependency {
                    wave,
                    prior_fact,
                    equalities: crate::EqualityLandmark {
                        as_of_edges,
                        pairs: equalities.into(),
                    },
                });
            }
        }
    }
    result
}

fn test_congruence_dependencies(
    snapshot: &crate::ReceiptSnapshot,
    reason: &crate::EqualityReason,
) -> (TestCauseDependencies, crate::EqualityLandmark) {
    let crate::EqualityReason::Congruence {
        cause,
        wave,
        as_of_edges,
    } = reason
    else {
        panic!("expected a congruence reason, got {reason:?}")
    };
    let dependencies = test_cause_dependencies(snapshot, *cause);
    let mut pairs = Vec::new();
    for rebuild in &dependencies.rebuilds {
        assert_eq!(rebuild.wave, *wave);
        assert_eq!(rebuild.equalities.as_of_edges, *as_of_edges);
        pairs.extend_from_slice(&rebuild.equalities.pairs);
    }
    (
        dependencies,
        crate::EqualityLandmark {
            as_of_edges: *as_of_edges,
            pairs: pairs.into_boxed_slice(),
        },
    )
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
            Box::new(|_, left, right, _| {
                assert_eq!(left, right);
                false
            }),
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
    assert!(receipts.snapshot().facts.is_empty());
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
            Box::new(|_, left, right, _| {
                assert_eq!(left, right);
                false
            }),
        ),
        iter::once(uf),
        iter::empty(),
    );
    let receipts = db.enable_causal_receipts();
    let table_sort = ReplaySortId::new(113);
    let uf_sort = ReplaySortId::new(114);
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
        receipts
            .install_source_row(
                rebuilt,
                &[value, Value::new(0)],
                &[term, crate::ReplayTermId::MISSING],
            )
            .unwrap();
        source_rows.stage_insert_with_cause(&[value, Value::new(0)], source_cause);
    }
    drop(source_rows);
    assert!(db.merge_all());
    let prior_fact = committed_fact_id(&db, rebuilt, old);

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

    receipts.intern_literal(table_sort, ReplayLiteral::Internal(new.index() as u64), new);
    assert!(
        db.apply_rebuild(uf, &[rebuilt], Value::new(2)),
        "retry must rescan the UF delta rejected before cursor commit"
    );
    db.finalize_causal_wave();
    assert!(db.get_table(rebuilt).get_row(&[old]).is_none());
    assert!(db.get_table(rebuilt).get_row(&[new]).is_some());
    assert_eq!(receipts.snapshot().counters.rebuild_causes, 1);
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
                    Box::new(|_, left, right, _| {
                        assert_eq!(left, right);
                        false
                    }),
                )
            };
            let first = db.add_table(relation(), iter::once(uf), iter::empty());
            let second = db.add_table(relation(), iter::once(uf), iter::empty());
            let receipts = db.enable_causal_receipts();
            let table_sort = ReplaySortId::new(115);
            let uf_sort = ReplaySortId::new(116);
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
                    receipts
                        .install_source_row(
                            table,
                            &[value, Value::new(0)],
                            &[term, crate::ReplayTermId::MISSING],
                        )
                        .unwrap();
                    rows.stage_insert_with_cause(&[value, Value::new(0)], source_cause);
                }
            }
            assert!(db.merge_all());
            let first_fact = committed_fact_id(&db, first, first_old);
            let second_fact = committed_fact_id(&db, second, second_old);

            // The first target can rekey exactly, while the second target is
            // deliberately missing the replay term for its canonical value.
            receipts.intern_literal(
                table_sort,
                ReplayLiteral::Internal(first_new.index() as u64),
                first_new,
            );
            for value in [first_old, first_new, second_old, second_new] {
                receipts.intern_literal(
                    uf_sort,
                    ReplayLiteral::Internal(value.index() as u64),
                    value,
                );
            }
            db.set_causal_wave(CausalWave::new(1));
            let union_cause = empty_rule_cause(&receipts, 115, CausalWave::new(1));
            for (old, new) in [(first_old, first_new), (second_old, second_new)] {
                stage_test_union(
                    &db,
                    uf,
                    union_cause,
                    uf_sort,
                    old,
                    new,
                    Value::new(1),
                );
            }
            assert!(db.merge_all());
            db.set_causal_wave(CausalWave::new(2));

            let failed = catch_unwind(AssertUnwindSafe(|| {
                db.apply_rebuild(uf, &[first, second], Value::new(2));
            }));
            assert!(failed.is_err());
            assert_eq!(committed_fact_id(&db, first, first_old), first_fact);
            assert_eq!(committed_fact_id(&db, second, second_old), second_fact);
            assert!(db.get_table(first).get_row(&[first_new]).is_none());
            assert!(db.get_table(second).get_row(&[second_new]).is_none());

            receipts.intern_literal(
                table_sort,
                ReplayLiteral::Internal(second_new.index() as u64),
                second_new,
            );
            assert!(
                db.apply_rebuild(uf, &[first, second], Value::new(2)),
                "retry must rescan the successful first target as well as the rejected second target"
            );
            db.finalize_causal_wave();
            for (table, old, new) in [
                (first, first_old, first_new),
                (second, second_old, second_new),
            ] {
                assert!(db.get_table(table).get_row(&[old]).is_none());
                assert!(db.get_table(table).get_row(&[new]).is_some());
            }
            assert_eq!(receipts.snapshot().counters.rebuild_causes, 2);
        });
}

fn capture_same_wave_rebuild_collision(
    row_count: u32,
    collision_count: u32,
    threads: usize,
) -> (crate::ReceiptSnapshot, Vec<FactId>) {
    assert!(row_count >= collision_count && collision_count >= 2);
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(threads)
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
        let causes =
            receipts.register_rule_matches(780, CausalWave::new(0), 0, &[], &[], &[], &lanes);
        let mut initial = db.new_buffer(rebuilt);
        for (index, (_, cause)) in causes.into_iter().enumerate() {
            let index = index as u32;
            initial.stage_insert_with_cause(&[old_key(index), output(index), Value::new(0)], cause);
        }
        drop(initial);
        assert!(db.merge_all());
        let old_facts = (0..collision_count)
            .map(|index| committed_fact_id(&db, rebuilt, old_key(index)))
            .collect::<Vec<_>>();

        db.set_causal_wave(CausalWave::new(1));
        let union_cause = empty_rule_cause(&receipts, 781, CausalWave::new(1));
        db.with_execution_state(|state| {
            state.set_active_cause(Some(union_cause));
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
        (receipts.snapshot(), old_facts)
    })
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
    assert_ne!(
        rebuilt_fact, prior_fact,
        "a semantic rekey creates one immutable fact version"
    );
    assert_eq!(
        receipts.fact_record(rebuilt_fact).unwrap().cause,
        crate::FactCause::Rebuild {
            wave: CausalWave::new(2),
            prior_fact,
            equalities: crate::EqualityLandmark {
                as_of_edges: crate::EqualityEdgeCount::new(1),
                pairs: vec![crate::TypedCellEquality {
                    column: ColumnId::new(0),
                    left: crate::EqualityEndpoint {
                        sort,
                        term: old_term,
                        raw: old,
                    },
                    right: crate::EqualityEndpoint {
                        sort,
                        term: new_term,
                        raw: new,
                    },
                }]
                .into_boxed_slice(),
            },
        }
    );

    let after_rekey = receipts.snapshot();
    let fact_count = after_rekey.facts.len();
    assert_eq!(after_rekey.counters.rebuild_causes, 1);
    assert_eq!(after_rekey.counters.rebuild_equalities, 1);
    assert!(after_rekey.counters.rebuild_bytes > 0);

    db.set_causal_wave(CausalWave::new(3));
    assert!(
        !db.apply_rebuild(uf, &[rebuilt], Value::new(3)),
        "an already-canonical row is a rebuild no-op"
    );
    db.finalize_causal_wave();
    assert_eq!(committed_fact_id(&db, rebuilt, new), rebuilt_fact);
    let after_noop = receipts.snapshot();
    assert_eq!(after_noop.facts.len(), fact_count);
    assert_eq!(after_noop.counters.rebuild_causes, 1);
    assert_eq!(after_noop.counters.rebuild_equalities, 1);

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
    let crate::FactCause::Rebuild { equalities, .. } =
        receipts.fact_record(rebuilt_fact).unwrap().cause
    else {
        panic!("rebuilt fact lost its direct rebuild cause")
    };
    assert_eq!(
        equalities.as_of_edges,
        crate::EqualityEdgeCount::new(1),
        "a later equality edge cannot justify an earlier table rekey"
    );
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
    assert!(receipts.fact_record(old_fact).is_some());
    assert_eq!(native_uf_root(&db, uf, old_output), target_output);
    let snapshot = receipts.snapshot();
    assert_eq!(snapshot.equalities.len(), 2);
    let (dependencies, equalities) =
        test_congruence_dependencies(&snapshot, &snapshot.equalities[1].reason);
    assert_eq!(dependencies.facts, [target_fact, old_fact]);
    assert!(dependencies.rules.is_empty());
    assert_eq!(equalities.as_of_edges, crate::EqualityEdgeCount::new(1));
    assert_eq!(
        equalities.pairs.as_ref(),
        &[crate::TypedCellEquality {
            column: ColumnId::new(0),
            left: crate::EqualityEndpoint {
                sort,
                term: old_key_term,
                raw: old_key,
            },
            right: crate::EqualityEndpoint {
                sort,
                term: target_key_term,
                raw: target_key,
            },
        }]
    );
    assert_eq!(snapshot.equalities[1].wave, CausalWave::new(2));
    assert_eq!(snapshot.equalities[1].left.term, target_output_term);
    assert_eq!(snapshot.equalities[1].right.term, old_output_term);
    assert_eq!(
        snapshot.matches.len(),
        1,
        "congruence must not invent a synthetic rule match"
    );
}

#[test]
fn causal_receipt_same_wave_rebuild_congruence_is_exact_serial_and_parallel() {
    let (serial, serial_old) = capture_same_wave_rebuild_collision(2, 2, 1);
    let serial_equality = serial
        .equalities
        .iter()
        .find(|equality| equality.wave == CausalWave::new(2))
        .expect("serial rebuild collision must apply one congruence union");
    let (serial_dependencies, equalities) =
        test_congruence_dependencies(&serial, &serial_equality.reason);
    let facts = &serial_dependencies.facts;
    assert_eq!(equalities.pairs.len(), 1);
    assert_eq!(facts.len(), 2);
    let prior_rebuild = serial
        .facts
        .iter()
        .find(|fact| fact.id == facts[0])
        .expect("serial congruence prior version must be an immutable fact");
    let crate::FactCause::Rebuild {
        prior_fact,
        equalities: prior_equalities,
        ..
    } = &prior_rebuild.cause
    else {
        panic!("serial congruence prior fact must retain its rebuild cause")
    };
    assert_eq!(prior_equalities.pairs.len(), 1);
    assert_eq!(equalities.as_of_edges, prior_equalities.as_of_edges);
    for (fact_id, pair) in [
        (facts[1], &equalities.pairs[0]),
        (*prior_fact, &prior_equalities.pairs[0]),
    ] {
        let fact = serial.facts.iter().find(|fact| fact.id == fact_id).unwrap();
        assert_eq!(pair.column, ColumnId::new(0));
        assert_eq!(pair.left.sort, ReplaySortId::new(78));
        assert_eq!(pair.right.sort, ReplaySortId::new(78));
        assert_eq!(pair.left.term, fact.terms[0]);
        assert_eq!(pair.right.raw, Value::new(100_000));
        assert!(
            serial
                .explain_equality(pair.left, pair.right, equalities.as_of_edges)
                .is_ok()
        );
    }
    let mut serial_priors = [facts[1].get(), prior_fact.get()];
    let mut expected_serial = [serial_old[0].get(), serial_old[1].get()];
    serial_priors.sort_unstable();
    expected_serial.sort_unstable();
    assert_eq!(serial_priors, expected_serial);

    // The real table threshold forces pre-commit folding. Neither rebuilt
    // proposal has a new FactId when the merge function emits its union, so
    // the equality cause is exactly Merge(Rebuild, Draft(Rebuild)).
    let (parallel, parallel_old) = capture_same_wave_rebuild_collision(20_001, 2, 4);
    let parallel_equality = parallel
        .equalities
        .iter()
        .find(|equality| equality.wave == CausalWave::new(2))
        .expect("parallel rebuild collision must apply one congruence union");
    let (parallel_dependencies, equalities) =
        test_congruence_dependencies(&parallel, &parallel_equality.reason);
    let facts = &parallel_dependencies.facts;
    assert_eq!(facts.len(), 2);
    let mut parallel_priors = [facts[0].get(), facts[1].get()];
    let mut expected_parallel = [parallel_old[0].get(), parallel_old[1].get()];
    parallel_priors.sort_unstable();
    expected_parallel.sort_unstable();
    assert_eq!(parallel_priors, expected_parallel);
    assert_eq!(equalities.pairs.len(), 2);
    assert_eq!(
        equalities.as_of_edges,
        crate::EqualityEdgeCount::new(20_001)
    );
    let mut changed_from = equalities
        .pairs
        .iter()
        .map(|pair| pair.left.raw.index())
        .collect::<Vec<_>>();
    changed_from.sort_unstable();
    assert_eq!(changed_from, [1_000_000, 1_000_001]);
    assert!(
        equalities
            .pairs
            .iter()
            .all(|pair| pair.right.raw == Value::new(100_000))
    );
    let explanation_index = parallel
        .equality_explanation_index(equalities.as_of_edges)
        .unwrap();
    for (fact_id, pair) in facts.iter().copied().zip(equalities.pairs.iter()) {
        let fact = parallel
            .facts
            .iter()
            .find(|fact| fact.id == fact_id)
            .unwrap();
        assert_eq!(pair.column, ColumnId::new(0));
        assert_eq!(pair.left.sort, ReplaySortId::new(78));
        assert_eq!(pair.right.sort, ReplaySortId::new(78));
        assert_eq!(pair.left.term, fact.terms[0]);
        assert_eq!(pair.right, equalities.pairs[0].right);
        assert!(
            explanation_index
                .explain_equality(pair.left, pair.right)
                .is_ok()
        );
    }
}

#[test]
fn causal_receipt_nested_same_wave_rebuild_congruence_keeps_every_leaf() {
    let (snapshot, old_facts) = capture_same_wave_rebuild_collision(20_001, 3, 4);
    let (_equality, dependencies, equalities) = snapshot
        .equalities
        .iter()
        .filter(|equality| equality.wave == CausalWave::new(2))
        .filter_map(|equality| {
            matches!(&equality.reason, crate::EqualityReason::Congruence { .. }).then(|| {
                let (dependencies, equalities) =
                    test_congruence_dependencies(&snapshot, &equality.reason);
                (equality, dependencies, equalities)
            })
        })
        .find(|(_, dependencies, _)| dependencies.facts.len() == 3)
        .expect("third same-key proposal must retain the nested rebuild merge DAG");
    let facts = &dependencies.facts;
    let mut recorded = facts.iter().map(|fact| fact.get()).collect::<Vec<_>>();
    let mut expected = old_facts.iter().map(|fact| fact.get()).collect::<Vec<_>>();
    recorded.sort_unstable();
    expected.sort_unstable();
    assert_eq!(recorded, expected);
    assert_eq!(equalities.pairs.len(), 3);
    assert_eq!(
        equalities.as_of_edges,
        crate::EqualityEdgeCount::new(20_001)
    );
    let explanation_index = snapshot
        .equality_explanation_index(equalities.as_of_edges)
        .unwrap();
    for (fact_id, pair) in facts.iter().copied().zip(equalities.pairs.iter()) {
        let fact = snapshot
            .facts
            .iter()
            .find(|fact| fact.id == fact_id)
            .unwrap();
        assert_eq!(pair.left.term, fact.terms[0]);
        assert_eq!(pair.right.raw, Value::new(100_000));
        assert!(
            explanation_index
                .explain_equality(pair.left, pair.right)
                .is_ok()
        );
    }
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
    let crate::FactCause::Rebuild {
        wave,
        prior_fact: actual_prior,
        equalities,
    } = receipts.fact_record(rebuilt_fact).unwrap().cause
    else {
        panic!("multi-column rekey must have a direct rebuild cause")
    };
    assert_eq!(wave, CausalWave::new(2));
    assert_eq!(actual_prior, prior_fact);
    assert_eq!(equalities.as_of_edges, crate::EqualityEdgeCount::new(2));
    assert_eq!(
        equalities.pairs.as_ref(),
        &[
            crate::TypedCellEquality {
                column: ColumnId::new(0),
                left: crate::EqualityEndpoint {
                    sort,
                    term: old_a_term,
                    raw: old_a,
                },
                right: crate::EqualityEndpoint {
                    sort,
                    term: new_a_term,
                    raw: new_a,
                },
            },
            crate::TypedCellEquality {
                column: ColumnId::new(1),
                left: crate::EqualityEndpoint {
                    sort,
                    term: old_b_term,
                    raw: old_b,
                },
                right: crate::EqualityEndpoint {
                    sort,
                    term: new_b_term,
                    raw: new_b,
                },
            },
        ]
    );
}

#[test]
fn causal_receipt_rebuild_missing_typed_endpoint_fails_before_staging() {
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
    let before = receipts.snapshot();

    let failed = catch_unwind(AssertUnwindSafe(|| {
        db.apply_rebuild(uf, &[rebuilt], Value::new(2));
    }));
    assert!(failed.is_err());
    assert_eq!(
        native_uf_root(&db, uf, old),
        new,
        "UF table was not restored"
    );
    assert_eq!(committed_fact_id(&db, rebuilt, old), prior_fact);
    assert!(db.get_table(rebuilt).get_row(&[new]).is_none());
    assert!(
        !db.merge_all(),
        "a failed rebuild left a staged removal or insertion behind"
    );
    db.finalize_causal_wave();
    let after = receipts.snapshot();
    assert_eq!(after.facts, before.facts);
    assert_eq!(after.equalities, before.equalities);
    assert_eq!(after.counters.rebuild_causes, 0);
    assert_eq!(after.counters.rebuild_equalities, 0);
}

#[test]
fn causal_receipt_rebuild_abort_discards_earlier_rows_before_later_merge() {
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
    let table_sort = ReplaySortId::new(89);
    let uf_sort = ReplaySortId::new(90);
    receipts
        .register_table_layout(rebuilt, &[Some(table_sort), None])
        .unwrap();

    let valid_old = Value::new(100);
    let valid_new = Value::new(90);
    let invalid_old = Value::new(80);
    let invalid_new = Value::new(70);
    let recovery = Value::new(200);
    for raw in [100, 90, 80, 200] {
        receipts.intern_literal(
            table_sort,
            ReplayLiteral::Internal(raw),
            Value::new(raw as u32),
        );
    }
    for raw in [100, 90, 80, 70] {
        receipts.intern_literal(
            uf_sort,
            ReplayLiteral::Internal(raw),
            Value::new(raw as u32),
        );
    }
    let stage_source = |db: &Database, value: Value, source| {
        db.stage_source_row(
            rebuilt,
            &[value, Value::new(0)],
            &[
                receipts.lookup_term(table_sort, value).unwrap(),
                crate::ReplayTermId::MISSING,
            ],
            SourceRef::Synthetic(source),
        )
        .unwrap();
    };
    // Separate barriers make row order deterministic: the first row is fully
    // validated and staged before the second row discovers its missing term.
    stage_source(&db, valid_old, 890);
    assert!(db.merge_all());
    stage_source(&db, invalid_old, 891);
    assert!(db.merge_all());
    let valid_fact = committed_fact_id(&db, rebuilt, valid_old);
    let invalid_fact = committed_fact_id(&db, rebuilt, invalid_old);

    db.set_causal_wave(CausalWave::new(1));
    let union_cause = empty_rule_cause(&receipts, 89, CausalWave::new(1));
    stage_test_union(
        &db,
        uf,
        union_cause,
        uf_sort,
        valid_old,
        valid_new,
        Value::new(1),
    );
    stage_test_union(
        &db,
        uf,
        union_cause,
        uf_sort,
        invalid_old,
        invalid_new,
        Value::new(1),
    );
    assert!(db.merge_all());
    db.set_causal_wave(CausalWave::new(2));
    let before = receipts.snapshot();

    let failed = catch_unwind(AssertUnwindSafe(|| {
        db.apply_rebuild(uf, &[rebuilt], Value::new(2));
    }));
    assert!(failed.is_err());

    // A later ordinary notification drains the rejected guarded batches. If
    // the first staged rekey leaked, this merge would make it observable.
    stage_source(&db, recovery, 892);
    assert!(db.merge_all());
    assert_eq!(committed_fact_id(&db, rebuilt, valid_old), valid_fact);
    assert_eq!(committed_fact_id(&db, rebuilt, invalid_old), invalid_fact);
    assert!(db.get_table(rebuilt).get_row(&[valid_new]).is_none());
    assert!(db.get_table(rebuilt).get_row(&[invalid_new]).is_none());
    assert!(db.get_table(rebuilt).get_row(&[recovery]).is_some());

    db.finalize_causal_wave();
    let after = receipts.snapshot();
    assert_eq!(after.equalities, before.equalities);
    assert_eq!(after.facts.len(), before.facts.len() + 1);
    assert_eq!(after.counters.rebuild_causes, 0);
    assert_eq!(after.counters.rebuild_equalities, 0);
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
    let uf_sort = ReplaySortId::new(92);
    for table in [first, second] {
        receipts
            .register_table_layout(table, &[Some(table_sort), None])
            .unwrap();
    }

    let first_old = Value::new(120);
    let first_new = Value::new(110);
    let second_old = Value::new(90);
    let second_new = Value::new(80);
    let recovery = Value::new(200);
    for raw in [120, 110, 90, 200] {
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
    assert!(db.merge_all());
    let first_fact = committed_fact_id(&db, first, first_old);
    let second_fact = committed_fact_id(&db, second, second_old);

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
    assert!(db.get_table(second).get_row(&[second_new]).is_none());
    assert!(db.get_table(first).get_row(&[recovery]).is_some());

    db.finalize_causal_wave();
    let snapshot = receipts.snapshot();
    assert_eq!(snapshot.counters.rebuild_causes, 0);
    assert_eq!(snapshot.counters.rebuild_equalities, 0);
}

#[test]
fn causal_receipt_same_id_refresh_fails_before_row_mutation() {
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

    let failed = catch_unwind(AssertUnwindSafe(|| {
        db.refresh_rows_for_values(&[rebuilt], &[key], Value::new(1));
    }));
    assert!(failed.is_err());
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

    let snapshot = receipts.snapshot();
    assert_eq!(snapshot.equality_nodes.len(), 2);
    assert_eq!(snapshot.equalities.len(), 2);
    assert_eq!(snapshot.matches.len(), 2);
    assert!(snapshot.matches.iter().all(|matched| matched.rule != 82));
    assert_eq!(snapshot.counters.redundant_unions, 1);
    let endpoint = |term, raw| crate::EqualityEndpoint { sort, term, raw };
    assert_eq!(
        snapshot
            .explain_equality(
                endpoint(a_term, a),
                endpoint(c_term, c),
                crate::EqualityEdgeCount::new(2),
            )
            .unwrap()
            .as_ref(),
        &[crate::EqualityEdgeId::new(1), crate::EqualityEdgeId::new(2)]
    );
    assert_eq!(
        snapshot
            .explain_equality(
                endpoint(b_term, b),
                endpoint(c_term, c),
                crate::EqualityEdgeCount::new(2),
            )
            .unwrap()
            .as_ref(),
        &[crate::EqualityEdgeId::new(2)]
    );
    assert!(
        snapshot
            .explain_equality(
                endpoint(a_term, a),
                endpoint(c_term, c),
                crate::EqualityEdgeCount::new(1),
            )
            .is_err(),
        "the lazy explanation must not cross its historical cutoff"
    );
    let first = &snapshot.equality_nodes[0];
    let second = &snapshot.equality_nodes[1];
    assert_eq!(first.id, crate::EqNodeId::new(1));
    assert_eq!(first.edge, first.id);
    assert_eq!(first.left, crate::EqComponentRef::Term(a_term));
    assert_eq!(first.right, crate::EqComponentRef::Term(b_term));
    assert_eq!(second.id, crate::EqNodeId::new(2));
    assert_eq!(second.edge, second.id);
    assert_eq!(second.left, crate::EqComponentRef::Node(first.id));
    assert_eq!(second.right, crate::EqComponentRef::Term(c_term));
    assert_eq!(
        (
            snapshot.equalities[0].wave,
            snapshot.equalities[0].native_parent,
            snapshot.equalities[0].native_child,
        ),
        (CausalWave::new(1), b, a)
    );
    assert_eq!(
        (
            snapshot.equalities[1].wave,
            snapshot.equalities[1].native_parent,
            snapshot.equalities[1].native_child,
        ),
        (CausalWave::new(2), c, b)
    );
    assert_eq!(native_uf_root(&db, uf, a), c);
    assert_eq!(native_uf_root(&db, uf, b), c);
    assert_eq!(native_uf_root(&db, uf, c), c);
    assert_eq!(
        snapshot.equality_nodes[0].left,
        crate::EqComponentRef::Term(a_term),
        "native path compression must not rewrite immutable join topology"
    );
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
                buffer.stage_insert_with_cause(&[left, right, Value::new(1)], cause);
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
        let snapshot = receipts.snapshot();
        assert!(snapshot.matches.is_empty());
        assert!(snapshot.equality_nodes.is_empty());
        assert!(snapshot.equalities.is_empty());
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
    let receipts = db.enable_causal_receipts();
    receipts
        .register_table_layout(target, &[Some(sort), Some(sort)])
        .unwrap();
    receipts
        .register_table_layout(proposal, &[Some(sort), Some(sort)])
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

    let snapshot = receipts.snapshot();
    assert_eq!(snapshot.equalities.len(), 1);
    assert_eq!(snapshot.equality_nodes.len(), 1);
    let equality = &snapshot.equalities[0];
    let (rule_match, recorded_prior) = match &equality.reason {
        crate::EqualityReason::MergeFn { cause } => {
            let dependencies = test_cause_dependencies(&snapshot, *cause);
            assert_eq!(dependencies.rules.len(), 1);
            assert_eq!(dependencies.facts.len(), 1);
            (dependencies.rules[0], dependencies.facts[0])
        }
        ref other => panic!("expected exact MergeFn reason, got {other:?}"),
    };
    assert_eq!(recorded_prior, prior_fact);
    let matched = snapshot
        .matches
        .iter()
        .find(|matched| matched.id == rule_match)
        .unwrap();
    assert_eq!(matched.rule, 100);
    assert_eq!(matched.premises.as_ref(), &[proposal_fact]);
    assert_eq!(equality.left.term, prior_term);
    assert_eq!(equality.right.term, incoming_term);
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

    let snapshot = receipts.snapshot();
    let crate::EqualityReason::MergeFn { cause } = &snapshot.equalities[0].reason else {
        panic!("same-wave merge-function union lost its proposal DAG")
    };
    let dependencies = test_cause_dependencies(&snapshot, *cause);
    assert!(dependencies.facts.is_empty());
    let rules = dependencies
        .rules
        .iter()
        .map(|id| {
            snapshot
                .matches
                .iter()
                .find(|record| record.id == *id)
                .unwrap()
                .rule
        })
        .collect::<Vec<_>>();
    assert_eq!(rules, [109, 110, 111]);
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

    let snapshot = receipts.snapshot();
    assert_eq!(snapshot.equalities.len(), PROPOSALS - 1);
    assert_eq!(snapshot.matches.len(), PROPOSALS);
    assert_eq!(snapshot.causes.len(), PROPOSALS * 2 - 1);
    assert!(
        std::mem::size_of::<crate::EqualityReason>() <= 32,
        "each equality reason must retain only a constant-size shared root"
    );
    let crate::EqualityReason::MergeFn { cause } = snapshot.equalities.last().unwrap().reason
    else {
        panic!("deep merge prefix lost its shared exact cause")
    };
    let dependencies = test_cause_dependencies(&snapshot, cause);
    assert_eq!(dependencies.rules.len(), PROPOSALS);
    let rules = dependencies
        .rules
        .iter()
        .map(|rule| {
            snapshot
                .matches
                .iter()
                .find(|record| record.id == *rule)
                .unwrap()
                .rule
        })
        .collect::<Vec<_>>();
    assert_eq!(rules, (0..PROPOSALS as u32).collect::<Vec<_>>());
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
    let snapshot = receipts.snapshot();
    assert_eq!(snapshot.equalities.len(), 1);
    assert_eq!(snapshot.equality_nodes.len(), 1);
    assert_eq!(snapshot.matches.len(), 1);
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
    let snapshot = receipts.snapshot();
    assert_eq!(snapshot.equalities.len(), 1);
    assert_eq!(snapshot.equality_nodes.len(), 1);
    assert_eq!(snapshot.matches.len(), 1);
    assert_eq!(snapshot.counters.redundant_unions, 0);
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

    let snapshot = receipts.snapshot();
    assert_eq!(snapshot.equalities.len(), 2);
    assert!(
        snapshot
            .equalities
            .iter()
            .any(|equality| equality.left.sort == first_sort)
    );
    assert!(
        snapshot
            .equalities
            .iter()
            .any(|equality| equality.left.sort == second_sort)
    );
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
            receipts.source_draft(SourceRef::Synthetic(130)),
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
    assert!(receipts.snapshot().equalities.is_empty());
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
            receipts.source_draft(SourceRef::Synthetic(135)),
            proposal,
        );
    }
    let mut state = ExecutionState::new(db.read_only_view(), Default::default());
    assert!(uf.merge(&mut state).added);
    db.finalize_causal_wave();
    let snapshot = receipts.snapshot();
    assert_eq!(snapshot.equalities.len(), 1);
    assert_eq!(snapshot.counters.redundant_unions, 1);
    assert_eq!(snapshot.matches.len(), 1);
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
            receipts.source_draft(SourceRef::Synthetic(131)),
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
    let snapshot = receipts.snapshot();
    assert!(snapshot.equalities.is_empty());
    assert!(snapshot.equality_nodes.is_empty());
    assert!(snapshot.matches.is_empty());
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
            receipts.source_draft(SourceRef::Synthetic(134)),
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
    let snapshot = receipts.snapshot();
    assert_eq!(snapshot.equalities.len(), 3);
    assert_eq!(
        snapshot.equalities.last().unwrap().id,
        crate::EqNodeId::new(3)
    );
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
    let counter = db.add_counter();
    let receipts = db.enable_causal_receipts();
    let value_sort = ReplaySortId::new(10);
    let primitive_sort = ReplaySortId::new(11);
    receipts
        .register_table_layout(input, &[Some(value_sort), None])
        .unwrap();
    receipts
        .register_table_layout(derived, &[Some(value_sort), Some(primitive_sort)])
        .unwrap();
    let value = Value::new(7);
    let primitive = Value::new(0);
    let value_term = receipts.intern_literal(value_sort, ReplayLiteral::I64(7), value);
    let primitive_term = receipts.intern_literal(primitive_sort, ReplayLiteral::I64(0), primitive);
    db.stage_source_row(
        input,
        &[value, Value::new(0)],
        &[value_term, crate::ReplayTermId::MISSING],
        SourceRef::Synthetic(70),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();

    let mut rules = RuleSetBuilder::new(&mut db);
    let mut query = rules.new_rule();
    let x = query.new_var_named("x");
    let timestamp = query.new_var_named("timestamp");
    let input_atom = query
        .add_atom(input, &[x.into(), timestamp.into()], &[])
        .unwrap();
    let mut action = query.build();
    let primitive_var = action.read_counter(counter);
    action
        .insert(derived, &[x.into(), primitive_var.into()])
        .unwrap();
    action.build_with_receipts(
        "current-value-receipt",
        RuleReceiptSpec::new(60, [input_atom], [x, primitive_var])
            .with_current_vars([(primitive_var, primitive_sort)]),
    );
    let rules = rules.build();
    db.set_causal_wave(CausalWave::new(1));
    assert!(db.run_rule_set(&rules, ReportLevel::TimeOnly).changed);
    db.finalize_causal_wave();

    let snapshot = receipts.snapshot();
    let derived_fact = snapshot
        .facts
        .iter()
        .find(|fact| fact.table == derived)
        .unwrap();
    assert_eq!(
        derived_fact.terms.as_ref(),
        &[value_term, primitive_term],
        "ignored source columns stay row-aligned while a primitive-only variable resolves from the typed current-value map"
    );
    let matched = snapshot
        .matches
        .iter()
        .find(|matched| matched.id == derived_fact.cause.rule_match().unwrap())
        .unwrap();
    assert_eq!(matched.terms.as_ref(), &[value_term, primitive_term]);
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
    let snapshot = receipts.snapshot();
    assert_eq!(snapshot.matches.len(), 1);
    let premise = snapshot.matches[0].premises[0];
    assert_eq!(
        snapshot
            .facts
            .iter()
            .find(|fact| fact.id == premise)
            .expect("the retained premise must be a durable source fact")
            .cause,
        crate::FactCause::Source(SourceRef::Synthetic(900)),
        "the conditional action must retain the condition-true lane"
    );
    let outputs = snapshot
        .facts
        .iter()
        .filter(|fact| fact.table == output)
        .collect::<Vec<_>>();
    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0].cause.rule_match(), Some(snapshot.matches[0].id));

    db.set_causal_wave(CausalWave::new(2));
    assert!(!db.run_rule_set(&rules, ReportLevel::TimeOnly).changed);
    db.finalize_causal_wave();
    let repeated = receipts.snapshot();
    assert_eq!(
        repeated.matches.len(),
        1,
        "a no-op firing stays provisional"
    );
    assert_eq!(
        repeated
            .facts
            .iter()
            .filter(|fact| fact.table == output)
            .count(),
        1
    );
}

#[test]
fn causal_receipts_serial_merge_records_final_output_row_terms() {
    let mut db = Database::default();
    let table = db.add_table(
        SortedWritesTable::new(
            1,
            2,
            None,
            vec![],
            Box::new(|_, left, right, out| {
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
    register_test_receipt_table(&receipts, table, 2);
    for value in [Value::new(0), Value::new(1), Value::new(2), Value::new(9)] {
        install_test_row_terms(&receipts, &[value]);
    }
    let one = receipts
        .lookup_term(TEST_REPLAY_SORT, Value::new(1))
        .unwrap();
    let zero = receipts
        .lookup_term(TEST_REPLAY_SORT, Value::new(0))
        .unwrap();
    db.stage_source_row(
        table,
        &[Value::new(1), Value::new(0)],
        &[one, zero],
        SourceRef::Synthetic(90),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_causal_wave();

    db.set_causal_wave(CausalWave::new(1));
    let cause = receipts.register_rule_matches(62, CausalWave::new(1), 0, &[], &[], &[], &[0])[0].1;
    let mut update = db.new_buffer(table);
    update.stage_insert_with_cause(&[Value::new(1), Value::new(2)], cause);
    drop(update);
    assert!(db.merge_all());
    db.finalize_causal_wave();

    let latest = receipts.snapshot().facts.pop().unwrap();
    assert_eq!(
        db.get_table(table)
            .get_row(&[Value::new(1)])
            .unwrap()
            .vals
            .as_slice(),
        &[Value::new(1), Value::new(9)]
    );
    assert_eq!(
        latest.terms.as_ref(),
        &[
            one,
            receipts
                .lookup_term(TEST_REPLAY_SORT, Value::new(9))
                .unwrap(),
        ],
        "serial FactId terms must use merge output scratch, not the proposal row"
    );
}

#[test]
fn causal_receipts_parallel_merge_preserves_proposal_and_fact_causes() {
    const N_KEYS: u32 = 20_001;
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(4)
        .build()
        .unwrap();
    pool.install(|| {
        let mut db = Database::default();
        let table = db.add_table_named(
            SortedWritesTable::new(
                1,
                2,
                None,
                vec![],
                Box::new(|_, left, right, out| {
                    if right[1] > left[1] {
                        out.extend_from_slice(&[right[0], Value::from_usize(right[1].index() + 1)]);
                        true
                    } else {
                        false
                    }
                }),
            ),
            "ParallelMerge".into(),
            iter::empty(),
            iter::empty(),
        );
        let receipts = db.enable_causal_receipts();
        register_test_receipt_table(&receipts, table, 2);
        for value in 0..=N_KEYS + 5 {
            install_test_row_terms(&receipts, &[Value::new(value)]);
        }
        db.set_causal_wave(CausalWave::new(1));

        // The total exceeds `parallelize_table_op`'s real threshold. Two
        // proposals for key zero merge before either has a committed FactId;
        // every other key has exactly one effective proposal.
        let key_zero =
            receipts.register_rule_matches(10, CausalWave::new(1), 0, &[], &[], &[], &[0])[0].1;
        let ordinary_lanes = (0..(N_KEYS as usize - 1)).collect::<Vec<_>>();
        let ordinary = receipts
            .register_rule_matches(1, CausalWave::new(1), 0, &[], &[], &[], &ordinary_lanes)
            .into_iter()
            .map(|(_, cause)| cause)
            .collect::<Vec<_>>();
        let replacement =
            receipts.register_rule_matches(11, CausalWave::new(1), 0, &[], &[], &[], &[0])[0].1;
        let mut first = db.new_buffer(table);
        first.stage_insert_with_cause(&[Value::new(0), Value::new(0)], key_zero);
        for (key, cause) in (1..N_KEYS).zip(ordinary) {
            first.stage_insert_with_cause(&[Value::new(key), Value::new(key)], cause);
        }
        first.stage_insert_with_cause(&[Value::new(0), Value::new(N_KEYS + 1)], replacement);
        drop(first);
        assert!(db.merge_all());
        db.finalize_causal_wave();

        let first_snapshot = receipts.snapshot();
        assert_eq!(first_snapshot.facts.len(), N_KEYS as usize);
        let same_wave_fact = first_snapshot
            .facts
            .iter()
            .find(|fact| {
                let crate::FactCause::Merge { cause } = &fact.cause else {
                    return false;
                };
                test_cause_dependencies(&first_snapshot, *cause).rules.len() == 2
            })
            .expect("same-wave proposal fold must retain both matches");
        let crate::FactCause::Merge { cause } = &same_wave_fact.cause else {
            panic!("same-wave fold must be represented as a merge")
        };
        let same_wave_dependencies = test_cause_dependencies(&first_snapshot, *cause);
        let same_wave_rules = same_wave_dependencies
            .rules
            .iter()
            .map(|id| {
                first_snapshot
                    .matches
                    .iter()
                    .find(|record| record.id == *id)
                    .unwrap()
                    .rule
            })
            .collect::<Vec<_>>();
        assert_eq!(same_wave_rules, [10, 11]);
        assert!(same_wave_dependencies.facts.is_empty());
        let same_wave_fact_id = same_wave_fact.id;

        // Force the parallel path again. All but key zero are no-ops; key zero
        // becomes one new immutable version that cites its prior FactId.
        db.set_causal_wave(CausalWave::new(2));
        let noop_lanes = (0..(N_KEYS as usize - 1)).collect::<Vec<_>>();
        let noops = receipts
            .register_rule_matches(20, CausalWave::new(2), 0, &[], &[], &[], &noop_lanes)
            .into_iter()
            .map(|(_, cause)| cause)
            .collect::<Vec<_>>();
        let update =
            receipts.register_rule_matches(21, CausalWave::new(2), 0, &[], &[], &[], &[0])[0].1;
        let duplicate_noop =
            receipts.register_rule_matches(22, CausalWave::new(2), 0, &[], &[], &[], &[0])[0].1;
        let mut second = db.new_buffer(table);
        for (key, cause) in (1..N_KEYS).zip(noops) {
            second.stage_insert_with_cause(&[Value::new(key), Value::new(key)], cause);
        }
        second.stage_insert_with_cause(&[Value::new(0), Value::new(N_KEYS + 4)], update);
        // Keep the count above the strict `> 20_000` threshold.
        second.stage_insert_with_cause(&[Value::new(1), Value::new(1)], duplicate_noop);
        drop(second);
        assert!(db.merge_all());
        db.finalize_causal_wave();

        let final_snapshot = receipts.snapshot();
        assert_eq!(final_snapshot.facts.len(), N_KEYS as usize + 1);
        let latest = final_snapshot.facts.last().unwrap();
        let crate::FactCause::Merge { cause } = &latest.cause else {
            panic!("committed update must retain its merge dependencies")
        };
        let dependencies = test_cause_dependencies(&final_snapshot, *cause);
        assert_eq!(dependencies.rules.len(), 1);
        assert_eq!(dependencies.facts.as_slice(), &[same_wave_fact_id]);
        assert!(dependencies.rebuilds.is_empty());
        let committed = db
            .get_table(table)
            .get_row(&[Value::new(0)])
            .expect("updated key zero must be committed");
        assert_eq!(
            committed.vals.as_slice(),
            &[Value::new(0), Value::new(N_KEYS + 4)],
            "record the row the native parallel table actually publishes, not merge scratch"
        );
        assert_eq!(
            latest.terms.as_ref(),
            &[
                receipts
                    .lookup_term(TEST_REPLAY_SORT, Value::new(0))
                    .unwrap(),
                receipts
                    .lookup_term(TEST_REPLAY_SORT, Value::new(N_KEYS + 4))
                    .unwrap(),
            ],
            "parallel FactId terms must align with the physical committed row"
        );
        let update_match = final_snapshot
            .matches
            .iter()
            .find(|record| record.id == dependencies.rules[0])
            .unwrap();
        assert_eq!(update_match.rule, 21);
        assert_eq!(update_match.wave, CausalWave::new(2));
        assert_eq!(
            final_snapshot
                .matches
                .iter()
                .filter(|record| record.wave == CausalWave::new(2))
                .count(),
            1,
            "wave-2 no-op match drafts must be reclaimed, not promoted"
        );
        assert_eq!(final_snapshot.counters.provisional_matches, 0);
        assert_eq!(final_snapshot.counters.live_provisional_bytes, 0);
        assert_eq!(final_snapshot.counters.unattributed_commits, 0);
    });
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
        .register_rule_matches(30, CausalWave::new(1), 0, &[], &[], &[], &lanes)
        .into_iter()
        .map(|(_, cause)| cause)
        .collect::<Vec<_>>();
    let mut updates = db.new_buffer(table);
    for (index, cause) in causes.into_iter().enumerate() {
        let key = 1 + index / 4;
        let value = 1 + index % 4;
        updates.stage_insert_with_cause(&[Value::from_usize(key), Value::from_usize(value)], cause);
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
        receipts.fact_record(historical).unwrap().id,
        historical,
        "a compacted-away historical row must remain addressable in the receipt arena"
    );
}

#[test]
fn parallel_compaction_preserves_live_and_historical_fact_ids() {
    const INITIAL_ROWS: usize = 20_001;
    const UPDATED_KEYS: usize = 10_001;
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(4)
        .build()
        .unwrap();
    pool.install(|| {
        let mut db = Database::default();
        let table = db.add_table_named(
            SortedWritesTable::new(
                1,
                3,
                Some(ColumnId::new(2)),
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
            "ParallelCompaction".into(),
            iter::empty(),
            iter::empty(),
        );
        let receipts = db.enable_causal_receipts();
        register_test_receipt_table(&receipts, table, 3);
        for value in 0..INITIAL_ROWS {
            install_test_row_terms(&receipts, &[Value::from_usize(value)]);
        }
        db.set_causal_wave(CausalWave::new(1));
        let initial_lanes = (0..INITIAL_ROWS).collect::<Vec<_>>();
        let initial_causes = receipts
            .register_rule_matches(40, CausalWave::new(1), 0, &[], &[], &[], &initial_lanes)
            .into_iter()
            .map(|(_, cause)| cause)
            .collect::<Vec<_>>();
        let mut initial = db.new_buffer(table);
        for (key, cause) in initial_causes.into_iter().enumerate() {
            initial.stage_insert_with_cause(
                &[Value::from_usize(key), Value::new(0), Value::new(0)],
                cause,
            );
        }
        drop(initial);
        assert!(db.merge_all());
        db.finalize_causal_wave();

        let survivor = Value::from_usize(INITIAL_ROWS - 1);
        let target_before = committed_fact_id(&db, table, survivor);
        let target_row_before = committed_row_id(&db, table, survivor);
        let historical = committed_fact_id(&db, table, Value::new(1));
        let version_before = db.get_table(table).version();
        db.set_causal_wave(CausalWave::new(2));
        let update_count = UPDATED_KEYS * 2;
        let update_lanes = (0..update_count).collect::<Vec<_>>();
        let update_causes = receipts
            .register_rule_matches(41, CausalWave::new(2), 0, &[], &[], &[], &update_lanes)
            .into_iter()
            .map(|(_, cause)| cause)
            .collect::<Vec<_>>();
        let mut updates = db.new_buffer(table);
        for (index, cause) in update_causes.into_iter().enumerate() {
            let key = 1 + index / 2;
            let value = 1 + index % 2;
            updates.stage_insert_with_cause(
                &[
                    Value::from_usize(key),
                    Value::from_usize(value),
                    Value::new(1),
                ],
                cause,
            );
        }
        drop(updates);
        assert!(db.merge_all());
        db.finalize_causal_wave();

        let version_after = db.get_table(table).version();
        assert_ne!(
            version_before.major, version_after.major,
            "the canary must cross the parallel physical rekey path"
        );
        assert_eq!(committed_fact_id(&db, table, survivor), target_before);
        assert_ne!(
            committed_row_id(&db, table, survivor),
            target_row_before,
            "the untouched canary row must physically move during parallel compaction"
        );
        assert_ne!(committed_fact_id(&db, table, Value::new(1)), historical);
        assert_eq!(receipts.fact_record(historical).unwrap().id, historical);
    });
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

    let snapshot = receipts.snapshot();
    let derived_fact = snapshot
        .facts
        .iter()
        .find(|fact| fact.table == derived)
        .expect("rectangle result must be committed");
    let match_id = derived_fact
        .cause
        .rule_match()
        .expect("rectangle result must cite its native match");
    let matched = snapshot
        .matches
        .iter()
        .find(|record| record.id == match_id)
        .expect("rectangle match receipt must be durable");
    assert_eq!(
        matched.premises.as_ref(),
        &[r_first, s_fact, t_fact, u_fact],
        "receipt premise order must follow the source rule"
    );
    assert!(!matched.premises.contains(&r_decoy));
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
    assert!(db.run_rule_set(&rule_set, ReportLevel::TimeOnly).changed);
    db.finalize_causal_wave();
    let snapshot = receipts.snapshot();
    let matches = snapshot
        .matches
        .iter()
        .filter(|record| record.rule == 51)
        .collect::<Vec<_>>();
    if retain_existential {
        assert_eq!(matches.len(), 2);
        let derived_facts = snapshot
            .facts
            .iter()
            .filter(|fact| fact.table == derived)
            .collect::<Vec<_>>();
        assert_eq!(derived_facts.len(), 2);
        for fact in derived_facts {
            let expected = if fact.terms[4] == existential_100_term {
                [r_first, s_first, t_fact, u_fact]
            } else {
                assert_eq!(fact.terms[4], existential_101_term);
                [r_second, s_second, t_fact, u_fact]
            };
            let matched = matches
                .iter()
                .find(|record| Some(record.id) == fact.cause.rule_match())
                .expect("each derived row must cite its own exact native match");
            assert_eq!(matched.premises.as_ref(), expected);
        }
    } else {
        assert_eq!(matches.len(), 1);
        assert_eq!(
            matches[0].premises.as_ref(),
            &[r_first, s_first, t_fact, u_fact]
        );
        assert!(!matches[0].premises.contains(&r_second));
        assert!(!matches[0].premises.contains(&s_second));
    }
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
fn guarded_rule_checks_before_heads_and_replays_captured_bindings() {
    run_serial_and_parallel(|| {
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
            // This deliberately crosses the database-level parallelism
            // threshold, so run_serial_and_parallel exercises both executors.
            for value in 0..10_001 {
                input_buffer.stage_insert(&[Value::new(value)]);
            }
        }
        db.merge_all();

        let head_calls = Arc::new(AtomicUsize::new(0));
        let calls = head_calls.clone();
        let observe_head =
            db.add_external_function(Box::new(make_external_func(move |_exec_state, args| {
                assert!(args.is_empty());
                calls.fetch_add(1, Ordering::Relaxed);
                Some(Value::new(7))
            })));

        let mut rules = RuleSetBuilder::new(&mut db);
        let mut query = rules.new_rule();
        let value = query.new_var_named("value");
        query.add_atom(input, &[value.into()], &[]).unwrap();
        let mut action = query.build();
        // Deliberately leave the body variable unused by the head. Replay must
        // still preserve the raw query multiplicity rather than collapsing
        // this to one head execution per batch.
        let observed = action.call_external(observe_head, &[]).unwrap();
        action.insert(output, &[observed.into()]).unwrap();
        action.build_with_description("guarded-copy");
        let rule_set = rules.build();

        let mismatch = db
            .run_rule_set_guarded(&rule_set, Some(10_000), ReportLevel::TimeOnly)
            .unwrap();
        assert!(matches!(
            mismatch,
            GuardedRuleSetRunOutcome::MatchCountMismatch {
                expected_matches: 10_000,
                observed_matches: 10_001,
            }
        ));
        assert_eq!(head_calls.load(Ordering::Relaxed), 0);
        assert_eq!(db.get_table(output).len(), 0);

        let applied = db
            .run_rule_set_guarded(&rule_set, Some(10_001), ReportLevel::TimeOnly)
            .unwrap();
        let GuardedRuleSetRunOutcome::Applied {
            observed_matches,
            report,
        } = applied
        else {
            panic!("exact guard should apply")
        };
        assert_eq!(observed_matches, 10_001);
        assert_eq!(report.num_matches("guarded-copy"), 10_001);
        assert_eq!(head_calls.load(Ordering::Relaxed), 10_001);
        assert_eq!(db.get_table(output).len(), 1);
    });
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
fn replay_fallback_promotes_only_primary_successes() {
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

    for output in [102, 104] {
        let term = receipts
            .lookup_term(TEST_REPLAY_SORT, Value::new(output))
            .expect("a primary result is promoted");
        assert!(matches!(
            receipts.replay_term(term),
            Some(ReplayTerm::Call { op, .. }) if op == ReplayOpId::new(700)
        ));
    }
    for output in [201, 203] {
        assert_eq!(
            receipts.lookup_term(TEST_REPLAY_SORT, Value::new(output)),
            None,
            "a fallback result must not be mislabeled as the primary call"
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
