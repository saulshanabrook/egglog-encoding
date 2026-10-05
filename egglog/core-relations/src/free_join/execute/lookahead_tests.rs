//! Direct tests of conservative lookahead probes. Include as a child module of
//! `execute/lookahead.rs` so incorrect estimates cannot hide behind the exact executor.
use super::*;
use crate::{
    free_join::{ProcessedConstraints, get_column_index_from_tableinfo},
    query::VarColumnMap,
    table::SortedWritesTable,
    table_shortcuts::v,
};

fn fixture() -> (Database, TableId, Atom) {
    let mut db = Database::new();
    let table = db.add_table(
        SortedWritesTable::new(
            2,
            2,
            None,
            vec![],
            Box::new(|_, old, new, _| {
                assert_eq!(old, new);
                false
            }),
        ),
        std::iter::empty(),
        std::iter::empty(),
    );
    {
        let mut buffer = db.new_buffer(table);
        for key in 0..32 {
            buffer.stage_insert(&[v(key), v(key)]);
        }
    }
    db.merge_all();
    let atom = Atom {
        table,
        var_columns: VarColumnMap::default(),
        constraints: ProcessedConstraints {
            subset: db.get_table(table).all(),
            fast: with_pool_set(|ps| ps.get()),
            slow: with_pool_set(|ps| ps.get()),
        },
        occurrence: None,
    };
    (db, table, atom)
}

#[test]
fn reset_catalog_is_unknown_until_refreshed_and_lookahead_never_builds_it() {
    let (mut db, table, atom) = fixture();
    let column = ColumnId::new(0);
    drop(get_column_index_from_tableinfo(
        db.get_table_info(table),
        column,
    ));
    {
        let mut buffer = db.new_buffer(table);
        buffer.stage_insert(&[v(1000), v(1000)]);
    }
    db.merge_all();

    let info = db.get_table_info(table);
    let pending = info.column_indexes.get_if_present(&column).unwrap();
    assert!(pending.get().is_none(), "insertion must reset the catalog");
    let before = info.column_indexes.get_or_insert_calls();
    let arena = SharedArena::new();
    let execution = ExecutionState::new(db.read_only_view(), Default::default());
    let join = JoinState::new(&db, execution.seed(), None, &arena);
    let source = AtomRows::Root(Arc::new(TrieRoot::new(db.get_table(table).all())));
    assert!(
        source.size() > row_limit(),
        "force the existing-catalog path"
    );

    // The old catalog did not contain 1000. Its reset state must be unknown,
    // preserving both keys instead of incorrectly rejecting the new witness.
    let mut keys = Keys(smallvec::smallvec![v(1000), v(2000)]);
    let mut budget = 256;
    join.probe_scan(&atom, &source, column, &[], &mut keys, &mut budget);
    assert_eq!(keys.0.as_slice(), &[v(1000), v(2000)]);
    assert_eq!(budget, 256);
    assert!(
        pending.get().is_none(),
        "lookahead must not refresh an index"
    );
    assert_eq!(info.column_indexes.get_or_insert_calls(), before);

    // Nor may a miss in the catalog create a new column index.
    let missing_column = ColumnId::new(1);
    assert!(
        info.column_indexes
            .get_if_present(&missing_column)
            .is_none()
    );
    join.probe_scan(&atom, &source, missing_column, &[], &mut keys, &mut budget);
    assert_eq!(keys.0.as_slice(), &[v(1000), v(2000)]);
    assert!(
        info.column_indexes
            .get_if_present(&missing_column)
            .is_none()
    );
    assert_eq!(info.column_indexes.get_or_insert_calls(), before);

    // Once normal execution refreshes the catalog, probing recognizes the
    // inserted witness and can reject a genuinely absent key.
    let refreshed = get_column_index_from_tableinfo(info, column);
    assert!(refreshed.get().unwrap().get_subset(&v(1000)).is_some());
    join.probe_scan(&atom, &source, column, &[], &mut keys, &mut budget);
    assert_eq!(keys.0.as_slice(), &[v(1000)]);
    assert!(budget < 256);
    assert_eq!(info.column_indexes.get_or_insert_calls(), before + 1);
}

#[test]
fn cached_projection_is_scoped_to_root_column_and_constraints() {
    let (db, table, atom) = fixture();
    let column = ColumnId::new(0);
    let lower = [
        Constraint::GtConst {
            col: ColumnId::new(1),
            val: v(0),
        },
        Constraint::LtConst {
            col: ColumnId::new(1),
            val: v(16),
        },
    ];
    let upper = [
        Constraint::GtConst {
            col: ColumnId::new(1),
            val: v(15),
        },
        Constraint::LtConst {
            col: ColumnId::new(1),
            val: v(32),
        },
    ];
    let unpublished = [Constraint::GtConst {
        col: ColumnId::new(1),
        val: v(31),
    }];
    let arena = SharedArena::new();
    let execution = ExecutionState::new(db.read_only_view(), Default::default());
    let join = JoinState::new(&db, execution.seed(), None, &arena);
    let root = Arc::new(TrieRoot::new_shared(db.get_table(table).all()));
    let source = AtomRows::Root(root.clone());
    assert!(
        source.size() > row_limit(),
        "small-key access must use the cache"
    );
    let lower_slot = root.projection_slot(column, &lower).unwrap();
    let upper_slot = root.projection_slot(column, &upper).unwrap();
    let unpublished_slot = root.projection_slot(column, &unpublished).unwrap();
    let projection = |range: std::ops::Range<usize>| {
        super::super::super::packed_cache::RootProjection::from_sorted_pairs(
            range.map(|n| (v(n), RowId::from_usize(n))).collect(),
        )
    };
    assert!(lower_slot.set(projection(1..16)).is_ok());
    assert!(upper_slot.set(projection(16..32)).is_ok());

    let reversed = [lower[1].clone(), lower[0].clone()];
    assert!(Arc::ptr_eq(
        &join.cached_projection(&source, column, &reversed).unwrap(),
        &lower_slot,
    ));
    assert!(Arc::ptr_eq(
        &join.cached_projection(&source, column, &upper).unwrap(),
        &upper_slot,
    ));
    let mut budget = 256;
    assert_eq!(
        join.small_keys(&atom, &source, column, &reversed, &mut budget)
            .unwrap()
            .0
            .as_slice(),
        &(1..16).map(v).collect::<Vec<_>>(),
    );
    assert_eq!(
        join.small_keys(&atom, &source, column, &upper, &mut budget)
            .unwrap()
            .0
            .as_slice(),
        &(16..32).map(v).collect::<Vec<_>>(),
    );

    assert!(
        join.cached_projection(&source, column, &unpublished)
            .is_none()
    );
    assert!(unpublished_slot.get().is_none());
    assert!(
        join.cached_projection(&source, ColumnId::new(1), &lower)
            .is_none()
    );
    let other_root = AtomRows::Root(Arc::new(TrieRoot::new_shared(db.get_table(table).all())));
    assert!(
        join.cached_projection(&other_root, column, &lower)
            .is_none()
    );
    let residual = AtomRows::Root(Arc::new(TrieRoot::new(db.get_table(table).all())));
    assert!(join.cached_projection(&residual, column, &lower).is_none());
}
#[test]
fn promoted_intersection_preserves_every_factorized_payload_row() {
    use crate::{PlanStrategy, free_join::join_tail::recompute_leaf_scans};

    let (mut db, facts, _) = fixture();
    let [gate, output] = [1, 2].map(|arity| {
        db.add_table(
            SortedWritesTable::new(
                arity,
                arity,
                None,
                vec![],
                Box::new(|_, old, new, _| {
                    assert_eq!(old, new);
                    false
                }),
            ),
            std::iter::empty(),
            std::iter::empty(),
        )
    });
    {
        let mut facts_buf = db.new_buffer(facts);
        let mut gate_buf = db.new_buffer(gate);
        for x in 0..32 {
            for payload in 100..108 {
                facts_buf.stage_insert(&[v(x), v(payload)]);
            }
        }
        // One genuinely rejected key ensures the lookahead sees selectivity,
        // not merely a cheap seed with no information from other relations.
        for key in [1, 2, 1000] {
            gate_buf.stage_insert(&[v(key)]);
        }
    }
    db.merge_all();
    drop(get_column_index_from_tableinfo(
        db.get_table_info(facts),
        ColumnId::new(0),
    ));
    let mut builder = db.new_rule_set();
    let mut query = builder.new_rule();
    query.set_plan_strategy(PlanStrategy::Gj);
    query.set_no_decomp(true);
    let x = query.new_var();
    let payload = query.new_var();
    let facts_atom = query
        .add_atom(facts, &[x.into(), payload.into()], &[])
        .unwrap();
    query.add_atom(gate, &[x.into()], &[]).unwrap();
    let mut action = query.build();
    action.insert(output, &[x.into(), payload.into()]).unwrap();
    action.build_with_description("lookahead-factorized-payloads");
    let rules = builder.build();

    let matches = {
        let (plan, _, _) = rules.plans.values().next().unwrap();
        let Plan::SinglePlan(plan) = plan else {
            panic!("expected a single plan");
        };
        assert_eq!(plan.stages.instrs.len(), 2);
        let payload_stage = plan
            .stages
            .instrs
            .iter()
            .position(|stage| {
                matches!(stage, JoinStage::FusedIntersect { cover, to_intersect, .. }
                if cover.to_index.atom == facts_atom && to_intersect.is_empty())
            })
            .unwrap();
        let intersection_stage = 1 - payload_stage;
        assert!(matches!(
            plan.stages.instrs[intersection_stage],
            JoinStage::Intersect { .. }
        ));
        let mut order = InstrOrder::from_iter([payload_stage, intersection_stage].into_iter());
        let arena = SharedArena::new();
        let execution = ExecutionState::new(db.read_only_view(), Default::default());
        let join = JoinState::new(&db, execution.seed(), None, &arena);
        let mut bindings = BindingInfo::default();
        for (id, atom) in plan.atoms.iter() {
            let headers: SmallVec<[&JoinHeader; 2]> =
                plan.header.iter().filter(|h| h.atom == id).collect();
            bindings.insert_node(id, join.root_node(atom.table, &headers).unwrap());
        }
        assert!(join.mixed_probe_order(&plan.stages, &plan.atoms, &mut order, 0, &bindings));
        assert_eq!(order.get(0), intersection_stage);
        let prepared = PreparedJoinIndexes::new(&db, &plan.atoms, &plan.stages);
        let mut leaves: LeafScans = std::iter::repeat_n(false, order.len()).collect();
        recompute_leaf_scans(&order, &mut leaves, &plan.stages.instrs, 0);
        assert!(
            leaves[1],
            "the promoted join must leave a factorized payload scan"
        );
        let counter = MatchCounter::new(rules.actions.n_ids());
        let mut buffer = InPlaceActionBuffer {
            rule_set: &rules,
            match_counter: &counter,
            batches: Default::default(),
            apply_time: Duration::ZERO,
        };
        join.run_plan(
            &plan.stages,
            &prepared,
            &plan.atoms,
            plan.actions,
            &mut order,
            &mut leaves,
            0,
            None,
            None::<u64>,
            &mut bindings,
            &mut buffer,
        );
        buffer.flush(&mut execution.clone());
        counter.read_matches(plan.actions)
    };
    db.merge_all();
    let table = db.get_table(output);
    let mut actual = table
        .scan(table.all().as_ref())
        .iter()
        .map(|(_, row)| row.to_vec())
        .collect::<Vec<_>>();
    let mut expected = [1, 2]
        .into_iter()
        .flat_map(|x| {
            std::iter::once(vec![v(x), v(x)])
                .chain((100..108).map(move |payload| vec![v(x), v(payload)]))
        })
        .collect::<Vec<_>>();
    actual.sort();
    expected.sort();
    assert_eq!(matches, expected.len());
    assert_eq!(actual, expected);
}

#[test]
fn independent_leaf_swap_must_cross_the_incumbents_last_atom_use() {
    use crate::free_join::{
        SubAtom,
        plan::{ScanSpec, SingleScanSpec},
    };

    let payload = |atom: usize| JoinStage::FusedIntersect {
        cover: ScanSpec {
            to_index: SubAtom {
                atom: AtomId::from_usize(atom),
                vars: smallvec::smallvec![ColumnId::new(1)],
            },
            constraints: Vec::new(),
            occurrence_cols: None,
        },
        bind: smallvec::smallvec![(ColumnId::new(1), Variable::from_usize(2 + atom))],
        to_intersect: Vec::new(),
    };
    let scan = |atom: usize| SingleScanSpec {
        atom: AtomId::from_usize(atom),
        column: ColumnId::new(0),
        occurrence_cols: None,
        cs: Vec::new(),
    };
    let join = |left, right| JoinStage::Intersect {
        var: Variable::new(0),
        scans: smallvec::smallvec![scan(left), scan(right)],
    };
    let permits = |stages: &[JoinStage], order: &[usize], cur, position| {
        JoinState::swap_factorizes_incumbent(
            stages,
            &InstrOrder::from_iter(order.iter().copied()),
            cur,
            position,
        )
    };
    // A=0, B=1, C=2, alias(A)=3, D=4. The gate depends on
    // relation occurrence identity, even when occurrences share a table.
    let (_db, _, atom) = fixture();
    let mut atoms = DenseIdMap::new();
    atoms.insert(AtomId::new(0), atom.clone());
    atoms.insert(AtomId::new(3), atom);
    assert_eq!(atoms[AtomId::new(0)].table, atoms[AtomId::new(3)].table);

    let base = [payload(0), join(0, 1), payload(2)];
    assert!(permits(&base, &[0, 1, 2], 0, 2));
    let blocked = [payload(0), join(0, 1), payload(2), join(0, 4)];
    assert!(!permits(&blocked, &[0, 1, 2, 3], 0, 2));
    // No dependency crossed: moving an independent leaf is pointless here.
    assert!(!permits(
        &[payload(0), join(3, 1), payload(2)],
        &[0, 1, 2],
        0,
        2
    ));
    // A later access to another alias does not keep A's payload non-leaf.
    assert!(permits(
        &[payload(0), join(0, 1), payload(2), join(3, 4)],
        &[0, 1, 2, 3],
        0,
        2,
    ));

    let mut duplicate_use = join(0, 1);
    let JoinStage::Intersect { scans, .. } = &mut duplicate_use else {
        unreachable!()
    };
    scans.push(scan(0));
    assert!(permits(
        &[payload(0), duplicate_use.clone(), payload(2)],
        &[0, 1, 2],
        0,
        2
    ));
    assert!(!permits(
        &[payload(0), join(0, 1), payload(2), duplicate_use],
        &[0, 1, 2, 3],
        0,
        2,
    ));
    // Read physical order and cur, not the logical stage positions.
    assert!(permits(
        &[payload(0), join(0, 1), payload(2), payload(4)],
        &[2, 0, 1, 3],
        1,
        3
    ));
    assert!(!permits(
        &[join(0, 1), payload(0), payload(2)],
        &[0, 1, 2],
        1,
        2
    ));
    assert!(permits(
        &[join(0, 1), payload(2), payload(0)],
        &[2, 0, 1],
        0,
        2
    ));
}

#[test]
fn incumbent_catalog_bound_counts_keys_and_ignores_missing_reset_and_occurrence_indexes() {
    use crate::free_join::{
        SubAtom,
        plan::{ScanSpec, SingleScanSpec},
    };

    let (mut db, _, mut atom) = fixture();
    let table = db.add_table(
        SortedWritesTable::new(
            2,
            2,
            None,
            vec![],
            Box::new(|_, old, new, _| {
                assert_eq!(old, new);
                false
            }),
        ),
        std::iter::empty(),
        std::iter::empty(),
    );
    {
        let mut buffer = db.new_buffer(table);
        for payload in 0..128 {
            buffer.stage_insert(&[v(payload % 2), v(payload)]);
        }
    }
    db.merge_all();
    atom.table = table;
    atom.constraints.subset = db.get_table(table).all();

    let id = AtomId::from_usize(0);
    let col = ColumnId::from_usize(0);
    let var = Variable::from_usize(0);
    let ordinary = JoinStage::Intersect {
        var,
        scans: smallvec::smallvec![SingleScanSpec {
            atom: id,
            column: col,
            occurrence_cols: None,
            cs: Vec::new(),
        }],
    };
    let mut occurrence = ordinary.clone();
    let JoinStage::Intersect { scans, .. } = &mut occurrence else {
        unreachable!()
    };
    scans[0].occurrence_cols = Some(smallvec::smallvec![col, ColumnId::from_usize(1)]);
    let fused = JoinStage::FusedIntersect {
        cover: ScanSpec {
            to_index: SubAtom {
                atom: id,
                vars: smallvec::smallvec![col],
            },
            constraints: Vec::new(),
            occurrence_cols: None,
        },
        bind: smallvec::smallvec![(col, var)],
        to_intersect: Vec::new(),
    };

    // Construct each execution anew so no root projection cache can supply
    // the key bound or survive a table merge. The only available metadata
    // source after refresh is the persistent column catalog.
    let bound = |db: &Database, stage: &JoinStage| {
        let mut atoms = DenseIdMap::new();
        atoms.insert(id, atom.clone());
        let arena = SharedArena::new();
        let execution = ExecutionState::new(db.read_only_view(), Default::default());
        let join = JoinState::new(db, execution.seed(), None, &arena);
        let mut bindings = BindingInfo::default();
        bindings.insert_node(id, Arc::new(TrieRoot::new(db.get_table(table).all())));
        join.incumbent_bound(stage, &atoms, &bindings)
    };

    let before = db
        .get_table_info(table)
        .column_indexes
        .get_or_insert_calls();
    assert_eq!(bound(&db, &ordinary), 128);
    assert!(
        db.get_table_info(table)
            .column_indexes
            .get_if_present(&col)
            .is_none()
    );
    assert_eq!(
        db.get_table_info(table)
            .column_indexes
            .get_or_insert_calls(),
        before
    );

    let handle = get_column_index_from_tableinfo(db.get_table_info(table), col);
    assert_eq!(handle.get().unwrap().len(), 2);
    assert_eq!(bound(&db, &ordinary), 2);
    assert_eq!(
        bound(&db, &fused),
        128,
        "fused physical-row multiplicity is unchanged"
    );
    assert_eq!(
        bound(&db, &occurrence),
        128,
        "one column cannot bound a union of occurrence columns"
    );
    assert_eq!(
        db.get_table_info(table)
            .column_indexes
            .get_or_insert_calls(),
        before + 1
    );
    // Merging resets the catalog through its uniquely owned Arc.
    drop(handle);

    {
        let mut buffer = db.new_buffer(table);
        buffer.stage_insert(&[v(2), v(1000)]);
    }
    db.merge_all();
    let pending = db
        .get_table_info(table)
        .column_indexes
        .get_if_present(&col)
        .unwrap();
    assert!(
        pending.get().is_none(),
        "merge invalidates the old two-key catalog"
    );
    assert_eq!(
        bound(&db, &ordinary),
        129,
        "a reset catalog is unknown, not a stale two-key bound"
    );
    assert!(
        pending.get().is_none(),
        "lookahead must not refresh the catalog"
    );
    assert_eq!(
        db.get_table_info(table)
            .column_indexes
            .get_or_insert_calls(),
        before + 1
    );
    drop(pending);

    let refreshed = get_column_index_from_tableinfo(db.get_table_info(table), col);
    assert_eq!(refreshed.get().unwrap().len(), 3);
    assert_eq!(bound(&db, &ordinary), 3);
    assert_eq!(
        db.get_table_info(table)
            .column_indexes
            .get_or_insert_calls(),
        before + 2
    );
}
