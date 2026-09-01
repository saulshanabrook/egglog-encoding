use std::panic::{AssertUnwindSafe, catch_unwind};

use crate::{
    Database, ExternalFunctionId, FlatTable, QueryError, Table, TableSchema, Value,
    action::WriteVal,
    numeric_id::NumericId,
    offsets::{OffsetRange, RowId, SubsetRef},
    table_shortcuts::v,
    table_spec::{ColumnId, Constraint, Offset, WrappedTable},
};

fn stage<const N: usize>(table: &WrappedTable, rows: &[[Value; N]]) {
    let mut buffer = table.new_buffer();
    for row in rows {
        buffer.stage_insert(row);
    }
}

fn scan(table: &WrappedTable, subset: SubsetRef<'_>) -> Vec<Vec<Value>> {
    table
        .scan(subset)
        .iter()
        .map(|(_, row)| row.to_vec())
        .collect()
}

fn sorted_rows(table: &WrappedTable) -> Vec<Vec<Value>> {
    let mut rows = scan(table, table.all().as_ref());
    rows.sort_unstable();
    rows
}

#[test]
fn appends_preserve_rows_duplicates_and_deltas() {
    empty_execution_state!(exec_state);
    let mut table = WrappedTable::new(FlatTable::new(3));

    let spec = table.spec();
    assert_eq!(spec.schema, TableSchema::Flat { n_cols: 3 });
    assert!(!spec.allows_delete);
    assert!(!table.has_stale_rows());

    stage(&table, &[[v(1), v(2), v(3)], [v(1), v(2), v(3)]]);
    assert!(table.is_empty(), "staged rows stay hidden until merge");
    assert!(table.merge(&mut exec_state).added);
    assert_eq!(
        scan(&table, table.all().as_ref()),
        vec![vec![v(1), v(2), v(3)], vec![v(1), v(2), v(3)],]
    );

    let before = table.version();
    stage(&table, &[[v(4), v(5), v(6)]]);
    assert!(table.merge(&mut exec_state).added);
    assert_eq!(
        scan(&table, table.updates_since(before.minor).as_ref()),
        vec![vec![v(4), v(5), v(6)]]
    );
    assert!(!table.merge(&mut exec_state).added);
}

#[test]
fn scans_apply_constraints_without_keyed_lookup() {
    empty_execution_state!(exec_state);
    let mut table = WrappedTable::new(FlatTable::new(3));
    stage(
        &table,
        &[
            [v(1), v(1), v(10)],
            [v(1), v(2), v(20)],
            [v(2), v(3), v(30)],
        ],
    );
    table.merge(&mut exec_state);

    let cases = [
        (
            Constraint::Eq {
                l_col: ColumnId::new(0),
                r_col: ColumnId::new(1),
            },
            vec![vec![v(1), v(1), v(10)]],
        ),
        (
            Constraint::EqConst {
                col: ColumnId::new(0),
                val: v(2),
            },
            vec![vec![v(2), v(3), v(30)]],
        ),
        (
            Constraint::LtConst {
                col: ColumnId::new(2),
                val: v(30),
            },
            vec![vec![v(1), v(1), v(10)], vec![v(1), v(2), v(20)]],
        ),
        (
            Constraint::GtConst {
                col: ColumnId::new(2),
                val: v(10),
            },
            vec![vec![v(1), v(2), v(20)], vec![v(2), v(3), v(30)]],
        ),
        (
            Constraint::LeConst {
                col: ColumnId::new(1),
                val: v(2),
            },
            vec![vec![v(1), v(1), v(10)], vec![v(1), v(2), v(20)]],
        ),
        (
            Constraint::GeConst {
                col: ColumnId::new(1),
                val: v(2),
            },
            vec![vec![v(1), v(2), v(20)], vec![v(2), v(3), v(30)]],
        ),
    ];
    for (constraint, expected) in cases {
        let matching = table.refine(table.all(), &[constraint]);
        assert_eq!(scan(&table, matching.as_ref()), expected);
    }

    let lookup = catch_unwind(AssertUnwindSafe(|| table.get_row(&[v(1), v(2)])));
    assert!(
        lookup.is_err(),
        "flat tables must not grow a lookup contract"
    );
}

#[test]
fn fresh_handles_submit_to_the_same_table() {
    empty_execution_state!(exec_state);
    let mut table = WrappedTable::new(FlatTable::new(2));
    let mut first = table.new_buffer();
    first.stage_insert(&[v(1), v(10)]);
    let mut second = first.fresh_handle();
    second.stage_insert(&[v(2), v(20)]);
    drop(first);
    drop(second);

    assert!(table.merge(&mut exec_state).added);
    assert_eq!(
        sorted_rows(&table),
        vec![vec![v(1), v(10)], vec![v(2), v(20)]]
    );
}

#[test]
fn bounded_scans_validate_offsets_and_handle_empty_sparse_subsets() {
    empty_execution_state!(exec_state);
    let mut table = FlatTable::new(2);
    let mut buffer = table.new_buffer();
    for row in [[v(1), v(1)], [v(1), v(2)], [v(2), v(2)], [v(3), v(4)]] {
        buffer.stage_insert(&row);
    }
    drop(buffer);
    table.merge(&mut exec_state);

    let equality = Constraint::Eq {
        l_col: ColumnId::new(0),
        r_col: ColumnId::new(1),
    };
    let all = table.all();
    let mut found = Vec::new();
    let next = table.scan_generic_bounded(
        all.as_ref(),
        Offset::new(0),
        2,
        std::slice::from_ref(&equality),
        |row_id, row| found.push((row_id, row.to_vec())),
    );
    assert_eq!(next, Some(Offset::new(2)));
    assert_eq!(found, vec![(RowId::new(0), vec![v(1), v(1)])]);

    let next = table.scan_generic_bounded(
        all.as_ref(),
        next.unwrap(),
        2,
        std::slice::from_ref(&equality),
        |row_id, row| found.push((row_id, row.to_vec())),
    );
    assert_eq!(next, None);
    assert_eq!(
        found,
        vec![
            (RowId::new(0), vec![v(1), v(1)]),
            (RowId::new(2), vec![v(2), v(2)]),
        ]
    );

    let sparse = table.refine_one(all, &equality);
    let empty_sparse = table.refine_one(
        sparse,
        &Constraint::EqConst {
            col: ColumnId::new(0),
            val: v(99),
        },
    );
    assert!(
        table
            .scan_generic_bounded(
                empty_sparse.as_ref(),
                Offset::new(0),
                usize::MAX,
                &[],
                |_, _| panic!("empty subsets must not emit rows"),
            )
            .is_none()
    );

    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            table.updates_since(Offset::from_usize(table.len() + 1));
        }))
        .is_err()
    );
    let too_large = SubsetRef::Dense(OffsetRange::new(
        RowId::new(0),
        RowId::from_usize(table.len() + 1),
    ));
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            table.scan_generic_bounded(too_large, Offset::new(0), 1, &[], |_, _| {});
        }))
        .is_err()
    );

    let mut empty = FlatTable::new(2);
    let version = empty.version();
    empty.clear();
    assert_eq!(empty.version(), version);
}

#[test]
fn clear_discards_submitted_and_late_batches() {
    empty_execution_state!(exec_state);
    let mut table = WrappedTable::new(FlatTable::new(2));
    stage(&table, &[[v(0), v(0)]]);
    table.merge(&mut exec_state);

    stage(&table, &[[v(1), v(1)]]);
    let mut late = table.new_buffer();
    late.stage_insert(&[v(2), v(2)]);
    let version = table.version();
    table.clear();
    drop(late);

    assert!(table.is_empty());
    assert_eq!(table.version().major, version.major.inc());
    assert_eq!(table.version().minor, Offset::new(0));
    assert!(!table.merge(&mut exec_state).added);
}

#[test]
fn clone_copies_committed_rows_and_has_independent_pending_state() {
    empty_execution_state!(exec_state);
    let mut original = WrappedTable::new(FlatTable::new(2));
    stage(&original, &[[v(0), v(0)]]);
    original.merge(&mut exec_state);
    stage(&original, &[[v(1), v(1)]]);

    let mut cloned = original.dyn_clone();
    stage(&original, &[[v(2), v(2)]]);
    stage(&cloned, &[[v(3), v(3)]]);

    original.merge(&mut exec_state);
    cloned.merge(&mut exec_state);
    assert_eq!(
        sorted_rows(&original),
        vec![vec![v(0), v(0)], vec![v(1), v(1)], vec![v(2), v(2)]]
    );
    assert_eq!(
        sorted_rows(&cloned),
        vec![vec![v(0), v(0)], vec![v(3), v(3)]]
    );
}

#[test]
fn concurrent_clones_see_the_same_committed_snapshot() {
    empty_execution_state!(exec_state);
    let mut original = WrappedTable::new(FlatTable::new(2));
    stage(&original, &[[v(1), v(1)], [v(2), v(2)]]);
    original.merge(&mut exec_state);

    let (mut left, mut right) = std::thread::scope(|scope| {
        let left = scope.spawn(|| original.dyn_clone());
        let right = scope.spawn(|| original.dyn_clone());
        (left.join().unwrap(), right.join().unwrap())
    });
    left.merge(&mut exec_state);
    right.merge(&mut exec_state);

    assert_eq!(sorted_rows(&left), sorted_rows(&right));
    assert_eq!(left.len(), 2);
}

#[test]
fn rule_builder_allows_scans_but_rejects_keyed_operations() {
    let mut db = Database::default();
    let flat = db.add_table(FlatTable::new(2), [], []);
    let mut rules = db.new_rule_set();
    let mut query = rules.new_rule();
    let left = query.new_var_named("left");
    let right = query.new_var_named("right");
    query
        .add_atom(flat, &[left.into(), right.into()], &[])
        .unwrap();

    let mut action = query.build();
    assert!(matches!(
        action.lookup_or_insert(
            flat,
            &[left.into()],
            &[WriteVal::QueryEntry(right.into())],
            ColumnId::new(1),
        ),
        Err(QueryError::UnsupportedKeyedOperation { table }) if table == flat
    ));
    assert!(matches!(
        action.lookup_with_default(flat, &[left.into()], right.into(), ColumnId::new(1)),
        Err(QueryError::UnsupportedKeyedOperation { table }) if table == flat
    ));
    assert!(matches!(
        action.lookup(flat, &[left.into()], ColumnId::new(1)),
        Err(QueryError::UnsupportedKeyedOperation { table }) if table == flat
    ));
    assert!(matches!(
        action.lookup_with_fallback(
            flat,
            &[left.into()],
            ColumnId::new(1),
            ExternalFunctionId::new(0),
            &[],
        ),
        Err(QueryError::UnsupportedKeyedOperation { table }) if table == flat
    ));
    assert!(matches!(
        action.remove(flat, &[left.into()]),
        Err(QueryError::UnsupportedKeyedOperation { table }) if table == flat
    ));
    action.insert(flat, &[left.into(), right.into()]).unwrap();
    action.build();
}

#[test]
fn parallel_batches_are_appended_without_loss() {
    empty_execution_state!(exec_state);
    let mut table = WrappedTable::new(FlatTable::new(2));
    let batches = 64;
    let rows_per_batch = 128;

    std::thread::scope(|scope| {
        for batch in 0..batches {
            let table = &table;
            scope.spawn(move || {
                let mut buffer = table.new_buffer();
                for row in 0..rows_per_batch {
                    let id = batch * rows_per_batch + row;
                    buffer.stage_insert(&[v(id), v(batch)]);
                }
            });
        }
    });
    let pool = egglog_concurrency::ThreadPool::new(4);
    pool.install(|| table.merge(&mut exec_state));

    assert_eq!(table.len(), batches * rows_per_batch);
    let rows = sorted_rows(&table);
    assert_eq!(rows.first(), Some(&vec![v(0), v(0)]));
    assert_eq!(
        rows.last(),
        Some(&vec![v(batches * rows_per_batch - 1), v(batches - 1)])
    );
}

#[test]
fn removals_wrong_arity_and_stale_rows_are_rejected() {
    let table = FlatTable::new(2);
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            table.new_buffer().stage_remove(&[v(1)])
        }))
        .is_err()
    );
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            table.new_buffer().stage_insert(&[v(1)])
        }))
        .is_err()
    );
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            table.new_buffer().stage_insert(&[Value::stale(), v(1)])
        }))
        .is_err()
    );
}
