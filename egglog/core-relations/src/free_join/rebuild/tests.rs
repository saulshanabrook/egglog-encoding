use std::sync::atomic::{AtomicUsize, Ordering};

use super::*;
use crate::{SortedWritesTable, table_shortcuts::v};

struct Rewrite {
    visited: AtomicUsize,
    replacements: Vec<(usize, Value, Value)>,
}

impl RowRebuilder for Rewrite {
    fn rebuild(&self, row: &[Value], _: &mut ExecutionState, out: &mut Vec<Value>) -> bool {
        self.visited.fetch_add(1, Ordering::Relaxed);
        if !self
            .replacements
            .iter()
            .any(|&(col, old, _)| row[col] == old)
        {
            return false;
        }
        out.extend_from_slice(row);
        for &(col, old, new) in &self.replacements {
            if row[col] == old {
                out[col] = new;
            }
        }
        true
    }
}

fn fixture(n: usize) -> (Database, TableId) {
    let mut db = Database::default();
    let table = db.add_table(
        SortedWritesTable::new(
            1,
            4,
            Some(ColumnId::new(3)),
            vec![],
            Box::new(|_, old, new, out| {
                if old[2] <= new[2] {
                    return false;
                }
                out.extend_from_slice(new);
                true
            }),
        ),
        [],
        [],
    );
    db.with_execution_state(None, |state| {
        for i in 0..n {
            state.stage_insert(table, &[v(i), v(i + 100), v(i + 200), v(0)]);
        }
    });
    db.merge_all();
    (db, table)
}

#[test]
fn affected_rows_are_deduplicated_and_key_collisions_use_normal_merge() {
    let (mut db, table) = fixture(100);
    let version = db.get_table(table).version();
    let rewrite = Rewrite {
        visited: AtomicUsize::new(0),
        replacements: vec![(0, v(9), v(8)), (1, v(109), v(108))],
    };
    let invalidated = [
        RebuildValues {
            columns: &[ColumnId::new(0)],
            values: &[v(9), v(9)],
        },
        RebuildValues {
            columns: &[ColumnId::new(1)],
            values: &[v(109)],
        },
    ];
    let progress = db.rebuild_rows(
        RebuildInput {
            table,
            after: Some(&version),
            invalidated: &invalidated,
            timestamp_column: ColumnId::new(3),
            next_timestamp: v(1),
        },
        &rewrite,
        None,
    );
    assert!(progress.changed);
    assert_eq!(rewrite.visited.load(Ordering::Relaxed), 1);
    assert_eq!(
        db.get_table(table).len(),
        100,
        "rebuild only stages changes"
    );
    db.merge_all();
    assert_eq!(db.get_table(table).len(), 99);
    assert!(db.get_table(table).get_row(&[v(9)]).is_none());
    assert_eq!(
        db.get_table(table).get_row(&[v(8)]).unwrap().vals[2],
        v(208)
    );
}

#[test]
fn new_rows_and_cleared_tables_are_processed_without_new_equalities() {
    let (mut db, table) = fixture(100);
    let version = db.get_table(table).version();
    let rewrite = Rewrite {
        visited: AtomicUsize::new(0),
        replacements: vec![(1, v(109), v(108))],
    };
    db.with_execution_state(None, |state| {
        state.stage_insert(table, &[v(500), v(109), v(7), v(1)])
    });
    db.merge_all();
    let progress = db.rebuild_rows(
        RebuildInput {
            table,
            after: Some(&version),
            invalidated: &[],
            timestamp_column: ColumnId::new(3),
            next_timestamp: v(2),
        },
        &rewrite,
        None,
    );
    assert!(progress.changed);
    db.merge_all();
    assert_eq!(
        db.get_table(table).get_row(&[v(500)]).unwrap().vals[1],
        v(108)
    );
    assert_eq!(
        db.get_table(table).get_row(&[v(500)]).unwrap().vals[3],
        v(2)
    );

    db.clear_table(table);
    db.with_execution_state(None, |state| {
        state.stage_insert(table, &[v(500), v(109), v(7), v(3)])
    });
    db.merge_all();
    assert!(
        db.rebuild_rows(
            RebuildInput {
                table,
                after: Some(&progress.consumed),
                invalidated: &[],
                timestamp_column: ColumnId::new(3),
                next_timestamp: v(4),
            },
            &rewrite,
            None
        )
        .changed
    );
    db.merge_all();
    assert_eq!(
        db.get_table(table).get_row(&[v(500)]).unwrap().vals[1],
        v(108)
    );
}

#[test]
fn output_only_replacement_survives_and_noop_keeps_version() {
    let (mut db, table) = fixture(100);
    let rewrite = Rewrite {
        visited: AtomicUsize::new(0),
        replacements: vec![(2, v(220), v(0))],
    };
    let progress = db.rebuild_rows(
        RebuildInput {
            table,
            after: None,
            invalidated: &[],
            timestamp_column: ColumnId::new(3),
            next_timestamp: v(1),
        },
        &rewrite,
        None,
    );
    assert!(progress.changed);
    db.merge_all();
    let row = db.get_table(table).get_row(&[v(20)]).unwrap();
    assert_eq!(row.vals.as_slice(), &[v(20), v(120), v(0), v(1)]);
    let version = db.get_table(table).version();
    let progress = db.rebuild_rows(
        RebuildInput {
            table,
            after: Some(&version),
            invalidated: &[],
            timestamp_column: ColumnId::new(3),
            next_timestamp: v(2),
        },
        &rewrite,
        None,
    );
    assert!(!progress.changed);
    assert!(!db.merge_all());
    assert_eq!(db.get_table(table).version(), version);
}

#[test]
fn full_parallel_pass_visits_every_live_row_once() {
    struct VisitOnce(Vec<AtomicUsize>);
    impl RowRebuilder for VisitOnce {
        fn rebuild(&self, row: &[Value], _: &mut ExecutionState, _: &mut Vec<Value>) -> bool {
            assert_eq!(self.0[row[0].index()].fetch_add(1, Ordering::Relaxed), 0);
            false
        }
    }
    // Several bounded batches per worker, with a partial final batch and stale
    // physical rows. Reusing a scan buffer must not replay its previous rows.
    let n = 100_003;
    for threads in [1, 4, 8, 12] {
        let pool = egglog_concurrency::ThreadPool::new(threads);
        pool.install(|| {
            let (mut db, table) = fixture(n);
            db.with_execution_state(None, |state| {
                for i in (0..n).step_by(3) {
                    state.stage_remove(table, &[v(i)]);
                }
            });
            db.merge_all();
            let rewrite = VisitOnce((0..n).map(|_| AtomicUsize::new(0)).collect());
            assert!(
                !db.rebuild_rows(
                    RebuildInput {
                        table,
                        after: None,
                        invalidated: &[],
                        timestamp_column: ColumnId::new(3),
                        next_timestamp: v(1),
                    },
                    &rewrite,
                    None
                )
                .changed
            );
            for (i, count) in rewrite.0.iter().enumerate() {
                assert_eq!(
                    count.load(Ordering::Relaxed),
                    usize::from(!i.is_multiple_of(3)),
                    "row={i}, threads={threads}"
                );
            }
        });
    }
}

#[test]
fn large_invalidation_batches_preserve_new_and_unaffected_rows() {
    for threads in [1, 4, 8, 12] {
        egglog_concurrency::ThreadPool::new(threads).install(|| {
            let (mut db, table) = fixture(100);
            let version = db.get_table(table).version();
            db.with_execution_state(None, |state| {
                state.stage_insert(table, &[v(500), v(109), v(7), v(1)]);
            });
            db.merge_all();
            // Almost all invalidated values are absent from this view. The
            // affected value occurs in both an old row and a newly added row.
            let mut values: Vec<_> = (1_000..2_000).map(v).collect();
            values.push(v(109));
            let rewrite = Rewrite {
                visited: AtomicUsize::new(0),
                replacements: vec![(1, v(109), v(0))],
            };
            let progress = db.rebuild_rows(
                RebuildInput {
                    table,
                    after: Some(&version),
                    invalidated: &[RebuildValues {
                        columns: &[ColumnId::new(1)],
                        values: &values,
                    }],
                    timestamp_column: ColumnId::new(3),
                    next_timestamp: v(2),
                },
                &rewrite,
                None,
            );
            assert!(progress.changed);
            db.merge_all();
            assert_eq!(db.get_table(table).len(), 101);
            for i in 0..100 {
                let row = db.get_table(table).get_row(&[v(i)]).unwrap();
                let expected = if i == 9 { v(0) } else { v(i + 100) };
                assert_eq!(row.vals[1], expected);
                assert_eq!(row.vals[2], v(i + 200));
            }
            assert_eq!(
                db.get_table(table).get_row(&[v(500)]).unwrap().vals[1],
                v(0)
            );
        });
    }
}

#[test]
fn parallel_replacements_preserve_collision_results() {
    struct PairKeys;
    impl RowRebuilder for PairKeys {
        fn rebuild(&self, row: &[Value], _: &mut ExecutionState, out: &mut Vec<Value>) -> bool {
            if row[0].index().is_multiple_of(2) {
                return false;
            }
            out.extend_from_slice(row);
            out[0] = v(row[0].index() - 1);
            out[1] = v(row[1].index() - 1);
            true
        }
    }
    for threads in [1, 4, 8, 12] {
        egglog_concurrency::ThreadPool::new(threads).install(|| {
            let (mut db, table) = fixture(10_000);
            assert!(
                db.rebuild_rows(
                    RebuildInput {
                        table,
                        after: None,
                        invalidated: &[],
                        timestamp_column: ColumnId::new(3),
                        next_timestamp: v(1),
                    },
                    &PairKeys,
                    None
                )
                .changed
            );
            db.merge_all();
            assert_eq!(db.get_table(table).len(), 5_000);
            for i in (0..10_000).step_by(2) {
                assert_eq!(
                    db.get_table(table).get_row(&[v(i)]).unwrap().vals[2],
                    v(i + 200)
                );
                assert!(db.get_table(table).get_row(&[v(i + 1)]).is_none());
            }
        });
    }
}
