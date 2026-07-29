use super::*;
use crate::table::SortedWritesTable;

fn relation(panic_on_conflict: bool) -> SortedWritesTable {
    SortedWritesTable::new(
        1,
        2,
        None,
        vec![],
        Box::new(move |_, _, _, _| {
            assert!(!panic_on_conflict, "intentional merge failure");
            false
        }),
    )
}

fn stage(db: &Database, table: TableId, value: u32) {
    let mut buffer = db.new_buffer(table);
    buffer.stage_insert(&[Value::new(0), Value::new(value)]);
}

#[test]
fn merge_simple_restores_table_before_resuming_unwind() {
    let mut db = Database::default();
    let table = db.add_table(relation(true), [], []);
    stage(&db, table, 1);
    assert!(db.merge_all());

    stage(&db, table, 2);
    let failed = catch_unwind(AssertUnwindSafe(|| db.merge_all()));
    assert!(failed.is_err());
    assert_eq!(db.get_table(table).len(), 1);
}

#[test]
fn merge_table_restores_table_and_size_before_resuming_unwind() {
    let mut db = Database::default();
    let table = db.add_table(relation(true), [], []);
    {
        let mut buffer = db.get_table(table).new_buffer();
        buffer.stage_insert(&[Value::new(0), Value::new(1)]);
    }
    assert!(db.merge_table(table));
    assert_eq!(db.total_size_estimate, 1);

    {
        let mut buffer = db.get_table(table).new_buffer();
        buffer.stage_insert(&[Value::new(0), Value::new(2)]);
    }
    let failed = catch_unwind(AssertUnwindSafe(|| db.merge_table(table)));
    assert!(failed.is_err());
    assert_eq!(db.get_table(table).len(), 1);
    assert_eq!(db.total_size_estimate, 1);
}

#[test]
fn strata_merge_restores_every_extracted_table_before_resuming_unwind() {
    let mut db = Database::default();
    let tables = [
        db.add_table(relation(false), [], []),
        db.add_table(relation(false), [], []),
        db.add_table(relation(true), [], []),
        db.add_table(relation(false), [], []),
    ];
    for table in tables {
        stage(&db, table, 1);
    }
    assert!(db.merge_all());

    for table in tables {
        stage(&db, table, 2);
    }
    let failed = catch_unwind(AssertUnwindSafe(|| db.merge_all()));
    assert!(failed.is_err());
    for table in tables {
        assert_eq!(db.get_table(table).len(), 1);
    }
}
