use std::iter;

use egglog_core_relations::{
    ColumnId, Database, DisplacedTable, MutationBuffer, QueryEntry, ReportLevel,
    RuleSetBuilder, SortedWritesTable, Table, Value,
};

fn v(n: usize) -> Value {
    Value::new(n as u32)
}

fn relation(n_keys: usize, n_cols: usize) -> SortedWritesTable {
    SortedWritesTable::new(
        n_keys,
        n_cols,
        None,
        vec![],
        Box::new(|_, left, right, _| {
            assert_eq!(left, right, "merge not supported");
            false
        }),
    )
}

fn rows(db: &Database, table: egglog_core_relations::TableId) -> Vec<Vec<Value>> {
    let table = db.get_table(table);
    let mut out = vec![];
    table
        .scan(table.all().as_ref())
        .iter()
        .for_each(|(_, row)| out.push(row.to_vec()));
    out
}

fn run_constant_probe(
    db: &mut Database,
    source: egglog_core_relations::TableId,
    output: egglog_core_relations::TableId,
    probe: Value,
) {
    let mut rules = RuleSetBuilder::new(db);
    let mut query = rules.new_rule();
    let c0 = query.new_var_named("c0");
    let c1 = query.new_var_named("c1");
    let c2 = query.new_var_named("c2");
    query
        .add_occurrence_atom(
            source,
            &[c0.into(), c1.into(), c2.into()],
            QueryEntry::Const(probe),
            &[ColumnId::new(0), ColumnId::new(1)],
            &[],
        )
        .unwrap();
    let mut action = query.build();
    action.insert(output, &[c0.into()]).unwrap();
    action.build();
    let rules = rules.build();
    db.run_rule_set(&rules, ReportLevel::TimeOnly);
}

fn main() {
    let mut db = Database::default();
    let source = db.add_table(DisplacedTable::default(), iter::empty(), iter::empty());
    let first = db.add_table(relation(1, 1), iter::empty(), iter::empty());
    let second = db.add_table(relation(1, 1), iter::empty(), iter::empty());

    {
        let mut b = db.new_buffer(source);
        b.stage_insert(&[v(0), v(1), v(0)]);
        b.stage_insert(&[v(2), v(3), v(0)]);
    }
    db.merge_all();
    let before = rows(&db, source);
    assert_eq!(before.len(), 2);

    // Prime the database-level occurrence index while column 1 has two leaders.
    run_constant_probe(&mut db, source, first, before[0][1]);
    db.merge_all();

    // merge_table is a supported low-level merge path. It advances the table's
    // minor version without resetting database-level indexes.
    {
        let mut b = db.new_buffer(source);
        b.stage_insert(&[before[0][1], before[1][1], v(1)]);
    }
    assert!(db.merge_table(source));

    let after = rows(&db, source);
    assert_eq!(after.len(), 3);
    let leader = after[0][1];
    assert!(after.iter().all(|row| row[1] == leader));

    run_constant_probe(&mut db, source, second, leader);
    db.merge_all();
    let got = rows(&db, second);
    println!("source rows: {after:?}");
    println!("matched keys: {got:?}");
    assert_eq!(got.len(), 3, "every source row contains the final leader");
}
