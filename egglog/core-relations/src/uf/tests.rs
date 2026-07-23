use crate::numeric_id::NumericId;

use crate::{
    CauseDraftId,
    common::Value,
    table_spec::{ColumnId, Constraint, Table},
};

use super::DisplacedTable;

fn v(x: usize) -> Value {
    Value::from_usize(x)
}

#[test]
fn displaced() {
    empty_execution_state!(e);
    let mut d = DisplacedTable::default();
    assert!(
        d.equality_components.is_none(),
        "ordinary UF starts without a receipt component sidecar"
    );
    {
        let mut buf = d.new_buffer();
        buf.stage_insert(&[v(0), v(1), v(0)]);
        buf.stage_insert(&[v(2), v(3), v(0)]);
    }
    d.merge(&mut e);
    assert!(
        d.equality_components.is_none(),
        "ordinary UF insertion must not allocate a receipt component sidecar"
    );
    let all = d.all();
    let mut updates = Vec::new();
    d.scan_generic(all.as_ref(), |_, row| {
        assert_eq!(row[2], v(0));
        updates.push((row[0], row[1]))
    });
    assert_eq!(updates.len(), 2);
    assert_ne!(updates[0], updates[1]);
    let eq_fst = d.refine(
        all,
        &[Constraint::EqConst {
            col: ColumnId::new(0),
            val: updates[0].0,
        }],
    );
    let mut rows = Vec::new();
    d.scan_generic(eq_fst.as_ref(), |_, row| {
        assert_eq!(row.len(), 3);
        rows.push((row[0], row[1], row[2]))
    });
    assert_eq!(rows, vec![(updates[0].0, updates[0].1, v(0))]);

    d.new_buffer().stage_insert(&[v(1), v(3), v(1)]);
    d.merge(&mut e);
    assert!(
        d.equality_components.is_none(),
        "ordinary UF merges keep the receipt component sidecar absent"
    );

    let all = d.all();
    let mut updates_2 = Vec::new();
    d.scan_generic(all.as_ref(), |_, row| updates_2.push((row[0], row[1])));
    assert!(updates_2.windows(2).all(|x| x[0].1 == x[1].1));
}

#[test]
fn ordinary_caused_staging_preserves_native_union_behavior() {
    empty_execution_state!(e);
    let mut table = DisplacedTable::default();
    {
        let mut buffer = table.new_buffer();
        buffer.stage_insert_with_cause(&[v(4), v(5), v(0)], CauseDraftId::new(1));
    }
    table.merge(&mut e);
    assert_eq!(
        table.underlying_uf().find_naive(v(4)),
        table.underlying_uf().find_naive(v(5))
    );
    assert!(table.equality_components.is_none());
}
