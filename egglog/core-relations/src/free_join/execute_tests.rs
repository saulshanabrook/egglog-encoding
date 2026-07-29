use std::panic::{AssertUnwindSafe, catch_unwind};

use super::*;
use crate::{
    SourceRef, TableId, free_join::ProcessedConstraints, query::VarColumnMap,
    table::SortedWritesTable,
};

fn capture_test_atom(table: TableId, variable: Variable) -> Atom {
    let mut var_columns = VarColumnMap::default();
    var_columns.insert(variable, ColumnId::new(0));
    let mut fast = Pooled::<Vec<Constraint>>::default();
    fast.push(Constraint::EqConst {
        col: ColumnId::new(1),
        val: Value::new(0),
    });
    Atom {
        table,
        var_columns,
        constraints: ProcessedConstraints {
            subset: Subset::empty(),
            fast,
            slow: Default::default(),
        },
    }
}

#[test]
fn capture_witness_rejects_first_row_decoy_and_accepts_bound_row() {
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
    let selected = db.add_table_named(
        relation(),
        "Selected".into(),
        std::iter::empty(),
        std::iter::empty(),
    );
    let candidates = db.add_table_named(
        relation(),
        "Candidates".into(),
        std::iter::empty(),
        std::iter::empty(),
    );
    let trace = db.try_enable_trace().unwrap();
    let test_sort = crate::ReplaySortId::new(0);
    trace
        .register_table_layout(selected, &[Some(test_sort), Some(test_sort)])
        .unwrap();
    trace
        .register_table_layout(candidates, &[Some(test_sort), Some(test_sort)])
        .unwrap();
    let zero = trace.intern_test_term("zero");
    let one = trace.intern_test_term("one");
    let two = trace.intern_test_term("two");
    db.stage_source_row(
        selected,
        &[Value::new(2), Value::new(0)],
        &[two, zero],
        SourceRef::Synthetic(0),
    )
    .unwrap();
    db.stage_source_row(
        candidates,
        &[Value::new(1), Value::new(0)],
        &[one, zero],
        SourceRef::Synthetic(1),
    )
    .unwrap();
    db.stage_source_row(
        candidates,
        &[Value::new(2), Value::new(0)],
        &[two, zero],
        SourceRef::Synthetic(2),
    )
    .unwrap();
    assert!(db.merge_all());
    db.finalize_trace_wave().unwrap();

    let variable = Variable::new(0);
    let selected_atom = capture_test_atom(selected, variable);
    let candidate_atom = capture_test_atom(candidates, variable);
    let mut bindings = DenseIdMap::default();
    bindings.insert(variable, Value::new(2));
    let exec_state = ExecutionState::new(db.read_only_view(), Default::default());

    let action = ActionId::new(0);
    let atom = AtomId::new(0);
    let selected_fact = validated_atom_fact(
        action,
        atom,
        "test",
        &selected_atom,
        RowId::new(0),
        &bindings,
        &[variable],
        &exec_state,
    );
    assert!(!selected_fact.is_missing());
    let decoy = catch_unwind(AssertUnwindSafe(|| {
        validated_atom_fact(
            action,
            atom,
            "test",
            &candidate_atom,
            RowId::new(0),
            &bindings,
            &[variable],
            &exec_state,
        )
    }));
    assert!(
        decoy.is_err(),
        "a non-selected atom's first row must not be accepted when it contradicts bindings"
    );
    let actual = validated_atom_fact(
        action,
        atom,
        "test",
        &candidate_atom,
        RowId::new(1),
        &bindings,
        &[variable],
        &exec_state,
    );
    assert!(!actual.is_missing());
    assert_ne!(selected_fact, actual);

    let omitted = Variable::new(1);
    let mut projected_atom = candidate_atom.clone();
    projected_atom.var_columns.insert(omitted, ColumnId::new(1));
    bindings.insert(omitted, Value::new(99));
    assert_eq!(
        validated_atom_fact(
            action,
            atom,
            "projected",
            &projected_atom,
            RowId::new(1),
            &bindings,
            &[variable],
            &exec_state,
        ),
        actual,
        "a projected-out variable must ignore a stale shared-map binding"
    );
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            validated_atom_fact(
                action,
                atom,
                "projected",
                &projected_atom,
                RowId::new(1),
                &bindings,
                &[variable, omitted],
                &exec_state,
            )
        }))
        .is_err(),
        "the same variable must be checked when the native block reads it"
    );
}
