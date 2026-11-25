use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};

use egglog_core_relations::{
    ActionInstruction as Op, BackendTable, ColumnId, Database, QueryEntry as E, RelationalAtom,
    RelationalBackend, RelationalRule, TableSchema, Value, Variable, WriteVal as W,
    make_external_func,
};
use egglog_gpu::{AdapterMode, Backend};
use egglog_numeric_id::NumericId;

#[test]
fn simulated_actions_preserve_partial_effects_and_failures() {
    actions(Arc::new(Backend::simulated(1000)));
}

#[test]
#[ignore = "requires software Vulkan"]
fn device_actions_preserve_partial_effects_and_failures() {
    actions(Arc::new(
        Backend::vulkan(AdapterMode::Software, 1000).unwrap(),
    ));
}

fn actions(backend: Arc<Backend>) {
    let mut db = Database::new();
    db.set_relational_backend(backend.clone());
    let mut add = |schema| {
        db.add_wrapped_table_named(
            backend.create_table(BackendTable {
                read_only: false,
                schema,
                timestamp: None,
                rebuild_columns: vec![],
                merge: Some(Box::new(|_, old, new, out| {
                    if old == new {
                        false
                    } else {
                        out.extend_from_slice(new);
                        true
                    }
                })),
            }),
            "actions".into(),
            [],
            [],
        )
    };
    let input = add(TableSchema::Flat { n_cols: 3 });
    let lookup = add(TableSchema::Fd {
        n_keys: 1,
        n_vals: 1,
    });
    let output = add(TableSchema::Fd {
        n_keys: 1,
        n_vals: 5,
    });
    let eq = add(TableSchema::Flat { n_cols: 1 });
    let final_output = add(TableSchema::Flat { n_cols: 2 });
    let counter = db.add_counter();
    {
        let mut buffer = db.new_buffer(input);
        for row in [[0, 5, 5], [1, 5, 6], [2, 7, 8], [3, 9, 9]] {
            buffer.stage_insert(&row.map(Value::new));
        }
        let mut buffer = db.new_buffer(lookup);
        for row in [[0, 10], [1, 20]] {
            buffer.stage_insert(&row.map(Value::new));
        }
    }
    db.merge_all();
    let calls = Arc::new(AtomicUsize::new(0));
    let calls2 = calls.clone();
    let fallback = db.add_external_function(Box::new(make_external_func(move |_, args| {
        calls2.fetch_add(1, Ordering::Relaxed);
        (args[0].rep() != 3).then(|| Value::new(args[0].rep() + 100))
    })));
    let first = db.add_external_function(Box::new(make_external_func(|_, args| {
        (args[0].rep() == 0).then(|| Value::new(200))
    })));
    let second = db.add_external_function(Box::new(make_external_func(|_, args| {
        (args[0].rep() != 2).then(|| Value::new(args[0].rep() + 200))
    })));
    let [x, l, r, d, dc, f, ext, clock, bound, loaded] =
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9].map(Variable::new);
    let v = E::Var;
    let c = |x| E::Const(Value::new(x));
    let rule = RelationalRule {
        description: "opcodes".into(),
        atoms: vec![RelationalAtom {
            table: input,
            columns: [x, l, r]
                .into_iter()
                .enumerate()
                .map(|(i, v)| (ColumnId::from_usize(i), v))
                .collect(),
            constraints: vec![],
            occurrence: None,
        }],
        inputs: vec![x, l, r],
        instructions: vec![
            Op::ReadCounter {
                counter,
                dst: clock,
            },
            Op::LookupWithDefault {
                table: lookup,
                args: vec![v(x)],
                dst_col: ColumnId::new(1),
                dst_var: d,
                default: v(l),
            },
            Op::LookupWithDefault {
                table: lookup,
                args: vec![v(x)],
                dst_col: ColumnId::new(1),
                dst_var: dc,
                default: c(99),
            },
            Op::LookupWithFallback {
                table: lookup,
                table_key: vec![v(x)],
                func: fallback,
                func_args: vec![v(x)],
                dst_col: ColumnId::new(1),
                dst_var: f,
            },
            Op::ExternalWithFallback {
                f1: first,
                args1: vec![v(x)],
                f2: second,
                args2: vec![v(x)],
                dst: ext,
            },
            Op::Insert {
                table: output,
                vals: [x, d, dc, f, ext, clock]
                    .into_iter()
                    .map(|v| W::QueryEntry(E::Var(v)))
                    .collect(),
                bind: Some((ColumnId::new(3), bound)),
            },
            Op::AssertEq(v(f), v(bound)),
            Op::InsertIfEq {
                table: eq,
                l: v(l),
                r: v(r),
                vals: vec![v(x)],
            },
            Op::AssertAnyNe {
                ops: vec![v(l), v(r)],
                divider: 1,
            },
            Op::AssertNe(v(x), c(0)),
            Op::AssertEq(v(f), c(20)),
            Op::Lookup {
                table: lookup,
                args: vec![v(x)],
                dst_col: ColumnId::new(1),
                dst_var: loaded,
            },
            Op::Remove {
                table: lookup,
                args: vec![v(x)],
            },
            Op::Insert {
                table: final_output,
                vals: vec![W::QueryEntry(v(x)), W::QueryEntry(v(loaded))],
                bind: None,
            },
        ],
    };
    assert_eq!(
        db.with_execution_state(None, |state| backend.execute(&[rule], state).unwrap()),
        [1]
    );
    db.merge_all();
    db.with_execution_state(None, |state| backend.check_tables(state).unwrap());
    assert_eq!(
        calls.load(Ordering::Relaxed),
        2,
        "fallbacks run only for misses"
    );
    assert_eq!(db.get_table(output).len(), 2);
    assert_eq!(
        db.get_table(output)
            .get_row(&[Value::new(0)])
            .unwrap()
            .vals
            .as_slice(),
        &([0, 10, 10, 10, 200, 0].map(Value::new))
    );
    assert_eq!(
        db.get_table(output)
            .get_row(&[Value::new(1)])
            .unwrap()
            .vals
            .as_slice(),
        &([1, 20, 20, 20, 201, 0].map(Value::new))
    );
    assert!(db.get_table(lookup).get_row(&[Value::new(0)]).is_some());
    assert!(db.get_table(lookup).get_row(&[Value::new(1)]).is_none());
    let scan = |id| {
        let table = db.get_table(id);
        table
            .scan(table.all().as_ref())
            .iter()
            .map(|(_, r)| r.to_vec())
            .collect::<Vec<_>>()
    };
    assert_eq!(scan(eq), vec![vec![Value::new(0)]]);
    assert_eq!(
        scan(final_output),
        vec![vec![Value::new(1), Value::new(20)]]
    );
}
