use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use egglog_core_relations::{
    ActionInstruction, BackendTable, ColumnId, Constraint, Database, QueryEntry, RelationalAtom,
    RelationalBackend, RelationalRule, TableSchema, Value, Variable, WriteVal,
};
use egglog_gpu::{AdapterMode, Backend};
use egglog_numeric_id::NumericId;
use rand::{Rng, SeedableRng, rngs::StdRng};

#[test]
fn simulator_queries_match_nested_loop_oracle() {
    queries(Arc::new(Backend::simulated(1_000_000)), 500);
}

#[test]
#[ignore = "requires software Vulkan"]
fn device_queries_match_nested_loop_oracle() {
    queries(
        Arc::new(Backend::vulkan(AdapterMode::Software, 1_000_000).unwrap()),
        200,
    );
}

#[test]
fn simulator_avoids_oversized_join_candidates() {
    selective_join(Arc::new(Backend::simulated(128)));
}

#[test]
#[ignore = "requires software Vulkan"]
fn device_avoids_oversized_join_candidates() {
    selective_join(Arc::new(
        Backend::vulkan(AdapterMode::Software, 128).unwrap(),
    ));
}

fn selective_join(backend: Arc<Backend>) {
    use std::fmt::Write;
    let mut source = String::from(
        "(relation r (i64 i64 i64))\n(relation s (i64 i64 i64))\n\
         (relation t (i64 i64 i64))\n(relation answer (i64 i64 i64 i64 i64 i64))\n\
         (rule ((r a b x) (s a c y) (t x y z)) ((answer a b c x y z)))\n",
    );
    for i in 0..64 {
        writeln!(source, "(r 0 {i} {i})").unwrap();
    }
    for i in 0..65 {
        writeln!(source, "(s 0 {} {})", 1000 + i, 2000 + i).unwrap();
    }
    for i in 0..64 {
        for j in 0..2 {
            writeln!(source, "(t {i} {} {})", 2000 + i + j, 2 * i + j).unwrap();
        }
    }
    source.push_str("(run 1)\n");
    for i in 0..64 {
        for j in 0..2 {
            writeln!(
                source,
                "(check (answer 0 {i} {} {i} {} {}))",
                1000 + i + j,
                2000 + i + j,
                2 * i + j
            )
            .unwrap();
        }
    }
    // r JOIN s contains 4,160 rows, but joining through t first never exceeds
    // 128. Check every expected binding as well as the exact output size.
    let mut graph = backend.egraph();
    graph.parse_and_run_program(None, &source).unwrap();
    let egglog::CommandOutput::PrintFunctionSize(size) = graph.print_size(Some("answer")).unwrap()
    else {
        panic!("expected relation size")
    };
    assert_eq!(size, 128);
}

fn queries(backend: Arc<Backend>, cases: usize) {
    let mut rng = StdRng::seed_from_u64(7731);
    for case in 0..cases {
        let mut db = Database::new();
        db.set_relational_backend(backend.clone());
        let mut atoms = Vec::new();
        let mut oracle = vec![BTreeMap::new()];
        let mut variables = BTreeSet::new();
        for _ in 0..rng.random_range(0..5) {
            let vars: Vec<_> = (0..4)
                .filter(|_| rng.random_bool(0.5))
                .map(Variable::new)
                .collect();
            variables.extend(&vars);
            let keys = (case % 2 == 0).then_some(vars.len().saturating_sub(1));
            let table = db.add_wrapped_table_named(
                backend.create_table(BackendTable {
                    read_only: false,
                    schema: keys.map_or(TableSchema::Flat { n_cols: vars.len() }, |n_keys| {
                        TableSchema::Fd {
                            n_keys,
                            n_vals: vars.len() - n_keys,
                        }
                    }),
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
                "input".into(),
                [],
                [],
            );
            let mut rows: Vec<Vec<_>> = (0..rng.random_range(0..12))
                .map(|_| {
                    vars.iter()
                        .map(|_| Value::new(rng.random_range(0..5)))
                        .collect()
                })
                .collect();
            {
                let mut buffer = db.new_buffer(table);
                for row in &rows {
                    buffer.stage_insert(row);
                }
            }
            if let Some(keys) = keys {
                // FD updates keep the last value for each input key. The oracle
                // observes the same committed relation, independently of Store.
                rows = rows
                    .into_iter()
                    .map(|row| (row[..keys].to_vec(), row))
                    .collect::<BTreeMap<_, _>>()
                    .into_values()
                    .collect();
            }
            let mut constraints = Vec::new();
            if !vars.is_empty() && rng.random_bool(0.5) {
                let col = ColumnId::from_usize(rng.random_range(0..vars.len()));
                let val = Value::new(rng.random_range(0..5));
                constraints.push(match rng.random_range(0..6) {
                    0 => Constraint::Eq {
                        l_col: col,
                        r_col: ColumnId::from_usize(rng.random_range(0..vars.len())),
                    },
                    1 => Constraint::EqConst { col, val },
                    2 => Constraint::LtConst { col, val },
                    3 => Constraint::LeConst { col, val },
                    4 => Constraint::GtConst { col, val },
                    _ => Constraint::GeConst { col, val },
                });
            }
            let occurrence = (!vars.is_empty() && rng.random_bool(0.4)).then(|| {
                let key = match rng.random_range(0..3) {
                    0 => QueryEntry::Const(Value::new(rng.random_range(0..5))),
                    1 => {
                        variables.insert(Variable::new(4));
                        QueryEntry::Var(Variable::new(4))
                    }
                    _ => QueryEntry::Var(vars[0]),
                };
                (
                    key,
                    (0..vars.len())
                        .map(ColumnId::from_usize)
                        .collect::<Vec<_>>(),
                )
            });
            let mut candidates = Vec::new();
            for row in &rows {
                if !constraints.iter().all(|c| match *c {
                    Constraint::Eq { l_col, r_col } => row[l_col.index()] == row[r_col.index()],
                    Constraint::EqConst { col, val } => row[col.index()] == val,
                    Constraint::LtConst { col, val } => row[col.index()] < val,
                    Constraint::LeConst { col, val } => row[col.index()] <= val,
                    Constraint::GtConst { col, val } => row[col.index()] > val,
                    Constraint::GeConst { col, val } => row[col.index()] >= val,
                }) {
                    continue;
                }
                let mapped: BTreeMap<_, _> =
                    vars.iter().copied().zip(row.iter().copied()).collect();
                match &occurrence {
                    None => candidates.push(mapped),
                    Some((QueryEntry::Const(val), cols)) => {
                        if cols.iter().any(|c| row[c.index()] == *val) {
                            candidates.push(mapped);
                        }
                    }
                    Some((QueryEntry::Var(v), cols)) => {
                        for c in cols {
                            if mapped.get(v).is_none_or(|&x| x == row[c.index()]) {
                                let mut bound = mapped.clone();
                                bound.insert(*v, row[c.index()]);
                                candidates.push(bound);
                            }
                        }
                    }
                }
            }
            let mut joined = Vec::new();
            for left in &oracle {
                for right in &candidates {
                    if left
                        .iter()
                        .all(|(v, x)| right.get(v).is_none_or(|y| x == y))
                    {
                        let mut row = left.clone();
                        row.extend(right);
                        joined.push(row);
                    }
                }
            }
            oracle = joined;
            atoms.push(RelationalAtom {
                table,
                columns: vars
                    .iter()
                    .enumerate()
                    .map(|(i, &v)| (ColumnId::from_usize(i), v))
                    .collect(),
                constraints,
                occurrence,
            });
        }
        // A variable used only in one atom and absent from the RHS is
        // existential, including an occurrence key with several possible values.
        let variables: Vec<_> = variables
            .into_iter()
            .filter(|_| atoms.len() != 1 || rng.random_bool(0.5))
            .collect();
        let output = db.add_wrapped_table_named(
            backend.create_table(BackendTable {
                read_only: false,
                schema: TableSchema::Flat {
                    n_cols: variables.len(),
                },
                timestamp: None,
                rebuild_columns: vec![],
                merge: None,
            }),
            "output".into(),
            [],
            [],
        );
        db.merge_all();
        let rule = RelationalRule {
            description: "random query".into(),
            atoms,
            inputs: variables.clone(),
            instructions: vec![ActionInstruction::Insert {
                table: output,
                vals: variables
                    .iter()
                    .map(|&v| WriteVal::QueryEntry(QueryEntry::Var(v)))
                    .collect(),
                bind: None,
            }],
        };
        db.with_execution_state(None, |state| backend.execute(&[rule], state).unwrap());
        db.merge_all();
        db.with_execution_state(None, |state| backend.check_tables(state).unwrap());
        let expected: BTreeSet<Vec<_>> = oracle
            .iter()
            .map(|r| variables.iter().map(|v| r[v]).collect())
            .collect();
        let table = db.get_table(output);
        let rows = table.scan(table.all().as_ref());
        let actual: BTreeSet<_> = rows.iter().map(|(_, row)| row.to_vec()).collect();
        assert_eq!(actual, expected, "query {case}");
        assert_eq!(
            rows.len(),
            expected.len(),
            "duplicate matches in query {case}"
        );
    }
}
