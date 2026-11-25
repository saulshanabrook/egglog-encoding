use egglog::CommandOutput;
use egglog_gpu::Backend;
use std::sync::Arc;

#[test]
fn relational_shader_validates() {
    let module = naga::front::wgsl::parse_str(include_str!("../src/relational.wgsl")).unwrap();
    naga::valid::Validator::new(
        naga::valid::ValidationFlags::all(),
        naga::valid::Capabilities::empty(),
    )
    .validate(&module)
    .unwrap();
}

#[test]
#[ignore = "requires software Vulkan"]
fn replacement_software_vulkan() {
    let backend = Arc::new(Backend::vulkan(egglog_gpu::AdapterMode::Software, 1_000_000).unwrap());
    programs(backend.clone());
    keyed_batches(backend.clone());
    multiplicity(backend.clone());
    assert!(backend.statistics().device_dispatches > 0);
}

#[test]
fn independent_backend_runs_term_encoding() {
    let backend = Arc::new(Backend::simulated(1_000_000));
    programs(backend.clone());
}

#[test]
fn simulated_keyed_batches() {
    keyed_batches(Arc::new(Backend::simulated(1_000_000)));
}

#[test]
fn projection_preserves_native_action_multiplicity() {
    multiplicity(Arc::new(Backend::simulated(100)));
}

fn multiplicity(backend: Arc<Backend>) {
    use egglog_core_relations::{
        BackendTable, Database, FlatTable, PlanStrategy, RelationalBackend, TableSchema, Value,
        make_external_func,
    };
    use egglog_numeric_id::NumericId;
    use std::sync::atomic::{AtomicUsize, Ordering};
    let run = |replacement: bool, shared: bool, decompose: bool| {
        let mut db = Database::new();
        if replacement {
            db.set_relational_backend(backend.clone());
        }
        let mut table = |arity| {
            if replacement {
                db.add_wrapped_table_named(
                    backend.create_table(BackendTable {
                        read_only: false,
                        schema: TableSchema::Flat { n_cols: arity },
                        timestamp: None,
                        rebuild_columns: vec![],
                        merge: None,
                    }),
                    "multiplicity".into(),
                    [],
                    [],
                )
            } else {
                db.add_table(FlatTable::new(arity), [], [])
            }
        };
        let source = table(2);
        let gate = table(1);
        {
            let mut buffer = db.new_buffer(source);
            buffer.stage_insert(&[Value::new(1), Value::new(2)]);
            buffer.stage_insert(&[Value::new(1), Value::new(3)]);
            let mut buffer = db.new_buffer(gate);
            for value in if shared { vec![2, 3] } else { vec![1] } {
                buffer.stage_insert(&[Value::new(value)]);
            }
        }
        db.merge_all();
        let count = Arc::new(AtomicUsize::new(0));
        let calls = count.clone();
        let action = db.add_external_function(Box::new(make_external_func(move |_, _| {
            calls.fetch_add(1, Ordering::Relaxed);
            Some(Value::new(0))
        })));
        let mut builder = db.new_rule_set();
        let mut query = builder.new_rule();
        query.set_plan_strategy(PlanStrategy::Gj);
        query.set_no_decomp(!decompose);
        let x = query.new_var();
        let y = query.new_var();
        query.add_atom(source, &[x.into(), y.into()], []).unwrap();
        query
            .add_atom(gate, &[if shared { y } else { x }.into()], [])
            .unwrap();
        let mut rule = query.build();
        rule.call_external(action, &[x.into()]).unwrap();
        rule.build();
        let rules = builder.build();
        db.run_rule_set(&rules, Default::default(), None);
        count.load(Ordering::Relaxed)
    };
    for shared in [false, true] {
        for decompose in [false, true] {
            assert_eq!(
                run(true, shared, decompose),
                run(false, shared, decompose),
                "shared={shared}, decompose={decompose}"
            );
        }
    }
}

// Exercise the replacement ABI directly: repeated requests across rules share
// predictions, nested terms use the returned ids, and CurrentVal copies the
// just-allocated id rather than allocating another one.
fn keyed_batches(backend: Arc<Backend>) {
    keyed_batch(backend.clone(), false);
    keyed_batch(backend, true);
}

fn keyed_batch(backend: Arc<Backend>, host_first: bool) {
    use egglog_core_relations::{
        ActionInstruction as Op, BackendTable, ColumnId, Database, MergeVal, QueryEntry as E,
        RelationalAtom, RelationalBackend, RelationalRule, TableSchema, Value, Variable,
        WriteVal as W, make_external_func,
    };
    use egglog_numeric_id::NumericId;
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
            "test".into(),
            [],
            [],
        )
    };
    let input = add(TableSchema::Flat { n_cols: 2 });
    let term = add(TableSchema::Fd {
        n_keys: 1,
        n_vals: 2,
    });
    let parent = add(TableSchema::Fd {
        n_keys: 1,
        n_vals: 1,
    });
    let out = add(TableSchema::Fd {
        n_keys: 1,
        n_vals: 2,
    });
    let counter = db.add_counter();
    {
        let mut buffer = db.new_buffer(input);
        for i in 0..130 {
            for duplicate in 0..3 {
                buffer.stage_insert(&[Value::new(i), Value::new(duplicate)]);
            }
        }
    }
    db.merge_all();
    let callback = db.add_external_function(Box::new(make_external_func(move |state, args| {
        // The opaque primitive and the device action must see the same staged
        // parent even though it is not committed until after both rules finish.
        Some(state.predict_col(
            parent,
            args,
            [MergeVal::Counter(counter)].into_iter(),
            ColumnId::new(1),
        ))
    })));
    let [x, local, id, pid, from_host] = [0, 1, 2, 3, 4].map(Variable::new);
    let mut rule = RelationalRule {
        description: "keyed batch".into(),
        atoms: vec![RelationalAtom {
            table: input,
            columns: vec![(ColumnId::new(0), x), (ColumnId::new(1), local)],
            constraints: vec![],
            occurrence: None,
        }],
        inputs: vec![x],
        instructions: vec![
            Op::LookupOrInsertDefault {
                table: term,
                args: vec![E::Var(x)],
                default: vec![W::IncCounter(counter), W::CurrentVal(1)],
                dst_col: ColumnId::new(1),
                dst_var: id,
            },
            Op::LookupOrInsertDefault {
                table: parent,
                args: vec![E::Var(id)],
                default: vec![W::IncCounter(counter)],
                dst_col: ColumnId::new(1),
                dst_var: pid,
            },
            Op::External {
                func: callback,
                args: vec![E::Var(id)],
                dst: from_host,
            },
            Op::AssertEq(E::Var(pid), E::Var(from_host)),
            Op::Insert {
                table: out,
                vals: vec![
                    W::QueryEntry(E::Var(x)),
                    W::QueryEntry(E::Var(id)),
                    W::QueryEntry(E::Var(pid)),
                ],
                bind: None,
            },
        ],
    };
    if host_first {
        rule.instructions.swap(1, 2);
    }
    let counts = db.with_execution_state(None, |state| {
        backend
            .execute(&[rule.clone(), rule.clone()], state)
            .unwrap()
    });
    assert_eq!(counts, [130, 130]);
    db.merge_all();
    db.with_execution_state(None, |state| {
        backend.check_tables(state).unwrap();
        assert_eq!(state.read_counter(counter), 260);
    });
    let mut ids = std::collections::BTreeSet::new();
    for i in 0..130 {
        let row = db.get_table(term).get_row(&[Value::new(i)]).unwrap();
        assert_eq!(row.vals[1], row.vals[2]);
        assert!(ids.insert(row.vals[1]));
        let parent_row = db.get_table(parent).get_row(&[row.vals[1]]).unwrap();
        assert!(ids.insert(parent_row.vals[1]));
        let output = db.get_table(out).get_row(&[Value::new(i)]).unwrap();
        assert_eq!(&output.vals[1..], &[row.vals[1], parent_row.vals[1]]);
    }
    db.with_execution_state(None, |state| {
        backend.execute(&[rule], state).unwrap();
        assert_eq!(
            state.read_counter(counter),
            260,
            "hits must not consume ids"
        );
        let remaining = u32::MAX as usize - 260;
        assert_eq!(
            state.reserve_counter(counter, remaining).unwrap().end,
            u32::MAX as usize
        );
        assert!(state.reserve_counter(counter, 1).is_err());
        assert_eq!(state.read_counter(counter), u32::MAX as usize);
    });
}

#[test]
fn capacity_failure_is_an_error() {
    let backend = Arc::new(Backend::simulated(1));
    let error = backend
        .egraph()
        .parse_and_run_program(None, include_str!("../examples/scheduled-terms.egg"))
        .unwrap_err();
    assert!(error.to_string().contains("limit"), "{error}");
}

fn programs(backend: Arc<Backend>) {
    for source in [
        include_str!("../examples/scheduled-terms.egg"),
        include_str!("../examples/containers.egg"),
        include_str!("../../egglog/tests/term-encoding-subsume-rebuild-bug.egg"),
        include_str!("../../egglog/tests/repro-small-rebuild-fail-term-encoding.egg"),
        include_str!("../../egglog/tests/repro-typecheck-term-encoding.egg"),
        include_str!("../../egglog/tests/custom-eqsort-output-rebuild.egg"),
        include_str!("../../egglog/tests/merge-during-rebuild.egg"),
        include_str!("../../egglog/tests/merge-saturates.egg"),
        include_str!("../../egglog/tests/subsume-relation.egg"),
        include_str!("../../egglog/tests/delete.egg"),
        include_str!("../../egglog/tests/repro-new-backend-delete.egg"),
        include_str!("../../egglog/tests/complex-merge-func.egg"),
        r#"
            (datatype T (N i64) (F T))
            (relation seed (i64))
            (seed 1) (seed 2)
            (ruleset a) (ruleset b)
            (rule ((seed x)) ((F (N 0))) :ruleset a)
            (rule ((seed x)) ((F (N 0))) :ruleset b)
            (run-schedule (repeat 3 (seq (run a) (run b))))
            (print-size N) (print-size F)
            (push)
            (union (N 0) (N 1))
            (run 1)
            (check (= (F (N 0)) (F (N 1))))
            (pop)
            (fail (check (= (N 0) (N 1))))
            (run-schedule (run a))
            (print-size N) (print-size F)
        "#,
        r#"
            (relation edge (i64 i64))
            (relation path (i64 i64))
            (edge 1 2) (edge 2 3) (edge 3 4)
            (ruleset step)
            (rule ((edge x y)) ((path x y)) :ruleset step)
            (rule ((path x y) (path y z)) ((path x z)) :ruleset step)
            (run-schedule (run step))
            (fail (check (path 1 3)))
            (run-schedule (run step :until (path 1 3)))
            (check (path 1 3))
            (fail (check (path 1 4)))
            (run-schedule (saturate step))
            (check (path 1 4))
            (print-size path)
        "#,
    ] {
        let mut graph = backend.egraph();
        let actual = graph.parse_and_run_program(None, source).unwrap();
        let mut reference = egglog_experimental::new_experimental_egraph_with_term_encoding();
        let expected = reference.parse_and_run_program(None, source).unwrap();
        assert_eq!(
            CommandOutput::snapshot_stable_under_proof_encoding(&actual),
            CommandOutput::snapshot_stable_under_proof_encoding(&expected)
        );
    }
    assert!(backend.statistics().rules > 0);
    assert!(backend.statistics().actions > 0);
    assert!(backend.statistics().tables > 1);
}

#[test]
fn frontend_rejections_are_preserved() {
    for source in [
        include_str!("../../egglog/tests/merge-action-block.egg"),
        include_str!("../../egglog/tests/merge_read.egg"),
        include_str!("../../egglog/tests/unsafe-seminaive-read-prim.egg"),
        include_str!("../../egglog/tests/delete-then-set.egg"),
        include_str!("../../egglog/tests/complex-merge-prim.egg"),
        include_str!("../../egglog/tests/tuple-output.egg"),
    ] {
        let expected = egglog_experimental::new_experimental_egraph_with_term_encoding()
            .parse_and_run_program(None, source)
            .unwrap_err();
        let actual = Arc::new(Backend::simulated(1_000_000))
            .egraph()
            .parse_and_run_program(None, source)
            .unwrap_err();
        assert_eq!(actual.to_string(), expected.to_string());
    }
}
