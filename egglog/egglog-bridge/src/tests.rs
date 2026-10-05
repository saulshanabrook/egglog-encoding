use std::{
    fmt::Debug,
    hash::Hash,
    slice,
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
    thread,
};

use crate::core_relations;
use crate::core_relations::{
    ContainerValue, ExternalFunctionId, Value, ValueRebuilder, make_external_func,
};
use crate::numeric_id::NumericId;
use log::debug;
use num_rational::Rational64;
use once_cell::sync::Lazy;

use crate::{
    ColumnTy, DefaultVal, EGraph, FunctionConfig, FunctionId, MergeAction, MergeFn, QueryEntry,
    TableAction, TableKind, add_expressions, define_rule,
};

#[derive(Debug, PartialEq, Eq)]
struct ActionState {
    next_id: usize,
    next_timestamp: usize,
    rows: Vec<Vec<Vec<Value>>>,
    panic: Option<String>,
}

// Include union-find rows and every physical column, including timestamps and
// subsumption flags. Public table projection would hide those differences.
fn action_state(graph: &EGraph) -> ActionState {
    let rows = std::iter::once(graph.uf_table)
        .chain(graph.funcs.iter().map(|(_, info)| info.table))
        .map(|table| {
            let mut rows = Vec::new();
            graph.scan_table(graph.db.get_table(table), |row| rows.push(row.to_vec()));
            rows.sort();
            rows
        })
        .collect();
    ActionState {
        next_id: graph.db.read_counter(graph.id_counter),
        next_timestamp: graph.db.read_counter(graph.timestamp_counter),
        rows,
        panic: graph.panic_message.lock().unwrap().clone(),
    }
}

fn ground_action_graph(threads: usize) -> (EGraph, [FunctionId; 3]) {
    let mut graph = EGraph::new(threads);
    let tables = [("A", 0), ("B", 0), ("Pair", 2)].map(|(name, inputs)| {
        graph.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id; inputs + 1],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::FreshId,
            merge: MergeFn::UnionId,
            name: name.into(),
            can_subsume: true,
        })
    });
    (graph, tables)
}

#[test]
fn batch_guard_allows_constructors_and_unit_relations() {
    let (mut graph, _) = ground_action_graph(1);
    assert!(graph.can_batch_actions());
    let unit = graph.base_values_mut().register_type::<()>();
    graph.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Base(unit)],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::AssertEq,
        name: "disequality-relation".into(),
        can_subsume: false,
    });
    assert!(graph.can_batch_actions());
    let _ = graph.container_values();
    assert!(graph.clone().can_batch_actions());
}

#[test]
fn batch_guard_rejects_non_unit_assertions_without_prior_unit_registration() {
    let (mut graph, _) = ground_action_graph(1);
    let integer = graph.base_values_mut().register_type::<i64>();
    graph.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Base(integer)],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::AssertEq,
        name: "hidden-conflict".into(),
        can_subsume: false,
    });
    assert!(!graph.can_batch_actions());
}

#[test]
fn batch_guard_checks_every_physical_merge() {
    let (mut graph, _) = ground_action_graph(1);
    let unit = graph.base_values_mut().register_type::<()>();
    let callback =
        graph.register_external_func(Box::new(make_external_func(|_, args| Some(args[0]))));
    // An unused primitive is harmless; invoking it from a merge is not.
    assert!(graph.can_batch_actions());
    for (name, outputs, default, merge) in [
        (
            "callback",
            vec![ColumnTy::Base(unit)],
            DefaultVal::Fail,
            MergeFn::Primitive(callback, vec![MergeFn::Old]),
        ),
        (
            "custom-unit-merge",
            vec![ColumnTy::Base(unit)],
            DefaultVal::Fail,
            MergeFn::Old,
        ),
        (
            "non-constructor-union",
            vec![ColumnTy::Id],
            DefaultVal::Fail,
            MergeFn::UnionId,
        ),
        (
            "tuple",
            vec![ColumnTy::Base(unit), ColumnTy::Base(unit)],
            DefaultVal::Fail,
            MergeFn::Columns(vec![MergeFn::AssertEq, MergeFn::AssertEq]),
        ),
    ] {
        let mut candidate = graph.clone();
        let n_vals = outputs.len();
        candidate.add_table(FunctionConfig {
            schema: std::iter::once(ColumnTy::Id).chain(outputs).collect(),
            n_vals,
            n_identity_vals: None,
            default,
            merge,
            name: name.into(),
            can_subsume: false,
        });
        assert!(!candidate.can_batch_actions(), "{name}");
        assert!(!candidate.clone().can_batch_actions(), "{name}");
    }
    graph.add_internal_flat_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Base(unit)],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::AssertEq,
        name: "hidden-flat-table".into(),
        can_subsume: false,
    });
    assert!(!graph.can_batch_actions());
}

#[test]
fn batch_guard_rejects_container_registration_and_mutable_access() {
    let (graph, _) = ground_action_graph(1);
    let mut exposed = graph.clone();
    let _ = exposed.container_values_mut();
    assert!(!exposed.can_batch_actions());
    assert!(!exposed.clone().can_batch_actions());

    let mut registered = graph.clone();
    registered.register_container_ty::<VecContainer>();
    assert!(!registered.can_batch_actions());

    let mut interned = graph;
    interned.get_container_value(VecContainer(vec![]));
    assert!(!interned.can_batch_actions());
}

// The same already-lowered instruction stream, executed either by an empty-LHS
// rule or in one ExecutionState. Indices name earlier lookup results.
fn execute_ground_actions(
    graph: &mut EGraph,
    lookups: &[(FunctionId, Vec<usize>)],
    union: Option<(usize, usize)>,
    direct: bool,
) -> crate::Result<()> {
    if direct {
        let lookups: Vec<_> = lookups
            .iter()
            .map(|(func, args)| (TableAction::new(graph, *func), args))
            .collect();
        let union_action = crate::UnionAction::new(graph);
        graph.run_actions(|state| {
            let mut values = Vec::new();
            for (table, args) in lookups {
                let args: Vec<_> = args.iter().map(|index| values[*index]).collect();
                values.push(table.lookup_or_insert(state, &args).unwrap());
            }
            if let Some((left, right)) = union {
                union_action.union(state, values[left], values[right]);
            }
        })
    } else {
        let mut builder = graph.new_rule("ground action oracle", false);
        let mut values = Vec::<QueryEntry>::new();
        for (table, args) in lookups {
            let args: Vec<_> = args.iter().map(|index| values[*index].clone()).collect();
            values.push(
                builder
                    .lookup(*table, &args, || "lookup failed".into())
                    .into(),
            );
        }
        if let Some((left, right)) = union {
            builder.union(values[left].clone(), values[right].clone());
        }
        let rule = builder.build();
        let result = graph.run_rules(&[rule], None);
        graph.free_rule(rule);
        result.map(|_| ())
    }
}

#[test]
fn ground_actions_match_rule_rows_ids_and_epochs() {
    for threads in [1, 4] {
        let (mut direct, [a, b, pair]) = ground_action_graph(threads);
        let (mut compiled, _) = ground_action_graph(threads);
        for (lookups, union) in [
            // Repeated absent keys must predict the same IDs within a batch.
            (
                vec![
                    (a, vec![]),
                    (a, vec![]),
                    (pair, vec![0, 1]),
                    (pair, vec![1, 0]),
                ],
                None,
            ),
            // Existing keys and self-unions still have the ordinary epoch behavior.
            (vec![(a, vec![]), (a, vec![])], Some((0, 1))),
            (vec![(b, vec![]), (pair, vec![0, 0])], None),
            // This union also merges the two Pair rows through congruence.
            (vec![(a, vec![]), (b, vec![])], Some((0, 1))),
            (
                vec![(a, vec![]), (b, vec![]), (pair, vec![0, 1])],
                Some((0, 1)),
            ),
            (vec![(a, vec![])], None),
        ] {
            execute_ground_actions(&mut compiled, &lookups, union, false).unwrap();
            execute_ground_actions(&mut direct, &lookups, union, true).unwrap();
            assert_eq!(action_state(&direct), action_state(&compiled));
        }
        // The ID counter is a reservation high-water mark, not a term count.
        // Check visible equality and congruence without assuming its block size.
        let a_id = direct.lookup_id(a, &[]).unwrap();
        let b_id = direct.lookup_id(b, &[]).unwrap();
        assert_eq!(a_id, b_id);
        let pair_id = direct.lookup_id(pair, &[a_id, a_id]).unwrap();
        assert_eq!(direct.lookup_id(pair, &[b_id, b_id]), Some(pair_id));
        assert_ne!(pair_id, a_id);
        assert_eq!(direct.table_size(pair), 1);

        // A pending panic is consumed after committing and recovery rebuilds
        // the completed effects. Compare both canonical partial states.
        for graph in [&mut direct, &mut compiled] {
            *graph.panic_message.lock().unwrap() = Some("pending panic".into());
        }
        let before = direct.next_ts();
        let lookups = [(a, vec![]), (pair, vec![0, 0]), (pair, vec![1, 0])];
        let direct_error = execute_ground_actions(&mut direct, &lookups, None, true).unwrap_err();
        let compiled_error =
            execute_ground_actions(&mut compiled, &lookups, None, false).unwrap_err();
        assert_eq!(direct_error.to_string(), compiled_error.to_string());
        assert!(direct.next_ts() > before);
        assert_eq!(action_state(&direct), action_state(&compiled));
        assert_eq!(direct.table_size(pair), 2);
    }
}

#[test]
fn rule_operation_errors_preserve_pending_work_and_empty_rules_recover_panics() {
    let (mut graph, [a, _, pair]) = ground_action_graph(1);
    let table = TableAction::new(&graph, a);
    graph.with_execution_state(None, |state| table.lookup_or_insert(state, &[]));
    *graph.panic_message.lock().unwrap() = Some("keep pending".into());
    let before = action_state(&graph);
    let mut builder = graph.new_rule("invalid lookup arity", false);
    builder.lookup(pair, &[], || "unreachable".into());
    let rule = builder.build();
    let error = graph.run_rules(&[rule], None).unwrap_err();
    assert!(
        matches!(
            error.downcast_ref::<core_relations::QueryError>(),
            Some(core_relations::QueryError::KeyArityMismatch {
                expected: 2,
                got: 0,
                ..
            })
        ),
        "{error:#}"
    );
    assert_eq!(action_state(&graph), before);
    graph.free_rule(rule);

    // Empty rule sets skip the normal merge, but panic recovery rebuilds the
    // completed effects and commits pending writes.
    assert!(graph.run_rules(&[], None).is_err());
    assert!(graph.next_ts().index() > before.next_timestamp);
    assert_eq!(graph.table_size(a), 1);
    let recovered_timestamp = graph.next_ts().index();
    graph.run_rules(&[], None).unwrap();
    assert_eq!(graph.next_ts().index(), recovered_timestamp + 1);
    assert_eq!(graph.table_size(a), 1);
    graph.run_actions(|_| {}).unwrap();
    assert_eq!(graph.table_size(a), 1);
}

#[test]
fn ground_actions_preserve_rebuild_conflict_partial_state() {
    for threads in [1, 4] {
        let (mut direct, [a, b, _]) = ground_action_graph(threads);
        let (mut compiled, _) = ground_action_graph(threads);
        for graph in [&mut direct, &mut compiled] {
            let base = graph.base_values_mut().register_type::<i64>();
            let one = graph.base_values().get(1_i64);
            let two = graph.base_values().get(2_i64);
            let function = graph.add_table(FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Base(base)],
                n_vals: 1,
                n_identity_vals: None,
                default: DefaultVal::Fail,
                merge: MergeFn::AssertEq,
                name: "conflict after union".into(),
                can_subsume: false,
            });
            let mut builder = graph.new_rule("seed distinct keys", false);
            let left = builder.lookup(a, &[], || "unreachable".into());
            let right = builder.lookup(b, &[], || "unreachable".into());
            builder.set(
                function,
                &[
                    left.into(),
                    QueryEntry::Const {
                        val: one,
                        ty: ColumnTy::Base(base),
                    },
                ],
            );
            builder.set(
                function,
                &[
                    right.into(),
                    QueryEntry::Const {
                        val: two,
                        ty: ColumnTy::Base(base),
                    },
                ],
            );
            let rule = builder.build();
            graph.run_rules(&[rule], None).unwrap();
            graph.free_rule(rule);
        }
        let before = direct.next_ts();
        let lookups = [(a, vec![]), (b, vec![])];
        let direct_error =
            execute_ground_actions(&mut direct, &lookups, Some((0, 1)), true).unwrap_err();
        let compiled_error =
            execute_ground_actions(&mut compiled, &lookups, Some((0, 1)), false).unwrap_err();
        assert!(direct_error.is::<crate::PanicError>());
        assert_eq!(direct_error.to_string(), compiled_error.to_string());
        assert_eq!(action_state(&direct), action_state(&compiled));
        assert!(direct.next_ts() > before);
        assert!(direct.panic_message.lock().unwrap().is_none());
    }
}

fn valid_flat_config(name: &str) -> FunctionConfig {
    FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::AssertEq,
        name: name.into(),
        can_subsume: false,
    }
}

#[test]
fn flat_storage_accepts_append_and_scan_semantics() {
    let mut egraph = EGraph::default();
    let table = egraph.add_internal_flat_table(valid_flat_config("flat"));
    assert!(egraph.table_is_flat(table));
    assert!(egraph.funcs[table].incremental_rebuild_rules.is_empty());
    assert_ne!(
        egraph.funcs[table].nonincremental_rebuild_rule,
        crate::RuleId::new(!0)
    );
}

#[test]
fn mint_batches_preserve_rows_and_fresh_ids() {
    for n_args in [0, 2, 12] {
        let mut egraph = EGraph::default();
        let int = egraph.base_values_mut().register_type::<i64>();
        let unit_ty = egraph.base_values_mut().register_type::<()>();
        let unit = egraph.base_values_mut().get(());
        // Mint primitives can be registered before their destination table.
        let mint = egraph.register_mint_row("proof-row".into(), n_args, vec![unit]);
        let mut schema = vec![ColumnTy::Base(int); n_args];
        schema.extend([ColumnTy::Id, ColumnTy::Base(unit_ty)]);
        let proof = egraph.add_internal_flat_table(FunctionConfig {
            schema,
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::AssertEq,
            name: "proof-row".into(),
            can_subsume: false,
        });
        let input = egraph.add_table(FunctionConfig {
            schema: vec![ColumnTy::Base(int), ColumnTy::Id],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::FreshId,
            merge: MergeFn::AssertEq,
            name: "input".into(),
            can_subsume: false,
        });
        let output = egraph.add_table(FunctionConfig {
            schema: vec![ColumnTy::Base(int), ColumnTy::Id, ColumnTy::Id],
            n_vals: 2,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::Columns(vec![MergeFn::AssertEq, MergeFn::AssertEq]),
            name: "output".into(),
            can_subsume: false,
        });
        let fixed = egraph.base_value_constant(42i64);
        let rule = {
            let mut rb = egraph.new_rule("mint twice", true);
            let x: QueryEntry = rb.new_var(ColumnTy::Base(int)).into();
            let id: QueryEntry = rb.new_var(ColumnTy::Id).into();
            rb.query_table(input, &[x.clone(), id], Some(false))
                .unwrap();
            let args: Vec<_> = (0..n_args)
                .map(|i| if i % 2 == 0 { x.clone() } else { fixed.clone() })
                .collect();
            let a = rb.call_external_func(mint, &args, ColumnTy::Id, String::new);
            let b = rb.call_external_func(mint, &args, ColumnTy::Id, String::new);
            rb.set(output, &[x, a.into(), b.into()]);
            rb.build()
        };
        assert!(!egraph.run_rules(&[rule], None).unwrap().changed());
        let mut used_ids = hashbrown::HashSet::new();
        for i in 0..600 {
            let value = egraph.base_values_mut().get(i as i64);
            used_ids.insert(egraph.add_term(input, &[value]));
        }
        assert!(egraph.run_rules(&[rule], None).unwrap().changed());
        let mut expected = hashbrown::HashMap::new();
        egraph.for_each(output, |row| {
            for &id in &row.vals[1..] {
                assert!(
                    used_ids.insert(id),
                    "mint ids must not collide with term ids"
                );
                assert!(
                    expected.insert(id, row.vals[0]).is_none(),
                    "minted ids must be unique"
                );
            }
        });
        assert_eq!(expected.len(), 1200);
        let mut count = 0;
        egraph.for_each(proof, |row| {
            let x = expected.remove(&row.vals[n_args]).unwrap();
            for i in 0..n_args {
                let expected = if i % 2 == 0 {
                    x
                } else {
                    egraph.base_values().get(42i64)
                };
                assert_eq!(row.vals[i], expected);
            }
            assert_eq!(row.vals[n_args + 1], unit);
            count += 1;
        });
        assert_eq!(count, 1200);
        assert!(expected.is_empty());
        // Scalar calls share the same counter and still stage visible rows.
        let args = vec![egraph.base_values().get(42i64); n_args];
        let scalar = egraph
            .with_execution_state(None, |state| state.call_external_func(mint, &args).unwrap());
        assert!(used_ids.insert(scalar));
        assert_ne!(scalar, egraph.fresh_id());
        egraph.flush_updates();
        let mut found = false;
        egraph.for_each(proof, |row| {
            if row.vals[n_args] == scalar {
                assert_eq!(&row.vals[..n_args], &args);
                assert_eq!(row.vals[n_args + 1], unit);
                found = true;
            }
        });
        assert!(found);
    }
}

#[test]
fn read_projection_is_part_of_table_construction() {
    let mut egraph = EGraph::default();
    let table = egraph.add_table_with_read_projection(
        FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::AssertEq,
            name: "encoded-view".into(),
            can_subsume: false,
        },
        TableKind::Constructor,
        1,
        1,
    );

    let direct = TableAction::new(&egraph, table);
    assert_eq!(
        direct.validate_read_projection(Some(TableKind::Constructor), true),
        Ok(1)
    );

    let registry = egraph.action_registry().read();
    let registered = registry.lookup_table("encoded-view").unwrap();
    assert_eq!(
        registered.validate_read_projection(Some(TableKind::Constructor), true),
        Ok(1)
    );
}

#[test]
#[should_panic(expected = "must have exactly one inert value column")]
fn flat_storage_rejects_multiple_value_columns() {
    let mut config = valid_flat_config("multiple-values");
    config.n_vals = 2;
    EGraph::default().add_internal_flat_table(config);
}

#[test]
#[should_panic(expected = "cannot declare identity value columns")]
fn flat_storage_rejects_identity_value_columns() {
    let mut config = valid_flat_config("identity-values");
    config.n_identity_vals = Some(1);
    EGraph::default().add_internal_flat_table(config);
}

#[test]
#[should_panic(expected = "cannot provide a lookup default")]
fn flat_storage_rejects_lookup_defaults() {
    let mut config = valid_flat_config("lookup-default");
    config.default = DefaultVal::FreshId;
    EGraph::default().add_internal_flat_table(config);
}

#[test]
#[should_panic(expected = "cannot provide merge behavior")]
fn flat_storage_rejects_merge_behavior() {
    let mut config = valid_flat_config("merge");
    config.merge = MergeFn::UnionId;
    EGraph::default().add_internal_flat_table(config);
}

#[test]
#[should_panic(expected = "cannot support subsumption")]
fn flat_storage_rejects_subsumption() {
    let mut config = valid_flat_config("subsumption");
    config.can_subsume = true;
    EGraph::default().add_internal_flat_table(config);
}

#[test]
#[should_panic(expected = "unknown storage implementation")]
fn flat_storage_introspection_rejects_unknown_table_types() {
    let mut egraph = EGraph::default();
    let table = egraph.add_table(valid_flat_config("displaced"));
    egraph.funcs[table].table = egraph.uf_table;
    egraph.table_is_flat(table);
}

/// Run a simple associativity/commutativity test.
///
/// The `can_subsume` argument is only used to enable subsumption on the underlying tables created
/// during this test, and exercise the different column handling caused by enabling subsumption.
/// Subsumption itself is not used.
fn ac_test(can_subsume: bool) {
    const N: usize = 5;
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();
    let num_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "num".into(),
        can_subsume,
    });
    let add_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id; 3],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "add".into(),
        can_subsume,
    });

    let add_comm = define_rule! {
        [egraph] ((-> (add_table x y) id))
              => ((set (add_table y x) id))
    };

    let add_assoc = define_rule! {
        [egraph] ((-> (add_table x (add_table y z)) id))
              => ((set (add_table (add_table x y) z) id))
    };

    // Running these rules on an empty database should change nothing.
    assert!(
        !egraph
            .run_rules(&[add_comm, add_assoc], None)
            .unwrap()
            .changed()
    );

    // Fill the database.
    let mut ids = Vec::new();
    //  Add 0 .. N to the database.
    for i in 0..N {
        let i = egraph.base_values_mut().get(i as i64);
        ids.push(egraph.add_term(num_table, &[i]));
    }

    // construct (0 + ... + N), left-associated, and (N + ... + 0),
    // right-associated. With the assoc and comm rules saturated, these two
    // should be equal.
    let (left_root, right_root) = {
        let mut prev = ids[0];
        for num in &ids[1..] {
            let id = egraph.add_term(add_table, &[*num, prev]);
            prev = id;
        }
        let left_root = prev;
        let mut prev = *ids.last().unwrap();
        for num in ids[0..(N - 1)].iter() {
            let id = egraph.add_term(add_table, &[prev, *num]);
            prev = id;
        }
        let right_root = prev;
        (left_root, right_root)
    };
    // Saturate
    while egraph
        .run_rules(&[add_comm, add_assoc], None)
        .unwrap()
        .changed()
    {}
    let canon_left = egraph.get_canon_in_uf(left_root);
    let canon_right = egraph.get_canon_in_uf(right_root);
    assert_eq!(canon_left, canon_right, "failed to reassociate!");
}

#[test]
fn ac() {
    ac_test(false);
}

#[test]
fn ac_subsume() {
    ac_test(true);
}

#[test]
fn ac_fail() {
    const N: usize = 5;
    let mut egraph = EGraph::default();
    egraph.base_values_mut().register_type::<i64>();
    let int_base = egraph.base_values_mut().get_ty::<i64>();
    let one = egraph.base_value_constant(1i64);
    let num_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "num".into(),
        can_subsume: false,
    });
    let add_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id; 3],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "add".into(),
        can_subsume: false,
    });

    let add_comm = define_rule! {
        [egraph] ((-> (add_table x y) id) (-> (num_table {one}) x))
              => ((set (add_table y x) id))
    };

    let add_assoc = define_rule! {
        [egraph] ((-> (add_table x (add_table y z)) id))
              => ((set (add_table (add_table x y) z) id))
    };

    // Running these rules on an empty database should change nothing.
    assert!(
        !egraph
            .run_rules(&[add_comm, add_assoc], None)
            .unwrap()
            .changed()
    );

    // Fill the database.
    let mut ids = Vec::new();
    //  Add 0 .. N to the database.
    let num_rows = (0..N)
        .map(|i| {
            let id = egraph.fresh_id();
            let i = egraph.base_values_mut().get(i as i64);
            ids.push(id);
            (num_table, vec![i, id])
        })
        .collect::<Vec<_>>();
    egraph.add_values(num_rows);

    // construct (0 + ... + N), left-associated, and (N + ... + 0),
    // right-associated. With the assoc and comm rules saturated, these two
    // should be equal.
    let (left_root, right_root) = {
        let mut to_add = Vec::new();
        let mut prev = ids[0];
        for num in &ids[1..] {
            let id = egraph.fresh_id();
            to_add.push((add_table, vec![*num, prev, id]));
            prev = id;
        }
        let left_root = to_add.last().unwrap().1[2];
        prev = *ids.last().unwrap();
        for num in ids[0..(N - 1)].iter() {
            let id = egraph.fresh_id();
            to_add.push((add_table, vec![prev, *num, id]));
            prev = id;
        }
        let right_root = to_add.last().unwrap().1[2];
        egraph.add_values(to_add);
        (left_root, right_root)
    };
    // Saturate
    while egraph
        .run_rules(&[add_comm, add_assoc], None)
        .unwrap()
        .changed()
    {}
    let canon_left = egraph.get_canon_in_uf(left_root);
    let canon_right = egraph.get_canon_in_uf(right_root);
    assert_ne!(canon_left, canon_right);
}

#[test]
fn math() {
    let handles =
        Vec::from_iter((0..2).map(|_| thread::spawn(|| math_test(EGraph::default(), false))));
    handles.into_iter().for_each(|h| h.join().unwrap());
}

#[test]
fn math_subsume() {
    let handles =
        Vec::from_iter((0..2).map(|_| thread::spawn(|| math_test(EGraph::default(), true))));
    handles.into_iter().for_each(|h| h.join().unwrap());
}

/// Run a more complex benchmark from the egg and egglog test suite. The core of this test is to
/// ensure that the test generates a set of tables of exactly the same
/// size that the corresponding rules in egglog do in egglog's initial implementation.
///
/// As in `ac_test` the `can_subsume` argument is only used to enable subsumption on the underlying
/// tables created during this test, and exercise the different column handling caused by enabling
/// subsumption. Subsumption itself is not used.
fn math_test(mut egraph: EGraph, can_subsume: bool) {
    const N: usize = 8;
    let rational_ty = egraph.base_values_mut().register_type::<Rational64>();
    let string_ty = egraph.base_values_mut().register_type::<&'static str>();
    // tables
    let diff = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "diff".into(),
        can_subsume,
    });
    let integral = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "integral".into(),
        can_subsume,
    });
    let add = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "add".into(),
        can_subsume,
    });
    let sub = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "sub".into(),
        can_subsume,
    });
    let mul = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "mul".into(),
        can_subsume,
    });
    let div = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "div".into(),
        can_subsume,
    });
    let pow = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "pow".into(),
        can_subsume,
    });

    let ln = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "ln".into(),
        can_subsume,
    });
    let sqrt = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "sqrt".into(),
        can_subsume,
    });
    let sin = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "sin".into(),
        can_subsume,
    });
    let cos = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "cos".into(),
        can_subsume,
    });
    let rat = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(rational_ty), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "rat".into(),
        can_subsume,
    });
    let var = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(string_ty), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "var".into(),
        can_subsume,
    });

    let zero = egraph.base_value_constant(Rational64::new(0, 1));
    let one = egraph.base_value_constant(Rational64::new(1, 1));
    let neg1 = egraph.base_value_constant(Rational64::new(-1, 1));
    let two = egraph.base_value_constant(Rational64::new(2, 1));
    let rules = [
        define_rule! {
            [egraph] ((-> (add x y) id)) => ((set (add y x) id))
        },
        define_rule! {
            [egraph] ((-> (mul x y) id)) => ((set (mul y x) id))
        },
        define_rule! {
            [egraph] ((-> (add x (add y z)) id)) => ((set (add (add x y) z) id))
        },
        define_rule! {
            [egraph] ((-> (mul x (mul y z)) id)) => ((set (mul (mul x y) z) id))
        },
        define_rule! {
            [egraph] ((-> (sub x y) id)) => ((set (add x (mul (rat {neg1.clone()}) y)) id))
        },
        define_rule! {
            [egraph] ((-> (add a (rat {zero.clone()})) id)) => ((union a id))
        },
        define_rule! {
            [egraph] ((-> (rat {zero.clone()}) z_id) (-> (mul a z_id) id))
                    => ((union id z_id))
        },
        define_rule! {
            [egraph] ((-> (mul a (rat {one.clone()})) id)) => ((union a id))
        },
        define_rule! {
            [egraph] ((-> (sub x x) id)) => ((union id (rat {zero})))
        },
        define_rule! {
            [egraph] ((-> (mul x (add b c)) id)) => ((set (add (mul x b) (mul x c)) id))
        },
        define_rule! {
            [egraph] ((-> (add (mul x a) (mul x b)) id)) => ((set (mul x (add a b)) id))
        },
        define_rule! {
            [egraph] ((-> (mul (pow a b) (pow a c)) id)) => ((set (pow a (add b c)) id))
        },
        define_rule! {
            [egraph] ((-> (pow x (rat {one.clone()})) id)) => ((union x id))
        },
        define_rule! {
            [egraph] ((-> (pow x (rat {two})) id)) => ((set (mul x x) id))
        },
        define_rule! {
            [egraph] ((-> (diff x (add a b)) id)) => ((set (add (diff x a) (diff x b)) id))
        },
        define_rule! {
            [egraph] ((-> (diff x (mul a b)) id)) => ((set (add (mul a (diff x b)) (mul b (diff x a))) id))
        },
        define_rule! {
            [egraph] ((-> (diff x (sin x)) id)) => ((set (cos x) id))
        },
        define_rule! {
            [egraph] ((-> (diff x (cos x)) id)) => ((set (mul (rat {neg1.clone()}) (sin x)) id))
        },
        define_rule! {
            [egraph] ((-> (integral (rat {one}) x) id)) => ((union id x))
        },
        define_rule! {
            [egraph] ((-> (integral (cos x) x) id)) => ((set (sin x) id))
        },
        define_rule! {
            [egraph] ((-> (integral (sin x) x) id)) => ((set (mul (rat {neg1}) (cos x)) id))
        },
        define_rule! {
            [egraph] ((-> (integral (add f g) x) id)) => ((set (add (integral f x) (integral g x)) id))
        },
        define_rule! {
            [egraph] ((-> (integral (sub f g) x) id)) => ((set (sub (integral f x) (integral g x)) id))
        },
        define_rule! {
            [egraph] ((-> (integral (mul a b) x) id))
            => ((set (sub (mul a (integral b x))
                          (integral (mul (diff x a) (integral b x)) x)) id))
        },
    ];

    {
        let one = egraph.base_values_mut().get(Rational64::new(1, 1));
        let two = egraph.base_values_mut().get(Rational64::new(2, 1));
        let three = egraph.base_values_mut().get(Rational64::new(3, 1));
        let seven = egraph.base_values_mut().get(Rational64::new(7, 1));
        let x_str = egraph.base_values_mut().get::<&'static str>("x");
        let y_str = egraph.base_values_mut().get::<&'static str>("y");
        let five_str = egraph.base_values_mut().get::<&'static str>("five");
        add_expressions! {
            [egraph]

            (integral (ln (var x_str)) (var x_str))
            (integral (add (var x_str) (cos (var x_str))) (var x_str))
            (integral (mul (cos (var x_str)) (var x_str)) (var x_str))
            (diff (var x_str)
                (add (rat one) (mul (rat two) (var x_str))))
            (diff (var x_str)
                (sub (pow (var x_str) (rat three)) (mul (rat seven) (pow (var x_str) (rat two)))))
            (add
                (mul (var y_str) (add (var x_str) (var y_str)))
                (sub (add (var x_str) (rat two)) (add (var x_str) (var x_str))))
            (div (rat one)
                 (sub (div (add (rat one) (sqrt (var five_str))) (rat two))
                      (div (sub (rat one) (sqrt (var five_str))) (rat two))))
        }
    }

    for _ in 0..N {
        if !egraph.run_rules(&rules, None).unwrap().changed() {
            break;
        }
    }

    // numbers validated against the egglog implementation.

    // Print out some debugging info. This gets hidden by default for passing tests.
    debug!("diff_size={:?} vs. 338", egraph.table_size(diff));
    debug!("integral_size={:?} vs. 782 ", egraph.table_size(integral));
    debug!("sub_size={:?} vs 483", egraph.table_size(sub));
    debug!("div_size={:?} vs. 3", egraph.table_size(div));
    debug!("pow_size={:?} vs 2", egraph.table_size(pow));
    debug!("ln_size={:?} vs 1", egraph.table_size(ln));
    debug!("sqrt_size={:?} vs 1", egraph.table_size(sqrt));
    debug!("sin_size={:?} vs 1", egraph.table_size(sin));
    debug!("cos_size={:?} vs 1", egraph.table_size(cos));
    debug!("rat_size={:?} vs 5", egraph.table_size(rat));
    debug!("var_size={:?} vs 3", egraph.table_size(var));
    debug!("add_size={:?} vs 2977", egraph.table_size(add));
    debug!("mul_size={:?} vs 3516", egraph.table_size(mul));

    assert_eq!(338, egraph.table_size(diff));
    assert_eq!(782, egraph.table_size(integral));
    assert_eq!(483, egraph.table_size(sub));
    assert_eq!(3, egraph.table_size(div));
    assert_eq!(2, egraph.table_size(pow));
    assert_eq!(1, egraph.table_size(ln));
    assert_eq!(1, egraph.table_size(sqrt));
    assert_eq!(1, egraph.table_size(sin));
    assert_eq!(1, egraph.table_size(cos));
    assert_eq!(5, egraph.table_size(rat));
    assert_eq!(3, egraph.table_size(var));
    assert_eq!(2977, egraph.table_size(add));
    assert_eq!(3516, egraph.table_size(mul));
}

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
struct VecContainer(Vec<Value>);
impl ContainerValue for VecContainer {
    fn rebuild_contents(&mut self, rebuilder: &dyn ValueRebuilder) -> bool {
        rebuilder.rebuild_slice(&mut self.0)
    }
    fn iter(&self) -> impl Iterator<Item = Value> + '_ {
        self.0.iter().copied()
    }
}

fn register_vec_push(egraph: &mut EGraph) -> ExternalFunctionId {
    egraph.register_container_ty::<VecContainer>();
    let external_func = make_external_func(move |state, vals| -> Option<Value> {
        let [vec_id, val] = vals else {
            panic!("[vec-push] expected 2 values, got {vals:?}")
        };
        let mut vec: VecContainer = state
            .container_values()
            .get_val::<VecContainer>(*vec_id)?
            .clone();
        vec.0.push(*val);
        // Vectors are immutable. May as well not use O(n) auxiliary space.
        vec.0.shrink_to_fit();
        Some(state.clone().container_values().register_val(vec, state))
    });
    egraph.register_external_func(Box::new(external_func))
}

fn register_vec_last(egraph: &mut EGraph) -> ExternalFunctionId {
    egraph.register_container_ty::<VecContainer>();
    let external_func = make_external_func(move |state, vals| -> Option<Value> {
        let [vec_id] = vals else {
            panic!("[vec-last] expected 1 value, got {vals:?}")
        };
        state
            .container_values()
            .get_val::<VecContainer>(*vec_id)?
            .0
            .last()
            .cloned()
    });
    egraph.register_external_func(Box::new(external_func))
}

fn dump_vecs(egraph: &EGraph) -> Vec<Vec<Value>> {
    let mut res = Vec::new();
    egraph
        .container_values()
        .for_each::<VecContainer>(|vec, _| res.push(vec.0.clone()));
    res
}

fn assert_unordered_eq<T: Ord + std::fmt::Debug>(mut a: Vec<T>, mut b: Vec<T>) {
    a.sort();
    b.sort();
    assert_eq!(a, b);
}

fn container_test() {
    // Test for containers:
    // * Basic math setup: (num i64), (add math math), (Vec (vec math))
    // * start with:
    //   - (Vec vec![1])
    //   - (Vec vec![])
    // * have a rule that does, for any vec, push (add 0 last-elt) onto it.
    // * have a rule that does, for any vec, push (add last-elt 0) onto it.
    // * Run this 3 times.
    // * Check that we get some decent number of vectors out.
    // * Saturate the rule that just evaluates add.
    // * should have just have:
    //  - vec![]
    //  - vec![1]
    //  - vec![1, 1]
    //  - vec![1, 1, 1]
    //  - vec![1, 1, 1, 1]
    //
    //  This tests:
    //  * basic get/set for containers.
    //  * running container operations from a rule, including ones that can fail.
    //  * Rebuilding:
    //      * rebuilding of container ids.
    //      * rebuilding inside of a container.
    //      * saturation for container rebuilding.
    //  * Dumping/foreach functionality.
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();
    let num_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "num".into(),
        can_subsume: false,
    });
    let add_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id; 3],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "add".into(),
        can_subsume: false,
    });
    let vec_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id; 2],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "vec".into(),
        can_subsume: false,
    });
    let int_add =
        egraph.register_external_func(Box::new(make_external_func(|exec_state, args| {
            let [x, y] = args else { panic!() };
            let x: i64 = exec_state.base_values().unwrap(*x);
            let y: i64 = exec_state.base_values().unwrap(*y);
            let z: i64 = x + y;
            Some(exec_state.base_values().get(z))
        })));
    let vec_last = register_vec_last(&mut egraph);
    let vec_push = register_vec_push(&mut egraph);

    let mut ids = Vec::new();
    //  Add 0 and 1 to the database.
    let num_rows = (0..=1)
        .map(|i| {
            let id = egraph.fresh_id();
            let i = egraph.base_values_mut().get(i as i64);
            ids.push(id);
            (num_table, vec![i, id])
        })
        .collect::<Vec<_>>();
    egraph.add_values(num_rows);

    let empty_vec = egraph.get_container_value(VecContainer(vec![]));
    let vec1 = egraph.get_container_value(VecContainer(vec![ids[1]]));

    let empty_vec_id = egraph.fresh_id();
    let vec1_id = egraph.fresh_id();

    egraph.add_values(vec![
        (vec_table, vec![empty_vec, empty_vec_id]),
        (vec_table, vec![vec1, vec1_id]),
    ]);

    let vec_expand = {
        let mut rb = egraph.new_rule("", true);
        let vec: QueryEntry = rb.new_var(ColumnTy::Id).into();
        let vec_id: QueryEntry = rb.new_var(ColumnTy::Id).into();
        let last: QueryEntry = rb.new_var(ColumnTy::Id).into();
        rb.query_table(vec_table, &[vec.clone(), vec_id], Some(false))
            .unwrap();
        rb.query_prim(vec_last, &[vec.clone(), last.clone()], ColumnTy::Id)
            .unwrap();
        let add_last_0 = rb
            .lookup(
                add_table,
                &[
                    last.clone(),
                    QueryEntry::Const {
                        val: ids[0],
                        ty: ColumnTy::Base(int_base),
                    },
                ],
                || "add_last_0".to_string(),
            )
            .into();
        let add_0_last = rb
            .lookup(
                add_table,
                &[
                    QueryEntry::Const {
                        val: ids[0],
                        ty: ColumnTy::Base(int_base),
                    },
                    last,
                ],
                || "add_0_last".to_string(),
            )
            .into();
        let new_vec_1 = rb
            .call_external_func(vec_push, &[vec.clone(), add_last_0], ColumnTy::Id, || {
                "".to_string()
            })
            .into();
        let new_vec_2 = rb
            .call_external_func(vec_push, &[vec, add_0_last], ColumnTy::Id, || {
                "".to_string()
            })
            .into();
        rb.lookup(vec_table, &[new_vec_1], String::new);
        rb.lookup(vec_table, &[new_vec_2], String::new);
        rb.build()
    };

    let eval_add = {
        let mut rb = egraph.new_rule("", true);
        let lhs_raw: QueryEntry = rb.new_var(ColumnTy::Base(int_base)).into();
        let lhs_id: QueryEntry = rb.new_var(ColumnTy::Id).into();
        let rhs_raw: QueryEntry = rb.new_var(ColumnTy::Base(int_base)).into();
        let rhs_id: QueryEntry = rb.new_var(ColumnTy::Id).into();
        let add_id: QueryEntry = rb.new_var(ColumnTy::Id).into();
        rb.query_table(num_table, &[lhs_raw.clone(), lhs_id.clone()], Some(false))
            .unwrap();
        rb.query_table(num_table, &[rhs_raw.clone(), rhs_id.clone()], Some(false))
            .unwrap();
        rb.query_table(
            add_table,
            &[lhs_id.clone(), rhs_id.clone(), add_id.clone()],
            Some(false),
        )
        .unwrap();
        let evaled: QueryEntry = rb
            .call_external_func(
                int_add,
                &[lhs_raw.clone(), rhs_raw.clone()],
                ColumnTy::Base(int_base),
                || "".to_string(),
            )
            .into();
        let boxed: QueryEntry = rb
            .lookup(num_table, std::slice::from_ref(&evaled), String::new)
            .into();
        rb.union(add_id.clone(), boxed.clone());
        rb.build()
    };

    assert_unordered_eq(
        dump_vecs(&egraph),
        vec![vec![], vec![egraph.get_canon_in_uf(ids[1])]],
    );

    assert!(egraph.run_rules(&[vec_expand], None).unwrap().changed());
    assert_eq!(dump_vecs(&egraph).len(), 4);
    // We have 2 new vectors with a last element. Each of those should spawn two more, adding 4.
    assert!(egraph.run_rules(&[vec_expand], None).unwrap().changed());
    assert_eq!(dump_vecs(&egraph).len(), 8);
    // We have 4 new vectors with a last element. Each of those should spawn two more, adding 8.
    assert!(egraph.run_rules(&[vec_expand], None).unwrap().changed());
    assert_eq!(dump_vecs(&egraph).len(), 16);

    // Now we want to saturate `eval_add`. This should collapse a bunch of new vectors.

    let mut saturated = false;
    for _ in 0..20 {
        saturated = !egraph.run_rules(&[eval_add], None).unwrap().changed();
        if saturated {
            break;
        }
    }
    assert!(saturated, "failed to saturate after 20 iterations");

    let one_id = egraph.get_canon_in_uf(ids[1]);
    assert_unordered_eq(
        dump_vecs(&egraph),
        vec![
            vec![],
            vec![one_id],
            vec![one_id; 2],
            vec![one_id; 3],
            vec![one_id; 4],
        ],
    );
}

#[test]
fn basic_container() {
    // Run the test 8 times to get a decent sample of incremental/nonincremental, parallel/serial.
    for _ in 0..8 {
        container_test()
    }
}

fn run_query_prim_container_match_case(seminaive: bool, seed_canonical: bool) -> bool {
    let mut egraph = EGraph::default();
    let k_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "k".into(),
        can_subsume: false,
    });
    let w_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "w".into(),
        can_subsume: false,
    });
    let l_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "l".into(),
        can_subsume: false,
    });

    let b = egraph.fresh_id();
    let k_b = egraph.add_term(k_table, &[b]);
    if seed_canonical {
        let _ = egraph.get_container_value(VecContainer(vec![k_b]));
    }
    let w_k_b = egraph.add_term(w_table, &[k_b]);
    let vec = egraph.get_container_value(VecContainer(vec![w_k_b]));
    let l_id = egraph.add_term(l_table, &[vec]);

    let raw_k_table = egraph.funcs[k_table].table;
    let match_singleton_k =
        egraph.register_external_func(Box::new(make_external_func(move |state, vals| {
            let [vec_id] = vals else {
                panic!("match_singleton_k expected 1 arg, got {vals:?}");
            };
            let vec = state.container_values().get_val::<VecContainer>(*vec_id)?;
            let [entry] = vec.0.as_slice() else {
                return None;
            };
            let table = state.get_table(raw_k_table);
            let rows = table.scan(table.all().as_ref());
            for (_, row) in rows.non_stale() {
                if row[1] == *entry {
                    return Some(row[0]);
                }
            }
            None
        })));

    let w_rewrite = {
        let mut rb = egraph.new_rule("w_rewrite", seminaive);
        let x: QueryEntry = rb.new_var(ColumnTy::Id).into();
        let w_id: QueryEntry = rb.new_var(ColumnTy::Id).into();
        rb.query_table(w_table, &[x.clone(), w_id.clone()], Some(false))
            .unwrap();
        rb.union(w_id, x);
        rb.build()
    };

    let l_rewrite = {
        let mut rb = egraph.new_rule("l_rewrite", seminaive);
        let vec: QueryEntry = rb.new_var(ColumnTy::Id).into();
        let l_id_entry: QueryEntry = rb.new_var(ColumnTy::Id).into();
        let x: QueryEntry = rb.new_var(ColumnTy::Id).into();
        rb.query_table(l_table, &[vec.clone(), l_id_entry.clone()], Some(false))
            .unwrap();
        rb.query_prim(match_singleton_k, &[vec, x.clone()], ColumnTy::Id)
            .unwrap();
        rb.union(l_id_entry, x);
        rb.build()
    };

    let mut saturated = false;
    for _ in 0..8 {
        saturated = !egraph
            .run_rules(&[w_rewrite, l_rewrite], None)
            .unwrap()
            .changed();
        if saturated {
            break;
        }
    }
    assert!(saturated, "failed to saturate after 8 iterations");
    egraph.get_canon_in_uf(l_id) == egraph.get_canon_in_uf(b)
}

#[test]
fn seminaive_query_prim_rechecks_after_rebuild() {
    assert!(run_query_prim_container_match_case(true, false));
    assert!(run_query_prim_container_match_case(false, false));
}

#[test]
fn seminaive_query_prim_rechecks_after_preseeded_container_rebuild() {
    assert!(run_query_prim_container_match_case(true, true));
}

#[test]
fn rhs_only_rule() {
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();
    let zero = egraph.base_values_mut().get(0i64);
    let one = egraph.base_values_mut().get(1i64);
    let num_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "num".into(),
        can_subsume: false,
    });
    let add_data = {
        let zero = egraph.base_value_constant(0i64);
        let one = egraph.base_value_constant(1i64);
        let mut rb = egraph.new_rule("", true);
        let _zero_id = rb.lookup(num_table, &[zero], String::new);
        let _one_id = rb.lookup(num_table, &[one], String::new);
        rb.build()
    };

    let mut contents = Vec::new();

    assert!(contents.is_empty());
    assert!(egraph.run_rules(&[add_data], None).unwrap().changed());
    egraph.for_each(num_table, |func_row| {
        assert!(!func_row.subsumed);
        contents.push(func_row.vals.to_vec());
    });

    contents.sort();
    assert_eq!(
        contents,
        vec![vec![zero, Value::new(0)], vec![one, Value::new(1)]]
    );
}

#[test]
fn rhs_only_rule_only_runs_once() {
    let mut egraph = EGraph::default();
    let counter = Arc::new(AtomicUsize::new(0));
    let inner = counter.clone();
    let inc_counter_func =
        egraph.register_external_func(Box::new(make_external_func(move |_, _| {
            inner.fetch_add(1, Ordering::SeqCst);
            Some(Value::new(0))
        })));
    let inc_counter_rule = {
        let mut rb = egraph.new_rule("", true);
        rb.call_external_func(inc_counter_func, &[], ColumnTy::Id, || "".to_string());
        rb.build()
    };

    assert!(
        !egraph
            .run_rules(&[inc_counter_rule], None)
            .unwrap()
            .changed()
    );
    assert_eq!(counter.load(Ordering::SeqCst), 1);
    assert!(
        !egraph
            .run_rules(&[inc_counter_rule], None)
            .unwrap()
            .changed()
    );
    assert_eq!(counter.load(Ordering::SeqCst), 1);
}

#[test]
fn mergefn_arithmetic() {
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();

    // Create external functions for multiplication and addition
    let multiply_func = egraph.register_external_func(Box::new(
        core_relations::make_external_func(|state, vals| -> Option<Value> {
            let [a, b] = vals else {
                return None;
            };
            let a_val = state.base_values().unwrap::<i64>(*a);
            let b_val = state.base_values().unwrap::<i64>(*b);
            let res = state.base_values().get::<i64>(a_val * b_val);
            Some(res)
        }),
    ));

    let add_func = egraph.register_external_func(Box::new(core_relations::make_external_func(
        |state, vals| -> Option<Value> {
            let [a, b] = vals else {
                return None;
            };
            let a_val = state.base_values().unwrap::<i64>(*a);
            let b_val = state.base_values().unwrap::<i64>(*b);
            let res = state.base_values().get::<i64>(a_val + b_val);
            Some(res)
        },
    )));

    let value_1 = egraph.base_values_mut().get(1i64);

    // Create a function with merge function (+ 1 (* old new))
    // This uses nested MergeFn::Primitive with external functions to build the complex merge function
    let f_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Base(int_base)],
        default: DefaultVal::Fail,
        merge: MergeFn::Primitive(
            add_func,
            vec![
                MergeFn::Const(value_1),
                MergeFn::Primitive(multiply_func, vec![MergeFn::Old, MergeFn::New]),
            ],
        ),
        name: "f".into(),
        can_subsume: false,
    });

    let value_0 = egraph.base_value_constant(0i64);
    let value_1 = egraph.base_value_constant(1i64);
    let value_2 = egraph.base_value_constant(2i64);
    let value_3 = egraph.base_value_constant(3i64);
    let value_4 = egraph.base_value_constant(4i64);
    let value_5 = egraph.base_value_constant(5i64);
    let value_6 = egraph.base_value_constant(6i64);

    // First rule writes (f 1 0) (f 2 1)
    let rule1 = {
        let mut rb = egraph.new_rule("rule1", true);
        rb.set(f_table, &[value_1.clone(), value_0]);
        rb.set(f_table, &[value_2.clone(), value_1.clone()]);
        rb.build()
    };

    // Run the first rule and check state
    assert!(egraph.run_rules(&[rule1], None).unwrap().changed());
    let mut contents = Vec::new();
    egraph.for_each(f_table, |func_row| {
        assert!(!func_row.subsumed);
        contents.push((
            egraph.base_values().unwrap::<i64>(func_row.vals[0]),
            egraph.base_values().unwrap::<i64>(func_row.vals[1]),
        ));
    });
    contents.sort();
    assert_eq!(contents, vec![(1, 0), (2, 1)]);

    // Second rule writes (f 1 5) (f 2 6)
    let rule2 = {
        let mut rb = egraph.new_rule("rule2", true);
        rb.set(f_table, &[value_1.clone(), value_5]);
        rb.set(f_table, &[value_2.clone(), value_6]);
        rb.build()
    };

    // Run the second rule and check state
    // Expected: (f 1 1) because 1 + (0 * 5) = 1
    // Expected: (f 2 7) because 1 + (1 * 6) = 7
    assert!(egraph.run_rules(&[rule2], None).unwrap().changed());
    contents.clear();
    egraph.for_each(f_table, |func_row| {
        assert!(!func_row.subsumed);
        contents.push((
            egraph.base_values().unwrap::<i64>(func_row.vals[0]),
            egraph.base_values().unwrap::<i64>(func_row.vals[1]),
        ));
    });
    contents.sort();
    assert_eq!(contents, vec![(1, 1), (2, 7)]);

    // Third rule writes (f 1 3) (f 2 4)
    let rule3 = {
        let mut rb = egraph.new_rule("rule3", true);
        rb.set(f_table, &[value_1, value_3]);
        rb.set(f_table, &[value_2, value_4]);
        rb.build()
    };

    // Run the third rule and check state
    // Expected: (f 1 4) because 1 + (1 * 3) = 4
    // Expected: (f 2 29) because 1 + (7 * 4) = 29
    assert!(egraph.run_rules(&[rule3], None).unwrap().changed());
    contents.clear();
    egraph.for_each(f_table, |func_row| {
        assert!(!func_row.subsumed);
        contents.push((
            egraph.base_values().unwrap::<i64>(func_row.vals[0]),
            egraph.base_values().unwrap::<i64>(func_row.vals[1]),
        ));
    });
    contents.sort();
    assert_eq!(contents, vec![(1, 4), (2, 29)]);
}

#[test]
fn mergefn_nested_function() {
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();

    // Create a function g that will be used in the merge function for f
    let g_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "g".into(),
        can_subsume: true,
    });

    // Create a function f whose merge function is (g (g new new) (g old old))
    // This uses nested MergeFn::Function to build the complex merge function
    let f_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::Function(
            g_table,
            vec![
                MergeFn::Function(g_table, vec![MergeFn::New, MergeFn::New]),
                MergeFn::Function(g_table, vec![MergeFn::Old, MergeFn::Old]),
            ],
        ),
        name: "f".into(),
        can_subsume: true,
    });

    let value_1 = egraph.base_value_constant(1i64);
    let value_2 = egraph.base_value_constant(2i64);

    // Create an rhs-only rule that writes f values with fresh IDs
    // We'll run this rule multiple times and observe how the merge function works

    let write_rule = {
        let mut rb = egraph.new_rule("write_rule", true);
        rb.lookup(f_table, slice::from_ref(&value_1), String::new);
        rb.lookup(f_table, &[value_2], String::new);
        rb.build()
    };

    // Helper function to get all g-table entries
    let get_g_entries = |egraph: &EGraph| {
        let mut entries = Vec::new();
        egraph.for_each(g_table, |func_row| {
            assert!(!func_row.subsumed);
            entries.push((func_row.vals[0], func_row.vals[1], func_row.vals[2]));
        });
        entries.sort();
        entries
    };

    // Helper function to get all f-table entries
    let get_f_entries = |egraph: &EGraph| {
        let mut entries = Vec::new();
        egraph.for_each(f_table, |func_row| {
            assert!(!func_row.subsumed);
            entries.push((
                egraph.base_values().unwrap::<i64>(func_row.vals[0]),
                func_row.vals[1],
            ));
        });
        entries.sort();
        entries
    };

    // First run of the rule
    assert!(egraph.run_rules(&[write_rule], None).unwrap().changed());
    let f_entries_1 = get_f_entries(&egraph);
    let g_entries_1 = get_g_entries(&egraph);
    assert_eq!(f_entries_1.len(), 2);
    let base_1 = f_entries_1[0].1;
    let base_2 = f_entries_1[1].1;
    // After first run, there should be no g entries yet because no merging occurred
    assert_eq!(g_entries_1.len(), 0);

    let set_rule = {
        let mut rb = egraph.new_rule("iterate", true);
        rb.set(
            f_table,
            &[
                value_1,
                QueryEntry::Const {
                    val: base_2,
                    ty: ColumnTy::Id,
                },
            ],
        );
        rb.build()
    };

    // Second run of the rule - should trigger merging with previous values
    assert!(egraph.run_rules(&[set_rule], None).unwrap().changed());
    let f_entries_2 = get_f_entries(&egraph);
    let g_entries_2 = get_g_entries(&egraph);
    assert_eq!(f_entries_2.len(), 2);
    // After second run, g table should have entries from the merge functions
    assert_eq!(g_entries_2.len(), 3);

    // Get the entry for (f 1)
    let new_base_1 = f_entries_2[0].1;
    // Find the first layer of g:
    let (mid_1, mid_2, _) = *g_entries_2
        .iter()
        .find(|(_, _, a)| *a == new_base_1)
        .unwrap();
    let (base_l1, base_l2, _) = *g_entries_2.iter().find(|(_, _, a)| *a == mid_1).unwrap();
    let (base_r1, base_r2, _) = *g_entries_2.iter().find(|(_, _, a)| *a == mid_2).unwrap();

    // The merge function for f is (g (g new new) (g old old))
    // new here should have been base_2, old should have been base_1
    //
    // That means basel1 == basel2 == base_2, and baser1 == baser2 == base_1
    assert_eq!(base_l1, base_l2);
    assert_eq!(base_l1, base_2);
    assert_eq!(base_r1, base_r2);
    assert_eq!(base_r1, base_1);
}

#[test]
fn constrain_prims_simple() {
    // Take two functions, f and g. Fill f with (f 1) (f 2) (f 3), then filter for even numbers
    // when adding to 'g'. This should only add 2 to g.
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();
    let bool_base = egraph.base_values_mut().register_type::<bool>();
    let f_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "f".into(),
        can_subsume: false,
    });
    let g_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "g".into(),
        can_subsume: false,
    });

    let query_prim_invocations = Arc::new(AtomicUsize::new(0));
    let query_prim_invocations_clone = query_prim_invocations.clone();
    let is_even = egraph.register_external_func(Box::new(core_relations::make_external_func(
        move |state, vals| -> Option<Value> {
            let [a] = vals else {
                return None;
            };
            query_prim_invocations_clone.fetch_add(1, Ordering::Relaxed);
            let a_val = state.base_values().unwrap::<i64>(*a);
            let result: bool = a_val % 2 == 0;
            Some(state.base_values().get(result))
        },
    )));

    let value_1 = egraph.base_value_constant(1i64);
    let value_2 = egraph.base_value_constant(2i64);
    let value_3 = egraph.base_value_constant(3i64);
    let value_true = egraph.base_value_constant(true);
    let write_f = {
        let mut rb = egraph.new_rule("write_f", true);
        rb.lookup(f_table, &[value_1], String::new);
        rb.lookup(f_table, &[value_2], String::new);
        rb.lookup(f_table, &[value_3], String::new);
        rb.build()
    };

    let copy_to_g = {
        let mut rb = egraph.new_rule("copy_to_g", true);
        let val: QueryEntry = rb.new_var(ColumnTy::Base(int_base)).into();
        let id: QueryEntry = rb.new_var(ColumnTy::Id).into();
        rb.query_table(f_table, &[val.clone(), id.clone()], Some(false))
            .unwrap();
        rb.query_prim(
            is_even,
            &[val.clone(), value_true.clone()],
            ColumnTy::Base(bool_base),
        )
        .unwrap();
        rb.set(g_table, &[val, id]);
        rb.build()
    };
    let get_entries = |egraph: &EGraph, table: FunctionId| {
        let mut entries = Vec::new();
        egraph.for_each(table, |func_row| {
            assert!(!func_row.subsumed);
            entries.push((
                egraph.base_values().unwrap::<i64>(func_row.vals[0]),
                func_row.vals[1],
            ));
        });
        entries.sort();
        entries
    };

    assert!(get_entries(&egraph, f_table).is_empty());
    assert!(get_entries(&egraph, g_table).is_empty());
    egraph.run_rules(&[write_f], None).unwrap();
    let f = get_entries(&egraph, f_table);
    assert_eq!(f.len(), 3);
    egraph.run_rules(&[copy_to_g], None).unwrap();
    let invocations_after_first = query_prim_invocations.load(Ordering::Relaxed);
    assert!(invocations_after_first > 0);
    assert!(!egraph.run_rules(&[copy_to_g], None).unwrap().changed());
    assert_eq!(
        query_prim_invocations.load(Ordering::Relaxed),
        invocations_after_first
    );
    let g = get_entries(&egraph, g_table);
    assert_eq!(g.len(), 1);
    assert_eq!(g[0], f[1])
}

#[test]
fn constrain_prims_abstract() {
    // Take two functions, f and g. Fill f with (f -1) (f 0) (f 1), then filter for numbers where
    // (neg x) = (abs x) when adding to 'g'. This adds only -1 and 0 to g
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();
    let f_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "f".into(),
        can_subsume: false,
    });
    let g_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "g".into(),
        can_subsume: false,
    });

    let neg = egraph.register_external_func(Box::new(core_relations::make_external_func(
        |state, vals| -> Option<Value> {
            let [a] = vals else {
                return None;
            };
            let a_val = state.base_values().unwrap::<i64>(*a);
            Some(state.base_values().get(-a_val))
        },
    )));
    let abs = egraph.register_external_func(Box::new(core_relations::make_external_func(
        |state, vals| -> Option<Value> {
            let [a] = vals else {
                return None;
            };
            let a_val = state.base_values().unwrap::<i64>(*a);
            Some(state.base_values().get(a_val.abs()))
        },
    )));

    let value_n1 = egraph.base_value_constant(-1i64);
    let value_0 = egraph.base_value_constant(0i64);
    let value_1 = egraph.base_value_constant(1i64);
    let write_f = {
        let mut rb = egraph.new_rule("write_f", true);
        rb.lookup(f_table, &[value_n1], String::new);
        rb.lookup(f_table, &[value_0], String::new);
        rb.lookup(f_table, &[value_1], String::new);
        rb.build()
    };

    let copy_to_g = {
        let mut rb = egraph.new_rule("copy_to_g", true);
        let val: QueryEntry = rb.new_var(ColumnTy::Base(int_base)).into();
        let id: QueryEntry = rb.new_var(ColumnTy::Id).into();
        let negval: QueryEntry = rb.new_var(ColumnTy::Base(int_base)).into();
        rb.query_table(f_table, &[val.clone(), id.clone()], Some(false))
            .unwrap();
        rb.query_prim(
            neg,
            &[val.clone(), negval.clone()],
            ColumnTy::Base(int_base),
        )
        .unwrap();
        rb.query_prim(
            abs,
            &[val.clone(), negval.clone()],
            ColumnTy::Base(int_base),
        )
        .unwrap();
        rb.set(g_table, &[val.clone(), id.clone()]);
        rb.build()
    };
    let get_entries = |egraph: &EGraph, table: FunctionId| {
        let mut entries = Vec::new();
        egraph.for_each(table, |func_row| {
            assert!(!func_row.subsumed);
            entries.push((
                egraph.base_values().unwrap::<i64>(func_row.vals[0]),
                func_row.vals[1],
            ));
        });
        entries.sort();
        entries
    };

    assert!(get_entries(&egraph, f_table).is_empty());
    assert!(get_entries(&egraph, g_table).is_empty());
    egraph.run_rules(&[write_f], None).unwrap();
    let f = get_entries(&egraph, f_table);
    assert_eq!(f.len(), 3);
    egraph.run_rules(&[copy_to_g], None).unwrap();
    let g = get_entries(&egraph, g_table);
    assert_eq!(g.len(), 2);
    assert_eq!(g, f[0..2])
}

#[test]
fn basic_subsumption() {
    // fill (f 1) (f 2). Subsume (f 3) (f 2). Copy (f to g). Should only see (g 1)

    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();
    let f_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "f".into(),
        can_subsume: true,
    });
    let g_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "g".into(),
        can_subsume: false,
    });

    let value_1 = egraph.base_value_constant(1i64);
    let value_2 = egraph.base_value_constant(2i64);
    let value_3 = egraph.base_value_constant(3i64);
    let write_f = {
        let mut rb = egraph.new_rule("write_f", true);
        rb.lookup(f_table, slice::from_ref(&value_1), String::new);
        rb.lookup(f_table, slice::from_ref(&value_2), String::new);
        rb.build()
    };

    let subsume_f = {
        let mut rb = egraph.new_rule("write_f", true);
        rb.subsume(f_table, slice::from_ref(&value_2));
        rb.subsume(f_table, slice::from_ref(&value_3));
        rb.build()
    };

    let copy_to_g = {
        let mut rb = egraph.new_rule("copy_to_g", true);
        let val: QueryEntry = rb.new_var(ColumnTy::Base(int_base)).into();
        let id: QueryEntry = rb.new_var(ColumnTy::Id).into();
        rb.query_table(f_table, &[val.clone(), id.clone()], Some(false))
            .unwrap();
        rb.set(g_table, &[val, id]);
        rb.build()
    };
    let get_entries = |egraph: &EGraph, table: FunctionId| {
        let mut entries = Vec::new();
        let mut num_subsumed = 0;
        egraph.for_each(table, |func_row| {
            entries.push((
                egraph.base_values().unwrap::<i64>(func_row.vals[0]),
                func_row.vals[1],
            ));
            if func_row.subsumed {
                num_subsumed += 1;
            }
        });
        entries.sort();
        (entries, num_subsumed)
    };

    assert!(get_entries(&egraph, f_table).0.is_empty());
    assert!(get_entries(&egraph, g_table).0.is_empty());
    egraph.run_rules(&[write_f], None).unwrap();
    let f = get_entries(&egraph, f_table);
    assert_eq!((f.0.len(), f.1), (2, 0));
    assert_eq!(f.0.iter().map(|(x, _)| *x).collect::<Vec<_>>(), vec![1, 2]);
    egraph.run_rules(&[subsume_f], None).unwrap();
    let f = get_entries(&egraph, f_table);
    assert_eq!((f.0.len(), f.1), (3, 2));
    assert_eq!(
        f.0.iter().map(|(x, _)| *x).collect::<Vec<_>>(),
        vec![1, 2, 3]
    );
    egraph.run_rules(&[copy_to_g], None).unwrap();
    let g = get_entries(&egraph, g_table);
    assert_eq!((g.0.len(), g.1), (1, 0));
    assert_eq!(g.0[0], f.0[0])
}

#[test]
fn lookup_failure_panics() {
    let mut egraph = EGraph::default();
    let f = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::Fail,
        merge: MergeFn::UnionId,
        name: "test".into(),
        can_subsume: false,
    });

    let to_entry = |val: u32| QueryEntry::Const {
        val: Value::new(val),
        ty: ColumnTy::Id,
    };

    let value_1 = to_entry(1);
    let value_2 = to_entry(2);
    let value_3 = to_entry(3);
    let write_f = {
        let mut rb = egraph.new_rule("write_f", true);
        rb.set(f, &[value_1.clone(), value_1.clone()]);
        rb.set(f, &[value_2.clone(), value_2.clone()]);
        rb.build()
    };
    egraph.run_rules(&[write_f], None).unwrap();

    let lookup_success = {
        let mut rb = egraph.new_rule("lookup_success", true);
        rb.lookup(f, slice::from_ref(&value_1), String::new);
        rb.build()
    };
    egraph.run_rules(&[lookup_success], None).unwrap();

    let lookup_failure = {
        let mut rb = egraph.new_rule("lookup_fail", true);
        rb.lookup(f, slice::from_ref(&value_3), String::new);
        rb.build()
    };
    egraph.run_rules(&[lookup_failure], None).err().unwrap();
}

#[test]
fn primitive_failure_panics() {
    let mut egraph = EGraph::default();
    let _int_base = egraph.base_values_mut().register_type::<i64>();
    let unit_base = egraph.base_values_mut().register_type::<()>();

    let value_1 = egraph.base_value_constant(1i64);
    let value_2 = egraph.base_value_constant(2i64);

    let assert_odd = egraph.register_external_func(Box::new(core_relations::make_external_func(
        |state, vals| -> Option<Value> {
            let [a] = vals else {
                return None;
            };
            let a_val = state.base_values().unwrap::<i64>(*a);
            if a_val % 2 == 1 {
                Some(state.base_values().get(()))
            } else {
                None
            }
        },
    )));

    let assert_odd_rule = {
        let mut rb = egraph.new_rule("assert_odd", true);
        rb.call_external_func(
            assert_odd,
            slice::from_ref(&value_1),
            ColumnTy::Base(unit_base),
            || "".to_string(),
        );
        rb.call_external_func(
            assert_odd,
            slice::from_ref(&value_2),
            ColumnTy::Base(unit_base),
            || "".to_string(),
        );
        rb.build()
    };

    egraph.run_rules(&[assert_odd_rule], None).err().unwrap();
}

#[test]
fn action_panic_rebuilds_before_returning() {
    let mut egraph = EGraph::default();
    let facts = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: MergeFn::UnionId,
        name: "facts".into(),
        can_subsume: false,
    });
    let a = egraph.fresh_id();
    let b = egraph.fresh_id();
    egraph.add_values([(facts, vec![a, a]), (facts, vec![b, b])]);
    assert_eq!(egraph.table_size(facts), 2);

    let id = |val| QueryEntry::Const {
        val,
        ty: ColumnTy::Id,
    };
    let union_then_panic = {
        let mut rb = egraph.new_rule("union_then_panic", true);
        rb.union(id(a), id(b));
        rb.panic("boom".to_string());
        rb.build()
    };

    let error = egraph.run_rules(&[union_then_panic], None).unwrap_err();
    assert_eq!(error.to_string(), "Panic: boom");
    assert_eq!(
        egraph.get_canon_repr(a, ColumnTy::Id),
        egraph.get_canon_repr(b, ColumnTy::Id)
    );
    assert_eq!(
        egraph.table_size(facts),
        1,
        "effects before the panic should be canonicalized before Err"
    );

    let c = egraph.fresh_id();
    let continue_after_error = {
        let mut rb = egraph.new_rule("continue_after_error", true);
        rb.union(id(a), id(c));
        rb.build()
    };
    egraph.run_rules(&[continue_after_error], None).unwrap();
    assert_eq!(
        egraph.get_canon_repr(a, ColumnTy::Id),
        egraph.get_canon_repr(c, ColumnTy::Id),
        "the egraph should remain usable after the action error"
    );
}

#[test]
fn panic_functions_trigger_early_stop() {
    let db = core_relations::Database::default();

    let channel: crate::SideChannel<String> = Default::default();
    let panic_fn = super::Panic("panic".to_string(), channel.clone());
    let stopped = db.with_execution_state(None, |state| {
        assert!(!state.should_stop());
        let res = core_relations::ExternalFunction::invoke(&panic_fn, state, &[Value::new(1)]);
        assert!(res.is_none());
        state.should_stop()
    });
    assert!(stopped);
    assert_eq!(channel.lock().unwrap().as_deref(), Some("panic"));

    let channel: crate::SideChannel<String> = Default::default();
    let lazy = Lazy::new(|| "lazy panic".to_string());
    let panic_fn = super::LazyPanic(Arc::new(lazy), channel.clone());
    let stopped = db.with_execution_state(None, |state| {
        assert!(!state.should_stop());
        let res = core_relations::ExternalFunction::invoke(&panic_fn, state, &[]);
        assert!(res.is_none());
        state.should_stop()
    });
    assert!(stopped);
    assert_eq!(channel.lock().unwrap().as_deref(), Some("lazy panic"));
}

#[test]
fn self_referential_merge_union_find() {
    // A merge that writes back into its OWN table, like the term encoding's single-table UF. On a
    // conflicting parent it keeps the smaller endpoint and re-inserts the displaced edge into
    // itself. Exercises `peek_next_function_id`, `MergeFn::TableInsert` into self, `Seq`, and the
    // e-graph's self-write buffer pre-seed.
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();
    let min_func = egraph.register_external_func(Box::new(core_relations::make_external_func(
        |state, vals| {
            let [a, b] = vals else { return None };
            let (a, b) = (
                state.base_values().unwrap::<i64>(*a),
                state.base_values().unwrap::<i64>(*b),
            );
            Some(state.base_values().get::<i64>(a.min(b)))
        },
    )));
    let max_func = egraph.register_external_func(Box::new(core_relations::make_external_func(
        |state, vals| {
            let [a, b] = vals else { return None };
            let (a, b) = (
                state.base_values().unwrap::<i64>(*a),
                state.base_values().unwrap::<i64>(*b),
            );
            Some(state.base_values().get::<i64>(a.max(b)))
        },
    )));

    // The merge references the table itself, so reserve its id before creating it.
    let uf_id = egraph.peek_next_function_id();
    let min = || MergeFn::Primitive(min_func, vec![MergeFn::Old, MergeFn::New]);
    let max = MergeFn::Primitive(max_func, vec![MergeFn::Old, MergeFn::New]);
    let uf = egraph.add_table(FunctionConfig {
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Base(int_base)],
        n_vals: 1,
        // The single parent column is the identity: the guard skips the merge when the parent is
        // unchanged, so the body stages the displaced edge unconditionally.
        n_identity_vals: Some(1),
        default: DefaultVal::Fail,
        merge: MergeFn::Block {
            actions: vec![MergeAction::Set(uf_id, vec![max, min()])],
            result: Box::new(min()),
        },
        name: "uf".into(),
        can_subsume: false,
    });
    assert_eq!(uf, uf_id, "peeked id must match the id add_table assigns");

    let set_parent = |egraph: &mut EGraph, child: i64, parent: i64| {
        let (c, p) = (
            egraph.base_value_constant(child),
            egraph.base_value_constant(parent),
        );
        let r = {
            let mut rb = egraph.new_rule("set", true);
            rb.set(uf, &[c, p]);
            rb.build()
        };
        egraph.run_rules(&[r], None).unwrap();
    };
    let parent_of = |egraph: &mut EGraph, node: i64| -> Option<i64> {
        let k = egraph.base_values_mut().get(node);
        egraph
            .lookup_id(uf, &[k])
            .map(|v| egraph.base_values().unwrap::<i64>(v))
    };

    // uf[5] = 3, then uf[5] = 1: the conflict keeps min (1) and re-inserts the displaced edge 3->1.
    set_parent(&mut egraph, 5, 3);
    set_parent(&mut egraph, 5, 1);
    assert_eq!(
        parent_of(&mut egraph, 5),
        Some(1),
        "5 points at the smaller endpoint"
    );
    assert_eq!(
        parent_of(&mut egraph, 3),
        Some(1),
        "displaced edge 3->1 must be re-inserted into uf itself (self-write)"
    );

    // A conflict where the new parent is larger: uf[3] = 2 keeps 1 and re-inserts 2->1.
    set_parent(&mut egraph, 3, 2);
    assert_eq!(parent_of(&mut egraph, 3), Some(1));
    assert_eq!(
        parent_of(&mut egraph, 2),
        Some(1),
        "displaced edge 2->1 re-inserted"
    );
}

#[test]
fn identity_column_guard_skips_payload_only_conflicts() {
    // A function with an identity column (col 0) and a payload column (col 1): a collision that
    // changes only the payload keeps the existing row (the merge is skipped); a collision that
    // changes the identity runs the merge.
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();
    let f = egraph.add_table(FunctionConfig {
        schema: vec![
            ColumnTy::Base(int_base), // key
            ColumnTy::Base(int_base), // value col 0 (identity)
            ColumnTy::Base(int_base), // value col 1 (payload)
        ],
        n_vals: 2,
        // col 0 is identity, col 1 is payload.
        n_identity_vals: Some(1),
        default: DefaultVal::Fail,
        // On a real (identity) conflict, take the new row.
        merge: MergeFn::Columns(vec![MergeFn::NewCol(0), MergeFn::NewCol(1)]),
        name: "f".into(),
        can_subsume: false,
    });

    let set = |egraph: &mut EGraph, a: i64, b: i64| {
        let (k, va, vb) = (
            egraph.base_value_constant(1i64),
            egraph.base_value_constant(a),
            egraph.base_value_constant(b),
        );
        let r = {
            let mut rb = egraph.new_rule("s", true);
            rb.set(f, &[k, va, vb]);
            rb.build()
        };
        egraph.run_rules(&[r], None).unwrap();
    };
    let read_row = |egraph: &EGraph| -> (i64, i64) {
        let mut out = None;
        egraph.for_each(f, |row| {
            out = Some((
                egraph.base_values().unwrap::<i64>(row.vals[1]),
                egraph.base_values().unwrap::<i64>(row.vals[2]),
            ));
        });
        out.unwrap()
    };

    set(&mut egraph, 10, 100);
    set(&mut egraph, 10, 200); // identity (10) unchanged -> keep old, payload stays 100
    assert_eq!(
        read_row(&egraph),
        (10, 100),
        "payload-only change should keep the existing row"
    );
    set(&mut egraph, 20, 300); // identity 10 -> 20 -> merge runs, takes new
    assert_eq!(
        read_row(&egraph),
        (20, 300),
        "an identity change should run the merge"
    );
}

#[test]
fn tuple_subsume_preserves_all_outputs() {
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();
    let f = egraph.add_table(FunctionConfig {
        schema: vec![
            ColumnTy::Base(int_base),
            ColumnTy::Base(int_base),
            ColumnTy::Base(int_base),
        ],
        n_vals: 2,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::Columns(vec![MergeFn::OldCol(0), MergeFn::OldCol(1)]),
        name: "tuple-subsume".into(),
        can_subsume: true,
    });
    let key = egraph.base_values_mut().get(1_i64);
    let first = egraph.base_values_mut().get(10_i64);
    let second = egraph.base_values_mut().get(20_i64);
    let action = TableAction::new(&egraph, f);
    egraph.db.with_execution_state(None, |state| {
        action.insert(state, [key, first, second].into_iter())
    });
    egraph.flush_updates();
    egraph
        .db
        .with_execution_state(None, |state| action.subsume(state, std::iter::once(key)));
    egraph.flush_updates();

    let mut rows = Vec::new();
    egraph.for_each(f, |row| rows.push((row.vals.to_vec(), row.subsumed)));
    assert_eq!(rows, vec![(vec![key, first, second], true)]);
}

const _: () = {
    const fn assert_send<T: Send>() {}
    assert_send::<EGraph>()
};
