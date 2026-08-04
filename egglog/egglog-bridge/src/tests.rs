use std::{
    any::TypeId,
    fmt::Debug,
    hash::Hash,
    iter, slice,
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
    thread,
};

use crate::core_relations;
use crate::core_relations::{
    ContainerValue, ExternalFunctionId, SortedWritesTable, Value, ValueRebuilder,
    make_external_func,
};
use crate::numeric_id::NumericId;
use log::debug;
use num_rational::Rational64;
use once_cell::sync::Lazy;

use crate::{
    ColumnTy, DefaultVal, EGraph, FunctionConfig, FunctionId, FunctionReplaySpec,
    GroundedRuleBinding, GroundedRuleRun, MergeAction, MergeBindingId, MergeExpr, MergeInputSide,
    MergePrimitiveOrigin, MergeProgram, MergeValueColumn, QueryEntry, ReplayCallSpec,
    ReplayLiteral, ReplayOpId, ReplaySortId, ReplayTableKind, SourceInputRow, TableAction,
    TraceLifecycleError, Variable, add_expressions, define_rule,
};

fn prior(column: usize) -> MergeExpr {
    MergeExpr::Input {
        side: MergeInputSide::Prior,
        column: MergeValueColumn::new(column),
    }
}

fn incoming(column: usize) -> MergeExpr {
    MergeExpr::Input {
        side: MergeInputSide::Incoming,
        column: MergeValueColumn::new(column),
    }
}

fn assert_equal(column: usize) -> MergeExpr {
    MergeExpr::AssertEq {
        column: MergeValueColumn::new(column),
    }
}

fn union_id(column: usize) -> MergeExpr {
    MergeExpr::UnionId {
        column: MergeValueColumn::new(column),
    }
}

fn primitive(
    function: ExternalFunctionId,
    arguments: Vec<MergeExpr>,
    origin: MergePrimitiveOrigin,
) -> MergeExpr {
    MergeExpr::Primitive {
        function,
        arguments,
        origin,
    }
}

fn function(function: FunctionId, arguments: Vec<MergeExpr>) -> MergeExpr {
    MergeExpr::Function {
        function,
        arguments,
    }
}

fn single_merge(result: MergeExpr) -> MergeProgram {
    MergeProgram {
        actions: Vec::new(),
        results: vec![result],
    }
}

#[test]
fn only_explicit_input_choice_primitives_receive_structural_selector() {
    let function = ExternalFunctionId::new_const(0);
    let generic = primitive(
        function,
        vec![prior(0), incoming(0)],
        MergePrimitiveOrigin::Opaque,
    );
    assert_eq!(
        generic.structural_origin_selector(1),
        core_relations::MergeOriginSelector::Unsupported,
        "a generic binary primitive such as addition must fail before its callback"
    );
    let choice = primitive(
        function,
        vec![prior(0), incoming(0)],
        MergePrimitiveOrigin::SelectsArgument,
    );
    assert_eq!(
        choice.structural_origin_selector(1),
        core_relations::MergeOriginSelector::PriorOrIncoming {
            incoming_column: 1,
            prior_column: 1,
        }
    );
}

#[test]
#[should_panic(expected = "declares let binding 1, expected 0")]
fn merge_rejects_out_of_order_binding() {
    let mut egraph = EGraph::default();
    egraph.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeProgram {
            actions: vec![MergeAction::Let {
                binding: MergeBindingId::new(1),
                value: prior(0),
            }],
            results: vec![prior(0)],
        },
        name: "out-of-order-binding".into(),
        can_subsume: false,
    });
}

#[test]
#[should_panic(expected = "references let binding 0 before it is bound")]
fn merge_rejects_unbound_binding_reference() {
    let mut egraph = EGraph::default();
    egraph.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: single_merge(MergeExpr::Binding(MergeBindingId::new(0))),
        name: "unbound-binding".into(),
        can_subsume: false,
    });
}

#[test]
#[should_panic(expected = "has 2 output columns; merge function calls require exactly one")]
fn merge_rejects_tuple_output_function_call() {
    let mut egraph = EGraph::default();
    let target = egraph.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        n_vals: 2,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeProgram {
            actions: Vec::new(),
            results: vec![prior(0), prior(1)],
        },
        name: "tuple-target".into(),
        can_subsume: false,
    });
    egraph.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: single_merge(function(
            target,
            vec![MergeExpr::Const(Value::from_usize(7))],
        )),
        name: "invalid-function-call".into(),
        can_subsume: false,
    });
}

#[test]
#[should_panic(expected = "with 0 key arguments, expected 1")]
fn merge_rejects_function_call_with_wrong_key_arity() {
    let mut egraph = EGraph::default();
    let target = egraph.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: single_merge(prior(0)),
        name: "target".into(),
        can_subsume: false,
    });
    egraph.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: single_merge(function(target, Vec::new())),
        name: "invalid-function-call".into(),
        can_subsume: false,
    });
}

#[test]
fn trace_capture_rejects_parallel_bridge_activation() {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(2)
        .build()
        .unwrap();
    pool.install(|| {
        let mut egraph = EGraph::default();
        let error = egraph.enable_trace().unwrap_err();
        assert!(error.to_string().contains(
            "trace capture requires a one-thread Rayon pool; parallel trace capture is unsupported"
        ));
    });
}

#[test]
fn trace_finalization_reports_disabled_capture() {
    let mut egraph = EGraph::default();
    assert_eq!(
        egraph.finalize_trace_wave(),
        Err(TraceLifecycleError::CaptureDisabled)
    );
}

#[test]
fn conflicting_source_constructor_container_type_is_rejected_before_staging() {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .build()
        .unwrap();
    pool.install(|| {
        let mut egraph = EGraph::default();
        egraph.enable_trace().unwrap();
        let int_base = egraph.base_values_mut().register_type::<i64>();
        let child_sort = ReplaySortId::new(0);
        let container_sort = ReplaySortId::new(1);
        let constructor = egraph.add_table(FunctionConfig {
            n_vals: 1,
            n_identity_vals: None,
            schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
            default: DefaultVal::FreshId,
            merge: single_merge(union_id(0)),
            name: "container-constructor".into(),
            can_subsume: false,
        });
        egraph
            .register_container_replay_sort(
                container_sort,
                TypeId::of::<VecContainer>(),
                &[child_sort],
            )
            .unwrap();
        let replay = |container_type, table_kind| {
            FunctionReplaySpec::new(
                [child_sort, container_sort],
                Some(
                    ReplayCallSpec::new(container_sort, ReplayOpId::new(0), [child_sort])
                        .with_container_type(container_type),
                ),
            )
            .with_table_kind(table_kind)
        };
        let id_counter_before = egraph.db.read_counter(egraph.id_counter);

        let error = egraph
            .register_function_replay(
                constructor,
                replay(TypeId::of::<Rational64>(), ReplayTableKind::ValueFunction),
            )
            .unwrap_err();
        assert_eq!(
            error.to_string(),
            "replay sort has conflicting physical container types"
        );
        assert_eq!(egraph.table_size(constructor), 0);
        assert_eq!(
            egraph.db.read_counter(egraph.id_counter),
            id_counter_before,
            "rejected replay metadata must not allocate a constructor result"
        );

        let child_value = egraph.base_values_mut().get(7_i64);
        let child_term = egraph
            .intern_replay_literal(child_sort, ReplayLiteral::I64(7), child_value)
            .unwrap();
        let row = SourceInputRow::new(
            core_relations::SourceRef::Synthetic(0),
            [child_value],
            [child_term],
        );
        let error = egraph
            .stage_source_input_rows(constructor, std::slice::from_ref(&row))
            .unwrap_err();
        assert!(error.to_string().contains("has no trace replay metadata"));
        assert_eq!(egraph.table_size(constructor), 0);
        assert_eq!(
            egraph.db.read_counter(egraph.id_counter),
            id_counter_before,
            "failed registration must leave source staging mutation-free"
        );
        assert!(
            !egraph.flush_updates(),
            "failed source staging must not leave a queued native row"
        );
        egraph
            .with_trace_view(|view| {
                let totals = view.totals();
                assert_eq!(totals.facts, 0);
                assert_eq!(totals.applied_equalities, 0);
                assert_eq!(totals.removals, 0);
                Ok(())
            })
            .unwrap();

        egraph
            .register_function_replay(
                constructor,
                replay(
                    TypeId::of::<VecContainer>(),
                    ReplayTableKind::PresenceRelation,
                ),
            )
            .unwrap();
        let error = egraph
            .register_function_replay(
                constructor,
                FunctionReplaySpec::new([child_sort, container_sort], None)
                    .with_table_kind(ReplayTableKind::PresenceRelation),
            )
            .unwrap_err();
        assert_eq!(
            error.to_string(),
            "function `container-constructor` already has different trace replay metadata"
        );
        egraph.stage_source_input_rows(constructor, &[row]).unwrap();
        assert_eq!(
            egraph.table_size(constructor),
            0,
            "source staging must not flush implicitly"
        );
        assert!(egraph.flush_updates());
        assert_eq!(egraph.table_size(constructor), 1);
        let table = egraph.funcs[constructor].table;
        egraph
            .with_trace_view(|view| {
                assert_eq!(
                    view.table_schema(table)?.kind,
                    ReplayTableKind::PresenceRelation,
                    "constructor source shape and replay table kind must remain independent"
                );
                Ok(())
            })
            .unwrap();
    });
}

#[test]
fn source_constructor_replay_rejects_tuple_outputs_before_staging() {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .build()
        .unwrap();
    pool.install(|| {
        let mut egraph = EGraph::default();
        egraph.enable_trace().unwrap();
        let int_base = egraph.base_values_mut().register_type::<i64>();
        let constructor = egraph.add_table(FunctionConfig {
            n_vals: 2,
            n_identity_vals: None,
            schema: vec![ColumnTy::Base(int_base), ColumnTy::Id, ColumnTy::Id],
            default: DefaultVal::FreshId,
            merge: MergeProgram {
                actions: Vec::new(),
                results: vec![union_id(0), union_id(1)],
            },
            name: "tuple-constructor".into(),
            can_subsume: false,
        });
        let child_sort = ReplaySortId::new(0);
        let output_sort = ReplaySortId::new(1);
        let error = egraph
            .register_function_replay(
                constructor,
                FunctionReplaySpec::new(
                    [child_sort, output_sort, output_sort],
                    Some(ReplayCallSpec::new(
                        output_sort,
                        ReplayOpId::new(0),
                        [child_sort],
                    )),
                ),
            )
            .unwrap_err();
        assert_eq!(
            error.to_string(),
            "function `tuple-constructor` has 2 outputs but constructor source replay requires exactly one"
        );
        assert_eq!(egraph.table_size(constructor), 0);
        assert_eq!(egraph.db.read_counter(egraph.id_counter), 0);
    });
}

#[test]
fn trace_wave_rejects_decreasing_stamp_without_panicking() {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .build()
        .unwrap();
    pool.install(|| {
        let mut egraph = EGraph::default();
        egraph.enable_trace().unwrap();
        egraph.set_trace_wave(2).unwrap();
        let error = egraph.set_trace_wave(1).unwrap_err();
        assert_eq!(error, TraceLifecycleError::WaveRegression);
    });
}

#[test]
fn trace_capture_rejects_unsupported_merge_before_table_allocation() {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .build()
        .unwrap();
    pool.install(|| {
        let mut egraph = EGraph::default();
        egraph.enable_trace().unwrap();
        let constructor = egraph.add_table(FunctionConfig {
            n_vals: 1,
            n_identity_vals: None,
            schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
            default: DefaultVal::FreshId,
            merge: single_merge(union_id(0)),
            name: "constructor".into(),
            can_subsume: false,
        });
        let next_function = egraph.peek_next_function_id();
        let next_table = egraph.db.next_table_id();

        let error = egraph
            .try_add_table(FunctionConfig {
                n_vals: 1,
                n_identity_vals: None,
                schema: vec![ColumnTy::Id, ColumnTy::Id],
                default: DefaultVal::Fail,
                merge: single_merge(function(constructor, vec![prior(0), incoming(0)])),
                name: "unsupported-merge".into(),
                can_subsume: false,
            })
            .unwrap_err();

        assert!(
            error
                .to_string()
                .contains("merge reached an unsupported structural result expression")
        );
        assert_eq!(egraph.peek_next_function_id(), next_function);
        assert_eq!(egraph.db.next_table_id(), next_table);
        assert!(
            egraph
                .action_registry()
                .read()
                .unwrap()
                .lookup_table("unsupported-merge")
                .is_none()
        );
    });
}

#[test]
fn grounded_wave_point_probes_every_match_before_running_any_head_without_planning() {
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();
    let unit_base = egraph.base_values_mut().register_type::<()>();
    let input = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "grounded-input".into(),
        can_subsume: false,
    });
    let zero = egraph.base_values_mut().get(0i64);
    let one = egraph.base_values_mut().get(1i64);
    let missing = egraph.base_values_mut().get(2i64);
    let zero_id = egraph.add_term(input, &[zero]);
    let one_id = egraph.add_term(input, &[one]);

    let head_calls = Arc::new(AtomicUsize::new(0));
    let calls = Arc::clone(&head_calls);
    let observe_head =
        egraph.register_external_func(Box::new(make_external_func(move |state, args| {
            assert!(args.is_empty());
            calls.fetch_add(1, Ordering::Relaxed);
            Some(state.base_values().get(()))
        })));
    let (rule, value, id) = {
        let mut builder = egraph.new_rule("grounded", true);
        let value = builder.new_var_named(ColumnTy::Base(int_base), "value");
        let QueryEntry::Var(value_var) = value.clone() else {
            unreachable!()
        };
        let id: QueryEntry = builder.new_var_named(ColumnTy::Id, "id");
        let QueryEntry::Var(id_var) = id.clone() else {
            unreachable!()
        };
        builder
            .query_table(input, &[value, id], Some(false))
            .unwrap();
        builder.finish_query();
        builder.call_external_func(observe_head, &[], ColumnTy::Base(unit_base), || {
            "head call failed".into()
        });
        (builder.build(), value_var, id_var)
    };

    let firing = |invocation_ordinal, value_arg, id_arg| GroundedRuleRun {
        invocation_ordinal,
        rule,
        bindings: vec![
            GroundedRuleBinding {
                variable: value.id,
                ty: ColumnTy::Base(int_base),
                value: value_arg,
            },
            GroundedRuleBinding {
                variable: id.id,
                ty: ColumnTy::Id,
                value: id_arg,
            },
        ]
        .into_boxed_slice(),
    };

    assert!(!egraph.rule_has_cached_plan(rule));
    let error = egraph
        .run_grounded_wave(&[firing(11, one, one_id), firing(10, zero, zero_id)])
        .unwrap_err();
    assert_eq!(
        error.to_string(),
        "grounded invocation ordinals must be strictly increasing; observed 11 followed by 10"
    );
    assert_eq!(head_calls.load(Ordering::Relaxed), 0);

    let error = egraph
        .run_grounded_wave(&[firing(10, zero, zero_id), firing(11, missing, one_id)])
        .unwrap_err();
    assert!(error.to_string().contains("premise"));
    assert_eq!(head_calls.load(Ordering::Relaxed), 0);
    assert!(!egraph.rule_has_cached_plan(rule));

    egraph
        .run_grounded_wave(&[firing(12, zero, zero_id), firing(13, one, one_id)])
        .unwrap();
    assert_eq!(head_calls.load(Ordering::Relaxed), 2);
    assert!(!egraph.rule_has_cached_plan(rule));

    // Grounded replay neither consumes the ordinary seminaive epoch nor
    // constructs a plan. The later planned run compiles its ordinary tape
    // independently and therefore sees both original rows exactly once.
    egraph.run_rules(&[rule]).unwrap();
    assert_eq!(head_calls.load(Ordering::Relaxed), 4);
    assert!(egraph.rule_has_cached_plan(rule));
}

#[test]
fn grounded_wave_uses_one_common_prestate_and_reports_committed_matches() {
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();
    let input = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "grounded-delete-input".into(),
        can_subsume: false,
    });
    let zero = egraph.base_values_mut().get(0i64);
    let one = egraph.base_values_mut().get(1i64);
    let zero_id = egraph.add_term(input, &[zero]);
    let one_id = egraph.add_term(input, &[one]);
    let (rule, value, id, target) = {
        let mut builder = egraph.new_rule("grounded-delete", true);
        let value = builder.new_var_named(ColumnTy::Base(int_base), "value");
        let id = builder.new_var_named(ColumnTy::Id, "id");
        let target = builder.new_var_named(ColumnTy::Base(int_base), "target");
        builder
            .query_table(input, &[value.clone(), id.clone()], Some(false))
            .unwrap();
        builder.finish_query();
        builder.remove(input, std::slice::from_ref(&target));
        let QueryEntry::Var(value) = value else {
            unreachable!()
        };
        let QueryEntry::Var(id) = id else {
            unreachable!()
        };
        let QueryEntry::Var(target) = target else {
            unreachable!()
        };
        (builder.build(), value, id, target)
    };
    let firing = |invocation_ordinal, value_arg, id_arg, target_arg| GroundedRuleRun {
        invocation_ordinal,
        rule,
        bindings: vec![
            GroundedRuleBinding {
                variable: value.id,
                ty: ColumnTy::Base(int_base),
                value: value_arg,
            },
            GroundedRuleBinding {
                variable: id.id,
                ty: ColumnTy::Id,
                value: id_arg,
            },
            GroundedRuleBinding {
                variable: target.id,
                ty: ColumnTy::Base(int_base),
                value: target_arg,
            },
        ]
        .into_boxed_slice(),
    };

    // The first firing deletes the row required by the second firing. Both
    // premises must nevertheless be validated before either delete is staged.
    let report = egraph
        .run_grounded_wave(&[
            firing(20, zero, zero_id, one),
            firing(21, one, one_id, zero),
        ])
        .unwrap();
    assert!(report.changed());
    assert_eq!(report.rule_set_report.num_matches("grounded-delete"), 2);
    assert!(egraph.lookup_row(input, &[zero]).is_none());
    assert!(egraph.lookup_row(input, &[one]).is_none());
}

#[test]
fn grounded_wave_guard_failure_runs_no_head() {
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();
    let unit_base = egraph.base_values_mut().register_type::<()>();
    let input = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "grounded-guard-input".into(),
        can_subsume: false,
    });
    let zero = egraph.base_values_mut().get(0i64);
    let one = egraph.base_values_mut().get(1i64);
    let zero_id = egraph.add_term(input, &[zero]);
    let one_id = egraph.add_term(input, &[one]);
    let identity =
        egraph.register_external_func(Box::new(make_external_func(|_, args| Some(args[0]))));
    let head_calls = Arc::new(AtomicUsize::new(0));
    let calls = Arc::clone(&head_calls);
    let head = egraph.register_external_func(Box::new(make_external_func(move |state, _| {
        calls.fetch_add(1, Ordering::Relaxed);
        Some(state.base_values().get(()))
    })));
    let (rule, value, id) = {
        let mut builder = egraph.new_rule("grounded-guard", true);
        let value = builder.new_var_named(ColumnTy::Base(int_base), "value");
        let id = builder.new_var_named(ColumnTy::Id, "id");
        builder
            .query_table(input, &[value.clone(), id.clone()], Some(false))
            .unwrap();
        builder
            .query_prim(
                identity,
                &[
                    value.clone(),
                    QueryEntry::Const {
                        val: zero,
                        ty: ColumnTy::Base(int_base),
                    },
                ],
                ColumnTy::Base(int_base),
            )
            .unwrap();
        builder.finish_query();
        builder.call_external_func(head, &[], ColumnTy::Base(unit_base), || {
            "head failed".into()
        });
        let QueryEntry::Var(value) = value else {
            unreachable!()
        };
        let QueryEntry::Var(id) = id else {
            unreachable!()
        };
        (builder.build(), value, id)
    };
    let firing = |invocation_ordinal, value_arg, id_arg| GroundedRuleRun {
        invocation_ordinal,
        rule,
        bindings: vec![
            GroundedRuleBinding {
                variable: value.id,
                ty: ColumnTy::Base(int_base),
                value: value_arg,
            },
            GroundedRuleBinding {
                variable: id.id,
                ty: ColumnTy::Id,
                value: id_arg,
            },
        ]
        .into_boxed_slice(),
    };

    let error = egraph
        .run_grounded_wave(&[firing(30, zero, zero_id), firing(31, one, one_id)])
        .unwrap_err();
    assert!(error.to_string().contains("guard rejected"));
    assert_eq!(head_calls.load(Ordering::Relaxed), 0);
}

#[test]
fn grounded_wave_head_failure_aborts_earlier_staged_mutations() {
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();
    let input = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "grounded-atomic-input".into(),
        can_subsume: false,
    });
    let output = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "grounded-atomic-output".into(),
        can_subsume: false,
    });
    let key = egraph.base_values_mut().get(9i64);
    let id = egraph.add_term(input, &[key]);
    let build = |egraph: &mut EGraph, desc: &str, fail: bool| {
        let mut builder = egraph.new_rule(desc, true);
        let key_variable = builder.new_var_named(ColumnTy::Base(int_base), "key");
        let id_variable = builder.new_var_named(ColumnTy::Id, "id");
        builder
            .query_table(
                input,
                &[key_variable.clone(), id_variable.clone()],
                Some(false),
            )
            .unwrap();
        builder.finish_query();
        if fail {
            builder.panic("grounded head failed".into());
        } else {
            builder.set(output, &[key_variable.clone(), id_variable.clone()]);
        }
        let QueryEntry::Var(key_variable) = key_variable else {
            unreachable!()
        };
        let QueryEntry::Var(id_variable) = id_variable else {
            unreachable!()
        };
        (builder.build(), key_variable, id_variable)
    };
    let (write_rule, write_key, write_id) = build(&mut egraph, "grounded-write", false);
    let (fail_rule, fail_key, fail_id) = build(&mut egraph, "grounded-fail", true);
    let firing = |invocation_ordinal, rule, key_variable: &Variable, id_variable: &Variable| {
        GroundedRuleRun {
            invocation_ordinal,
            rule,
            bindings: vec![
                GroundedRuleBinding {
                    variable: key_variable.id,
                    ty: ColumnTy::Base(int_base),
                    value: key,
                },
                GroundedRuleBinding {
                    variable: id_variable.id,
                    ty: ColumnTy::Id,
                    value: id,
                },
            ]
            .into_boxed_slice(),
        }
    };

    let error = egraph
        .run_grounded_wave(&[
            firing(35, write_rule, &write_key, &write_id),
            firing(36, fail_rule, &fail_key, &fail_id),
        ])
        .unwrap_err();
    assert!(error.to_string().contains("grounded head failed"));
    assert!(egraph.lookup_row(output, &[key]).is_none());
}

#[test]
fn grounded_wave_resolves_proof_like_probe_dependencies_without_supplied_proof_vars() {
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();
    let unit_base = egraph.base_values_mut().register_type::<()>();
    let source = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "proof-source".into(),
        can_subsume: false,
    });
    let premise = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "proof-premise".into(),
        can_subsume: false,
    });
    let key = egraph.base_values_mut().get(7i64);
    let proof = egraph.add_term(source, &[key]);
    let conclusion = egraph.add_term(premise, &[proof]);
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let head = egraph.register_external_func(Box::new(make_external_func(move |state, args| {
        assert_eq!(args, &[conclusion]);
        observed.fetch_add(1, Ordering::Relaxed);
        Some(state.base_values().get(()))
    })));
    let (rule, key_variable) = {
        let mut builder = egraph.new_rule("proof-like-grounded", true);
        let key_variable = builder.new_var_named(ColumnTy::Base(int_base), "key");
        let proof_variable: QueryEntry = builder.new_var(ColumnTy::Id).into();
        let conclusion_variable: QueryEntry = builder.new_var(ColumnTy::Id).into();
        // Deliberately reverse producer order. The first key is an injected
        // proof variable that the later point probe will bind.
        builder
            .query_table(
                premise,
                &[proof_variable.clone(), conclusion_variable.clone()],
                Some(false),
            )
            .unwrap();
        builder
            .query_table(source, &[key_variable.clone(), proof_variable], Some(false))
            .unwrap();
        builder.finish_query();
        builder.call_external_func(
            head,
            std::slice::from_ref(&conclusion_variable),
            ColumnTy::Base(unit_base),
            || "proof head failed".into(),
        );
        let QueryEntry::Var(key_variable) = key_variable else {
            unreachable!()
        };
        (builder.build(), key_variable)
    };

    let report = egraph
        .run_grounded_wave(&[GroundedRuleRun {
            invocation_ordinal: 40,
            rule,
            bindings: vec![GroundedRuleBinding {
                variable: key_variable.id,
                ty: ColumnTy::Base(int_base),
                value: key,
            }]
            .into_boxed_slice(),
        }])
        .unwrap();
    assert!(matches!(
        report.rule_set_report.pre_merge,
        crate::PreMergeTiming::Split {
            search,
            apply,
            ..
        } if search.is_zero() && apply.is_zero()
    ));
    assert_eq!(calls.load(Ordering::Relaxed), 1);
}

#[test]
fn grounded_wave_computes_hidden_primitive_keys_before_point_probes() {
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();
    let unit_base = egraph.base_values_mut().register_type::<()>();
    let source = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "computed-key-source".into(),
        can_subsume: false,
    });
    let key = egraph.base_values_mut().get(7i64);
    let value = egraph.add_term(source, &[key]);
    let identity =
        egraph.register_external_func(Box::new(make_external_func(|_, args| Some(args[0]))));
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let head = egraph.register_external_func(Box::new(make_external_func(move |state, args| {
        assert_eq!(args, &[value]);
        observed.fetch_add(1, Ordering::Relaxed);
        Some(state.base_values().get(()))
    })));
    let (rule, seed_variable) = {
        let mut builder = egraph.new_rule("computed-key-grounded", true);
        let seed_variable = builder.new_var_named(ColumnTy::Base(int_base), "seed");
        let derived_variable: QueryEntry = builder.new_var(ColumnTy::Base(int_base)).into();
        let value_variable: QueryEntry = builder.new_var(ColumnTy::Id).into();
        builder
            .query_prim(
                identity,
                &[seed_variable.clone(), derived_variable.clone()],
                ColumnTy::Base(int_base),
            )
            .unwrap();
        builder
            .query_table(
                source,
                &[derived_variable, value_variable.clone()],
                Some(false),
            )
            .unwrap();
        builder.finish_query();
        builder.call_external_func(
            head,
            std::slice::from_ref(&value_variable),
            ColumnTy::Base(unit_base),
            || "computed-key head failed".into(),
        );
        let QueryEntry::Var(seed_variable) = seed_variable else {
            unreachable!()
        };
        (builder.build(), seed_variable)
    };

    egraph
        .run_grounded_wave(&[GroundedRuleRun {
            invocation_ordinal: 41,
            rule,
            bindings: vec![GroundedRuleBinding {
                variable: seed_variable.id,
                ty: ColumnTy::Base(int_base),
                value: key,
            }]
            .into_boxed_slice(),
        }])
        .unwrap();
    assert_eq!(calls.load(Ordering::Relaxed), 1);
}

#[test]
fn grounded_wave_handles_reverse_primitive_dependency_order() {
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();
    let unit_base = egraph.base_values_mut().register_type::<()>();
    let source = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "reverse-primitive-source".into(),
        can_subsume: false,
    });
    let seven = egraph.base_values_mut().get(7i64);
    let eight = egraph.base_values_mut().get(8i64);
    let value = egraph.add_term(source, &[seven]);
    let identity =
        egraph.register_external_func(Box::new(make_external_func(|_, args| Some(args[0]))));
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let head = egraph.register_external_func(Box::new(make_external_func(move |state, args| {
        assert_eq!(args, &[value]);
        observed.fetch_add(1, Ordering::Relaxed);
        Some(state.base_values().get(()))
    })));
    let (rule, seed, x) = {
        let mut builder = egraph.new_rule("reverse-primitive-grounded", true);
        let seed = builder.new_var_named(ColumnTy::Base(int_base), "seed");
        let x = builder.new_var_named(ColumnTy::Base(int_base), "x");
        let y = builder.new_var_named(ColumnTy::Base(int_base), "y");
        let value_var: QueryEntry = builder.new_var(ColumnTy::Id).into();
        // The consumer is deliberately compiled before x's producer.
        builder
            .query_prim(identity, &[x.clone(), y.clone()], ColumnTy::Base(int_base))
            .unwrap();
        builder
            .query_prim(
                identity,
                &[seed.clone(), x.clone()],
                ColumnTy::Base(int_base),
            )
            .unwrap();
        builder
            .query_table(source, &[y.clone(), value_var.clone()], Some(false))
            .unwrap();
        builder.finish_query();
        builder.call_external_func(
            head,
            std::slice::from_ref(&value_var),
            ColumnTy::Base(unit_base),
            || "reverse primitive head failed".into(),
        );
        let QueryEntry::Var(seed) = seed else {
            unreachable!()
        };
        let QueryEntry::Var(x) = x else {
            unreachable!()
        };
        (builder.build(), seed, x)
    };
    let binding = |variable: &Variable, value| GroundedRuleBinding {
        variable: variable.id,
        ty: ColumnTy::Base(int_base),
        value,
    };

    let error = egraph
        .run_grounded_wave(&[GroundedRuleRun {
            invocation_ordinal: 42,
            rule,
            bindings: vec![binding(&seed, seven), binding(&x, eight)].into_boxed_slice(),
        }])
        .unwrap_err();
    assert!(error.to_string().contains("guard rejected"));
    assert_eq!(calls.load(Ordering::Relaxed), 0);

    egraph
        .run_grounded_wave(&[GroundedRuleRun {
            invocation_ordinal: 43,
            rule,
            bindings: vec![binding(&seed, seven)].into_boxed_slice(),
        }])
        .unwrap();
    assert_eq!(calls.load(Ordering::Relaxed), 1);
}

#[test]
fn ordinary_planned_rule_keeps_primitive_result_constraint() {
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();
    let unit_base = egraph.base_values_mut().register_type::<()>();
    let source = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "ordinary-primitive-source".into(),
        can_subsume: false,
    });
    let seven = egraph.base_values_mut().get(7i64);
    let eight = egraph.base_values_mut().get(8i64);
    egraph.add_term(source, &[seven]);
    egraph.add_term(source, &[eight]);

    let identity =
        egraph.register_external_func(Box::new(make_external_func(|_, args| Some(args[0]))));
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let head = egraph.register_external_func(Box::new(make_external_func(move |state, _| {
        observed.fetch_add(1, Ordering::Relaxed);
        Some(state.base_values().get(()))
    })));
    let rule = {
        let mut builder = egraph.new_rule("ordinary-primitive-constraint", true);
        let derived: QueryEntry = builder.new_var(ColumnTy::Base(int_base)).into();
        let value: QueryEntry = builder.new_var(ColumnTy::Id).into();
        builder
            .query_prim(
                identity,
                &[
                    QueryEntry::Const {
                        val: seven,
                        ty: ColumnTy::Base(int_base),
                    },
                    derived.clone(),
                ],
                ColumnTy::Base(int_base),
            )
            .unwrap();
        builder
            .query_table(source, &[derived, value.clone()], Some(false))
            .unwrap();
        builder.finish_query();
        builder.call_external_func(
            head,
            std::slice::from_ref(&value),
            ColumnTy::Base(unit_base),
            || "ordinary primitive head failed".into(),
        );
        builder.build()
    };

    egraph.run_rules(&[rule]).unwrap();
    assert_eq!(calls.load(Ordering::Relaxed), 1);
}

#[test]
fn dropped_rule_builder_releases_panics() {
    let mut egraph = EGraph::default();
    let unit_type = egraph.base_values_mut().register_type::<()>();
    let register = |egraph: &mut EGraph| {
        egraph.register_external_func(Box::new(make_external_func(
            |state: &mut core_relations::ExecutionState<'_>, _args: &[Value]| {
                Some(state.base_values().get(()))
            },
        )))
    };
    let target = register(&mut egraph);
    let reusable = register(&mut egraph);
    egraph.free_external_func(reusable);

    let mut builder = egraph.new_rule("dropped", false);
    builder.call_external_func(target, &[], ColumnTy::Base(unit_type), || "failed".into());
    drop(builder);

    assert_eq!(register(&mut egraph), reusable);
    egraph.free_external_func(reusable);

    let mut builder = egraph.new_rule("dropped", false);
    assert_eq!(builder.new_panic("direct panic".into()), reusable);
    drop(builder);
    assert_eq!(register(&mut egraph), reusable);
    egraph.free_external_func(reusable);

    let mut builder = egraph.new_rule("dropped", false);
    builder.panic("rule panic".into());
    drop(builder);
    assert_eq!(register(&mut egraph), reusable);
    egraph.free_external_func(reusable);

    let transferred = register(&mut egraph);
    let mut builder = egraph.new_rule("dropped", false);
    builder.own_external_func(transferred);
    drop(builder);
    assert_eq!(register(&mut egraph), transferred);
    egraph.free_external_func(transferred);

    let mut builder = egraph.new_rule("dropped", false);
    let first = builder.new_panic("shared panic".into());
    let second = builder.new_panic("shared panic".into());
    assert_eq!(first, reusable);
    assert_eq!(second, reusable);
    drop(builder);
    assert_eq!(register(&mut egraph), reusable);
    egraph.free_external_func(reusable);

    let rule = {
        let mut builder = egraph.new_rule("built", false);
        builder.panic("built panic".into());
        builder.build()
    };
    let occupied = register(&mut egraph);
    assert_ne!(occupied, reusable);
    egraph.free_external_func(occupied);
    egraph.free_rule(rule);
    assert_eq!(register(&mut egraph), reusable);
}

#[test]
fn removing_last_table_restores_shadowed_registry_entry_and_id() {
    let mut egraph = EGraph::default();
    let unit_type = egraph.base_values_mut().register_type::<()>();
    let unit = egraph.base_values().get(());
    let config = || FunctionConfig {
        schema: vec![ColumnTy::Base(unit_type)],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Const(unit),
        merge: single_merge(assert_equal(0)),
        name: "temporary".into(),
        can_subsume: false,
    };

    let original = egraph.add_table(config());
    let original_action = egraph
        .action_registry()
        .read()
        .unwrap()
        .lookup_table("temporary")
        .unwrap()
        .clone();
    let temporary = egraph.add_table(config());

    egraph.remove_last_table(temporary).unwrap();
    assert_eq!(
        egraph
            .action_registry()
            .read()
            .unwrap()
            .lookup_table("temporary"),
        Some(&original_action)
    );
    assert_eq!(egraph.add_table(config()), temporary);
    assert_ne!(original, temporary);
}

#[test]
fn removing_unknown_or_non_last_function_preserves_registrations() {
    let mut egraph = EGraph::default();
    let unit_type = egraph.base_values_mut().register_type::<()>();
    let unit = egraph.base_values().get(());
    let config = |name: &str| FunctionConfig {
        schema: vec![ColumnTy::Base(unit_type)],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Const(unit),
        merge: single_merge(assert_equal(0)),
        name: name.into(),
        can_subsume: false,
    };
    let first = egraph.add_table(config("first"));
    let second = egraph.add_table(config("second"));
    let first_action = TableAction::new(&egraph, first);
    let second_action = TableAction::new(&egraph, second);

    assert!(egraph.remove_last_table(FunctionId::new(u32::MAX)).is_err());
    assert_eq!(egraph.table_size(first), 0);
    assert_eq!(egraph.table_size(second), 0);
    assert_eq!(
        egraph
            .action_registry()
            .read()
            .unwrap()
            .lookup_table("first"),
        Some(&first_action)
    );
    assert_eq!(
        egraph
            .action_registry()
            .read()
            .unwrap()
            .lookup_table("second"),
        Some(&second_action)
    );

    assert!(egraph.remove_last_table(first).is_err());
    assert_eq!(egraph.table_size(first), 0);
    assert_eq!(egraph.table_size(second), 0);
    assert_eq!(
        egraph
            .action_registry()
            .read()
            .unwrap()
            .lookup_table("first"),
        Some(&first_action)
    );
    assert_eq!(
        egraph
            .action_registry()
            .read()
            .unwrap()
            .lookup_table("second"),
        Some(&second_action)
    );
}

#[test]
fn failed_database_table_removal_restores_function_registration() {
    let mut egraph = EGraph::default();
    let unit_type = egraph.base_values_mut().register_type::<()>();
    let unit = egraph.base_values().get(());
    let function = egraph.add_table(FunctionConfig {
        schema: vec![ColumnTy::Base(unit_type)],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Const(unit),
        merge: single_merge(assert_equal(0)),
        name: "function".into(),
        can_subsume: false,
    });
    let action = TableAction::new(&egraph, function);
    let blocker = egraph.db.add_table(
        SortedWritesTable::new(1, 1, None, vec![], Box::new(|_, _, _, _| false)),
        iter::empty(),
        iter::empty(),
    );

    assert!(egraph.remove_last_table(function).is_err());
    assert_eq!(egraph.table_size(function), 0);
    assert_eq!(
        egraph
            .action_registry()
            .read()
            .unwrap()
            .lookup_table("function"),
        Some(&action)
    );
    assert!(egraph.db.remove_last_table(blocker));
    egraph.remove_last_table(function).unwrap();
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
        merge: single_merge(union_id(0)),
        name: "num".into(),
        can_subsume,
    });
    let add_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id; 3],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
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
    assert!(!egraph.run_rules(&[add_comm, add_assoc]).unwrap().changed());

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
    while egraph.run_rules(&[add_comm, add_assoc]).unwrap().changed() {}
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
        merge: single_merge(union_id(0)),
        name: "num".into(),
        can_subsume: false,
    });
    let add_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id; 3],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
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
    assert!(!egraph.run_rules(&[add_comm, add_assoc]).unwrap().changed());

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
    while egraph.run_rules(&[add_comm, add_assoc]).unwrap().changed() {}
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
        merge: single_merge(union_id(0)),
        name: "diff".into(),
        can_subsume,
    });
    let integral = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "integral".into(),
        can_subsume,
    });
    let add = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "add".into(),
        can_subsume,
    });
    let sub = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "sub".into(),
        can_subsume,
    });
    let mul = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "mul".into(),
        can_subsume,
    });
    let div = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "div".into(),
        can_subsume,
    });
    let pow = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "pow".into(),
        can_subsume,
    });

    let ln = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "ln".into(),
        can_subsume,
    });
    let sqrt = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "sqrt".into(),
        can_subsume,
    });
    let sin = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "sin".into(),
        can_subsume,
    });
    let cos = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "cos".into(),
        can_subsume,
    });
    let rat = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(rational_ty), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "rat".into(),
        can_subsume,
    });
    let var = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(string_ty), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
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
        if !egraph.run_rules(&rules).unwrap().changed() {
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
        merge: single_merge(union_id(0)),
        name: "num".into(),
        can_subsume: false,
    });
    let add_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id; 3],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "add".into(),
        can_subsume: false,
    });
    let vec_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id; 2],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
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

    assert!(egraph.run_rules(&[vec_expand]).unwrap().changed());
    assert_eq!(dump_vecs(&egraph).len(), 4);
    // We have 2 new vectors with a last element. Each of those should spawn two more, adding 4.
    assert!(egraph.run_rules(&[vec_expand]).unwrap().changed());
    assert_eq!(dump_vecs(&egraph).len(), 8);
    // We have 4 new vectors with a last element. Each of those should spawn two more, adding 8.
    assert!(egraph.run_rules(&[vec_expand]).unwrap().changed());
    assert_eq!(dump_vecs(&egraph).len(), 16);

    // Now we want to saturate `eval_add`. This should collapse a bunch of new vectors.

    let mut saturated = false;
    for _ in 0..20 {
        saturated = !egraph.run_rules(&[eval_add]).unwrap().changed();
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
        merge: single_merge(union_id(0)),
        name: "k".into(),
        can_subsume: false,
    });
    let w_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "w".into(),
        can_subsume: false,
    });
    let l_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
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
        saturated = !egraph.run_rules(&[w_rewrite, l_rewrite]).unwrap().changed();
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
        merge: single_merge(union_id(0)),
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
    assert!(egraph.run_rules(&[add_data]).unwrap().changed());
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

    assert!(!egraph.run_rules(&[inc_counter_rule]).unwrap().changed());
    assert_eq!(counter.load(Ordering::SeqCst), 1);
    assert!(!egraph.run_rules(&[inc_counter_rule]).unwrap().changed());
    assert_eq!(counter.load(Ordering::SeqCst), 1);
}

#[test]
fn merge_expr_arithmetic() {
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
    // This uses nested MergeExpr::Primitive with external functions to build the complex merge function
    let f_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Base(int_base)],
        default: DefaultVal::Fail,
        merge: single_merge(primitive(
            add_func,
            vec![
                MergeExpr::Const(value_1),
                primitive(
                    multiply_func,
                    vec![prior(0), incoming(0)],
                    MergePrimitiveOrigin::Opaque,
                ),
            ],
            MergePrimitiveOrigin::Opaque,
        )),
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
    assert!(egraph.run_rules(&[rule1]).unwrap().changed());
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
    assert!(egraph.run_rules(&[rule2]).unwrap().changed());
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
    assert!(egraph.run_rules(&[rule3]).unwrap().changed());
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
fn merge_expr_nested_function() {
    let mut egraph = EGraph::default();
    let int_base = egraph.base_values_mut().register_type::<i64>();

    // Create a function g that will be used in the merge function for f
    let g_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
        name: "g".into(),
        can_subsume: true,
    });

    // Create a function f whose merge function is (g (g new new) (g old old))
    // This uses nested MergeExpr::Function to build the complex merge function
    let f_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(function(
            g_table,
            vec![
                function(g_table, vec![incoming(0), incoming(0)]),
                function(g_table, vec![prior(0), prior(0)]),
            ],
        )),
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
    assert!(egraph.run_rules(&[write_rule]).unwrap().changed());
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
    assert!(egraph.run_rules(&[set_rule]).unwrap().changed());
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
        merge: single_merge(union_id(0)),
        name: "f".into(),
        can_subsume: false,
    });
    let g_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
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
    egraph.run_rules(&[write_f]).unwrap();
    let f = get_entries(&egraph, f_table);
    assert_eq!(f.len(), 3);
    egraph.run_rules(&[copy_to_g]).unwrap();
    let invocations_after_first = query_prim_invocations.load(Ordering::Relaxed);
    assert!(invocations_after_first > 0);
    assert!(!egraph.run_rules(&[copy_to_g]).unwrap().changed());
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
        merge: single_merge(union_id(0)),
        name: "f".into(),
        can_subsume: false,
    });
    let g_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
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
    egraph.run_rules(&[write_f]).unwrap();
    let f = get_entries(&egraph, f_table);
    assert_eq!(f.len(), 3);
    egraph.run_rules(&[copy_to_g]).unwrap();
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
        merge: single_merge(union_id(0)),
        name: "f".into(),
        can_subsume: true,
    });
    let g_table = egraph.add_table(FunctionConfig {
        n_vals: 1,
        n_identity_vals: None,
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Id],
        default: DefaultVal::FreshId,
        merge: single_merge(union_id(0)),
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
    egraph.run_rules(&[write_f]).unwrap();
    let f = get_entries(&egraph, f_table);
    assert_eq!((f.0.len(), f.1), (2, 0));
    assert_eq!(f.0.iter().map(|(x, _)| *x).collect::<Vec<_>>(), vec![1, 2]);
    egraph.run_rules(&[subsume_f]).unwrap();
    let f = get_entries(&egraph, f_table);
    assert_eq!((f.0.len(), f.1), (3, 2));
    assert_eq!(
        f.0.iter().map(|(x, _)| *x).collect::<Vec<_>>(),
        vec![1, 2, 3]
    );
    egraph.run_rules(&[copy_to_g]).unwrap();
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
        merge: single_merge(union_id(0)),
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
    egraph.run_rules(&[write_f]).unwrap();

    let lookup_success = {
        let mut rb = egraph.new_rule("lookup_success", true);
        rb.lookup(f, slice::from_ref(&value_1), String::new);
        rb.build()
    };
    egraph.run_rules(&[lookup_success]).unwrap();

    let lookup_failure = {
        let mut rb = egraph.new_rule("lookup_fail", true);
        rb.lookup(f, slice::from_ref(&value_3), String::new);
        rb.build()
    };
    egraph.run_rules(&[lookup_failure]).err().unwrap();
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

    egraph.run_rules(&[assert_odd_rule]).err().unwrap();
}

#[test]
fn panic_functions_trigger_early_stop() {
    let db = core_relations::Database::default();

    let channel: crate::SideChannel<String> = Default::default();
    let panic_fn = super::Panic("panic".to_string(), channel.clone());
    let stopped = db.with_execution_state(|state| {
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
    let stopped = db.with_execution_state(|state| {
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
    // itself. Exercises `peek_next_function_id`, `MergeAction::Set` into self, and the backend's
    // self-write buffer pre-seed.
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
    let min = || {
        primitive(
            min_func,
            vec![prior(0), incoming(0)],
            MergePrimitiveOrigin::Opaque,
        )
    };
    let max = primitive(
        max_func,
        vec![prior(0), incoming(0)],
        MergePrimitiveOrigin::Opaque,
    );
    let uf = egraph.add_table(FunctionConfig {
        schema: vec![ColumnTy::Base(int_base), ColumnTy::Base(int_base)],
        n_vals: 1,
        // The single parent column is the identity: the guard skips the merge when the parent is
        // unchanged, so the body stages the displaced edge unconditionally.
        n_identity_vals: Some(1),
        default: DefaultVal::Fail,
        merge: MergeProgram {
            actions: vec![MergeAction::Set {
                function: uf_id,
                arguments: vec![max, min()],
            }],
            results: vec![min()],
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
        egraph.run_rules(&[r]).unwrap();
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
    let action_calls = Arc::new(AtomicUsize::new(0));
    let observed_calls = action_calls.clone();
    let count_action =
        egraph.register_external_func(Box::new(make_external_func(move |_state, values| {
            assert!(values.is_empty());
            observed_calls.fetch_add(1, Ordering::SeqCst);
            Some(Value::new(0))
        })));
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
        merge: MergeProgram {
            actions: vec![MergeAction::Let {
                binding: MergeBindingId::new(0),
                value: primitive(count_action, Vec::new(), MergePrimitiveOrigin::Opaque),
            }],
            results: vec![incoming(0), incoming(1)],
        },
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
        egraph.run_rules(&[r]).unwrap();
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
    assert_eq!(action_calls.load(Ordering::SeqCst), 0);
    set(&mut egraph, 20, 300); // identity 10 -> 20 -> merge runs, takes new
    assert_eq!(
        read_row(&egraph),
        (20, 300),
        "an identity change should run the merge"
    );
    assert_eq!(
        action_calls.load(Ordering::SeqCst),
        1,
        "the action must run once for the conflict, not once per result"
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
        merge: MergeProgram {
            actions: Vec::new(),
            results: vec![prior(0), prior(1)],
        },
        name: "tuple-subsume".into(),
        can_subsume: true,
    });
    let key = egraph.base_values_mut().get(1_i64);
    let first = egraph.base_values_mut().get(10_i64);
    let second = egraph.base_values_mut().get(20_i64);
    let action = TableAction::new(&egraph, f);
    egraph
        .db
        .with_execution_state(|state| action.insert(state, [key, first, second].into_iter()));
    egraph.flush_updates();
    egraph
        .db
        .with_execution_state(|state| action.subsume(state, std::iter::once(key)));
    egraph.flush_updates();

    let mut rows = Vec::new();
    egraph.for_each(f, |row| rows.push((row.vals.to_vec(), row.subsumed)));
    assert_eq!(rows, vec![(vec![key, first, second], true)]);
}

const _: () = {
    const fn assert_send<T: Send>() {}
    assert_send::<EGraph>()
};
