use std::time::{Duration, Instant};

use anyhow::{Result, bail};
use egglog_ast::{
    core::{
        GenericAtom, GenericAtomTerm, GenericCoreAction, GenericCoreActions, GenericCoreRule, Query,
    },
    span::Span,
};
use egglog_backend_trait::{
    Backend, BaseValueId, ColumnTy, DefaultVal, ExternalFunctionId, FunctionConfig, FunctionId,
    MatchObserver, MergeFn, PreMergeTiming, ReadMode, RuleActionCall, RuleBodyCall, RuleId,
    RuleSetRun, RuleSpec, RuleValue, RuleVar, Value,
};
use egglog_core_relations::Boxed;
use egglog_numeric_id::NumericId;
use ordered_float::OrderedFloat;

use crate::EGraph;

type RuleTerm = GenericAtomTerm<RuleVar, RuleValue>;
type PointerTranscript = Vec<(bool, Vec<(String, u32)>)>;
type MathTranscript = Vec<(bool, Vec<(u32, u32, u32)>)>;

const POINTER_SOURCE: &str = include_str!("../../../benchmarks/pointer-analysis-small.egg");
const MATH_SOURCE: &str = include_str!("../../../egglog/tests/math-microbenchmark.egg");

#[derive(Clone, Copy)]
struct ScalarTypes {
    unit: BaseValueId,
    string: BaseValueId,
    i64: BaseValueId,
}

fn register_scalar_types<B: Backend>(backend: &mut B) -> ScalarTypes {
    ScalarTypes {
        unit: backend.base_values_mut().register_type::<()>(),
        string: backend.base_values_mut().register_type::<Boxed<String>>(),
        i64: backend.base_values_mut().register_type::<i64>(),
    }
}

fn table<B: Backend>(backend: &mut B, name: &str, schema: Vec<ColumnTy>) -> FunctionId {
    table_with_merge(backend, name, schema, MergeFn::Old)
}

fn table_with_merge<B: Backend>(
    backend: &mut B,
    name: &str,
    schema: Vec<ColumnTy>,
    merge: MergeFn,
) -> FunctionId {
    backend.add_table(FunctionConfig {
        schema,
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge,
        name: name.to_string(),
        can_subsume: false,
    })
}

fn subsumable_table<B: Backend>(backend: &mut B, name: &str, schema: Vec<ColumnTy>) -> FunctionId {
    backend.add_table(FunctionConfig {
        schema,
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::Old,
        name: name.to_string(),
        can_subsume: true,
    })
}

fn var(id: u32, name: &str, ty: ColumnTy) -> RuleTerm {
    GenericAtomTerm::Var(
        Span::Panic,
        RuleVar {
            id,
            name: name.into(),
            ty,
        },
    )
}

fn literal(value: Value, ty: ColumnTy) -> RuleTerm {
    GenericAtomTerm::Literal(Span::Panic, RuleValue { value, ty })
}

fn atom(id: FunctionId, args: Vec<RuleTerm>) -> GenericAtom<RuleBodyCall, RuleVar, RuleValue> {
    atom_with_read(id, ReadMode::Live, args)
}

fn atom_with_read(
    id: FunctionId,
    read: ReadMode,
    args: Vec<RuleTerm>,
) -> GenericAtom<RuleBodyCall, RuleVar, RuleValue> {
    GenericAtom {
        span: Span::Panic,
        head: RuleBodyCall::Table { id, read },
        args,
    }
}

fn observation_rule(
    name: &str,
    token: ExternalFunctionId,
    body: Vec<GenericAtom<RuleBodyCall, RuleVar, RuleValue>>,
) -> RuleSpec {
    RuleSpec {
        name: name.to_string(),
        seminaive: false,
        no_decomp: false,
        core: GenericCoreRule {
            span: Span::Panic,
            body: Query { atoms: body },
            head: GenericCoreActions::new(vec![GenericCoreAction::Let(
                Span::Panic,
                RuleVar {
                    id: 10_000,
                    name: "unused-observer-result".into(),
                    ty: ColumnTy::Id,
                },
                RuleActionCall::Primitive {
                    id: token,
                    name: "diagnostic-only-observer-name".into(),
                    output: ColumnTy::Id,
                },
                Vec::new(),
            )]),
        },
    }
}

fn register_observation<B: Backend>(
    backend: &mut B,
    name: &str,
    body: Vec<GenericAtom<RuleBodyCall, RuleVar, RuleValue>>,
) -> Result<(MatchObserver, ExternalFunctionId, RuleId)> {
    let observer = MatchObserver::new();
    let token = backend.register_match_observer(observer.clone());
    let rule = backend.add_rule(observation_rule(name, token, body))?;
    Ok((observer, token, rule))
}

fn set_rule(
    name: &str,
    seminaive: bool,
    body: Vec<GenericAtom<RuleBodyCall, RuleVar, RuleValue>>,
    target: FunctionId,
    keys: Vec<RuleTerm>,
    values: Vec<RuleTerm>,
) -> RuleSpec {
    RuleSpec {
        name: name.to_string(),
        seminaive,
        no_decomp: false,
        core: GenericCoreRule {
            span: Span::Panic,
            body: Query { atoms: body },
            head: GenericCoreActions::new(vec![GenericCoreAction::Set(
                Span::Panic,
                RuleActionCall::Table {
                    id: target,
                    name: "diagnostic-only-table-name".into(),
                },
                keys,
                values,
            )]),
        },
    }
}

fn run<B: Backend>(backend: &mut B, rules: &[RuleId]) -> Result<bool> {
    Ok(backend
        .run_rules(RuleSetRun {
            name: Some("checkpoint-0.5-test"),
            rules,
        })?
        .changed())
}

fn string_value<B: Backend>(backend: &B, value: &str) -> Value {
    backend.base_values().get(Boxed::new(value.to_string()))
}

fn unit_value<B: Backend>(backend: &B) -> Value {
    backend.base_values().get(())
}

fn i64_value<B: Backend>(backend: &B, value: i64) -> Value {
    backend.base_values().get(value)
}

fn scan_values<B: Backend>(backend: &B, id: FunctionId) -> Vec<Vec<Value>> {
    let mut rows = Vec::new();
    backend.for_each_while_dyn(id, &mut |entry| {
        rows.push(entry.vals.to_vec());
        true
    });
    rows
}

fn scan_state<B: Backend>(backend: &B, id: FunctionId) -> Vec<(Vec<Value>, bool)> {
    let mut rows = Vec::new();
    backend.for_each_while_dyn(id, &mut |entry| {
        rows.push((entry.vals.to_vec(), entry.subsumed));
        true
    });
    rows.sort_by_key(|(values, subsumed)| {
        (
            values.iter().map(|value| value.rep()).collect::<Vec<_>>(),
            *subsumed,
        )
    });
    rows
}

struct PointerFixture {
    rule: RuleId,
    function_name: FunctionId,
    witness: FunctionId,
    fresh_name: Value,
    unit: Value,
}

fn pointer_fixture<B: Backend>(backend: &mut B) -> Result<PointerFixture> {
    let types = register_scalar_types(backend);
    backend
        .base_values_mut()
        .register_type::<Boxed<OrderedFloat<f64>>>();
    backend.base_values_mut().register_type::<bool>();
    let string = ColumnTy::Base(types.string);
    let integer = ColumnTy::Base(types.i64);
    let unit_ty = ColumnTy::Base(types.unit);

    let function_name = table(backend, "function_name", vec![string, unit_ty]);
    let function_param = table(
        backend,
        "function_param",
        vec![string, integer, string, unit_ty],
    );
    let call_target = table(
        backend,
        "call_instruction_fn_target",
        vec![string, string, unit_ty],
    );
    let call_arg = table(
        backend,
        "call_instruction_arg",
        vec![string, integer, string, unit_ty],
    );
    let expr_points_to = table(backend, "expr_points_to", vec![string, ColumnTy::Id]);
    let witness = table(backend, "pointer_witness", vec![string, ColumnTy::Id]);

    let f1 = string_value(backend, "f1");
    let f2 = string_value(backend, "f2");
    let f_decoy = string_value(backend, "unrelated");
    let c1 = string_value(backend, "call-1");
    let c2 = string_value(backend, "call-2");
    let c_decoy = string_value(backend, "call-decoy");
    let x1 = string_value(backend, "x1");
    let x2 = string_value(backend, "x2");
    let x_decoy = string_value(backend, "x-decoy");
    let v1 = string_value(backend, "v1");
    let v2 = string_value(backend, "v2");
    let v_decoy = string_value(backend, "v-decoy");
    let zero = i64_value(backend, 0);
    let one = i64_value(backend, 1);
    let unit = unit_value(backend);

    backend.add_values(vec![
        (function_name, vec![f1, unit]),
        (function_name, vec![f_decoy, unit]),
        (function_param, vec![f1, zero, x1, unit]),
        (function_param, vec![f2, zero, x2, unit]),
        (function_param, vec![f_decoy, one, x_decoy, unit]),
        (call_target, vec![c1, f1, unit]),
        (call_target, vec![c2, f2, unit]),
        (call_target, vec![c_decoy, f_decoy, unit]),
        (call_arg, vec![c1, zero, v1, unit]),
        (call_arg, vec![c2, zero, v2, unit]),
        (call_arg, vec![c_decoy, zero, v_decoy, unit]),
        (expr_points_to, vec![v1, Value::new(101)]),
        (expr_points_to, vec![v2, Value::new(202)]),
        (expr_points_to, vec![v_decoy, Value::new(303)]),
    ])?;

    let f = var(0, "f", string);
    let idx = var(1, "idx", integer);
    let x = var(2, "x", string);
    let instr = var(3, "instr", string);
    let v = var(4, "v", string);
    let allocation = var(5, "allocation", ColumnTy::Id);
    let unit_literal = literal(unit, unit_ty);
    let spec = set_rule(
        "pointer-five-way-source-lines-168-176",
        true,
        vec![
            atom(function_name, vec![f.clone(), unit_literal.clone()]),
            atom(
                function_param,
                vec![f.clone(), idx.clone(), x.clone(), unit_literal.clone()],
            ),
            atom(
                call_target,
                vec![instr.clone(), f.clone(), unit_literal.clone()],
            ),
            atom(
                call_arg,
                vec![instr.clone(), idx.clone(), v.clone(), unit_literal],
            ),
            atom(expr_points_to, vec![v, allocation.clone()]),
        ],
        witness,
        vec![x],
        vec![allocation],
    );
    let rule = backend.add_rule(spec)?;
    Ok(PointerFixture {
        rule,
        function_name,
        witness,
        fresh_name: f2,
        unit,
    })
}

fn pointer_witnesses<B: Backend>(backend: &B, table: FunctionId) -> Vec<(String, u32)> {
    let mut rows = scan_values(backend, table)
        .into_iter()
        .map(|row| {
            (
                backend
                    .base_values()
                    .unwrap::<Boxed<String>>(row[0])
                    .into_inner()
                    .to_string(),
                row[1].rep(),
            )
        })
        .collect::<Vec<_>>();
    rows.sort();
    rows
}

fn pointer_transcript<B: Backend>(backend: &mut B) -> Result<PointerTranscript> {
    let fixture = pointer_fixture(backend)?;
    let mut transcript = Vec::new();
    transcript.push((
        run(backend, &[fixture.rule])?,
        pointer_witnesses(backend, fixture.witness),
    ));
    backend.add_values(vec![(
        fixture.function_name,
        vec![fixture.fresh_name, fixture.unit],
    )])?;
    transcript.push((
        run(backend, &[fixture.rule])?,
        pointer_witnesses(backend, fixture.witness),
    ));
    transcript.push((
        run(backend, &[fixture.rule])?,
        pointer_witnesses(backend, fixture.witness),
    ));
    Ok(transcript)
}

struct MathFixture {
    rule: RuleId,
    add: FunctionId,
}

fn math_fixture<B: Backend>(backend: &mut B) -> Result<MathFixture> {
    register_scalar_types(backend);
    backend
        .base_values_mut()
        .register_type::<Boxed<OrderedFloat<f64>>>();
    backend.base_values_mut().register_type::<bool>();
    let add = table(
        backend,
        "Add",
        vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
    );
    backend.add_values(vec![
        (add, vec![Value::new(1), Value::new(2), Value::new(101)]),
        (add, vec![Value::new(3), Value::new(4), Value::new(202)]),
    ])?;
    let a = var(0, "a", ColumnTy::Id);
    let b = var(1, "b", ColumnTy::Id);
    let output = var(2, "output", ColumnTy::Id);
    let rule = backend.add_rule(set_rule(
        "math-add-commutativity-source-line-19",
        true,
        vec![atom(add, vec![a.clone(), b.clone(), output.clone()])],
        add,
        vec![b, a],
        vec![output],
    ))?;
    Ok(MathFixture { rule, add })
}

fn math_rows<B: Backend>(backend: &B, table: FunctionId) -> Vec<(u32, u32, u32)> {
    let mut rows = scan_values(backend, table)
        .into_iter()
        .map(|row| (row[0].rep(), row[1].rep(), row[2].rep()))
        .collect::<Vec<_>>();
    rows.sort();
    rows
}

fn math_transcript<B: Backend>(backend: &mut B) -> Result<MathTranscript> {
    let fixture = math_fixture(backend)?;
    let mut transcript = Vec::new();
    transcript.push((
        run(backend, &[fixture.rule])?,
        math_rows(backend, fixture.add),
    ));
    backend.add_values(vec![(
        fixture.add,
        vec![Value::new(5), Value::new(6), Value::new(303)],
    )])?;
    transcript.push((
        run(backend, &[fixture.rule])?,
        math_rows(backend, fixture.add),
    ));
    transcript.push((
        run(backend, &[fixture.rule])?,
        math_rows(backend, fixture.add),
    ));
    Ok(transcript)
}

fn pointer_observation_fixture<B: Backend>(
    backend: &mut B,
    hit: bool,
) -> Result<(MatchObserver, ExternalFunctionId, RuleId)> {
    let types = register_scalar_types(backend);
    backend
        .base_values_mut()
        .register_type::<Boxed<OrderedFloat<f64>>>();
    backend.base_values_mut().register_type::<bool>();
    let string = ColumnTy::Base(types.string);
    let left = table(
        backend,
        "pointer encoded left relation",
        vec![string, ColumnTy::Id, ColumnTy::Id],
    );
    let right = table(
        backend,
        "pointer encoded right relation",
        vec![ColumnTy::Id, string, ColumnTy::Id],
    );
    let call = string_value(backend, "call-site");
    let formal = string_value(backend, "formal");
    let decoy = string_value(backend, "decoy");
    backend.add_values(vec![
        (left, vec![call, Value::new(101), Value::new(901)]),
        (left, vec![decoy, Value::new(999), Value::new(902)]),
        (
            right,
            vec![
                if hit {
                    Value::new(101)
                } else {
                    Value::new(777)
                },
                formal,
                Value::new(903),
            ],
        ),
        (right, vec![Value::new(888), decoy, Value::new(904)]),
    ])?;
    let allocation_left = var(0, "allocation-left", ColumnTy::Id);
    let allocation_right = var(0, "renamed-allocation-right", ColumnTy::Id);
    register_observation(
        backend,
        "pointer-two-All-observation",
        vec![
            atom_with_read(
                left,
                ReadMode::All,
                vec![
                    literal(call, string),
                    allocation_left,
                    var(1, "opaque-left-proof", ColumnTy::Id),
                ],
            ),
            atom_with_read(
                right,
                ReadMode::All,
                vec![
                    allocation_right,
                    literal(formal, string),
                    var(2, "opaque-right-proof", ColumnTy::Id),
                ],
            ),
        ],
    )
}

fn subsume_selected_row(
    backend: &mut EGraph,
    name: &str,
    target: FunctionId,
    shared: Value,
    label: Value,
    string: ColumnTy,
) -> Result<RuleId> {
    backend.add_rule(RuleSpec {
        name: name.to_string(),
        seminaive: false,
        no_decomp: false,
        core: GenericCoreRule {
            span: Span::Panic,
            body: Query {
                atoms: vec![atom(
                    target,
                    vec![
                        literal(shared, ColumnTy::Id),
                        literal(label, string),
                        var(0, "opaque-proof", ColumnTy::Id),
                    ],
                )],
            },
            head: GenericCoreActions::new(vec![GenericCoreAction::Change(
                Span::Panic,
                egglog_ast::generic_ast::Change::Subsume,
                RuleActionCall::Table {
                    id: target,
                    name: "diagnostic-only-subsume-target".into(),
                },
                vec![literal(shared, ColumnTy::Id), literal(label, string)],
            )]),
        },
    })
}

#[test]
fn match_observation_pointer_shape_matches_reference_for_hit_and_miss() -> Result<()> {
    for hit in [false, true] {
        let mut reference = egglog_bridge::EGraph::default();
        let (reference_observer, reference_token, reference_rule) =
            pointer_observation_fixture(&mut reference, hit)?;
        assert!(!run(&mut reference, &[reference_rule])?);
        reference.free_rule(reference_rule);
        reference.free_external_func(reference_token);
        assert_eq!(reference_observer.matched(), hit);

        let mut duckdb = EGraph::new()?;
        let (duckdb_observer, duckdb_token, duckdb_rule) =
            pointer_observation_fixture(&mut duckdb, hit)?;
        assert!(!run(&mut duckdb, &[duckdb_rule])?);
        assert_eq!(duckdb.last_rule_match_counts(), &[usize::from(hit)]);
        assert_eq!(duckdb.last_rule_insert_counts(), &[0]);
        duckdb.free_rule(duckdb_rule);
        duckdb.free_external_func(duckdb_token);
        assert_eq!(duckdb_observer.matched(), reference_observer.matched());
    }
    Ok(())
}

#[test]
fn duckdb_reports_serial_rule_time_as_split_unattributed_elapsed() -> Result<()> {
    let mut backend = EGraph::new()?;
    let (observer, token, rule) = pointer_observation_fixture(&mut backend, true)?;
    let report = backend.run_rules(RuleSetRun {
        name: Some("timed-observation"),
        rules: &[rule],
    })?;
    let PreMergeTiming::Split {
        search,
        apply,
        unattributed,
    } = report.rule_set_report.pre_merge
    else {
        panic!("serial DuckDB execution must report split timing")
    };
    assert_eq!(search, Duration::ZERO);
    assert_eq!(apply, Duration::ZERO);
    assert_eq!(report.rule_set_report.pre_merge.total(), unattributed);
    assert!(observer.matched());

    let empty = backend.run_rules(RuleSetRun {
        name: Some("empty"),
        rules: &[],
    })?;
    assert_eq!(
        empty.rule_set_report.pre_merge,
        PreMergeTiming::Split {
            search: Duration::ZERO,
            apply: Duration::ZERO,
            unattributed: Duration::ZERO,
        }
    );
    backend.free_rule(rule);
    backend.free_external_func(token);
    Ok(())
}

#[test]
fn match_observation_reports_absent_one_and_three_match_cardinalities() -> Result<()> {
    for expected in [0_usize, 1, 3] {
        let mut backend = EGraph::new()?;
        let left = table(
            &mut backend,
            "cardinality-left",
            vec![ColumnTy::Id, ColumnTy::Id],
        );
        let right = table(
            &mut backend,
            "cardinality-right",
            vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        );
        backend.add_values(vec![(left, vec![Value::new(7), Value::new(70)])])?;
        backend.add_values(
            (0..expected)
                .map(|index| {
                    (
                        right,
                        vec![
                            Value::new(7),
                            Value::new(u32::try_from(index + 1).unwrap()),
                            Value::new(u32::try_from(80 + index).unwrap()),
                        ],
                    )
                })
                .collect(),
        )?;
        let generation = backend.storage.generation()?;
        let shared = var(0, "shared-left", ColumnTy::Id);
        let (observer, token, rule) = register_observation(
            &mut backend,
            "cardinality-observer",
            vec![
                atom_with_read(
                    left,
                    ReadMode::All,
                    vec![shared, var(1, "left-proof", ColumnTy::Id)],
                ),
                atom_with_read(
                    right,
                    ReadMode::All,
                    vec![
                        var(0, "shared-right", ColumnTy::Id),
                        var(2, "tag", ColumnTy::Id),
                        var(3, "right-proof", ColumnTy::Id),
                    ],
                ),
            ],
        )?;

        assert!(!run(&mut backend, &[rule])?);
        assert_eq!(observer.matched(), expected != 0);
        assert_eq!(backend.last_rule_match_counts(), &[expected]);
        assert_eq!(backend.last_rule_insert_counts(), &[0]);
        assert_eq!(
            backend.rules[rule.rep() as usize]
                .as_ref()
                .unwrap()
                .watermark,
            generation
        );
        let manifest = backend.storage.latest_rule_sql();
        assert_eq!(backend.last_rule_statement_count(), manifest.len() + 1);
        assert!(manifest.iter().all(|sql| {
            !sql.contains("INSERT ")
                && !sql.contains("UPDATE ")
                && !sql.contains("DELETE ")
                && !sql.contains('?')
        }));
        assert!(
            manifest
                .first()
                .is_some_and(|sql| sql.contains("SELECT TRUE AS __matched"))
        );
        backend.free_rule(rule);
        backend.free_external_func(token);
        assert_eq!(observer.matched(), expected != 0);
    }
    Ok(())
}

#[test]
fn match_observation_all_reads_cover_every_live_and_subsumed_pair() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = register_scalar_types(&mut backend);
    backend
        .base_values_mut()
        .register_type::<Boxed<OrderedFloat<f64>>>();
    backend.base_values_mut().register_type::<bool>();
    let string = ColumnTy::Base(types.string);
    let left = subsumable_table(
        &mut backend,
        "visibility-left",
        vec![ColumnTy::Id, string, ColumnTy::Id],
    );
    let right = subsumable_table(
        &mut backend,
        "visibility-right",
        vec![ColumnTy::Id, string, ColumnTy::Id],
    );
    let shared = Value::new(41);
    let live = string_value(&backend, "live");
    let subsumed = string_value(&backend, "subsumed");
    backend.add_values(vec![
        (left, vec![shared, live, Value::new(101)]),
        (left, vec![shared, subsumed, Value::new(102)]),
        (right, vec![shared, live, Value::new(201)]),
        (right, vec![shared, subsumed, Value::new(202)]),
    ])?;
    let subsume_left =
        subsume_selected_row(&mut backend, "subsume-left", left, shared, subsumed, string)?;
    let subsume_right = subsume_selected_row(
        &mut backend,
        "subsume-right",
        right,
        shared,
        subsumed,
        string,
    )?;
    assert!(run(&mut backend, &[subsume_left, subsume_right])?);

    let mut observers = Vec::new();
    let mut tokens = Vec::new();
    let mut rules = Vec::new();
    for (left_label, right_label, name) in [
        (live, live, "live-live"),
        (live, subsumed, "live-subsumed"),
        (subsumed, live, "subsumed-live"),
        (subsumed, subsumed, "subsumed-subsumed"),
    ] {
        let (observer, token, rule) = register_observation(
            &mut backend,
            name,
            vec![
                atom_with_read(
                    left,
                    ReadMode::All,
                    vec![
                        var(0, "shared-left", ColumnTy::Id),
                        literal(left_label, string),
                        var(1, "left-proof", ColumnTy::Id),
                    ],
                ),
                atom_with_read(
                    right,
                    ReadMode::All,
                    vec![
                        var(0, "renamed-shared-right", ColumnTy::Id),
                        literal(right_label, string),
                        var(2, "right-proof", ColumnTy::Id),
                    ],
                ),
            ],
        )?;
        observers.push(observer);
        tokens.push(token);
        rules.push(rule);
    }
    let generation = backend.storage.generation()?;
    assert!(!run(&mut backend, &rules)?);
    assert!(observers.iter().all(MatchObserver::matched));
    assert_eq!(backend.last_rule_match_counts(), &[1, 1, 1, 1]);
    assert_eq!(backend.last_rule_insert_counts(), &[0, 0, 0, 0]);
    assert!(
        backend
            .storage
            .latest_rule_sql()
            .iter()
            .all(|sql| !sql.contains("__subsumed"))
    );
    for rule in &rules {
        assert_eq!(
            backend.rules[rule.rep() as usize]
                .as_ref()
                .unwrap()
                .watermark,
            generation
        );
    }
    for (rule, token) in rules.into_iter().zip(tokens) {
        backend.free_rule(rule);
        backend.free_external_func(token);
    }
    Ok(())
}

#[test]
fn match_observation_uses_typed_literals_and_id_type_variable_identity() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = register_scalar_types(&mut backend);
    backend
        .base_values_mut()
        .register_type::<Boxed<OrderedFloat<f64>>>();
    backend.base_values_mut().register_type::<bool>();
    let string = ColumnTy::Base(types.string);
    let left = table(
        &mut backend,
        "hostile source name; DROP TABLE decoy",
        vec![string, string, string, ColumnTy::Id],
    );
    let right = table(
        &mut backend,
        "renamed right source",
        vec![string, string, ColumnTy::Id],
    );
    let wrong_type_right = table(
        &mut backend,
        "wrong-type-right",
        vec![ColumnTy::Id, string, ColumnTy::Id],
    );
    let hostile = "'); DROP TABLE egglog_function_0; -- 🦆";
    let hostile_value = string_value(&backend, hostile);
    let join = string_value(&backend, "join");
    let decoy = string_value(&backend, "decoy");
    backend.add_values(vec![
        (left, vec![hostile_value, join, join, Value::new(101)]),
        (left, vec![hostile_value, join, decoy, Value::new(102)]),
        (right, vec![join, hostile_value, Value::new(201)]),
        (right, vec![decoy, hostile_value, Value::new(202)]),
        (
            wrong_type_right,
            vec![Value::new(7), hostile_value, Value::new(301)],
        ),
    ])?;

    let (observer, token, rule) = register_observation(
        &mut backend,
        "hostile rule name; check_facts_match",
        vec![
            atom_with_read(
                left,
                ReadMode::All,
                vec![
                    literal(hostile_value, string),
                    var(0, "first-name", string),
                    var(0, "renamed-repeated-name", string),
                    var(1, "left-proof", ColumnTy::Id),
                ],
            ),
            atom_with_read(
                right,
                ReadMode::All,
                vec![
                    var(0, "renamed-shared-name", string),
                    literal(hostile_value, string),
                    var(2, "right-proof", ColumnTy::Id),
                ],
            ),
        ],
    )?;
    assert!(!run(&mut backend, &[rule])?);
    assert!(observer.matched());
    assert_eq!(backend.last_rule_match_counts(), &[1]);
    let sql = backend.storage.latest_rule_sql();
    let materialize = &sql[0];
    assert!(materialize.contains("decode(from_hex('"));
    assert!(materialize.contains("b0.c2 IS NOT DISTINCT FROM b0.c1"));
    assert!(materialize.contains("b1.c0 IS NOT DISTINCT FROM b0.c1"));
    for diagnostic in [
        hostile,
        "hostile source name",
        "renamed right source",
        "hostile rule name",
        "first-name",
        "renamed-repeated-name",
        "renamed-shared-name",
        "check_facts_match",
    ] {
        assert!(!materialize.contains(diagnostic), "leaked `{diagnostic}`");
    }

    let wrong_observer = MatchObserver::new();
    let wrong_token = backend.register_match_observer(wrong_observer.clone());
    let invalid = observation_rule(
        "same-id-wrong-type",
        wrong_token,
        vec![
            atom_with_read(
                left,
                ReadMode::All,
                vec![
                    literal(hostile_value, string),
                    var(50, "string occurrence", string),
                    var(51, "other string", string),
                    var(52, "left proof", ColumnTy::Id),
                ],
            ),
            atom_with_read(
                wrong_type_right,
                ReadMode::All,
                vec![
                    var(50, "same id but Id", ColumnTy::Id),
                    literal(hostile_value, string),
                    var(53, "right proof", ColumnTy::Id),
                ],
            ),
        ],
    );
    let rule_slots = backend.rules.len();
    let error = backend.add_rule(invalid).unwrap_err();
    assert!(
        error.to_string().contains("inconsistent type metadata"),
        "{error:#}"
    );
    assert_eq!(backend.rules.len(), rule_slots);
    assert!(!wrong_observer.matched());

    backend.free_rule(rule);
    backend.free_external_func(token);
    backend.free_external_func(wrong_token);
    Ok(())
}

#[test]
fn match_observation_admission_is_token_owned_exact_and_preallocating() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = register_scalar_types(&mut backend);
    let left = table(
        &mut backend,
        "admission-left",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    let right = table(
        &mut backend,
        "admission-right",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    backend.add_values(vec![
        (left, vec![Value::new(5), Value::new(50)]),
        (right, vec![Value::new(5), Value::new(60)]),
    ])?;
    let observer = MatchObserver::new();
    let token = backend.register_match_observer(observer.clone());
    let base = observation_rule(
        "valid-observer",
        token,
        vec![
            atom_with_read(
                left,
                ReadMode::All,
                vec![
                    var(0, "shared-left", ColumnTy::Id),
                    var(1, "left-proof", ColumnTy::Id),
                ],
            ),
            atom_with_read(
                right,
                ReadMode::All,
                vec![
                    var(0, "shared-right", ColumnTy::Id),
                    var(2, "right-proof", ColumnTy::Id),
                ],
            ),
        ],
    );
    let callback =
        backend.register_external_func(Box::new(egglog_core_relations::make_external_func(
            |_, args: &[Value]| args.is_empty().then_some(Value::new_const(0)),
        )));

    let mut invalid = Vec::<(&str, RuleSpec)>::new();
    let mut spoof = base.clone();
    spoof.name = "ordinary-callback-name-spoof".to_string();
    if let GenericCoreAction::Let(_, _, RuleActionCall::Primitive { id, name, .. }, _) =
        &mut spoof.core.head.0[0]
    {
        *id = callback;
        *name = "check_facts_match".into();
    }
    invalid.push(("ordinary callback spoof", spoof));

    let mut arity = base.clone();
    if let GenericCoreAction::Let(_, _, _, arguments) = &mut arity.core.head.0[0] {
        arguments.push(literal(Value::new(9), ColumnTy::Id));
    }
    invalid.push(("observer arity", arity));

    let mut output = base.clone();
    if let GenericCoreAction::Let(
        _,
        result,
        RuleActionCall::Primitive {
            output: call_output,
            ..
        },
        _,
    ) = &mut output.core.head.0[0]
    {
        *call_output = ColumnTy::Base(types.i64);
        result.ty = ColumnTy::Base(types.i64);
    }
    invalid.push(("observer output", output));

    for read in [ReadMode::Live, ReadMode::Subsumed] {
        let mut wrong_read = base.clone();
        if let RuleBodyCall::Table {
            read: actual_read, ..
        } = &mut wrong_read.core.body.atoms[0].head
        {
            *actual_read = read;
        }
        invalid.push(("observer read mode", wrong_read));
    }

    let mut seminaive = base.clone();
    seminaive.seminaive = true;
    invalid.push(("seminaive flag", seminaive));
    let mut no_decomp = base.clone();
    no_decomp.no_decomp = true;
    invalid.push(("decomposition flag", no_decomp));

    let mut extra_action = base.clone();
    extra_action.core.head.0.push(GenericCoreAction::Panic(
        Span::Panic,
        "must not execute".to_string(),
    ));
    invalid.push(("extra action", extra_action));

    let mut one_atom = base.clone();
    one_atom.core.body.atoms.pop();
    invalid.push(("one body atom", one_atom));
    let mut three_atoms = base.clone();
    three_atoms
        .core
        .body
        .atoms
        .push(three_atoms.core.body.atoms[0].clone());
    invalid.push(("three body atoms", three_atoms));

    let mut primitive_body = base.clone();
    primitive_body.core.body.atoms[0].head = RuleBodyCall::Primitive {
        id: callback,
        name: "body callback".into(),
        output: ColumnTy::Id,
    };
    invalid.push(("primitive body", primitive_body));

    let mut global_body = base.clone();
    global_body.core.body.atoms[0].args[0] = GenericAtomTerm::Global(
        Span::Panic,
        RuleVar {
            id: 99,
            name: "global".into(),
            ty: ColumnTy::Id,
        },
    );
    invalid.push(("global body", global_body));

    let mut wrong_body_arity = base.clone();
    wrong_body_arity.core.body.atoms[0].args.pop();
    invalid.push(("body arity", wrong_body_arity));

    for (case, spec) in invalid {
        let before = backend.rules.len();
        let error = match backend.add_rule(spec) {
            Ok(_) => panic!("{case} unexpectedly admitted"),
            Err(error) => error,
        };
        assert_eq!(backend.rules.len(), before, "{case} allocated a RuleId");
        assert!(
            !error.to_string().is_empty(),
            "{case} returned an empty error"
        );
    }

    let mut diagnostic_mutation = base;
    diagnostic_mutation.name = "renamed/path/check_facts_match".to_string();
    for atom in &mut diagnostic_mutation.core.body.atoms {
        atom.span = Span::Panic;
        for term in &mut atom.args {
            if let GenericAtomTerm::Var(_, variable) = term {
                variable.name = format!("diagnostic-{}", variable.id).into_boxed_str();
            }
        }
    }
    if let GenericCoreAction::Let(_, result, RuleActionCall::Primitive { name, .. }, _) =
        &mut diagnostic_mutation.core.head.0[0]
    {
        result.name = "renamed-result".into();
        *name = "check_facts_match".into();
    }
    let admitted = backend.add_rule(diagnostic_mutation)?;
    assert_eq!(admitted, RuleId::new(0));
    assert!(!run(&mut backend, &[admitted])?);
    assert!(observer.matched());

    backend.free_rule(admitted);
    backend.free_external_func(token);
    backend.free_external_func(callback);
    Ok(())
}

#[test]
fn match_observation_reauth_rejects_callback_reuse_and_same_kind_aba_before_sql() -> Result<()> {
    let mut backend = EGraph::new()?;
    let left = table(
        &mut backend,
        "reauth-left",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    let right = table(
        &mut backend,
        "reauth-right",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    backend.add_values(vec![
        (left, vec![Value::new(3), Value::new(30)]),
        (right, vec![Value::new(3), Value::new(40)]),
    ])?;
    let old_observer = MatchObserver::new();
    let old_token = backend.register_match_observer(old_observer.clone());
    let rule = backend.add_rule(observation_rule(
        "reauth-observer",
        old_token,
        vec![
            atom_with_read(
                left,
                ReadMode::All,
                vec![
                    var(0, "shared-left", ColumnTy::Id),
                    var(1, "left-proof", ColumnTy::Id),
                ],
            ),
            atom_with_read(
                right,
                ReadMode::All,
                vec![
                    var(0, "shared-right", ColumnTy::Id),
                    var(2, "right-proof", ColumnTy::Id),
                ],
            ),
        ],
    ))?;
    let generation = backend.storage.generation()?;
    let fresh = backend.storage.next_fresh_id()?;
    let left_state = scan_state(&backend, left);
    let right_state = scan_state(&backend, right);
    let telemetry = backend.last_rule.clone();
    let trace = backend.storage.latest_rule_sql();

    backend.free_external_func(old_token);
    let callback_invoked = MatchObserver::new();
    let callback_probe = callback_invoked.clone();
    let callback_token = backend.register_external_func(Box::new(
        egglog_core_relations::make_external_func(move |_, _args: &[Value]| {
            callback_probe.mark();
            Some(Value::new_const(0))
        }),
    ));
    assert_eq!(
        callback_token, old_token,
        "freed registry slot was not reused"
    );
    let callback_error = backend
        .run_rules(RuleSetRun {
            name: Some("callback-reuse"),
            rules: &[rule],
        })
        .unwrap_err();
    assert!(
        callback_error
            .to_string()
            .contains("authenticated as an observer"),
        "{callback_error:#}"
    );
    assert!(!callback_invoked.matched());
    assert!(!old_observer.matched());
    assert_eq!(backend.last_rule, telemetry);
    assert_eq!(backend.storage.latest_rule_sql(), trace);
    assert_eq!(backend.storage.generation()?, generation);
    assert_eq!(backend.storage.next_fresh_id()?, fresh);
    assert_eq!(scan_state(&backend, left), left_state);
    assert_eq!(scan_state(&backend, right), right_state);
    assert_eq!(
        backend.rules[rule.rep() as usize]
            .as_ref()
            .unwrap()
            .watermark,
        0
    );
    backend.free_external_func(callback_token);

    let replacement_observer = MatchObserver::new();
    let replacement_token = backend.register_match_observer(replacement_observer.clone());
    assert_eq!(replacement_token, old_token);
    let aba_error = backend
        .run_rules(RuleSetRun {
            name: Some("observer-aba"),
            rules: &[rule],
        })
        .unwrap_err();
    assert!(aba_error.to_string().contains("stale authority epoch"));
    assert!(!old_observer.matched());
    assert!(!replacement_observer.matched());
    assert_eq!(backend.last_rule, telemetry);
    assert_eq!(backend.storage.latest_rule_sql(), trace);
    assert_eq!(backend.storage.generation()?, generation);
    assert_eq!(backend.storage.next_fresh_id()?, fresh);
    assert_eq!(scan_state(&backend, left), left_state);
    assert_eq!(scan_state(&backend, right), right_state);
    backend.storage.with_connection(|connection| {
        let scratch = connection.query_row(
            "SELECT count(*) FROM duckdb_tables() WHERE table_name LIKE 'egglog_rule_stage_%'",
            [],
            |row| row.get::<_, u64>(0),
        )?;
        assert_eq!(scratch, 0);
        Ok(())
    })?;

    backend.free_rule(rule);
    backend.free_external_func(replacement_token);
    Ok(())
}

#[test]
fn match_observation_late_stage_failure_publishes_nothing_and_retry_is_identical() -> Result<()> {
    let mut backend = EGraph::new()?;
    let first = table(
        &mut backend,
        "atomic-first",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    let second = table(
        &mut backend,
        "atomic-second",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    let renamed = table(
        &mut backend,
        "atomic-renamed",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    backend.add_values(vec![
        (first, vec![Value::new(9), Value::new(90)]),
        (second, vec![Value::new(9), Value::new(91)]),
        (renamed, vec![Value::new(9), Value::new(92)]),
    ])?;

    let (sentinel_observer, sentinel_token, sentinel_rule) = register_observation(
        &mut backend,
        "sentinel-miss",
        vec![
            atom_with_read(
                first,
                ReadMode::All,
                vec![
                    literal(Value::new(777), ColumnTy::Id),
                    var(1, "sentinel-left-proof", ColumnTy::Id),
                ],
            ),
            atom_with_read(
                second,
                ReadMode::All,
                vec![
                    literal(Value::new(777), ColumnTy::Id),
                    var(2, "sentinel-right-proof", ColumnTy::Id),
                ],
            ),
        ],
    )?;
    assert!(!run(&mut backend, &[sentinel_rule])?);
    assert!(!sentinel_observer.matched());
    let sentinel_telemetry = backend.last_rule.clone();
    let sentinel_trace = backend.storage.latest_rule_sql();
    assert!(
        sentinel_trace
            .iter()
            .any(|sql| sql.contains("egglog_rule_stage_0_0"))
    );

    let (first_observer, first_token, first_rule) = register_observation(
        &mut backend,
        "atomic-first-observer",
        vec![
            atom_with_read(
                first,
                ReadMode::All,
                vec![
                    var(0, "first-shared", ColumnTy::Id),
                    var(1, "first-left-proof", ColumnTy::Id),
                ],
            ),
            atom_with_read(
                second,
                ReadMode::All,
                vec![
                    var(0, "first-shared-renamed", ColumnTy::Id),
                    var(2, "first-right-proof", ColumnTy::Id),
                ],
            ),
        ],
    )?;
    let (second_observer, second_token, second_rule) = register_observation(
        &mut backend,
        "atomic-second-observer",
        vec![
            atom_with_read(
                first,
                ReadMode::All,
                vec![
                    var(10, "second-shared", ColumnTy::Id),
                    var(11, "second-left-proof", ColumnTy::Id),
                ],
            ),
            atom_with_read(
                renamed,
                ReadMode::All,
                vec![
                    var(10, "second-shared-renamed", ColumnTy::Id),
                    var(12, "second-right-proof", ColumnTy::Id),
                ],
            ),
        ],
    )?;
    let generation = backend.storage.generation()?;
    let fresh = backend.storage.next_fresh_id()?;
    let first_state = scan_state(&backend, first);
    let second_state = scan_state(&backend, second);
    let renamed_state = scan_state(&backend, renamed);
    let physical_name = crate::storage::sql_table(renamed);
    let hidden_name = "egglog_hidden_match_observation_failure";
    backend.storage.with_connection(|connection| {
        connection.execute(
            &format!("ALTER TABLE {physical_name} RENAME TO {hidden_name}"),
            [],
        )?;
        Ok(())
    })?;

    let error = backend
        .run_rules(RuleSetRun {
            name: Some("late-observation-stage-failure"),
            rules: &[first_rule, second_rule],
        })
        .unwrap_err();
    assert!(
        error.to_string().contains(&physical_name),
        "unexpected failure: {error:#}"
    );
    assert!(!first_observer.matched());
    assert!(!second_observer.matched());
    assert_eq!(backend.last_rule, sentinel_telemetry);
    assert_eq!(backend.storage.latest_rule_sql(), sentinel_trace);
    assert_eq!(backend.storage.generation()?, generation);
    assert_eq!(backend.storage.next_fresh_id()?, fresh);
    for rule in [first_rule, second_rule] {
        assert_eq!(
            backend.rules[rule.rep() as usize]
                .as_ref()
                .unwrap()
                .watermark,
            0
        );
    }
    backend.storage.with_connection(|connection| {
        let scratch = connection.query_row(
            "SELECT count(*) FROM duckdb_tables() WHERE table_name LIKE 'egglog_rule_stage_%'",
            [],
            |row| row.get::<_, u64>(0),
        )?;
        assert_eq!(scratch, 0);
        connection.execute(
            &format!("ALTER TABLE {hidden_name} RENAME TO {physical_name}"),
            [],
        )?;
        Ok(())
    })?;
    assert_eq!(scan_state(&backend, first), first_state);
    assert_eq!(scan_state(&backend, second), second_state);
    assert_eq!(scan_state(&backend, renamed), renamed_state);

    assert!(!run(&mut backend, &[first_rule, second_rule])?);
    assert!(first_observer.matched());
    assert!(second_observer.matched());
    assert_eq!(backend.last_rule_match_counts(), &[1, 1]);
    assert_eq!(backend.last_rule_insert_counts(), &[0, 0]);
    assert_eq!(backend.storage.generation()?, generation);
    assert_eq!(backend.storage.next_fresh_id()?, fresh);
    let retry_trace = backend.storage.latest_rule_sql();
    assert!(
        retry_trace
            .iter()
            .any(|sql| sql.contains("egglog_rule_stage_1_0"))
    );
    assert!(
        retry_trace
            .iter()
            .any(|sql| sql.contains("egglog_rule_stage_1_1"))
    );
    assert_eq!(backend.last_rule_statement_count(), retry_trace.len() + 1);
    assert!(retry_trace.iter().all(|sql| {
        !sql.contains("INSERT ")
            && !sql.contains("UPDATE ")
            && !sql.contains("DELETE ")
            && !sql.contains("__subsumed")
            && !sql.contains("__generation")
            && !sql.contains('?')
    }));
    for rule in [first_rule, second_rule] {
        assert_eq!(
            backend.rules[rule.rep() as usize]
                .as_ref()
                .unwrap()
                .watermark,
            generation
        );
    }
    backend.storage.with_connection(|connection| {
        let scratch = connection.query_row(
            "SELECT count(*) FROM duckdb_tables() WHERE table_name LIKE 'egglog_rule_stage_%'",
            [],
            |row| row.get::<_, u64>(0),
        )?;
        assert_eq!(scratch, 0);
        Ok(())
    })?;

    for rule in [sentinel_rule, first_rule, second_rule] {
        backend.free_rule(rule);
    }
    for token in [sentinel_token, first_token, second_token] {
        backend.free_external_func(token);
    }
    Ok(())
}

#[test]
fn source_pinned_pointer_five_way_matches_main_across_delta_transcript() -> Result<()> {
    assert!(POINTER_SOURCE.contains(
        "(function_name f)\n    (function_param f idx x)\n    (call_instruction_fn_target instr f)\n    (call_instruction_arg instr idx v)\n    (= (expr_points_to v) a)"
    ));
    let mut main = egglog_bridge::EGraph::default();
    let expected = pointer_transcript(&mut main)?;
    let mut duckdb = EGraph::new()?;
    let actual = pointer_transcript(&mut duckdb)?;
    assert_eq!(actual, expected);
    assert_eq!(
        actual,
        vec![
            (true, vec![("x1".to_string(), 101)]),
            (true, vec![("x1".to_string(), 101), ("x2".to_string(), 202)]),
            (
                false,
                vec![("x1".to_string(), 101), ("x2".to_string(), 202)]
            ),
        ]
    );
    assert_eq!(duckdb.last_rule_match_counts(), &[0]);
    assert_eq!(duckdb.last_rule_insert_counts(), &[0]);
    assert_eq!(
        duckdb.last_rule_statement_count(),
        5,
        "one rule/no change = generation read + create/count/insert/drop"
    );
    let materialize = &duckdb.storage.latest_rule_sql()[0];
    for atom in 0..5 {
        assert!(
            materialize.contains(&format!("b{atom}.__generation >=")),
            "every body relation must independently admit a fresh delta"
        );
    }
    Ok(())
}

#[test]
fn source_pinned_math_add_swap_matches_main_across_delta_transcript() -> Result<()> {
    assert!(MATH_SOURCE.contains("(rewrite (Add a b) (Add b a))"));
    let mut main = egglog_bridge::EGraph::default();
    let expected = math_transcript(&mut main)?;
    let mut duckdb = EGraph::new()?;
    let actual = math_transcript(&mut duckdb)?;
    assert_eq!(actual, expected);
    assert_eq!(
        actual.iter().map(|entry| entry.0).collect::<Vec<_>>(),
        [true, true, false]
    );
    assert_eq!(actual[0].1.len(), 4);
    assert_eq!(actual[1].1.len(), 6);
    assert_eq!(actual[2].1.len(), 6);
    Ok(())
}

#[test]
fn all_rule_matches_use_a_stable_pre_wave_snapshot() -> Result<()> {
    let mut backend = EGraph::new()?;
    register_scalar_types(&mut backend);
    backend
        .base_values_mut()
        .register_type::<Boxed<OrderedFloat<f64>>>();
    backend.base_values_mut().register_type::<bool>();
    let seed = table(&mut backend, "seed", vec![ColumnTy::Id, ColumnTy::Id]);
    let middle = table(&mut backend, "middle", vec![ColumnTy::Id, ColumnTy::Id]);
    let output = table(&mut backend, "output", vec![ColumnTy::Id, ColumnTy::Id]);
    backend.add_values(vec![(seed, vec![Value::new(7), Value::new(8)])])?;
    let key = var(0, "key", ColumnTy::Id);
    let value = var(1, "value", ColumnTy::Id);
    let to_middle = backend.add_rule(set_rule(
        "seed-to-middle",
        true,
        vec![atom(seed, vec![key.clone(), value.clone()])],
        middle,
        vec![key.clone()],
        vec![value.clone()],
    ))?;
    let to_output = backend.add_rule(set_rule(
        "middle-to-output",
        true,
        vec![atom(middle, vec![key.clone(), value.clone()])],
        output,
        vec![key],
        vec![value],
    ))?;

    assert!(run(&mut backend, &[to_middle, to_output])?);
    assert_eq!(backend.table_size(middle), 1);
    assert_eq!(backend.table_size(output), 0);
    assert!(run(&mut backend, &[to_middle, to_output])?);
    assert_eq!(backend.table_size(output), 1);
    assert!(!run(&mut backend, &[to_middle, to_output])?);
    Ok(())
}

#[test]
fn assert_eq_rule_checks_stage_conflicts_before_ranking_and_recovers() -> Result<()> {
    let mut backend = EGraph::new()?;
    register_scalar_types(&mut backend);
    backend
        .base_values_mut()
        .register_type::<Boxed<OrderedFloat<f64>>>();
    backend.base_values_mut().register_type::<bool>();
    let source = table(
        &mut backend,
        "assert-source",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    let target = table_with_merge(
        &mut backend,
        "assert-target",
        vec![ColumnTy::Id, ColumnTy::Id],
        MergeFn::AssertEq,
    );
    backend.add_values(vec![
        (source, vec![Value::new(1), Value::new(10)]),
        (source, vec![Value::new(2), Value::new(20)]),
    ])?;
    let source_key = var(0, "source-key", ColumnTy::Id);
    let output = var(1, "output", ColumnTy::Id);
    let rule = backend.add_rule(set_rule(
        "assert-eq-stage-conflict",
        true,
        vec![atom(source, vec![source_key, output.clone()])],
        target,
        vec![literal(Value::new(7), ColumnTy::Id)],
        vec![output],
    ))?;
    let generation_before = backend.storage.generation()?;

    let error = backend
        .run_rules(RuleSetRun {
            name: Some("assert-stage-conflict"),
            rules: &[rule],
        })
        .unwrap_err();
    assert!(error.to_string().contains("MergeFn::AssertEq"));
    assert_eq!(backend.table_size(target), 0);
    assert_eq!(backend.storage.generation()?, generation_before);
    assert_eq!(
        backend.rules[rule.rep() as usize]
            .as_ref()
            .unwrap()
            .watermark,
        0
    );
    backend.storage.with_connection(|connection| {
        let stages = connection.query_row(
            "SELECT count(*) FROM duckdb_tables() WHERE table_name LIKE 'egglog_rule_stage_%'",
            [],
            |row| row.get::<_, u64>(0),
        )?;
        assert_eq!(stages, 0);
        Ok(())
    })?;

    backend.clear_table(source);
    backend.add_values(vec![
        (source, vec![Value::new(1), Value::new(10)]),
        (source, vec![Value::new(2), Value::new(10)]),
    ])?;
    assert!(run(&mut backend, &[rule])?);
    assert_eq!(backend.table_size(target), 1);
    assert_eq!(backend.last_rule_insert_counts(), &[1]);
    assert!(!run(&mut backend, &[rule])?);
    assert_eq!(backend.last_rule_insert_counts(), &[0]);
    assert!(
        backend
            .storage
            .latest_rule_sql()
            .iter()
            .all(|statement| !statement.contains('?'))
    );
    Ok(())
}

#[test]
fn later_assert_eq_rule_observes_earlier_scheduled_insert_atomically() -> Result<()> {
    let mut backend = EGraph::new()?;
    register_scalar_types(&mut backend);
    backend
        .base_values_mut()
        .register_type::<Boxed<OrderedFloat<f64>>>();
    backend.base_values_mut().register_type::<bool>();
    let first_source = table(
        &mut backend,
        "first-assert-source",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    let second_source = table(
        &mut backend,
        "second-assert-source",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    let target = table_with_merge(
        &mut backend,
        "scheduled-assert-target",
        vec![ColumnTy::Id, ColumnTy::Id],
        MergeFn::AssertEq,
    );
    backend.add_values(vec![
        (first_source, vec![Value::new(1), Value::new(10)]),
        (second_source, vec![Value::new(2), Value::new(20)]),
    ])?;
    let key = var(0, "source-key", ColumnTy::Id);
    let output = var(1, "output", ColumnTy::Id);
    let first = backend.add_rule(set_rule(
        "first-assert-rule",
        true,
        vec![atom(first_source, vec![key.clone(), output.clone()])],
        target,
        vec![literal(Value::new(7), ColumnTy::Id)],
        vec![output.clone()],
    ))?;
    let second = backend.add_rule(set_rule(
        "second-assert-rule",
        true,
        vec![atom(second_source, vec![key, output.clone()])],
        target,
        vec![literal(Value::new(7), ColumnTy::Id)],
        vec![output],
    ))?;
    let generation_before = backend.storage.generation()?;

    let error = backend
        .run_rules(RuleSetRun {
            name: Some("scheduled-conflict"),
            rules: &[first, second],
        })
        .unwrap_err();
    assert!(error.to_string().contains("AssertEq"));
    assert_eq!(backend.table_size(target), 0);
    assert_eq!(backend.storage.generation()?, generation_before);
    for rule in [first, second] {
        assert_eq!(
            backend.rules[rule.rep() as usize]
                .as_ref()
                .unwrap()
                .watermark,
            0
        );
    }

    backend.clear_table(second_source);
    backend.add_values(vec![(second_source, vec![Value::new(2), Value::new(10)])])?;
    assert!(run(&mut backend, &[first, second])?);
    assert_eq!(backend.last_rule_insert_counts(), &[1, 0]);
    assert_eq!(
        backend.lookup_row(target, &[Value::new(7)]),
        Some(vec![Value::new(7), Value::new(10)])
    );
    assert!(!run(&mut backend, &[first, second])?);
    assert_eq!(backend.last_rule_insert_counts(), &[0, 0]);
    Ok(())
}

#[test]
fn generated_rule_sql_is_literal_only_numeric_named_and_index_free() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = register_scalar_types(&mut backend);
    backend
        .base_values_mut()
        .register_type::<Boxed<OrderedFloat<f64>>>();
    backend.base_values_mut().register_type::<bool>();
    let string = ColumnTy::Base(types.string);
    let unit_ty = ColumnTy::Base(types.unit);
    let source = table(&mut backend, "source user name", vec![string, unit_ty]);
    let target = table(&mut backend, "target user name", vec![string, unit_ty]);
    let hostile = "'); DROP TABLE egglog_function_0; --";
    let hostile_value = string_value(&backend, hostile);
    let unit = unit_value(&backend);
    backend.add_values(vec![(source, vec![hostile_value, unit])])?;
    let rule = backend.add_rule(set_rule(
        "rule name; DROP TABLE anything",
        true,
        vec![atom(
            source,
            vec![literal(hostile_value, string), literal(unit, unit_ty)],
        )],
        target,
        vec![literal(hostile_value, string)],
        vec![literal(unit, unit_ty)],
    ))?;
    assert!(run(&mut backend, &[rule])?);
    let sql = backend.storage.latest_rule_sql();
    assert!(!sql.is_empty());
    assert!(sql.iter().all(|statement| !statement.contains('?')));
    assert!(sql.iter().all(|statement| !statement.contains(hostile)));
    assert!(
        sql.iter()
            .all(|statement| !statement.contains("source user name"))
    );
    assert!(
        sql.iter()
            .all(|statement| !statement.contains("target user name"))
    );
    assert!(sql.iter().all(|statement| !statement.contains("rule name")));
    backend.storage.with_connection(|connection| {
        let indexes = connection.query_row(
            "SELECT count(*) FROM duckdb_indexes() WHERE table_name LIKE 'egglog_function_%'",
            [],
            |row| row.get::<_, u64>(0),
        )?;
        let keys = connection.query_row(
            "SELECT count(*) FROM duckdb_constraints()
             WHERE table_name LIKE 'egglog_function_%'
               AND constraint_type IN ('PRIMARY KEY', 'UNIQUE')",
            [],
            |row| row.get::<_, u64>(0),
        )?;
        assert_eq!(indexes, 0);
        assert_eq!(keys, 0);
        Ok(())
    })?;
    Ok(())
}

fn basic_duckdb_rule_fixture() -> Result<(EGraph, FunctionId, FunctionId, RuleSpec)> {
    let mut backend = EGraph::new()?;
    register_scalar_types(&mut backend);
    backend
        .base_values_mut()
        .register_type::<Boxed<OrderedFloat<f64>>>();
    backend.base_values_mut().register_type::<bool>();
    let source = table(
        &mut backend,
        "unsupported-source",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    let target = table(
        &mut backend,
        "unsupported-target",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    let key = var(0, "key", ColumnTy::Id);
    let value = var(1, "value", ColumnTy::Id);
    let spec = set_rule(
        "valid",
        true,
        vec![atom(source, vec![key.clone(), value.clone()])],
        target,
        vec![key],
        vec![value],
    );
    Ok((backend, source, target, spec))
}

#[test]
fn unsupported_rule_ir_fails_closed_before_allocating_an_id() -> Result<()> {
    let (mut backend, source, _target, valid) = basic_duckdb_rule_fixture()?;
    let next = RuleId::new(0);

    let mut empty_body = valid.clone();
    empty_body.name = "empty-body".to_string();
    empty_body.core.body.atoms.clear();
    assert!(
        backend
            .add_rule(empty_body)
            .unwrap_err()
            .to_string()
            .contains("before binding")
    );

    let mut non_live = valid.clone();
    non_live.name = "non-live".to_string();
    non_live.core.body.atoms[0].head = RuleBodyCall::Table {
        id: source,
        read: ReadMode::All,
    };
    assert!(
        backend
            .add_rule(non_live)
            .unwrap_err()
            .to_string()
            .contains("only Live")
    );

    let mut primitive_body = valid.clone();
    primitive_body.name = "primitive-body".to_string();
    let primitive = backend.new_panic("unreachable primitive".to_string());
    primitive_body.core.body.atoms[0].head = RuleBodyCall::Primitive {
        id: primitive,
        name: "primitive".into(),
        output: ColumnTy::Id,
    };
    let error = backend.add_rule(primitive_body).unwrap_err();
    assert!(
        format!("{error:#}").contains("unauthenticated or callback"),
        "{error:#}"
    );

    let mut unbound = valid.clone();
    unbound.name = "unbound".to_string();
    if let GenericCoreAction::Set(_, _, _, values) = &mut unbound.core.head.0[0] {
        values[0] = var(999, "unbound", ColumnTy::Id);
    }
    assert!(
        backend
            .add_rule(unbound)
            .unwrap_err()
            .to_string()
            .contains("not bound")
    );

    let mut multiple = valid.clone();
    multiple.name = "multiple-actions".to_string();
    let mut invalid_second = multiple.core.head.0[0].clone();
    if let GenericCoreAction::Set(_, _, keys, _) = &mut invalid_second {
        keys[0] = var(999, "unbound-multi", ColumnTy::Id);
    }
    multiple.core.head.0.push(invalid_second);
    assert!(
        backend
            .add_rule(multiple)
            .unwrap_err()
            .to_string()
            .contains("before binding")
    );

    let mut non_set_actions = Vec::new();
    let key = var(0, "key", ColumnTy::Id);
    non_set_actions.push(GenericCoreAction::Let(
        Span::Panic,
        RuleVar {
            id: 3,
            name: "lookup".into(),
            ty: ColumnTy::Id,
        },
        RuleActionCall::Table {
            id: source,
            name: "source".into(),
        },
        vec![key.clone()],
    ));
    non_set_actions.push(GenericCoreAction::LetAtomTerm(
        Span::Panic,
        RuleVar {
            id: 4,
            name: "let".into(),
            ty: ColumnTy::Id,
        },
        key.clone(),
    ));
    non_set_actions.push(GenericCoreAction::Union(Span::Panic, key.clone(), key));
    non_set_actions.push(GenericCoreAction::Panic(
        Span::Panic,
        "unsupported".to_string(),
    ));
    for (index, action) in non_set_actions.into_iter().enumerate() {
        let mut spec = valid.clone();
        spec.name = format!("non-set-{index}");
        spec.core.head.0 = vec![action];
        let error = backend.add_rule(spec).unwrap_err().to_string();
        if index < 2 {
            assert!(error.contains("no durable Set effect"), "{error}");
        } else {
            assert!(error.contains("unsupported action"), "{error}");
        }
    }

    let mut wrong_arity = valid.clone();
    wrong_arity.name = "wrong-arity".to_string();
    wrong_arity.core.body.atoms[0].args.pop();
    assert!(
        backend
            .add_rule(wrong_arity)
            .unwrap_err()
            .to_string()
            .contains("expects 2 arguments")
    );

    let mut wrong_type = valid.clone();
    wrong_type.name = "wrong-type".to_string();
    wrong_type.core.body.atoms[0].args[0] = var(
        0,
        "key",
        ColumnTy::Base(backend.base_values().get_ty::<i64>()),
    );
    assert!(
        backend
            .add_rule(wrong_type)
            .unwrap_err()
            .to_string()
            .contains("expected Id")
    );

    let mut primitive_target = valid.clone();
    primitive_target.name = "primitive-target".to_string();
    if let GenericCoreAction::Set(_, call, _, _) = &mut primitive_target.core.head.0[0] {
        *call = RuleActionCall::Primitive {
            id: primitive,
            name: "primitive".into(),
            output: ColumnTy::Id,
        };
    }
    assert!(
        backend
            .add_rule(primitive_target)
            .unwrap_err()
            .to_string()
            .contains("set a primitive")
    );

    let mut global = valid.clone();
    global.name = "global".to_string();
    global.core.body.atoms[0].args[0] = GenericAtomTerm::Global(
        Span::Panic,
        RuleVar {
            id: 44,
            name: "global".into(),
            ty: ColumnTy::Id,
        },
    );
    assert!(
        backend
            .add_rule(global)
            .unwrap_err()
            .to_string()
            .contains("global")
    );

    let deferred_target = table_with_merge(
        &mut backend,
        "deferred-rule-target",
        vec![ColumnTy::Id, ColumnTy::Id],
        MergeFn::New,
    );
    let mut deferred = valid.clone();
    deferred.name = "deferred-target".to_string();
    if let GenericCoreAction::Set(_, RuleActionCall::Table { id, .. }, _, _) =
        &mut deferred.core.head.0[0]
    {
        *id = deferred_target;
    }
    assert!(
        backend
            .add_rule(deferred)
            .unwrap_err()
            .to_string()
            .contains("incompatible ordered-union target")
    );

    let id = backend.add_rule(valid)?;
    assert_eq!(id, next, "failed admissions must not consume rule ids");
    backend.free_rule(id);
    assert!(
        run(&mut backend, &[id])
            .unwrap_err()
            .to_string()
            .contains("freed")
    );
    Ok(())
}

#[test]
fn later_target_failure_rolls_back_effects_generation_stages_and_watermarks() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = register_scalar_types(&mut backend);
    backend
        .base_values_mut()
        .register_type::<Boxed<OrderedFloat<f64>>>();
    backend.base_values_mut().register_type::<bool>();
    let integer = ColumnTy::Base(types.i64);
    let first_source = table(&mut backend, "first-source", vec![ColumnTy::Id, integer]);
    let second_source = table(&mut backend, "second-source", vec![ColumnTy::Id, integer]);
    let first_target = table(&mut backend, "first-target", vec![ColumnTy::Id, integer]);
    let second_target = table_with_merge(
        &mut backend,
        "second-target",
        vec![ColumnTy::Id, integer],
        MergeFn::AssertEq,
    );
    let positive = i64_value(&backend, 10);
    let negative = i64_value(&backend, -1);
    backend.add_values(vec![
        (first_source, vec![Value::new(1), positive]),
        (second_source, vec![Value::new(2), negative]),
        (second_target, vec![Value::new(2), positive]),
    ])?;
    let key = var(0, "key", ColumnTy::Id);
    let value = var(1, "value", integer);
    let first_rule = backend.add_rule(set_rule(
        "first-rule",
        true,
        vec![atom(first_source, vec![key.clone(), value.clone()])],
        first_target,
        vec![key.clone()],
        vec![value.clone()],
    ))?;
    let second_rule = backend.add_rule(set_rule(
        "second-rule",
        true,
        vec![atom(second_source, vec![key.clone(), value.clone()])],
        second_target,
        vec![key],
        vec![value],
    ))?;
    let generation_before = backend.storage.generation()?;
    let error = backend
        .run_rules(RuleSetRun {
            name: Some("rollback"),
            rules: &[first_rule, second_rule],
        })
        .unwrap_err();
    assert!(error.to_string().contains("MergeFn::AssertEq"));
    assert_eq!(backend.table_size(first_target), 0);
    assert_eq!(backend.table_size(second_target), 1);
    assert_eq!(
        backend.lookup_row(second_target, &[Value::new(2)]),
        Some(vec![Value::new(2), positive])
    );
    assert_eq!(backend.storage.generation()?, generation_before);
    assert_eq!(
        backend.rules[first_rule.rep() as usize]
            .as_ref()
            .unwrap()
            .watermark,
        0
    );
    assert_eq!(
        backend.rules[second_rule.rep() as usize]
            .as_ref()
            .unwrap()
            .watermark,
        0
    );
    backend.storage.with_connection(|connection| {
        let stages = connection.query_row(
            "SELECT count(*) FROM duckdb_tables() WHERE table_name LIKE 'egglog_rule_stage_%'",
            [],
            |row| row.get::<_, u64>(0),
        )?;
        assert_eq!(stages, 0);
        Ok(())
    })?;
    backend.clear_table(second_target);
    assert!(run(&mut backend, &[first_rule, second_rule])?);
    assert_eq!(backend.table_size(first_target), 1);
    assert_eq!(backend.table_size(second_target), 1);
    Ok(())
}

#[test]
fn bounded_descriptive_production_kernel_costs() -> Result<()> {
    fn measure(mut setup: impl FnMut() -> Result<(EGraph, RuleId)>) -> Result<Vec<Duration>> {
        let (mut warmup_backend, warmup_rule) = setup()?;
        run(&mut warmup_backend, &[warmup_rule])?;
        let mut measurements = Vec::new();
        for _ in 0..3 {
            let (mut backend, rule) = setup()?;
            let start = Instant::now();
            run(&mut backend, &[rule])?;
            measurements.push(start.elapsed());
        }
        Ok(measurements)
    }

    let pointer = measure(|| {
        let mut backend = EGraph::new()?;
        let fixture = pointer_fixture(&mut backend)?;
        Ok((backend, fixture.rule))
    })?;
    let math = measure(|| {
        let mut backend = EGraph::new()?;
        let fixture = math_fixture(&mut backend)?;
        Ok((backend, fixture.rule))
    })?;
    if pointer.len() != 3 || math.len() != 3 {
        bail!("bounded measurement protocol did not produce three samples");
    }
    eprintln!("checkpoint-0.5 descriptive rule cost: pointer={pointer:?}, math={math:?}");
    Ok(())
}
