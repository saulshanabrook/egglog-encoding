use std::time::{Duration, Instant};

use anyhow::{Result, bail};
use egglog_ast::{
    core::{
        GenericAtom, GenericAtomTerm, GenericCoreAction, GenericCoreActions, GenericCoreRule, Query,
    },
    span::Span,
};
use egglog_backend_trait::{
    Backend, BaseValueId, ColumnTy, DefaultVal, FunctionConfig, FunctionId, MergeFn, ReadMode,
    RuleActionCall, RuleBodyCall, RuleId, RuleSetRun, RuleSpec, RuleValue, RuleVar, Value,
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
    GenericAtom {
        span: Span::Panic,
        head: RuleBodyCall::Table {
            id,
            read: ReadMode::Live,
        },
        args,
    }
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
            .contains("empty body")
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
    assert!(
        backend
            .add_rule(primitive_body)
            .unwrap_err()
            .to_string()
            .contains("primitive body")
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
    multiple.core.head.0.push(multiple.core.head.0[0].clone());
    assert!(
        backend
            .add_rule(multiple)
            .unwrap_err()
            .to_string()
            .contains("exactly one Set")
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
    non_set_actions.push(GenericCoreAction::Change(
        Span::Panic,
        egglog_ast::generic_ast::Change::Delete,
        RuleActionCall::Table {
            id: source,
            name: "source".into(),
        },
        vec![key.clone()],
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
        assert!(
            backend
                .add_rule(spec)
                .unwrap_err()
                .to_string()
                .contains("unsupported action")
        );
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
            .contains("registered but deferred")
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
