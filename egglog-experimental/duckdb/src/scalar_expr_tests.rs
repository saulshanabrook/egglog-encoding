use anyhow::Result;
use egglog_ast::{
    core::{
        GenericAtom, GenericAtomTerm, GenericCoreAction, GenericCoreActions, GenericCoreRule, Query,
    },
    span::Span,
};
use egglog_backend_trait::{
    Backend, BaseValueId, ColumnTy, DefaultVal, ExternalFunction, ExternalFunctionId,
    FunctionConfig, FunctionId, MergeFn, NativePrimitive, NativeScalarPrimitive, ReadMode,
    RuleActionCall, RuleBodyCall, RuleId, RuleSetRun, RuleSpec, RuleValue, RuleVar, Value,
};
use egglog_core_relations::{Boxed, ExecutionState, make_external_func};
use egglog_numeric_id::NumericId;
use ordered_float::OrderedFloat;

use crate::EGraph;
use crate::scalar_expr::ScalarExpression;
use crate::storage::{ScalarSqlType, sql_table};

type Term = GenericAtomTerm<RuleVar, RuleValue>;
type Action = GenericCoreAction<RuleActionCall, RuleVar, RuleValue>;

#[derive(Clone, Copy)]
struct Types {
    unit: BaseValueId,
    i64: BaseValueId,
    f64: BaseValueId,
    string: BaseValueId,
}

fn register_types(backend: &mut dyn Backend) -> Types {
    backend.base_values_mut().register_type::<bool>();
    Types {
        unit: backend.base_values_mut().register_type::<()>(),
        i64: backend.base_values_mut().register_type::<i64>(),
        f64: backend
            .base_values_mut()
            .register_type::<Boxed<OrderedFloat<f64>>>(),
        string: backend.base_values_mut().register_type::<Boxed<String>>(),
    }
}

fn table(backend: &mut EGraph, name: &str, schema: Vec<ColumnTy>, n_vals: usize) -> FunctionId {
    backend.add_table(FunctionConfig {
        schema,
        n_vals,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::AssertEq,
        name: name.to_string(),
        can_subsume: false,
    })
}

fn var(id: u32, name: &str, ty: ColumnTy) -> RuleVar {
    RuleVar {
        id,
        name: name.into(),
        ty,
    }
}

fn variable(variable: RuleVar) -> Term {
    GenericAtomTerm::Var(Span::Panic, variable)
}

fn literal(value: Value, ty: ColumnTy) -> Term {
    GenericAtomTerm::Literal(Span::Panic, RuleValue { value, ty })
}

fn table_atom(
    target: FunctionId,
    arguments: Vec<Term>,
) -> GenericAtom<RuleBodyCall, RuleVar, RuleValue> {
    GenericAtom {
        span: Span::Panic,
        head: RuleBodyCall::Table {
            id: target,
            read: ReadMode::Live,
        },
        args: arguments,
    }
}

fn primitive_atom(
    token: ExternalFunctionId,
    diagnostic_name: &str,
    output: ColumnTy,
    arguments: Vec<Term>,
) -> GenericAtom<RuleBodyCall, RuleVar, RuleValue> {
    GenericAtom {
        span: Span::Panic,
        head: RuleBodyCall::Primitive {
            id: token,
            name: diagnostic_name.into(),
            output,
        },
        args: arguments,
    }
}

fn primitive_let(
    binding: RuleVar,
    token: ExternalFunctionId,
    diagnostic_name: &str,
    output: ColumnTy,
    arguments: Vec<Term>,
) -> Action {
    GenericCoreAction::Let(
        Span::Panic,
        binding,
        RuleActionCall::Primitive {
            id: token,
            name: diagnostic_name.into(),
            output,
        },
        arguments,
    )
}

fn set_action(target: FunctionId, keys: Vec<Term>, values: Vec<Term>) -> Action {
    GenericCoreAction::Set(
        Span::Panic,
        RuleActionCall::Table {
            id: target,
            name: "hostile table diagnostic '); --".into(),
        },
        keys,
        values,
    )
}

fn rule(
    name: &str,
    seminaive: bool,
    body: Vec<GenericAtom<RuleBodyCall, RuleVar, RuleValue>>,
    head: Vec<Action>,
) -> RuleSpec {
    RuleSpec {
        name: name.to_string(),
        seminaive,
        no_decomp: false,
        core: GenericCoreRule {
            span: Span::Panic,
            body: Query { atoms: body },
            head: GenericCoreActions::new(head),
        },
    }
}

fn run(backend: &mut EGraph, rules: &[RuleId]) -> Result<bool> {
    Ok(backend
        .run_rules(RuleSetRun {
            name: Some("authenticated scalar expression test"),
            rules,
        })?
        .changed())
}

#[derive(Clone, Copy, Debug)]
enum Input {
    Id(u32),
    I64(i64),
    F64(f64),
    String(&'static str),
}

impl Input {
    fn ty(self, types: Types) -> ColumnTy {
        match self {
            Self::Id(_) => ColumnTy::Id,
            Self::I64(_) => ColumnTy::Base(types.i64),
            Self::F64(_) => ColumnTy::Base(types.f64),
            Self::String(_) => ColumnTy::Base(types.string),
        }
    }

    fn value(self, backend: &dyn Backend) -> Value {
        match self {
            Self::Id(value) => Value::new(value),
            Self::I64(value) => backend.base_values().get(value),
            Self::F64(value) => backend.base_values().get(Boxed::new(OrderedFloat(value))),
            Self::String(value) => backend.base_values().get(Boxed::new(value.to_string())),
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
enum Observed {
    Id(u32),
    I64(i64),
    Unit,
}

fn typed_output(primitive: NativeScalarPrimitive, types: Types) -> ColumnTy {
    match primitive {
        NativeScalarPrimitive::I64Add
        | NativeScalarPrimitive::I64Sub
        | NativeScalarPrimitive::I64Mul
        | NativeScalarPrimitive::I64Div
        | NativeScalarPrimitive::I64Rem
        | NativeScalarPrimitive::I64BitAnd
        | NativeScalarPrimitive::I64Min
        | NativeScalarPrimitive::I64Max => ColumnTy::Base(types.i64),
        NativeScalarPrimitive::I64Ge
        | NativeScalarPrimitive::I64Lt
        | NativeScalarPrimitive::F64Gt
        | NativeScalarPrimitive::F64Lt => ColumnTy::Base(types.unit),
        _ => panic!("test helper does not support native scalar descriptor {primitive:?}"),
    }
}

fn scalar_fallback(primitive: NativeScalarPrimitive) -> Box<dyn ExternalFunction + 'static> {
    Box::new(make_external_func(
        move |state: &mut ExecutionState<'_>, args: &[Value]| {
            let [left, right] = args else {
                return None;
            };
            match primitive {
                NativeScalarPrimitive::I64Add
                | NativeScalarPrimitive::I64Sub
                | NativeScalarPrimitive::I64Mul
                | NativeScalarPrimitive::I64Div
                | NativeScalarPrimitive::I64Rem
                | NativeScalarPrimitive::I64BitAnd
                | NativeScalarPrimitive::I64Min
                | NativeScalarPrimitive::I64Max
                | NativeScalarPrimitive::I64Ge
                | NativeScalarPrimitive::I64Lt => {
                    let left = state.base_values().unwrap::<i64>(*left);
                    let right = state.base_values().unwrap::<i64>(*right);
                    match primitive {
                        NativeScalarPrimitive::I64Add => left
                            .checked_add(right)
                            .map(|value| state.base_values().get(value)),
                        NativeScalarPrimitive::I64Sub => left
                            .checked_sub(right)
                            .map(|value| state.base_values().get(value)),
                        NativeScalarPrimitive::I64Mul => left
                            .checked_mul(right)
                            .map(|value| state.base_values().get(value)),
                        NativeScalarPrimitive::I64Div => left
                            .checked_div(right)
                            .map(|value| state.base_values().get(value)),
                        NativeScalarPrimitive::I64Rem => left
                            .checked_rem(right)
                            .map(|value| state.base_values().get(value)),
                        NativeScalarPrimitive::I64BitAnd => {
                            Some(state.base_values().get(left & right))
                        }
                        NativeScalarPrimitive::I64Min => {
                            Some(state.base_values().get(left.min(right)))
                        }
                        NativeScalarPrimitive::I64Max => {
                            Some(state.base_values().get(left.max(right)))
                        }
                        NativeScalarPrimitive::I64Ge => {
                            (left >= right).then(|| state.base_values().get::<()>(()))
                        }
                        NativeScalarPrimitive::I64Lt => {
                            (left < right).then(|| state.base_values().get::<()>(()))
                        }
                        NativeScalarPrimitive::F64Gt | NativeScalarPrimitive::F64Lt => {
                            unreachable!()
                        }
                        _ => {
                            panic!(
                                "test helper does not support native scalar descriptor {primitive:?}"
                            )
                        }
                    }
                }
                NativeScalarPrimitive::F64Gt | NativeScalarPrimitive::F64Lt => {
                    let left = state
                        .base_values()
                        .unwrap::<Boxed<OrderedFloat<f64>>>(*left);
                    let right = state
                        .base_values()
                        .unwrap::<Boxed<OrderedFloat<f64>>>(*right);
                    let defined = if primitive == NativeScalarPrimitive::F64Gt {
                        left > right
                    } else {
                        left < right
                    };
                    defined.then(|| state.base_values().get::<()>(()))
                }
                _ => panic!("test helper does not support native scalar descriptor {primitive:?}"),
            }
        },
    ))
}

fn observe_reference(
    backend: &dyn Backend,
    output: ColumnTy,
    value: Option<Value>,
) -> Option<Observed> {
    value.map(
        |value| match ScalarSqlType::from_column(backend.base_values(), output).unwrap() {
            ScalarSqlType::Id => Observed::Id(value.rep()),
            ScalarSqlType::I64 => Observed::I64(backend.base_values().unwrap::<i64>(value)),
            ScalarSqlType::Unit => {
                backend.base_values().unwrap::<()>(value);
                Observed::Unit
            }
            other => panic!("unexpected scalar test output {other:?}"),
        },
    )
}

fn observe_sql(
    backend: &EGraph,
    output: ColumnTy,
    value_sql: &str,
    defined_sql: &str,
) -> Result<Option<Observed>> {
    let output = ScalarSqlType::from_column(backend.base_values(), output)?;
    backend.storage.with_connection(|connection| {
        let sql = format!("SELECT {value_sql}, {defined_sql}");
        let (defined, value) = connection.query_row(&sql, [], |row| {
            let defined = row.get::<_, bool>(1)?;
            let value = match output {
                ScalarSqlType::Id => Observed::Id(row.get::<_, u32>(0)?),
                ScalarSqlType::I64 => Observed::I64(row.get::<_, i64>(0)?),
                ScalarSqlType::Unit => {
                    assert!(row.get::<_, bool>(0)?);
                    Observed::Unit
                }
                other => panic!("unexpected scalar SQL output {other:?}"),
            };
            Ok((defined, value))
        })?;
        Ok(defined.then_some(value))
    })
}

fn assert_closed_sql(sql: &str) {
    let upper = sql.to_ascii_uppercase();
    for forbidden in [
        "NULL",
        "TRY",
        "LEAST",
        "GREATEST",
        "CREATE FUNCTION",
        "UDF",
        "APPENDER",
        "ARROW",
        "UNSAFE",
        "FFI",
    ] {
        assert!(!upper.contains(forbidden), "forbidden {forbidden} in {sql}");
    }
    assert!(!sql.contains('?'), "parameter marker in {sql}");
    assert!(!sql.contains("diagnostic"));
}

fn compare_typed(primitive: NativeScalarPrimitive, cases: &[(Input, Input)]) -> Result<()> {
    let mut reference = egglog_bridge::EGraph::default();
    let reference_types = register_types(&mut reference);
    let reference_token = Backend::register_native_scalar_primitive(
        &mut reference,
        primitive,
        scalar_fallback(primitive),
    );

    let mut duckdb = EGraph::new()?;
    let duckdb_types = register_types(&mut duckdb);
    let duckdb_token = Backend::register_native_scalar_primitive(
        &mut duckdb,
        primitive,
        scalar_fallback(primitive),
    );
    let output = typed_output(primitive, duckdb_types);

    for &(left, right) in cases {
        let inputs = [left.ty(duckdb_types), right.ty(duckdb_types)];
        let expression = ScalarExpression::authenticate(
            duckdb.base_values(),
            &duckdb.native_primitives,
            &duckdb.native_scalar_primitives,
            duckdb_token,
            &inputs,
            output,
        )?;
        let input_sql = [left, right]
            .into_iter()
            .map(|input| {
                let ty = input.ty(duckdb_types);
                ScalarSqlType::from_column(duckdb.base_values(), ty).and_then(|scalar| {
                    scalar.sql_literal(duckdb.base_values(), input.value(&duckdb))
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let rendered = expression.render(&input_sql);
        assert_closed_sql(&rendered.value);
        assert_closed_sql(&rendered.defined);
        match primitive {
            NativeScalarPrimitive::I64Add
            | NativeScalarPrimitive::I64Sub
            | NativeScalarPrimitive::I64Mul => {
                assert!(rendered.value.contains("HUGEINT"));
                assert!(rendered.value.contains("CASE WHEN"));
                assert!(rendered.value.contains("AS BIGINT"));
                assert!(rendered.defined.contains("-9223372036854775808"));
                assert!(rendered.defined.contains("9223372036854775807"));
            }
            NativeScalarPrimitive::I64Div | NativeScalarPrimitive::I64Rem => {
                assert!(rendered.defined.contains("CAST('0' AS BIGINT)"));
                assert!(rendered.defined.contains("CAST('-1' AS BIGINT)"));
                assert!(rendered.value.contains("CASE WHEN"));
                assert!(rendered.value.contains("CAST('1' AS HUGEINT)"));
            }
            NativeScalarPrimitive::F64Gt | NativeScalarPrimitive::F64Lt => {
                assert!(rendered.defined.contains("isnan"));
            }
            NativeScalarPrimitive::I64BitAnd
            | NativeScalarPrimitive::I64Min
            | NativeScalarPrimitive::I64Max
            | NativeScalarPrimitive::I64Ge
            | NativeScalarPrimitive::I64Lt => {}
            _ => panic!("test helper does not support native scalar descriptor {primitive:?}"),
        }

        let reference_args = [left.value(&reference), right.value(&reference)];
        let reference_result = reference.with_execution_state(|state| {
            state.call_external_func(reference_token, &reference_args)
        });
        let expected = observe_reference(
            &reference,
            typed_output(primitive, reference_types),
            reference_result,
        );
        let actual = observe_sql(&duckdb, output, &rendered.value, &rendered.defined)?;
        assert_eq!(
            actual, expected,
            "{primitive:?} disagreed for {left:?}, {right:?}; SQL: {rendered:?}"
        );
    }
    Ok(())
}

fn compare_raw(primitive: NativePrimitive, cases: &[(Input, Input)]) -> Result<()> {
    let mut reference = egglog_bridge::EGraph::default();
    let reference_types = register_types(&mut reference);
    let reference_token = Backend::register_native_primitive(&mut reference, primitive);

    let mut duckdb = EGraph::new()?;
    let duckdb_types = register_types(&mut duckdb);
    let duckdb_token = Backend::register_native_primitive(&mut duckdb, primitive);

    for &(left, right) in cases {
        let output = if matches!(
            primitive,
            NativePrimitive::OrderingMin | NativePrimitive::OrderingMax
        ) {
            ColumnTy::Id
        } else {
            ColumnTy::Base(duckdb_types.unit)
        };
        let inputs = [left.ty(duckdb_types), right.ty(duckdb_types)];
        let expression = ScalarExpression::authenticate(
            duckdb.base_values(),
            &duckdb.native_primitives,
            &duckdb.native_scalar_primitives,
            duckdb_token,
            &inputs,
            output,
        )?;
        let input_sql = [left, right]
            .into_iter()
            .map(|input| {
                let ty = input.ty(duckdb_types);
                ScalarSqlType::from_column(duckdb.base_values(), ty).and_then(|scalar| {
                    scalar.sql_literal(duckdb.base_values(), input.value(&duckdb))
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let rendered = expression.render(&input_sql);
        assert_closed_sql(&rendered.value);
        assert_closed_sql(&rendered.defined);
        if primitive == NativePrimitive::ValueNeq && matches!(left, Input::F64(_)) {
            assert!(rendered.defined.contains("isnan"));
        }

        let reference_args = [left.value(&reference), right.value(&reference)];
        let reference_result = reference.with_execution_state(|state| {
            state.call_external_func(reference_token, &reference_args)
        });
        let reference_output = if output == ColumnTy::Id {
            ColumnTy::Id
        } else {
            ColumnTy::Base(reference_types.unit)
        };
        let expected = observe_reference(&reference, reference_output, reference_result);
        let actual = observe_sql(&duckdb, output, &rendered.value, &rendered.defined)?;
        assert_eq!(
            actual, expected,
            "{primitive:?} disagreed for {left:?}, {right:?}; SQL: {rendered:?}"
        );
        if matches!(
            primitive,
            NativePrimitive::OrderingMin | NativePrimitive::OrderingMax
        ) {
            assert!(rendered.value.contains("CASE WHEN"));
            assert!(rendered.value.contains("ELSE"));
            assert!(
                rendered.value.contains(&format!("ELSE ({})", input_sql[1])),
                "raw ordering must choose the right expression on ties: {}",
                rendered.value
            );
        }
    }
    Ok(())
}

#[test]
fn every_reached_scalar_matches_reference_at_semantic_edges() -> Result<()> {
    use Input::{F64, I64, Id, String as S};
    use NativeScalarPrimitive::*;

    compare_typed(
        I64Add,
        &[
            (I64(2), I64(3)),
            (I64(i64::MAX), I64(0)),
            (I64(i64::MAX), I64(1)),
            (I64(i64::MIN), I64(-1)),
        ],
    )?;
    compare_typed(
        I64Sub,
        &[
            (I64(2), I64(3)),
            (I64(i64::MIN), I64(1)),
            (I64(i64::MAX), I64(-1)),
        ],
    )?;
    compare_typed(
        I64Mul,
        &[
            (I64(-7), I64(3)),
            (I64(i64::MAX), I64(2)),
            (I64(i64::MIN), I64(-1)),
            (I64(i64::MIN), I64(1)),
        ],
    )?;
    compare_typed(
        I64Div,
        &[
            (I64(-7), I64(3)),
            (I64(7), I64(-3)),
            (I64(-7), I64(-3)),
            (I64(7), I64(0)),
            (I64(i64::MIN), I64(-1)),
        ],
    )?;
    compare_typed(
        I64Rem,
        &[
            (I64(-7), I64(3)),
            (I64(7), I64(-3)),
            (I64(-7), I64(-3)),
            (I64(7), I64(0)),
            (I64(i64::MIN), I64(-1)),
        ],
    )?;
    compare_typed(I64BitAnd, &[(I64(-5), I64(3)), (I64(-1), I64(-8))])?;
    compare_typed(I64Min, &[(I64(-5), I64(3)), (I64(7), I64(7))])?;
    compare_typed(I64Max, &[(I64(-5), I64(3)), (I64(7), I64(7))])?;
    compare_typed(I64Ge, &[(I64(3), I64(3)), (I64(-2), I64(1))])?;
    compare_typed(I64Lt, &[(I64(-2), I64(1)), (I64(3), I64(3))])?;

    let nan = f64::NAN;
    let other_nan = f64::from_bits(0x7ff8_0000_0000_0042);
    compare_typed(
        F64Gt,
        &[
            (F64(nan), F64(1.0)),
            (F64(1.0), F64(nan)),
            (F64(nan), F64(nan)),
            (F64(nan), F64(other_nan)),
            (F64(f64::INFINITY), F64(f64::NEG_INFINITY)),
            (F64(-0.0), F64(0.0)),
        ],
    )?;
    compare_typed(
        F64Lt,
        &[
            (F64(nan), F64(1.0)),
            (F64(1.0), F64(nan)),
            (F64(nan), F64(nan)),
            (F64(other_nan), F64(nan)),
            (F64(f64::NEG_INFINITY), F64(f64::INFINITY)),
            (F64(-0.0), F64(0.0)),
        ],
    )?;

    compare_raw(
        NativePrimitive::ValueNeq,
        &[
            (Id(1), Id(2)),
            (Id(3), Id(3)),
            (I64(-1), I64(1)),
            (I64(9), I64(9)),
            (F64(nan), F64(nan)),
            (F64(nan), F64(other_nan)),
            (F64(nan), F64(f64::INFINITY)),
            (F64(-0.0), F64(0.0)),
            (S("same"), S("same")),
            (S("left"), S("right")),
            (S("Case"), S("case")),
            (S("quoted ' Δ🙂"), S("quoted ' Δ🙂")),
            (S("quoted ' Δ🙂"), S("quoted ' δ🙂")),
        ],
    )?;
    compare_raw(
        NativePrimitive::OrderingMin,
        &[(Id(9), Id(4)), (Id(4), Id(9)), (Id(7), Id(7))],
    )?;
    compare_raw(
        NativePrimitive::OrderingMax,
        &[(Id(9), Id(4)), (Id(4), Id(9)), (Id(7), Id(7))],
    )?;
    Ok(())
}

#[test]
fn scalar_body_binds_checks_chains_and_prunes_undefined_lanes() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = register_types(&mut backend);
    let i64_ty = ColumnTy::Base(types.i64);
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let source = table(
        &mut backend,
        "scalar body source",
        vec![i64_ty, i64_ty, i64_ty, i64_ty, unit_ty],
        1,
    );
    let target = table(&mut backend, "scalar body target", vec![i64_ty, unit_ty], 1);
    let rows = [
        (2, 3, 5, 10),
        (2, 4, 7, 10),
        (i64::MAX, 1, 0, 10),
        (8, 3, 11, 12),
    ];
    backend.add_values(
        rows.into_iter()
            .map(|(left, right, expected, limit)| {
                (
                    source,
                    vec![
                        backend.base_values().get(left),
                        backend.base_values().get(right),
                        backend.base_values().get(expected),
                        backend.base_values().get(limit),
                        unit,
                    ],
                )
            })
            .collect(),
    )?;

    let add = backend.register_native_scalar_primitive(
        NativeScalarPrimitive::I64Add,
        scalar_fallback(NativeScalarPrimitive::I64Add),
    );
    let lt = backend.register_native_scalar_primitive(
        NativeScalarPrimitive::I64Lt,
        scalar_fallback(NativeScalarPrimitive::I64Lt),
    );
    let left = var(0, "hostile left diagnostic", i64_ty);
    let right = var(1, "hostile right diagnostic", i64_ty);
    let expected = var(2, "hostile expected diagnostic", i64_ty);
    let limit = var(3, "hostile limit diagnostic", i64_ty);
    let sum = var(4, "hostile sum diagnostic", i64_ty);
    let chained = var(5, "hostile chained diagnostic", i64_ty);
    let one = backend.base_values().get(1_i64);
    // Each use of an existing SSA id below deliberately has a different
    // display name. Identity is the id/type pair across table bindings,
    // primitive body inputs and outputs, and action inputs.
    let id = backend.add_rule(rule(
        "body diagnostic must not enter SQL",
        true,
        vec![
            table_atom(
                source,
                vec![
                    variable(left.clone()),
                    variable(right.clone()),
                    variable(expected.clone()),
                    variable(limit.clone()),
                    literal(unit, unit_ty),
                ],
            ),
            primitive_atom(
                add,
                "spoofed + binding diagnostic",
                i64_ty,
                vec![
                    variable(var(0, "renamed left scalar input", i64_ty)),
                    variable(var(1, "renamed right scalar input", i64_ty)),
                    variable(sum.clone()),
                ],
            ),
            primitive_atom(
                add,
                "spoofed + bound-output diagnostic",
                i64_ty,
                vec![
                    variable(var(0, "renamed left bound-output input", i64_ty)),
                    variable(var(1, "renamed right bound-output input", i64_ty)),
                    variable(var(2, "renamed expected scalar output", i64_ty)),
                ],
            ),
            primitive_atom(
                add,
                "spoofed + chain diagnostic",
                i64_ty,
                vec![
                    variable(var(4, "renamed sum scalar input", i64_ty)),
                    literal(one, i64_ty),
                    variable(chained.clone()),
                ],
            ),
            primitive_atom(
                lt,
                "spoofed < predicate diagnostic",
                unit_ty,
                vec![
                    variable(var(5, "renamed chained predicate input", i64_ty)),
                    variable(var(3, "renamed limit predicate input", i64_ty)),
                    literal(unit, unit_ty),
                ],
            ),
        ],
        vec![set_action(
            target,
            vec![variable(var(5, "renamed chained action input", i64_ty))],
            vec![literal(unit, unit_ty)],
        )],
    ))?;

    assert!(run(&mut backend, &[id])?);
    assert_eq!(backend.table_size(target), 1);
    assert_eq!(
        backend.lookup_id(target, &[backend.base_values().get(6_i64)]),
        Some(unit)
    );
    let match_sql = backend
        .storage
        .latest_rule_sql()
        .into_iter()
        .find(|sql| sql.starts_with("CREATE TEMP TABLE egglog_scalar_match_"))
        .expect("scalar body is fused into one match CTAS");
    assert!(match_sql.contains("HUGEINT"));
    assert!(match_sql.contains("AS b4"));
    assert_closed_sql(&match_sql);
    assert!(!match_sql.contains("diagnostic"));

    assert!(!run(&mut backend, &[id])?);
    assert_eq!(backend.last_rule_match_counts(), &[0]);
    assert_eq!(backend.table_size(target), 1);
    Ok(())
}

#[test]
fn empty_body_scalar_actions_chain_and_fire_once() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = register_types(&mut backend);
    let i64_ty = ColumnTy::Base(types.i64);
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let target = table(
        &mut backend,
        "empty body scalar target",
        vec![i64_ty, unit_ty],
        1,
    );
    let add = backend.register_native_scalar_primitive(
        NativeScalarPrimitive::I64Add,
        scalar_fallback(NativeScalarPrimitive::I64Add),
    );
    let mul = backend.register_native_scalar_primitive(
        NativeScalarPrimitive::I64Mul,
        scalar_fallback(NativeScalarPrimitive::I64Mul),
    );
    let sum = var(0, "empty body sum", i64_ty);
    let product = var(1, "empty body product", i64_ty);
    let two = backend.base_values().get(2_i64);
    let three = backend.base_values().get(3_i64);
    let four = backend.base_values().get(4_i64);
    let id = backend.add_rule(rule(
        "empty body scalar action chain",
        true,
        vec![],
        vec![
            primitive_let(
                sum.clone(),
                add,
                "name is not + authority",
                i64_ty,
                vec![literal(two, i64_ty), literal(three, i64_ty)],
            ),
            primitive_let(
                product.clone(),
                mul,
                "name is not * authority",
                i64_ty,
                vec![variable(sum), literal(four, i64_ty)],
            ),
            set_action(
                target,
                vec![variable(product)],
                vec![literal(unit, unit_ty)],
            ),
        ],
    ))?;
    let plan = backend.rules[id.rep() as usize]
        .as_ref()
        .expect("registered rule")
        .plan
        .scalar_action()
        .expect("scalar plan");
    assert_eq!(plan.slots().len(), 2);
    assert_eq!(plan.action_count(), 3);

    assert!(run(&mut backend, &[id])?);
    assert_eq!(backend.storage.next_fresh_id()?, 0);
    assert_eq!(
        backend.lookup_id(target, &[backend.base_values().get(20_i64)]),
        Some(unit)
    );
    assert_eq!(backend.last_rule_match_counts(), &[1]);
    assert_eq!(backend.last_rule_insert_counts(), &[1]);
    assert_eq!(
        backend
            .storage
            .latest_rule_sql()
            .iter()
            .filter(|sql| sql.starts_with("CREATE TEMP TABLE egglog_scalar_slot_"))
            .count(),
        2
    );
    assert!(!run(&mut backend, &[id])?);
    assert_eq!(backend.storage.next_fresh_id()?, 0);
    Ok(())
}

#[test]
fn primitive_only_body_keeps_projection_and_definedness_without_from() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = register_types(&mut backend);
    let i64_ty = ColumnTy::Base(types.i64);
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let target = table(
        &mut backend,
        "primitive-only body target",
        vec![i64_ty, unit_ty],
        1,
    );
    let overflow_target = table(
        &mut backend,
        "primitive-only overflow target",
        vec![i64_ty, unit_ty],
        1,
    );
    let add = backend.register_native_scalar_primitive(
        NativeScalarPrimitive::I64Add,
        scalar_fallback(NativeScalarPrimitive::I64Add),
    );
    let two = backend.base_values().get(2_i64);
    let three = backend.base_values().get(3_i64);
    let max = backend.base_values().get(i64::MAX);
    let one = backend.base_values().get(1_i64);
    let output = var(0, "literal body output", i64_ty);
    let valid = backend.add_rule(rule(
        "literal-only scalar body",
        true,
        vec![primitive_atom(
            add,
            "literal-only Add diagnostic",
            i64_ty,
            vec![
                literal(two, i64_ty),
                literal(three, i64_ty),
                variable(output.clone()),
            ],
        )],
        vec![set_action(
            target,
            vec![variable(output)],
            vec![literal(unit, unit_ty)],
        )],
    ))?;
    let overflow = var(1, "literal overflow output", i64_ty);
    let invalid = backend.add_rule(rule(
        "undefined literal-only scalar body",
        true,
        vec![primitive_atom(
            add,
            "literal-only overflowing Add diagnostic",
            i64_ty,
            vec![
                literal(max, i64_ty),
                literal(one, i64_ty),
                variable(overflow.clone()),
            ],
        )],
        vec![set_action(
            overflow_target,
            vec![variable(overflow)],
            vec![literal(unit, unit_ty)],
        )],
    ))?;

    let valid_plan = backend.rules[valid.rep() as usize]
        .as_ref()
        .expect("registered rule")
        .plan
        .scalar_action()
        .expect("scalar plan");
    let sql = valid_plan.materialize_match_sql("egglog_scalar_literal_body", 0);
    assert!(sql.contains(" AS b0"));
    assert!(sql.contains("HUGEINT"));
    assert!(!sql.contains(" FROM "));
    assert_closed_sql(&sql);

    assert!(run(&mut backend, &[valid, invalid])?);
    assert_eq!(backend.last_rule_match_counts(), &[1, 0]);
    assert_eq!(
        backend.lookup_id(target, &[backend.base_values().get(5_i64)]),
        Some(unit)
    );
    assert_eq!(backend.table_size(overflow_target), 0);
    assert!(!run(&mut backend, &[valid, invalid])?);
    assert_eq!(backend.last_rule_match_counts(), &[0, 0]);
    Ok(())
}

#[test]
fn undefined_action_rolls_back_before_fresh_and_retries_action_major() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = register_types(&mut backend);
    let i64_ty = ColumnTy::Base(types.i64);
    let string_ty = ColumnTy::Base(types.string);
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let source = table(
        &mut backend,
        "undefined action source",
        vec![i64_ty, i64_ty, unit_ty],
        1,
    );
    let target = table(
        &mut backend,
        "undefined action target",
        vec![ColumnTy::Id, ColumnTy::Id, i64_ty, unit_ty],
        1,
    );
    backend.add_values(vec![
        (
            source,
            vec![
                backend.base_values().get(-6_i64),
                backend.base_values().get(0_i64),
                unit,
            ],
        ),
        (
            source,
            vec![
                backend.base_values().get(8_i64),
                backend.base_values().get(0_i64),
                unit,
            ],
        ),
    ])?;
    let fresh = backend.register_get_fresh();
    let div = backend.register_native_scalar_primitive(
        NativeScalarPrimitive::I64Div,
        scalar_fallback(NativeScalarPrimitive::I64Div),
    );
    let label = backend
        .base_values()
        .get(Boxed::new("scalar rollback fresh label".to_string()));
    let left = var(0, "rollback lhs", i64_ty);
    let right = var(1, "rollback rhs", i64_ty);
    let first = var(2, "first fresh", ColumnTy::Id);
    let quotient = var(3, "quotient", i64_ty);
    let second = var(4, "second fresh", ColumnTy::Id);
    let id = backend.add_rule(rule(
        "undefined scalar action rollback and retry",
        true,
        vec![table_atom(
            source,
            vec![
                variable(left.clone()),
                variable(right.clone()),
                literal(unit, unit_ty),
            ],
        )],
        vec![
            primitive_let(
                first.clone(),
                fresh,
                "fresh diagnostic before expression",
                ColumnTy::Id,
                vec![literal(label, string_ty)],
            ),
            primitive_let(
                quotient.clone(),
                div,
                "division diagnostic",
                i64_ty,
                vec![variable(left), variable(right)],
            ),
            primitive_let(
                second.clone(),
                fresh,
                "fresh diagnostic after expression",
                ColumnTy::Id,
                vec![literal(label, string_ty)],
            ),
            set_action(
                target,
                vec![variable(first), variable(second), variable(quotient)],
                vec![literal(unit, unit_ty)],
            ),
        ],
    ))?;

    let plan = backend.rules[id.rep() as usize]
        .as_ref()
        .expect("registered rule")
        .plan
        .scalar_action()
        .expect("scalar plan");
    let preflight = plan
        .slot_preflight_sql("egglog_scalar_preflight_input", 1)
        .expect("division is fallible");
    assert!(preflight.starts_with("SELECT EXISTS"));
    assert!(preflight.contains("CAST('0' AS BIGINT)"));
    assert!(preflight.contains("CAST('-1' AS BIGINT)"));
    assert_closed_sql(&preflight);
    let expression_ctas = plan.materialize_slot_sql(
        "egglog_scalar_preflight_input",
        "egglog_scalar_preflight_output",
        1,
        0,
        2,
        None,
    );
    assert!(expression_ctas.contains(" // "));
    assert!(expression_ctas.contains("CASE WHEN"));
    assert!(expression_ctas.contains("CAST('1' AS HUGEINT)"));
    assert_closed_sql(&expression_ctas);

    let before_generation = backend.storage.generation()?;
    let before_fresh = backend.storage.next_fresh_id()?;
    let before_trace = backend.storage.latest_rule_sql();
    let before_statement_count = backend.last_rule_statement_count();
    let before_matches = backend.last_rule_match_counts().to_vec();
    let before_inserts = backend.last_rule_insert_counts().to_vec();
    let before_watermark = backend.rules[id.rep() as usize]
        .as_ref()
        .expect("registered rule")
        .watermark;
    let error = run(&mut backend, &[id]).unwrap_err();
    assert!(
        error.to_string().contains("evaluated undefined"),
        "{error:#}"
    );
    assert_eq!(backend.storage.generation()?, before_generation);
    assert_eq!(backend.storage.next_fresh_id()?, before_fresh);
    assert_eq!(backend.storage.latest_rule_sql(), before_trace);
    assert_eq!(backend.last_rule_statement_count(), before_statement_count);
    assert_eq!(backend.last_rule_match_counts(), before_matches);
    assert_eq!(backend.last_rule_insert_counts(), before_inserts);
    assert_eq!(
        backend.rules[id.rep() as usize]
            .as_ref()
            .expect("registered rule")
            .watermark,
        before_watermark
    );
    assert_eq!(backend.table_size(target), 0);
    let scratch = backend.storage.with_connection(|connection| {
        connection
            .query_row(
                "SELECT count(*) FROM duckdb_tables() WHERE table_name LIKE 'egglog_scalar_%'",
                [],
                |row| row.get::<_, u64>(0),
            )
            .map_err(Into::into)
    })?;
    assert_eq!(scratch, 0);

    backend.storage.with_connection(|connection| {
        connection.execute(
            &format!("UPDATE {} SET c1 = CAST('2' AS BIGINT)", sql_table(source)),
            [],
        )?;
        Ok(())
    })?;
    assert!(run(&mut backend, &[id])?);
    assert_eq!(backend.storage.next_fresh_id()?, 4);
    assert_eq!(
        backend.lookup_id(
            target,
            &[
                Value::new(0),
                Value::new(2),
                backend.base_values().get(-3_i64),
            ],
        ),
        Some(unit)
    );
    assert_eq!(
        backend.lookup_id(
            target,
            &[
                Value::new(1),
                Value::new(3),
                backend.base_values().get(4_i64),
            ],
        ),
        Some(unit)
    );
    assert_eq!(backend.last_rule_match_counts(), &[2]);
    assert_eq!(backend.last_rule_insert_counts(), &[2]);

    assert!(!run(&mut backend, &[id])?);
    assert_eq!(backend.last_rule_match_counts(), &[0]);
    assert_eq!(backend.storage.next_fresh_id()?, 4);
    assert_eq!(backend.table_size(target), 2);
    Ok(())
}

#[test]
fn raw_id_math_shape_is_max_min_max_min() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = register_types(&mut backend);
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let source = table(
        &mut backend,
        "raw math shape source",
        vec![
            ColumnTy::Id,
            ColumnTy::Id,
            ColumnTy::Id,
            ColumnTy::Id,
            ColumnTy::Id,
            unit_ty,
        ],
        1,
    );
    let target = table(
        &mut backend,
        "raw math shape target",
        vec![ColumnTy::Id, unit_ty],
        1,
    );
    backend.add_values(
        [
            [1_u32, 2, 3, 4, 5],
            [5_u32, 4, 3, 2, 1],
            [7_u32, 7, 7, 7, 7],
        ]
        .into_iter()
        .map(|values| {
            let mut row = values.into_iter().map(Value::new).collect::<Vec<_>>();
            row.push(unit);
            (source, row)
        })
        .collect(),
    )?;
    let min = backend.register_native_primitive(NativePrimitive::OrderingMin);
    let max = backend.register_native_primitive(NativePrimitive::OrderingMax);
    let inputs = (0..5)
        .map(|index| var(index, &format!("raw input {index}"), ColumnTy::Id))
        .collect::<Vec<_>>();
    let first = var(10, "raw max one", ColumnTy::Id);
    let second = var(11, "raw min one", ColumnTy::Id);
    let third = var(12, "raw max two", ColumnTy::Id);
    let fourth = var(13, "raw min two", ColumnTy::Id);
    let id = backend.add_rule(rule(
        "exact Math max min max min action shape",
        true,
        vec![table_atom(
            source,
            inputs
                .iter()
                .cloned()
                .map(variable)
                .chain([literal(unit, unit_ty)])
                .collect(),
        )],
        vec![
            primitive_let(
                first.clone(),
                max,
                "hostile max diagnostic",
                ColumnTy::Id,
                vec![variable(inputs[0].clone()), variable(inputs[1].clone())],
            ),
            primitive_let(
                second.clone(),
                min,
                "hostile min diagnostic",
                ColumnTy::Id,
                vec![variable(first), variable(inputs[2].clone())],
            ),
            primitive_let(
                third.clone(),
                max,
                "second hostile max diagnostic",
                ColumnTy::Id,
                vec![variable(second), variable(inputs[3].clone())],
            ),
            primitive_let(
                fourth.clone(),
                min,
                "second hostile min diagnostic",
                ColumnTy::Id,
                vec![variable(third), variable(inputs[4].clone())],
            ),
            set_action(target, vec![variable(fourth)], vec![literal(unit, unit_ty)]),
        ],
    ))?;

    assert!(run(&mut backend, &[id])?);
    for expected in [1_u32, 4, 7] {
        assert_eq!(
            backend.lookup_id(target, &[Value::new(expected)]),
            Some(unit)
        );
    }
    assert_eq!(backend.table_size(target), 3);
    let slots = backend
        .storage
        .latest_rule_sql()
        .into_iter()
        .filter(|sql| sql.starts_with("CREATE TEMP TABLE egglog_scalar_slot_"))
        .collect::<Vec<_>>();
    assert_eq!(slots.len(), 4);
    for (index, (operator, slot)) in [">", "<", ">", "<"].into_iter().zip(&slots).enumerate() {
        assert!(slot.contains(&format!(" AS s{index}")), "{slot}");
        assert!(slot.contains(&format!(" {operator} ")), "{slot}");
        assert!(slot.contains(" ELSE "), "{slot}");
        assert_closed_sql(slot);
        assert!(!slot.contains("diagnostic"));
    }
    Ok(())
}

#[test]
fn scalar_rule_bodies_observe_one_stable_prewave() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = register_types(&mut backend);
    let i64_ty = ColumnTy::Base(types.i64);
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let source = table(
        &mut backend,
        "stable prewave source",
        vec![i64_ty, unit_ty],
        1,
    );
    let middle = table(
        &mut backend,
        "stable prewave middle",
        vec![i64_ty, unit_ty],
        1,
    );
    let target = table(
        &mut backend,
        "stable prewave target",
        vec![i64_ty, unit_ty],
        1,
    );
    let one = backend.base_values().get(1_i64);
    backend.add_values(vec![(source, vec![one, unit])])?;
    let add = backend.register_native_scalar_primitive(
        NativeScalarPrimitive::I64Add,
        scalar_fallback(NativeScalarPrimitive::I64Add),
    );
    let first_input = var(0, "first input", i64_ty);
    let first_output = var(1, "first output", i64_ty);
    let first = backend.add_rule(rule(
        "stable prewave producer",
        false,
        vec![
            table_atom(
                source,
                vec![variable(first_input.clone()), literal(unit, unit_ty)],
            ),
            primitive_atom(
                add,
                "producer add",
                i64_ty,
                vec![
                    variable(first_input),
                    literal(one, i64_ty),
                    variable(first_output.clone()),
                ],
            ),
        ],
        vec![set_action(
            middle,
            vec![variable(first_output)],
            vec![literal(unit, unit_ty)],
        )],
    ))?;
    let second_input = var(10, "second input", i64_ty);
    let second_output = var(11, "second output", i64_ty);
    let second = backend.add_rule(rule(
        "stable prewave consumer",
        false,
        vec![
            table_atom(
                middle,
                vec![variable(second_input.clone()), literal(unit, unit_ty)],
            ),
            primitive_atom(
                add,
                "consumer add",
                i64_ty,
                vec![
                    variable(second_input),
                    literal(one, i64_ty),
                    variable(second_output.clone()),
                ],
            ),
        ],
        vec![set_action(
            target,
            vec![variable(second_output)],
            vec![literal(unit, unit_ty)],
        )],
    ))?;

    assert!(run(&mut backend, &[first, second])?);
    assert_eq!(
        backend.lookup_id(middle, &[backend.base_values().get(2_i64)]),
        Some(unit)
    );
    assert_eq!(backend.table_size(target), 0);
    assert_eq!(backend.last_rule_match_counts(), &[1, 0]);

    assert!(run(&mut backend, &[first, second])?);
    assert_eq!(
        backend.lookup_id(target, &[backend.base_values().get(3_i64)]),
        Some(unit)
    );
    assert_eq!(backend.last_rule_match_counts(), &[1, 1]);
    assert!(!run(&mut backend, &[first, second])?);
    Ok(())
}

#[test]
fn scalar_admission_rejects_spoofs_and_malformed_signatures_without_rule_ids() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = register_types(&mut backend);
    let i64_ty = ColumnTy::Base(types.i64);
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let target = table(
        &mut backend,
        "scalar admission target",
        vec![i64_ty, unit_ty],
        1,
    );
    let id_target = table(
        &mut backend,
        "scalar admission Id target",
        vec![ColumnTy::Id, unit_ty],
        1,
    );
    let one = backend.base_values().get(1_i64);
    let two = backend.base_values().get(2_i64);
    let add = backend.register_native_scalar_primitive(
        NativeScalarPrimitive::I64Add,
        scalar_fallback(NativeScalarPrimitive::I64Add),
    );
    let f64_gt = backend.register_native_scalar_primitive(
        NativeScalarPrimitive::F64Gt,
        scalar_fallback(NativeScalarPrimitive::F64Gt),
    );
    let callback = backend.new_panic("callback must never run".to_string());
    let payload_selector = backend.register_native_primitive(NativePrimitive::SelectMaxPayload);
    let raw_ordering = backend.register_native_primitive(NativePrimitive::OrderingMax);
    let raw_neq = backend.register_native_primitive(NativePrimitive::ValueNeq);

    let valid = |name: &str, token: ExternalFunctionId| {
        let output = var(0, "scalar admission output", i64_ty);
        rule(
            name,
            true,
            vec![],
            vec![
                primitive_let(
                    output.clone(),
                    token,
                    "hostile diagnostic pretending to be something else",
                    i64_ty,
                    vec![literal(one, i64_ty), literal(two, i64_ty)],
                ),
                set_action(target, vec![variable(output)], vec![literal(unit, unit_ty)]),
            ],
        )
    };

    let error = backend
        .add_rule(valid("callback spoof", callback))
        .unwrap_err();
    assert!(
        format!("{error:#}").contains("unauthenticated or callback"),
        "{error:#}"
    );
    assert!(backend.rules.is_empty());

    let mut wrong_arity = valid("wrong typed arity", add);
    let GenericCoreAction::Let(_, _, _, arguments) = &mut wrong_arity.core.head.0[0] else {
        unreachable!()
    };
    arguments.pop();
    let error = backend.add_rule(wrong_arity).unwrap_err();
    assert!(
        format!("{error:#}").contains("exactly two inputs"),
        "{error:#}"
    );
    assert!(backend.rules.is_empty());

    let mut wrong_output = valid("wrong typed output", add);
    let GenericCoreAction::Let(_, binding, RuleActionCall::Primitive { output, .. }, _) =
        &mut wrong_output.core.head.0[0]
    else {
        unreachable!()
    };
    binding.ty = unit_ty;
    *output = unit_ty;
    let error = backend.add_rule(wrong_output).unwrap_err();
    assert!(format!("{error:#}").contains("expected"), "{error:#}");
    assert!(backend.rules.is_empty());

    let mut unbound = valid("unbound typed input", add);
    let GenericCoreAction::Let(_, _, _, arguments) = &mut unbound.core.head.0[0] else {
        unreachable!()
    };
    arguments[0] = variable(var(99, "never bound", i64_ty));
    let error = backend.add_rule(unbound).unwrap_err();
    assert!(format!("{error:#}").contains("before binding"), "{error:#}");
    assert!(backend.rules.is_empty());

    let typed_value = var(0, "typed value binding name", i64_ty);
    let error = backend
        .add_rule(rule(
            "same id with inconsistent type",
            true,
            vec![],
            vec![
                primitive_let(
                    typed_value,
                    add,
                    "typed value call name",
                    i64_ty,
                    vec![literal(one, i64_ty), literal(two, i64_ty)],
                ),
                set_action(
                    id_target,
                    vec![variable(var(0, "same id but Id type", ColumnTy::Id))],
                    vec![literal(unit, unit_ty)],
                ),
            ],
        ))
        .unwrap_err();
    assert!(
        format!("{error:#}").contains("inconsistent type metadata"),
        "{error:#}"
    );
    assert!(backend.rules.is_empty());

    let error = backend
        .add_rule(valid("wrong typed descriptor signature", f64_gt))
        .unwrap_err();
    assert!(format!("{error:#}").contains("expected"), "{error:#}");
    assert!(backend.rules.is_empty());

    let error = backend
        .add_rule(valid("payload selector wrong arity", payload_selector))
        .unwrap_err();
    assert!(
        format!("{error:#}").contains("requires exactly four inputs"),
        "{error:#}"
    );
    assert!(backend.rules.is_empty());

    let error = backend
        .add_rule(valid("raw ordering cannot decode i64", raw_ordering))
        .unwrap_err();
    assert!(
        format!("{error:#}").contains("requires (Id, Id) -> Id"),
        "{error:#}"
    );
    assert!(backend.rules.is_empty());

    let unit_result = var(0, "unit inequality output", unit_ty);
    let error = backend
        .add_rule(rule(
            "ValueNeq rejects Unit",
            true,
            vec![],
            vec![
                primitive_let(
                    unit_result.clone(),
                    raw_neq,
                    "!= diagnostic",
                    unit_ty,
                    vec![literal(unit, unit_ty), literal(unit, unit_ty)],
                ),
                set_action(
                    target,
                    vec![literal(one, i64_ty)],
                    vec![variable(unit_result)],
                ),
            ],
        ))
        .unwrap_err();
    assert!(
        format!("{error:#}").contains("Id/i64/f64/String"),
        "{error:#}"
    );
    assert!(backend.rules.is_empty());

    let id = backend.add_rule(valid(
        "valid hostile-name rule after rejected admissions",
        add,
    ))?;
    assert_eq!(id, RuleId::new(0));
    assert!(run(&mut backend, &[id])?);
    assert_eq!(
        backend.lookup_id(target, &[backend.base_values().get(3_i64)]),
        Some(unit)
    );
    Ok(())
}

#[test]
fn payload_selectors_authenticate_and_render_four_inputs() -> Result<()> {
    let mut backend = EGraph::new()?;
    let token = backend.register_native_primitive(NativePrimitive::SelectMinPayload);
    let expression = ScalarExpression::authenticate(
        backend.base_values(),
        &backend.native_primitives,
        &backend.native_scalar_primitives,
        token,
        &[ColumnTy::Id, ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        ColumnTy::Id,
    )?;
    let rendered = expression.render(&[
        "left".into(),
        "left_payload".into(),
        "right".into(),
        "right_payload".into(),
    ]);
    assert_eq!(rendered.defined, "TRUE");
    assert_eq!(
        rendered.value,
        "CASE WHEN (left) < (right) THEN (left_payload) ELSE (right_payload) END"
    );
    Ok(())
}

#[test]
fn same_descriptor_token_reuse_fails_epoch_reauthorization_before_sql() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = register_types(&mut backend);
    let i64_ty = ColumnTy::Base(types.i64);
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let target = table(
        &mut backend,
        "same descriptor ABA target",
        vec![i64_ty, unit_ty],
        1,
    );
    let one = backend.base_values().get(1_i64);
    let two = backend.base_values().get(2_i64);
    let stale = backend.register_native_scalar_primitive(
        NativeScalarPrimitive::I64Add,
        scalar_fallback(NativeScalarPrimitive::I64Add),
    );
    let output = var(0, "ABA output", i64_ty);
    let id = backend.add_rule(rule(
        "same descriptor ABA rule",
        true,
        vec![],
        vec![
            primitive_let(
                output.clone(),
                stale,
                "ABA diagnostic",
                i64_ty,
                vec![literal(one, i64_ty), literal(two, i64_ty)],
            ),
            set_action(target, vec![variable(output)], vec![literal(unit, unit_ty)]),
        ],
    ))?;
    let generation = backend.storage.generation()?;
    let trace = backend.storage.latest_rule_sql();
    let watermark = backend.rules[id.rep() as usize]
        .as_ref()
        .expect("registered rule")
        .watermark;

    backend.free_external_func(stale);
    let replacement = backend.register_native_scalar_primitive(
        NativeScalarPrimitive::I64Add,
        scalar_fallback(NativeScalarPrimitive::I64Add),
    );
    assert_eq!(replacement, stale);
    let error = run(&mut backend, &[id]).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("freed or reused authority token"),
        "{error:#}"
    );
    assert_eq!(backend.storage.generation()?, generation);
    assert_eq!(backend.storage.latest_rule_sql(), trace);
    assert_eq!(backend.storage.next_fresh_id()?, 0);
    assert_eq!(backend.table_size(target), 0);
    assert_eq!(
        backend.rules[id.rep() as usize]
            .as_ref()
            .expect("registered rule")
            .watermark,
        watermark
    );
    Ok(())
}
