use anyhow::Result;
use egglog_ast::{
    core::{
        GenericAtom, GenericAtomTerm, GenericCoreAction, GenericCoreActions, GenericCoreRule, Query,
    },
    span::Span,
};
use egglog_backend_trait::{
    Backend, BaseValueId, ColumnTy, DefaultVal, ExternalFunctionId, FunctionConfig, FunctionId,
    MergeFn, NativePrimitive, ReadMode, RuleActionCall, RuleBodyCall, RuleId, RuleSetRun, RuleSpec,
    RuleValue, RuleVar, Value,
};
use egglog_core_relations::Boxed;
use egglog_numeric_id::NumericId;
use ordered_float::OrderedFloat;

use crate::{EGraph, storage::sql_table};

type Term = GenericAtomTerm<RuleVar, RuleValue>;
type Action = GenericCoreAction<RuleActionCall, RuleVar, RuleValue>;

#[derive(Clone, Copy)]
struct Types {
    unit: BaseValueId,
    string: BaseValueId,
}

fn types(backend: &mut impl Backend) -> Types {
    let unit = backend.base_values_mut().register_type::<()>();
    backend.base_values_mut().register_type::<bool>();
    backend.base_values_mut().register_type::<i64>();
    backend
        .base_values_mut()
        .register_type::<Boxed<OrderedFloat<f64>>>();
    let string = backend.base_values_mut().register_type::<Boxed<String>>();
    Types { unit, string }
}

fn table(
    backend: &mut impl Backend,
    name: &str,
    schema: Vec<ColumnTy>,
    n_vals: usize,
    merge: MergeFn,
    can_subsume: bool,
) -> FunctionId {
    backend.add_table(FunctionConfig {
        schema,
        n_vals,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge,
        name: name.to_string(),
        can_subsume,
    })
}

fn all_index_delete_set_case(
    backend: &mut impl Backend,
) -> Result<(RuleId, FunctionId, FunctionId, FunctionId, Value)> {
    let types = types(backend);
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let source = table(
        backend,
        "generic occurrence source",
        vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id, unit_ty],
        1,
        MergeFn::AssertEq,
        true,
    );
    let canonical = table(
        backend,
        "generic canonical target",
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::AssertEq,
        false,
    );
    let decoy = table(
        backend,
        "generic same-schema decoy",
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::AssertEq,
        false,
    );
    backend.add_values(vec![
        (
            source,
            vec![Value::new(1), Value::new(1), Value::new(2), unit],
        ),
        (canonical, vec![Value::new(1), Value::new(90)]),
        (decoy, vec![Value::new(1), Value::new(91)]),
    ])?;
    let neq = backend.register_native_primitive(NativePrimitive::ValueNeq);
    let fresh_token = backend.register_get_fresh();
    let label = backend
        .base_values()
        .get(Boxed::new("generic decoy fresh".to_string()));
    let x = var(0, "x", ColumnTy::Id);
    let y = var(1, "y", ColumnTy::Id);
    let alias = var(2, "alias", ColumnTy::Id);
    let fresh = var(3, "fresh", ColumnTy::Id);
    let body_row = vec![
        variable(x.clone()),
        variable(x.clone()),
        variable(y.clone()),
        literal(unit, unit_ty),
    ];
    let body = vec![
        GenericAtom {
            span: Span::Panic,
            head: RuleBodyCall::Table {
                id: source,
                read: ReadMode::All,
            },
            args: body_row.clone(),
        },
        GenericAtom {
            span: Span::Panic,
            head: RuleBodyCall::IndexTable {
                id: source,
                any_of: vec![0, 1],
                read: ReadMode::All,
            },
            args: std::iter::once(variable(x.clone()))
                .chain(body_row)
                .chain(std::iter::once(literal(unit, unit_ty)))
                .collect(),
        },
        GenericAtom {
            span: Span::Panic,
            head: RuleBodyCall::Primitive {
                id: neq,
                name: "diagnostic name is not authority".into(),
                output: unit_ty,
            },
            args: vec![
                variable(x.clone()),
                variable(y.clone()),
                literal(unit, unit_ty),
            ],
        },
    ];
    let mut canonical_rule = rule(
        "generic All occurrence delete then set",
        true,
        body,
        vec![
            GenericCoreAction::Let(
                Span::Panic,
                fresh,
                RuleActionCall::Primitive {
                    id: fresh_token,
                    name: "diagnostic fresh name is not authority".into(),
                    output: ColumnTy::Id,
                },
                vec![literal(label, ColumnTy::Base(types.string))],
            ),
            GenericCoreAction::LetAtomTerm(Span::Panic, alias.clone(), variable(x)),
            GenericCoreAction::Change(
                Span::Panic,
                egglog_ast::generic_ast::Change::Delete,
                table_call(canonical),
                vec![variable(alias.clone())],
            ),
            GenericCoreAction::Set(
                Span::Panic,
                table_call(canonical),
                vec![variable(alias)],
                vec![variable(y)],
            ),
        ],
    );
    // The exercised rule differs only in the exact action FunctionId. This is
    // deliberately a same-schema decoy against structural role inference.
    for action in &mut canonical_rule.core.head.0 {
        match action {
            GenericCoreAction::Change(_, _, RuleActionCall::Table { id, .. }, _)
            | GenericCoreAction::Set(_, RuleActionCall::Table { id, .. }, _, _) => *id = decoy,
            _ => {}
        }
    }
    Ok((
        backend.add_rule(canonical_rule)?,
        source,
        canonical,
        decoy,
        unit,
    ))
}

#[test]
fn all_index_delete_set_uses_exact_decoy_target_and_general_plan() -> Result<()> {
    let mut duckdb = EGraph::new()?;
    let (duck_rule, source, canonical, decoy, _) = all_index_delete_set_case(&mut duckdb)?;
    let compiled = &duckdb.rules[duck_rule.rep() as usize]
        .as_ref()
        .expect("registered rule")
        .plan;
    assert!(compiled.scalar_action().is_some());
    assert!(compiled.standard_rebuild().is_none());
    assert!(compiled.marker_rekey().is_none());
    assert!(compiled.path_compression().is_none());
    assert!(run(&mut duckdb, &[duck_rule])?);
    assert_eq!(duckdb.last_rule_match_counts(), &[1]);
    assert_eq!(duckdb.storage.next_fresh_id()?, 1);
    let match_sql = duckdb
        .storage
        .latest_rule_sql()
        .into_iter()
        .find(|sql| sql.starts_with("CREATE TEMP TABLE egglog_scalar_match_"))
        .expect("frozen scalar match stage");
    assert!(
        match_sql
            .contains("(b1.c0 IS NOT DISTINCT FROM b0.c0 OR b1.c1 IS NOT DISTINCT FROM b0.c0)")
    );
    assert_eq!(
        match_sql
            .matches(&format!("{} AS b1", sql_table(source)))
            .count(),
        1
    );
    assert_eq!(
        duckdb.lookup_id(canonical, &[Value::new(1)]),
        Some(Value::new(90))
    );
    assert_eq!(
        duckdb.lookup_id(decoy, &[Value::new(1)]),
        Some(Value::new(2))
    );

    let mut reference = egglog_bridge::EGraph::default();
    let (reference_rule, _, reference_canonical, reference_decoy, _) =
        all_index_delete_set_case(&mut reference)?;
    assert!(run(&mut reference, &[reference_rule])?);
    assert_eq!(
        reference.lookup_id(reference_canonical, &[Value::new(1)]),
        duckdb.lookup_id(canonical, &[Value::new(1)])
    );
    assert_eq!(
        reference.lookup_id(reference_decoy, &[Value::new(1)]),
        duckdb.lookup_id(decoy, &[Value::new(1)])
    );
    Ok(())
}

#[test]
fn multi_column_index_binds_an_unbound_probe_from_a_repeated_indexed_column() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = types(&mut backend);
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let source = table(
        &mut backend,
        "unbound repeated index source",
        vec![ColumnTy::Id, ColumnTy::Id, unit_ty],
        1,
        MergeFn::AssertEq,
        false,
    );
    let target = table(
        &mut backend,
        "unbound repeated index target",
        vec![ColumnTy::Id, unit_ty],
        1,
        MergeFn::AssertEq,
        false,
    );
    backend.add_values(vec![(source, vec![Value::new(7), Value::new(7), unit])])?;
    let probe = var(0, "probe", ColumnTy::Id);
    let id = backend.add_rule(rule(
        "multi-column repeated probe binder",
        false,
        vec![GenericAtom {
            span: Span::Panic,
            head: RuleBodyCall::IndexTable {
                id: source,
                any_of: vec![0, 1],
                read: ReadMode::All,
            },
            args: vec![
                variable(probe.clone()),
                variable(probe.clone()),
                variable(probe.clone()),
                literal(unit, unit_ty),
                literal(unit, unit_ty),
            ],
        }],
        vec![GenericCoreAction::Set(
            Span::Panic,
            table_call(target),
            vec![variable(probe)],
            vec![literal(unit, unit_ty)],
        )],
    ))?;
    assert!(run(&mut backend, &[id])?);
    assert_eq!(backend.last_rule_match_counts(), &[1]);
    assert_eq!(backend.lookup_id(target, &[Value::new(7)]), Some(unit));
    Ok(())
}

#[test]
fn malformed_index_rules_reject_before_rule_id_and_singleton_second_pass_runs() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = types(&mut backend);
    let unit_ty = ColumnTy::Base(types.unit);
    let i64_ty = ColumnTy::Base(backend.base_values().get_ty::<i64>());
    let unit = backend.base_values().get(());
    let one = backend.base_values().get(1_i64);
    let source = table(
        &mut backend,
        "direct DuckDB index admission source",
        vec![i64_ty, i64_ty, i64_ty],
        1,
        MergeFn::Old,
        false,
    );
    let target = table(
        &mut backend,
        "direct DuckDB index admission target",
        vec![i64_ty, unit_ty],
        1,
        MergeFn::AssertEq,
        false,
    );
    backend.add_values(vec![(source, vec![one, one, one])])?;

    let index_atom = |probe: Term, any_of: Vec<usize>, row: Vec<Term>, output: Term| GenericAtom {
        span: Span::Panic,
        head: RuleBodyCall::IndexTable {
            id: source,
            any_of,
            read: ReadMode::All,
        },
        args: std::iter::once(probe)
            .chain(row)
            .chain(std::iter::once(output))
            .collect(),
    };
    let index_rule = |name: &str, body| {
        rule(
            name,
            false,
            body,
            vec![GenericCoreAction::Set(
                Span::Panic,
                table_call(target),
                vec![literal(one, i64_ty)],
                vec![literal(unit, unit_ty)],
            )],
        )
    };
    let i64_literal = || literal(one, i64_ty);
    let unit_literal = || literal(unit, unit_ty);
    let probe = var(90, "cyclic or unindexed probe", i64_ty);
    let y = var(91, "other cyclic probe", i64_ty);
    let cyclic = index_rule(
        "mutually cyclic direct DuckDB probes",
        vec![
            index_atom(
                variable(probe.clone()),
                vec![0, 1],
                vec![variable(y.clone()), i64_literal(), i64_literal()],
                unit_literal(),
            ),
            index_atom(
                variable(y),
                vec![0, 1],
                vec![variable(probe.clone()), i64_literal(), i64_literal()],
                unit_literal(),
            ),
        ],
    );
    let unindexed = index_rule(
        "direct DuckDB probe repeated only at unindexed column",
        vec![index_atom(
            variable(probe.clone()),
            vec![0, 1],
            vec![i64_literal(), i64_literal(), variable(probe.clone())],
            unit_literal(),
        )],
    );
    let literal_probe = || literal(one, i64_ty);
    let ordinary_row = || vec![i64_literal(), i64_literal(), i64_literal()];
    let mut short = ordinary_row();
    short.pop();
    let mut long = ordinary_row();
    long.push(i64_literal());
    let malformed = vec![
        cyclic,
        unindexed,
        index_rule(
            "direct DuckDB empty occurrence columns",
            vec![index_atom(
                literal_probe(),
                vec![],
                ordinary_row(),
                unit_literal(),
            )],
        ),
        index_rule(
            "direct DuckDB out-of-range occurrence column",
            vec![index_atom(
                literal_probe(),
                vec![3],
                ordinary_row(),
                unit_literal(),
            )],
        ),
        index_rule(
            "direct DuckDB short index row",
            vec![index_atom(literal_probe(), vec![0], short, unit_literal())],
        ),
        index_rule(
            "direct DuckDB long index row",
            vec![index_atom(literal_probe(), vec![0], long, unit_literal())],
        ),
        index_rule(
            "direct DuckDB nonliteral Unit output",
            vec![index_atom(
                literal_probe(),
                vec![0],
                ordinary_row(),
                variable(var(92, "nonliteral output", unit_ty)),
            )],
        ),
        index_rule(
            "direct DuckDB mistyped Unit output",
            vec![index_atom(
                literal_probe(),
                vec![0],
                ordinary_row(),
                i64_literal(),
            )],
        ),
        index_rule(
            "direct DuckDB noncanonical Unit output",
            vec![index_atom(
                literal_probe(),
                vec![0],
                ordinary_row(),
                literal(Value::new(unit.rep() + 1), unit_ty),
            )],
        ),
        index_rule(
            "direct DuckDB mistyped index row",
            vec![index_atom(
                literal_probe(),
                vec![0],
                vec![unit_literal(), i64_literal(), i64_literal()],
                unit_literal(),
            )],
        ),
        index_rule(
            "direct DuckDB mistyped index probe",
            vec![index_atom(
                unit_literal(),
                vec![0],
                ordinary_row(),
                unit_literal(),
            )],
        ),
    ];
    for malformed_rule in malformed {
        backend
            .add_rule(malformed_rule)
            .expect_err("malformed direct DuckDB IndexTable must reject before RuleId");
    }

    let valid = index_rule(
        "deduplicated singleton direct DuckDB occurrence",
        vec![index_atom(
            variable(probe.clone()),
            vec![0, 0],
            vec![i64_literal(), i64_literal(), i64_literal()],
            unit_literal(),
        )],
    );
    let id = backend.add_rule(valid)?;
    assert_eq!(id, RuleId::new(0));
    assert!(run(&mut backend, &[id])?);
    assert_eq!(backend.last_rule_match_counts(), &[1]);
    assert_eq!(backend.lookup_id(target, &[one]), Some(unit));
    Ok(())
}

fn duplicate_occurrence_columns_case(
    backend: &mut impl Backend,
) -> Result<(FunctionId, Value, bool)> {
    let types = types(backend);
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let source = table(
        backend,
        "duplicate occurrence-column source",
        vec![ColumnTy::Id, ColumnTy::Id, unit_ty],
        1,
        MergeFn::AssertEq,
        false,
    );
    let target = table(
        backend,
        "duplicate occurrence-column target",
        vec![ColumnTy::Id, ColumnTy::Id, unit_ty],
        1,
        MergeFn::AssertEq,
        false,
    );
    backend.add_values(vec![(source, vec![Value::new(7), Value::new(7), unit])])?;
    let fresh_token = backend.register_get_fresh();
    let label = backend
        .base_values()
        .get(Boxed::new("duplicate occurrence-column fresh".to_string()));
    let left = var(0, "repeated left", ColumnTy::Id);
    let right = var(1, "repeated right", ColumnTy::Id);
    let fresh = var(2, "one fresh per deduplicated match", ColumnTy::Id);
    let id = backend.add_rule(rule(
        "duplicate occurrence columns are set semantics",
        false,
        vec![GenericAtom {
            span: Span::Panic,
            head: RuleBodyCall::IndexTable {
                id: source,
                any_of: vec![0, 0, 1, 1],
                read: ReadMode::All,
            },
            args: vec![
                literal(Value::new(7), ColumnTy::Id),
                variable(left.clone()),
                variable(right),
                literal(unit, unit_ty),
                literal(unit, unit_ty),
            ],
        }],
        vec![
            GenericCoreAction::Let(
                Span::Panic,
                fresh.clone(),
                RuleActionCall::Primitive {
                    id: fresh_token,
                    name: "duplicate occurrence fresh".into(),
                    output: ColumnTy::Id,
                },
                vec![literal(label, ColumnTy::Base(types.string))],
            ),
            GenericCoreAction::Set(
                Span::Panic,
                table_call(target),
                vec![variable(fresh), variable(left)],
                vec![literal(unit, unit_ty)],
            ),
        ],
    ))?;
    let changed = run(backend, &[id])?;
    let next_fresh = backend.fresh_id();
    Ok((target, next_fresh, changed))
}

#[test]
fn duplicate_occurrence_columns_and_repeated_values_have_one_match() -> Result<()> {
    let mut duckdb = EGraph::new()?;
    let (duck_target, duck_next_fresh, duck_changed) =
        duplicate_occurrence_columns_case(&mut duckdb)?;
    let mut reference = egglog_bridge::EGraph::default();
    let (reference_target, reference_next_fresh, reference_changed) =
        duplicate_occurrence_columns_case(&mut reference)?;

    assert_eq!(duck_changed, reference_changed);
    assert!(duck_changed);
    assert_eq!(duckdb.last_rule_match_counts(), &[1]);
    assert_eq!(duckdb.table_size(duck_target), 1);
    assert_eq!(reference.table_size(reference_target), 1);
    assert_eq!(duck_next_fresh, Value::new(1));
    assert_eq!(reference_next_fresh, Value::new(1));
    let expected = Some(Value::new(duckdb.base_values().get(()).rep()));
    assert_eq!(
        duckdb.lookup_id(duck_target, &[Value::new(0), Value::new(7)]),
        expected
    );
    assert_eq!(
        reference.lookup_id(reference_target, &[Value::new(0), Value::new(7)]),
        expected
    );
    Ok(())
}

fn var(id: u32, name: &str, ty: ColumnTy) -> RuleVar {
    RuleVar {
        id,
        name: name.into(),
        ty,
    }
}

fn variable(value: RuleVar) -> Term {
    GenericAtomTerm::Var(Span::Panic, value)
}

fn literal(value: Value, ty: ColumnTy) -> Term {
    GenericAtomTerm::Literal(Span::Panic, RuleValue { value, ty })
}

fn table_call(id: FunctionId) -> RuleActionCall {
    RuleActionCall::Table {
        id,
        name: "hostile diagnostic table '); --".into(),
    }
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

fn set_if_empty_rule(
    token: ExternalFunctionId,
    output: FunctionId,
    unit_ty: ColumnTy,
    unit: Value,
    arguments: Vec<Term>,
) -> RuleSpec {
    let canonical = var(0, "canonical", ColumnTy::Id);
    rule(
        "FD descriptor admission canary",
        false,
        vec![],
        vec![
            GenericCoreAction::Let(
                Span::Panic,
                canonical.clone(),
                RuleActionCall::Primitive {
                    id: token,
                    name: "diagnostic name is not authority".into(),
                    output: ColumnTy::Id,
                },
                arguments,
            ),
            GenericCoreAction::Set(
                Span::Panic,
                table_call(output),
                vec![variable(canonical)],
                vec![literal(unit, unit_ty)],
            ),
        ],
    )
}

fn run(backend: &mut impl Backend, rules: &[RuleId]) -> Result<bool> {
    Ok(backend
        .run_rules(RuleSetRun {
            name: Some("general scalar action test"),
            rules,
        })?
        .changed())
}

fn repeated_set_if_empty_case(
    backend: &mut impl Backend,
    types: Types,
    token: ExternalFunctionId,
    view_name: &str,
) -> Result<(FunctionId, FunctionId)> {
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let source = table(
        backend,
        "repeated FD source",
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::AssertEq,
        false,
    );
    let view = table(
        backend,
        view_name,
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::Old,
        true,
    );
    let output = table(
        backend,
        "repeated FD observation",
        vec![ColumnTy::Id, ColumnTy::Id, unit_ty],
        1,
        MergeFn::AssertEq,
        false,
    );
    backend.add_values(vec![
        (source, vec![Value::new(1), Value::new(10)]),
        (source, vec![Value::new(2), Value::new(20)]),
    ])?;
    let event = var(0, "event", ColumnTy::Id);
    let fallback = var(1, "fallback", ColumnTy::Id);
    let canonical = var(2, "canonical", ColumnTy::Id);
    let id = backend.add_rule(rule(
        "repeated same-key set-if-empty",
        false,
        vec![GenericAtom {
            span: Span::Panic,
            head: RuleBodyCall::Table {
                id: source,
                read: ReadMode::Live,
            },
            args: vec![variable(event.clone()), variable(fallback.clone())],
        }],
        vec![
            GenericCoreAction::Let(
                Span::Panic,
                canonical.clone(),
                RuleActionCall::Primitive {
                    id: token,
                    name: "set-if-empty diagnostic".into(),
                    output: ColumnTy::Id,
                },
                vec![literal(Value::new(7), ColumnTy::Id), variable(fallback)],
            ),
            GenericCoreAction::Set(
                Span::Panic,
                table_call(output),
                vec![variable(event), variable(canonical)],
                vec![literal(unit, unit_ty)],
            ),
        ],
    ))?;
    assert!(run(backend, &[id])?);
    Ok((view, output))
}

#[test]
fn repeated_same_key_set_if_empty_matches_reference_first_staged_default() -> Result<()> {
    let view_name = "repeated FD exact authority";

    let mut duckdb = EGraph::new()?;
    let duck_types = types(&mut duckdb);
    let duck_token = duckdb.register_set_if_empty(view_name.to_string(), 1, 1);
    let (duck_view, duck_output) =
        repeated_set_if_empty_case(&mut duckdb, duck_types, duck_token, view_name)?;

    let mut reference = egglog_bridge::EGraph::default();
    let reference_types = types(&mut reference);
    let reference_token = reference.register_set_if_empty(view_name.to_string(), 1, 1);
    let (reference_view, reference_output) =
        repeated_set_if_empty_case(&mut reference, reference_types, reference_token, view_name)?;

    assert_eq!(
        duckdb.lookup_id(duck_view, &[Value::new(7)]),
        reference.lookup_id(reference_view, &[Value::new(7)])
    );
    assert_eq!(
        duckdb.lookup_id(duck_view, &[Value::new(7)]),
        Some(Value::new(10))
    );
    for event in [1, 2] {
        assert_eq!(
            duckdb.lookup_id(duck_output, &[Value::new(event), Value::new(10)]),
            reference.lookup_id(reference_output, &[Value::new(event), Value::new(10)],)
        );
        assert!(
            duckdb
                .lookup_id(duck_output, &[Value::new(event), Value::new(10)])
                .is_some()
        );
    }
    assert_eq!(
        duckdb.lookup_id(duck_output, &[Value::new(2), Value::new(20)]),
        None
    );
    Ok(())
}

fn two_action_set_if_empty_case(
    backend: &mut impl Backend,
    types: Types,
    token: ExternalFunctionId,
    view_name: &str,
) -> Result<(FunctionId, FunctionId)> {
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let source = table(
        backend,
        "two-action FD source",
        vec![
            ColumnTy::Id,
            ColumnTy::Id,
            ColumnTy::Id,
            ColumnTy::Id,
            ColumnTy::Id,
        ],
        1,
        MergeFn::AssertEq,
        false,
    );
    let view = table(
        backend,
        view_name,
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::Old,
        true,
    );
    let output = table(
        backend,
        "two-action FD observation",
        vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id, unit_ty],
        1,
        MergeFn::AssertEq,
        false,
    );
    backend.add_values(vec![
        (
            source,
            vec![
                Value::new(1),
                Value::new(1),
                Value::new(2),
                Value::new(10),
                Value::new(110),
            ],
        ),
        (
            source,
            vec![
                Value::new(2),
                Value::new(2),
                Value::new(1),
                Value::new(20),
                Value::new(120),
            ],
        ),
    ])?;
    let vars = (0..7)
        .map(|id| var(id, &format!("v{id}"), ColumnTy::Id))
        .collect::<Vec<_>>();
    let id = backend.add_rule(rule(
        "two-action two-match set-if-empty",
        false,
        vec![GenericAtom {
            span: Span::Panic,
            head: RuleBodyCall::Table {
                id: source,
                read: ReadMode::Live,
            },
            args: vars[..5].iter().cloned().map(variable).collect(),
        }],
        vec![
            GenericCoreAction::Let(
                Span::Panic,
                vars[5].clone(),
                RuleActionCall::Primitive {
                    id: token,
                    name: "first set-if-empty".into(),
                    output: ColumnTy::Id,
                },
                vec![variable(vars[1].clone()), variable(vars[3].clone())],
            ),
            GenericCoreAction::Let(
                Span::Panic,
                vars[6].clone(),
                RuleActionCall::Primitive {
                    id: token,
                    name: "second set-if-empty".into(),
                    output: ColumnTy::Id,
                },
                vec![variable(vars[2].clone()), variable(vars[4].clone())],
            ),
            GenericCoreAction::Set(
                Span::Panic,
                table_call(output),
                vec![
                    variable(vars[0].clone()),
                    variable(vars[5].clone()),
                    variable(vars[6].clone()),
                ],
                vec![literal(unit, unit_ty)],
            ),
        ],
    ))?;
    assert!(run(backend, &[id])?);
    Ok((view, output))
}

#[test]
fn two_set_if_empty_actions_across_two_matches_are_action_major_like_reference() -> Result<()> {
    let view_name = "two-action FD exact authority";
    let mut duckdb = EGraph::new()?;
    let duck_types = types(&mut duckdb);
    let duck_token = duckdb.register_set_if_empty(view_name.to_string(), 1, 1);
    let (duck_view, duck_output) =
        two_action_set_if_empty_case(&mut duckdb, duck_types, duck_token, view_name)?;

    let mut reference = egglog_bridge::EGraph::default();
    let reference_types = types(&mut reference);
    let reference_token = reference.register_set_if_empty(view_name.to_string(), 1, 1);
    let (reference_view, reference_output) =
        two_action_set_if_empty_case(&mut reference, reference_types, reference_token, view_name)?;

    for (key, value) in [(1, 10), (2, 20)] {
        assert_eq!(
            duckdb.lookup_id(duck_view, &[Value::new(key)]),
            reference.lookup_id(reference_view, &[Value::new(key)])
        );
        assert_eq!(
            duckdb.lookup_id(duck_view, &[Value::new(key)]),
            Some(Value::new(value))
        );
    }
    for (event, first, second) in [(1, 10, 20), (2, 20, 10)] {
        let keys = [Value::new(event), Value::new(first), Value::new(second)];
        assert_eq!(
            duckdb.lookup_id(duck_output, &keys),
            reference.lookup_id(reference_output, &keys)
        );
        assert!(duckdb.lookup_id(duck_output, &keys).is_some());
    }
    Ok(())
}

fn scheduled_multi_output_fd_case(
    backend: &mut impl Backend,
    types: Types,
    token: ExternalFunctionId,
    view_name: &str,
    reversed: bool,
) -> Result<(FunctionId, FunctionId, FunctionId, Value, Value)> {
    let unit_ty = ColumnTy::Base(types.unit);
    let string_ty = ColumnTy::Base(types.string);
    let unit = backend.base_values().get(());
    let first_proof = backend
        .base_values()
        .get(Boxed::new("first full default".to_string()));
    let second_proof = backend
        .base_values()
        .get(Boxed::new("second full default".to_string()));
    let view = table(
        backend,
        view_name,
        vec![ColumnTy::Id, ColumnTy::Id, string_ty],
        2,
        MergeFn::Columns(vec![MergeFn::OldCol(0), MergeFn::OldCol(1)]),
        true,
    );
    let first_output = table(
        backend,
        "scheduled FD first observation",
        vec![ColumnTy::Id, unit_ty],
        1,
        MergeFn::AssertEq,
        false,
    );
    let second_output = table(
        backend,
        "scheduled FD second observation",
        vec![ColumnTy::Id, unit_ty],
        1,
        MergeFn::AssertEq,
        false,
    );
    let first = backend.add_rule(set_if_empty_rule(
        token,
        first_output,
        unit_ty,
        unit,
        vec![
            literal(Value::new(7), ColumnTy::Id),
            literal(Value::new(10), ColumnTy::Id),
            literal(first_proof, string_ty),
        ],
    ))?;
    let second = backend.add_rule(set_if_empty_rule(
        token,
        second_output,
        unit_ty,
        unit,
        vec![
            literal(Value::new(7), ColumnTy::Id),
            literal(Value::new(20), ColumnTy::Id),
            literal(second_proof, string_ty),
        ],
    ))?;
    let schedule = if reversed {
        [second, first]
    } else {
        [first, second]
    };
    assert!(run(backend, &schedule)?);
    Ok((view, first_output, second_output, first_proof, second_proof))
}

#[test]
fn scheduled_rules_share_one_typed_prediction_ledger_in_schedule_order() -> Result<()> {
    for reversed in [false, true] {
        let view_name = if reversed {
            "scheduled reversed FD authority"
        } else {
            "scheduled forward FD authority"
        };
        let mut duckdb = EGraph::new()?;
        let duck_types = types(&mut duckdb);
        let duck_token = duckdb.register_set_if_empty(view_name.to_string(), 1, 2);
        let unit = duckdb.base_values().get(());
        let (duck_view, duck_first, duck_second, duck_first_proof, duck_second_proof) =
            scheduled_multi_output_fd_case(
                &mut duckdb,
                duck_types,
                duck_token,
                view_name,
                reversed,
            )?;

        let mut reference = egglog_bridge::EGraph::default();
        let reference_types = types(&mut reference);
        let reference_token = reference.register_set_if_empty(view_name.to_string(), 1, 2);
        let (reference_view, reference_first, reference_second, _, _) =
            scheduled_multi_output_fd_case(
                &mut reference,
                reference_types,
                reference_token,
                view_name,
                reversed,
            )?;

        let (canonical, proof) = if reversed {
            (20, duck_second_proof)
        } else {
            (10, duck_first_proof)
        };
        assert_eq!(
            duckdb.lookup_row(duck_view, &[Value::new(7)]),
            Some(vec![Value::new(7), Value::new(canonical), proof])
        );
        assert_eq!(
            duckdb.lookup_row(duck_view, &[Value::new(7)]),
            reference.lookup_row(reference_view, &[Value::new(7)])
        );
        for (duck_output, reference_output) in [
            (duck_first, reference_first),
            (duck_second, reference_second),
        ] {
            assert_eq!(
                duckdb.lookup_id(duck_output, &[Value::new(canonical)]),
                reference.lookup_id(reference_output, &[Value::new(canonical)])
            );
            assert_eq!(
                duckdb.lookup_id(duck_output, &[Value::new(canonical)]),
                Some(unit)
            );
        }

        let sql = duckdb.storage.latest_rule_sql();
        assert_eq!(
            sql.iter()
                .filter(
                    |statement| statement.starts_with("CREATE TEMP TABLE egglog_scalar_fd_ledger_")
                )
                .count(),
            1
        );
        assert_eq!(
            sql.iter()
                .filter(
                    |statement| statement.starts_with("CREATE TEMP TABLE egglog_scalar_fd_winner_")
                )
                .count(),
            2
        );
        for statement in sql.iter().filter(|statement| {
            statement.contains("egglog_scalar_fd_") || statement.contains(" AS choice ON TRUE")
        }) {
            assert!(!statement.contains(" IS NULL"), "{statement}");
            assert!(!statement.contains("COALESCE"), "{statement}");
            assert!(!statement.contains("first("), "{statement}");
            assert!(statement.matches("UNION ALL").count() <= 1, "{statement}");
        }
    }
    Ok(())
}

#[test]
fn set_if_empty_prefers_a_subsumed_durable_full_owner_over_the_ledger() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = types(&mut backend);
    let unit_ty = ColumnTy::Base(types.unit);
    let string_ty = ColumnTy::Base(types.string);
    let unit = backend.base_values().get(());
    let durable_proof = backend
        .base_values()
        .get(Boxed::new("subsumed durable proof".to_string()));
    let fallback_proof = backend
        .base_values()
        .get(Boxed::new("unused fallback proof".to_string()));
    let view_name = "subsumed durable FD authority";
    let token = backend.register_set_if_empty(view_name.to_string(), 1, 2);
    let view = table(
        &mut backend,
        view_name,
        vec![ColumnTy::Id, ColumnTy::Id, string_ty],
        2,
        MergeFn::Columns(vec![MergeFn::OldCol(0), MergeFn::OldCol(1)]),
        true,
    );
    let output = table(
        &mut backend,
        "subsumed durable observation",
        vec![ColumnTy::Id, unit_ty],
        1,
        MergeFn::AssertEq,
        false,
    );
    backend.add_values(vec![(
        view,
        vec![Value::new(7), Value::new(30), durable_proof],
    )])?;
    backend.storage.with_connection(|connection| {
        connection.execute(
            &format!("UPDATE {} SET __subsumed = TRUE", sql_table(view)),
            [],
        )?;
        Ok(())
    })?;
    let id = backend.add_rule(set_if_empty_rule(
        token,
        output,
        unit_ty,
        unit,
        vec![
            literal(Value::new(7), ColumnTy::Id),
            literal(Value::new(40), ColumnTy::Id),
            literal(fallback_proof, string_ty),
        ],
    ))?;
    assert!(run(&mut backend, &[id])?);
    let rows = backend.storage.with_connection(|connection| {
        Ok(connection.query_row(
            &format!(
                "SELECT count(*), count(*) FILTER (WHERE __subsumed) FROM {}",
                sql_table(view)
            ),
            [],
            |row| Ok((row.get::<_, u64>(0)?, row.get::<_, u64>(1)?)),
        )?)
    })?;
    assert_eq!(rows, (1, 1));
    assert_eq!(backend.lookup_id(output, &[Value::new(30)]), Some(unit));
    assert_eq!(backend.table_size(output), 1);
    assert!(backend.storage.latest_rule_sql().iter().any(|statement| {
        statement.starts_with("INSERT INTO egglog_scalar_fd_ledger_")
            && statement.contains("SELECT * FROM egglog_scalar_fd_winner_")
    }));
    Ok(())
}

#[test]
fn losing_fresh_default_and_late_failure_roll_back_then_retry_exactly() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = types(&mut backend);
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let label = backend
        .base_values()
        .get(Boxed::new("losing FD fresh default".to_string()));
    let view_name = "rollback FD prediction authority";
    let set_if_empty = backend.register_set_if_empty(view_name.to_string(), 1, 1);
    let fresh_token = backend.register_get_fresh();
    let view = table(
        &mut backend,
        view_name,
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::Old,
        true,
    );
    let observation = table(
        &mut backend,
        "losing fresh observation",
        vec![ColumnTy::Id, unit_ty],
        1,
        MergeFn::AssertEq,
        false,
    );
    let conflict = table(
        &mut backend,
        "late FD conflict",
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::AssertEq,
        false,
    );
    backend.add_values(vec![(conflict, vec![Value::new(1), Value::new(90)])])?;
    let first = backend.add_rule(set_if_empty_rule(
        set_if_empty,
        observation,
        unit_ty,
        unit,
        vec![
            literal(Value::new(7), ColumnTy::Id),
            literal(Value::new(10), ColumnTy::Id),
        ],
    ))?;
    let fresh = var(0, "losing fresh", ColumnTy::Id);
    let canonical = var(1, "predicted canonical", ColumnTy::Id);
    let second = backend.add_rule(rule(
        "losing fresh FD then late conflict",
        false,
        vec![],
        vec![
            GenericCoreAction::Let(
                Span::Panic,
                fresh.clone(),
                RuleActionCall::Primitive {
                    id: fresh_token,
                    name: "authenticated fresh".into(),
                    output: ColumnTy::Id,
                },
                vec![literal(label, ColumnTy::Base(types.string))],
            ),
            GenericCoreAction::Let(
                Span::Panic,
                canonical.clone(),
                RuleActionCall::Primitive {
                    id: set_if_empty,
                    name: "authenticated set-if-empty".into(),
                    output: ColumnTy::Id,
                },
                vec![literal(Value::new(7), ColumnTy::Id), variable(fresh)],
            ),
            GenericCoreAction::Set(
                Span::Panic,
                table_call(observation),
                vec![variable(canonical)],
                vec![literal(unit, unit_ty)],
            ),
            GenericCoreAction::Set(
                Span::Panic,
                table_call(conflict),
                vec![literal(Value::new(1), ColumnTy::Id)],
                vec![literal(Value::new(99), ColumnTy::Id)],
            ),
        ],
    ))?;
    backend.storage.set_next_fresh_id(100)?;
    let generation = backend.storage.generation()?;
    let error = run(&mut backend, &[first, second]).unwrap_err();
    assert!(format!("{error:#}").contains("AssertEq"), "{error:#}");
    assert_eq!(backend.table_size(view), 0);
    assert_eq!(backend.table_size(observation), 0);
    assert_eq!(backend.storage.next_fresh_id()?, 100);
    assert_eq!(backend.storage.generation()?, generation);

    backend.storage.with_connection(|connection| {
        connection.execute(&format!("DELETE FROM {}", sql_table(conflict)), [])?;
        Ok(())
    })?;
    assert!(run(&mut backend, &[first, second])?);
    assert_eq!(
        backend.lookup_id(view, &[Value::new(7)]),
        Some(Value::new(10))
    );
    assert_eq!(
        backend.lookup_id(observation, &[Value::new(10)]),
        Some(unit)
    );
    assert_eq!(backend.storage.next_fresh_id()?, 101);
    assert_eq!(backend.storage.generation()?, generation + 1);
    Ok(())
}

#[test]
fn empty_body_seminaive_fresh_fires_once() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = types(&mut backend);
    let unit = backend.base_values().get(());
    let label = backend
        .base_values()
        .get(Boxed::new("fresh label with ' quote".to_string()));
    let target = table(
        &mut backend,
        "general empty-body fresh target",
        vec![ColumnTy::Id, ColumnTy::Base(types.unit)],
        1,
        MergeFn::AssertEq,
        false,
    );
    let fresh_token = backend.register_get_fresh();
    let fresh = var(0, "fresh", ColumnTy::Id);
    let id = backend.add_rule(rule(
        "general seminaive empty body",
        true,
        vec![],
        vec![
            GenericCoreAction::Let(
                Span::Panic,
                fresh.clone(),
                RuleActionCall::Primitive {
                    id: fresh_token,
                    name: "spoofed fresh diagnostic".into(),
                    output: ColumnTy::Id,
                },
                vec![literal(label, ColumnTy::Base(types.string))],
            ),
            GenericCoreAction::Set(
                Span::Panic,
                table_call(target),
                vec![variable(fresh)],
                vec![literal(unit, ColumnTy::Base(types.unit))],
            ),
        ],
    ))?;

    assert!(run(&mut backend, &[id])?);
    assert_eq!(backend.table_size(target), 1);
    assert_eq!(backend.storage.next_fresh_id()?, 1);
    assert!(!run(&mut backend, &[id])?);
    assert_eq!(backend.table_size(target), 1);
    assert_eq!(backend.storage.next_fresh_id()?, 1);
    assert_eq!(backend.last_rule_match_counts(), &[0]);
    Ok(())
}

#[test]
fn multiple_live_bodies_and_duplicate_schedule_are_bounded() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = types(&mut backend);
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let left = table(
        &mut backend,
        "general left",
        vec![ColumnTy::Id, unit_ty],
        1,
        MergeFn::AssertEq,
        false,
    );
    let right = table(
        &mut backend,
        "general right",
        vec![ColumnTy::Id, unit_ty],
        1,
        MergeFn::AssertEq,
        false,
    );
    let target = table(
        &mut backend,
        "general joined target",
        vec![ColumnTy::Id, unit_ty],
        1,
        MergeFn::AssertEq,
        false,
    );
    backend.add_values(vec![
        (left, vec![Value::new(7), unit]),
        (right, vec![Value::new(7), unit]),
    ])?;
    let key = var(0, "key", ColumnTy::Id);
    let alias = var(1, "alias", ColumnTy::Id);
    let body = [left, right]
        .into_iter()
        .map(|id| GenericAtom {
            span: Span::Panic,
            head: RuleBodyCall::Table {
                id,
                read: ReadMode::Live,
            },
            args: vec![
                variable(key.clone()),
                literal(unit, ColumnTy::Base(types.unit)),
            ],
        })
        .collect();
    let id = backend.add_rule(rule(
        "general two-body join",
        true,
        body,
        vec![
            GenericCoreAction::LetAtomTerm(Span::Panic, alias.clone(), variable(key)),
            GenericCoreAction::Set(
                Span::Panic,
                table_call(target),
                vec![variable(alias)],
                vec![literal(unit, unit_ty)],
            ),
        ],
    ))?;

    let generation = backend.storage.generation()?;
    let error = run(&mut backend, &[id, id]).unwrap_err();
    assert!(error.to_string().contains("duplicate RuleId"));
    assert_eq!(backend.storage.generation()?, generation);
    assert_eq!(backend.table_size(target), 0);
    assert!(run(&mut backend, &[id])?);
    assert_eq!(backend.lookup_id(target, &[Value::new(7)]), Some(unit));
    assert!(!run(&mut backend, &[id])?);
    Ok(())
}

#[test]
fn fd_miss_is_staged_and_later_read_still_uses_fallback() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = types(&mut backend);
    let unit = backend.base_values().get(());
    let view_name = "general fd view exact authority";
    let set_if_empty = backend.register_set_if_empty(view_name.to_string(), 1, 1);
    let view_read = backend.register_view_column_read(view_name.to_string(), 1, 0);
    let view = table(
        &mut backend,
        view_name,
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::Old,
        true,
    );
    let output = table(
        &mut backend,
        "general fd observation",
        vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Base(types.unit)],
        1,
        MergeFn::AssertEq,
        false,
    );
    let canonical = var(0, "canonical", ColumnTy::Id);
    let observed = var(1, "observed", ColumnTy::Id);
    let id = backend.add_rule(rule(
        "general fd miss and fallback",
        false,
        vec![],
        vec![
            GenericCoreAction::Let(
                Span::Panic,
                canonical.clone(),
                RuleActionCall::Primitive {
                    id: set_if_empty,
                    name: "spoofed-set-if-empty-name".into(),
                    output: ColumnTy::Id,
                },
                vec![
                    literal(Value::new(1), ColumnTy::Id),
                    literal(Value::new(10), ColumnTy::Id),
                ],
            ),
            GenericCoreAction::Let(
                Span::Panic,
                observed.clone(),
                RuleActionCall::Primitive {
                    id: view_read,
                    name: "spoofed-view-read-name".into(),
                    output: ColumnTy::Id,
                },
                vec![
                    literal(Value::new(1), ColumnTy::Id),
                    literal(Value::new(99), ColumnTy::Id),
                ],
            ),
            GenericCoreAction::Set(
                Span::Panic,
                table_call(output),
                vec![variable(canonical), variable(observed)],
                vec![literal(unit, ColumnTy::Base(types.unit))],
            ),
        ],
    ))?;

    assert!(run(&mut backend, &[id])?);
    assert_eq!(
        backend.lookup_id(view, &[Value::new(1)]),
        Some(Value::new(10))
    );
    assert_eq!(
        backend.lookup_id(output, &[Value::new(10), Value::new(99)]),
        Some(unit)
    );
    assert!(run(&mut backend, &[id])?);
    assert_eq!(
        backend.lookup_id(output, &[Value::new(10), Value::new(10)]),
        Some(unit)
    );

    let generation = backend.storage.generation()?;
    let trace = backend.storage.latest_rule_sql();
    backend.free_external_func(view_read);
    let error = run(&mut backend, &[id]).unwrap_err();
    assert!(error.to_string().contains("freed or reused FD token"));
    assert_eq!(backend.storage.generation()?, generation);
    assert_eq!(backend.storage.latest_rule_sql(), trace);
    Ok(())
}

#[test]
fn fd_descriptor_ambiguity_schema_and_reuse_reject_without_rule_ids() -> Result<()> {
    let mut ambiguous = EGraph::new()?;
    let ambiguous_types = types(&mut ambiguous);
    let ambiguous_unit = ambiguous.base_values().get(());
    let ambiguous_name = "ambiguous registered FD view";
    let ambiguous_token = ambiguous.register_set_if_empty(ambiguous_name.to_string(), 1, 1);
    for _ in 0..2 {
        table(
            &mut ambiguous,
            ambiguous_name,
            vec![ColumnTy::Id, ColumnTy::Id],
            1,
            MergeFn::Old,
            true,
        );
    }
    let ambiguous_output = table(
        &mut ambiguous,
        "ambiguous FD output",
        vec![ColumnTy::Id, ColumnTy::Base(ambiguous_types.unit)],
        1,
        MergeFn::AssertEq,
        false,
    );
    let error = ambiguous
        .add_rule(set_if_empty_rule(
            ambiguous_token,
            ambiguous_output,
            ColumnTy::Base(ambiguous_types.unit),
            ambiguous_unit,
            vec![
                literal(Value::new(1), ColumnTy::Id),
                literal(Value::new(2), ColumnTy::Id),
            ],
        ))
        .unwrap_err();
    assert!(format!("{error:#}").contains("not unique"), "{error:#}");
    assert!(ambiguous.rules.is_empty());

    let mut mismatched = EGraph::new()?;
    let mismatch_types = types(&mut mismatched);
    let mismatch_unit = mismatched.base_values().get(());
    let mismatch_name = "schema-mismatched registered FD view";
    let mismatch_token = mismatched.register_set_if_empty(mismatch_name.to_string(), 2, 1);
    table(
        &mut mismatched,
        mismatch_name,
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::Old,
        true,
    );
    let mismatch_output = table(
        &mut mismatched,
        "mismatched FD output",
        vec![ColumnTy::Id, ColumnTy::Base(mismatch_types.unit)],
        1,
        MergeFn::AssertEq,
        false,
    );
    let error = mismatched
        .add_rule(set_if_empty_rule(
            mismatch_token,
            mismatch_output,
            ColumnTy::Base(mismatch_types.unit),
            mismatch_unit,
            vec![
                literal(Value::new(1), ColumnTy::Id),
                literal(Value::new(2), ColumnTy::Id),
                literal(Value::new(3), ColumnTy::Id),
            ],
        ))
        .unwrap_err();
    assert!(
        error.to_string().contains("descriptor disagrees"),
        "{error:#}"
    );
    assert!(mismatched.rules.is_empty());

    let mut reused = EGraph::new()?;
    let reused_types = types(&mut reused);
    let reused_unit = reused.base_values().get(());
    let reused_name = "freed registered FD view";
    let stale = reused.register_set_if_empty(reused_name.to_string(), 1, 1);
    reused.free_external_func(stale);
    let replacement = reused.new_panic("ordinary replacement token".to_string());
    assert_eq!(replacement, stale);
    table(
        &mut reused,
        reused_name,
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::Old,
        true,
    );
    let reused_output = table(
        &mut reused,
        "reused FD output",
        vec![ColumnTy::Id, ColumnTy::Base(reused_types.unit)],
        1,
        MergeFn::AssertEq,
        false,
    );
    let error = reused
        .add_rule(set_if_empty_rule(
            stale,
            reused_output,
            ColumnTy::Base(reused_types.unit),
            reused_unit,
            vec![
                literal(Value::new(1), ColumnTy::Id),
                literal(Value::new(2), ColumnTy::Id),
            ],
        ))
        .unwrap_err();
    assert!(
        format!("{error:#}").contains("unauthenticated or callback"),
        "{error:#}"
    );
    assert!(reused.rules.is_empty());
    Ok(())
}

#[test]
fn exact_count_heuristic_does_not_shadow_general_admission() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = types(&mut backend);
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let label = backend.base_values().get(Boxed::new(
        "exact-count heuristic shadow witness".to_string(),
    ));
    let target = table(
        &mut backend,
        "exact-count shadow target",
        vec![ColumnTy::Id, unit_ty],
        1,
        MergeFn::AssertEq,
        false,
    );
    let fresh_token = backend.register_get_fresh();
    let fresh = (0..14)
        .map(|index| var(index, &format!("fresh {index}"), ColumnTy::Id))
        .collect::<Vec<_>>();
    let aliases = (0..21)
        .map(|index| var(100 + index, &format!("alias {index}"), ColumnTy::Id))
        .collect::<Vec<_>>();
    let mut head = Vec::new();
    for binding in &fresh {
        head.push(GenericCoreAction::Let(
            Span::Panic,
            binding.clone(),
            RuleActionCall::Primitive {
                id: fresh_token,
                name: "authenticated fresh token with hostile diagnostic".into(),
                output: ColumnTy::Id,
            },
            vec![literal(label, ColumnTy::Base(types.string))],
        ));
    }
    for (index, binding) in aliases.iter().enumerate() {
        head.push(GenericCoreAction::LetAtomTerm(
            Span::Panic,
            binding.clone(),
            variable(fresh[index % fresh.len()].clone()),
        ));
    }
    for binding in &fresh {
        head.push(GenericCoreAction::Set(
            Span::Panic,
            table_call(target),
            vec![variable(binding.clone())],
            vec![literal(unit, unit_ty)],
        ));
    }
    assert_eq!(head.len(), 49);
    let id = backend.add_rule(rule(
        "exact-count heuristic must continue to general admission",
        true,
        vec![],
        head,
    ))?;

    assert!(run(&mut backend, &[id])?);
    assert_eq!(backend.table_size(target), 14);
    assert_eq!(backend.storage.next_fresh_id()?, 14);
    Ok(())
}

#[test]
fn unrelated_three_body_four_action_rule_uses_general_stream() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = types(&mut backend);
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let sources = (0..3)
        .map(|index| {
            table(
                &mut backend,
                &format!("unrelated source {index}"),
                vec![ColumnTy::Id, unit_ty],
                1,
                MergeFn::AssertEq,
                false,
            )
        })
        .collect::<Vec<_>>();
    let targets = (0..3)
        .map(|index| {
            table(
                &mut backend,
                &format!("unrelated target {index}"),
                vec![ColumnTy::Id, unit_ty],
                1,
                MergeFn::AssertEq,
                false,
            )
        })
        .collect::<Vec<_>>();
    backend.add_values(
        sources
            .iter()
            .map(|&source| (source, vec![Value::new(17), unit]))
            .collect(),
    )?;
    let key = var(0, "joined key", ColumnTy::Id);
    let alias = var(1, "joined alias", ColumnTy::Id);
    let body = sources
        .iter()
        .map(|&source| GenericAtom {
            span: Span::Panic,
            head: RuleBodyCall::Table {
                id: source,
                read: ReadMode::Live,
            },
            args: vec![variable(key.clone()), literal(unit, unit_ty)],
        })
        .collect();
    let mut head = vec![GenericCoreAction::LetAtomTerm(
        Span::Panic,
        alias.clone(),
        variable(key),
    )];
    for target in &targets {
        head.push(GenericCoreAction::Set(
            Span::Panic,
            table_call(*target),
            vec![variable(alias.clone())],
            vec![literal(unit, unit_ty)],
        ));
    }
    assert_eq!(head.len(), 4);
    let id = backend.add_rule(rule(
        "unrelated actionful three-body four-action rule",
        true,
        body,
        head,
    ))?;

    assert!(run(&mut backend, &[id])?);
    for target in targets {
        assert_eq!(backend.lookup_id(target, &[Value::new(17)]), Some(unit));
    }
    Ok(())
}

#[test]
fn lookup_keyed_by_an_earlier_lookup_result() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = types(&mut backend);
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let lookup = table(
        &mut backend,
        "chained Fail lookup",
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::Old,
        false,
    );
    let output = table(
        &mut backend,
        "chained lookup output",
        vec![ColumnTy::Id, unit_ty],
        1,
        MergeFn::AssertEq,
        false,
    );
    backend.add_values(vec![
        (lookup, vec![Value::new(1), Value::new(2)]),
        (lookup, vec![Value::new(2), Value::new(3)]),
    ])?;
    let first = var(0, "first lookup", ColumnTy::Id);
    let second = var(1, "second lookup", ColumnTy::Id);
    let id = backend.add_rule(rule(
        "later lookup key is earlier lookup result",
        false,
        vec![],
        vec![
            GenericCoreAction::Let(
                Span::Panic,
                first.clone(),
                table_call(lookup),
                vec![literal(Value::new(1), ColumnTy::Id)],
            ),
            GenericCoreAction::Let(
                Span::Panic,
                second.clone(),
                table_call(lookup),
                vec![variable(first)],
            ),
            GenericCoreAction::Set(
                Span::Panic,
                table_call(output),
                vec![variable(second)],
                vec![literal(unit, unit_ty)],
            ),
        ],
    ))?;

    assert!(run(&mut backend, &[id])?);
    assert_eq!(backend.lookup_id(output, &[Value::new(3)]), Some(unit));
    Ok(())
}

#[test]
fn fail_owner_preflight_rejects_before_materializing_a_value_slot() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = types(&mut backend);
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let lookup = table(
        &mut backend,
        "Fail lookup preflight table",
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::Old,
        false,
    );
    let output = table(
        &mut backend,
        "Fail lookup preflight output",
        vec![ColumnTy::Id, unit_ty],
        1,
        MergeFn::AssertEq,
        false,
    );
    let found = var(0, "Fail lookup result", ColumnTy::Id);
    let id = backend.add_rule(rule(
        "missing and duplicate Fail owner preflight",
        false,
        vec![],
        vec![
            GenericCoreAction::Let(
                Span::Panic,
                found.clone(),
                table_call(lookup),
                vec![literal(Value::new(1), ColumnTy::Id)],
            ),
            GenericCoreAction::Set(
                Span::Panic,
                table_call(output),
                vec![variable(found)],
                vec![literal(unit, unit_ty)],
            ),
        ],
    ))?;
    let plan = backend.rules[id.rep() as usize]
        .as_ref()
        .expect("rule remains registered")
        .plan
        .scalar_action()
        .expect("two-action rule is owned by the scalar stream");
    let preflight = plan
        .slot_preflight_sql("egglog_scalar_input", 0)
        .expect("DefaultVal::Fail lookup has a preflight");
    assert!(preflight.starts_with("SELECT EXISTS"));
    assert!(preflight.contains("FROM egglog_scalar_input AS prior"));
    assert!(preflight.contains("lookup.__owners <> 1"));
    assert!(!preflight.contains("CREATE TEMP TABLE"));
    assert!(!preflight.contains(" AS s0"));
    let materialize = plan.materialize_slot_sql(
        "egglog_scalar_input",
        "egglog_scalar_slot_test",
        0,
        0,
        1,
        None,
    );
    assert!(materialize.contains("JOIN egglog_function_"));
    assert!(!materialize.contains("LEFT JOIN"));
    assert!(!materialize.contains("first("));
    assert!(!materialize.contains("__invalid"));
    assert!(!materialize.contains("NULL"));
    assert!(
        plan.slot_invalid_sql("egglog_scalar_slot_test", 0)
            .is_none()
    );

    let generation = backend.storage.generation()?;
    let trace = backend.storage.latest_rule_sql();
    let missing = run(&mut backend, &[id]).unwrap_err();
    assert!(
        missing
            .to_string()
            .contains("did not have exactly one pre-wave owner")
    );
    assert_eq!(backend.storage.generation()?, generation);
    assert_eq!(backend.storage.latest_rule_sql(), trace);

    backend.storage.with_connection(|connection| {
        connection.execute(
            &format!(
                "INSERT INTO {} (c0, c1, __generation, __subsumed) VALUES
                 (CAST('1' AS UBIGINT), CAST('2' AS UBIGINT), CAST('0' AS UBIGINT), FALSE),
                 (CAST('1' AS UBIGINT), CAST('3' AS UBIGINT), CAST('0' AS UBIGINT), FALSE)",
                sql_table(lookup)
            ),
            [],
        )?;
        Ok(())
    })?;
    let duplicate = run(&mut backend, &[id]).unwrap_err();
    assert!(duplicate.to_string().contains("found duplicate owners"));
    assert_eq!(backend.storage.generation()?, generation);
    assert_eq!(backend.storage.latest_rule_sql(), trace);
    let scratch = backend.storage.with_connection(|connection| {
        connection
            .query_row(
                "SELECT count(*) FROM duckdb_tables()
                 WHERE table_name LIKE 'egglog_scalar_%'",
                [],
                |row| row.get::<_, u64>(0),
            )
            .map_err(Into::into)
    })?;
    assert_eq!(scratch, 0);
    assert_eq!(backend.table_size(output), 0);
    Ok(())
}

#[test]
fn late_conflict_rolls_back_fresh_generation_watermark_trace_and_scratch_then_retries() -> Result<()>
{
    let mut backend = EGraph::new()?;
    let types = types(&mut backend);
    let unit_ty = ColumnTy::Base(types.unit);
    let unit = backend.base_values().get(());
    let source = table(
        &mut backend,
        "late conflict source",
        vec![ColumnTy::Id, unit_ty],
        1,
        MergeFn::AssertEq,
        false,
    );
    let safe = table(
        &mut backend,
        "late conflict rolled-back target",
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::AssertEq,
        false,
    );
    let conflict = table(
        &mut backend,
        "late conflict final target",
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::AssertEq,
        false,
    );
    backend.add_values(vec![
        (source, vec![Value::new(1), unit]),
        (conflict, vec![Value::new(1), Value::new(8)]),
    ])?;
    let fresh_token = backend.register_get_fresh();
    let label = backend
        .base_values()
        .get(Boxed::new("late conflict fresh".to_string()));
    let key = var(0, "key", ColumnTy::Id);
    let fresh = var(1, "fresh", ColumnTy::Id);
    let id = backend.add_rule(rule(
        "late scalar conflict rollback and retry",
        true,
        vec![GenericAtom {
            span: Span::Panic,
            head: RuleBodyCall::Table {
                id: source,
                read: ReadMode::All,
            },
            args: vec![variable(key.clone()), literal(unit, unit_ty)],
        }],
        vec![
            GenericCoreAction::Let(
                Span::Panic,
                fresh.clone(),
                RuleActionCall::Primitive {
                    id: fresh_token,
                    name: "late conflict fresh".into(),
                    output: ColumnTy::Id,
                },
                vec![literal(label, ColumnTy::Base(types.string))],
            ),
            GenericCoreAction::Set(
                Span::Panic,
                table_call(safe),
                vec![variable(key.clone())],
                vec![variable(fresh)],
            ),
            GenericCoreAction::Set(
                Span::Panic,
                table_call(conflict),
                vec![variable(key)],
                vec![literal(Value::new(9), ColumnTy::Id)],
            ),
        ],
    ))?;
    let generation = backend.storage.generation()?;
    let fresh_before = backend.storage.next_fresh_id()?;
    let trace = backend.storage.latest_rule_sql();
    let error = run(&mut backend, &[id]).unwrap_err();
    assert!(error.to_string().contains("AssertEq"));
    assert_eq!(backend.storage.generation()?, generation);
    assert_eq!(backend.storage.next_fresh_id()?, fresh_before);
    assert_eq!(backend.storage.latest_rule_sql(), trace);
    assert_eq!(backend.table_size(safe), 0);
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

    backend.clear_table(conflict);
    assert!(run(&mut backend, &[id])?);
    assert_eq!(backend.last_rule_match_counts(), &[1]);
    assert_eq!(backend.storage.next_fresh_id()?, fresh_before + 1);
    assert_eq!(
        backend.lookup_id(safe, &[Value::new(1)]),
        Some(Value::new(fresh_before as u32))
    );
    assert_eq!(
        backend.lookup_id(conflict, &[Value::new(1)]),
        Some(Value::new(9))
    );
    Ok(())
}
