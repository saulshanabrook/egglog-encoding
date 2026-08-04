use anyhow::Result;
use egglog_ast::{
    core::{
        GenericAtom, GenericAtomTerm, GenericCoreAction, GenericCoreActions, GenericCoreRule, Query,
    },
    span::Span,
};
use egglog_backend_trait::{
    Backend, BaseValueId, ColumnTy, DefaultVal, ExternalFunctionId, FunctionConfig, FunctionId,
    MergeFn, ReadMode, RuleActionCall, RuleBodyCall, RuleId, RuleSetRun, RuleSpec, RuleValue,
    RuleVar, Value,
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

fn types(backend: &mut EGraph) -> Types {
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
    backend: &mut EGraph,
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

fn run(backend: &mut EGraph, rules: &[RuleId]) -> Result<bool> {
    Ok(backend
        .run_rules(RuleSetRun {
            name: Some("general scalar action test"),
            rules,
        })?
        .changed())
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
    let materialize =
        plan.materialize_slot_sql("egglog_scalar_input", "egglog_scalar_slot_test", 0, 0, 1);
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
    assert!(
        duplicate
            .to_string()
            .contains("did not have exactly one pre-wave owner")
    );
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
