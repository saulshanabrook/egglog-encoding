use anyhow::Result;
use egglog_ast::{
    core::{
        GenericAtom, GenericAtomTerm, GenericCoreAction, GenericCoreActions, GenericCoreRule, Query,
    },
    generic_ast::Change,
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

#[derive(Clone, Copy)]
struct ScalarTypes {
    string: BaseValueId,
    i64: BaseValueId,
}

fn register_scalar_types<B: Backend>(backend: &mut B) -> ScalarTypes {
    backend.base_values_mut().register_type::<()>();
    let types = ScalarTypes {
        string: backend.base_values_mut().register_type::<Boxed<String>>(),
        i64: backend.base_values_mut().register_type::<i64>(),
    };
    backend
        .base_values_mut()
        .register_type::<Boxed<OrderedFloat<f64>>>();
    backend.base_values_mut().register_type::<bool>();
    types
}

fn table_with(
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

fn table(backend: &mut impl Backend, name: &str, schema: Vec<ColumnTy>) -> FunctionId {
    table_with(backend, name, schema, 1, MergeFn::Old, false)
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

fn table_call(id: FunctionId, hostile_diagnostic_name: &str) -> RuleActionCall {
    RuleActionCall::Table {
        id,
        name: hostile_diagnostic_name.into(),
    }
}

fn delete_action(
    target: FunctionId,
    keys: Vec<RuleTerm>,
) -> GenericCoreAction<RuleActionCall, RuleVar, RuleValue> {
    GenericCoreAction::Change(
        Span::Panic,
        Change::Delete,
        table_call(target, "ignored delete name; DROP TABLE"),
        keys,
    )
}

fn subsume_action(
    target: FunctionId,
    keys: Vec<RuleTerm>,
) -> GenericCoreAction<RuleActionCall, RuleVar, RuleValue> {
    GenericCoreAction::Change(
        Span::Panic,
        Change::Subsume,
        table_call(target, "ignored subsume name; DROP TABLE"),
        keys,
    )
}

fn set_action(
    target: FunctionId,
    keys: Vec<RuleTerm>,
    values: Vec<RuleTerm>,
) -> GenericCoreAction<RuleActionCall, RuleVar, RuleValue> {
    GenericCoreAction::Set(
        Span::Panic,
        table_call(target, "ignored set name; DROP TABLE"),
        keys,
        values,
    )
}

fn rule(
    name: &str,
    seminaive: bool,
    body: Vec<GenericAtom<RuleBodyCall, RuleVar, RuleValue>>,
    actions: Vec<GenericCoreAction<RuleActionCall, RuleVar, RuleValue>>,
) -> RuleSpec {
    RuleSpec {
        name: name.to_string(),
        seminaive,
        no_decomp: false,
        core: GenericCoreRule {
            span: Span::Panic,
            body: Query { atoms: body },
            head: GenericCoreActions::new(actions),
        },
    }
}

fn run<B: Backend>(backend: &mut B, rules: &[RuleId]) -> Result<bool> {
    Ok(backend
        .run_rules(RuleSetRun {
            name: Some("native-cleanup-effects"),
            rules,
        })?
        .changed())
}

fn delete_self_fixture<B: Backend>(backend: &mut B) -> Result<(FunctionId, RuleId)> {
    register_scalar_types(backend);
    let target = table(
        backend,
        "renamed pure delete target",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    backend.add_values(vec![(target, vec![Value::new(7), Value::new(70)])])?;
    let key = var(0, "semantic-key", ColumnTy::Id);
    let value = var(1, "semantic-value", ColumnTy::Id);
    let delete = backend.add_rule(rule(
        "renamed pure delete rule",
        true,
        vec![atom(target, vec![key.clone(), value])],
        vec![delete_action(target, vec![key])],
    ))?;
    Ok((target, delete))
}

#[test]
fn reference_pure_delete_report_is_false_while_duckdb_tracks_physical_freshness() -> Result<()> {
    let mut reference = egglog_bridge::EGraph::default();
    let (reference_target, reference_rule) = delete_self_fixture(&mut reference)?;
    assert!(!run(&mut reference, &[reference_rule])?);
    assert_eq!(reference.table_size(reference_target), 0);

    let mut backend = EGraph::new()?;
    let (target, delete) = delete_self_fixture(&mut backend)?;
    let generation_before = backend.storage.generation()?;
    let fresh_before = backend.storage.next_fresh_id()?;
    assert!(!run(&mut backend, &[delete])?);
    assert_eq!(backend.table_size(target), 0);
    assert_eq!(backend.storage.generation()?, generation_before + 1);
    assert_eq!(backend.storage.next_fresh_id()?, fresh_before);
    assert_eq!(backend.last_rule_insert_counts(), &[0]);

    // The equal logical row is a fresh seminaive event after reinsertion.
    backend.add_values(vec![(target, vec![Value::new(7), Value::new(70)])])?;
    let generation_before_second_delete = backend.storage.generation()?;
    assert!(!run(&mut backend, &[delete])?);
    assert_eq!(backend.table_size(target), 0);
    assert_eq!(
        backend.storage.generation()?,
        generation_before_second_delete + 1
    );
    assert_eq!(backend.last_rule_match_counts(), &[1]);
    let generation_after_second_delete = backend.storage.generation()?;
    assert!(!run(&mut backend, &[delete])?);
    assert_eq!(backend.last_rule_match_counts(), &[0]);
    assert_eq!(
        backend.storage.generation()?,
        generation_after_second_delete,
        "a missing Delete is not a physical transition"
    );
    Ok(())
}

#[test]
fn delete_only_accepts_nullary_mixed_scalar_and_synthetic_27_key_targets() -> Result<()> {
    let mut backend = EGraph::new()?;
    let types = register_scalar_types(&mut backend);

    let nullary = table(&mut backend, "nullary victim", vec![ColumnTy::Id]);
    backend.add_values(vec![(nullary, vec![Value::new(11)])])?;
    let nullary_value = var(0, "nullary-value", ColumnTy::Id);
    let nullary_rule = backend.add_rule(rule(
        "nullary delete",
        true,
        vec![atom(nullary, vec![nullary_value])],
        vec![delete_action(nullary, vec![])],
    ))?;
    assert!(!run(&mut backend, &[nullary_rule])?);
    assert_eq!(backend.table_size(nullary), 0);

    let string = ColumnTy::Base(types.string);
    let integer = ColumnTy::Base(types.i64);
    let mixed = table(
        &mut backend,
        "mixed target",
        vec![ColumnTy::Id, string, integer],
    );
    let hostile = backend.base_values().get(Boxed::new(
        "'); DROP TABLE egglog_function_0; --".to_string(),
    ));
    let minus_seven = backend.base_values().get(-7_i64);
    backend.add_values(vec![(mixed, vec![Value::new(12), hostile, minus_seven])])?;
    let mixed_value = var(1, "mixed-value", integer);
    let mixed_rule = backend.add_rule(rule(
        "hostile literal delete",
        true,
        vec![atom(
            mixed,
            vec![
                literal(Value::new(12), ColumnTy::Id),
                literal(hostile, string),
                mixed_value,
            ],
        )],
        vec![delete_action(
            mixed,
            vec![
                literal(Value::new(12), ColumnTy::Id),
                literal(hostile, string),
            ],
        )],
    ))?;
    assert!(!run(&mut backend, &[mixed_rule])?);
    assert_eq!(backend.table_size(mixed), 0);
    assert!(
        backend
            .storage
            .latest_rule_sql()
            .iter()
            .all(|sql| !sql.contains("DROP TABLE egglog_function_0; --"))
    );

    let mut schema = vec![ColumnTy::Id; 28];
    let wide = table(&mut backend, "synthetic 27 key target", schema.clone());
    let row = (0..28)
        .map(|index| Value::new(100 + index))
        .collect::<Vec<_>>();
    backend.add_values(vec![(wide, row)])?;
    let terms = schema
        .drain(..)
        .enumerate()
        .map(|(index, ty)| var(100 + index as u32, &format!("wide-{index}"), ty))
        .collect::<Vec<_>>();
    let wide_rule = backend.add_rule(rule(
        "synthetic 27 key delete",
        true,
        vec![atom(wide, terms.clone())],
        vec![delete_action(wide, terms[..27].to_vec())],
    ))?;
    assert!(!run(&mut backend, &[wide_rule])?);
    assert_eq!(backend.table_size(wide), 0);
    Ok(())
}

#[test]
fn three_body_four_delete_rule_bypasses_path_dispatch_without_consuming_rejected_rule_id()
-> Result<()> {
    let mut backend = EGraph::new()?;
    register_scalar_types(&mut backend);
    let targets = (0..4)
        .map(|index| {
            table(
                &mut backend,
                &format!("four-delete-target-{index}"),
                vec![ColumnTy::Id, ColumnTy::Id],
            )
        })
        .collect::<Vec<_>>();
    backend.add_values(
        targets
            .iter()
            .enumerate()
            .map(|(index, &target)| (target, vec![Value::new(1), Value::new(10 + index as u32)]))
            .collect(),
    )?;
    let key = var(0, "shared-delete-key", ColumnTy::Id);
    let values = (0..3)
        .map(|index| var(1 + index, &format!("body-value-{index}"), ColumnTy::Id))
        .collect::<Vec<_>>();
    let body = targets[..3]
        .iter()
        .zip(&values)
        .map(|(&target, value)| atom(target, vec![key.clone(), value.clone()]))
        .collect::<Vec<_>>();
    let valid = rule(
        "three table body with four deletes",
        true,
        body.clone(),
        targets
            .iter()
            .map(|&target| delete_action(target, vec![key.clone()]))
            .collect(),
    );

    let mut invalid = valid.clone();
    invalid.name = "same arity but invalid mixed path candidate".to_string();
    invalid.core.head.0[2] = set_action(targets[3], vec![key.clone()], vec![values[0].clone()]);
    let mixed = backend.add_rule(invalid)?;
    assert_eq!(mixed, RuleId::new(0));

    let accepted = backend.add_rule(valid)?;
    assert_eq!(
        accepted,
        RuleId::new(1),
        "the generic mixed cleanup rule consumes exactly one RuleId"
    );
    assert!(!run(&mut backend, &[accepted])?);
    for target in targets {
        assert_eq!(backend.table_size(target), 0);
    }
    assert_eq!(backend.last_rule_match_counts(), &[1]);
    assert_eq!(backend.last_rule_insert_counts(), &[0]);
    Ok(())
}

#[test]
fn duplicate_deletes_remove_live_subsumed_and_deferred_rows_without_insert_telemetry() -> Result<()>
{
    let mut backend = EGraph::new()?;
    register_scalar_types(&mut backend);
    let trigger = table(
        &mut backend,
        "delete trigger",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    let target = table_with(
        &mut backend,
        "deferred merge delete target",
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::New,
        true,
    );
    backend.add_values(vec![(trigger, vec![Value::new(4), Value::new(40)])])?;
    backend.storage.with_connection(|connection| {
        connection.execute(
            &format!(
                "INSERT INTO {} (c0, c1, __generation, __subsumed) VALUES
                 (CAST('4' AS UBIGINT), CAST('41' AS UBIGINT), CAST('0' AS UBIGINT), FALSE),
                 (CAST('5' AS UBIGINT), CAST('51' AS UBIGINT), CAST('0' AS UBIGINT), TRUE)",
                crate::storage::sql_table(target)
            ),
            [],
        )?;
        Ok(())
    })?;
    let key = var(0, "duplicate-key", ColumnTy::Id);
    let value = var(1, "trigger-value", ColumnTy::Id);
    let duplicate = backend.add_rule(rule(
        "two same target deletes",
        true,
        vec![atom(trigger, vec![key.clone(), value])],
        vec![
            delete_action(target, vec![key.clone()]),
            delete_action(target, vec![key]),
            delete_action(target, vec![literal(Value::new(5), ColumnTy::Id)]),
        ],
    ))?;
    assert!(!run(&mut backend, &[duplicate])?);
    assert_eq!(backend.table_size(target), 0);
    assert_eq!(backend.last_rule_insert_counts(), &[0]);
    assert_eq!(backend.storage.next_fresh_id()?, 0);
    Ok(())
}

fn phase_order_fixture(
    schedule_set_first: bool,
) -> Result<(EGraph, FunctionId, FunctionId, Vec<RuleId>)> {
    let mut backend = EGraph::new()?;
    register_scalar_types(&mut backend);
    let source = table(
        &mut backend,
        "phase source",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    let target = table(
        &mut backend,
        "phase target",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    let observed = table(
        &mut backend,
        "prewave observer",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    backend.add_values(vec![
        (source, vec![Value::new(1), Value::new(99)]),
        (target, vec![Value::new(1), Value::new(10)]),
    ])?;
    let key = var(0, "phase-key", ColumnTy::Id);
    let value = var(1, "phase-value", ColumnTy::Id);
    let delete = backend.add_rule(rule(
        "phase delete",
        true,
        vec![atom(target, vec![key.clone(), value.clone()])],
        vec![delete_action(target, vec![key.clone()])],
    ))?;
    let set = backend.add_rule(rule(
        "phase set",
        true,
        vec![atom(source, vec![key.clone(), value.clone()])],
        vec![set_action(target, vec![key.clone()], vec![value.clone()])],
    ))?;
    let observe = backend.add_rule(rule(
        "stable prewave observer",
        true,
        vec![atom(target, vec![key.clone(), value.clone()])],
        vec![set_action(observed, vec![key], vec![value])],
    ))?;
    let rules = if schedule_set_first {
        vec![set, observe, delete]
    } else {
        vec![delete, observe, set]
    };
    Ok((backend, target, observed, rules))
}

#[test]
fn global_delete_then_set_order_and_stable_prewave_hold_in_both_schedule_orders() -> Result<()> {
    for schedule_set_first in [false, true] {
        let (mut backend, target, observed, rules) = phase_order_fixture(schedule_set_first)?;
        assert!(run(&mut backend, &rules)?);
        assert_eq!(
            backend.lookup_row(target, &[Value::new(1)]),
            Some(vec![Value::new(1), Value::new(99)])
        );
        assert_eq!(
            backend.lookup_row(observed, &[Value::new(1)]),
            Some(vec![Value::new(1), Value::new(10)]),
            "observer must consume the pre-wave target row"
        );
    }
    Ok(())
}

fn subsume_fixture() -> Result<(EGraph, FunctionId, RuleId)> {
    let mut backend = EGraph::new()?;
    register_scalar_types(&mut backend);
    let target = table_with(
        &mut backend,
        "renamed subsumable target",
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::Old,
        true,
    );
    backend.add_values(vec![(target, vec![Value::new(2), Value::new(20)])])?;
    let key = var(0, "sub-key", ColumnTy::Id);
    let value = var(1, "sub-value", ColumnTy::Id);
    let subsume = backend.add_rule(rule(
        "renamed body-bound subsume",
        true,
        vec![atom(target, vec![key.clone(), value])],
        vec![subsume_action(target, vec![key])],
    ))?;
    Ok((backend, target, subsume))
}

#[test]
fn body_bound_subsume_preserves_values_marks_fresh_and_delete_removes_subsumed_rows() -> Result<()>
{
    let (mut backend, target, subsume) = subsume_fixture()?;
    let generation_before = backend.storage.generation()?;
    assert!(run(&mut backend, &[subsume])?);
    let rows = backend.storage.scan(backend.base_values(), target)?;
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].values, vec![Value::new(2), Value::new(20)]);
    assert!(rows[0].subsumed);
    assert_eq!(rows[0].generation, generation_before);
    assert_eq!(backend.storage.generation()?, generation_before + 1);
    assert_eq!(backend.last_rule_insert_counts(), &[0]);
    assert!(!run(&mut backend, &[subsume])?);
    assert_eq!(backend.last_rule_match_counts(), &[0]);

    let trigger = table(
        &mut backend,
        "subsumed delete trigger",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    backend.add_values(vec![(trigger, vec![Value::new(2), Value::new(200)])])?;
    let key = var(10, "delete-sub-key", ColumnTy::Id);
    let value = var(11, "delete-trigger-value", ColumnTy::Id);
    let delete = backend.add_rule(rule(
        "delete subsumed row",
        true,
        vec![atom(trigger, vec![key.clone(), value])],
        vec![delete_action(target, vec![key])],
    ))?;
    assert!(!run(&mut backend, &[delete])?);
    assert_eq!(backend.table_size(target), 0);
    Ok(())
}

#[test]
fn body_bound_subsume_preserves_a_complete_multi_value_deferred_row() -> Result<()> {
    let mut backend = EGraph::new()?;
    register_scalar_types(&mut backend);
    let target = table_with(
        &mut backend,
        "ordinary multi value target",
        vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        2,
        MergeFn::Columns(vec![MergeFn::OldCol(0), MergeFn::OldCol(1)]),
        true,
    );
    // Deferred merge targets cannot use native input yet. Seed the exact typed
    // physical row through the same safe public SQL boundary used by native
    // rule effects; Subsume itself must not invoke the deferred merge.
    backend.storage.with_connection(|connection| {
        connection.execute(
            &format!(
                "INSERT INTO {} (c0, c1, c2, __generation, __subsumed)
                 VALUES (CAST('8' AS UBIGINT), CAST('80' AS UBIGINT),
                         CAST('800' AS UBIGINT), CAST('0' AS UBIGINT), FALSE)",
                crate::storage::sql_table(target)
            ),
            [],
        )?;
        Ok(())
    })?;
    let key = var(0, "multi-key", ColumnTy::Id);
    let first = var(1, "multi-first", ColumnTy::Id);
    let second = var(2, "multi-second", ColumnTy::Id);
    let subsume = backend.add_rule(rule(
        "multi value body-bound subsume",
        true,
        vec![atom(target, vec![key.clone(), first, second])],
        vec![subsume_action(target, vec![key])],
    ))?;
    assert!(run(&mut backend, &[subsume])?);
    let rows = backend.storage.scan(backend.base_values(), target)?;
    assert_eq!(rows.len(), 1);
    assert_eq!(
        rows[0].values,
        vec![Value::new(8), Value::new(80), Value::new(800)]
    );
    assert!(rows[0].subsumed);
    Ok(())
}

#[test]
fn same_wave_delete_set_and_subsume_preserve_post_set_value_or_staged_fallback() -> Result<()> {
    // Delete + Subsume restores the staged pre-wave value as subsumed.
    let (mut fallback_backend, fallback_target, fallback_subsume) = subsume_fixture()?;
    let key = var(20, "fallback-key", ColumnTy::Id);
    let value = var(21, "fallback-value", ColumnTy::Id);
    let fallback_delete = fallback_backend.add_rule(rule(
        "fallback delete",
        true,
        vec![atom(fallback_target, vec![key.clone(), value])],
        vec![delete_action(fallback_target, vec![key])],
    ))?;
    assert!(run(
        &mut fallback_backend,
        &[fallback_subsume, fallback_delete]
    )?);
    let fallback = fallback_backend
        .storage
        .scan(fallback_backend.base_values(), fallback_target)?;
    assert_eq!(fallback.len(), 1);
    assert_eq!(fallback[0].values, vec![Value::new(2), Value::new(20)]);
    assert!(fallback[0].subsumed);

    // Delete + Set + Subsume uses the post-Set row, not the staged old value.
    let (mut backend, target, subsume) = subsume_fixture()?;
    let source = table(
        &mut backend,
        "post-set source",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    backend.add_values(vec![(source, vec![Value::new(2), Value::new(200)])])?;
    let old_key = var(30, "old-key", ColumnTy::Id);
    let old_value = var(31, "old-value", ColumnTy::Id);
    let delete = backend.add_rule(rule(
        "post-set delete",
        true,
        vec![atom(target, vec![old_key.clone(), old_value])],
        vec![delete_action(target, vec![old_key])],
    ))?;
    let new_key = var(32, "new-key", ColumnTy::Id);
    let new_value = var(33, "new-value", ColumnTy::Id);
    let set = backend.add_rule(rule(
        "post-set insert",
        true,
        vec![atom(source, vec![new_key.clone(), new_value.clone()])],
        vec![set_action(target, vec![new_key], vec![new_value])],
    ))?;
    assert!(run(&mut backend, &[subsume, set, delete])?);
    let rows = backend.storage.scan(backend.base_values(), target)?;
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].values, vec![Value::new(2), Value::new(200)]);
    assert!(rows[0].subsumed);
    assert_eq!(backend.last_rule_insert_counts(), &[0, 1, 0]);
    Ok(())
}

#[test]
fn late_assert_eq_failure_rolls_back_delete_generation_scratch_and_watermarks() -> Result<()> {
    let mut backend = EGraph::new()?;
    register_scalar_types(&mut backend);
    let delete_target = table(
        &mut backend,
        "rollback delete target",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    let conflict_source = table(
        &mut backend,
        "rollback conflict source",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    let conflict_target = table_with(
        &mut backend,
        "rollback assert target",
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::AssertEq,
        false,
    );
    backend.add_values(vec![
        (delete_target, vec![Value::new(1), Value::new(10)]),
        (conflict_source, vec![Value::new(2), Value::new(20)]),
        (conflict_target, vec![Value::new(2), Value::new(21)]),
    ])?;
    let delete_key = var(0, "rollback-delete-key", ColumnTy::Id);
    let delete_value = var(1, "rollback-delete-value", ColumnTy::Id);
    let delete = backend.add_rule(rule(
        "rollback first delete",
        true,
        vec![atom(delete_target, vec![delete_key.clone(), delete_value])],
        vec![delete_action(delete_target, vec![delete_key])],
    ))?;
    let set_key = var(2, "rollback-set-key", ColumnTy::Id);
    let set_value = var(3, "rollback-set-value", ColumnTy::Id);
    let conflict = backend.add_rule(rule(
        "rollback late conflict",
        true,
        vec![atom(
            conflict_source,
            vec![set_key.clone(), set_value.clone()],
        )],
        vec![set_action(conflict_target, vec![set_key], vec![set_value])],
    ))?;
    let generation_before = backend.storage.generation()?;
    let fresh_before = backend.storage.next_fresh_id()?;
    let error = backend
        .run_rules(RuleSetRun {
            name: Some("cleanup rollback"),
            rules: &[delete, conflict],
        })
        .unwrap_err();
    assert!(error.to_string().contains("AssertEq"));
    assert_eq!(
        backend.lookup_row(delete_target, &[Value::new(1)]),
        Some(vec![Value::new(1), Value::new(10)])
    );
    assert_eq!(backend.storage.generation()?, generation_before);
    assert_eq!(backend.storage.next_fresh_id()?, fresh_before);
    for rule in [delete, conflict] {
        assert_eq!(
            backend.rules[rule.rep() as usize]
                .as_ref()
                .unwrap()
                .watermark,
            0
        );
    }
    backend.storage.with_connection(|connection| {
        let stages = connection.query_row(
            "SELECT count(*) FROM duckdb_tables() WHERE table_name LIKE 'egglog_rule_stage_%'",
            [],
            |row| row.get::<_, u64>(0),
        )?;
        assert_eq!(stages, 0);
        Ok(())
    })?;
    Ok(())
}

#[test]
fn cleanup_admission_is_fail_closed_and_does_not_consume_rule_ids() -> Result<()> {
    let mut backend = EGraph::new()?;
    register_scalar_types(&mut backend);
    let source = table(
        &mut backend,
        "admission source",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    let target = table_with(
        &mut backend,
        "admission target",
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::Old,
        true,
    );
    let no_subsume = table(
        &mut backend,
        "admission no subsume",
        vec![ColumnTy::Id, ColumnTy::Id],
    );
    let key = var(0, "admission-key", ColumnTy::Id);
    let value = var(1, "admission-value", ColumnTy::Id);
    let body = vec![atom(target, vec![key.clone(), value.clone()])];

    let accepted = vec![
        rule(
            "mixed delete set",
            true,
            body.clone(),
            vec![
                delete_action(target, vec![key.clone()]),
                set_action(target, vec![key.clone()], vec![value.clone()]),
            ],
        ),
        rule(
            "multiple subsumes",
            true,
            body.clone(),
            vec![
                subsume_action(target, vec![key.clone()]),
                subsume_action(target, vec![key.clone()]),
            ],
        ),
        rule(
            "delete diagnostic metadata name",
            true,
            body.clone(),
            vec![delete_action(
                target,
                vec![var(0, "different-name", ColumnTy::Id)],
            )],
        ),
    ];
    for (index, spec) in accepted.into_iter().enumerate() {
        assert_eq!(backend.add_rule(spec)?, RuleId::new(index as u32));
    }

    let invalid = vec![
        rule(
            "subsume unsupported table",
            true,
            vec![atom(no_subsume, vec![key.clone(), value.clone()])],
            vec![subsume_action(no_subsume, vec![key.clone()])],
        ),
        rule(
            "subsume without target body",
            true,
            vec![atom(source, vec![key.clone(), value.clone()])],
            vec![subsume_action(target, vec![key.clone()])],
        ),
        rule(
            "subsume inconsistent body key",
            true,
            body.clone(),
            vec![subsume_action(
                target,
                vec![literal(Value::new(9), ColumnTy::Id)],
            )],
        ),
        rule(
            "delete wrong arity",
            true,
            body.clone(),
            vec![delete_action(target, vec![])],
        ),
        rule(
            "delete unbound metadata",
            true,
            body.clone(),
            vec![delete_action(
                target,
                vec![var(99, "missing", ColumnTy::Id)],
            )],
        ),
        rule(
            "delete global key",
            true,
            body.clone(),
            vec![delete_action(
                target,
                vec![GenericAtomTerm::Global(
                    Span::Panic,
                    RuleVar {
                        id: 100,
                        name: "global-key".into(),
                        ty: ColumnTy::Id,
                    },
                )],
            )],
        ),
    ];
    for spec in invalid {
        let label = spec.name.clone();
        if let Ok(id) = backend.add_rule(spec) {
            panic!("{label} unexpectedly admitted as {id:?}");
        }
    }

    let primitive = backend.new_panic("must not run".to_string());
    let primitive_delete = rule(
        "primitive delete target",
        true,
        body.clone(),
        vec![GenericCoreAction::Change(
            Span::Panic,
            Change::Delete,
            RuleActionCall::Primitive {
                id: primitive,
                name: "primitive".into(),
                output: ColumnTy::Id,
            },
            vec![key.clone()],
        )],
    );
    assert!(
        backend
            .add_rule(primitive_delete)
            .unwrap_err()
            .to_string()
            .contains("primitive")
    );

    let deferred = table_with(
        &mut backend,
        "deferred delete is allowed",
        vec![ColumnTy::Id, ColumnTy::Id],
        1,
        MergeFn::New,
        false,
    );
    let valid = backend.add_rule(rule(
        "valid deferred delete",
        true,
        body,
        vec![delete_action(deferred, vec![key])],
    ))?;
    assert_eq!(
        valid,
        RuleId::new(3),
        "failed cleanup admissions must not consume RuleIds"
    );
    Ok(())
}
