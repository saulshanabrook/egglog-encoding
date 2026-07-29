use anyhow::Result;
use egglog_ast::{
    core::{
        GenericAtom, GenericAtomTerm, GenericCoreAction, GenericCoreActions, GenericCoreRule, Query,
    },
    generic_ast::Change,
    span::Span,
};
use egglog_backend_trait::{
    Backend, ColumnTy, DefaultVal, FunctionConfig, FunctionId, MergeFn, ReadMode, RuleActionCall,
    RuleBodyCall, RuleId, RuleSetRun, RuleSpec, RuleValue, RuleVar, Value,
};
use egglog_core_relations::Boxed;
use egglog_numeric_id::NumericId;

use crate::{
    EGraph,
    marker_rekey::compile_marker_rekey,
    path_compress_tests::path_rule,
    rebuild_tests::{BodyOrder, Fixture, ids, ordered_union},
    storage::sql_table,
};

type Term = GenericAtomTerm<RuleVar, RuleValue>;

struct MarkerFixture {
    inner: Fixture,
    marker: FunctionId,
}

impl MarkerFixture {
    fn new(inner: Fixture, name: &str) -> Self {
        Self::with_marker_config(inner, name, |_| {})
    }

    fn with_marker_config(
        mut inner: Fixture,
        name: &str,
        configure: impl FnOnce(&mut FunctionConfig),
    ) -> Self {
        let mut config = marker_config(&inner, name);
        configure(&mut config);
        let marker = inner.backend.add_table(config);
        Self { inner, marker }
    }

    fn one_id(name: &str) -> Result<Self> {
        Ok(Self::new(Fixture::one_id(name)?, name))
    }

    fn rule(&self, name: &str, key_index: usize, order: BodyOrder) -> RuleSpec {
        let mut next = 10_000_u32;
        let keys = self
            .inner
            .key_types
            .iter()
            .enumerate()
            .map(|(index, &ty)| {
                let variable = var(next, &format!("{name}-key-{index}"), ty);
                next += 7;
                variable
            })
            .collect::<Vec<_>>();
        let marker_output = var(
            next,
            "opaque-marker-output",
            ColumnTy::Base(self.inner.unit),
        );
        next += 7;
        let canonical = var(next, "opaque-canonical", ColumnTy::Id);
        next += 7;
        let uf_payload = var(next, "opaque-unused-payload", ColumnTy::Id);
        next += 7;
        let neq_result = var(
            next,
            "opaque-inequality-result",
            ColumnTy::Base(self.inner.unit),
        );

        let mut marker_args = keys.clone();
        marker_args.push(marker_output);
        let marker_atom = table_atom(self.marker, ReadMode::All, marker_args);
        let uf_atom = table_atom(
            self.inner.uf,
            ReadMode::All,
            vec![keys[key_index].clone(), canonical.clone(), uf_payload],
        );
        let inequality = inequality(
            self.inner.tokens.neq,
            self.inner.unit,
            keys[key_index].clone(),
            canonical.clone(),
            neq_result,
        );
        let atoms = ordered_atoms(order, marker_atom, uf_atom, inequality);

        let mut canonical_keys = keys.clone();
        canonical_keys[key_index] = canonical;
        RuleSpec {
            name: format!("{name}-totally-renamed-marker-rekey"),
            seminaive: true,
            no_decomp: false,
            core: GenericCoreRule {
                span: Span::Panic,
                body: Query { atoms },
                head: GenericCoreActions::new(vec![
                    GenericCoreAction::Set(
                        Span::Panic,
                        table_call(self.marker),
                        canonical_keys,
                        vec![unit_literal(&self.inner.backend, self.inner.unit)],
                    ),
                    GenericCoreAction::Change(
                        Span::Panic,
                        Change::Delete,
                        table_call(self.marker),
                        keys,
                    ),
                ]),
            },
        }
    }

    fn insert_marker(&self, keys: &[Value], generation: u64, subsumed: bool) -> Result<()> {
        let mut row = keys.to_vec();
        row.push(self.inner.backend.base_values().get(()));
        self.inner
            .insert_typed(self.marker, &row, generation, subsumed)
    }

    fn run(&mut self, rules: &[RuleId]) -> Result<bool> {
        self.inner.run(rules)
    }

    fn marker_row(&self, keys: &[Value]) -> Option<Vec<Value>> {
        self.inner.backend.lookup_row(self.marker, keys)
    }
}

fn marker_config(inner: &Fixture, name: &str) -> FunctionConfig {
    let mut schema = inner.key_types.clone();
    schema.push(ColumnTy::Base(inner.unit));
    FunctionConfig {
        schema,
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::AssertEq,
        name: format!("{name}-opaque-marker"),
        can_subsume: false,
    }
}

fn ordered_atoms(
    order: BodyOrder,
    marker: GenericAtom<RuleBodyCall, RuleVar, RuleValue>,
    uf: GenericAtom<RuleBodyCall, RuleVar, RuleValue>,
    inequality: GenericAtom<RuleBodyCall, RuleVar, RuleValue>,
) -> Vec<GenericAtom<RuleBodyCall, RuleVar, RuleValue>> {
    match order {
        BodyOrder::ViewUfNeq => vec![marker, uf, inequality],
        BodyOrder::NeqUfView => vec![inequality, uf, marker],
        BodyOrder::UfViewNeq => vec![uf, marker, inequality],
    }
}

fn table_atom(
    id: FunctionId,
    read: ReadMode,
    args: Vec<Term>,
) -> GenericAtom<RuleBodyCall, RuleVar, RuleValue> {
    GenericAtom {
        span: Span::Panic,
        head: RuleBodyCall::Table { id, read },
        args,
    }
}

fn inequality(
    token: egglog_backend_trait::ExternalFunctionId,
    unit: egglog_backend_trait::BaseValueId,
    lhs: Term,
    rhs: Term,
    result: Term,
) -> GenericAtom<RuleBodyCall, RuleVar, RuleValue> {
    GenericAtom {
        span: Span::Panic,
        head: RuleBodyCall::Primitive {
            id: token,
            name: "renamed-marker-neq-diagnostic".into(),
            output: ColumnTy::Base(unit),
        },
        args: vec![lhs, rhs, result],
    }
}

fn table_call(id: FunctionId) -> RuleActionCall {
    RuleActionCall::Table {
        id,
        name: format!("opaque-target-{}", id.rep()).into(),
    }
}

fn var(id: u32, name: &str, ty: ColumnTy) -> Term {
    variable(RuleVar {
        id,
        name: name.into(),
        ty,
    })
}

fn variable(variable: RuleVar) -> Term {
    GenericAtomTerm::Var(Span::Panic, variable)
}

fn literal(value: Value, ty: ColumnTy) -> Term {
    GenericAtomTerm::Literal(Span::Panic, RuleValue { value, ty })
}

fn unit_literal(backend: &EGraph, unit: egglog_backend_trait::BaseValueId) -> Term {
    literal(backend.base_values().get(()), ColumnTy::Base(unit))
}

fn marker_keys(backend: &EGraph, marker: FunctionId) -> Result<Vec<Vec<u32>>> {
    Ok(backend
        .storage
        .scan(backend.base_values(), marker)?
        .into_iter()
        .map(|row| {
            row.values[..row.values.len() - 1]
                .iter()
                .map(|value| value.rep())
                .collect()
        })
        .collect())
}

#[test]
fn renamed_permuted_marker_executes_without_ids_or_host_callbacks() -> Result<()> {
    for order in [
        BodyOrder::ViewUfNeq,
        BodyOrder::NeqUfView,
        BodyOrder::UfViewNeq,
    ] {
        let mut fixture = MarkerFixture::one_id("marker-hostile-name")?;
        let rule = fixture
            .inner
            .backend
            .add_rule(fixture.rule("hostile-rule-name", 0, order))?;
        fixture.inner.backend.storage.set_next_fresh_id(100)?;
        fixture.insert_marker(&[Value::new(30)], 0, false)?;
        fixture
            .inner
            .insert_ids(fixture.inner.uf, &[30, 20, 80], 0, false)?;

        assert!(fixture.run(&[rule])?);
        assert_eq!(fixture.inner.backend.storage.next_fresh_id()?, 100);
        assert_eq!(fixture.inner.backend.last_rule_match_counts(), &[1]);
        assert_eq!(fixture.inner.backend.last_rule_insert_counts(), &[1]);
        assert_eq!(fixture.marker_row(&[Value::new(30)]), None);
        assert_eq!(
            ids(fixture.marker_row(&[Value::new(20)])),
            Some(vec![20, 0])
        );
        assert!(!fixture.run(&[rule])?);
        assert_eq!(fixture.inner.scratch_count()?, 0);
        assert!(
            fixture
                .inner
                .backend
                .storage
                .latest_rule_sql()
                .iter()
                .all(|sql| !sql.contains("hostile") && !sql.contains('?'))
        );
    }
    Ok(())
}

#[test]
fn mixed_typed_twenty_seven_key_index_twenty_one_executes() -> Result<()> {
    let inner = Fixture::new("wide-marker", |string, i64_ty| {
        (0..27)
            .map(|index| match index % 3 {
                0 => ColumnTy::Id,
                1 => ColumnTy::Base(i64_ty),
                _ => ColumnTy::Base(string),
            })
            .collect()
    })?;
    let mut fixture = MarkerFixture::new(inner, "wide-marker");
    let selected = 21;
    assert_eq!(fixture.inner.key_types[selected], ColumnTy::Id);
    let rule = fixture.inner.backend.add_rule(fixture.rule(
        "wide-index-twenty-one",
        selected,
        BodyOrder::NeqUfView,
    ))?;
    let keys = fixture
        .inner
        .key_types
        .iter()
        .enumerate()
        .map(|(index, ty)| match ty {
            ColumnTy::Id => Value::new(100 + index as u32),
            ColumnTy::Base(base) if *base == fixture.inner.i64_ty => {
                fixture.inner.backend.base_values().get(index as i64 - 10)
            }
            ColumnTy::Base(base) if *base == fixture.inner.string => fixture
                .inner
                .backend
                .base_values()
                .get(Boxed::new(format!("key-{index}-'--"))),
            _ => unreachable!(),
        })
        .collect::<Vec<_>>();
    let leader = Value::new(900);
    fixture.insert_marker(&keys, 0, false)?;
    fixture.inner.insert_ids(
        fixture.inner.uf,
        &[keys[selected].rep() as u64, leader.rep() as u64, 901],
        0,
        false,
    )?;
    assert!(fixture.run(&[rule])?);
    let mut canonical = keys.clone();
    canonical[selected] = leader;
    assert!(fixture.marker_row(&keys).is_none());
    assert!(fixture.marker_row(&canonical).is_some());
    assert_eq!(fixture.inner.backend.storage.next_fresh_id()?, 0);
    Ok(())
}

#[test]
fn subsumed_all_row_rekeys_to_existing_canonical_as_deletion_only() -> Result<()> {
    let mut fixture = MarkerFixture::one_id("deletion-only")?;
    let rule = fixture.inner.backend.add_rule(fixture.rule(
        "deletion-only-rule",
        0,
        BodyOrder::UfViewNeq,
    ))?;
    fixture
        .inner
        .backend
        .storage
        .set_next_fresh_id(u32::MAX as u64)?;
    fixture.insert_marker(&[Value::new(30)], 0, true)?;
    fixture.insert_marker(&[Value::new(20)], 0, false)?;
    fixture
        .inner
        .insert_ids(fixture.inner.uf, &[30, 20, 80], 0, false)?;

    assert!(!fixture.run(&[rule])?);
    assert_eq!(fixture.inner.backend.storage.generation()?, 2);
    assert_eq!(
        fixture.inner.backend.storage.next_fresh_id()?,
        u32::MAX as u64
    );
    assert_eq!(fixture.inner.backend.last_rule_match_counts(), &[1]);
    assert_eq!(fixture.inner.backend.last_rule_insert_counts(), &[0]);
    assert!(fixture.marker_row(&[Value::new(30)]).is_none());
    assert!(fixture.marker_row(&[Value::new(20)]).is_some());
    Ok(())
}

#[test]
fn marker_chain_advances_one_stable_hop_per_bounded_call() -> Result<()> {
    let mut fixture = MarkerFixture::one_id("cross-call-chain")?;
    let rule = fixture.inner.backend.add_rule(fixture.rule(
        "cross-call-chain-rule",
        0,
        BodyOrder::ViewUfNeq,
    ))?;
    fixture.insert_marker(&[Value::new(30)], 0, false)?;
    fixture
        .inner
        .insert_ids(fixture.inner.uf, &[30, 20, 80], 0, false)?;
    fixture
        .inner
        .insert_ids(fixture.inner.uf, &[20, 10, 81], 0, false)?;

    assert!(fixture.run(&[rule])?);
    assert!(fixture.marker_row(&[Value::new(20)]).is_some());
    assert!(fixture.marker_row(&[Value::new(10)]).is_none());
    assert!(fixture.run(&[rule])?);
    assert!(fixture.marker_row(&[Value::new(20)]).is_none());
    assert!(fixture.marker_row(&[Value::new(10)]).is_some());
    assert!(!fixture.run(&[rule])?);
    Ok(())
}

#[test]
fn converging_marker_candidates_install_one_canonical_owner() -> Result<()> {
    let mut fixture = MarkerFixture::one_id("converging")?;
    let rule =
        fixture
            .inner
            .backend
            .add_rule(fixture.rule("converging-rule", 0, BodyOrder::NeqUfView))?;
    fixture.insert_marker(&[Value::new(30)], 0, false)?;
    fixture.insert_marker(&[Value::new(40)], 0, false)?;
    fixture
        .inner
        .insert_ids(fixture.inner.uf, &[30, 20, 80], 0, false)?;
    fixture
        .inner
        .insert_ids(fixture.inner.uf, &[40, 20, 81], 0, false)?;

    assert!(fixture.run(&[rule])?);
    assert_eq!(fixture.inner.backend.last_rule_match_counts(), &[2]);
    assert_eq!(fixture.inner.backend.last_rule_insert_counts(), &[1]);
    assert_eq!(
        marker_keys(&fixture.inner.backend, fixture.marker)?,
        vec![vec![20]]
    );
    assert_eq!(fixture.inner.backend.storage.next_fresh_id()?, 0);
    Ok(())
}

fn run_cross_delete_schedule(reversed: bool) -> Result<Vec<Vec<u32>>> {
    let inner = Fixture::new("cross-delete", |_, _| vec![ColumnTy::Id, ColumnTy::Id])?;
    let mut fixture = MarkerFixture::new(inner, "cross-delete");
    let first =
        fixture
            .inner
            .backend
            .add_rule(fixture.rule("first-key-rule", 0, BodyOrder::ViewUfNeq))?;
    let second =
        fixture
            .inner
            .backend
            .add_rule(fixture.rule("second-key-rule", 1, BodyOrder::UfViewNeq))?;
    fixture.insert_marker(&[Value::new(30), Value::new(7)], 0, false)?;
    fixture.insert_marker(&[Value::new(20), Value::new(7)], 0, false)?;
    fixture
        .inner
        .insert_ids(fixture.inner.uf, &[30, 20, 80], 0, false)?;
    fixture
        .inner
        .insert_ids(fixture.inner.uf, &[7, 6, 81], 0, false)?;
    fixture.inner.backend.storage.set_next_fresh_id(700)?;
    let rules = if reversed {
        [second, first]
    } else {
        [first, second]
    };
    assert!(fixture.run(&rules)?);
    assert_eq!(fixture.inner.backend.storage.next_fresh_id()?, 700);
    assert_eq!(
        fixture.inner.backend.last_rule_match_counts(),
        if reversed { &[2, 1] } else { &[1, 2] }
    );
    let mut keys = marker_keys(&fixture.inner.backend, fixture.marker)?;
    keys.sort();
    Ok(keys)
}

#[test]
fn global_deletes_precede_marker_sets_in_both_schedule_orders() -> Result<()> {
    let expected = vec![vec![20, 6], vec![20, 7], vec![30, 6]];
    assert_eq!(run_cross_delete_schedule(false)?, expected);
    assert_eq!(run_cross_delete_schedule(true)?, expected);
    Ok(())
}

struct MixedScheduleOutcome {
    marker_row: Vec<u32>,
    view_row: Vec<u32>,
    next_fresh: u64,
    inserted_rows: Vec<usize>,
}

fn run_mixed_schedule(marker_first: bool) -> Result<MixedScheduleOutcome> {
    let mut fixture = MarkerFixture::one_id("mixed-standard-marker")?;
    let marker = fixture.inner.backend.add_rule(fixture.rule(
        "mixed-marker-rule",
        0,
        BodyOrder::NeqUfView,
    ))?;
    let standard = fixture.inner.backend.add_rule(fixture.inner.eq_rule(
        "mixed-standard-rule",
        0,
        BodyOrder::UfViewNeq,
    ))?;
    fixture.inner.backend.storage.set_next_fresh_id(100)?;
    fixture.insert_marker(&[Value::new(20)], 0, false)?;
    fixture
        .inner
        .insert_ids(fixture.inner.view, &[30, 40, 70], 0, false)?;
    fixture
        .inner
        .insert_ids(fixture.inner.uf, &[30, 20, 80], 0, false)?;
    fixture
        .inner
        .insert_ids(fixture.inner.uf, &[20, 10, 81], 0, false)?;
    let rules = if marker_first {
        [marker, standard]
    } else {
        [standard, marker]
    };
    assert!(fixture.run(&rules)?);
    let marker_row = ids(fixture.marker_row(&[Value::new(10)])).unwrap();
    let view_row = ids(fixture
        .inner
        .backend
        .lookup_row(fixture.inner.view, &[Value::new(20)]))
    .unwrap();
    Ok(MixedScheduleOutcome {
        marker_row,
        view_row,
        next_fresh: fixture.inner.backend.storage.next_fresh_id()?,
        inserted_rows: fixture.inner.backend.last_rule_insert_counts().to_vec(),
    })
}

#[test]
fn mixed_standard_marker_schedule_is_stable_and_marker_reserves_no_ids() -> Result<()> {
    let standard_first = run_mixed_schedule(false)?;
    let marker_first = run_mixed_schedule(true)?;
    assert_eq!(standard_first.marker_row, vec![10, 0]);
    assert_eq!(standard_first.view_row, vec![20, 40, 100]);
    assert_eq!(standard_first.next_fresh, 101);
    assert_eq!(marker_first.marker_row, standard_first.marker_row);
    assert_eq!(marker_first.view_row, standard_first.view_row);
    assert_eq!(marker_first.next_fresh, standard_first.next_fresh);
    assert_eq!(standard_first.inserted_rows, vec![1, 1]);
    assert_eq!(marker_first.inserted_rows, vec![1, 1]);
    Ok(())
}

#[test]
fn mixed_late_conflict_rolls_back_rows_ids_watermarks_and_scratch() -> Result<()> {
    let mut fixture = MarkerFixture::one_id("mixed-rollback")?;
    let marker =
        fixture
            .inner
            .backend
            .add_rule(fixture.rule("rollback-marker", 0, BodyOrder::ViewUfNeq))?;
    let standard = fixture.inner.backend.add_rule(fixture.inner.eq_rule(
        "rollback-standard",
        0,
        BodyOrder::NeqUfView,
    ))?;

    let unit = fixture.inner.backend.base_values().get(());
    fixture.inner.backend.add_values(vec![(
        fixture.inner.sym,
        vec![Value::new(900), Value::new(901), unit],
    )])?;
    assert_eq!(fixture.inner.backend.storage.generation()?, 2);
    assert!(!fixture.run(&[marker, standard])?);
    assert_eq!(fixture.inner.watermark(marker), 2);
    assert_eq!(fixture.inner.watermark(standard), 2);
    let prior_sql = fixture.inner.backend.storage.latest_rule_sql();

    fixture.inner.backend.storage.set_next_fresh_id(500)?;
    fixture.insert_marker(&[Value::new(20)], 2, false)?;
    fixture
        .inner
        .insert_ids(fixture.inner.view, &[30, 40, 70], 2, false)?;
    fixture
        .inner
        .insert_ids(fixture.inner.uf, &[30, 20, 80], 2, false)?;
    fixture
        .inner
        .insert_ids(fixture.inner.uf, &[20, 10, 81], 2, false)?;
    fixture
        .inner
        .backend
        .storage
        .with_connection(|connection| {
            connection.execute(
                &format!(
                    "INSERT INTO {} VALUES (
                     CAST('70' AS UBIGINT), CAST('0' AS BIGINT),
                     CAST('80' AS UBIGINT), CAST('500' AS UBIGINT),
                     FALSE, CAST('2' AS UBIGINT), FALSE
                 )",
                    sql_table(fixture.inner.congr)
                ),
                [],
            )?;
            Ok(())
        })?;

    let error = fixture.run(&[marker, standard]).unwrap_err();
    assert!(error.to_string().contains("AssertEq"), "{error:#}");
    assert_eq!(fixture.inner.backend.storage.generation()?, 2);
    assert_eq!(fixture.inner.backend.storage.next_fresh_id()?, 500);
    assert_eq!(fixture.inner.watermark(marker), 2);
    assert_eq!(fixture.inner.watermark(standard), 2);
    assert!(fixture.marker_row(&[Value::new(20)]).is_some());
    assert!(fixture.marker_row(&[Value::new(10)]).is_none());
    assert!(
        fixture
            .inner
            .backend
            .lookup_row(fixture.inner.view, &[Value::new(30)])
            .is_some()
    );
    assert_eq!(fixture.inner.scratch_count()?, 0);
    assert_eq!(fixture.inner.backend.storage.latest_rule_sql(), prior_sql);

    fixture
        .inner
        .backend
        .storage
        .with_connection(|connection| {
            connection.execute(
                &format!("DELETE FROM {}", sql_table(fixture.inner.congr)),
                [],
            )?;
            Ok(())
        })?;
    assert!(fixture.run(&[marker, standard])?);
    assert_eq!(fixture.inner.backend.storage.next_fresh_id()?, 501);
    assert!(fixture.marker_row(&[Value::new(10)]).is_some());
    assert!(
        fixture
            .inner
            .backend
            .lookup_row(fixture.inner.view, &[Value::new(20)])
            .is_some()
    );
    Ok(())
}

#[test]
fn duplicate_marker_owner_rejects_before_mutation() -> Result<()> {
    let mut fixture = MarkerFixture::one_id("duplicate-owner")?;
    let rule = fixture.inner.backend.add_rule(fixture.rule(
        "duplicate-owner-rule",
        0,
        BodyOrder::UfViewNeq,
    ))?;
    fixture.inner.backend.storage.set_next_fresh_id(42)?;
    fixture.insert_marker(&[Value::new(30)], 0, false)?;
    fixture.insert_marker(&[Value::new(30)], 0, false)?;
    fixture
        .inner
        .insert_ids(fixture.inner.uf, &[30, 20, 80], 0, false)?;
    let error = fixture.run(&[rule]).unwrap_err();
    assert!(error.to_string().contains("duplicate owners"), "{error:#}");
    assert_eq!(fixture.inner.backend.storage.generation()?, 1);
    assert_eq!(fixture.inner.backend.storage.next_fresh_id()?, 42);
    assert_eq!(fixture.inner.watermark(rule), 0);
    assert_eq!(fixture.inner.scratch_count()?, 0);
    assert_eq!(
        marker_keys(&fixture.inner.backend, fixture.marker)?.len(),
        2
    );
    Ok(())
}

fn assert_rejected_preserves_rule_id(
    fixture: &mut MarkerFixture,
    rule: RuleSpec,
    fragment: &str,
) -> Result<()> {
    let classified = compile_marker_rekey(
        &fixture.inner.backend.storage,
        fixture.inner.backend.base_values(),
        &fixture.inner.backend.native_primitives,
        &fixture.inner.backend.fresh_tokens,
        &rule,
    );
    let classifier_error = classified.unwrap_err().to_string();
    assert!(
        classifier_error.contains("marker rekey"),
        "{classifier_error}"
    );
    assert!(classifier_error.contains(fragment), "{classifier_error}");

    let registration_error = fixture
        .inner
        .backend
        .add_rule(rule)
        .unwrap_err()
        .to_string();
    assert!(
        registration_error.contains("marker rekey"),
        "{registration_error}"
    );
    assert!(
        registration_error.contains(fragment),
        "{registration_error}"
    );
    let valid_config = marker_config(&fixture.inner, "valid-after-rejection");
    fixture.marker = fixture.inner.backend.add_table(valid_config);
    let valid = fixture.rule("valid-after-rejection", 0, BodyOrder::NeqUfView);
    assert_eq!(fixture.inner.backend.add_rule(valid)?, RuleId::new(0));
    Ok(())
}

fn assert_fallthrough_preserves_rule_id(fixture: &mut MarkerFixture, rule: RuleSpec) -> Result<()> {
    let classified = compile_marker_rekey(
        &fixture.inner.backend.storage,
        fixture.inner.backend.base_values(),
        &fixture.inner.backend.native_primitives,
        &fixture.inner.backend.fresh_tokens,
        &rule,
    )?;
    assert!(classified.is_none(), "near-shape was captured as a marker");
    let valid = fixture.rule("valid-after-fallthrough", 0, BodyOrder::NeqUfView);
    assert_eq!(fixture.inner.backend.add_rule(valid)?, RuleId::new(0));
    Ok(())
}

#[test]
fn marker_tri_state_matrix_is_fail_closed_without_consuming_rule_ids() -> Result<()> {
    let mut mode = MarkerFixture::one_id("bad-mode")?;
    let mut rule = mode.rule("bad-mode-rule", 0, BodyOrder::ViewUfNeq);
    let marker = mode.marker;
    let RuleBodyCall::Table { read, .. } = &mut rule
        .core
        .body
        .atoms
        .iter_mut()
        .find(|atom| matches!(atom.head, RuleBodyCall::Table { id, .. } if id == marker))
        .expect("marker atom")
        .head
    else {
        unreachable!()
    };
    *read = ReadMode::Live;
    assert_rejected_preserves_rule_id(&mut mode, rule, "requires All")?;

    let mut primitive = MarkerFixture::one_id("bad-primitive")?;
    let mut rule = primitive.rule("bad-primitive-rule", 0, BodyOrder::UfViewNeq);
    let RuleBodyCall::Primitive { id, name, .. } = &mut rule.core.body.atoms[2].head else {
        unreachable!()
    };
    *id = primitive.inner.tokens.ordering_min;
    *name = "!=".into();
    assert_rejected_preserves_rule_id(&mut primitive, rule, "ValueNeq")?;

    let mut primitive_output = MarkerFixture::one_id("bad-primitive-output")?;
    let mut rule = primitive_output.rule("bad-primitive-output-rule", 0, BodyOrder::NeqUfView);
    let RuleBodyCall::Primitive { output, .. } = &mut rule.core.body.atoms[0].head else {
        unreachable!()
    };
    *output = ColumnTy::Id;
    assert_rejected_preserves_rule_id(&mut primitive_output, rule, "ValueNeq")?;

    let mut primitive_arity = MarkerFixture::one_id("bad-primitive-arity")?;
    let mut rule = primitive_arity.rule("bad-primitive-arity-rule", 0, BodyOrder::ViewUfNeq);
    let inequality = rule
        .core
        .body
        .atoms
        .iter_mut()
        .find(|atom| matches!(atom.head, RuleBodyCall::Primitive { .. }))
        .expect("inequality atom");
    inequality.args.pop();
    assert_rejected_preserves_rule_id(&mut primitive_arity, rule, "wrong arity")?;

    let mut roles = MarkerFixture::one_id("bad-primitive-roles")?;
    let mut rule = roles.rule("bad-primitive-roles-rule", 0, BodyOrder::ViewUfNeq);
    let inequality = rule
        .core
        .body
        .atoms
        .iter_mut()
        .find(|atom| matches!(atom.head, RuleBodyCall::Primitive { .. }))
        .expect("inequality atom");
    inequality.args.swap(0, 1);
    assert_rejected_preserves_rule_id(&mut roles, rule, "inequality lhs")?;

    let mut order = MarkerFixture::one_id("bad-action-order")?;
    let mut rule = order.rule("bad-action-order-rule", 0, BodyOrder::NeqUfView);
    rule.core.head.0.reverse();
    assert_rejected_preserves_rule_id(&mut order, rule, "first action")?;

    let mut change = MarkerFixture::one_id("bad-change-kind")?;
    let mut rule = change.rule("bad-change-kind-rule", 0, BodyOrder::UfViewNeq);
    let GenericCoreAction::Change(_, kind, _, _) = &mut rule.core.head.0[1] else {
        unreachable!()
    };
    *kind = Change::Subsume;
    assert_rejected_preserves_rule_id(&mut change, rule, "must be Delete")?;

    let mut action_target = MarkerFixture::one_id("bad-action-target")?;
    let mut rule = action_target.rule("bad-action-target-rule", 0, BodyOrder::ViewUfNeq);
    let GenericCoreAction::Set(_, call, _, _) = &mut rule.core.head.0[0] else {
        unreachable!()
    };
    *call = RuleActionCall::Primitive {
        id: action_target.inner.tokens.neq,
        name: "opaque-non-table-target".into(),
        output: ColumnTy::Base(action_target.inner.unit),
    };
    assert_rejected_preserves_rule_id(&mut action_target, rule, "canonical marker Set")?;

    let mut action_unit = MarkerFixture::one_id("bad-action-unit")?;
    let mut rule = action_unit.rule("bad-action-unit-rule", 0, BodyOrder::NeqUfView);
    let GenericCoreAction::Set(_, _, _, values) = &mut rule.core.head.0[0] else {
        unreachable!()
    };
    values[0] = literal(Value::new(17), ColumnTy::Id);
    assert_rejected_preserves_rule_id(&mut action_unit, rule, "Unit literal")?;

    let mut flags = MarkerFixture::one_id("bad-flags")?;
    let mut rule = flags.rule("bad-flags-rule", 0, BodyOrder::ViewUfNeq);
    rule.no_decomp = true;
    assert_rejected_preserves_rule_id(&mut flags, rule, "seminaive and decomposed")?;

    let mut seminaive = MarkerFixture::one_id("bad-seminaive")?;
    let mut rule = seminaive.rule("bad-seminaive-rule", 0, BodyOrder::UfViewNeq);
    rule.seminaive = false;
    assert_rejected_preserves_rule_id(&mut seminaive, rule, "seminaive and decomposed")?;

    let inner = Fixture::one_id("bad-marker-config")?;
    let mut config = MarkerFixture::with_marker_config(inner, "bad-marker-config", |config| {
        config.merge = MergeFn::Old;
    });
    let rule = config.rule("bad-marker-config-rule", 0, BodyOrder::NeqUfView);
    assert_rejected_preserves_rule_id(&mut config, rule, "incompatible configuration")?;

    let inner = Fixture::one_id("bad-marker-default")?;
    let unit_value = inner.backend.base_values().get(());
    let mut default = MarkerFixture::with_marker_config(inner, "bad-marker-default", |config| {
        config.default = DefaultVal::Const(unit_value);
    });
    let rule = default.rule("bad-marker-default-rule", 0, BodyOrder::UfViewNeq);
    assert_rejected_preserves_rule_id(&mut default, rule, "incompatible configuration")?;

    let inner = Fixture::one_id("bad-marker-identity")?;
    let mut identity = MarkerFixture::with_marker_config(inner, "bad-marker-identity", |config| {
        config.n_identity_vals = Some(1);
    });
    let rule = identity.rule("bad-marker-identity-rule", 0, BodyOrder::ViewUfNeq);
    assert_rejected_preserves_rule_id(&mut identity, rule, "incompatible configuration")?;

    let inner = Fixture::one_id("bad-marker-subsumable")?;
    let mut subsumable =
        MarkerFixture::with_marker_config(inner, "bad-marker-subsumable", |config| {
            config.can_subsume = true;
        });
    let rule = subsumable.rule("bad-marker-subsumable-rule", 0, BodyOrder::NeqUfView);
    assert_rejected_preserves_rule_id(&mut subsumable, rule, "incompatible configuration")?;

    let mut alias = MarkerFixture::one_id("bad-alias")?;
    let mut rule = alias.rule("bad-alias-rule", 0, BodyOrder::ViewUfNeq);
    let uf = rule
        .core
        .body
        .atoms
        .iter_mut()
        .find(|atom| matches!(atom.head, RuleBodyCall::Table { id, .. } if id == alias.inner.uf))
        .expect("UF atom");
    uf.args[2] = uf.args[1].clone();
    assert_rejected_preserves_rule_id(&mut alias, rule, "aliases structurally distinct")?;

    let mut uf_config = MarkerFixture::one_id("bad-uf-config")?;
    let original_uf = uf_config.inner.uf;
    let info = uf_config.inner.backend.storage.table_info(original_uf)?;
    let malformed_uf = uf_config.inner.backend.add_table(FunctionConfig {
        schema: info.schema.clone(),
        n_vals: info.n_vals,
        n_identity_vals: info.n_identity_vals,
        default: info.default,
        merge: ordered_union(
            uf_config.inner.tokens,
            uf_config.inner.label,
            uf_config.inner.string,
            uf_config.inner.unit,
            uf_config.inner.backend.base_values().get(()),
            uf_config.inner.sym,
            uf_config.inner.trans,
            original_uf,
            false,
        ),
        name: "opaque-non-self-displacing-uf".to_string(),
        can_subsume: info.can_subsume,
    });
    let mut rule = uf_config.rule("bad-uf-config-rule", 0, BodyOrder::UfViewNeq);
    for atom in &mut rule.core.body.atoms {
        if let RuleBodyCall::Table { id, .. } = &mut atom.head
            && *id == original_uf
        {
            *id = malformed_uf;
        }
    }
    assert_rejected_preserves_rule_id(&mut uf_config, rule, "incompatible UF")?;

    let mut orientation = MarkerFixture::one_id("bad-uf-orientation")?;
    let original_uf = orientation.inner.uf;
    let predicted = orientation.inner.backend.peek_next_function_id();
    let unit_value = orientation.inner.backend.base_values().get(());
    let opposite = orientation.inner.backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        n_vals: 2,
        n_identity_vals: Some(1),
        default: DefaultVal::Fail,
        merge: ordered_union(
            orientation.inner.tokens,
            orientation.inner.label,
            orientation.inner.string,
            orientation.inner.unit,
            unit_value,
            orientation.inner.sym,
            orientation.inner.trans,
            predicted,
            true,
        ),
        name: "opaque-opposite-orientation-uf".to_string(),
        can_subsume: false,
    });
    assert_eq!(opposite, predicted);
    let mut rule = orientation.rule("bad-uf-orientation-rule", 0, BodyOrder::NeqUfView);
    for atom in &mut rule.core.body.atoms {
        if let RuleBodyCall::Table { id, .. } = &mut atom.head
            && *id == original_uf
        {
            *id = opposite;
        }
    }
    assert_rejected_preserves_rule_id(&mut orientation, rule, "incompatible UF")?;

    Ok(())
}

#[test]
fn marker_outer_near_shapes_explicitly_fall_through_without_allocating_rule_ids() -> Result<()> {
    let mut both_ordered = MarkerFixture::one_id("both-ordered-union")?;
    let original_marker = both_ordered.marker;
    let mut rule = both_ordered.rule("both-ordered-union-rule", 0, BodyOrder::ViewUfNeq);
    for atom in &mut rule.core.body.atoms {
        if let RuleBodyCall::Table { id, .. } = &mut atom.head
            && *id == original_marker
        {
            *id = both_ordered.inner.view;
        }
    }
    assert_fallthrough_preserves_rule_id(&mut both_ordered, rule)?;

    let mut path = MarkerFixture::one_id("path-near-shape")?;
    let rule = path_rule(
        "path-near-shape-rule",
        path.inner.unit,
        path.inner.string,
        path.inner.label,
        path.inner.tokens,
        path.inner.trans,
        path.inner.uf,
    );
    assert_fallthrough_preserves_rule_id(&mut path, rule)?;

    let mut container = MarkerFixture::one_id("container-near-shape")?;
    let mut rule = container.rule("container-near-shape-rule", 0, BodyOrder::NeqUfView);
    let atom = rule
        .core
        .body
        .atoms
        .iter_mut()
        .find(
            |atom| matches!(atom.head, RuleBodyCall::Table { id, .. } if id == container.inner.uf),
        )
        .expect("UF atom");
    atom.head = RuleBodyCall::Primitive {
        id: container.inner.tokens.neq,
        name: "opaque-container-rebuild".into(),
        output: ColumnTy::Id,
    };
    assert_fallthrough_preserves_rule_id(&mut container, rule)?;

    let mut custom = MarkerFixture::one_id("custom-block-near-shape")?;
    let custom_block = custom.inner.backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::Block {
            actions: Vec::new(),
            result: Box::new(MergeFn::Old),
        },
        name: "opaque-custom-block".to_string(),
        can_subsume: false,
    });
    let original_uf = custom.inner.uf;
    let mut rule = custom.rule("custom-block-near-shape-rule", 0, BodyOrder::UfViewNeq);
    for atom in &mut rule.core.body.atoms {
        if let RuleBodyCall::Table { id, .. } = &mut atom.head
            && *id == original_uf
        {
            *id = custom_block;
        }
    }
    assert_fallthrough_preserves_rule_id(&mut custom, rule)?;

    let mut outer_fallthrough = MarkerFixture::one_id("outer-fallthrough")?;
    let mut rule = outer_fallthrough.rule("outer-fallthrough-rule", 0, BodyOrder::ViewUfNeq);
    for atom in &mut rule.core.body.atoms {
        if let RuleBodyCall::Table { id, .. } = &mut atom.head
            && *id == outer_fallthrough.inner.uf
        {
            *id = outer_fallthrough.inner.sym;
        }
    }
    assert_fallthrough_preserves_rule_id(&mut outer_fallthrough, rule)?;

    let mut direct = MarkerFixture::one_id("ordinary-direct")?;
    let mut rule = direct.rule("ordinary-direct-rule", 0, BodyOrder::UfViewNeq);
    let mut marker_atom = rule
        .core
        .body
        .atoms
        .iter()
        .find(|atom| matches!(atom.head, RuleBodyCall::Table { id, .. } if id == direct.marker))
        .expect("marker atom")
        .clone();
    let RuleBodyCall::Table { read, .. } = &mut marker_atom.head else {
        unreachable!()
    };
    *read = ReadMode::Live;
    rule.core.body.atoms = vec![marker_atom];
    rule.core.head.0.remove(0);
    assert!(
        compile_marker_rekey(
            &direct.inner.backend.storage,
            direct.inner.backend.base_values(),
            &direct.inner.backend.native_primitives,
            &direct.inner.backend.fresh_tokens,
            &rule,
        )?
        .is_none()
    );
    assert_eq!(direct.inner.backend.add_rule(rule)?, RuleId::new(0));

    let mut standard = Fixture::one_id("ordinary-standard")?;
    let rule = standard.eq_rule("ordinary-standard-rule", 0, BodyOrder::ViewUfNeq);
    assert!(
        compile_marker_rekey(
            &standard.backend.storage,
            standard.backend.base_values(),
            &standard.backend.native_primitives,
            &standard.backend.fresh_tokens,
            &rule,
        )?
        .is_none()
    );
    assert_eq!(standard.backend.add_rule(rule)?, RuleId::new(0));
    Ok(())
}

#[test]
fn marker_only_schedule_uses_one_transaction_and_leaves_no_scratch() -> Result<()> {
    let mut fixture = MarkerFixture::one_id("marker-only-transaction")?;
    let rule = fixture.inner.backend.add_rule(fixture.rule(
        "marker-only-transaction-rule",
        0,
        BodyOrder::ViewUfNeq,
    ))?;
    fixture.insert_marker(&[Value::new(4)], 0, false)?;
    fixture
        .inner
        .insert_ids(fixture.inner.uf, &[4, 3, 2], 0, false)?;
    let report = fixture.inner.backend.run_rules(RuleSetRun {
        name: Some("opaque-marker-run"),
        rules: &[rule],
    })?;
    assert!(report.changed());
    assert_eq!(fixture.inner.scratch_count()?, 0);
    assert_eq!(fixture.inner.backend.storage.generation()?, 2);
    Ok(())
}
