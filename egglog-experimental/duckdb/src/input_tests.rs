use anyhow::Result;
use egglog_ast::{
    core::{
        GenericAtom, GenericAtomTerm, GenericCoreAction, GenericCoreActions, GenericCoreRule, Query,
    },
    span::Span,
};
use egglog_backend_trait::{
    Backend, BaseValueId, ColumnTy, DefaultVal, ExternalFunctionId, FunctionConfig, FunctionId,
    MergeAction, MergeFn, NativeInputValue, NativePrimitive, ReadMode, RuleActionCall,
    RuleBodyCall, RuleSetRun, RuleSpec, RuleValue, RuleVar, Value,
};
use egglog_core_relations::Boxed;
use egglog_numeric_id::NumericId;
use ordered_float::OrderedFloat;

use crate::EGraph;
use crate::storage::{WriteCapability, sql_table};

#[derive(Clone, Copy)]
struct OrderedPrimitives {
    proof_min: ExternalFunctionId,
    proof_max: ExternalFunctionId,
    ordering_min: ExternalFunctionId,
    ordering_max: ExternalFunctionId,
    fresh: ExternalFunctionId,
}

struct Fixture<B> {
    backend: B,
    unit: BaseValueId,
    string: BaseValueId,
    label: Value,
    primitives: OrderedPrimitives,
    sym: FunctionId,
    trans: FunctionId,
    uf: FunctionId,
    view: FunctionId,
}

impl<B: Backend> Fixture<B> {
    fn new(mut backend: B, prefix: &str) -> Result<Self> {
        let unit = backend.base_values_mut().register_type::<()>();
        backend.base_values_mut().register_type::<bool>();
        backend.base_values_mut().register_type::<i64>();
        backend
            .base_values_mut()
            .register_type::<Boxed<OrderedFloat<f64>>>();
        let string = backend.base_values_mut().register_type::<Boxed<String>>();
        let label = backend
            .base_values()
            .get(Boxed::new(format!("{prefix}-opaque-domain")));
        let primitives = ordered_primitives(&mut backend);
        let unit_value = backend.base_values().get(());

        let sym = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Base(unit)],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::AssertEq,
            name: format!("{prefix}-unary-evidence"),
            can_subsume: false,
        });
        let trans = backend.add_table(FunctionConfig {
            schema: vec![
                ColumnTy::Id,
                ColumnTy::Id,
                ColumnTy::Id,
                ColumnTy::Base(unit),
            ],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::AssertEq,
            name: format!("{prefix}-binary-evidence"),
            can_subsume: false,
        });
        let predicted_uf = backend.peek_next_function_id();
        let uf = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
            n_vals: 2,
            n_identity_vals: Some(1),
            default: DefaultVal::Fail,
            merge: ordered_union(
                primitives,
                label,
                string,
                unit,
                unit_value,
                sym,
                trans,
                predicted_uf,
                false,
            ),
            name: format!("{prefix}-parent-map"),
            can_subsume: false,
        });
        assert_eq!(uf, predicted_uf);
        let view = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
            n_vals: 2,
            n_identity_vals: Some(1),
            default: DefaultVal::Fail,
            merge: ordered_union(
                primitives, label, string, unit, unit_value, sym, trans, uf, true,
            ),
            name: format!("{prefix}-view"),
            can_subsume: true,
        });
        Ok(Self {
            backend,
            unit,
            string,
            label,
            primitives,
            sym,
            trans,
            uf,
            view,
        })
    }

    fn advance_fresh_to_100(&mut self) {
        for expected in 0..100 {
            assert_eq!(self.backend.fresh_id(), Value::new(expected));
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
struct IdentityTranscript {
    view: Option<Vec<Value>>,
    sym_rows: usize,
    trans_rows: usize,
    uf_rows: usize,
    next_id: Value,
}

fn identity_transcript<B: Backend>(mut fixture: Fixture<B>) -> Result<IdentityTranscript> {
    fixture.advance_fresh_to_100();
    fixture.backend.add_values(vec![(
        fixture.view,
        vec![Value::new(1), Value::new(100), Value::new(90)],
    )])?;
    fixture.backend.add_values_with_fresh(vec![(
        fixture.view,
        vec![
            NativeInputValue::Existing(Value::new(1)),
            NativeInputValue::FreshSlot(0),
            NativeInputValue::FreshSlot(1),
        ],
    )])?;
    Ok(IdentityTranscript {
        view: fixture.backend.lookup_row(fixture.view, &[Value::new(1)]),
        sym_rows: fixture.backend.table_size(fixture.sym),
        trans_rows: fixture.backend.table_size(fixture.trans),
        uf_rows: fixture.backend.table_size(fixture.uf),
        next_id: fixture.backend.fresh_id(),
    })
}

fn ordered_primitives(backend: &mut impl Backend) -> OrderedPrimitives {
    let proof_min = backend.register_native_primitive(NativePrimitive::SelectMinPayload);
    let proof_max = backend.register_native_primitive(NativePrimitive::SelectMaxPayload);
    let ordering_min = backend.register_native_primitive(NativePrimitive::OrderingMin);
    let ordering_max = backend.register_native_primitive(NativePrimitive::OrderingMax);
    let fresh = backend.register_get_fresh();
    OrderedPrimitives {
        proof_min,
        proof_max,
        ordering_min,
        ordering_max,
        fresh,
    }
}

#[allow(clippy::too_many_arguments)]
fn ordered_union(
    primitives: OrderedPrimitives,
    label: Value,
    string: BaseValueId,
    unit: BaseValueId,
    unit_value: Value,
    sym: FunctionId,
    trans: FunctionId,
    displaced: FunctionId,
    eclass_to_term: bool,
) -> MergeFn {
    let proof = |id, name: &str| MergeFn::Primitive {
        id,
        name: name.to_string(),
        input: vec![ColumnTy::Id; 4],
        output: ColumnTy::Id,
        args: vec![
            MergeFn::OldCol(0),
            MergeFn::OldCol(1),
            MergeFn::NewCol(0),
            MergeFn::NewCol(1),
        ],
    };
    let ordering = |id, name: &str| MergeFn::Primitive {
        id,
        name: name.to_string(),
        input: vec![ColumnTy::Id; 2],
        output: ColumnTy::Id,
        args: vec![MergeFn::OldCol(0), MergeFn::NewCol(0)],
    };
    let fresh = || MergeFn::Primitive {
        id: primitives.fresh,
        name: "renamed-input-fresh-diagnostic".to_string(),
        input: vec![ColumnTy::Base(string)],
        output: ColumnTy::Id,
        args: vec![MergeFn::Const {
            value: label,
            ty: ColumnTy::Base(string),
        }],
    };
    let unit_constant = || MergeFn::Const {
        value: unit_value,
        ty: ColumnTy::Base(unit),
    };
    let sym_input = if eclass_to_term { 1 } else { 0 };
    let (trans_first, trans_second) = if eclass_to_term { (0, 2) } else { (2, 1) };
    MergeFn::Block {
        actions: vec![
            MergeAction::Let {
                slot: 0,
                value: proof(primitives.proof_max, "renamed-input-select-max"),
            },
            MergeAction::Let {
                slot: 1,
                value: proof(primitives.proof_min, "renamed-input-select-min"),
            },
            MergeAction::Let {
                slot: 2,
                value: fresh(),
            },
            MergeAction::Set(
                sym,
                vec![
                    MergeFn::LetVar(sym_input),
                    MergeFn::LetVar(2),
                    unit_constant(),
                ],
            ),
            MergeAction::Let {
                slot: 3,
                value: fresh(),
            },
            MergeAction::Set(
                trans,
                vec![
                    MergeFn::LetVar(trans_first),
                    MergeFn::LetVar(trans_second),
                    MergeFn::LetVar(3),
                    unit_constant(),
                ],
            ),
            MergeAction::Set(
                displaced,
                vec![
                    ordering(primitives.ordering_max, "renamed-input-ordering-max"),
                    ordering(primitives.ordering_min, "renamed-input-ordering-min"),
                    MergeFn::LetVar(3),
                ],
            ),
        ],
        result: Box::new(MergeFn::Columns(vec![
            ordering(primitives.ordering_min, "another-input-ordering-min"),
            MergeFn::LetVar(1),
        ])),
    }
}

#[derive(Debug, Eq, PartialEq)]
struct CollisionTranscript {
    view: Option<Vec<Value>>,
    sym: Option<Vec<Value>>,
    trans: Option<Vec<Value>>,
    uf: Option<Vec<Value>>,
    next_id: Value,
}

fn collision_transcript<B: Backend>(
    mut fixture: Fixture<B>,
    old_identity: u32,
    old_payload: u32,
) -> Result<CollisionTranscript> {
    fixture.advance_fresh_to_100();
    fixture.backend.add_values(vec![(
        fixture.view,
        vec![
            Value::new(1),
            Value::new(old_identity),
            Value::new(old_payload),
        ],
    )])?;
    fixture.backend.add_values_with_fresh(vec![(
        fixture.view,
        vec![
            NativeInputValue::Existing(Value::new(1)),
            NativeInputValue::FreshSlot(0),
            NativeInputValue::FreshSlot(1),
        ],
    )])?;
    let (retained_identity, retained_payload, high_identity, sym_input, trans_first) =
        if old_identity < 100 {
            (old_identity, old_payload, 100, old_payload, 101)
        } else {
            (100, 101, old_identity, 101, old_payload)
        };
    let unit = fixture.backend.base_values().get(());
    let transcript = CollisionTranscript {
        view: fixture.backend.lookup_row(fixture.view, &[Value::new(1)]),
        sym: fixture
            .backend
            .lookup_row(fixture.sym, &[Value::new(sym_input), Value::new(102)]),
        trans: fixture.backend.lookup_row(
            fixture.trans,
            &[Value::new(trans_first), Value::new(102), Value::new(103)],
        ),
        uf: fixture
            .backend
            .lookup_row(fixture.uf, &[Value::new(high_identity)]),
        next_id: fixture.backend.fresh_id(),
    };
    assert_eq!(
        transcript.view,
        Some(vec![
            Value::new(1),
            Value::new(retained_identity),
            Value::new(retained_payload),
        ])
    );
    assert_eq!(
        transcript.sym,
        Some(vec![Value::new(sym_input), Value::new(102), unit])
    );
    assert_eq!(
        transcript.trans,
        Some(vec![
            Value::new(trans_first),
            Value::new(102),
            Value::new(103),
            unit,
        ])
    );
    assert_eq!(
        transcript.uf,
        Some(vec![
            Value::new(high_identity),
            Value::new(retained_identity),
            Value::new(103),
        ])
    );
    assert_eq!(transcript.next_id, Value::new(104));
    Ok(transcript)
}

#[test]
fn ordered_union_input_matches_reference_old_and_new_minima() -> Result<()> {
    for (old_identity, old_payload) in [(50, 60), (200, 201)] {
        let reference = collision_transcript(
            Fixture::new(egglog_bridge::EGraph::default(), "reference-opaque")?,
            old_identity,
            old_payload,
        )?;
        let duckdb = collision_transcript(
            Fixture::new(EGraph::new()?, "duckdb-renamed")?,
            old_identity,
            old_payload,
        )?;
        assert_eq!(duckdb, reference);
    }
    Ok(())
}

#[test]
fn ordered_union_identity_equal_input_matches_reference_and_is_physical_noop() -> Result<()> {
    let reference = identity_transcript(Fixture::new(
        egglog_bridge::EGraph::default(),
        "reference-identity",
    )?)?;

    let mut duckdb = Fixture::new(EGraph::new()?, "duckdb-identity")?;
    duckdb.advance_fresh_to_100();
    duckdb.backend.add_values(vec![(
        duckdb.view,
        vec![Value::new(1), Value::new(100), Value::new(90)],
    )])?;
    let generation = duckdb.backend.storage.generation()?;
    duckdb.backend.add_values_with_fresh(vec![(
        duckdb.view,
        vec![
            NativeInputValue::Existing(Value::new(1)),
            NativeInputValue::FreshSlot(0),
            NativeInputValue::FreshSlot(1),
        ],
    )])?;
    let duckdb_transcript = IdentityTranscript {
        view: duckdb.backend.lookup_row(duckdb.view, &[Value::new(1)]),
        sym_rows: duckdb.backend.table_size(duckdb.sym),
        trans_rows: duckdb.backend.table_size(duckdb.trans),
        uf_rows: duckdb.backend.table_size(duckdb.uf),
        next_id: duckdb.backend.fresh_id(),
    };

    assert_eq!(duckdb_transcript, reference);
    assert_eq!(
        duckdb_transcript,
        IdentityTranscript {
            view: Some(vec![Value::new(1), Value::new(100), Value::new(90)]),
            sym_rows: 0,
            trans_rows: 0,
            uf_rows: 0,
            next_id: Value::new(102),
        }
    );
    assert_eq!(duckdb.backend.storage.generation()?, generation);
    assert_eq!(duckdb.backend.last_input_rows(), 1);
    assert_eq!(duckdb.backend.last_input_target_statements(), 1);
    assert_eq!(duckdb.backend.last_input_inserted_rows(), 0);
    assert!(!duckdb.backend.flush_updates());
    Ok(())
}

#[test]
fn native_input_rejects_table_registration_merge_aba_before_transaction() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "native input merge ABA")?;
    let stale = fixture.primitives.proof_min;
    fixture.backend.free_external_func(stale);
    let replacement = fixture
        .backend
        .register_native_primitive(NativePrimitive::SelectMinPayload);
    assert_eq!(replacement, stale, "the canary requires same-id reuse");
    let generation = fixture.backend.storage.generation()?;
    let fresh = fixture.backend.storage.next_fresh_id()?;
    let trace = fixture.backend.storage.latest_input_sql();

    let error = fixture
        .backend
        .add_values(vec![(
            fixture.view,
            vec![Value::new(1), Value::new(2), Value::new(3)],
        )])
        .unwrap_err();
    assert!(
        format!("{error:#}").contains("registration authority"),
        "{error:#}"
    );
    assert_eq!(fixture.backend.storage.generation()?, generation);
    assert_eq!(fixture.backend.storage.next_fresh_id()?, fresh);
    assert_eq!(fixture.backend.storage.latest_input_sql(), trace);
    assert_eq!(fixture.backend.last_input_rows(), 0);
    assert_eq!(fixture.backend.table_size(fixture.view), 0);
    Ok(())
}

#[test]
fn frontend_shaped_heterogeneous_input_preserves_global_ordinals_and_telemetry() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "heterogeneous-opaque")?;
    let first = fixture.backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::Old,
        name: "first-direct-target".into(),
        can_subsume: false,
    });
    let second = fixture.backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::Old,
        name: "second-direct-target".into(),
        can_subsume: false,
    });

    fixture.backend.add_values_with_fresh(vec![
        (
            first,
            vec![
                NativeInputValue::Existing(Value::new(10)),
                NativeInputValue::Existing(Value::new(11)),
            ],
        ),
        (
            fixture.view,
            vec![
                NativeInputValue::Existing(Value::new(1)),
                NativeInputValue::FreshSlot(0),
                NativeInputValue::FreshSlot(1),
            ],
        ),
        (
            second,
            vec![
                NativeInputValue::Existing(Value::new(20)),
                NativeInputValue::Existing(Value::new(21)),
            ],
        ),
        (
            fixture.view,
            vec![
                NativeInputValue::Existing(Value::new(1)),
                NativeInputValue::FreshSlot(2),
                NativeInputValue::FreshSlot(3),
            ],
        ),
    ])?;

    assert_eq!(
        fixture.backend.lookup_row(fixture.view, &[Value::new(1)]),
        Some(vec![Value::new(1), Value::new(0), Value::new(1)])
    );
    assert_eq!(
        fixture.backend.lookup_row(fixture.uf, &[Value::new(2)]),
        Some(vec![Value::new(2), Value::new(0), Value::new(5)])
    );
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 6);
    assert_eq!(fixture.backend.last_input_rows(), 4);
    assert_eq!(fixture.backend.last_input_target_statements(), 3);
    assert_eq!(fixture.backend.last_input_inserted_rows(), 3);
    assert!(!fixture.backend.flush_updates());

    let sql = fixture.backend.storage.latest_input_sql().join("\n");
    assert!(
        sql.contains("CAST('0' AS UBIGINT), CAST('2' AS UBIGINT)")
            && sql.contains("CAST('0' AS UBIGINT), CAST('4' AS UBIGINT)"),
        "ordered rows must retain caller-global ordinals 2 and 4: {sql}"
    );
    assert!(!sql.contains('?'));
    assert!(!sql.contains("heterogeneous-opaque"));
    Ok(())
}

#[test]
fn cross_target_then_self_target_queues_reach_the_unbounded_fixed_point() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "multiwave-opaque")?;
    fixture.advance_fresh_to_100();
    fixture.backend.add_values(vec![
        (
            fixture.view,
            vec![Value::new(1), Value::new(10), Value::new(11)],
        ),
        (
            fixture.uf,
            vec![Value::new(20), Value::new(15), Value::new(30)],
        ),
        (
            fixture.uf,
            vec![Value::new(15), Value::new(12), Value::new(31)],
        ),
        (
            fixture.uf,
            vec![Value::new(12), Value::new(5), Value::new(32)],
        ),
    ])?;
    let generation = fixture.backend.storage.generation()?;

    fixture.backend.add_values(vec![(
        fixture.view,
        vec![Value::new(1), Value::new(20), Value::new(21)],
    )])?;

    assert_eq!(fixture.backend.storage.next_fresh_id()?, 108);
    assert_eq!(fixture.backend.storage.generation()?, generation + 1);
    assert_eq!(
        fixture.backend.lookup_row(fixture.view, &[Value::new(1)]),
        Some(vec![Value::new(1), Value::new(10), Value::new(11)])
    );
    assert_eq!(
        fixture.backend.lookup_row(fixture.uf, &[Value::new(20)]),
        Some(vec![Value::new(20), Value::new(10), Value::new(101)])
    );
    assert_eq!(
        fixture.backend.lookup_row(fixture.uf, &[Value::new(15)]),
        Some(vec![Value::new(15), Value::new(10), Value::new(103)])
    );
    assert_eq!(
        fixture.backend.lookup_row(fixture.uf, &[Value::new(12)]),
        Some(vec![Value::new(12), Value::new(5), Value::new(32)])
    );
    assert_eq!(
        fixture.backend.lookup_row(fixture.uf, &[Value::new(10)]),
        Some(vec![Value::new(10), Value::new(5), Value::new(107)])
    );
    assert_eq!(fixture.backend.table_size(fixture.sym), 4);
    assert_eq!(fixture.backend.table_size(fixture.trans), 4);
    assert_eq!(fixture.backend.last_input_rows(), 1);
    assert_eq!(fixture.backend.last_input_inserted_rows(), 0);
    let scratch = fixture.backend.storage.with_connection(|connection| {
        connection
            .query_row(
                "SELECT count(*) FROM duckdb_tables() WHERE table_name LIKE 'egglog_input_%'",
                [],
                |row| row.get::<_, u64>(0),
            )
            .map_err(Into::into)
    })?;
    assert_eq!(scratch, 0);
    Ok(())
}

#[test]
fn subsumed_view_collisions_preserve_owner_and_corrupt_owners_fail_before_mutation() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "subsumed-opaque")?;
    fixture.advance_fresh_to_100();
    fixture.backend.add_values(vec![(
        fixture.view,
        vec![Value::new(1), Value::new(50), Value::new(51)],
    )])?;
    fixture.backend.storage.with_connection(|connection| {
        connection.execute(
            &format!(
                "UPDATE {} SET __subsumed = TRUE WHERE c0 = CAST('1' AS UBIGINT)",
                sql_table(fixture.view)
            ),
            [],
        )?;
        Ok(())
    })?;

    fixture.backend.add_values(vec![
        (
            fixture.view,
            vec![Value::new(1), Value::new(200), Value::new(201)],
        ),
        (
            fixture.view,
            vec![Value::new(1), Value::new(150), Value::new(151)],
        ),
    ])?;
    let view = fixture
        .backend
        .storage
        .scan(fixture.backend.base_values(), fixture.view)?;
    assert_eq!(view.len(), 1);
    assert_eq!(
        view[0].values,
        vec![Value::new(1), Value::new(50), Value::new(51)]
    );
    assert!(view[0].subsumed);
    assert_eq!(fixture.backend.last_input_rows(), 2);
    assert_eq!(fixture.backend.last_input_inserted_rows(), 0);
    assert_eq!(fixture.backend.table_size(fixture.sym), 2);
    assert_eq!(fixture.backend.table_size(fixture.trans), 2);

    let generation = fixture.backend.storage.generation()?;
    let fresh = fixture.backend.storage.next_fresh_id()?;
    fixture.backend.storage.with_connection(|connection| {
        connection.execute(
            &format!(
                "INSERT INTO {} VALUES (CAST('1' AS UBIGINT), CAST('40' AS UBIGINT), CAST('41' AS UBIGINT), CAST('1' AS UBIGINT), FALSE)",
                sql_table(fixture.view)
            ),
            [],
        )?;
        Ok(())
    })?;
    let duplicate = fixture
        .backend
        .add_values(vec![(
            fixture.view,
            vec![Value::new(1), Value::new(25), Value::new(26)],
        )])
        .unwrap_err();
    assert!(duplicate.to_string().contains("duplicate owners"));
    assert_eq!(fixture.backend.storage.generation()?, generation);
    assert_eq!(fixture.backend.storage.next_fresh_id()?, fresh);
    assert_eq!(fixture.backend.last_input_rows(), 0);

    fixture.backend.storage.with_connection(|connection| {
        connection.execute(
            &format!(
                "DELETE FROM {} WHERE c0 = CAST('1' AS UBIGINT) AND c1 = CAST('40' AS UBIGINT)",
                sql_table(fixture.view)
            ),
            [],
        )?;
        connection.execute(
            &format!("UPDATE {} SET __subsumed = TRUE", sql_table(fixture.uf)),
            [],
        )?;
        Ok(())
    })?;
    fixture.backend.add_values(vec![(
        fixture.view,
        vec![Value::new(2), Value::new(70), Value::new(71)],
    )])?;
    assert_eq!(
        fixture.backend.lookup_row(fixture.view, &[Value::new(2)]),
        Some(vec![Value::new(2), Value::new(70), Value::new(71)])
    );
    let subsumed_owners = fixture.backend.storage.with_connection(|connection| {
        Ok(connection.query_row(
            &format!(
                "SELECT count(*) FROM {} WHERE __subsumed",
                sql_table(fixture.uf)
            ),
            [],
            |row| row.get::<_, u64>(0),
        )?)
    })?;
    assert_eq!(subsumed_owners, 2);
    assert_eq!(fixture.backend.storage.generation()?, generation + 1);
    assert_eq!(fixture.backend.storage.next_fresh_id()?, fresh);
    Ok(())
}

#[test]
fn late_generated_assert_eq_failure_rolls_back_everything_and_retry_reuses_ids() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "rollback-opaque")?;
    fixture.advance_fresh_to_100();
    fixture.backend.add_values(vec![(
        fixture.view,
        vec![Value::new(1), Value::new(50), Value::new(60)],
    )])?;
    let rule_source = fixture.backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::Old,
        name: "rollback-rule-source".into(),
        can_subsume: false,
    });
    let rule_target = fixture.backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::Old,
        name: "rollback-rule-target".into(),
        can_subsume: false,
    });
    fixture.backend.add_values(vec![(
        rule_source,
        vec![Value::new(70), Value::new(71), Value::new(72)],
    )])?;
    let rule = fixture
        .backend
        .add_rule(direct_set_rule(rule_source, rule_target, false))?;
    fixture.backend.run_rules(RuleSetRun {
        name: Some("rollback-rule-telemetry"),
        rules: &[rule],
    })?;
    let rule_watermark = fixture.backend.rules[rule.rep() as usize]
        .as_ref()
        .unwrap()
        .watermark;
    let rule_statement_count = fixture.backend.last_rule_statement_count();
    let rule_match_counts = fixture.backend.last_rule_match_counts().to_vec();
    let rule_insert_counts = fixture.backend.last_rule_insert_counts().to_vec();
    let committed_rule_trace = fixture.backend.storage.latest_rule_sql();
    let generation = fixture.backend.storage.generation()?;
    let committed_trace = fixture.backend.storage.latest_input_sql();
    fixture.backend.storage.with_connection(|connection| {
        connection.execute(
            &format!(
                "INSERT INTO {} VALUES (CAST('60' AS UBIGINT), CAST('102' AS UBIGINT), FALSE, CAST('1' AS UBIGINT), FALSE)",
                sql_table(fixture.sym)
            ),
            [],
        )?;
        Ok(())
    })?;

    let view = fixture.view;
    let direct_target = rule_target;
    let candidate = || {
        vec![
            (
                direct_target,
                vec![
                    NativeInputValue::Existing(Value::new(80)),
                    NativeInputValue::Existing(Value::new(81)),
                    NativeInputValue::Existing(Value::new(82)),
                ],
            ),
            (
                view,
                vec![
                    NativeInputValue::Existing(Value::new(1)),
                    NativeInputValue::FreshSlot(0),
                    NativeInputValue::FreshSlot(1),
                ],
            ),
        ]
    };
    let error = fixture
        .backend
        .add_values_with_fresh(candidate())
        .unwrap_err();
    assert!(error.to_string().contains("AssertEq"));
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 100);
    assert_eq!(fixture.backend.storage.generation()?, generation);
    assert_eq!(
        fixture.backend.lookup_row(fixture.view, &[Value::new(1)]),
        Some(vec![Value::new(1), Value::new(50), Value::new(60)])
    );
    assert_eq!(fixture.backend.table_size(fixture.uf), 0);
    assert_eq!(fixture.backend.table_size(fixture.trans), 0);
    assert_eq!(
        fixture
            .backend
            .lookup_row(direct_target, &[Value::new(80), Value::new(81)]),
        None
    );
    assert_eq!(fixture.backend.last_input_rows(), 0);
    assert_eq!(fixture.backend.last_input_inserted_rows(), 0);
    assert_eq!(fixture.backend.last_input_target_statements(), 0);
    assert_eq!(fixture.backend.storage.latest_input_sql(), committed_trace);
    assert_eq!(
        fixture.backend.rules[rule.rep() as usize]
            .as_ref()
            .unwrap()
            .watermark,
        rule_watermark
    );
    assert_eq!(
        fixture.backend.last_rule_statement_count(),
        rule_statement_count
    );
    assert_eq!(fixture.backend.last_rule_match_counts(), rule_match_counts);
    assert_eq!(
        fixture.backend.last_rule_insert_counts(),
        rule_insert_counts
    );
    assert_eq!(
        fixture.backend.storage.latest_rule_sql(),
        committed_rule_trace
    );
    let scratch = fixture.backend.storage.with_connection(|connection| {
        connection
            .query_row(
                "SELECT count(*) FROM duckdb_tables() WHERE table_name LIKE 'egglog_input_%'",
                [],
                |row| row.get::<_, u64>(0),
            )
            .map_err(Into::into)
    })?;
    assert_eq!(scratch, 0);

    fixture.backend.storage.with_connection(|connection| {
        connection.execute(&format!("DELETE FROM {}", sql_table(fixture.sym)), [])?;
        Ok(())
    })?;
    fixture.backend.add_values_with_fresh(candidate())?;
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 104);
    assert_eq!(
        fixture
            .backend
            .lookup_row(fixture.sym, &[Value::new(60), Value::new(102)]),
        Some(vec![
            Value::new(60),
            Value::new(102),
            fixture.backend.base_values().get(()),
        ])
    );
    assert_eq!(
        fixture.backend.lookup_row(fixture.uf, &[Value::new(100)]),
        Some(vec![Value::new(100), Value::new(50), Value::new(103)])
    );
    assert_eq!(
        fixture
            .backend
            .lookup_row(direct_target, &[Value::new(80), Value::new(81)]),
        Some(vec![Value::new(80), Value::new(81), Value::new(82)])
    );
    assert_eq!(fixture.backend.last_input_rows(), 2);
    assert_eq!(fixture.backend.last_input_target_statements(), 2);
    assert_eq!(fixture.backend.last_input_inserted_rows(), 1);

    fixture.backend.add_values(vec![(
        fixture.view,
        vec![Value::new(2), Value::new(10), Value::new(11)],
    )])?;
    fixture
        .backend
        .storage
        .set_next_fresh_id(u32::MAX as u64 - 1)?;
    let capacity_generation = fixture.backend.storage.generation()?;
    let capacity_trace = fixture.backend.storage.latest_input_sql();
    let capacity_error = fixture
        .backend
        .add_values(vec![(
            fixture.view,
            vec![Value::new(2), Value::new(20), Value::new(21)],
        )])
        .unwrap_err();
    assert!(capacity_error.to_string().contains("usable Value domain"));
    assert_eq!(
        fixture.backend.storage.next_fresh_id()?,
        u32::MAX as u64 - 1
    );
    assert_eq!(fixture.backend.storage.generation()?, capacity_generation);
    assert_eq!(fixture.backend.storage.latest_input_sql(), capacity_trace);
    assert_eq!(
        fixture.backend.lookup_row(fixture.view, &[Value::new(2)]),
        Some(vec![Value::new(2), Value::new(10), Value::new(11)])
    );
    assert_eq!(fixture.backend.last_input_rows(), 0);
    Ok(())
}

type RuleTerm = GenericAtomTerm<RuleVar, RuleValue>;

fn rule_var(id: u32, name: &str) -> RuleTerm {
    GenericAtomTerm::Var(
        Span::Panic,
        RuleVar {
            id,
            name: name.into(),
            ty: ColumnTy::Id,
        },
    )
}

fn direct_set_rule(
    source: FunctionId,
    target: FunctionId,
    target_has_two_values: bool,
) -> RuleSpec {
    let key = rule_var(0, "opaque-key");
    let identity = rule_var(1, "opaque-identity");
    let payload = rule_var(2, "opaque-payload");
    let (keys, values) = if target_has_two_values {
        (vec![key.clone()], vec![identity.clone(), payload.clone()])
    } else {
        (vec![key.clone(), identity.clone()], vec![payload.clone()])
    };
    RuleSpec {
        name: "ordinary-direct-set-canary".into(),
        seminaive: true,
        no_decomp: false,
        core: GenericCoreRule {
            span: Span::Panic,
            body: Query {
                atoms: vec![GenericAtom {
                    span: Span::Panic,
                    head: RuleBodyCall::Table {
                        id: source,
                        read: ReadMode::Live,
                    },
                    args: vec![key, identity, payload],
                }],
            },
            head: GenericCoreActions::new(vec![GenericCoreAction::Set(
                Span::Panic,
                RuleActionCall::Table {
                    id: target,
                    name: "diagnostic-only-name".into(),
                },
                keys,
                values,
            )]),
        },
    }
}

fn add_view_with_keys(
    fixture: &mut Fixture<EGraph>,
    name: &str,
    mut key_schema: Vec<ColumnTy>,
) -> FunctionId {
    key_schema.extend([ColumnTy::Id, ColumnTy::Id]);
    fixture.backend.add_table(FunctionConfig {
        schema: key_schema,
        n_vals: 2,
        n_identity_vals: Some(1),
        default: DefaultVal::Fail,
        merge: ordered_union(
            fixture.primitives,
            fixture.label,
            fixture.string,
            fixture.unit,
            fixture.backend.base_values().get(()),
            fixture.sym,
            fixture.trans,
            fixture.uf,
            true,
        ),
        name: name.into(),
        can_subsume: true,
    })
}

fn fixture_ordered_union(
    fixture: &Fixture<EGraph>,
    displaced: FunctionId,
    eclass_to_term: bool,
) -> MergeFn {
    ordered_union(
        fixture.primitives,
        fixture.label,
        fixture.string,
        fixture.unit,
        fixture.backend.base_values().get(()),
        fixture.sym,
        fixture.trans,
        displaced,
        eclass_to_term,
    )
}

fn add_three_id_view(fixture: &mut Fixture<EGraph>, name: &str, merge: MergeFn) -> FunctionId {
    fixture.backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        n_vals: 2,
        n_identity_vals: Some(1),
        default: DefaultVal::Fail,
        merge,
        name: name.into(),
        can_subsume: true,
    })
}

enum NativeInputOutcome<'a> {
    Accept,
    Reject(&'a str),
}

fn assert_input_outcome(
    fixture: &mut Fixture<EGraph>,
    target: FunctionId,
    outcome: NativeInputOutcome<'_>,
) -> Result<()> {
    let generation = fixture.backend.storage.generation()?;
    let fresh = fixture.backend.storage.next_fresh_id()?;
    let trace = fixture.backend.storage.latest_input_sql();
    let sym_rows = fixture.backend.table_size(fixture.sym);
    let trans_rows = fixture.backend.table_size(fixture.trans);
    let uf_rows = fixture.backend.table_size(fixture.uf);
    let result = fixture.backend.add_values(vec![(
        target,
        vec![Value::new(1), Value::new(2), Value::new(3)],
    )]);
    match outcome {
        NativeInputOutcome::Accept => {
            result?;
            assert_eq!(fixture.backend.table_size(target), 1);
            assert_eq!(fixture.backend.storage.generation()?, generation + 1);
            assert_eq!(fixture.backend.last_input_rows(), 1);
        }
        NativeInputOutcome::Reject(diagnostic) => {
            let error = result.unwrap_err();
            assert!(
                format!("{error:#}").contains(diagnostic),
                "expected `{diagnostic}` rejection, got: {error:#}"
            );
            assert_eq!(fixture.backend.table_size(target), 0);
            assert_eq!(fixture.backend.table_size(fixture.sym), sym_rows);
            assert_eq!(fixture.backend.table_size(fixture.trans), trans_rows);
            assert_eq!(fixture.backend.table_size(fixture.uf), uf_rows);
            assert_eq!(fixture.backend.storage.generation()?, generation);
            assert_eq!(fixture.backend.storage.next_fresh_id()?, fresh);
            assert_eq!(fixture.backend.storage.latest_input_sql(), trace);
            assert_eq!(fixture.backend.last_input_rows(), 0);
            assert_eq!(fixture.backend.last_input_inserted_rows(), 0);
            assert_eq!(fixture.backend.last_input_target_statements(), 0);
        }
    }
    Ok(())
}

#[test]
fn native_input_admission_is_exact_and_supported_deferred_set_is_scalar() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "admission-opaque")?;
    let original_generation = fixture.backend.storage.generation()?;
    let original_fresh = fixture.backend.storage.next_fresh_id()?;

    let mut near_merge = ordered_union(
        fixture.primitives,
        fixture.label,
        fixture.string,
        fixture.unit,
        fixture.backend.base_values().get(()),
        fixture.sym,
        fixture.trans,
        fixture.uf,
        true,
    );
    let MergeFn::Block { actions, .. } = &mut near_merge else {
        unreachable!()
    };
    actions.pop();
    let near = fixture.backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        n_vals: 2,
        n_identity_vals: Some(1),
        default: DefaultVal::Fail,
        merge: near_merge,
        name: "ordered-near-shape".into(),
        can_subsume: true,
    });
    fixture.backend.add_values(vec![(
        near,
        vec![Value::new(1), Value::new(2), Value::new(3)],
    )])?;
    assert_eq!(fixture.backend.table_size(near), 1);

    let mut fake_primitive = ordered_union(
        fixture.primitives,
        fixture.label,
        fixture.string,
        fixture.unit,
        fixture.backend.base_values().get(()),
        fixture.sym,
        fixture.trans,
        fixture.uf,
        true,
    );
    let MergeFn::Block { actions, .. } = &mut fake_primitive else {
        unreachable!()
    };
    let MergeAction::Let { value, .. } = &mut actions[0] else {
        unreachable!()
    };
    let hostile = fixture
        .backend
        .new_panic("ordinary callback must not authenticate native input".into());
    let MergeFn::Primitive { id, name, .. } = value else {
        unreachable!()
    };
    *id = hostile;
    *name = "proof-of-max".into();
    let malformed = fixture.backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        n_vals: 2,
        n_identity_vals: Some(1),
        default: DefaultVal::Fail,
        merge: fake_primitive,
        name: "ordered-fake-primitive".into(),
        can_subsume: true,
    });
    let malformed_error = fixture
        .backend
        .add_values(vec![(
            malformed,
            vec![Value::new(1), Value::new(2), Value::new(3)],
        )])
        .unwrap_err();
    assert!(
        format!("{malformed_error:#}").contains("unauthenticated merge token"),
        "unexpected unauthenticated primitive error: {malformed_error:#}"
    );

    let unknown = fixture
        .backend
        .add_values(vec![(
            FunctionId::new(99_999),
            vec![Value::new(1), Value::new(2), Value::new(3)],
        )])
        .unwrap_err();
    assert!(unknown.to_string().contains("unregistered"));
    assert!(
        fixture
            .backend
            .add_values(vec![(fixture.view, vec![Value::new(1), Value::new(2)])])
            .unwrap_err()
            .to_string()
            .contains("expects 3 columns")
    );
    assert!(
        fixture
            .backend
            .add_values(vec![(
                fixture.view,
                vec![Value::new(1), Value::new(2), Value::new(u32::MAX)],
            )])
            .unwrap_err()
            .to_string()
            .contains("stale Value sentinel")
    );
    assert!(
        fixture
            .backend
            .add_values_with_fresh(vec![(
                fixture.view,
                vec![
                    NativeInputValue::Existing(Value::new(1)),
                    NativeInputValue::FreshSlot(1),
                    NativeInputValue::Existing(Value::new(3)),
                ],
            )])
            .unwrap_err()
            .to_string()
            .contains("dense")
    );
    assert_eq!(
        fixture.backend.storage.generation()?,
        original_generation + 1
    );
    assert_eq!(fixture.backend.storage.next_fresh_id()?, original_fresh);
    assert_eq!(fixture.backend.last_input_rows(), 0);

    let source = fixture.backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::Old,
        name: "direct-source".into(),
        can_subsume: false,
    });
    let deferred_rule = fixture
        .backend
        .add_rule(direct_set_rule(source, fixture.view, true))?;
    assert_eq!(
        fixture
            .backend
            .storage
            .table_info(fixture.view)?
            .write_capability,
        WriteCapability::Deferred
    );
    assert!(
        fixture.backend.rules[deferred_rule.rep() as usize]
            .as_ref()
            .expect("deferred rule remains registered")
            .plan
            .scalar_action()
            .is_some(),
        "authenticated deferred ordered-union Set must use ScalarAction"
    );
    let sink = fixture.backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::Old,
        name: "direct-sink".into(),
        can_subsume: false,
    });
    let first_rule = fixture
        .backend
        .add_rule(direct_set_rule(source, sink, false))?;
    assert_eq!(
        first_rule.rep(),
        1,
        "supported deferred ScalarAction should consume exactly one RuleId"
    );

    let minted_not_stored = fixture.backend.fresh_id();
    fixture.backend.add_values(vec![(
        fixture.view,
        vec![minted_not_stored, Value::new(70), Value::new(71)],
    )])?;
    assert_eq!(
        fixture
            .backend
            .lookup_row(fixture.view, &[minted_not_stored]),
        Some(vec![minted_not_stored, Value::new(70), Value::new(71)])
    );
    Ok(())
}

#[test]
fn custom_seven_action_view_with_plain_displaced_target_is_generic() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "ownership-witness")?;
    let plain_assert_eq = fixture.backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::AssertEq,
        name: "plain-displaced-target".into(),
        can_subsume: false,
    });
    let merge = fixture_ordered_union(&fixture, plain_assert_eq, true);
    let custom_view = add_three_id_view(&mut fixture, "custom-seven-action-view", merge);
    assert_input_outcome(&mut fixture, custom_view, NativeInputOutcome::Accept)
}

#[test]
fn owned_graph_admission_mutation_matrix_fails_closed() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "owned-mutation-matrix")?;

    let alternate_label = fixture
        .backend
        .base_values()
        .get(Boxed::new("alternate-fresh-domain".to_string()));
    let mismatched_uf_id = fixture.backend.peek_next_function_id();
    let mismatched_uf = fixture.backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        n_vals: 2,
        n_identity_vals: Some(1),
        default: DefaultVal::Fail,
        merge: ordered_union(
            fixture.primitives,
            alternate_label,
            fixture.string,
            fixture.unit,
            fixture.backend.base_values().get(()),
            fixture.sym,
            fixture.trans,
            mismatched_uf_id,
            false,
        ),
        name: "fresh-label-mismatch-uf".into(),
        can_subsume: false,
    });
    let merge = fixture_ordered_union(&fixture, mismatched_uf, true);
    let label_mismatch = add_three_id_view(&mut fixture, "fresh-label-mismatch-view", merge);
    assert_input_outcome(&mut fixture, label_mismatch, NativeInputOutcome::Accept)?;

    let nonself_uf_id = fixture.backend.peek_next_function_id();
    let nonself_uf = fixture.backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        n_vals: 2,
        n_identity_vals: Some(1),
        default: DefaultVal::Fail,
        merge: fixture_ordered_union(&fixture, fixture.uf, false),
        name: format!("nonself-uf-{}", nonself_uf_id.rep()),
        can_subsume: false,
    });
    let merge = fixture_ordered_union(&fixture, nonself_uf, true);
    let nonself_view = add_three_id_view(&mut fixture, "nonself-displaced-view", merge);
    assert_input_outcome(&mut fixture, nonself_view, NativeInputOutcome::Accept)?;

    let wrong_orientation_id = fixture.backend.peek_next_function_id();
    let wrong_orientation = fixture.backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        n_vals: 2,
        n_identity_vals: Some(1),
        default: DefaultVal::Fail,
        merge: ordered_union(
            fixture.primitives,
            fixture.label,
            fixture.string,
            fixture.unit,
            fixture.backend.base_values().get(()),
            fixture.sym,
            fixture.trans,
            wrong_orientation_id,
            true,
        ),
        name: "wrong-orientation-uf".into(),
        can_subsume: false,
    });
    let merge = fixture_ordered_union(&fixture, wrong_orientation, true);
    let wrong_orientation_view = add_three_id_view(&mut fixture, "wrong-orientation-view", merge);
    assert_input_outcome(
        &mut fixture,
        wrong_orientation_view,
        NativeInputOutcome::Accept,
    )?;

    let wrong_config_id = fixture.backend.peek_next_function_id();
    let wrong_config = fixture.backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        n_vals: 2,
        n_identity_vals: Some(1),
        default: DefaultVal::Fail,
        merge: fixture_ordered_union(&fixture, wrong_config_id, false),
        name: "subsumable-displaced-uf".into(),
        can_subsume: true,
    });
    let merge = fixture_ordered_union(&fixture, wrong_config, true);
    let wrong_config_view = add_three_id_view(&mut fixture, "wrong-config-view", merge);
    assert_input_outcome(&mut fixture, wrong_config_view, NativeInputOutcome::Accept)?;

    let mut wrong_slot_merge = fixture_ordered_union(&fixture, fixture.uf, true);
    let MergeFn::Block { actions, .. } = &mut wrong_slot_merge else {
        unreachable!()
    };
    let MergeAction::Set(_, arguments) = &mut actions[3] else {
        unreachable!()
    };
    arguments[0] = MergeFn::LetVar(0);
    let wrong_slot = add_three_id_view(&mut fixture, "wrong-let-slot-view", wrong_slot_merge);
    assert_input_outcome(&mut fixture, wrong_slot, NativeInputOutcome::Accept)?;

    let bad_proof = fixture.backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Base(fixture.unit)],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::Old,
        name: "non-assert-proof-target".into(),
        can_subsume: false,
    });
    let mut bad_proof_merge = fixture_ordered_union(&fixture, fixture.uf, true);
    let MergeFn::Block { actions, .. } = &mut bad_proof_merge else {
        unreachable!()
    };
    let MergeAction::Set(target, _) = &mut actions[3] else {
        unreachable!()
    };
    *target = bad_proof;
    let bad_proof_view = add_three_id_view(&mut fixture, "bad-proof-target-view", bad_proof_merge);
    assert_input_outcome(&mut fixture, bad_proof_view, NativeInputOutcome::Accept)?;

    let mut bad_result_merge = fixture_ordered_union(&fixture, fixture.uf, true);
    let MergeFn::Block { result, .. } = &mut bad_result_merge else {
        unreachable!()
    };
    let MergeFn::Columns(results) = result.as_mut() else {
        unreachable!()
    };
    results[1] = MergeFn::LetVar(0);
    let bad_result = add_three_id_view(&mut fixture, "bad-result-tuple-view", bad_result_merge);
    assert_input_outcome(&mut fixture, bad_result, NativeInputOutcome::Accept)?;

    let mut swapped_tag_merge = fixture_ordered_union(&fixture, fixture.uf, true);
    let MergeFn::Block { actions, .. } = &mut swapped_tag_merge else {
        unreachable!()
    };
    let MergeAction::Let { value, .. } = &mut actions[0] else {
        unreachable!()
    };
    let MergeFn::Primitive { id, name, .. } = value else {
        unreachable!()
    };
    *id = fixture.primitives.proof_min;
    *name = "proof-of-max".into();
    let swapped_tag = add_three_id_view(&mut fixture, "swapped-native-tag-view", swapped_tag_merge);
    assert_input_outcome(&mut fixture, swapped_tag, NativeInputOutcome::Accept)?;

    let mut malformed_signature_merge = fixture_ordered_union(&fixture, fixture.uf, true);
    let MergeFn::Block { actions, .. } = &mut malformed_signature_merge else {
        unreachable!()
    };
    let MergeAction::Let { value, .. } = &mut actions[0] else {
        unreachable!()
    };
    let MergeFn::Primitive { output, .. } = value else {
        unreachable!()
    };
    *output = ColumnTy::Base(fixture.unit);
    let malformed_signature = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        add_three_id_view(
            &mut fixture,
            "genuine-tag-malformed-signature-view",
            malformed_signature_merge,
        )
    }))
    .expect_err("mistyped primitive must fail during table registration");
    let malformed_message = malformed_signature
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| malformed_signature.downcast_ref::<&str>().copied())
        .expect("registration panic must carry a string diagnostic");
    assert!(malformed_message.contains("raw SelectMaxPayload requires"));

    let alternate_max = fixture
        .backend
        .register_native_primitive(NativePrimitive::SelectMaxPayload);
    let mut alternate_context_merge = fixture_ordered_union(&fixture, fixture.uf, true);
    let MergeFn::Block { actions, .. } = &mut alternate_context_merge else {
        unreachable!()
    };
    let MergeAction::Let { value, .. } = &mut actions[0] else {
        unreachable!()
    };
    let MergeFn::Primitive { id, .. } = value else {
        unreachable!()
    };
    *id = alternate_max;
    let alternate_context = add_three_id_view(
        &mut fixture,
        "distinct-context-same-tag-view",
        alternate_context_merge,
    );
    fixture.backend.add_values(vec![(
        alternate_context,
        vec![Value::new(9), Value::new(90), Value::new(91)],
    )])?;
    assert_eq!(fixture.backend.table_size(alternate_context), 1);
    assert_eq!(fixture.backend.pending_panic_message(), None);
    fixture.backend.run_rules(RuleSetRun {
        name: Some("placeholder-uninvoked-native-input"),
        rules: &[],
    })?;

    let stale = fixture.primitives.proof_max;
    fixture.backend.free_external_func(stale);
    let reused = fixture.backend.register_external_func(Box::new(
        egglog_core_relations::make_external_func(
            |_state: &mut egglog_backend_trait::ExecutionState<'_>, _args: &[Value]| {
                Some(Value::new(999))
            },
        ),
    ));
    assert_eq!(reused, stale, "freed native ids should be reusable");
    let original_view = fixture.view;
    assert_input_outcome(
        &mut fixture,
        original_view,
        NativeInputOutcome::Reject("registration authority"),
    )?;

    Ok(())
}

#[test]
fn nullary_and_twenty_seven_hostile_typed_keys_use_closed_inline_values_sql() -> Result<()> {
    let mut fixture = Fixture::new(EGraph::new()?, "typed-hostile-opaque")?;
    let nullary = add_view_with_keys(&mut fixture, "nullary-view", vec![]);
    fixture.backend.add_values(vec![
        (nullary, vec![Value::new(50), Value::new(51)]),
        (nullary, vec![Value::new(60), Value::new(61)]),
    ])?;
    assert_eq!(
        fixture.backend.lookup_row(nullary, &[]),
        Some(vec![Value::new(50), Value::new(51)])
    );
    assert_eq!(fixture.backend.last_input_inserted_rows(), 1);

    let i64_ty = fixture.backend.base_values().get_ty::<i64>();
    let bool_ty = fixture.backend.base_values().get_ty::<bool>();
    let float_ty = fixture
        .backend
        .base_values()
        .get_ty::<Boxed<OrderedFloat<f64>>>();
    let key_schema = (0..27)
        .map(|index| match index % 5 {
            0 => ColumnTy::Id,
            1 => ColumnTy::Base(i64_ty),
            2 => ColumnTy::Base(fixture.string),
            3 => ColumnTy::Base(bool_ty),
            _ => ColumnTy::Base(float_ty),
        })
        .collect::<Vec<_>>();
    let wide = add_view_with_keys(
        &mut fixture,
        "wide-view-with-hostile-name",
        key_schema.clone(),
    );
    let hostile = "'); DROP TABLE egglog_function_0; -- embedded\0雪🦆";
    let keys = key_schema
        .iter()
        .enumerate()
        .map(|(index, ty)| match ty {
            ColumnTy::Id => Value::new(4_000 + u32::try_from(index).unwrap()),
            ColumnTy::Base(base) if *base == i64_ty => fixture
                .backend
                .base_values()
                .get(i64::MIN + i64::try_from(index).unwrap()),
            ColumnTy::Base(base) if *base == fixture.string => fixture
                .backend
                .base_values()
                .get(Boxed::new(format!("{hostile}-{index}"))),
            ColumnTy::Base(base) if *base == bool_ty => {
                fixture.backend.base_values().get(index % 2 == 0)
            }
            ColumnTy::Base(base) if *base == float_ty => fixture
                .backend
                .base_values()
                .get(Boxed::new(OrderedFloat(index as f64 + 0.25))),
            _ => unreachable!(),
        })
        .collect::<Vec<_>>();

    let mut wrong_slot = keys
        .iter()
        .copied()
        .map(NativeInputValue::Existing)
        .collect::<Vec<_>>();
    let string_column = key_schema
        .iter()
        .position(|ty| *ty == ColumnTy::Base(fixture.string))
        .unwrap();
    wrong_slot[string_column] = NativeInputValue::FreshSlot(0);
    wrong_slot.extend([
        NativeInputValue::Existing(Value::new(500)),
        NativeInputValue::Existing(Value::new(501)),
    ]);
    let wrong_type = fixture
        .backend
        .add_values_with_fresh(vec![(wide, wrong_slot)])
        .unwrap_err();
    assert!(wrong_type.to_string().contains("non-id"));
    assert_eq!(fixture.backend.table_size(wide), 0);

    let mut row = keys.clone();
    row.extend([Value::new(500), Value::new(501)]);
    fixture.backend.add_values(vec![(wide, row.clone())])?;
    assert_eq!(fixture.backend.lookup_row(wide, &keys), Some(row));
    assert_eq!(fixture.backend.last_input_rows(), 1);
    assert_eq!(fixture.backend.last_input_inserted_rows(), 1);
    let sql = fixture.backend.storage.latest_input_sql().join("\n");
    assert!(!sql.contains('?'));
    assert!(!sql.contains(hostile));
    assert!(!sql.contains("wide-view-with-hostile-name"));
    assert!(sql.contains("FROM (VALUES"));
    Ok(())
}
