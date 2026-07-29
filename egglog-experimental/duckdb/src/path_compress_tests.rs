use anyhow::Result;
use egglog_ast::{
    core::{
        GenericAtom, GenericAtomTerm, GenericCoreAction, GenericCoreActions, GenericCoreRule, Query,
    },
    span::Span,
};
use egglog_backend_trait::{
    Backend, BaseValueId, ColumnTy, DefaultVal, FunctionConfig, FunctionId, MergeAction, MergeFn,
    NativePrimitive, ReadMode, RuleActionCall, RuleBodyCall, RuleId, RuleSetRun, RuleSpec,
    RuleValue, RuleVar, Value,
};
use egglog_core_relations::Boxed;
use egglog_numeric_id::NumericId;
use ordered_float::OrderedFloat;

use crate::{EGraph, rebuild_tests::NativeTokens, storage::sql_table};

type Term = GenericAtomTerm<RuleVar, RuleValue>;

struct Fixture {
    backend: EGraph,
    unit: BaseValueId,
    string: BaseValueId,
    proof_sort: Value,
    tokens: NativeTokens,
    sym: FunctionId,
    trans: FunctionId,
    uf: FunctionId,
    rule: RuleId,
}

#[derive(Clone, Copy)]
struct Instance {
    sym: FunctionId,
    trans: FunctionId,
    uf: FunctionId,
    rule: RuleId,
}

impl Fixture {
    fn new(prefix: &str) -> Result<Self> {
        let mut backend = EGraph::new()?;
        let unit = backend.base_values_mut().register_type::<()>();
        let string = backend.base_values_mut().register_type::<Boxed<String>>();
        backend.base_values_mut().register_type::<bool>();
        backend.base_values_mut().register_type::<i64>();
        backend
            .base_values_mut()
            .register_type::<Boxed<OrderedFloat<f64>>>();
        let proof_sort = backend
            .base_values()
            .get(Boxed::new(format!("{prefix}-opaque-sort")));
        let tokens = NativeTokens {
            neq: backend.register_native_primitive(NativePrimitive::ValueNeq),
            select_min: backend.register_native_primitive(NativePrimitive::SelectMinPayload),
            select_max: backend.register_native_primitive(NativePrimitive::SelectMaxPayload),
            ordering_min: backend.register_native_primitive(NativePrimitive::OrderingMin),
            ordering_max: backend.register_native_primitive(NativePrimitive::OrderingMax),
            fresh: backend.register_get_fresh(),
        };
        let Instance {
            sym,
            trans,
            uf,
            rule,
        } = add_instance(&mut backend, prefix, unit, string, proof_sort, tokens)?;
        Ok(Self {
            backend,
            unit,
            string,
            proof_sort,
            tokens,
            sym,
            trans,
            uf,
            rule,
        })
    }

    fn seed_uf(&self, rows: &[(u64, u64, u64)]) -> Result<()> {
        self.backend.storage.with_connection(|connection| {
            for &(key, parent, proof) in rows {
                connection.execute(
                    &format!(
                        "INSERT INTO {} VALUES (
                             CAST('{key}' AS UBIGINT), CAST('{parent}' AS UBIGINT),
                             CAST('{proof}' AS UBIGINT), CAST('0' AS UBIGINT), FALSE
                         )",
                        sql_table(self.uf)
                    ),
                    [],
                )?;
            }
            Ok(())
        })
    }

    fn run(&mut self, rules: &[RuleId]) -> Result<bool> {
        Ok(self
            .backend
            .run_rules(RuleSetRun {
                name: Some("renamed-path-canary"),
                rules,
            })?
            .changed())
    }

    fn scratch_count(&self) -> Result<u64> {
        self.backend.storage.with_connection(|connection| {
            connection
                .query_row(
                    "SELECT count(*) FROM duckdb_tables()
                     WHERE table_name LIKE 'egglog_path_%'",
                    [],
                    |row| row.get(0),
                )
                .map_err(Into::into)
        })
    }

    fn rule_spec(&self, prefix: &str) -> RuleSpec {
        path_rule(
            prefix,
            self.unit,
            self.string,
            self.proof_sort,
            self.tokens,
            self.trans,
            self.uf,
        )
    }
}

fn add_instance(
    backend: &mut EGraph,
    prefix: &str,
    unit: BaseValueId,
    string: BaseValueId,
    proof_sort: Value,
    tokens: NativeTokens,
) -> Result<Instance> {
    let unit_value = backend.base_values().get(());
    let sym = backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Base(unit)],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::AssertEq,
        name: format!("{prefix}-binary-evidence"),
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
        name: format!("{prefix}-ternary-evidence"),
        can_subsume: false,
    });
    let predicted = backend.peek_next_function_id();
    let uf = backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        n_vals: 2,
        n_identity_vals: Some(1),
        default: DefaultVal::Fail,
        merge: path_ordered_union(
            tokens, string, unit, proof_sort, unit_value, sym, trans, predicted,
        ),
        name: format!("{prefix}-parent-map"),
        can_subsume: false,
    });
    assert_eq!(uf, predicted);
    let rule = backend.add_rule(path_rule(
        prefix, unit, string, proof_sort, tokens, trans, uf,
    ))?;
    Ok(Instance {
        sym,
        trans,
        uf,
        rule,
    })
}

#[allow(clippy::too_many_arguments)]
fn path_ordered_union(
    tokens: NativeTokens,
    string: BaseValueId,
    unit: BaseValueId,
    proof_sort: Value,
    unit_value: Value,
    sym: FunctionId,
    trans: FunctionId,
    displaced: FunctionId,
) -> MergeFn {
    let fresh = || MergeFn::Primitive {
        id: tokens.fresh,
        name: "renamed-merge-fresh-diagnostic".to_string(),
        input: vec![ColumnTy::Base(string)],
        output: ColumnTy::Id,
        args: vec![MergeFn::Const {
            value: proof_sort,
            ty: ColumnTy::Base(string),
        }],
    };
    let orient = |id, name: &str| MergeFn::Primitive {
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
    let unit_constant = || MergeFn::Const {
        value: unit_value,
        ty: ColumnTy::Base(unit),
    };
    MergeFn::Block {
        actions: vec![
            MergeAction::Let {
                slot: 0,
                value: orient(tokens.select_max, "renamed-select-max-diagnostic"),
            },
            MergeAction::Let {
                slot: 1,
                value: orient(tokens.select_min, "renamed-select-min-diagnostic"),
            },
            MergeAction::Let {
                slot: 2,
                value: fresh(),
            },
            MergeAction::Set(
                sym,
                vec![MergeFn::LetVar(0), MergeFn::LetVar(2), unit_constant()],
            ),
            MergeAction::Let {
                slot: 3,
                value: fresh(),
            },
            MergeAction::Set(
                trans,
                vec![
                    MergeFn::LetVar(2),
                    MergeFn::LetVar(1),
                    MergeFn::LetVar(3),
                    unit_constant(),
                ],
            ),
            MergeAction::Set(
                displaced,
                vec![
                    ordering(tokens.ordering_max, "renamed-ordering-max-diagnostic"),
                    ordering(tokens.ordering_min, "renamed-ordering-min-diagnostic"),
                    MergeFn::LetVar(3),
                ],
            ),
        ],
        result: Box::new(MergeFn::Columns(vec![
            ordering(tokens.ordering_min, "another-ordering-min-diagnostic"),
            MergeFn::LetVar(1),
        ])),
    }
}

pub(crate) fn path_rule(
    prefix: &str,
    unit: BaseValueId,
    string: BaseValueId,
    proof_sort: Value,
    tokens: NativeTokens,
    trans: FunctionId,
    uf: FunctionId,
) -> RuleSpec {
    let a = var(0, "left", ColumnTy::Id);
    let b = var(1, "middle", ColumnTy::Id);
    let pb = var(2, "left-proof", ColumnTy::Id);
    let c = var(3, "right", ColumnTy::Id);
    let pc = var(4, "right-proof", ColumnTy::Id);
    let neq_result = var(5, "unused-unit", ColumnTy::Base(unit));
    let fresh_binding = RuleVar {
        id: 6,
        name: "opaque-fresh-result".into(),
        ty: ColumnTy::Id,
    };
    let alias = RuleVar {
        id: 7,
        name: "opaque-alias".into(),
        ty: ColumnTy::Id,
    };
    RuleSpec {
        name: format!("{prefix}-completely-renamed-rule"),
        seminaive: true,
        no_decomp: false,
        core: GenericCoreRule {
            span: Span::Panic,
            body: Query {
                atoms: vec![
                    table_atom(uf, vec![a.clone(), b.clone(), pb.clone()]),
                    table_atom(uf, vec![b.clone(), c.clone(), pc.clone()]),
                    GenericAtom {
                        span: Span::Panic,
                        head: RuleBodyCall::Primitive {
                            id: tokens.neq,
                            name: "renamed-neq-diagnostic".into(),
                            output: ColumnTy::Base(unit),
                        },
                        args: vec![b.clone(), c.clone(), neq_result],
                    },
                ],
            },
            head: GenericCoreActions::new(vec![
                GenericCoreAction::Let(
                    Span::Panic,
                    fresh_binding.clone(),
                    RuleActionCall::Primitive {
                        id: tokens.fresh,
                        name: "renamed-head-fresh-diagnostic".into(),
                        output: ColumnTy::Id,
                    },
                    vec![literal(proof_sort, ColumnTy::Base(string))],
                ),
                GenericCoreAction::LetAtomTerm(Span::Panic, alias.clone(), variable(fresh_binding)),
                GenericCoreAction::Set(
                    Span::Panic,
                    RuleActionCall::Table {
                        id: trans,
                        name: "renamed-head-evidence".into(),
                    },
                    vec![pb, pc, variable(alias.clone())],
                    vec![literal(Value::new(0), ColumnTy::Base(unit))],
                ),
                GenericCoreAction::Set(
                    Span::Panic,
                    RuleActionCall::Table {
                        id: uf,
                        name: "renamed-parent-map".into(),
                    },
                    vec![a],
                    vec![c, variable(alias)],
                ),
            ]),
        },
    }
}

fn table_atom(id: FunctionId, args: Vec<Term>) -> GenericAtom<RuleBodyCall, RuleVar, RuleValue> {
    GenericAtom {
        span: Span::Panic,
        head: RuleBodyCall::Table {
            id,
            read: ReadMode::Live,
        },
        args,
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

fn remap_rule_role(rule: &mut RuleSpec, from: u32, to: u32) {
    fn remap_term(term: &mut Term, from: u32, to: u32) {
        if let GenericAtomTerm::Var(_, variable) = term
            && variable.id == from
        {
            variable.id = to;
        }
    }

    for atom in &mut rule.core.body.atoms {
        for argument in &mut atom.args {
            remap_term(argument, from, to);
        }
    }
    for action in &mut rule.core.head.0 {
        match action {
            GenericCoreAction::Let(_, binding, _, arguments) => {
                if binding.id == from {
                    binding.id = to;
                }
                for argument in arguments {
                    remap_term(argument, from, to);
                }
            }
            GenericCoreAction::LetAtomTerm(_, binding, source) => {
                if binding.id == from {
                    binding.id = to;
                }
                remap_term(source, from, to);
            }
            GenericCoreAction::Set(_, _, arguments, values) => {
                for term in arguments.iter_mut().chain(values) {
                    remap_term(term, from, to);
                }
            }
            _ => unreachable!("path-rule test helper received an unrelated action"),
        }
    }
}

fn ids(row: Option<Vec<Value>>) -> Option<Vec<u32>> {
    row.map(|values| values.into_iter().map(Value::rep).collect())
}

#[test]
fn renamed_path_rule_executes_new_min_and_identity_guard_without_host_callbacks() -> Result<()> {
    let mut fixture = Fixture::new("not-proof")?;
    fixture.backend.storage.set_next_fresh_id(100)?;
    fixture.seed_uf(&[(30, 20, 70), (20, 10, 80)])?;

    let rule = fixture.rule;
    assert!(fixture.run(&[rule])?);
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 103);
    assert_eq!(
        ids(fixture.backend.lookup_row(fixture.uf, &[Value::new(30)])),
        Some(vec![30, 10, 100])
    );
    // The generated 20 -> 10 candidate has equal identity but a different
    // payload.  It must retain the old proof and allocate no second Block.
    assert_eq!(
        ids(fixture.backend.lookup_row(fixture.uf, &[Value::new(20)])),
        Some(vec![20, 10, 80])
    );
    assert_eq!(
        ids(fixture.backend.lookup_row(
            fixture.trans,
            &[Value::new(70), Value::new(80), Value::new(100)]
        )),
        Some(vec![70, 80, 100, 0])
    );
    assert_eq!(
        ids(fixture
            .backend
            .lookup_row(fixture.sym, &[Value::new(70), Value::new(101)])),
        Some(vec![70, 101, 0])
    );
    assert_eq!(
        ids(fixture.backend.lookup_row(
            fixture.trans,
            &[Value::new(101), Value::new(100), Value::new(102)]
        )),
        Some(vec![101, 100, 102, 0])
    );
    assert_eq!(fixture.scratch_count()?, 0);
    let sql = fixture.backend.storage.latest_rule_sql();
    assert!(sql.iter().all(|statement| !statement.contains('?')));
    assert!(sql.iter().all(|statement| !statement.contains("not-proof")));
    assert!(
        sql.iter()
            .any(|statement| statement.contains("egglog_path_queue_"))
    );
    assert!(!fixture.run(&[rule])?);
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 103);
    Ok(())
}

#[test]
fn old_min_keeps_owner_generation_but_emits_collision_effects_and_edge() -> Result<()> {
    let mut fixture = Fixture::new("old-min")?;
    fixture.backend.storage.set_next_fresh_id(100)?;
    fixture.seed_uf(&[(10, 20, 70), (20, 30, 80)])?;
    let before = fixture
        .backend
        .storage
        .scan(fixture.backend.base_values(), fixture.uf)?
        .into_iter()
        .find(|row| row.values[0] == Value::new(10))
        .unwrap()
        .generation;

    let rule = fixture.rule;
    assert!(fixture.run(&[rule])?);
    let owner = fixture
        .backend
        .storage
        .scan(fixture.backend.base_values(), fixture.uf)?
        .into_iter()
        .find(|row| row.values[0] == Value::new(10))
        .unwrap();
    assert_eq!(
        owner.values,
        [Value::new(10), Value::new(20), Value::new(70)]
    );
    assert_eq!(owner.generation, before);
    assert_eq!(
        ids(fixture.backend.lookup_row(fixture.uf, &[Value::new(30)])),
        Some(vec![30, 20, 102])
    );
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 103);
    assert_eq!(
        ids(fixture
            .backend
            .lookup_row(fixture.sym, &[Value::new(100), Value::new(101)])),
        Some(vec![100, 101, 0])
    );
    Ok(())
}

#[test]
fn duplicate_same_key_candidates_fold_one_at_a_time_after_all_head_ids() -> Result<()> {
    let mut fixture = Fixture::new("duplicate")?;
    fixture.backend.storage.set_next_fresh_id(100)?;
    fixture.seed_uf(&[(30, 20, 70), (20, 10, 80)])?;
    let rule = fixture.rule;
    let second = fixture
        .backend
        .add_rule(fixture.rule_spec("duplicate-second-rule-id"))?;
    assert!(fixture.run(&[rule, second])?);
    assert_eq!(fixture.backend.last_rule_match_counts(), [1, 1]);
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 104);
    assert_eq!(
        ids(fixture.backend.lookup_row(fixture.uf, &[Value::new(30)])),
        Some(vec![30, 10, 100])
    );
    // 100 and 101 are both head ids.  The first collision begins at 102.
    assert!(
        fixture
            .backend
            .lookup_row(
                fixture.trans,
                &[Value::new(70), Value::new(80), Value::new(101)]
            )
            .is_some()
    );
    assert!(
        fixture
            .backend
            .lookup_row(fixture.sym, &[Value::new(70), Value::new(102)])
            .is_some()
    );
    Ok(())
}

#[test]
fn multi_wave_self_writes_drain_to_fixpoint_deterministically() -> Result<()> {
    type FixpointTranscript = (Vec<Vec<u32>>, Vec<Vec<u32>>, Vec<Vec<u32>>, u64);

    fn run(prefix: &str) -> Result<FixpointTranscript> {
        let mut fixture = Fixture::new(prefix)?;
        fixture.backend.storage.set_next_fresh_id(100)?;
        fixture.seed_uf(&[(40, 30, 70), (30, 20, 80), (20, 10, 90)])?;
        let rule = fixture.rule;
        assert!(fixture.run(&[rule])?);
        let scan = |table| {
            let mut rows = fixture
                .backend
                .storage
                .scan(fixture.backend.base_values(), table)?
                .into_iter()
                .map(|row| row.values.into_iter().map(Value::rep).collect::<Vec<_>>())
                .collect::<Vec<_>>();
            rows.sort();
            Ok::<_, anyhow::Error>(rows)
        };
        let result = (
            scan(fixture.uf)?,
            scan(fixture.sym)?,
            scan(fixture.trans)?,
            fixture.backend.storage.next_fresh_id()?,
        );
        assert_eq!(fixture.scratch_count()?, 0);
        Ok(result)
    }

    let first = run("deterministic-alpha")?;
    let second = run("deterministic-beta")?;
    assert_eq!(first, second, "names must not affect the SQL transcript");
    assert_eq!(first.3, 108, "two head and three collision pairs");
    assert!(first.0.contains(&vec![30, 10, 100]));
    assert!(first.0.contains(&vec![40, 20, 101]));
    assert!(first.0.contains(&vec![20, 10, 90]));
    Ok(())
}

#[test]
fn independent_targets_globally_drain_wave_before_later_generated_candidates() -> Result<()> {
    let mut fixture = Fixture::new("first-target")?;
    let second_label = fixture
        .backend
        .base_values()
        .get(Boxed::new("second-target-opaque-sort".to_string()));
    let second = add_instance(
        &mut fixture.backend,
        "second-target",
        fixture.unit,
        fixture.string,
        second_label,
        fixture.tokens,
    )?;
    fixture.backend.storage.set_next_fresh_id(100)?;
    fixture.seed_uf(&[(40, 30, 70), (30, 20, 80), (20, 10, 90)])?;
    fixture.backend.storage.with_connection(|connection| {
        for (key, parent, proof) in [(230_u64, 220_u64, 270_u64), (220, 210, 280)] {
            connection.execute(
                &format!(
                    "INSERT INTO {} VALUES ({key}, {parent}, {proof}, 0, FALSE)",
                    sql_table(second.uf)
                ),
                [],
            )?;
        }
        Ok(())
    })?;

    let first_rule = fixture.rule;
    assert!(fixture.run(&[first_rule, second.rule])?);
    // Heads are 100, 101, 102.  First-target wave 0 gets 103..106;
    // second-target wave 0 must get 107/108 before first-target wave 1
    // becomes eligible for 109/110.
    assert!(
        fixture
            .backend
            .lookup_row(second.sym, &[Value::new(270), Value::new(107)])
            .is_some()
    );
    assert!(
        fixture
            .backend
            .lookup_row(fixture.sym, &[Value::new(106), Value::new(109)])
            .is_some()
    );
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 111);
    assert_eq!(fixture.scratch_count()?, 0);
    Ok(())
}

#[test]
fn late_assert_eq_failure_rolls_back_rows_ids_watermark_and_scratch_then_reuses_ids() -> Result<()>
{
    let mut fixture = Fixture::new("late-failure")?;
    fixture.backend.storage.set_next_fresh_id(100)?;
    fixture.seed_uf(&[(30, 20, 70), (20, 10, 80)])?;
    let generation = fixture.backend.storage.generation()?;
    fixture.backend.storage.with_connection(|connection| {
        // This is the collision Trans key predicted after head=100 and Sym=101.
        // FALSE is deliberately corrupt for Unit and forces AssertEq after the
        // head Trans and Sym statements have already executed in-transaction.
        connection.execute(
            &format!(
                "INSERT INTO {} VALUES (101, 100, 102, FALSE, 0, FALSE)",
                sql_table(fixture.trans)
            ),
            [],
        )?;
        Ok(())
    })?;

    let rule = fixture.rule;
    let error = fixture
        .backend
        .run_rules(RuleSetRun {
            name: Some("late-assert-eq"),
            rules: &[rule],
        })
        .unwrap_err();
    assert!(error.to_string().contains("AssertEq"));
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 100);
    assert_eq!(fixture.backend.storage.generation()?, generation);
    assert_eq!(fixture.backend.table_size(fixture.sym), 0);
    assert_eq!(fixture.backend.table_size(fixture.trans), 1);
    assert_eq!(
        ids(fixture.backend.lookup_row(fixture.uf, &[Value::new(30)])),
        Some(vec![30, 20, 70])
    );
    assert_eq!(fixture.scratch_count()?, 0);

    fixture.backend.storage.with_connection(|connection| {
        connection.execute(&format!("DELETE FROM {}", sql_table(fixture.trans)), [])?;
        Ok(())
    })?;
    assert!(fixture.run(&[rule])?);
    assert!(
        fixture
            .backend
            .lookup_row(
                fixture.trans,
                &[Value::new(70), Value::new(80), Value::new(100)]
            )
            .is_some()
    );
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 103);
    Ok(())
}

#[test]
fn head_and_collision_fresh_exhaustion_fail_closed_without_phantom_state() -> Result<()> {
    let mut head = Fixture::new("head-exhaustion")?;
    head.seed_uf(&[(30, 20, 70), (20, 10, 80)])?;
    head.backend.storage.set_next_fresh_id(u32::MAX as u64)?;
    let rule = head.rule;
    let error = head
        .backend
        .run_rules(RuleSetRun {
            name: Some("head-exhaustion"),
            rules: &[rule],
        })
        .unwrap_err();
    assert!(error.to_string().contains("usable Value domain"));
    assert_eq!(head.backend.storage.next_fresh_id()?, u32::MAX as u64);
    assert_eq!(head.backend.table_size(head.sym), 0);
    assert_eq!(head.backend.table_size(head.trans), 0);
    assert_eq!(head.scratch_count()?, 0);

    let mut collision = Fixture::new("collision-exhaustion")?;
    collision.seed_uf(&[(30, 20, 70), (20, 10, 80)])?;
    collision
        .backend
        .storage
        .set_next_fresh_id(u32::MAX as u64 - 2)?;
    let rule = collision.rule;
    let error = collision
        .backend
        .run_rules(RuleSetRun {
            name: Some("collision-exhaustion"),
            rules: &[rule],
        })
        .unwrap_err();
    assert!(error.to_string().contains("usable Value domain"));
    assert_eq!(
        collision.backend.storage.next_fresh_id()?,
        u32::MAX as u64 - 2
    );
    assert_eq!(collision.backend.table_size(collision.sym), 0);
    assert_eq!(collision.backend.table_size(collision.trans), 0);
    assert_eq!(collision.scratch_count()?, 0);
    collision.backend.storage.set_next_fresh_id(100)?;
    assert!(collision.run(&[rule])?);
    assert_eq!(collision.backend.storage.next_fresh_id()?, 103);
    Ok(())
}

#[test]
fn corrupt_duplicate_owners_fail_closed_and_unsupported_shape_consumes_no_rule_id() -> Result<()> {
    let mut fixture = Fixture::new("fail-closed")?;
    fixture.backend.storage.set_next_fresh_id(100)?;
    fixture.seed_uf(&[(30, 20, 70), (30, 21, 71), (20, 10, 80), (21, 10, 81)])?;
    let rule = fixture.rule;
    let error = fixture
        .backend
        .run_rules(RuleSetRun {
            name: Some("duplicate-owner"),
            rules: &[rule],
        })
        .unwrap_err();
    assert!(error.to_string().contains("duplicate"));
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 100);
    assert_eq!(fixture.backend.table_size(fixture.sym), 0);
    assert_eq!(fixture.backend.table_size(fixture.trans), 0);
    assert_eq!(fixture.scratch_count()?, 0);

    let mut unsupported = fixture.rule_spec("unsupported-primitive");
    let RuleBodyCall::Primitive { id, name, .. } = &mut unsupported.core.body.atoms[2].head else {
        unreachable!();
    };
    *id = fixture.tokens.ordering_min;
    *name = "!=".into();
    assert!(
        fixture
            .backend
            .add_rule(unsupported)
            .unwrap_err()
            .to_string()
            .contains("ValueNeq")
    );
    let next = fixture.backend.add_rule(fixture.rule_spec("still-valid"))?;
    assert_eq!(next.rep(), 1, "failed admission must not consume RuleId 1");
    Ok(())
}

fn add_mutated_path_union_find(
    fixture: &mut Fixture,
    name: &str,
    mutate: impl FnOnce(&mut MergeFn),
) -> Result<FunctionId> {
    let info = fixture.backend.storage.table_info(fixture.uf)?;
    let predicted = fixture.backend.peek_next_function_id();
    let mut merge = path_ordered_union(
        fixture.tokens,
        fixture.string,
        fixture.unit,
        fixture.proof_sort,
        fixture.backend.base_values().get(()),
        fixture.sym,
        fixture.trans,
        predicted,
    );
    mutate(&mut merge);
    let target = fixture.backend.add_table(FunctionConfig {
        schema: info.schema,
        n_vals: info.n_vals,
        n_identity_vals: info.n_identity_vals,
        default: info.default,
        merge,
        name: name.into(),
        can_subsume: info.can_subsume,
    });
    assert_eq!(target, predicted);
    Ok(target)
}

fn assert_path_admission_rejected(
    fixture: &mut Fixture,
    target: FunctionId,
    name: &str,
    fragment: &str,
) {
    let error = fixture
        .backend
        .add_rule(path_rule(
            name,
            fixture.unit,
            fixture.string,
            fixture.proof_sort,
            fixture.tokens,
            fixture.trans,
            target,
        ))
        .unwrap_err();
    assert!(error.to_string().contains(fragment), "{error:#}");
}

#[test]
fn native_path_merge_tags_and_topology_are_authenticated_before_rule_id() -> Result<()> {
    let mut fixture = Fixture::new("path-native-auth")?;

    let hostile = fixture
        .backend
        .new_panic("ordinary canonical-name callback must stay declarative".into());
    let ordinary = add_mutated_path_union_find(&mut fixture, "ordinary-max-token", |merge| {
        let MergeFn::Block { actions, .. } = merge else {
            unreachable!()
        };
        let MergeAction::Let { value, .. } = &mut actions[0] else {
            unreachable!()
        };
        let MergeFn::Primitive { id, name, .. } = value else {
            unreachable!()
        };
        *id = hostile;
        *name = "proof-of-max".into();
    })?;
    assert_path_admission_rejected(
        &mut fixture,
        ordinary,
        "ordinary max token",
        "SelectMaxPayload",
    );

    let select_min = fixture.tokens.select_min;
    let swapped = add_mutated_path_union_find(&mut fixture, "swapped-max-token", |merge| {
        let MergeFn::Block { actions, .. } = merge else {
            unreachable!()
        };
        let MergeAction::Let { value, .. } = &mut actions[0] else {
            unreachable!()
        };
        let MergeFn::Primitive { id, .. } = value else {
            unreachable!()
        };
        *id = select_min;
    })?;
    assert_path_admission_rejected(
        &mut fixture,
        swapped,
        "swapped max token",
        "SelectMaxPayload",
    );

    let unit = fixture.unit;
    let malformed =
        add_mutated_path_union_find(&mut fixture, "malformed-max-signature", |merge| {
            let MergeFn::Block { actions, .. } = merge else {
                unreachable!()
            };
            let MergeAction::Let { value, .. } = &mut actions[0] else {
                unreachable!()
            };
            let MergeFn::Primitive { output, .. } = value else {
                unreachable!()
            };
            *output = ColumnTy::Base(unit);
        })?;
    assert_path_admission_rejected(
        &mut fixture,
        malformed,
        "malformed max signature",
        "SelectMaxPayload",
    );

    let topology = add_mutated_path_union_find(&mut fixture, "malformed-max-topology", |merge| {
        let MergeFn::Block { actions, .. } = merge else {
            unreachable!()
        };
        let MergeAction::Let { value, .. } = &mut actions[0] else {
            unreachable!()
        };
        let MergeFn::Primitive { args, .. } = value else {
            unreachable!()
        };
        args.swap(0, 2);
    })?;
    assert_path_admission_rejected(
        &mut fixture,
        topology,
        "malformed max topology",
        "topology mismatch",
    );

    let next = fixture
        .backend
        .add_rule(fixture.rule_spec("valid-after-native-auth"))?;
    assert_eq!(next.rep(), 1, "rejected native shapes must not consume ids");
    Ok(())
}

#[test]
fn admission_requires_all_eight_rule_roles_to_be_distinct() -> Result<()> {
    // Each mutation preserves the intended join/alias edges while making one
    // semantic role reuse another role's numeric identity.
    for (label, from, to) in [
        ("inequality-output-v5", 5, 0),
        ("fresh-binding-v6", 6, 5),
        ("alias-binding-v7", 7, 6),
    ] {
        let mut fixture = Fixture::new(label)?;
        let mut invalid = fixture.rule_spec(label);
        remap_rule_role(&mut invalid, from, to);
        let error = fixture.backend.add_rule(invalid).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("aliases structurally distinct variables"),
            "unexpected {label} admission error: {error:#}"
        );
        let next = fixture
            .backend
            .add_rule(fixture.rule_spec(&format!("{label}-valid")))?;
        assert_eq!(next.rep(), 1, "failed {label} admission consumed RuleId 1");
    }
    Ok(())
}

#[test]
fn proof_targets_require_fail_default_and_no_identity_guard() -> Result<()> {
    for (label, constant_default, n_identity_vals) in [
        ("non-fail-default", true, None),
        ("identity-guard", false, Some(1)),
    ] {
        let mut fixture = Fixture::new(label)?;
        let default = if constant_default {
            DefaultVal::Const(fixture.backend.base_values().get(()))
        } else {
            DefaultVal::Fail
        };
        let malformed = fixture.backend.add_table(FunctionConfig {
            schema: vec![
                ColumnTy::Id,
                ColumnTy::Id,
                ColumnTy::Id,
                ColumnTy::Base(fixture.unit),
            ],
            n_vals: 1,
            n_identity_vals,
            default,
            merge: MergeFn::AssertEq,
            name: format!("{label}-malformed-proof-target"),
            can_subsume: false,
        });
        let mut invalid = fixture.rule_spec(label);
        let GenericCoreAction::Set(_, call, _, _) = &mut invalid.core.head.0[2] else {
            unreachable!();
        };
        let RuleActionCall::Table { id, .. } = call else {
            unreachable!();
        };
        *id = malformed;
        let error = fixture.backend.add_rule(invalid).unwrap_err();
        assert!(
            error.to_string().contains("proof target"),
            "unexpected {label} admission error: {error:#}"
        );
        let next = fixture
            .backend
            .add_rule(fixture.rule_spec(&format!("{label}-valid")))?;
        assert_eq!(next.rep(), 1, "failed {label} admission consumed RuleId 1");
    }
    Ok(())
}
