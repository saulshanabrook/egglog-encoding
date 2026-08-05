use anyhow::Result;
use egglog_ast::{
    core::{
        GenericAtom, GenericAtomTerm, GenericCoreAction, GenericCoreActions, GenericCoreRule, Query,
    },
    generic_ast::Change,
    span::Span,
};
use egglog_backend_trait::{
    Backend, BaseValueId, ColumnTy, DefaultVal, ExternalFunctionId, FunctionConfig, FunctionId,
    MergeAction, MergeFn, NativePrimitive, ReadMode, RuleActionCall, RuleBodyCall, RuleId,
    RuleSetRun, RuleSpec, RuleValue, RuleVar, Value,
};
use egglog_core_relations::Boxed;
use egglog_numeric_id::NumericId;
use ordered_float::OrderedFloat;

use crate::{
    EGraph,
    storage::{ScalarSqlType, sql_table},
};

type Term = GenericAtomTerm<RuleVar, RuleValue>;

#[derive(Clone, Copy)]
pub(crate) enum BodyOrder {
    ViewUfNeq,
    NeqUfView,
    UfViewNeq,
}

#[derive(Clone, Copy)]
pub(crate) struct NativeTokens {
    pub(crate) neq: ExternalFunctionId,
    pub(crate) select_min: ExternalFunctionId,
    pub(crate) select_max: ExternalFunctionId,
    pub(crate) ordering_min: ExternalFunctionId,
    pub(crate) ordering_max: ExternalFunctionId,
    pub(crate) fresh: ExternalFunctionId,
}

pub(crate) struct Fixture {
    pub(crate) backend: EGraph,
    pub(crate) unit: BaseValueId,
    pub(crate) string: BaseValueId,
    pub(crate) i64_ty: BaseValueId,
    pub(crate) label: Value,
    pub(crate) tokens: NativeTokens,
    pub(crate) sym: FunctionId,
    pub(crate) trans: FunctionId,
    pub(crate) congr: FunctionId,
    pub(crate) uf: FunctionId,
    pub(crate) output_uf: FunctionId,
    pub(crate) view: FunctionId,
    pub(crate) key_types: Vec<ColumnTy>,
}

impl Fixture {
    pub(crate) fn new(
        prefix: &str,
        key_layout: impl FnOnce(BaseValueId, BaseValueId) -> Vec<ColumnTy>,
    ) -> Result<Self> {
        Self::new_with_distinct_output(prefix, key_layout, false)
    }

    fn new_with_distinct_output(
        prefix: &str,
        key_layout: impl FnOnce(BaseValueId, BaseValueId) -> Vec<ColumnTy>,
        distinct_output_uf: bool,
    ) -> Result<Self> {
        let mut backend = EGraph::new()?;
        let unit = backend.base_values_mut().register_type::<()>();
        let string = backend.base_values_mut().register_type::<Boxed<String>>();
        let i64_ty = backend.base_values_mut().register_type::<i64>();
        backend.base_values_mut().register_type::<bool>();
        backend
            .base_values_mut()
            .register_type::<Boxed<OrderedFloat<f64>>>();
        let label = backend
            .base_values()
            .get(Boxed::new(format!("{prefix}-opaque-fresh-domain")));
        let tokens = NativeTokens {
            neq: backend.register_native_primitive(NativePrimitive::ValueNeq),
            select_min: backend.register_native_primitive(NativePrimitive::SelectMinPayload),
            select_max: backend.register_native_primitive(NativePrimitive::SelectMaxPayload),
            ordering_min: backend.register_native_primitive(NativePrimitive::OrderingMin),
            ordering_max: backend.register_native_primitive(NativePrimitive::OrderingMax),
            fresh: backend.register_get_fresh(),
        };
        let key_types = key_layout(string, i64_ty);
        let unit_value = backend.base_values().get(());

        let sym = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Base(unit)],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::AssertEq,
            name: format!("{prefix}-renamed-unary-evidence"),
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
            name: format!("{prefix}-renamed-binary-evidence"),
            can_subsume: false,
        });
        let congr = backend.add_table(FunctionConfig {
            schema: vec![
                ColumnTy::Id,
                ColumnTy::Base(i64_ty),
                ColumnTy::Id,
                ColumnTy::Id,
                ColumnTy::Base(unit),
            ],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::AssertEq,
            name: format!("{prefix}-renamed-indexed-evidence"),
            can_subsume: false,
        });

        let predicted_uf = backend.peek_next_function_id();
        let uf = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
            n_vals: 2,
            n_identity_vals: Some(1),
            default: DefaultVal::Fail,
            merge: ordered_union(
                tokens,
                label,
                string,
                unit,
                unit_value,
                sym,
                trans,
                predicted_uf,
                false,
            ),
            name: format!("{prefix}-renamed-parent-map"),
            can_subsume: false,
        });
        assert_eq!(uf, predicted_uf);

        let output_uf = if distinct_output_uf {
            let predicted_output_uf = backend.peek_next_function_id();
            let output_uf = backend.add_table(FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
                n_vals: 2,
                n_identity_vals: Some(1),
                default: DefaultVal::Fail,
                merge: ordered_union(
                    tokens,
                    label,
                    string,
                    unit,
                    unit_value,
                    sym,
                    trans,
                    predicted_output_uf,
                    false,
                ),
                name: format!("{prefix}-renamed-output-parent-map"),
                can_subsume: false,
            });
            assert_eq!(output_uf, predicted_output_uf);
            output_uf
        } else {
            uf
        };

        let mut view_schema = key_types.clone();
        view_schema.extend([ColumnTy::Id, ColumnTy::Id]);
        let view = backend.add_table(FunctionConfig {
            schema: view_schema,
            n_vals: 2,
            n_identity_vals: Some(1),
            default: DefaultVal::Fail,
            merge: ordered_union(
                tokens, label, string, unit, unit_value, sym, trans, output_uf, true,
            ),
            name: format!("{prefix}-renamed-view"),
            can_subsume: true,
        });

        Ok(Self {
            backend,
            unit,
            string,
            i64_ty,
            label,
            tokens,
            sym,
            trans,
            congr,
            uf,
            output_uf,
            view,
            key_types,
        })
    }

    pub(crate) fn one_id(prefix: &str) -> Result<Self> {
        Self::new(prefix, |_, _| vec![ColumnTy::Id])
    }

    fn one_id_with_distinct_output(prefix: &str) -> Result<Self> {
        Self::new_with_distinct_output(prefix, |_, _| vec![ColumnTy::Id], true)
    }

    fn nullary(prefix: &str) -> Result<Self> {
        Self::new(prefix, |_, _| vec![])
    }

    pub(crate) fn eq_rule(&self, prefix: &str, child_index: usize, order: BodyOrder) -> RuleSpec {
        let mut next = 0_u32;
        let keys = self
            .key_types
            .iter()
            .enumerate()
            .map(|(index, &ty)| {
                let variable = var(next, &format!("{prefix}-key-{index}"), ty);
                next += 1;
                variable
            })
            .collect::<Vec<_>>();
        let identity = var(next, "opaque-identity", ColumnTy::Id);
        next += 1;
        let row_payload = var(next, "opaque-row-payload", ColumnTy::Id);
        next += 1;
        let canonical = var(next, "opaque-canonical", ColumnTy::Id);
        next += 1;
        let edge_payload = var(next, "opaque-edge-payload", ColumnTy::Id);
        next += 1;
        let neq_result = var(next, "opaque-unit", ColumnTy::Base(self.unit));
        next += 1;
        let fresh = RuleVar {
            id: next,
            name: "opaque-head-fresh".into(),
            ty: ColumnTy::Id,
        };
        next += 1;
        let alias = RuleVar {
            id: next,
            name: "opaque-head-alias".into(),
            ty: ColumnTy::Id,
        };

        let mut view_args = keys.clone();
        view_args.extend([identity.clone(), row_payload.clone()]);
        let view_atom = table_atom(self.view, ReadMode::All, view_args);
        let uf_atom = table_atom(
            self.uf,
            ReadMode::All,
            vec![
                keys[child_index].clone(),
                canonical.clone(),
                edge_payload.clone(),
            ],
        );
        let neq_atom = inequality(
            self.tokens.neq,
            self.unit,
            keys[child_index].clone(),
            canonical.clone(),
            neq_result,
        );
        let atoms = ordered_atoms(order, view_atom, uf_atom, neq_atom);

        let mut updated_keys = keys.clone();
        updated_keys[child_index] = canonical;
        RuleSpec {
            name: format!("{prefix}-totally-renamed-eq-key"),
            seminaive: true,
            no_decomp: false,
            core: GenericCoreRule {
                span: Span::Panic,
                body: Query { atoms },
                head: GenericCoreActions::new(vec![
                    fresh_action(self.tokens.fresh, self.string, self.label, fresh.clone()),
                    GenericCoreAction::LetAtomTerm(Span::Panic, alias.clone(), variable(fresh)),
                    GenericCoreAction::Set(
                        Span::Panic,
                        table_call(self.congr),
                        vec![
                            row_payload,
                            literal(
                                self.backend.base_values().get(child_index as i64),
                                ColumnTy::Base(self.i64_ty),
                            ),
                            edge_payload,
                            variable(alias.clone()),
                        ],
                        vec![unit_literal(&self.backend, self.unit)],
                    ),
                    GenericCoreAction::Set(
                        Span::Panic,
                        table_call(self.view),
                        updated_keys,
                        vec![identity, variable(alias)],
                    ),
                    GenericCoreAction::Change(
                        Span::Panic,
                        Change::Delete,
                        table_call(self.view),
                        keys,
                    ),
                ]),
            },
        }
    }

    fn eclass_rule(&self, prefix: &str, order: BodyOrder) -> RuleSpec {
        let mut next = 100_u32;
        let keys = self
            .key_types
            .iter()
            .enumerate()
            .map(|(index, &ty)| {
                let variable = var(next, &format!("{prefix}-key-{index}"), ty);
                next += 3;
                variable
            })
            .collect::<Vec<_>>();
        let identity = var(next, "opaque-value", ColumnTy::Id);
        next += 3;
        let row_payload = var(next, "opaque-view-payload", ColumnTy::Id);
        next += 3;
        let canonical = var(next, "opaque-leader", ColumnTy::Id);
        next += 3;
        let edge_payload = var(next, "opaque-uf-payload", ColumnTy::Id);
        next += 3;
        let neq_result = var(next, "opaque-unused-unit", ColumnTy::Base(self.unit));
        next += 3;
        let sym_fresh = RuleVar {
            id: next,
            name: "opaque-first-fresh".into(),
            ty: ColumnTy::Id,
        };
        next += 3;
        let sym_alias = RuleVar {
            id: next,
            name: "opaque-first-alias".into(),
            ty: ColumnTy::Id,
        };
        next += 3;
        let trans_fresh = RuleVar {
            id: next,
            name: "opaque-second-fresh".into(),
            ty: ColumnTy::Id,
        };
        next += 3;
        let trans_alias = RuleVar {
            id: next,
            name: "opaque-second-alias".into(),
            ty: ColumnTy::Id,
        };

        let mut view_args = keys.clone();
        view_args.extend([identity.clone(), row_payload.clone()]);
        let view_atom = table_atom(self.view, ReadMode::All, view_args);
        let uf_atom = table_atom(
            self.uf,
            ReadMode::All,
            vec![identity.clone(), canonical.clone(), edge_payload.clone()],
        );
        let neq_atom = inequality(
            self.tokens.neq,
            self.unit,
            identity,
            canonical.clone(),
            neq_result,
        );
        let atoms = ordered_atoms(order, view_atom, uf_atom, neq_atom);

        RuleSpec {
            name: format!("{prefix}-totally-renamed-eclass-output"),
            seminaive: true,
            no_decomp: false,
            core: GenericCoreRule {
                span: Span::Panic,
                body: Query { atoms },
                head: GenericCoreActions::new(vec![
                    fresh_action(
                        self.tokens.fresh,
                        self.string,
                        self.label,
                        sym_fresh.clone(),
                    ),
                    GenericCoreAction::LetAtomTerm(
                        Span::Panic,
                        sym_alias.clone(),
                        variable(sym_fresh),
                    ),
                    GenericCoreAction::Set(
                        Span::Panic,
                        table_call(self.sym),
                        vec![edge_payload, variable(sym_alias.clone())],
                        vec![unit_literal(&self.backend, self.unit)],
                    ),
                    fresh_action(
                        self.tokens.fresh,
                        self.string,
                        self.label,
                        trans_fresh.clone(),
                    ),
                    GenericCoreAction::LetAtomTerm(
                        Span::Panic,
                        trans_alias.clone(),
                        variable(trans_fresh),
                    ),
                    GenericCoreAction::Set(
                        Span::Panic,
                        table_call(self.trans),
                        vec![
                            variable(sym_alias),
                            row_payload,
                            variable(trans_alias.clone()),
                        ],
                        vec![unit_literal(&self.backend, self.unit)],
                    ),
                    GenericCoreAction::Set(
                        Span::Panic,
                        table_call(self.view),
                        keys,
                        vec![canonical, variable(trans_alias)],
                    ),
                ]),
            },
        }
    }

    pub(crate) fn insert_ids(
        &self,
        table: FunctionId,
        values: &[u64],
        generation: u64,
        subsumed: bool,
    ) -> Result<()> {
        self.backend.storage.with_connection(|connection| {
            let values = values
                .iter()
                .map(|value| format!("CAST('{value}' AS UBIGINT)"))
                .collect::<Vec<_>>()
                .join(", ");
            connection.execute(
                &format!(
                    "INSERT INTO {} VALUES ({values}, CAST('{generation}' AS UBIGINT), {subsumed})",
                    sql_table(table)
                ),
                [],
            )?;
            Ok(())
        })
    }

    pub(crate) fn insert_typed(
        &self,
        table: FunctionId,
        values: &[Value],
        generation: u64,
        subsumed: bool,
    ) -> Result<()> {
        let info = self.backend.storage.table_info(table)?;
        assert_eq!(values.len(), info.schema.len());
        let values = info
            .schema
            .iter()
            .zip(values)
            .map(|(&ty, &value)| {
                ScalarSqlType::from_column(self.backend.base_values(), ty)?
                    .sql_literal(self.backend.base_values(), value)
            })
            .collect::<Result<Vec<_>>>()?
            .join(", ");
        self.backend.storage.with_connection(|connection| {
            connection.execute(
                &format!(
                    "INSERT INTO {} VALUES ({values}, CAST('{generation}' AS UBIGINT), {subsumed})",
                    sql_table(table)
                ),
                [],
            )?;
            Ok(())
        })
    }

    pub(crate) fn run(&mut self, rules: &[RuleId]) -> Result<bool> {
        Ok(self
            .backend
            .run_rules(RuleSetRun {
                name: Some("renamed-standard-rebuild-canary"),
                rules,
            })?
            .changed())
    }

    pub(crate) fn scratch_count(&self) -> Result<u64> {
        self.backend.storage.with_connection(|connection| {
            connection
                .query_row(
                    "SELECT count(*) FROM duckdb_tables()
                     WHERE table_name LIKE 'egglog_rebuild_%'",
                    [],
                    |row| row.get(0),
                )
                .map_err(Into::into)
        })
    }

    pub(crate) fn watermark(&self, rule: RuleId) -> u64 {
        self.backend.rules[rule.rep() as usize]
            .as_ref()
            .expect("test rule remains registered")
            .watermark
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn ordered_union(
    tokens: NativeTokens,
    label: Value,
    string: BaseValueId,
    unit: BaseValueId,
    unit_value: Value,
    sym: FunctionId,
    trans: FunctionId,
    displaced: FunctionId,
    eclass_to_term: bool,
) -> MergeFn {
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
    let fresh = || MergeFn::Primitive {
        id: tokens.fresh,
        name: "renamed-fresh-diagnostic".to_string(),
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

fn ordered_atoms(
    order: BodyOrder,
    view: GenericAtom<RuleBodyCall, RuleVar, RuleValue>,
    uf: GenericAtom<RuleBodyCall, RuleVar, RuleValue>,
    neq: GenericAtom<RuleBodyCall, RuleVar, RuleValue>,
) -> Vec<GenericAtom<RuleBodyCall, RuleVar, RuleValue>> {
    match order {
        BodyOrder::ViewUfNeq => vec![view, uf, neq],
        BodyOrder::NeqUfView => vec![neq, uf, view],
        BodyOrder::UfViewNeq => vec![uf, view, neq],
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
    token: ExternalFunctionId,
    unit: BaseValueId,
    lhs: Term,
    rhs: Term,
    result: Term,
) -> GenericAtom<RuleBodyCall, RuleVar, RuleValue> {
    GenericAtom {
        span: Span::Panic,
        head: RuleBodyCall::Primitive {
            id: token,
            name: "renamed-rebuild-neq-diagnostic".into(),
            output: ColumnTy::Base(unit),
        },
        args: vec![lhs, rhs, result],
    }
}

fn fresh_action(
    token: ExternalFunctionId,
    string: BaseValueId,
    label: Value,
    binding: RuleVar,
) -> GenericCoreAction<RuleActionCall, RuleVar, RuleValue> {
    GenericCoreAction::Let(
        Span::Panic,
        binding,
        RuleActionCall::Primitive {
            id: token,
            name: "renamed-rebuild-head-fresh".into(),
            output: ColumnTy::Id,
        },
        vec![literal(label, ColumnTy::Base(string))],
    )
}

fn table_call(id: FunctionId) -> RuleActionCall {
    RuleActionCall::Table {
        id,
        name: format!("opaque-target-{}", id.rep()).into(),
    }
}

fn retarget_eq_view(
    rule: &mut RuleSpec,
    old_view: FunctionId,
    new_view: FunctionId,
    read: ReadMode,
) {
    for atom in &mut rule.core.body.atoms {
        if let RuleBodyCall::Table {
            id,
            read: atom_read,
        } = &mut atom.head
            && *id == old_view
        {
            *id = new_view;
            *atom_read = read;
        }
    }
    for action in &mut rule.core.head.0 {
        let call = match action {
            GenericCoreAction::Set(_, call, ..) | GenericCoreAction::Change(_, _, call, ..) => call,
            _ => continue,
        };
        if let RuleActionCall::Table { id, .. } = call
            && *id == old_view
        {
            *id = new_view;
        }
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

fn unit_literal(backend: &EGraph, unit: BaseValueId) -> Term {
    literal(backend.base_values().get(()), ColumnTy::Base(unit))
}

pub(crate) fn ids(row: Option<Vec<Value>>) -> Option<Vec<u32>> {
    row.map(|values| values.into_iter().map(Value::rep).collect())
}

fn rejected_rule_preserves_id(
    fixture: &mut Fixture,
    rule: RuleSpec,
    standard_family: bool,
    message_fragment: &str,
) -> Result<()> {
    let error = format!("{:#}", fixture.backend.add_rule(rule).unwrap_err());
    let classified_standard = error.contains("standard rebuild")
        || error.contains("eq-key rebuild")
        || error.contains("eclass-output rebuild");
    assert_eq!(classified_standard, standard_family, "{error}");
    assert!(error.contains(message_fragment), "{error}");
    let valid = fixture.eq_rule("valid-after-mutation", 0, BodyOrder::NeqUfView);
    assert_eq!(fixture.backend.add_rule(valid)?, RuleId::new(0));
    Ok(())
}

#[test]
fn renamed_and_reordered_standard_shapes_execute_without_host_callbacks() -> Result<()> {
    let mut eq = Fixture::one_id("eq-hostile-name")?;
    let eq_rule = eq
        .backend
        .add_rule(eq.eq_rule("eq-hostile-rule", 0, BodyOrder::NeqUfView))?;
    let plan = &eq.backend.rules[eq_rule.rep() as usize]
        .as_ref()
        .expect("registered rule")
        .plan;
    assert!(plan.scalar_action().is_some());
    assert!(plan.standard_rebuild().is_none());
    assert!(plan.marker_rekey().is_none());
    assert!(plan.path_compression().is_none());
    eq.backend.storage.set_next_fresh_id(100)?;
    eq.insert_ids(eq.view, &[30, 40, 70], 0, false)?;
    eq.insert_ids(eq.uf, &[30, 20, 80], 0, false)?;
    assert!(eq.run(&[eq_rule])?);
    assert_eq!(eq.backend.storage.next_fresh_id()?, 101);
    assert_eq!(eq.backend.lookup_row(eq.view, &[Value::new(30)]), None);
    assert_eq!(
        ids(eq.backend.lookup_row(eq.view, &[Value::new(20)])),
        Some(vec![20, 40, 100])
    );
    assert_eq!(
        ids(eq.backend.lookup_row(
            eq.congr,
            &[
                Value::new(70),
                eq.backend.base_values().get(0_i64),
                Value::new(80),
                Value::new(100),
            ],
        )),
        Some(vec![70, 0, 80, 100, 0])
    );
    assert_eq!(eq.scratch_count()?, 0);
    assert!(
        eq.backend
            .storage
            .latest_rule_sql()
            .iter()
            .all(|sql| !sql.contains("hostile") && !sql.contains('?'))
    );
    let mut replay = Fixture::one_id("different-names-same-plan")?;
    let replay_rule =
        replay
            .backend
            .add_rule(replay.eq_rule("different-rule-name", 0, BodyOrder::ViewUfNeq))?;
    replay.backend.storage.set_next_fresh_id(100)?;
    replay.insert_ids(replay.view, &[30, 40, 70], 0, false)?;
    replay.insert_ids(replay.uf, &[30, 20, 80], 0, false)?;
    assert!(replay.run(&[replay_rule])?);
    assert_eq!(replay.backend.storage.next_fresh_id()?, 101);
    assert_eq!(
        ids(replay.backend.lookup_row(replay.view, &[Value::new(20)])),
        Some(vec![20, 40, 100])
    );

    let mut output = Fixture::one_id("output-hostile-name")?;
    let output_rule = output
        .backend
        .add_rule(output.eclass_rule("output-hostile-rule", BodyOrder::UfViewNeq))?;
    output.backend.storage.set_next_fresh_id(200)?;
    output.insert_ids(output.view, &[1, 30, 70], 0, false)?;
    output.insert_ids(output.uf, &[30, 20, 80], 0, false)?;
    assert!(output.run(&[output_rule])?);
    assert_eq!(output.backend.storage.next_fresh_id()?, 204);
    assert_eq!(
        ids(output.backend.lookup_row(output.view, &[Value::new(1)])),
        Some(vec![1, 20, 201])
    );
    assert_eq!(
        ids(output
            .backend
            .lookup_row(output.sym, &[Value::new(201), Value::new(202)])),
        Some(vec![201, 202, 0])
    );
    assert_eq!(
        ids(output.backend.lookup_row(
            output.trans,
            &[Value::new(70), Value::new(202), Value::new(203)]
        )),
        Some(vec![70, 202, 203, 0])
    );
    // The generated UF candidate has an equal leading identity and therefore
    // retains the complete old UF tuple without a second merge.
    assert_eq!(
        ids(output.backend.lookup_row(output.uf, &[Value::new(30)])),
        Some(vec![30, 20, 80])
    );
    assert_eq!(output.scratch_count()?, 0);
    Ok(())
}

#[test]
fn eq_key_view_collision_targets_the_independent_output_union_find() -> Result<()> {
    let mut fixture = Fixture::one_id_with_distinct_output("distinct-output-uf")?;
    let rule = fixture.backend.add_rule(fixture.eq_rule(
        "distinct-output-uf-rule",
        0,
        BodyOrder::UfViewNeq,
    ))?;
    fixture.backend.storage.set_next_fresh_id(500)?;

    // The body UF canonicalizes the stale key 20 -> 10. Rekeying then collides
    // with the existing View owner, whose output eclass is a different sort:
    // that displaced 60 -> 50 edge must enter output_uf, not the body UF.
    fixture.insert_ids(fixture.view, &[10, 50, 90], 0, false)?;
    fixture.insert_ids(fixture.view, &[20, 60, 91], 0, false)?;
    fixture.insert_ids(fixture.uf, &[20, 10, 80], 0, false)?;
    assert!(fixture.run(&[rule])?);
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 503);
    assert_eq!(
        ids(fixture.backend.lookup_row(fixture.view, &[Value::new(10)])),
        Some(vec![10, 50, 90])
    );
    assert_eq!(
        ids(fixture
            .backend
            .lookup_row(fixture.output_uf, &[Value::new(60)])),
        Some(vec![60, 50, 502])
    );
    assert_eq!(
        ids(fixture.backend.lookup_row(fixture.uf, &[Value::new(20)])),
        Some(vec![20, 10, 80])
    );
    assert_eq!(fixture.scratch_count()?, 0);
    Ok(())
}

#[test]
fn all_reads_preserve_a_subsumed_owner_and_old_min_still_emits_effects() -> Result<()> {
    let mut fixture = Fixture::one_id("subsumed-old-min")?;
    let rule = fixture
        .backend
        .add_rule(fixture.eclass_rule("subsumed-old-min-rule", BodyOrder::ViewUfNeq))?;
    fixture.backend.storage.set_next_fresh_id(300)?;
    // Synthetic old-min edge: 30 canonicalizes to 40. The View owner remains
    // byte-identical but its merge Block must still emit Sym/Trans and UF(40).
    fixture.insert_ids(fixture.view, &[1, 30, 70], 0, true)?;
    fixture.insert_ids(fixture.uf, &[30, 40, 80], 0, false)?;
    assert!(fixture.run(&[rule])?);
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 304);
    let view = fixture
        .backend
        .storage
        .scan(fixture.backend.base_values(), fixture.view)?;
    assert_eq!(view.len(), 1);
    assert_eq!(
        view[0]
            .values
            .iter()
            .map(|value| value.rep())
            .collect::<Vec<_>>(),
        vec![1, 30, 70]
    );
    assert!(view[0].subsumed, "collision must not revive an owner");
    assert_eq!(
        view[0].generation, 0,
        "byte-identical old-min owner is not retimestamped"
    );
    assert_eq!(
        ids(fixture
            .backend
            .lookup_row(fixture.sym, &[Value::new(70), Value::new(302)])),
        Some(vec![70, 302, 0])
    );
    assert_eq!(
        ids(fixture.backend.lookup_row(
            fixture.trans,
            &[Value::new(301), Value::new(302), Value::new(303)]
        )),
        Some(vec![301, 302, 303, 0])
    );
    assert_eq!(
        ids(fixture.backend.lookup_row(fixture.uf, &[Value::new(40)])),
        Some(vec![40, 30, 303])
    );
    Ok(())
}

#[test]
fn malformed_standard_interior_rejects_before_rule_id_and_marker_falls_through() -> Result<()> {
    let mut mode = Fixture::one_id("bad-mode")?;
    let mut bad_mode = mode.eq_rule("bad-mode-rule", 0, BodyOrder::ViewUfNeq);
    let RuleBodyCall::Table { read, .. } = &mut bad_mode.core.body.atoms[0].head else {
        unreachable!()
    };
    *read = ReadMode::Live;
    assert_eq!(mode.backend.add_rule(bad_mode)?, RuleId::new(0));
    assert_eq!(
        mode.backend
            .add_rule(mode.eq_rule("valid-after-mode", 0, BodyOrder::NeqUfView))?,
        RuleId::new(1)
    );

    let mut index = Fixture::one_id("bad-index")?;
    let mut bad_index = index.eq_rule("bad-index-rule", 0, BodyOrder::ViewUfNeq);
    let GenericCoreAction::Set(_, _, arguments, _) = &mut bad_index.core.head.0[2] else {
        unreachable!()
    };
    arguments[1] = literal(
        index.backend.base_values().get(1_i64),
        ColumnTy::Base(index.i64_ty),
    );
    assert_eq!(index.backend.add_rule(bad_index)?, RuleId::new(0));
    assert_eq!(
        index
            .backend
            .add_rule(index.eq_rule("valid-after-index", 0, BodyOrder::ViewUfNeq))?,
        RuleId::new(1)
    );

    let mut mismatched_output = Fixture::one_id_with_distinct_output("bad-output-uf")?;
    assert_eq!(
        mismatched_output
            .backend
            .add_rule(mismatched_output.eclass_rule("bad-output-uf-rule", BodyOrder::UfViewNeq))?,
        RuleId::new(0)
    );
    assert_eq!(
        mismatched_output
            .backend
            .add_rule(mismatched_output.eq_rule(
                "valid-key-output-split",
                0,
                BodyOrder::NeqUfView,
            ))?,
        RuleId::new(1)
    );

    let mut marker = Fixture::one_id("marker")?;
    let mut marker_rule = marker.eq_rule("marker-rule", 0, BodyOrder::ViewUfNeq);
    marker_rule.core.head.0 = marker_rule.core.head.0.split_off(3);
    let marker_error = marker.backend.add_rule(marker_rule).unwrap_err();
    assert!(format!("{marker_error:#}").contains("before binding"));
    assert_eq!(
        marker
            .backend
            .add_rule(marker.eq_rule("valid-after-marker", 0, BodyOrder::ViewUfNeq))?,
        RuleId::new(0)
    );
    Ok(())
}

#[test]
fn structural_admission_mutation_matrix_is_fail_closed_without_consuming_rule_ids() -> Result<()> {
    let mut wrong_join = Fixture::one_id("matrix-wrong-join")?;
    let mut rule = wrong_join.eq_rule("matrix-wrong-join-rule", 0, BodyOrder::ViewUfNeq);
    let view_identity = rule.core.body.atoms[0].args[1].clone();
    rule.core.body.atoms[1].args[0] = view_identity;
    assert_eq!(wrong_join.backend.add_rule(rule)?, RuleId::new(0));
    assert_eq!(
        wrong_join.backend.add_rule(wrong_join.eq_rule(
            "valid-after-mutation",
            0,
            BodyOrder::NeqUfView
        ))?,
        RuleId::new(1)
    );

    let mut alias = Fixture::one_id("matrix-alias")?;
    let mut rule = alias.eq_rule("matrix-alias-rule", 0, BodyOrder::ViewUfNeq);
    let GenericCoreAction::Let(_, fresh, ..) = &rule.core.head.0[0] else {
        unreachable!()
    };
    let fresh = fresh.clone();
    let GenericCoreAction::LetAtomTerm(_, alias_binding, _) = &mut rule.core.head.0[1] else {
        unreachable!()
    };
    *alias_binding = fresh.clone();
    let GenericCoreAction::Set(_, _, congr_arguments, _) = &mut rule.core.head.0[2] else {
        unreachable!()
    };
    congr_arguments[3] = variable(fresh.clone());
    let GenericCoreAction::Set(_, _, _, view_values) = &mut rule.core.head.0[3] else {
        unreachable!()
    };
    view_values[1] = variable(fresh);
    rejected_rule_preserves_id(&mut alias, rule, false, "rebinds SSA variable")?;

    let mut fake_name = Fixture::one_id("matrix-fake-name")?;
    let mut rule = fake_name.eq_rule("matrix-fake-name-rule", 0, BodyOrder::ViewUfNeq);
    let RuleBodyCall::Primitive { id, name, .. } = &mut rule.core.body.atoms[2].head else {
        unreachable!()
    };
    *id = fake_name.tokens.ordering_min;
    *name = "!=".into();
    rejected_rule_preserves_id(
        &mut fake_name,
        rule,
        false,
        "raw OrderingMin scalar lowering",
    )?;

    let mut fake_signature = Fixture::one_id("matrix-fake-signature")?;
    let mut rule = fake_signature.eq_rule("matrix-fake-signature-rule", 0, BodyOrder::ViewUfNeq);
    let RuleBodyCall::Primitive { output, .. } = &mut rule.core.body.atoms[2].head else {
        unreachable!()
    };
    *output = ColumnTy::Id;
    rejected_rule_preserves_id(&mut fake_signature, rule, false, "ValueNeq requires")?;

    let mut child_type = Fixture::one_id("matrix-child-type")?;
    let mut rule = child_type.eq_rule("matrix-child-type-rule", 0, BodyOrder::ViewUfNeq);
    let GenericCoreAction::Set(_, _, arguments, _) = &mut rule.core.head.0[2] else {
        unreachable!()
    };
    arguments[1] = literal(child_type.label, ColumnTy::Base(child_type.string));
    rejected_rule_preserves_id(&mut child_type, rule, false, "mistyped literal")?;

    let mut container = Fixture::one_id("matrix-container")?;
    let mut rule = container.eq_rule("matrix-container-rule", 0, BodyOrder::ViewUfNeq);
    rule.core.body.atoms[1].head = RuleBodyCall::Primitive {
        id: container.tokens.neq,
        name: "opaque-container-rebuild".into(),
        output: ColumnTy::Id,
    };
    rejected_rule_preserves_id(&mut container, rule, false, "")?;
    Ok(())
}

#[test]
fn custom_view_merges_with_the_same_rule_head_are_generic() -> Result<()> {
    let mut fixture = Fixture::one_id("custom-merge-fallthrough")?;
    let mut schema = fixture.key_types.clone();
    schema.extend([ColumnTy::Id, ColumnTy::Id]);
    let unit_value = fixture.backend.base_values().get(());
    let custom_displaced = fixture.backend.add_table(FunctionConfig {
        schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
        n_vals: 1,
        n_identity_vals: None,
        default: DefaultVal::Fail,
        merge: MergeFn::AssertEq,
        name: "opaque-custom-displaced-proof".into(),
        can_subsume: false,
    });
    let custom_view = fixture.backend.add_table(FunctionConfig {
        schema: schema.clone(),
        n_vals: 2,
        n_identity_vals: Some(1),
        default: DefaultVal::Fail,
        // Same seven-action/Columns cardinality as ordered union, but its final
        // Set targets an AssertEq proof table rather than a self-merging UF.
        // That is a custom Block family and must fall through tri-state
        // admission before standard interior validation.
        merge: ordered_union(
            fixture.tokens,
            fixture.label,
            fixture.string,
            fixture.unit,
            unit_value,
            fixture.sym,
            fixture.trans,
            custom_displaced,
            true,
        ),
        name: "opaque-custom-view".into(),
        can_subsume: true,
    });
    let columns_view = fixture.backend.add_table(FunctionConfig {
        schema,
        n_vals: 2,
        n_identity_vals: Some(1),
        default: DefaultVal::Fail,
        merge: MergeFn::Columns(vec![MergeFn::OldCol(0), MergeFn::OldCol(1)]),
        name: "opaque-columns-view".into(),
        can_subsume: true,
    });

    let mut custom_rule = fixture.eq_rule("custom-merge-rule", 0, BodyOrder::ViewUfNeq);
    custom_rule.seminaive = false;
    retarget_eq_view(&mut custom_rule, fixture.view, custom_view, ReadMode::Live);
    assert_eq!(fixture.backend.add_rule(custom_rule)?, RuleId::new(0));

    let mut columns_rule = fixture.eq_rule("columns-merge-rule", 0, BodyOrder::UfViewNeq);
    retarget_eq_view(
        &mut columns_rule,
        fixture.view,
        columns_view,
        ReadMode::Live,
    );
    assert_eq!(fixture.backend.add_rule(columns_rule)?, RuleId::new(1));
    assert_eq!(
        fixture
            .backend
            .add_rule(fixture.eq_rule("valid-after-custom", 0, BodyOrder::NeqUfView,))?,
        RuleId::new(2)
    );
    Ok(())
}

#[test]
fn nullary_and_wide_scalar_admission_remain_target_typed() -> Result<()> {
    let mut nullary = Fixture::nullary("nullary")?;
    let rule = nullary
        .backend
        .add_rule(nullary.eclass_rule("nullary-output", BodyOrder::NeqUfView))?;
    nullary.backend.storage.set_next_fresh_id(400)?;
    nullary.insert_ids(nullary.view, &[30, 70], 0, false)?;
    nullary.insert_ids(nullary.uf, &[30, 20, 80], 0, false)?;
    assert!(nullary.run(&[rule])?);
    assert_eq!(
        ids(nullary.backend.lookup_row(nullary.view, &[])),
        Some(vec![20, 401])
    );

    let mut wide = Fixture::new("wide", |string, i64_ty| {
        (0..27)
            .map(|index| match index % 3 {
                0 => ColumnTy::Id,
                1 => ColumnTy::Base(i64_ty),
                _ => ColumnTy::Base(string),
            })
            .collect()
    })?;
    let rebuilt_index = 24;
    assert_eq!(wide.key_types[rebuilt_index], ColumnTy::Id);
    let rule = wide.backend.add_rule(wide.eq_rule(
        "wide-mixed-eq-key",
        rebuilt_index,
        BodyOrder::UfViewNeq,
    ))?;
    assert_eq!(rule, RuleId::new(0));
    let generation = wide.backend.storage.generation()?;
    let stale_keys = wide
        .key_types
        .iter()
        .enumerate()
        .map(|(index, ty)| match index % 3 {
            0 => {
                assert_eq!(*ty, ColumnTy::Id);
                Value::new(if index == rebuilt_index {
                    30
                } else {
                    1_000 + index as u32
                })
            }
            1 => {
                assert_eq!(*ty, ColumnTy::Base(wide.i64_ty));
                wide.backend.base_values().get(index as i64 - 50)
            }
            _ => {
                assert_eq!(*ty, ColumnTy::Base(wide.string));
                wide.backend
                    .base_values()
                    .get(Boxed::new(format!("mixed-key-{index}")))
            }
        })
        .collect::<Vec<_>>();
    let mut canonical_keys = stale_keys.clone();
    canonical_keys[rebuilt_index] = Value::new(20);
    let mut stale_row = stale_keys.clone();
    stale_row.extend([Value::new(40), Value::new(70)]);
    wide.insert_typed(wide.view, &stale_row, generation, false)?;
    wide.insert_ids(wide.uf, &[30, 20, 80], generation, false)?;
    wide.backend.storage.set_next_fresh_id(450)?;

    assert!(wide.run(&[rule])?);
    assert_eq!(wide.backend.storage.next_fresh_id()?, 451);
    assert_eq!(
        wide.backend.lookup_row(wide.view, &stale_keys),
        None,
        "stale mixed key must be deleted"
    );
    let mut canonical_row = canonical_keys.clone();
    canonical_row.extend([Value::new(40), Value::new(450)]);
    assert_eq!(
        wide.backend.lookup_row(wide.view, &canonical_keys),
        Some(canonical_row.clone())
    );
    let view_rows = wide
        .backend
        .storage
        .scan(wide.backend.base_values(), wide.view)?;
    assert_eq!(view_rows.len(), 1);
    assert_eq!(view_rows[0].values, canonical_row);
    assert!(!view_rows[0].subsumed);
    assert_eq!(view_rows[0].generation, generation);

    let proof_key = vec![
        Value::new(70),
        wide.backend.base_values().get(rebuilt_index as i64),
        Value::new(80),
        Value::new(450),
    ];
    let mut proof_row = proof_key.clone();
    proof_row.push(wide.backend.base_values().get(()));
    assert_eq!(
        wide.backend.lookup_row(wide.congr, &proof_key),
        Some(proof_row.clone())
    );
    let proof_rows = wide
        .backend
        .storage
        .scan(wide.backend.base_values(), wide.congr)?;
    assert_eq!(proof_rows.len(), 1);
    assert_eq!(proof_rows[0].values, proof_row);
    assert!(!proof_rows[0].subsumed);
    assert_eq!(proof_rows[0].generation, generation);
    assert_eq!(wide.backend.storage.generation()?, generation + 1);
    assert_eq!(wide.scratch_count()?, 0);
    Ok(())
}

#[test]
fn late_head_conflict_rolls_back_delete_counter_generation_and_scratch_then_reuses_id() -> Result<()>
{
    let mut fixture = Fixture::one_id("rollback")?;
    let rule =
        fixture
            .backend
            .add_rule(fixture.eq_rule("rollback-rule", 0, BodyOrder::ViewUfNeq))?;
    assert!(!fixture.run(&[rule])?);
    let watermark = fixture.watermark(rule);
    assert!(
        watermark > 0,
        "rollback canary requires a nonzero watermark"
    );
    fixture.backend.storage.set_next_fresh_id(500)?;
    fixture.insert_ids(fixture.view, &[30, 40, 70], watermark, false)?;
    fixture.insert_ids(fixture.uf, &[30, 20, 80], watermark, false)?;
    let generation = fixture.backend.storage.generation()?;
    assert_eq!(watermark, generation);
    fixture.backend.storage.with_connection(|connection| {
        connection.execute(
            &format!(
                "INSERT INTO {} VALUES (
                     CAST('70' AS UBIGINT), CAST('0' AS BIGINT),
                     CAST('80' AS UBIGINT), CAST('500' AS UBIGINT),
                     FALSE, CAST('0' AS UBIGINT), FALSE
                 )",
                sql_table(fixture.congr)
            ),
            [],
        )?;
        Ok(())
    })?;

    let error = fixture.run(&[rule]).unwrap_err();
    assert!(error.to_string().contains("AssertEq"));
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 500);
    assert_eq!(fixture.backend.storage.generation()?, generation);
    assert_eq!(fixture.watermark(rule), watermark);
    assert_eq!(
        ids(fixture.backend.lookup_row(fixture.view, &[Value::new(30)])),
        Some(vec![30, 40, 70])
    );
    assert_eq!(
        fixture.backend.lookup_row(fixture.view, &[Value::new(20)]),
        None
    );
    assert_eq!(fixture.scratch_count()?, 0);

    fixture.backend.storage.with_connection(|connection| {
        connection.execute(&format!("DELETE FROM {}", sql_table(fixture.congr)), [])?;
        Ok(())
    })?;
    assert!(fixture.run(&[rule])?);
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 501);
    assert_eq!(fixture.watermark(rule), watermark);
    assert_eq!(
        ids(fixture.backend.lookup_row(fixture.view, &[Value::new(20)])),
        Some(vec![20, 40, 500])
    );
    Ok(())
}

#[test]
fn corrupt_owners_and_fresh_exhaustion_fail_before_durable_mutation() -> Result<()> {
    let mut duplicate = Fixture::one_id("duplicate-owner")?;
    let rule = duplicate.backend.add_rule(duplicate.eq_rule(
        "duplicate-owner-rule",
        0,
        BodyOrder::ViewUfNeq,
    ))?;
    duplicate.backend.storage.set_next_fresh_id(600)?;
    duplicate.insert_ids(duplicate.view, &[30, 40, 70], 0, false)?;
    duplicate.insert_ids(duplicate.view, &[30, 41, 71], 0, true)?;
    duplicate.insert_ids(duplicate.uf, &[30, 20, 80], 0, false)?;
    assert!(
        duplicate
            .run(&[rule])
            .unwrap_err()
            .to_string()
            .contains("duplicate owners")
    );
    assert_eq!(duplicate.backend.storage.next_fresh_id()?, 600);
    assert_eq!(duplicate.backend.table_size(duplicate.view), 2);
    assert_eq!(duplicate.scratch_count()?, 0);

    let mut subsumed_uf = Fixture::one_id("subsumed-uf")?;
    let uf_rule = subsumed_uf
        .backend
        .add_rule(subsumed_uf.eclass_rule("subsumed-uf-rule", BodyOrder::ViewUfNeq))?;
    subsumed_uf.backend.storage.set_next_fresh_id(700)?;
    subsumed_uf.insert_ids(subsumed_uf.view, &[1, 30, 70], 0, false)?;
    subsumed_uf.insert_ids(subsumed_uf.uf, &[30, 20, 80], 0, true)?;
    assert!(subsumed_uf.run(&[uf_rule])?);
    assert_eq!(subsumed_uf.backend.storage.next_fresh_id()?, 704);
    let (uf_rows, subsumed_rows) = subsumed_uf.backend.storage.with_connection(|connection| {
        Ok(connection.query_row(
            &format!(
                "SELECT count(*), count(*) FILTER (WHERE __subsumed) FROM {}",
                sql_table(subsumed_uf.uf)
            ),
            [],
            |row| Ok((row.get::<_, u64>(0)?, row.get::<_, u64>(1)?)),
        )?)
    })?;
    assert_eq!((uf_rows, subsumed_rows), (1, 1));

    let mut exhausted = Fixture::one_id("head-exhausted")?;
    let exhausted_rule = exhausted.backend.add_rule(exhausted.eq_rule(
        "head-exhausted-rule",
        0,
        BodyOrder::ViewUfNeq,
    ))?;
    exhausted
        .backend
        .storage
        .set_next_fresh_id(u64::from(u32::MAX))?;
    exhausted.insert_ids(exhausted.view, &[30, 40, 70], 0, false)?;
    exhausted.insert_ids(exhausted.uf, &[30, 20, 80], 0, false)?;
    assert!(
        exhausted
            .run(&[exhausted_rule])
            .unwrap_err()
            .to_string()
            .contains("usable Value domain")
    );
    assert_eq!(
        exhausted.backend.storage.next_fresh_id()?,
        u64::from(u32::MAX)
    );
    assert_eq!(
        ids(exhausted
            .backend
            .lookup_row(exhausted.view, &[Value::new(30)])),
        Some(vec![30, 40, 70])
    );
    assert_eq!(exhausted.scratch_count()?, 0);
    Ok(())
}

#[test]
fn all_source_subsumption_refires_once_then_returns_to_no_delta() -> Result<()> {
    let mut fixture = Fixture::one_id("all-refire")?;
    let rule = fixture
        .backend
        .add_rule(fixture.eclass_rule("all-refire-rule", BodyOrder::ViewUfNeq))?;
    fixture.backend.storage.set_next_fresh_id(800)?;
    // An old-min mapping leaves the stale View tuple byte-identical, allowing
    // this test to isolate All-mode seminaive refiring from value rebuild.
    fixture.insert_ids(fixture.view, &[1, 30, 70], 0, false)?;
    fixture.insert_ids(fixture.uf, &[30, 40, 80], 0, false)?;
    assert!(fixture.run(&[rule])?);
    assert_eq!(fixture.backend.last_rule_match_counts(), &[1]);
    assert!(!fixture.run(&[rule])?);
    assert_eq!(fixture.backend.last_rule_match_counts(), &[0]);

    // Model the already-accepted direct Subsume phase: transition the live row
    // at the current generation and advance the global generation once.
    let transition_generation = fixture.backend.storage.generation()?;
    fixture.backend.storage.with_connection(|connection| {
        connection.execute(
            &format!(
                "UPDATE {} SET __subsumed = TRUE,
                               __generation = CAST('{transition_generation}' AS UBIGINT)",
                sql_table(fixture.view)
            ),
            [],
        )?;
        connection.execute(
            "UPDATE egglog_backend_counters SET value = value + 1 WHERE name = 'generation'",
            [],
        )?;
        Ok(())
    })?;

    assert!(fixture.run(&[rule])?);
    assert_eq!(fixture.backend.last_rule_match_counts(), &[1]);
    let after_refire = fixture.backend.storage.next_fresh_id()?;
    assert!(!fixture.run(&[rule])?);
    assert_eq!(fixture.backend.last_rule_match_counts(), &[0]);
    assert_eq!(fixture.backend.storage.next_fresh_id()?, after_refire);
    assert!(
        fixture
            .backend
            .storage
            .scan(fixture.backend.base_values(), fixture.view)?[0]
            .subsumed
    );
    Ok(())
}

#[test]
fn duplicate_candidates_fold_deterministically_and_new_rows_wait_for_the_next_run() -> Result<()> {
    let mut fixture = Fixture::one_id("stable-prewave")?;
    let first = fixture.backend.add_rule(fixture.eq_rule(
        "stable-prewave-first",
        0,
        BodyOrder::ViewUfNeq,
    ))?;
    let second = fixture.backend.add_rule(fixture.eq_rule(
        "stable-prewave-second",
        0,
        BodyOrder::NeqUfView,
    ))?;
    fixture.backend.storage.set_next_fresh_id(900)?;
    fixture.insert_ids(fixture.view, &[30, 50, 70], 0, false)?;
    fixture.insert_ids(fixture.uf, &[30, 20, 80], 0, false)?;
    fixture.insert_ids(fixture.uf, &[20, 10, 81], 0, false)?;

    assert!(fixture.run(&[first, second])?);
    assert_eq!(fixture.backend.last_rule_match_counts(), &[1, 1]);
    assert_eq!(fixture.backend.last_rule_insert_counts(), &[1, 1]);
    assert_eq!(
        fixture.backend.lookup_row(fixture.view, &[Value::new(30)]),
        None
    );
    assert_eq!(
        ids(fixture.backend.lookup_row(fixture.view, &[Value::new(20)])),
        Some(vec![20, 50, 900])
    );
    assert_eq!(
        fixture.backend.lookup_row(fixture.view, &[Value::new(10)]),
        None,
        "same-run Set must not become a match input"
    );
    // The second candidate has the same leading identity and a different
    // fresh payload. It retains the complete first tuple and allocates no
    // collision proof pair.
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 902);

    assert!(fixture.run(&[first, second])?);
    assert_eq!(fixture.backend.last_rule_match_counts(), &[1, 1]);
    assert_eq!(
        fixture.backend.lookup_row(fixture.view, &[Value::new(20)]),
        None
    );
    assert_eq!(
        ids(fixture.backend.lookup_row(fixture.view, &[Value::new(10)])),
        Some(vec![10, 50, 902])
    );
    assert_eq!(fixture.scratch_count()?, 0);
    Ok(())
}

#[test]
fn view_collision_drives_multiwave_uf_self_writes_with_key_orientation() -> Result<()> {
    let mut fixture = Fixture::one_id("multiwave")?;
    let rule =
        fixture
            .backend
            .add_rule(fixture.eq_rule("multiwave-rule", 0, BodyOrder::UfViewNeq))?;
    fixture.backend.storage.set_next_fresh_id(1000)?;
    fixture.insert_ids(fixture.view, &[30, 50, 70], 0, false)?;
    fixture.insert_ids(fixture.view, &[20, 40, 71], 0, false)?;
    fixture.insert_ids(fixture.uf, &[30, 20, 80], 0, false)?;
    fixture.insert_ids(fixture.uf, &[50, 30, 81], 0, false)?;
    fixture.insert_ids(fixture.uf, &[40, 20, 82], 0, false)?;

    assert!(fixture.run(&[rule])?);
    // One head Congr ID, then three identity-changing collisions: View,
    // UF(50), and UF(40). The generated UF(30)->20 candidate is identity-equal.
    assert_eq!(fixture.backend.storage.next_fresh_id()?, 1007);
    assert_eq!(
        fixture.backend.lookup_row(fixture.view, &[Value::new(30)]),
        None
    );
    assert_eq!(
        ids(fixture.backend.lookup_row(fixture.view, &[Value::new(20)])),
        Some(vec![20, 40, 71])
    );
    assert_eq!(
        ids(fixture.backend.lookup_row(fixture.uf, &[Value::new(50)])),
        Some(vec![50, 30, 81])
    );
    assert_eq!(
        ids(fixture.backend.lookup_row(fixture.uf, &[Value::new(40)])),
        Some(vec![40, 20, 82])
    );

    // View orientation: Sym(low payload=71), Trans(high payload=head=1000,
    // sym=1001). UF orientation then symmetrizes the high/incoming payload.
    assert!(
        fixture
            .backend
            .lookup_row(fixture.sym, &[Value::new(71), Value::new(1001)])
            .is_some()
    );
    assert!(
        fixture
            .backend
            .lookup_row(
                fixture.trans,
                &[Value::new(1000), Value::new(1001), Value::new(1002)]
            )
            .is_some()
    );
    assert!(
        fixture
            .backend
            .lookup_row(fixture.sym, &[Value::new(1002), Value::new(1003)])
            .is_some()
    );
    assert!(
        fixture
            .backend
            .lookup_row(
                fixture.trans,
                &[Value::new(1003), Value::new(81), Value::new(1004)]
            )
            .is_some()
    );
    assert!(
        fixture
            .backend
            .lookup_row(fixture.sym, &[Value::new(1004), Value::new(1005)])
            .is_some()
    );
    assert!(
        fixture
            .backend
            .lookup_row(
                fixture.trans,
                &[Value::new(1005), Value::new(82), Value::new(1006)]
            )
            .is_some()
    );
    assert_eq!(fixture.scratch_count()?, 0);
    Ok(())
}

#[test]
fn collision_exhaustion_rolls_back_head_delete_and_counter() -> Result<()> {
    let mut fixture = Fixture::one_id("collision-exhausted")?;
    let rule = fixture.backend.add_rule(fixture.eq_rule(
        "collision-exhausted-rule",
        0,
        BodyOrder::ViewUfNeq,
    ))?;
    let first = u64::from(u32::MAX) - 1;
    fixture.backend.storage.set_next_fresh_id(first)?;
    fixture.insert_ids(fixture.view, &[30, 50, 70], 0, false)?;
    fixture.insert_ids(fixture.view, &[20, 40, 71], 0, false)?;
    fixture.insert_ids(fixture.uf, &[30, 20, 80], 0, false)?;
    let generation = fixture.backend.storage.generation()?;

    let error = fixture.run(&[rule]).unwrap_err();
    assert!(error.to_string().contains("usable Value domain"));
    assert_eq!(fixture.backend.storage.next_fresh_id()?, first);
    assert_eq!(fixture.backend.storage.generation()?, generation);
    assert_eq!(
        ids(fixture.backend.lookup_row(fixture.view, &[Value::new(30)])),
        Some(vec![30, 50, 70])
    );
    assert_eq!(
        ids(fixture.backend.lookup_row(fixture.view, &[Value::new(20)])),
        Some(vec![20, 40, 71])
    );
    assert_eq!(fixture.backend.table_size(fixture.congr), 0);
    assert_eq!(fixture.scratch_count()?, 0);
    Ok(())
}
