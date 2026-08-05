//! General lowering for scalar rule bodies and action streams.
//!
//! Admission records one closed, typed Design-B SQL plan. DuckDB materializes
//! matches, lookups, fresh slots, generic merge programs, and effects; Rust
//! only schedules statements and observes scalar counts.

use std::collections::{BTreeMap, BTreeSet};

use crate::AuthorityRegistries;
use crate::merge_program::{MergeOpKind, MergePrimitive};
use crate::scalar_expr::{ScalarAuthority, ScalarExpression};
use crate::storage::{ScalarSqlType, Storage, TableInfo, WriteCapability, sql_table};
use anyhow::{Context, Result, anyhow, bail, ensure};
use egglog_ast::core::{GenericAtomTerm, GenericCoreAction};
use egglog_ast::generic_ast::Change;
use egglog_backend_trait::{
    BaseValues, ColumnTy, DefaultVal, ExternalFunctionId, FunctionId, NativePrimitive,
    NativeScalarPrimitive, ReadMode, RuleActionCall, RuleBodyCall, RuleSpec, RuleValue, RuleVar,
};
use egglog_numeric_id::NumericId;

/// Backend-minted authority for proof FD operations. The primitive's display
/// name is diagnostic only; admission resolves this descriptor's exact table
/// name once and retains the resulting FunctionId in the immutable plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum FdDescriptor {
    SetIfEmpty {
        view_name: String,
        n_keys: usize,
        out_arity: usize,
    },
    ViewColumnRead {
        view_name: String,
        n_keys: usize,
        col_idx: usize,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ScalarLiteral {
    value: RuleValue,
    scalar: ScalarSqlType,
    sql: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ScalarValueRef {
    Body(usize),
    Slot(usize),
    Literal(ScalarLiteral),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ScalarEffectKind {
    AssertEq,
    KeepOld,
    GenericMerge,
    Delete,
    Subsume,
}

#[derive(Clone, Debug)]
pub(crate) struct ScalarEffectPlan {
    pub(crate) event_ordinal: u64,
    pub(crate) target: FunctionId,
    pub(crate) arity: usize,
    pub(crate) n_keys: usize,
    pub(crate) kind: ScalarEffectKind,
    arguments: Vec<ScalarValueRef>,
    values: Vec<ScalarValueRef>,
    condition_slot: Option<usize>,
}

#[derive(Clone)]
struct BoundValue {
    ty: ColumnTy,
    value: ScalarValueRef,
}

fn argument_ty(term: &GenericAtomTerm<RuleVar, RuleValue>) -> ColumnTy {
    match term {
        GenericAtomTerm::Var(_, variable) => variable.ty,
        GenericAtomTerm::Literal(_, literal) => literal.ty,
        GenericAtomTerm::Global(_, global) => global.ty,
    }
}

fn assert_scratch_name(name: &str) {
    debug_assert!(
        name.bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
    );
}

// -------------------------------------------------------------------------
// General scalar action-stream lowering.

#[derive(Clone, Debug)]
enum ScalarActionRead {
    Table {
        target: FunctionId,
        n_keys: usize,
        result_column: usize,
        keys: Vec<ScalarValueRef>,
    },
    SetIfEmpty {
        target: FunctionId,
        n_keys: usize,
        keys: Vec<ScalarValueRef>,
        defaults: Vec<ScalarValueRef>,
    },
    ViewColumn {
        target: FunctionId,
        n_keys: usize,
        result_column: usize,
        keys: Vec<ScalarValueRef>,
        fallback: ScalarValueRef,
    },
}

#[derive(Clone, Debug)]
enum ScalarActionSlotSource {
    Fresh {
        rank: u64,
    },
    Read(ScalarActionRead),
    Expression {
        expression: ScalarExpression,
        inputs: Vec<ScalarValueRef>,
    },
}

#[derive(Clone, Debug)]
pub(crate) struct ScalarActionSlot {
    raw_action_ordinal: usize,
    runtime_ordinal: u64,
    ty: ColumnTy,
    source: ScalarActionSlotSource,
}

/// A closed typed scalar program. Rows remain in DuckDB scratch relations;
/// Rust retains only immutable schema-level expressions and scheduling data.
#[derive(Clone, Debug)]
pub(crate) struct ScalarActionPlan {
    seminaive: bool,
    match_projection: Vec<String>,
    match_from: Vec<String>,
    match_predicates: Vec<String>,
    freshness_columns: Vec<String>,
    order_columns: Vec<String>,
    slots: Vec<ScalarActionSlot>,
    effects: Vec<ScalarEffectPlan>,
    fresh_slots: u64,
    action_count: u64,
    required_fresh_tokens: BTreeSet<ExternalFunctionId>,
    required_fd_descriptors: BTreeMap<ExternalFunctionId, FdDescriptor>,
    required_native_primitives: BTreeMap<ExternalFunctionId, NativePrimitive>,
    required_native_scalar_primitives: BTreeMap<ExternalFunctionId, NativeScalarPrimitive>,
    required_authority_epochs: BTreeMap<ExternalFunctionId, u64>,
}

impl ScalarActionPlan {
    pub(crate) fn authorize(
        &self,
        native_primitives: &BTreeMap<ExternalFunctionId, NativePrimitive>,
        native_scalar_primitives: &BTreeMap<ExternalFunctionId, NativeScalarPrimitive>,
        authority_epochs: &BTreeMap<ExternalFunctionId, u64>,
        fresh_tokens: &BTreeSet<ExternalFunctionId>,
        fd_descriptors: &BTreeMap<ExternalFunctionId, FdDescriptor>,
    ) -> Result<()> {
        for (token, descriptor) in &self.required_native_primitives {
            ensure!(
                native_primitives.get(token) == Some(descriptor),
                "DuckDB scalar action plan references a freed or reused native token {}",
                token.rep()
            );
        }
        for (token, descriptor) in &self.required_native_scalar_primitives {
            ensure!(
                native_scalar_primitives.get(token) == Some(descriptor),
                "DuckDB scalar action plan references a freed or reused native scalar token {}",
                token.rep()
            );
        }
        for token in &self.required_fresh_tokens {
            ensure!(
                fresh_tokens.contains(token),
                "DuckDB scalar action plan references a freed or reused get-fresh token {}",
                token.rep()
            );
        }
        for (token, descriptor) in &self.required_fd_descriptors {
            ensure!(
                fd_descriptors.get(token) == Some(descriptor),
                "DuckDB scalar action plan references a freed or reused FD token {}",
                token.rep()
            );
        }
        // Descriptor/kind diagnostics stay specific. The epoch is the final
        // ABA guard when a token is freed and reused with the same authority.
        for (token, epoch) in &self.required_authority_epochs {
            ensure!(
                authority_epochs.get(token) == Some(epoch),
                "DuckDB scalar action plan references a freed or reused authority token {}",
                token.rep()
            );
        }
        Ok(())
    }

    pub(crate) fn fresh_slots(&self) -> u64 {
        self.fresh_slots
    }

    pub(crate) fn action_count(&self) -> u64 {
        self.action_count
    }

    pub(crate) fn slots(&self) -> &[ScalarActionSlot] {
        &self.slots
    }

    pub(crate) fn prediction_targets(&self) -> BTreeSet<FunctionId> {
        self.slots
            .iter()
            .filter_map(|slot| match slot.source {
                ScalarActionSlotSource::Read(ScalarActionRead::SetIfEmpty { target, .. }) => {
                    Some(target)
                }
                _ => None,
            })
            .collect()
    }

    pub(crate) fn set_if_empty_target(&self, slot_index: usize) -> Option<FunctionId> {
        match self.slots[slot_index].source {
            ScalarActionSlotSource::Read(ScalarActionRead::SetIfEmpty { target, .. }) => {
                Some(target)
            }
            _ => None,
        }
    }

    pub(crate) fn effects(&self) -> &[ScalarEffectPlan] {
        &self.effects
    }

    pub(crate) fn owner_checks(&self) -> Vec<(FunctionId, usize, bool)> {
        let mut checks = Vec::new();
        for slot in &self.slots {
            match &slot.source {
                ScalarActionSlotSource::Read(read) => {
                    let (target, n_keys) = match read {
                        ScalarActionRead::Table { target, n_keys, .. }
                        | ScalarActionRead::SetIfEmpty { target, n_keys, .. }
                        | ScalarActionRead::ViewColumn { target, n_keys, .. } => (*target, *n_keys),
                    };
                    checks.push((target, n_keys, false));
                }
                ScalarActionSlotSource::Fresh { .. }
                | ScalarActionSlotSource::Expression { .. } => {}
            }
        }
        checks.extend(
            self.effects
                .iter()
                .map(|effect| (effect.target, effect.n_keys, false)),
        );
        checks
    }

    pub(crate) fn materialize_match_sql(&self, stage: &str, watermark: u64) -> String {
        assert_scratch_name(stage);
        if self.match_from.is_empty() {
            let run = !self.seminaive || watermark == 0;
            let mut predicates = self.match_predicates.clone();
            predicates.push(if run { "TRUE" } else { "FALSE" }.to_string());
            let mut projection = self
                .match_projection
                .iter()
                .enumerate()
                .map(|(column, expression)| format!("{expression} AS b{column}"))
                .collect::<Vec<_>>();
            projection.push("CAST('1' AS UBIGINT) AS __match_ordinal".to_string());
            return format!(
                "CREATE TEMP TABLE {stage} AS
                 SELECT {}
                 WHERE {}",
                projection.join(", "),
                predicates.join(" AND ")
            );
        }

        let mut predicates = self.match_predicates.clone();
        if self.seminaive {
            predicates.push(format!(
                "({})",
                self.freshness_columns
                    .iter()
                    .map(|column| format!("{column} >= CAST('{watermark}' AS UBIGINT)"))
                    .collect::<Vec<_>>()
                    .join(" OR ")
            ));
        }
        let mut projection = self
            .match_projection
            .iter()
            .enumerate()
            .map(|(column, expression)| format!("{expression} AS b{column}"))
            .collect::<Vec<_>>();
        projection.push(format!(
            "row_number() OVER (ORDER BY {}) AS __match_ordinal",
            self.order_columns.join(", ")
        ));
        format!(
            "CREATE TEMP TABLE {stage} AS
             SELECT {}
             FROM {}
             WHERE {}",
            projection.join(", "),
            self.match_from.join(" CROSS JOIN "),
            predicates.join(" AND ")
        )
    }

    pub(crate) fn materialize_slot_sql(
        &self,
        input_stage: &str,
        output_stage: &str,
        slot_index: usize,
        first_fresh: u64,
        match_count: u64,
        prediction_ledger: Option<&str>,
    ) -> String {
        assert_scratch_name(input_stage);
        assert_scratch_name(output_stage);
        let slot = &self.slots[slot_index];
        match &slot.source {
            ScalarActionSlotSource::Fresh { rank, .. } => format!(
                "CREATE TEMP TABLE {output_stage} AS
                 SELECT prior.*,
                        CAST('{first_fresh}' AS UBIGINT)
                            + CAST('{rank}' AS UBIGINT) * CAST('{match_count}' AS UBIGINT)
                            + prior.__match_ordinal - 1 AS s{slot_index}
                 FROM {input_stage} AS prior"
            ),
            ScalarActionSlotSource::Expression { expression, inputs } => {
                let inputs = inputs
                    .iter()
                    .map(|input| render_general_ref(input, "prior"))
                    .collect::<Vec<_>>();
                let rendered = expression.render(&inputs);
                format!(
                    "CREATE TEMP TABLE {output_stage} AS
                     SELECT prior.*, {} AS s{slot_index}
                     FROM {input_stage} AS prior",
                    rendered.value
                )
            }
            ScalarActionSlotSource::Read(ScalarActionRead::Table {
                target,
                n_keys,
                result_column,
                keys,
            }) => {
                debug_assert_eq!(keys.len(), *n_keys);
                let equality = render_read_equality(keys, *n_keys, "prior");
                format!(
                    "CREATE TEMP TABLE {output_stage} AS
                     SELECT prior.*,
                            existing.c{result_column} AS s{slot_index}
                     FROM {input_stage} AS prior
                     JOIN {} AS existing ON {equality}",
                    sql_table(*target)
                )
            }
            ScalarActionSlotSource::Read(ScalarActionRead::SetIfEmpty {
                target,
                n_keys,
                keys,
                ..
            }) => {
                let ledger = prediction_ledger.expect("SetIfEmpty requires a prediction ledger");
                assert_scratch_name(ledger);
                let durable_equality = render_read_equality(keys, *n_keys, "prior");
                let ledger_equality =
                    render_scratch_key_equality(keys, *n_keys, "predicted", "prior");
                format!(
                    "CREATE TEMP TABLE {output_stage} AS
                     SELECT prior.*,
                            choice.__value AS s{slot_index}
                     FROM {input_stage} AS prior
                     JOIN LATERAL (
                         SELECT alternatives.__value
                         FROM (
                             SELECT existing.c{n_keys} AS __value,
                                    CAST('0' AS UTINYINT) AS __source
                             FROM {} AS existing
                             WHERE {durable_equality}
                             UNION ALL
                             SELECT predicted.c{n_keys} AS __value,
                                    CAST('1' AS UTINYINT) AS __source
                             FROM {ledger} AS predicted
                             WHERE {ledger_equality}
                         ) AS alternatives
                         ORDER BY alternatives.__source
                         LIMIT 1
                     ) AS choice ON TRUE",
                    sql_table(*target),
                )
            }
            ScalarActionSlotSource::Read(ScalarActionRead::ViewColumn {
                target,
                n_keys,
                result_column,
                keys,
                fallback,
            }) => {
                let equality = render_read_equality(keys, *n_keys, "prior");
                format!(
                    "CREATE TEMP TABLE {output_stage} AS
                     SELECT prior.*,
                            choice.__value AS s{slot_index}
                     FROM {input_stage} AS prior
                     JOIN LATERAL (
                         SELECT alternatives.__value
                         FROM (
                             SELECT existing.c{result_column} AS __value,
                                    CAST('0' AS UTINYINT) AS __source
                             FROM {} AS existing
                             WHERE {equality}
                             UNION ALL
                             SELECT {} AS __value,
                                    CAST('1' AS UTINYINT) AS __source
                         ) AS alternatives
                         ORDER BY alternatives.__source
                         LIMIT 1
                     ) AS choice ON TRUE",
                    sql_table(*target),
                    render_general_ref(fallback, "prior"),
                )
            }
        }
    }

    pub(crate) fn materialize_prediction_winner_sql(
        &self,
        input_stage: &str,
        winner_stage: &str,
        ledger: &str,
        slot_index: usize,
        match_count: u64,
        event_offset: u64,
    ) -> Option<String> {
        assert_scratch_name(input_stage);
        assert_scratch_name(winner_stage);
        assert_scratch_name(ledger);
        let slot = &self.slots[slot_index];
        let ScalarActionSlotSource::Read(ScalarActionRead::SetIfEmpty {
            target,
            n_keys,
            keys,
            defaults,
        }) = &slot.source
        else {
            return None;
        };
        let mut projection = keys
            .iter()
            .chain(defaults)
            .enumerate()
            .map(|(column, value)| format!("{} AS c{column}", render_general_ref(value, "prior")))
            .collect::<Vec<_>>();
        projection.push(format!(
            "CAST('{event_offset}' AS UBIGINT)
             + CAST('{}' AS UBIGINT) * CAST('{match_count}' AS UBIGINT)
             + prior.__match_ordinal AS __event",
            slot.runtime_ordinal
        ));
        let partition = if *n_keys == 0 {
            String::new()
        } else {
            format!(
                "PARTITION BY {} ",
                keys.iter()
                    .map(|key| render_general_ref(key, "prior"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        projection.push(format!(
            "row_number() OVER ({partition}ORDER BY prior.__match_ordinal) AS __site_rank"
        ));
        let durable_equality = render_row_key_equality(*n_keys, "existing", "candidate");
        let ledger_equality = render_row_key_equality(*n_keys, "predicted", "candidate");
        Some(format!(
            "CREATE TEMP TABLE {winner_stage} AS
             SELECT candidate.* EXCLUDE (__site_rank)
             FROM (
                 SELECT {}
                 FROM {input_stage} AS prior
             ) AS candidate
             WHERE candidate.__site_rank = 1
               AND NOT EXISTS (
                   SELECT 1 FROM {} AS existing WHERE {durable_equality}
               )
               AND NOT EXISTS (
                   SELECT 1 FROM {ledger} AS predicted WHERE {ledger_equality}
               )",
            projection.join(", "),
            sql_table(*target),
        ))
    }

    pub(crate) fn prediction_effect_slot(&self, effect: &ScalarEffectPlan) -> Option<usize> {
        effect.condition_slot.filter(|&slot| {
            matches!(
                self.slots[slot].source,
                ScalarActionSlotSource::Read(ScalarActionRead::SetIfEmpty { .. })
            )
        })
    }

    pub(crate) fn materialize_prediction_effect_sql(
        &self,
        winner_stage: &str,
        effect_stage: &str,
        effect: &ScalarEffectPlan,
    ) -> String {
        assert_scratch_name(winner_stage);
        assert_scratch_name(effect_stage);
        let projection = (0..effect.arity)
            .map(|column| format!("winner.c{column}"))
            .chain(std::iter::once("winner.__event AS __ordinal".to_string()))
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            "CREATE TEMP TABLE {effect_stage} AS
             SELECT {projection}
             FROM {winner_stage} AS winner
             ORDER BY winner.__event"
        )
    }

    /// Fail lookups validate every input lane against the durable pre-wave
    /// table before a result-bearing scratch relation can be created.
    pub(crate) fn slot_preflight_sql(
        &self,
        input_stage: &str,
        slot_index: usize,
    ) -> Option<String> {
        assert_scratch_name(input_stage);
        match &self.slots[slot_index].source {
            ScalarActionSlotSource::Read(ScalarActionRead::Table {
                target,
                n_keys,
                keys,
                ..
            }) => {
                debug_assert_eq!(keys.len(), *n_keys);
                let equality = render_read_equality(keys, *n_keys, "prior");
                Some(format!(
                    "SELECT EXISTS (
                         SELECT 1
                         FROM {input_stage} AS prior
                         LEFT JOIN LATERAL (
                             SELECT count(existing.__generation) AS __owners
                             FROM {} AS existing
                             WHERE {equality}
                         ) AS lookup ON TRUE
                         WHERE lookup.__owners <> 1
                     )",
                    sql_table(*target)
                ))
            }
            ScalarActionSlotSource::Expression { expression, inputs } => {
                let inputs = inputs
                    .iter()
                    .map(|input| render_general_ref(input, "prior"))
                    .collect::<Vec<_>>();
                let rendered = expression.render(&inputs);
                (!rendered.is_total()).then(|| {
                    format!(
                        "SELECT EXISTS (SELECT 1 FROM {input_stage} AS prior WHERE NOT ({}))",
                        rendered.defined
                    )
                })
            }
            ScalarActionSlotSource::Fresh { .. }
            | ScalarActionSlotSource::Read(
                ScalarActionRead::SetIfEmpty { .. } | ScalarActionRead::ViewColumn { .. },
            ) => None,
        }
    }

    pub(crate) fn slot_invalid_sql(&self, stage: &str, slot_index: usize) -> Option<String> {
        assert_scratch_name(stage);
        let _ = slot_index;
        None
    }

    pub(crate) fn slot_error(&self, slot_index: usize) -> String {
        let slot = &self.slots[slot_index];
        match &slot.source {
            ScalarActionSlotSource::Read(ScalarActionRead::Table { target, .. }) => format!(
                "DuckDB scalar action {} (runtime {}, result {:?}) Fail lookup for function {} did not have exactly one pre-wave owner",
                slot.raw_action_ordinal,
                slot.runtime_ordinal,
                slot.ty,
                target.rep()
            ),
            ScalarActionSlotSource::Read(_) => format!(
                "DuckDB scalar action {} (runtime {}, result {:?}) has duplicate durable pre-wave owners",
                slot.raw_action_ordinal, slot.runtime_ordinal, slot.ty
            ),
            ScalarActionSlotSource::Fresh { .. } => {
                unreachable!("fresh slots have no ownership check")
            }
            ScalarActionSlotSource::Expression { expression, .. } => format!(
                "DuckDB scalar action {} (runtime {}, result {:?}) evaluated undefined for authenticated token {}",
                slot.raw_action_ordinal,
                slot.runtime_ordinal,
                slot.ty,
                expression.token().rep()
            ),
        }
    }

    pub(crate) fn materialize_effect_sql(
        &self,
        head_stage: &str,
        effect_stage: &str,
        effect: &ScalarEffectPlan,
        first_event: u64,
    ) -> String {
        assert_scratch_name(head_stage);
        assert_scratch_name(effect_stage);
        let mut projection = effect
            .arguments
            .iter()
            .chain(&effect.values)
            .enumerate()
            .map(|(column, value)| format!("{} AS c{column}", render_general_ref(value, "head")))
            .collect::<Vec<_>>();
        projection.push(format!(
            "CAST('{first_event}' AS UBIGINT) + head.__match_ordinal - 1 AS __ordinal"
        ));
        let predicate = effect
            .condition_slot
            .map_or("TRUE".to_string(), |slot| format!("head.__missing_s{slot}"));
        format!(
            "CREATE TEMP TABLE {effect_stage} AS
             SELECT {}
             FROM {head_stage} AS head
             WHERE {predicate}
             ORDER BY head.__match_ordinal",
            projection.join(", ")
        )
    }
}

#[derive(Clone)]
struct ScalarBodyBinding {
    ty: ColumnTy,
    expression: String,
    stage_column: usize,
}

struct ScalarBodyPlan {
    match_projection: Vec<String>,
    match_from: Vec<String>,
    match_predicates: Vec<String>,
    freshness_columns: Vec<String>,
    order_columns: Vec<String>,
    bindings: BTreeMap<u32, ScalarBodyBinding>,
    rows: Vec<(FunctionId, Vec<ScalarValueRef>)>,
    required_native_primitives: BTreeMap<ExternalFunctionId, NativePrimitive>,
    required_native_scalar_primitives: BTreeMap<ExternalFunctionId, NativeScalarPrimitive>,
}

fn compile_scalar_body(
    storage: &Storage,
    base_values: &BaseValues,
    native_primitives: &BTreeMap<ExternalFunctionId, NativePrimitive>,
    native_scalar_primitives: &BTreeMap<ExternalFunctionId, NativeScalarPrimitive>,
    rule: &RuleSpec,
) -> Result<ScalarBodyPlan> {
    let mut plan = ScalarBodyPlan {
        match_projection: Vec::new(),
        match_from: Vec::new(),
        match_predicates: Vec::new(),
        freshness_columns: Vec::new(),
        order_columns: Vec::new(),
        bindings: BTreeMap::new(),
        rows: Vec::new(),
        required_native_primitives: BTreeMap::new(),
        required_native_scalar_primitives: BTreeMap::new(),
    };

    // Row variables bind independently of source atom order. Ordinary table
    // rows seed reachability; occurrence rows then bind to a fixed point once
    // their probe is literal, already bound, or repeated at an indexed column.
    for (atom_index, atom) in rule.core.body.atoms.iter().enumerate() {
        if let RuleBodyCall::Table { id, .. } = atom.head {
            let info = storage.table_info(id)?;
            ensure!(
                atom.args.len() == info.arity(),
                "DuckDB scalar rule `{}` body table has the wrong arity",
                rule.name
            );
            prebind_scalar_row(&rule.name, &mut plan, &atom.args, &info.schema, atom_index)?;
        }
    }
    let mut admitted_indices = BTreeSet::new();
    loop {
        let mut changed = false;
        for (atom_index, atom) in rule.core.body.atoms.iter().enumerate() {
            let RuleBodyCall::IndexTable { id, any_of, .. } = &atom.head else {
                continue;
            };
            if admitted_indices.contains(&atom_index) {
                continue;
            }
            let info = storage.table_info(*id)?;
            let any_of = any_of.iter().copied().collect::<BTreeSet<_>>();
            let (probe, rest) = atom.args.split_first().context("index atom has no probe")?;
            let (_output, row) = rest.split_last().context("index atom has no Unit output")?;
            ensure!(
                row.len() == info.arity(),
                "DuckDB scalar rule `{}` index row has the wrong arity",
                rule.name
            );
            ensure!(
                !any_of.is_empty() && any_of.iter().all(|column| *column < info.arity()),
                "DuckDB scalar rule `{}` index has invalid occurrence columns",
                rule.name
            );
            let bind_column = match probe {
                GenericAtomTerm::Literal(..) => None,
                GenericAtomTerm::Var(_, variable) => {
                    if plan
                        .bindings
                        .get(&variable.id)
                        .is_some_and(|binding| binding.ty == variable.ty)
                    {
                        None
                    } else {
                        row.iter().enumerate().find_map(|(column, term)| {
                            matches!(term, GenericAtomTerm::Var(_, row_var) if row_var.id == variable.id && row_var.ty == variable.ty && any_of.contains(&column))
                                .then_some(column)
                        }).or_else(|| (any_of.len() == 1).then(|| *any_of.first().unwrap()))
                    }
                }
                GenericAtomTerm::Global(..) => continue,
            };
            let ready = matches!(probe, GenericAtomTerm::Literal(..))
                || matches!(probe, GenericAtomTerm::Var(_, variable) if plan.bindings.get(&variable.id).is_some_and(|binding| binding.ty == variable.ty))
                || bind_column.is_some();
            if ready {
                if let GenericAtomTerm::Var(_, variable) = probe
                    && !plan.bindings.contains_key(&variable.id)
                {
                    let column = bind_column.expect("unbound admitted probe has a binding column");
                    prebind_scalar_variable(
                        &rule.name,
                        &mut plan,
                        variable,
                        info.schema[column],
                        format!("b{atom_index}.c{column}"),
                    )?;
                }
                prebind_scalar_row(&rule.name, &mut plan, row, &info.schema, atom_index)?;
                admitted_indices.insert(atom_index);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    ensure!(
        rule.core
            .body
            .atoms
            .iter()
            .enumerate()
            .all(
                |(index, atom)| !matches!(atom.head, RuleBodyCall::IndexTable { .. })
                    || admitted_indices.contains(&index)
            ),
        "DuckDB scalar rule `{}` contains an unreachable occurrence probe",
        rule.name
    );

    for (atom_index, atom) in rule.core.body.atoms.iter().enumerate() {
        match &atom.head {
            RuleBodyCall::Table { id, read } => {
                let info = storage.table_info(*id).with_context(|| {
                    format!(
                        "DuckDB scalar rule `{}` references invalid body table {}",
                        rule.name,
                        id.rep()
                    )
                })?;
                ensure!(
                    atom.args.len() == info.arity(),
                    "DuckDB scalar rule `{}` body table `{}` expects {} arguments, got {}",
                    rule.name,
                    info.name,
                    info.arity(),
                    atom.args.len()
                );
                let alias = format!("b{atom_index}");
                plan.match_from
                    .push(format!("{} AS {alias}", sql_table(*id)));
                match read {
                    ReadMode::Live => plan
                        .match_predicates
                        .push(format!("{alias}.__subsumed = FALSE")),
                    ReadMode::Subsumed => plan
                        .match_predicates
                        .push(format!("{alias}.__subsumed = TRUE")),
                    ReadMode::All => {}
                }
                plan.freshness_columns.push(format!("{alias}.__generation"));
                plan.order_columns.push(format!("{alias}.__generation"));
                plan.order_columns
                    .extend((0..info.arity()).map(|column| format!("{alias}.c{column}")));

                for (column, (term, &expected)) in atom.args.iter().zip(&info.schema).enumerate() {
                    let expression = format!("{alias}.c{column}");
                    match term {
                        GenericAtomTerm::Var(_, variable) => {
                            ensure!(
                                variable.ty == expected,
                                "DuckDB scalar rule `{}` table variable `{}` has the wrong type",
                                rule.name,
                                variable.name
                            );
                            if let Some(binding) = plan.bindings.get(&variable.id) {
                                ensure_body_metadata(&rule.name, variable, binding)?;
                                plan.match_predicates.push(format!(
                                    "{expression} IS NOT DISTINCT FROM {}",
                                    binding.expression
                                ));
                            } else {
                                let stage_column = plan.match_projection.len();
                                plan.match_projection.push(expression.clone());
                                plan.bindings.insert(
                                    variable.id,
                                    ScalarBodyBinding {
                                        ty: variable.ty,
                                        expression,
                                        stage_column,
                                    },
                                );
                            }
                        }
                        GenericAtomTerm::Literal(_, literal) => {
                            ensure!(
                                literal.ty == expected,
                                "DuckDB scalar rule `{}` has a mistyped body literal",
                                rule.name
                            );
                            let literal = ScalarSqlType::from_column(base_values, expected)?
                                .sql_literal(base_values, literal.value)?;
                            plan.match_predicates
                                .push(format!("{expression} IS NOT DISTINCT FROM {literal}"));
                        }
                        GenericAtomTerm::Global(..) => bail!(
                            "DuckDB scalar rule `{}` contains an unsupported body global",
                            rule.name
                        ),
                    }
                }
                plan.rows.push((
                    *id,
                    atom.args
                        .iter()
                        .zip(&info.schema)
                        .map(|(term, &ty)| {
                            scalar_body_ref(base_values, &rule.name, &plan.bindings, term, ty)
                        })
                        .collect::<Result<Vec<_>>>()?,
                ));
            }
            RuleBodyCall::IndexTable { id, any_of, read } => {
                let info = storage.table_info(*id)?;
                let any_of = any_of.iter().copied().collect::<BTreeSet<_>>();
                ensure!(
                    !any_of.is_empty(),
                    "DuckDB scalar rule `{}` index lists no occurrence columns",
                    rule.name
                );
                ensure!(
                    any_of.iter().all(|column| *column < info.arity()),
                    "DuckDB scalar rule `{}` index has an out-of-range occurrence column",
                    rule.name
                );
                let (probe, rest) = atom.args.split_first().context("index atom has no probe")?;
                let (output, row) = rest.split_last().context("index atom has no Unit output")?;
                ensure!(
                    row.len() == info.arity(),
                    "DuckDB scalar rule `{}` index row has the wrong arity",
                    rule.name
                );
                let unit_ty = ColumnTy::Base(base_values.get_ty::<()>());
                let GenericAtomTerm::Literal(_, output) = output else {
                    bail!(
                        "DuckDB scalar rule `{}` index output must be canonical Unit",
                        rule.name
                    )
                };
                ensure!(
                    output.ty == unit_ty && output.value == base_values.get(()),
                    "DuckDB scalar rule `{}` index output must be canonical Unit",
                    rule.name
                );
                let probe_ty = argument_ty(probe);
                for &column in &any_of {
                    ensure!(
                        info.schema[column] == probe_ty,
                        "DuckDB scalar rule `{}` index probe type disagrees with occurrence column {column}",
                        rule.name
                    );
                }
                let probe = compile_scalar_body_term(
                    base_values,
                    &rule.name,
                    &plan.bindings,
                    probe,
                    probe_ty,
                    "index probe",
                )?;
                let alias = format!("b{atom_index}");
                plan.match_from
                    .push(format!("{} AS {alias}", sql_table(*id)));
                match read {
                    ReadMode::Live => plan
                        .match_predicates
                        .push(format!("{alias}.__subsumed = FALSE")),
                    ReadMode::Subsumed => plan
                        .match_predicates
                        .push(format!("{alias}.__subsumed = TRUE")),
                    ReadMode::All => {}
                }
                plan.match_predicates.push(format!(
                    "({})",
                    any_of
                        .iter()
                        .map(|column| format!("{alias}.c{column} IS NOT DISTINCT FROM {probe}"))
                        .collect::<Vec<_>>()
                        .join(" OR ")
                ));
                plan.freshness_columns.push(format!("{alias}.__generation"));
                plan.order_columns.push(format!("{alias}.__generation"));
                plan.order_columns
                    .extend((0..info.arity()).map(|column| format!("{alias}.c{column}")));
                for (column, (term, &expected)) in row.iter().zip(&info.schema).enumerate() {
                    bind_scalar_body_term(
                        base_values,
                        &rule.name,
                        &mut plan,
                        term,
                        expected,
                        format!("{alias}.c{column}"),
                    )?;
                }
                plan.rows.push((
                    *id,
                    row.iter()
                        .zip(&info.schema)
                        .map(|(term, &ty)| {
                            scalar_body_ref(base_values, &rule.name, &plan.bindings, term, ty)
                        })
                        .collect::<Result<Vec<_>>>()?,
                ));
            }
            RuleBodyCall::Primitive {
                id,
                name: _,
                output,
                ..
            } => {
                let Some((result, inputs)) = atom.args.split_last() else {
                    bail!(
                        "DuckDB scalar rule `{}` primitive body atom has no output term",
                        rule.name
                    );
                };
                let input_tys = inputs.iter().map(argument_ty).collect::<Vec<_>>();
                let expression = ScalarExpression::authenticate(
                    base_values,
                    native_primitives,
                    native_scalar_primitives,
                    *id,
                    &input_tys,
                    *output,
                )
                .with_context(|| {
                    format!(
                        "DuckDB scalar rule `{}` has an invalid primitive body atom",
                        rule.name
                    )
                })?;
                let inputs = inputs
                    .iter()
                    .zip(input_tys)
                    .map(|(term, ty)| {
                        compile_scalar_body_term(
                            base_values,
                            &rule.name,
                            &plan.bindings,
                            term,
                            ty,
                            "primitive input",
                        )
                    })
                    .collect::<Result<Vec<_>>>()?;
                let rendered = expression.render(&inputs);
                if !rendered.is_total() {
                    plan.match_predicates.push(rendered.defined);
                }
                match result {
                    GenericAtomTerm::Var(_, variable) => {
                        ensure!(
                            variable.ty == *output,
                            "DuckDB scalar rule `{}` primitive output variable has the wrong type",
                            rule.name
                        );
                        if let Some(binding) = plan.bindings.get(&variable.id) {
                            ensure_body_metadata(&rule.name, variable, binding)?;
                            plan.match_predicates.push(format!(
                                "{} IS NOT DISTINCT FROM {}",
                                rendered.value, binding.expression
                            ));
                        } else {
                            let stage_column = plan.match_projection.len();
                            plan.match_projection.push(rendered.value.clone());
                            plan.bindings.insert(
                                variable.id,
                                ScalarBodyBinding {
                                    ty: variable.ty,
                                    expression: rendered.value,
                                    stage_column,
                                },
                            );
                        }
                    }
                    GenericAtomTerm::Literal(_, literal) => {
                        ensure!(
                            literal.ty == *output,
                            "DuckDB scalar rule `{}` primitive output literal has the wrong type",
                            rule.name
                        );
                        let literal = ScalarSqlType::from_column(base_values, *output)?
                            .sql_literal(base_values, literal.value)?;
                        plan.match_predicates
                            .push(format!("{} IS NOT DISTINCT FROM {literal}", rendered.value));
                    }
                    GenericAtomTerm::Global(..) => bail!(
                        "DuckDB scalar rule `{}` primitive output cannot be a global",
                        rule.name
                    ),
                }
                match expression.authority() {
                    ScalarAuthority::Native(descriptor) => {
                        plan.required_native_primitives.insert(*id, descriptor);
                    }
                    ScalarAuthority::Typed(descriptor) => {
                        plan.required_native_scalar_primitives
                            .insert(*id, descriptor);
                    }
                }
            }
        }
    }
    Ok(plan)
}

fn prebind_scalar_row(
    rule_name: &str,
    plan: &mut ScalarBodyPlan,
    row: &[GenericAtomTerm<RuleVar, RuleValue>],
    schema: &[ColumnTy],
    atom_index: usize,
) -> Result<()> {
    for (column, (term, &expected)) in row.iter().zip(schema).enumerate() {
        if let GenericAtomTerm::Var(_, variable) = term {
            prebind_scalar_variable(
                rule_name,
                plan,
                variable,
                expected,
                format!("b{atom_index}.c{column}"),
            )?;
        }
    }
    Ok(())
}

fn prebind_scalar_variable(
    rule_name: &str,
    plan: &mut ScalarBodyPlan,
    variable: &RuleVar,
    expected: ColumnTy,
    expression: String,
) -> Result<()> {
    ensure!(
        variable.ty == expected,
        "DuckDB scalar rule `{rule_name}` body variable has the wrong type"
    );
    if let Some(binding) = plan.bindings.get(&variable.id) {
        return ensure_body_metadata(rule_name, variable, binding);
    }
    let stage_column = plan.match_projection.len();
    plan.match_projection.push(expression.clone());
    plan.bindings.insert(
        variable.id,
        ScalarBodyBinding {
            ty: variable.ty,
            expression,
            stage_column,
        },
    );
    Ok(())
}

fn ensure_body_metadata(
    rule_name: &str,
    variable: &RuleVar,
    binding: &ScalarBodyBinding,
) -> Result<()> {
    ensure!(
        binding.ty == variable.ty,
        "DuckDB scalar rule `{rule_name}` reuses variable id {} with inconsistent type metadata",
        variable.id
    );
    Ok(())
}

fn bind_scalar_body_term(
    base_values: &BaseValues,
    rule_name: &str,
    plan: &mut ScalarBodyPlan,
    term: &GenericAtomTerm<RuleVar, RuleValue>,
    expected: ColumnTy,
    expression: String,
) -> Result<()> {
    match term {
        GenericAtomTerm::Var(_, variable) => {
            ensure!(
                variable.ty == expected,
                "DuckDB scalar rule `{rule_name}` body variable has the wrong type"
            );
            if let Some(binding) = plan.bindings.get(&variable.id) {
                ensure_body_metadata(rule_name, variable, binding)?;
                plan.match_predicates.push(format!(
                    "{expression} IS NOT DISTINCT FROM {}",
                    binding.expression
                ));
            } else {
                let stage_column = plan.match_projection.len();
                plan.match_projection.push(expression.clone());
                plan.bindings.insert(
                    variable.id,
                    ScalarBodyBinding {
                        ty: variable.ty,
                        expression,
                        stage_column,
                    },
                );
            }
        }
        GenericAtomTerm::Literal(_, literal) => {
            ensure!(
                literal.ty == expected,
                "DuckDB scalar rule `{rule_name}` has a mistyped body literal"
            );
            let literal = ScalarSqlType::from_column(base_values, expected)?
                .sql_literal(base_values, literal.value)?;
            plan.match_predicates
                .push(format!("{expression} IS NOT DISTINCT FROM {literal}"));
        }
        GenericAtomTerm::Global(..) => {
            bail!("DuckDB scalar rule `{rule_name}` contains an unsupported body global")
        }
    }
    Ok(())
}

fn scalar_body_ref(
    base_values: &BaseValues,
    rule_name: &str,
    bindings: &BTreeMap<u32, ScalarBodyBinding>,
    term: &GenericAtomTerm<RuleVar, RuleValue>,
    expected: ColumnTy,
) -> Result<ScalarValueRef> {
    match term {
        GenericAtomTerm::Var(_, variable) => {
            ensure!(
                variable.ty == expected,
                "DuckDB scalar rule `{rule_name}` body row has a mistyped variable"
            );
            let binding = bindings.get(&variable.id).ok_or_else(|| {
                anyhow!("DuckDB scalar rule `{rule_name}` body row uses an unbound variable")
            })?;
            ensure_body_metadata(rule_name, variable, binding)?;
            Ok(ScalarValueRef::Body(binding.stage_column))
        }
        GenericAtomTerm::Literal(_, literal) => {
            ensure!(
                literal.ty == expected,
                "DuckDB scalar rule `{rule_name}` body row has a mistyped literal"
            );
            let scalar = ScalarSqlType::from_column(base_values, expected)?;
            Ok(ScalarValueRef::Literal(ScalarLiteral {
                value: *literal,
                scalar,
                sql: scalar.sql_literal(base_values, literal.value)?,
            }))
        }
        GenericAtomTerm::Global(..) => {
            bail!("DuckDB scalar rule `{rule_name}` body row contains an unsupported global")
        }
    }
}

fn compile_scalar_body_term(
    base_values: &BaseValues,
    rule_name: &str,
    bindings: &BTreeMap<u32, ScalarBodyBinding>,
    term: &GenericAtomTerm<RuleVar, RuleValue>,
    expected: ColumnTy,
    context: &str,
) -> Result<String> {
    match term {
        GenericAtomTerm::Var(_, variable) => {
            ensure!(
                variable.ty == expected,
                "DuckDB scalar rule `{rule_name}` {context} has a mistyped variable"
            );
            let binding = bindings.get(&variable.id).ok_or_else(|| {
                anyhow!(
                    "DuckDB scalar rule `{rule_name}` {context} uses variable id {} before binding",
                    variable.id
                )
            })?;
            ensure_body_metadata(rule_name, variable, binding)?;
            Ok(binding.expression.clone())
        }
        GenericAtomTerm::Literal(_, literal) => {
            ensure!(
                literal.ty == expected,
                "DuckDB scalar rule `{rule_name}` {context} has a mistyped literal"
            );
            ScalarSqlType::from_column(base_values, expected)?
                .sql_literal(base_values, literal.value)
        }
        GenericAtomTerm::Global(..) => {
            bail!("DuckDB scalar rule `{rule_name}` {context} contains an unsupported global")
        }
    }
}

struct GeneralScalarCompiler<'a> {
    storage: &'a Storage,
    base_values: &'a BaseValues,
    native_primitives: &'a BTreeMap<ExternalFunctionId, NativePrimitive>,
    native_scalar_primitives: &'a BTreeMap<ExternalFunctionId, NativeScalarPrimitive>,
    authority_epochs: &'a BTreeMap<ExternalFunctionId, u64>,
    fresh_tokens: &'a BTreeSet<ExternalFunctionId>,
    fd_descriptors: &'a BTreeMap<ExternalFunctionId, FdDescriptor>,
    rule_name: &'a str,
    body_rows: Vec<(FunctionId, Vec<ScalarValueRef>)>,
    bindings: BTreeMap<u32, BoundValue>,
    slots: Vec<ScalarActionSlot>,
    effects: Vec<ScalarEffectPlan>,
    fresh_rank: u64,
    runtime_ordinal: u64,
    required_fresh_tokens: BTreeSet<ExternalFunctionId>,
    required_fd_descriptors: BTreeMap<ExternalFunctionId, FdDescriptor>,
    required_native_primitives: BTreeMap<ExternalFunctionId, NativePrimitive>,
    required_native_scalar_primitives: BTreeMap<ExternalFunctionId, NativeScalarPrimitive>,
    required_authority_epochs: BTreeMap<ExternalFunctionId, u64>,
}

impl<'a> GeneralScalarCompiler<'a> {
    fn retain_merge_program_closure(&mut self, root: FunctionId) -> Result<()> {
        let mut pending = vec![root];
        let mut visited = BTreeSet::new();
        while let Some(target) = pending.pop() {
            if !visited.insert(target) {
                continue;
            }
            let info = self.storage.table_info(target)?;
            info.merge_program.ensure_proof_supported(&info.name)?;
            for (&token, &registered_epoch) in &info.merge_program.required_authorities {
                ensure!(
                    self.authority_epochs.get(&token) == Some(&registered_epoch),
                    "DuckDB scalar rule `{}` target {} has a stale registration authority token {}",
                    self.rule_name,
                    target.rep(),
                    token.rep()
                );
                self.required_authority_epochs
                    .insert(token, registered_epoch);
            }
            pending.extend(info.merge_program.write_targets.iter().copied());
            for op in &info.merge_program.ops {
                let MergeOpKind::Primitive { primitive, .. } = &op.kind else {
                    continue;
                };
                match primitive {
                    MergePrimitive::Fresh { token } => {
                        self.required_fresh_tokens.insert(*token);
                    }
                    MergePrimitive::Fd { token, descriptor } => {
                        self.required_fd_descriptors
                            .insert(*token, descriptor.clone());
                    }
                    MergePrimitive::Scalar(expression) => match expression.authority() {
                        ScalarAuthority::Native(descriptor) => {
                            self.required_native_primitives
                                .insert(expression.token(), descriptor);
                        }
                        ScalarAuthority::Typed(descriptor) => {
                            self.required_native_scalar_primitives
                                .insert(expression.token(), descriptor);
                        }
                    },
                    MergePrimitive::Unauthenticated { token } => bail!(
                        "DuckDB scalar rule `{}` target {} has unauthenticated merge token {}",
                        self.rule_name,
                        target.rep(),
                        token.rep()
                    ),
                }
            }
        }
        Ok(())
    }

    fn compile_term(
        &self,
        term: &GenericAtomTerm<RuleVar, RuleValue>,
        expected: ColumnTy,
        context: &str,
    ) -> Result<ScalarValueRef> {
        match term {
            GenericAtomTerm::Var(_, variable) => {
                ensure!(
                    variable.ty == expected,
                    "DuckDB scalar rule `{}` {context} has a mistyped variable",
                    self.rule_name
                );
                let binding = self.bindings.get(&variable.id).ok_or_else(|| {
                    anyhow!(
                        "DuckDB scalar rule `{}` {context} uses variable id {} before binding",
                        self.rule_name,
                        variable.id
                    )
                })?;
                ensure!(
                    binding.ty == variable.ty,
                    "DuckDB scalar rule `{}` reuses variable id {} with inconsistent type metadata",
                    self.rule_name,
                    variable.id
                );
                Ok(binding.value.clone())
            }
            GenericAtomTerm::Literal(_, literal) => {
                ensure!(
                    literal.ty == expected,
                    "DuckDB scalar rule `{}` {context} has a mistyped literal",
                    self.rule_name
                );
                let scalar = ScalarSqlType::from_column(self.base_values, expected)?;
                Ok(ScalarValueRef::Literal(ScalarLiteral {
                    value: *literal,
                    scalar,
                    sql: scalar.sql_literal(self.base_values, literal.value)?,
                }))
            }
            GenericAtomTerm::Global(..) => bail!(
                "DuckDB scalar rule `{}` {context} contains an unsupported global",
                self.rule_name
            ),
        }
    }

    fn bind_value(
        &mut self,
        variable: &RuleVar,
        value: ScalarValueRef,
        context: &str,
    ) -> Result<()> {
        ensure!(
            !self.bindings.contains_key(&variable.id),
            "DuckDB scalar rule `{}` {context} rebinds SSA variable id {}",
            self.rule_name,
            variable.id
        );
        self.bindings.insert(
            variable.id,
            BoundValue {
                ty: variable.ty,
                value,
            },
        );
        Ok(())
    }

    fn bind_slot(
        &mut self,
        raw_action_ordinal: usize,
        variable: &RuleVar,
        source: ScalarActionSlotSource,
    ) -> Result<usize> {
        let slot = self.slots.len();
        self.bind_value(variable, ScalarValueRef::Slot(slot), "Let")?;
        self.slots.push(ScalarActionSlot {
            raw_action_ordinal,
            runtime_ordinal: self.runtime_ordinal,
            ty: variable.ty,
            source,
        });
        Ok(slot)
    }

    fn classify_effect(
        &mut self,
        target: FunctionId,
        info: &TableInfo,
    ) -> Result<ScalarEffectKind> {
        Ok(match info.write_capability {
            WriteCapability::AssertEq => ScalarEffectKind::AssertEq,
            WriteCapability::KeepOld => ScalarEffectKind::KeepOld,
            WriteCapability::Deferred => {
                self.retain_merge_program_closure(target)?;
                ScalarEffectKind::GenericMerge
            }
        })
    }

    fn compile_set(
        &mut self,
        raw_action_ordinal: usize,
        call: &RuleActionCall,
        arguments: &[GenericAtomTerm<RuleVar, RuleValue>],
        values: &[GenericAtomTerm<RuleVar, RuleValue>],
        condition_slot: Option<usize>,
    ) -> Result<()> {
        let RuleActionCall::Table { id: target, .. } = call else {
            bail!(
                "DuckDB scalar rule `{}` action {raw_action_ordinal} cannot Set a primitive",
                self.rule_name
            );
        };
        let info = self.storage.table_info(*target).with_context(|| {
            format!(
                "DuckDB scalar rule `{}` action {raw_action_ordinal} has an invalid target",
                self.rule_name
            )
        })?;
        ensure!(
            arguments.len() == info.n_keys && values.len() == info.n_vals,
            "DuckDB scalar rule `{}` action {raw_action_ordinal} has the wrong complete-row Set arity",
            self.rule_name
        );
        let arguments = arguments
            .iter()
            .zip(&info.schema[..info.n_keys])
            .map(|(term, &ty)| self.compile_term(term, ty, "Set key"))
            .collect::<Result<Vec<_>>>()?;
        let values = values
            .iter()
            .zip(&info.schema[info.n_keys..])
            .map(|(term, &ty)| self.compile_term(term, ty, "Set value"))
            .collect::<Result<Vec<_>>>()?;
        let kind = self.classify_effect(*target, &info)?;
        self.effects.push(ScalarEffectPlan {
            event_ordinal: self.runtime_ordinal,
            target: *target,
            arity: info.arity(),
            n_keys: info.n_keys,
            kind,
            arguments,
            values,
            condition_slot,
        });
        Ok(())
    }

    fn compile_change(
        &mut self,
        raw_action_ordinal: usize,
        change: Change,
        call: &RuleActionCall,
        arguments: &[GenericAtomTerm<RuleVar, RuleValue>],
    ) -> Result<()> {
        let RuleActionCall::Table { id: target, .. } = call else {
            bail!(
                "DuckDB scalar rule `{}` action {raw_action_ordinal} cannot change a primitive",
                self.rule_name
            )
        };
        let info = self.storage.table_info(*target)?;
        ensure!(
            arguments.len() == info.n_keys,
            "DuckDB scalar rule `{}` action {raw_action_ordinal} has the wrong change key arity",
            self.rule_name
        );
        let keys = arguments
            .iter()
            .zip(&info.schema[..info.n_keys])
            .map(|(term, &ty)| self.compile_term(term, ty, "change key"))
            .collect::<Result<Vec<_>>>()?;
        let (kind, values) = match change {
            Change::Delete => (ScalarEffectKind::Delete, Vec::new()),
            Change::Subsume => {
                ensure!(
                    info.can_subsume,
                    "DuckDB scalar rule `{}` cannot subsume a nonsubsumable table",
                    self.rule_name
                );
                let mut candidates = self.body_rows.iter().filter(|(id, row)| {
                    id == target && row.len() == info.arity() && row[..info.n_keys] == keys
                });
                let (_, row) = candidates.next().ok_or_else(|| anyhow!(
                    "DuckDB scalar rule `{}` Subsume does not identify a complete pre-wave body row",
                    self.rule_name
                ))?;
                ensure!(
                    candidates.next().is_none(),
                    "DuckDB scalar rule `{}` Subsume ambiguously identifies multiple body rows",
                    self.rule_name
                );
                (ScalarEffectKind::Subsume, row[info.n_keys..].to_vec())
            }
        };
        self.effects.push(ScalarEffectPlan {
            event_ordinal: self.runtime_ordinal,
            target: *target,
            arity: info.arity(),
            n_keys: info.n_keys,
            kind,
            arguments: keys,
            values,
            condition_slot: None,
        });
        Ok(())
    }

    fn resolve_fd_view(&self, descriptor: &FdDescriptor) -> Result<(FunctionId, TableInfo)> {
        let name = match descriptor {
            FdDescriptor::SetIfEmpty { view_name, .. }
            | FdDescriptor::ViewColumnRead { view_name, .. } => view_name,
        };
        self.storage.table_by_exact_name(name).with_context(|| {
            format!(
                "DuckDB scalar rule `{}` cannot resolve FD view",
                self.rule_name
            )
        })
    }

    fn compile_let(
        &mut self,
        raw_action_ordinal: usize,
        variable: &RuleVar,
        call: &RuleActionCall,
        arguments: &[GenericAtomTerm<RuleVar, RuleValue>],
    ) -> Result<()> {
        match call {
            RuleActionCall::Table { id: target, .. } => {
                let info = self.storage.table_info(*target)?;
                ensure!(
                    info.n_vals == 1 && matches!(info.default, DefaultVal::Fail),
                    "DuckDB scalar rule `{}` action {raw_action_ordinal} table Let requires exactly one output and DefaultVal::Fail",
                    self.rule_name
                );
                ensure!(
                    arguments.len() == info.n_keys && variable.ty == info.schema[info.n_keys],
                    "DuckDB scalar rule `{}` action {raw_action_ordinal} table Let has the wrong signature",
                    self.rule_name
                );
                let keys = arguments
                    .iter()
                    .zip(&info.schema[..info.n_keys])
                    .map(|(term, &ty)| self.compile_term(term, ty, "table Let key"))
                    .collect::<Result<Vec<_>>>()?;
                self.bind_slot(
                    raw_action_ordinal,
                    variable,
                    ScalarActionSlotSource::Read(ScalarActionRead::Table {
                        target: *target,
                        n_keys: info.n_keys,
                        result_column: info.n_keys,
                        keys,
                    }),
                )?;
            }
            RuleActionCall::Primitive { id, output, .. } => {
                ensure!(
                    *output == variable.ty,
                    "DuckDB scalar rule `{}` action {raw_action_ordinal} primitive result type disagrees with its binding",
                    self.rule_name
                );
                if self.fresh_tokens.contains(id) {
                    ensure!(
                        *output == ColumnTy::Id && variable.ty == ColumnTy::Id,
                        "DuckDB scalar rule `{}` action {raw_action_ordinal} get-fresh result must be Id",
                        self.rule_name
                    );
                    let [label] = arguments else {
                        bail!(
                            "DuckDB scalar rule `{}` action {raw_action_ordinal} get-fresh requires one String literal",
                            self.rule_name
                        );
                    };
                    let ScalarValueRef::Literal(label) =
                        self.compile_term(label, argument_ty(label), "fresh label")?
                    else {
                        bail!(
                            "DuckDB scalar rule `{}` action {raw_action_ordinal} fresh label must be a literal",
                            self.rule_name
                        );
                    };
                    ensure!(
                        label.scalar == ScalarSqlType::String,
                        "DuckDB scalar rule `{}` action {raw_action_ordinal} fresh label must be String",
                        self.rule_name
                    );
                    self.required_fresh_tokens.insert(*id);
                    let rank = self.fresh_rank;
                    self.fresh_rank = self
                        .fresh_rank
                        .checked_add(1)
                        .context("DuckDB scalar fresh-site count overflow")?;
                    self.bind_slot(
                        raw_action_ordinal,
                        variable,
                        ScalarActionSlotSource::Fresh { rank },
                    )?;
                } else if let Some(descriptor) = self.fd_descriptors.get(id).cloned() {
                    let (target, info) = self.resolve_fd_view(&descriptor)?;
                    ensure!(
                        matches!(info.default, DefaultVal::Fail),
                        "DuckDB scalar rule `{}` action {raw_action_ordinal} FD view must use DefaultVal::Fail",
                        self.rule_name
                    );
                    self.required_fd_descriptors.insert(*id, descriptor.clone());
                    match descriptor {
                        FdDescriptor::SetIfEmpty {
                            n_keys, out_arity, ..
                        } => {
                            ensure!(
                                info.n_keys == n_keys
                                    && info.n_vals == out_arity
                                    && arguments.len() == n_keys + out_arity
                                    && variable.ty == info.schema[n_keys],
                                "DuckDB scalar rule `{}` action {raw_action_ordinal} set-if-empty descriptor disagrees with the resolved view schema",
                                self.rule_name
                            );
                            let keys = arguments[..n_keys]
                                .iter()
                                .zip(&info.schema[..n_keys])
                                .map(|(term, &ty)| self.compile_term(term, ty, "set-if-empty key"))
                                .collect::<Result<Vec<_>>>()?;
                            let defaults = arguments[n_keys..]
                                .iter()
                                .zip(&info.schema[n_keys..])
                                .map(|(term, &ty)| {
                                    self.compile_term(term, ty, "set-if-empty default")
                                })
                                .collect::<Result<Vec<_>>>()?;
                            let slot = self.bind_slot(
                                raw_action_ordinal,
                                variable,
                                ScalarActionSlotSource::Read(ScalarActionRead::SetIfEmpty {
                                    target,
                                    n_keys,
                                    keys: keys.clone(),
                                    defaults: defaults.clone(),
                                }),
                            )?;
                            let kind = self.classify_effect(target, &info)?;
                            self.effects.push(ScalarEffectPlan {
                                event_ordinal: self.runtime_ordinal,
                                target,
                                arity: info.arity(),
                                n_keys,
                                kind,
                                arguments: keys,
                                values: defaults,
                                condition_slot: Some(slot),
                            });
                        }
                        FdDescriptor::ViewColumnRead {
                            n_keys, col_idx, ..
                        } => {
                            ensure!(
                                info.n_keys == n_keys
                                    && col_idx < info.n_vals
                                    && arguments.len() == n_keys + 1
                                    && variable.ty == info.schema[n_keys + col_idx],
                                "DuckDB scalar rule `{}` action {raw_action_ordinal} view-column descriptor disagrees with the resolved view schema",
                                self.rule_name
                            );
                            let keys = arguments[..n_keys]
                                .iter()
                                .zip(&info.schema[..n_keys])
                                .map(|(term, &ty)| self.compile_term(term, ty, "view-column key"))
                                .collect::<Result<Vec<_>>>()?;
                            let fallback = self.compile_term(
                                &arguments[n_keys],
                                info.schema[n_keys + col_idx],
                                "view-column fallback",
                            )?;
                            self.bind_slot(
                                raw_action_ordinal,
                                variable,
                                ScalarActionSlotSource::Read(ScalarActionRead::ViewColumn {
                                    target,
                                    n_keys,
                                    result_column: n_keys + col_idx,
                                    keys,
                                    fallback,
                                }),
                            )?;
                        }
                    }
                } else {
                    let input_tys = arguments.iter().map(argument_ty).collect::<Vec<_>>();
                    let expression = ScalarExpression::authenticate(
                        self.base_values,
                        self.native_primitives,
                        self.native_scalar_primitives,
                        *id,
                        &input_tys,
                        *output,
                    )
                    .with_context(|| {
                        format!(
                            "DuckDB scalar rule `{}` action {raw_action_ordinal} has an invalid scalar expression",
                            self.rule_name
                        )
                    })?;
                    let inputs = arguments
                        .iter()
                        .zip(input_tys)
                        .map(|(term, ty)| self.compile_term(term, ty, "scalar expression input"))
                        .collect::<Result<Vec<_>>>()?;
                    match expression.authority() {
                        ScalarAuthority::Native(descriptor) => {
                            self.required_native_primitives.insert(*id, descriptor);
                        }
                        ScalarAuthority::Typed(descriptor) => {
                            self.required_native_scalar_primitives
                                .insert(*id, descriptor);
                        }
                    }
                    self.bind_slot(
                        raw_action_ordinal,
                        variable,
                        ScalarActionSlotSource::Expression { expression, inputs },
                    )?;
                }
            }
        }
        Ok(())
    }
}

/// Tri-state admission for the general scalar action stream. Direct cleanup
/// rules and a single directly executable Set retain their existing compiler;
/// once this branch owns a supported Live-table body and Let/Set vocabulary,
/// every interior operation is validated before a RuleId can be allocated.
pub(crate) fn compile_scalar_action(
    storage: &Storage,
    base_values: &BaseValues,
    authorities: &AuthorityRegistries<'_>,
    rule: &RuleSpec,
) -> Result<Option<ScalarActionPlan>> {
    let native_primitives = authorities.native_primitives;
    let native_scalar_primitives = authorities.native_scalar_primitives;
    let authority_epochs = authorities.authority_epochs;
    let fresh_tokens = authorities.fresh_tokens;
    let fd_descriptors = authorities.fd_descriptors;
    if rule.core.head.0.is_empty()
        || !rule.core.body.atoms.iter().all(|atom| {
            matches!(
                atom.head,
                RuleBodyCall::Table { .. }
                    | RuleBodyCall::IndexTable { .. }
                    | RuleBodyCall::Primitive { .. }
            )
        })
        || !rule.core.head.0.iter().all(|action| {
            matches!(
                action,
                GenericCoreAction::Let(..)
                    | GenericCoreAction::LetAtomTerm(..)
                    | GenericCoreAction::Set(..)
                    | GenericCoreAction::Change(_, Change::Delete | Change::Subsume, ..)
            )
        })
    {
        return Ok(None);
    }
    // Once a rule is wholly inside the generic body's and action stream's
    // supported vocabulary, this compiler owns it. A single direct Set or
    // Change must not escape to a second executor and split a frozen ruleset.

    let body = compile_scalar_body(
        storage,
        base_values,
        native_primitives,
        native_scalar_primitives,
        rule,
    )?;
    let mut bindings = BTreeMap::new();
    for (&id, binding) in &body.bindings {
        bindings.insert(
            id,
            BoundValue {
                ty: binding.ty,
                value: ScalarValueRef::Body(binding.stage_column),
            },
        );
    }
    let mut compiler = GeneralScalarCompiler {
        storage,
        base_values,
        native_primitives,
        native_scalar_primitives,
        authority_epochs,
        fresh_tokens,
        fd_descriptors,
        rule_name: &rule.name,
        body_rows: body.rows,
        bindings,
        slots: Vec::new(),
        effects: Vec::new(),
        fresh_rank: 0,
        runtime_ordinal: 0,
        required_fresh_tokens: BTreeSet::new(),
        required_fd_descriptors: BTreeMap::new(),
        required_native_primitives: body.required_native_primitives,
        required_native_scalar_primitives: body.required_native_scalar_primitives,
        required_authority_epochs: BTreeMap::new(),
    };

    for (raw_action_ordinal, action) in rule.core.head.0.iter().enumerate() {
        match action {
            GenericCoreAction::Let(_, variable, call, arguments) => {
                compiler.compile_let(raw_action_ordinal, variable, call, arguments)?;
                compiler.runtime_ordinal = compiler
                    .runtime_ordinal
                    .checked_add(1)
                    .context("DuckDB scalar runtime action count overflow")?;
            }
            GenericCoreAction::LetAtomTerm(_, variable, source) => {
                let context = format!("action {raw_action_ordinal} LetAtomTerm");
                let source = compiler.compile_term(source, variable.ty, &context)?;
                compiler.bind_value(variable, source, &context)?;
            }
            GenericCoreAction::Set(_, call, arguments, values) => {
                compiler.compile_set(raw_action_ordinal, call, arguments, values, None)?;
                compiler.runtime_ordinal = compiler
                    .runtime_ordinal
                    .checked_add(1)
                    .context("DuckDB scalar runtime action count overflow")?;
            }
            GenericCoreAction::Change(_, change, call, arguments) => {
                compiler.compile_change(raw_action_ordinal, *change, call, arguments)?;
                compiler.runtime_ordinal = compiler
                    .runtime_ordinal
                    .checked_add(1)
                    .context("DuckDB scalar runtime action count overflow")?;
            }
            GenericCoreAction::Union(..) | GenericCoreAction::Panic(..) => {
                unreachable!("owner vocabulary checked above")
            }
        }
    }
    ensure!(
        !compiler.effects.is_empty(),
        "DuckDB scalar rule `{}` has no durable Set effect",
        rule.name
    );

    let required_tokens = compiler
        .required_native_primitives
        .keys()
        .chain(compiler.required_native_scalar_primitives.keys())
        .chain(compiler.required_fresh_tokens.iter())
        .chain(compiler.required_fd_descriptors.keys())
        .copied()
        .collect::<BTreeSet<_>>();
    let mut required_authority_epochs = compiler.required_authority_epochs;
    for token in required_tokens {
        let epoch = authority_epochs.get(&token).copied().ok_or_else(|| {
            anyhow!(
                "DuckDB scalar rule `{}` has no live authority epoch for token {}",
                rule.name,
                token.rep()
            )
        })?;
        if let Some(required) = required_authority_epochs.insert(token, epoch) {
            ensure!(
                required == epoch,
                "DuckDB scalar rule `{}` token {} changed authority epoch after table registration",
                rule.name,
                token.rep()
            );
        }
    }

    Ok(Some(ScalarActionPlan {
        seminaive: rule.seminaive,
        match_projection: body.match_projection,
        match_from: body.match_from,
        match_predicates: body.match_predicates,
        freshness_columns: body.freshness_columns,
        order_columns: body.order_columns,
        slots: compiler.slots,
        effects: compiler.effects,
        fresh_slots: compiler.fresh_rank,
        action_count: compiler.runtime_ordinal,
        required_fresh_tokens: compiler.required_fresh_tokens,
        required_fd_descriptors: compiler.required_fd_descriptors,
        required_native_primitives: compiler.required_native_primitives,
        required_native_scalar_primitives: compiler.required_native_scalar_primitives,
        required_authority_epochs,
    }))
}

fn render_general_ref(value: &ScalarValueRef, alias: &str) -> String {
    match value {
        ScalarValueRef::Body(column) => format!("{alias}.b{column}"),
        ScalarValueRef::Slot(slot) => format!("{alias}.s{slot}"),
        ScalarValueRef::Literal(literal) => literal.sql.clone(),
    }
}

fn render_read_equality(keys: &[ScalarValueRef], n_keys: usize, alias: &str) -> String {
    if n_keys == 0 {
        "TRUE".to_string()
    } else {
        keys.iter()
            .enumerate()
            .map(|(column, value)| {
                format!(
                    "existing.c{column} IS NOT DISTINCT FROM {}",
                    render_general_ref(value, alias)
                )
            })
            .collect::<Vec<_>>()
            .join(" AND ")
    }
}

fn render_scratch_key_equality(
    requested_keys: &[ScalarValueRef],
    n_keys: usize,
    scratch_alias: &str,
    requested_alias: &str,
) -> String {
    if n_keys == 0 {
        "TRUE".to_string()
    } else {
        requested_keys
            .iter()
            .enumerate()
            .map(|(column, requested)| {
                format!(
                    "{scratch_alias}.c{column} IS NOT DISTINCT FROM {}",
                    render_general_ref(requested, requested_alias)
                )
            })
            .collect::<Vec<_>>()
            .join(" AND ")
    }
}

fn render_row_key_equality(n_keys: usize, left: &str, right: &str) -> String {
    if n_keys == 0 {
        "TRUE".to_string()
    } else {
        (0..n_keys)
            .map(|column| format!("{left}.c{column} IS NOT DISTINCT FROM {right}.c{column}"))
            .collect::<Vec<_>>()
            .join(" AND ")
    }
}
