//! SQL lowering for the first production `RuleSpec` subset.
//!
//! This module deliberately represents a narrow, closed language. Admission
//! validates every body atom, term, action, table schema, and merge policy
//! before a rule id is allocated. Execution materializes matches in DuckDB;
//! Rust retains only immutable SQL plans, generation watermarks, and scalar
//! statement/count telemetry.

use std::collections::BTreeMap;

use anyhow::{Result, anyhow, bail};
use egglog_ast::core::{GenericAtomTerm, GenericCoreAction};
use egglog_ast::generic_ast::Change;
use egglog_backend_trait::{
    BaseValues, ColumnTy, FunctionId, ReadMode, RuleActionCall, RuleBodyCall, RuleSpec, RuleValue,
    RuleVar,
};
use egglog_numeric_id::NumericId;

use crate::marker_rekey::{MarkerRekeyPlan, compile_marker_rekey};
use crate::path_compress::{
    PathCompressionPlan, compile_path_compression, looks_like_path_compression,
};
use crate::rebuild::{StandardRebuildPlan, compile_standard_rebuild};
use crate::storage::{
    ScalarSqlType, Storage, TableInfo, WriteCapability, assert_eq_conflict_sql, sql_table,
    visible_columns,
};

#[derive(Clone, Debug)]
struct VariableBinding {
    expression: String,
    ty: ColumnTy,
    name: Box<str>,
}

#[derive(Clone, Debug)]
pub(crate) struct CompiledRule {
    pub(crate) seminaive: bool,
    kind: CompiledRuleKind,
}

#[derive(Clone, Debug)]
enum CompiledRuleKind {
    Direct(DirectRule),
    MarkerRekey(MarkerRekeyPlan),
    PathCompression(PathCompressionPlan),
    StandardRebuild(StandardRebuildPlan),
}

#[derive(Clone, Debug)]
struct DirectRule {
    effects: Vec<DirectEffect>,
    select_expressions: Vec<String>,
    from: Vec<String>,
    predicates: Vec<String>,
    freshness_columns: Vec<String>,
    order_columns: Vec<String>,
}

#[derive(Clone, Debug)]
enum DirectEffect {
    Set {
        target: FunctionId,
        target_arity: usize,
        target_n_keys: usize,
        target_write_capability: WriteCapability,
        column_offset: usize,
    },
    Delete {
        target: FunctionId,
        target_n_keys: usize,
        column_offset: usize,
    },
    Subsume {
        target: FunctionId,
        target_arity: usize,
        target_n_keys: usize,
        column_offset: usize,
    },
}

#[derive(Clone, Debug)]
struct BodyTable {
    id: FunctionId,
    alias: String,
    args: Vec<GenericAtomTerm<RuleVar, RuleValue>>,
}

impl CompiledRule {
    pub(crate) fn materialize_sql(&self, stage: &str, watermark: u64) -> String {
        if let CompiledRuleKind::PathCompression(plan) = &self.kind {
            return plan.materialize_sql(stage, watermark);
        }
        if let CompiledRuleKind::StandardRebuild(plan) = &self.kind {
            return plan.materialize_sql(stage, watermark);
        }
        if let CompiledRuleKind::MarkerRekey(plan) = &self.kind {
            return plan.materialize_sql(stage, watermark);
        }
        let CompiledRuleKind::Direct(direct) = &self.kind else {
            unreachable!();
        };
        debug_assert!(
            stage
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        );
        let mut predicates = direct.predicates.clone();
        if self.seminaive {
            predicates.push(format!(
                "({})",
                direct
                    .freshness_columns
                    .iter()
                    .map(|column| { format!("{column} >= CAST('{watermark}' AS UBIGINT)") })
                    .collect::<Vec<_>>()
                    .join(" OR ")
            ));
        }
        let predicate = if predicates.is_empty() {
            "TRUE".to_string()
        } else {
            predicates.join(" AND ")
        };
        let mut projection = direct
            .select_expressions
            .iter()
            .enumerate()
            .map(|(column, expression)| format!("{expression} AS c{column}"))
            .collect::<Vec<_>>();
        projection.push(format!(
            "row_number() OVER (ORDER BY {}) AS __match_ordinal",
            direct.order_columns.join(", ")
        ));
        format!(
            "CREATE TEMP TABLE {stage} AS
             SELECT {}
             FROM {}
             WHERE {predicate}",
            projection.join(", "),
            direct.from.join(" CROSS JOIN ")
        )
    }

    pub(crate) fn delete_sql(&self, stage: &str) -> Vec<String> {
        let CompiledRuleKind::Direct(direct) = &self.kind else {
            unreachable!("staged-queue rules use their dedicated executor");
        };
        direct
            .effects
            .iter()
            .filter_map(|effect| {
                let DirectEffect::Delete {
                    target,
                    target_n_keys,
                    column_offset,
                } = effect
                else {
                    return None;
                };
                let predicate =
                    stage_key_equality("existing", "staged", *column_offset, *target_n_keys);
                Some(format!(
                    "DELETE FROM {} AS existing
                     WHERE EXISTS (SELECT 1 FROM {stage} AS staged WHERE {predicate})",
                    sql_table(*target)
                ))
            })
            .collect()
    }

    pub(crate) fn insert_sql(&self, stage: &str, generation: u64) -> Option<String> {
        let CompiledRuleKind::Direct(direct) = &self.kind else {
            unreachable!("staged-queue rules use their dedicated executor");
        };
        let DirectEffect::Set {
            target,
            target_arity,
            target_n_keys,
            column_offset,
            ..
        } = direct.effects.first()?
        else {
            return None;
        };
        debug_assert!(
            stage
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        );
        let partition = if *target_n_keys == 0 {
            "ORDER BY staged.__match_ordinal".to_string()
        } else {
            format!(
                "PARTITION BY {} ORDER BY staged.__match_ordinal",
                qualified_column_range("staged", *column_offset, *target_n_keys)
            )
        };
        let no_existing = if *target_n_keys == 0 {
            format!("NOT EXISTS (SELECT 1 FROM {})", sql_table(*target))
        } else {
            let equality = stage_key_equality("existing", "ranked", *column_offset, *target_n_keys);
            format!(
                "NOT EXISTS (SELECT 1 FROM {} AS existing WHERE {equality})",
                sql_table(*target)
            )
        };

        Some(format!(
            "INSERT INTO {} ({}, __generation, __subsumed)
             SELECT {}, CAST('{generation}' AS UBIGINT), FALSE
             FROM (
                 SELECT staged.*,
                        row_number() OVER ({partition}) AS __key_rank
                 FROM {stage} AS staged
             ) AS ranked
             WHERE ranked.__key_rank = 1 AND {no_existing}",
            sql_table(*target),
            visible_columns(*target_arity),
            qualified_column_range("ranked", *column_offset, *target_arity),
        ))
    }

    pub(crate) fn conflict_sql(&self, stage: &str) -> Option<String> {
        let CompiledRuleKind::Direct(direct) = &self.kind else {
            return None;
        };
        let DirectEffect::Set {
            target,
            target_n_keys,
            target_write_capability,
            column_offset,
            ..
        } = direct.effects.first()?
        else {
            return None;
        };
        debug_assert_eq!(*column_offset, 0);
        (*target_write_capability == WriteCapability::AssertEq)
            .then(|| assert_eq_conflict_sql(*target, *target_n_keys, stage))
    }

    pub(crate) fn subsume_sql(&self, stage: &str, generation: u64) -> Vec<String> {
        let CompiledRuleKind::Direct(direct) = &self.kind else {
            unreachable!("staged-queue rules use their dedicated executor");
        };
        direct
            .effects
            .iter()
            .filter_map(|effect| {
                let DirectEffect::Subsume {
                    target,
                    target_arity,
                    target_n_keys,
                    column_offset,
                } = effect
                else {
                    return None;
                };
                let equality =
                    stage_key_equality("existing", "staged", *column_offset, *target_n_keys);
                let partition = if *target_n_keys == 0 {
                    "ORDER BY staged.__match_ordinal".to_string()
                } else {
                    format!(
                        "PARTITION BY {} ORDER BY staged.__match_ordinal",
                        qualified_column_range("staged", *column_offset, *target_n_keys)
                    )
                };
                let no_existing = if *target_n_keys == 0 {
                    format!("NOT EXISTS (SELECT 1 FROM {})", sql_table(*target))
                } else {
                    let equality =
                        stage_key_equality("existing", "ranked", *column_offset, *target_n_keys);
                    format!(
                        "NOT EXISTS (SELECT 1 FROM {} AS existing WHERE {equality})",
                        sql_table(*target)
                    )
                };
                Some(vec![
                    format!(
                        "UPDATE {} AS existing
                         SET __generation = CAST('{generation}' AS UBIGINT), __subsumed = TRUE
                         WHERE existing.__subsumed = FALSE
                           AND EXISTS (SELECT 1 FROM {stage} AS staged WHERE {equality})",
                        sql_table(*target)
                    ),
                    format!(
                        "INSERT INTO {} ({}, __generation, __subsumed)
                         SELECT {}, CAST('{generation}' AS UBIGINT), TRUE
                         FROM (
                             SELECT staged.*,
                                    row_number() OVER ({partition}) AS __key_rank
                             FROM {stage} AS staged
                         ) AS ranked
                         WHERE ranked.__key_rank = 1 AND {no_existing}",
                        sql_table(*target),
                        visible_columns(*target_arity),
                        qualified_column_range("ranked", *column_offset, *target_arity),
                    ),
                ])
            })
            .flatten()
            .collect()
    }

    pub(crate) fn path_compression(&self) -> Option<&PathCompressionPlan> {
        match &self.kind {
            CompiledRuleKind::PathCompression(plan) => Some(plan),
            CompiledRuleKind::Direct(_)
            | CompiledRuleKind::MarkerRekey(_)
            | CompiledRuleKind::StandardRebuild(_) => None,
        }
    }

    pub(crate) fn standard_rebuild(&self) -> Option<&StandardRebuildPlan> {
        match &self.kind {
            CompiledRuleKind::StandardRebuild(plan) => Some(plan),
            CompiledRuleKind::Direct(_)
            | CompiledRuleKind::MarkerRekey(_)
            | CompiledRuleKind::PathCompression(_) => None,
        }
    }

    pub(crate) fn marker_rekey(&self) -> Option<&MarkerRekeyPlan> {
        match &self.kind {
            CompiledRuleKind::MarkerRekey(plan) => Some(plan),
            CompiledRuleKind::Direct(_)
            | CompiledRuleKind::PathCompression(_)
            | CompiledRuleKind::StandardRebuild(_) => None,
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct RuleExecutionStats {
    pub(crate) changed: bool,
    /// The next seminaive lower bound after this committed pre-wave snapshot.
    pub(crate) watermark: u64,
    pub(crate) matched_rows: Vec<usize>,
    pub(crate) inserted_rows: Vec<usize>,
    pub(crate) statement_count: usize,
}

pub(crate) fn compile_rule(
    storage: &Storage,
    base_values: &BaseValues,
    rule: RuleSpec,
) -> Result<CompiledRule> {
    // Rebuild admission is tri-state and must precede the path compiler's
    // intentionally cheap arity discriminator. A malformed standard outer
    // topology is an error; marker/container/custom topologies fall through.
    if let Some(plan) = compile_standard_rebuild(storage, base_values, &rule)? {
        return Ok(CompiledRule {
            seminaive: rule.seminaive,
            kind: CompiledRuleKind::StandardRebuild(plan),
        });
    }
    if let Some(plan) = compile_marker_rekey(storage, base_values, &rule)? {
        return Ok(CompiledRule {
            seminaive: rule.seminaive,
            kind: CompiledRuleKind::MarkerRekey(plan),
        });
    }
    // A Delete-only head is already a complete direct language regardless of
    // body/head cardinality. Give it priority over the path compiler's cheap
    // arity discriminator so a three-body/four-Delete rule cannot be captured
    // as a malformed path candidate.
    if looks_like_path_compression(&rule) && !is_delete_only(&rule) {
        let seminaive = rule.seminaive;
        let plan = compile_path_compression(storage, base_values, &rule)?;
        return Ok(CompiledRule {
            seminaive,
            kind: CompiledRuleKind::PathCompression(plan),
        });
    }
    if rule.core.body.atoms.is_empty() {
        bail!("DuckDB rule `{}` has an empty body", rule.name);
    }
    let mut bindings = BTreeMap::<u32, VariableBinding>::new();
    let mut from = Vec::with_capacity(rule.core.body.atoms.len());
    let mut predicates = Vec::new();
    let mut freshness_columns = Vec::with_capacity(rule.core.body.atoms.len());
    let mut order_columns = Vec::new();
    let mut body_tables = Vec::with_capacity(rule.core.body.atoms.len());

    for (atom_index, atom) in rule.core.body.atoms.iter().enumerate() {
        let RuleBodyCall::Table { id, read } = &atom.head else {
            bail!(
                "DuckDB rule `{}` contains a primitive body atom; only table atoms are supported",
                rule.name
            );
        };
        if *read != ReadMode::Live {
            bail!(
                "DuckDB rule `{}` requests {read:?}; only Live table reads are supported",
                rule.name
            );
        }
        let info = storage.table_info(*id).map_err(|error| {
            anyhow!(
                "DuckDB rule `{}` references an invalid body table {}: {error:#}",
                rule.name,
                id.rep()
            )
        })?;
        if atom.args.len() != info.arity() {
            bail!(
                "DuckDB rule `{}` body table `{}` expects {} arguments, got {}",
                rule.name,
                info.name,
                info.arity(),
                atom.args.len()
            );
        }

        let alias = format!("b{atom_index}");
        from.push(format!("{} AS {alias}", sql_table(*id)));
        predicates.push(format!("{alias}.__subsumed = FALSE"));
        freshness_columns.push(format!("{alias}.__generation"));
        order_columns.push(format!("{alias}.__generation"));
        order_columns.extend((0..info.arity()).map(|column| format!("{alias}.c{column}")));
        body_tables.push(BodyTable {
            id: *id,
            alias: alias.clone(),
            args: atom.args.clone(),
        });

        for (column, (term, &expected)) in atom.args.iter().zip(&info.schema).enumerate() {
            let column_expression = format!("{alias}.c{column}");
            match term {
                GenericAtomTerm::Var(_, variable) => {
                    validate_variable(&rule.name, variable, expected)?;
                    if let Some(binding) = bindings.get(&variable.id) {
                        if binding.ty != variable.ty || binding.name != variable.name {
                            bail!(
                                "DuckDB rule `{}` reuses variable id {} with inconsistent metadata",
                                rule.name,
                                variable.id
                            );
                        }
                        predicates.push(format!(
                            "{column_expression} IS NOT DISTINCT FROM {}",
                            binding.expression
                        ));
                    } else {
                        bindings.insert(
                            variable.id,
                            VariableBinding {
                                expression: column_expression,
                                ty: variable.ty,
                                name: variable.name.clone(),
                            },
                        );
                    }
                }
                GenericAtomTerm::Literal(_, literal) => {
                    validate_literal(&rule.name, literal, expected)?;
                    let encoded = ScalarSqlType::from_column(base_values, expected)?
                        .sql_literal(base_values, literal.value)?;
                    predicates.push(format!(
                        "{column_expression} IS NOT DISTINCT FROM {encoded}"
                    ));
                }
                GenericAtomTerm::Global(..) => {
                    bail!(
                        "DuckDB rule `{}` contains a global body term; globals must be desugared",
                        rule.name
                    );
                }
            }
        }
    }

    let (effects, select_expressions) =
        compile_direct_effects(storage, base_values, &rule, &bindings, &body_tables)?;

    Ok(CompiledRule {
        seminaive: rule.seminaive,
        kind: CompiledRuleKind::Direct(DirectRule {
            effects,
            select_expressions,
            from,
            predicates,
            freshness_columns,
            order_columns,
        }),
    })
}

fn compile_direct_effects(
    storage: &Storage,
    base_values: &BaseValues,
    rule: &RuleSpec,
    bindings: &BTreeMap<u32, VariableBinding>,
    body_tables: &[BodyTable],
) -> Result<(Vec<DirectEffect>, Vec<String>)> {
    if rule.core.head.0.is_empty() {
        bail!("DuckDB rule `{}` has an empty action list", rule.name);
    }

    if rule.core.head.0.len() == 1
        && let GenericCoreAction::Set(_, call, arguments, values) = &rule.core.head.0[0]
    {
        let RuleActionCall::Table { id: target, .. } = call else {
            bail!(
                "DuckDB rule `{}` attempts to set a primitive; exactly one table Set is required",
                rule.name
            );
        };
        let target_info = action_table_info(storage, &rule.name, *target)?;
        validate_target(&rule.name, &target_info, arguments.len(), values.len())?;
        let mut select_expressions = Vec::with_capacity(target_info.arity());
        for (term, &expected) in arguments.iter().chain(values).zip(&target_info.schema) {
            select_expressions.push(head_expression(
                &rule.name,
                base_values,
                bindings,
                term,
                expected,
            )?);
        }
        return Ok((
            vec![DirectEffect::Set {
                target: *target,
                target_arity: target_info.arity(),
                target_n_keys: target_info.n_keys,
                target_write_capability: target_info.write_capability,
                column_offset: 0,
            }],
            select_expressions,
        ));
    }

    if is_delete_only(rule) {
        let mut effects = Vec::with_capacity(rule.core.head.0.len());
        let mut select_expressions = Vec::new();
        for action in &rule.core.head.0 {
            let GenericCoreAction::Change(_, Change::Delete, call, arguments) = action else {
                unreachable!();
            };
            let RuleActionCall::Table { id: target, .. } = call else {
                bail!(
                    "DuckDB rule `{}` attempts to delete a primitive; Delete requires a table target",
                    rule.name
                );
            };
            let target_info = action_table_info(storage, &rule.name, *target)?;
            validate_change_key(&rule.name, &target_info, arguments)?;
            let column_offset = select_expressions.len();
            for (term, &expected) in arguments.iter().zip(&target_info.schema) {
                select_expressions.push(head_expression(
                    &rule.name,
                    base_values,
                    bindings,
                    term,
                    expected,
                )?);
            }
            effects.push(DirectEffect::Delete {
                target: *target,
                target_n_keys: target_info.n_keys,
                column_offset,
            });
        }
        return Ok((effects, select_expressions));
    }

    if rule.core.head.0.len() == 1
        && let GenericCoreAction::Change(_, Change::Subsume, call, arguments) = &rule.core.head.0[0]
    {
        let RuleActionCall::Table { id: target, .. } = call else {
            bail!(
                "DuckDB rule `{}` attempts to subsume a primitive; Subsume requires a table target",
                rule.name
            );
        };
        let target_info = action_table_info(storage, &rule.name, *target)?;
        validate_change_key(&rule.name, &target_info, arguments)?;
        if !target_info.can_subsume {
            bail!(
                "DuckDB rule `{}` target `{}` does not support subsumption",
                rule.name,
                target_info.name
            );
        }
        let body = body_tables
            .iter()
            .find(|body| {
                body.id == *target
                    && body.args[..target_info.n_keys]
                        .iter()
                        .zip(arguments)
                        .all(|(body, action)| same_rule_term(body, action))
            })
            .ok_or_else(|| {
                anyhow!(
                    "DuckDB rule `{}` Subsume target `{}` requires a complete Live body row with identical keys",
                    rule.name,
                    target_info.name
                )
            })?;
        let select_expressions = (0..target_info.arity())
            .map(|column| format!("{}.c{column}", body.alias))
            .collect();
        return Ok((
            vec![DirectEffect::Subsume {
                target: *target,
                target_arity: target_info.arity(),
                target_n_keys: target_info.n_keys,
                column_offset: 0,
            }],
            select_expressions,
        ));
    }

    bail!(
        "DuckDB rule `{}` has an unsupported action language; expected exactly one Set, a nonempty Delete-only head, or exactly one body-bound Subsume",
        rule.name
    )
}

fn is_delete_only(rule: &RuleSpec) -> bool {
    !rule.core.head.0.is_empty()
        && rule
            .core
            .head
            .0
            .iter()
            .all(|action| matches!(action, GenericCoreAction::Change(_, Change::Delete, _, _)))
}

fn action_table_info(storage: &Storage, rule_name: &str, target: FunctionId) -> Result<TableInfo> {
    storage.table_info(target).map_err(|error| {
        anyhow!(
            "DuckDB rule `{rule_name}` references an invalid target table {}: {error:#}",
            target.rep()
        )
    })
}

fn validate_change_key(
    rule_name: &str,
    target: &TableInfo,
    arguments: &[GenericAtomTerm<RuleVar, RuleValue>],
) -> Result<()> {
    if arguments.len() != target.n_keys {
        bail!(
            "DuckDB rule `{rule_name}` target `{}` requires {} key term(s), got {}",
            target.name,
            target.n_keys,
            arguments.len()
        );
    }
    Ok(())
}

fn same_rule_term(
    lhs: &GenericAtomTerm<RuleVar, RuleValue>,
    rhs: &GenericAtomTerm<RuleVar, RuleValue>,
) -> bool {
    match (lhs, rhs) {
        (GenericAtomTerm::Var(_, lhs), GenericAtomTerm::Var(_, rhs)) => lhs == rhs,
        (GenericAtomTerm::Literal(_, lhs), GenericAtomTerm::Literal(_, rhs)) => lhs == rhs,
        (GenericAtomTerm::Global(_, lhs), GenericAtomTerm::Global(_, rhs)) => lhs == rhs,
        _ => false,
    }
}

fn qualified_column_range(alias: &str, offset: usize, len: usize) -> String {
    (offset..offset + len)
        .map(|column| format!("{alias}.c{column}"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn stage_key_equality(
    existing_alias: &str,
    stage_alias: &str,
    stage_offset: usize,
    n_keys: usize,
) -> String {
    if n_keys == 0 {
        return "TRUE".to_string();
    }
    (0..n_keys)
        .map(|column| {
            format!(
                "{existing_alias}.c{column} IS NOT DISTINCT FROM {stage_alias}.c{}",
                stage_offset + column
            )
        })
        .collect::<Vec<_>>()
        .join(" AND ")
}

fn validate_target(
    rule_name: &str,
    target: &TableInfo,
    argument_count: usize,
    value_count: usize,
) -> Result<()> {
    if argument_count != target.n_keys || value_count != 1 || target.arity() != target.n_keys + 1 {
        bail!(
            "DuckDB rule `{rule_name}` target `{}` requires {} key and one value term; got {argument_count} key and {value_count} value terms",
            target.name,
            target.n_keys
        );
    }
    if target.write_capability == WriteCapability::Deferred {
        bail!(
            "DuckDB rule `{rule_name}` target `{}` has a registered but deferred merge capability",
            target.name
        );
    }
    Ok(())
}

fn validate_variable(rule_name: &str, variable: &RuleVar, expected: ColumnTy) -> Result<()> {
    if variable.ty != expected {
        bail!(
            "DuckDB rule `{rule_name}` variable `{}` has type {:?}, expected {:?}",
            variable.name,
            variable.ty,
            expected
        );
    }
    Ok(())
}

fn validate_literal(rule_name: &str, literal: &RuleValue, expected: ColumnTy) -> Result<()> {
    if literal.ty != expected {
        bail!(
            "DuckDB rule `{rule_name}` literal has type {:?}, expected {:?}",
            literal.ty,
            expected
        );
    }
    Ok(())
}

fn head_expression(
    rule_name: &str,
    base_values: &BaseValues,
    bindings: &BTreeMap<u32, VariableBinding>,
    term: &GenericAtomTerm<RuleVar, RuleValue>,
    expected: ColumnTy,
) -> Result<String> {
    match term {
        GenericAtomTerm::Var(_, variable) => {
            validate_variable(rule_name, variable, expected)?;
            let binding = bindings.get(&variable.id).ok_or_else(|| {
                anyhow!(
                    "DuckDB rule `{rule_name}` head variable `{}` is not bound by its body",
                    variable.name
                )
            })?;
            if binding.ty != variable.ty || binding.name != variable.name {
                bail!(
                    "DuckDB rule `{rule_name}` reuses variable id {} with inconsistent metadata",
                    variable.id
                );
            }
            Ok(binding.expression.clone())
        }
        GenericAtomTerm::Literal(_, literal) => {
            validate_literal(rule_name, literal, expected)?;
            ScalarSqlType::from_column(base_values, expected)?
                .sql_literal(base_values, literal.value)
        }
        GenericAtomTerm::Global(..) => bail!(
            "DuckDB rule `{rule_name}` contains a global head term; globals must be desugared"
        ),
    }
}
