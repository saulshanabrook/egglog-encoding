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
use egglog_backend_trait::{
    BaseValues, ColumnTy, FunctionId, ReadMode, RuleActionCall, RuleBodyCall, RuleSpec, RuleValue,
    RuleVar,
};
use egglog_numeric_id::NumericId;

use crate::storage::{
    ScalarSqlType, Storage, TableInfo, WriteCapability, assert_eq_conflict_sql, qualified_columns,
    sql_table, visible_columns,
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
    target: FunctionId,
    target_arity: usize,
    target_n_keys: usize,
    target_write_capability: WriteCapability,
    select_expressions: Vec<String>,
    from: Vec<String>,
    predicates: Vec<String>,
    freshness_columns: Vec<String>,
    order_columns: Vec<String>,
}

impl CompiledRule {
    pub(crate) fn materialize_sql(&self, stage: &str, watermark: u64) -> String {
        debug_assert!(
            stage
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        );
        let mut predicates = self.predicates.clone();
        if self.seminaive {
            predicates.push(format!(
                "({})",
                self.freshness_columns
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
        let projection = self
            .select_expressions
            .iter()
            .enumerate()
            .map(|(column, expression)| format!("{expression} AS c{column}"))
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            "CREATE TEMP TABLE {stage} AS
             SELECT {projection},
                    row_number() OVER (ORDER BY {}) AS __match_ordinal
             FROM {}
             WHERE {predicate}",
            self.order_columns.join(", "),
            self.from.join(" CROSS JOIN ")
        )
    }

    pub(crate) fn insert_sql(&self, stage: &str, generation: u64) -> String {
        debug_assert!(
            stage
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        );
        let partition = if self.target_n_keys == 0 {
            "ORDER BY staged.__match_ordinal".to_string()
        } else {
            format!(
                "PARTITION BY {} ORDER BY staged.__match_ordinal",
                qualified_columns("staged", self.target_n_keys)
            )
        };
        let no_existing = if self.target_n_keys == 0 {
            format!("NOT EXISTS (SELECT 1 FROM {})", sql_table(self.target))
        } else {
            let equality = (0..self.target_n_keys)
                .map(|column| format!("existing.c{column} IS NOT DISTINCT FROM ranked.c{column}"))
                .collect::<Vec<_>>()
                .join(" AND ");
            format!(
                "NOT EXISTS (SELECT 1 FROM {} AS existing WHERE {equality})",
                sql_table(self.target)
            )
        };

        format!(
            "INSERT INTO {} ({}, __generation, __subsumed)
             SELECT {}, CAST('{generation}' AS UBIGINT), FALSE
             FROM (
                 SELECT staged.*,
                        row_number() OVER ({partition}) AS __key_rank
                 FROM {stage} AS staged
             ) AS ranked
             WHERE ranked.__key_rank = 1 AND {no_existing}",
            sql_table(self.target),
            visible_columns(self.target_arity),
            qualified_columns("ranked", self.target_arity),
        )
    }

    pub(crate) fn conflict_sql(&self, stage: &str) -> Option<String> {
        (self.target_write_capability == WriteCapability::AssertEq)
            .then(|| assert_eq_conflict_sql(self.target, self.target_n_keys, stage))
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
    if rule.core.body.atoms.is_empty() {
        bail!("DuckDB rule `{}` has an empty body", rule.name);
    }
    if rule.core.head.0.len() != 1 {
        bail!(
            "DuckDB rule `{}` must contain exactly one Set action, found {} actions",
            rule.name,
            rule.core.head.0.len()
        );
    }

    let mut bindings = BTreeMap::<u32, VariableBinding>::new();
    let mut from = Vec::with_capacity(rule.core.body.atoms.len());
    let mut predicates = Vec::new();
    let mut freshness_columns = Vec::with_capacity(rule.core.body.atoms.len());
    let mut order_columns = Vec::new();

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

    let GenericCoreAction::Set(_, call, arguments, values) = &rule.core.head.0[0] else {
        bail!(
            "DuckDB rule `{}` has an unsupported action; exactly one table Set is required",
            rule.name
        );
    };
    let RuleActionCall::Table { id: target, .. } = call else {
        bail!(
            "DuckDB rule `{}` attempts to set a primitive; exactly one table Set is required",
            rule.name
        );
    };
    let target_info = storage.table_info(*target).map_err(|error| {
        anyhow!(
            "DuckDB rule `{}` references an invalid target table {}: {error:#}",
            rule.name,
            target.rep()
        )
    })?;
    validate_target(&rule.name, &target_info, arguments.len(), values.len())?;

    let mut select_expressions = Vec::with_capacity(target_info.arity());
    for (term, &expected) in arguments.iter().chain(values).zip(&target_info.schema) {
        select_expressions.push(head_expression(
            &rule.name,
            base_values,
            &bindings,
            term,
            expected,
        )?);
    }

    Ok(CompiledRule {
        seminaive: rule.seminaive,
        target: *target,
        target_arity: target_info.arity(),
        target_n_keys: target_info.n_keys,
        target_write_capability: target_info.write_capability,
        select_expressions,
        from,
        predicates,
        freshness_columns,
        order_columns,
    })
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
