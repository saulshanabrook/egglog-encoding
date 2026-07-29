//! Closed lowering for generated scalar marker-rekey rules.
//!
//! Marker rows are ordinary typed function rows. This compiler recognizes the
//! exact rule/config topology without consulting generated names, then emits a
//! small immutable SQL plan for the combined rebuilding executor.

use std::collections::{BTreeMap, BTreeSet};

use crate::rebuild::{
    OrderedUnionPlan, ordered_union_outer, safe_scratch_name, validate_marker_union_find,
};
use crate::storage::{ScalarSqlType, Storage, TableInfo, WriteCapability, sql_table};
use anyhow::{Result, anyhow, bail, ensure};
use egglog_ast::core::{GenericAtomTerm, GenericCoreAction};
use egglog_ast::generic_ast::Change;
use egglog_backend_trait::{
    BaseValues, ColumnTy, DefaultVal, ExternalFunctionId, FunctionId, MergeFn, NativePrimitive,
    ReadMode, RuleActionCall, RuleBodyCall, RuleSpec, RuleValue, RuleVar,
};

/// A fully validated scalar marker-rekey rule.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct MarkerRekeyPlan {
    pub(crate) seminaive: bool,
    pub(crate) marker: FunctionId,
    pub(crate) marker_columns: Vec<ScalarSqlType>,
    pub(crate) n_keys: usize,
    pub(crate) key_index: usize,
    pub(crate) union_find: OrderedUnionPlan,
}

impl MarkerRekeyPlan {
    pub(crate) fn materialize_sql(&self, stage: &str, watermark: u64) -> String {
        debug_assert!(safe_scratch_name(stage));
        let marker = sql_table(self.marker);
        let union_find = sql_table(self.union_find.target);
        let freshness = if self.seminaive {
            format!(
                "AND (marker_row.__generation >= CAST('{watermark}' AS UBIGINT)\n                       OR uf_row.__generation >= CAST('{watermark}' AS UBIGINT))"
            )
        } else {
            String::new()
        };
        let mut bindings = (0..self.n_keys)
            .map(|column| format!("marker_row.c{column} AS c{column}"))
            .collect::<Vec<_>>();
        bindings.push(format!("uf_row.c1 AS c{}", self.n_keys));
        let order = (0..=self.n_keys)
            .map(|column| format!("c{column}"))
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            "CREATE TEMP TABLE {stage} AS
             WITH bindings AS (
                 SELECT DISTINCT {}
                 FROM {marker} AS marker_row
                 JOIN {union_find} AS uf_row
                   ON marker_row.c{} IS NOT DISTINCT FROM uf_row.c0
                 WHERE marker_row.c{} IS DISTINCT FROM uf_row.c1
                   {freshness}
             )
             SELECT bindings.*,
                    row_number() OVER (ORDER BY {order}) AS __match_ordinal
             FROM bindings",
            bindings.join(", "),
            self.key_index,
            self.key_index,
        )
    }

    pub(crate) fn delete_sql(&self, stage: &str) -> String {
        debug_assert!(safe_scratch_name(stage));
        let equality = key_equality("existing", "staged", self.n_keys);
        format!(
            "DELETE FROM {} AS existing
             WHERE EXISTS (SELECT 1 FROM {stage} AS staged WHERE {equality})",
            sql_table(self.marker)
        )
    }

    pub(crate) fn create_head_stage_sql(&self, stage: &str, head_stage: &str) -> String {
        debug_assert!(safe_scratch_name(stage));
        debug_assert!(safe_scratch_name(head_stage));
        let canonical = self.n_keys;
        let mut values = (0..self.n_keys)
            .map(|column| {
                if column == self.key_index {
                    format!("c{canonical} AS c{column}")
                } else {
                    format!("c{column}")
                }
            })
            .collect::<Vec<_>>();
        values.push(format!("CAST(TRUE AS BOOLEAN) AS c{}", self.n_keys));
        format!(
            "CREATE TEMP TABLE {head_stage} AS
             SELECT {}, __match_ordinal AS __ordinal
             FROM {stage}",
            values.join(", ")
        )
    }

    pub(crate) fn arity(&self) -> usize {
        self.marker_columns.len()
    }
}

/// Tri-state admission: `None` is an unrelated family, `Some` is a completely
/// validated marker rule, and `Err` is a malformed selected marker family.
pub(crate) fn compile_marker_rekey(
    storage: &Storage,
    base_values: &BaseValues,
    native_primitives: &BTreeMap<ExternalFunctionId, NativePrimitive>,
    fresh_tokens: &BTreeSet<ExternalFunctionId>,
    rule: &RuleSpec,
) -> Result<Option<MarkerRekeyPlan>> {
    let Some(selected) = select_outer_family(storage, rule)? else {
        return Ok(None);
    };
    compile_selected(
        storage,
        base_values,
        native_primitives,
        fresh_tokens,
        rule,
        selected,
    )
    .map(Some)
}

struct SelectedOuter<'a> {
    marker_atom: &'a egglog_ast::core::GenericAtom<RuleBodyCall, RuleVar, RuleValue>,
    union_find_atom: &'a egglog_ast::core::GenericAtom<RuleBodyCall, RuleVar, RuleValue>,
    inequality: &'a egglog_ast::core::GenericAtom<RuleBodyCall, RuleVar, RuleValue>,
    marker: FunctionId,
    union_find: FunctionId,
}

fn select_outer_family<'a>(
    storage: &Storage,
    rule: &'a RuleSpec,
) -> Result<Option<SelectedOuter<'a>>> {
    if rule.core.body.atoms.len() != 3 {
        return Ok(None);
    }
    let tables = rule
        .core
        .body
        .atoms
        .iter()
        .filter(|atom| matches!(atom.head, RuleBodyCall::Table { .. }))
        .collect::<Vec<_>>();
    let primitives = rule
        .core
        .body
        .atoms
        .iter()
        .filter(|atom| matches!(atom.head, RuleBodyCall::Primitive { .. }))
        .collect::<Vec<_>>();
    let ([first, second], [inequality]) = (tables.as_slice(), primitives.as_slice()) else {
        return Ok(None);
    };
    let [first_action, second_action] = rule.core.head.0.as_slice() else {
        return Ok(None);
    };
    let action_shape = matches!(first_action, GenericCoreAction::Set(..))
        && matches!(second_action, GenericCoreAction::Change(..))
        || matches!(first_action, GenericCoreAction::Change(..))
            && matches!(second_action, GenericCoreAction::Set(..));
    if !action_shape {
        return Ok(None);
    }

    let first_id = table_atom_id(first);
    let second_id = table_atom_id(second);
    let first_info = storage.table_info(first_id)?;
    let second_info = storage.table_info(second_id)?;
    match (
        ordered_union_outer(&first_info.merge),
        ordered_union_outer(&second_info.merge),
    ) {
        (Some(_), None) => Ok(Some(SelectedOuter {
            marker_atom: second,
            union_find_atom: first,
            inequality,
            marker: second_id,
            union_find: first_id,
        })),
        (None, Some(_)) => Ok(Some(SelectedOuter {
            marker_atom: first,
            union_find_atom: second,
            inequality,
            marker: first_id,
            union_find: second_id,
        })),
        (None, None) | (Some(_), Some(_)) => Ok(None),
    }
}

fn compile_selected(
    storage: &Storage,
    base_values: &BaseValues,
    native_primitives: &BTreeMap<ExternalFunctionId, NativePrimitive>,
    fresh_tokens: &BTreeSet<ExternalFunctionId>,
    rule: &RuleSpec,
    selected: SelectedOuter<'_>,
) -> Result<MarkerRekeyPlan> {
    ensure!(
        rule.seminaive && !rule.no_decomp,
        "DuckDB marker rekey rule `{}` must be seminaive and decomposed",
        rule.name
    );
    let marker_info = storage.table_info(selected.marker)?;
    validate_marker_table(base_values, &rule.name, &marker_info)?;
    let union_find = validate_marker_union_find(
        base_values,
        storage,
        native_primitives,
        fresh_tokens,
        &rule.name,
        selected.union_find,
    )?;

    let (_, marker_read, marker_terms) = table_atom_parts(selected.marker_atom);
    let (_, union_find_read, union_find_terms) = table_atom_parts(selected.union_find_atom);
    ensure!(
        marker_read == ReadMode::All && union_find_read == ReadMode::All,
        "DuckDB marker rekey rule `{}` requires All table atoms",
        rule.name
    );
    ensure!(
        marker_terms.len() == marker_info.arity(),
        "DuckDB marker rekey rule `{}` marker atom has the wrong arity",
        rule.name
    );
    let key_vars = marker_terms[..marker_info.n_keys]
        .iter()
        .zip(&marker_info.schema[..marker_info.n_keys])
        .map(|(term, &ty)| typed_var(&rule.name, term, ty))
        .collect::<Result<Vec<_>>>()?;
    let marker_output = typed_var(
        &rule.name,
        &marker_terms[marker_info.n_keys],
        marker_info.schema[marker_info.n_keys],
    )?;
    ensure!(
        ScalarSqlType::from_column(base_values, marker_output.ty)? == ScalarSqlType::Unit,
        "DuckDB marker rekey rule `{}` marker body output must have Unit type",
        rule.name
    );

    let [union_find_key, canonical, union_find_payload] = union_find_terms else {
        bail!(
            "DuckDB marker rekey rule `{}` UF atom must have three Id variables",
            rule.name
        );
    };
    let union_find_key = id_var(&rule.name, union_find_key)?;
    let canonical = id_var(&rule.name, canonical)?;
    let union_find_payload = id_var(&rule.name, union_find_payload)?;
    let key_positions = key_vars
        .iter()
        .enumerate()
        .filter_map(|(index, key)| same_var_value(key, union_find_key).then_some(index))
        .collect::<Vec<_>>();
    let [key_index] = key_positions.as_slice() else {
        bail!(
            "DuckDB marker rekey rule `{}` UF key must be exactly one marker key",
            rule.name
        );
    };
    ensure!(
        marker_info.schema[*key_index] == ColumnTy::Id,
        "DuckDB marker rekey rule `{}` selected key must have Id type",
        rule.name
    );
    let inequality_result = validate_inequality(
        base_values,
        native_primitives,
        &rule.name,
        selected.inequality,
        union_find_key,
        canonical,
    )?;
    let mut body_vars = key_vars.clone();
    body_vars.extend([
        marker_output,
        canonical,
        union_find_payload,
        inequality_result,
    ]);
    distinct_vars(&rule.name, &body_vars)?;

    let [set_action, delete_action] = rule.core.head.0.as_slice() else {
        bail!(
            "DuckDB marker rekey rule `{}` must have exactly Set then Delete",
            rule.name
        );
    };
    validate_marker_set(
        base_values,
        &rule.name,
        set_action,
        selected.marker,
        &key_vars,
        *key_index,
        canonical,
    )?;
    validate_marker_delete(&rule.name, delete_action, selected.marker, &key_vars)?;

    Ok(MarkerRekeyPlan {
        seminaive: rule.seminaive,
        marker: selected.marker,
        marker_columns: marker_info.columns,
        n_keys: marker_info.n_keys,
        key_index: *key_index,
        union_find,
    })
}

fn validate_marker_table(
    base_values: &BaseValues,
    rule_name: &str,
    info: &TableInfo,
) -> Result<()> {
    ensure!(
        info.n_keys >= 1
            && info.n_vals == 1
            && info.arity() == info.n_keys + 1
            && info.n_identity_vals.is_none()
            && matches!(info.default, DefaultVal::Fail)
            && matches!(info.merge.as_ref(), MergeFn::AssertEq)
            && info.write_capability == WriteCapability::AssertEq
            && !info.can_subsume,
        "DuckDB marker rekey rule `{rule_name}` marker has an incompatible configuration"
    );
    for &ty in &info.schema[..info.n_keys] {
        ScalarSqlType::from_column(base_values, ty)?;
    }
    ensure!(
        ScalarSqlType::from_column(base_values, info.schema[info.n_keys])? == ScalarSqlType::Unit,
        "DuckDB marker rekey rule `{rule_name}` marker output must have Unit type"
    );
    Ok(())
}

fn validate_inequality<'a>(
    base_values: &BaseValues,
    native_primitives: &BTreeMap<ExternalFunctionId, NativePrimitive>,
    rule_name: &str,
    atom: &'a egglog_ast::core::GenericAtom<RuleBodyCall, RuleVar, RuleValue>,
    stale: &RuleVar,
    canonical: &RuleVar,
) -> Result<&'a RuleVar> {
    let RuleBodyCall::Primitive { id, name, output } = &atom.head else {
        unreachable!("selected primitive atom")
    };
    ensure!(
        native_primitives.get(id) == Some(&NativePrimitive::ValueNeq)
            && ScalarSqlType::from_column(base_values, *output)? == ScalarSqlType::Unit,
        "DuckDB marker rekey rule `{rule_name}` requires authenticated ValueNeq (diagnostic name `{name}`) with (Id, Id) -> Unit"
    );
    let [lhs, rhs, result] = atom.args.as_slice() else {
        bail!("DuckDB marker rekey rule `{rule_name}` inequality has the wrong arity");
    };
    same_var(rule_name, stale, id_var(rule_name, lhs)?, "inequality lhs")?;
    same_var(
        rule_name,
        canonical,
        id_var(rule_name, rhs)?,
        "inequality rhs",
    )?;
    let result = typed_var(rule_name, result, *output)?;
    Ok(result)
}

fn validate_marker_set(
    base_values: &BaseValues,
    rule_name: &str,
    action: &GenericCoreAction<RuleActionCall, RuleVar, RuleValue>,
    marker: FunctionId,
    keys: &[&RuleVar],
    key_index: usize,
    canonical: &RuleVar,
) -> Result<()> {
    let GenericCoreAction::Set(_, call, arguments, values) = action else {
        bail!("DuckDB marker rekey rule `{rule_name}` first action must be Set");
    };
    ensure!(table_action(rule_name, call, "canonical marker Set")? == marker);
    ensure!(
        arguments.len() == keys.len(),
        "DuckDB marker rekey rule `{rule_name}` marker Set has the wrong key arity"
    );
    for (index, (argument, original)) in arguments.iter().zip(keys).enumerate() {
        let expected = if index == key_index {
            canonical
        } else {
            *original
        };
        same_var(
            rule_name,
            expected,
            typed_var(rule_name, argument, expected.ty)?,
            "canonical marker key",
        )?;
    }
    let [value] = values.as_slice() else {
        bail!("DuckDB marker rekey rule `{rule_name}` marker Set must have one Unit value");
    };
    unit_literal(base_values, rule_name, value)
}

fn validate_marker_delete(
    rule_name: &str,
    action: &GenericCoreAction<RuleActionCall, RuleVar, RuleValue>,
    marker: FunctionId,
    keys: &[&RuleVar],
) -> Result<()> {
    let GenericCoreAction::Change(_, change, call, arguments) = action else {
        bail!("DuckDB marker rekey rule `{rule_name}` second action must be Delete");
    };
    ensure!(
        *change == Change::Delete,
        "DuckDB marker rekey rule `{rule_name}` second action must be Delete"
    );
    ensure!(table_action(rule_name, call, "stale marker Delete")? == marker);
    ensure!(
        arguments.len() == keys.len(),
        "DuckDB marker rekey rule `{rule_name}` marker Delete has the wrong key arity"
    );
    for (argument, expected) in arguments.iter().zip(keys) {
        same_var(
            rule_name,
            expected,
            typed_var(rule_name, argument, expected.ty)?,
            "stale marker key",
        )?;
    }
    Ok(())
}

fn table_atom_id(
    atom: &egglog_ast::core::GenericAtom<RuleBodyCall, RuleVar, RuleValue>,
) -> FunctionId {
    let RuleBodyCall::Table { id, .. } = atom.head else {
        unreachable!("selected table atom")
    };
    id
}

fn table_atom_parts(
    atom: &egglog_ast::core::GenericAtom<RuleBodyCall, RuleVar, RuleValue>,
) -> (FunctionId, ReadMode, &[GenericAtomTerm<RuleVar, RuleValue>]) {
    let RuleBodyCall::Table { id, read } = atom.head else {
        unreachable!("selected table atom")
    };
    (id, read, &atom.args)
}

fn table_action(rule_name: &str, call: &RuleActionCall, role: &str) -> Result<FunctionId> {
    let RuleActionCall::Table { id, .. } = call else {
        bail!("DuckDB marker rekey rule `{rule_name}` {role} must target a table");
    };
    Ok(*id)
}

fn unit_literal(
    base_values: &BaseValues,
    rule_name: &str,
    term: &GenericAtomTerm<RuleVar, RuleValue>,
) -> Result<()> {
    let GenericAtomTerm::Literal(_, value) = term else {
        bail!("DuckDB marker rekey rule `{rule_name}` requires a Unit literal");
    };
    ensure!(
        ScalarSqlType::from_column(base_values, value.ty)? == ScalarSqlType::Unit,
        "DuckDB marker rekey rule `{rule_name}` requires a Unit literal"
    );
    ScalarSqlType::Unit.sql_literal(base_values, value.value)?;
    Ok(())
}

fn typed_var<'a>(
    rule_name: &str,
    term: &'a GenericAtomTerm<RuleVar, RuleValue>,
    expected: ColumnTy,
) -> Result<&'a RuleVar> {
    let GenericAtomTerm::Var(_, variable) = term else {
        return Err(anyhow!(
            "DuckDB marker rekey rule `{rule_name}` requires variables"
        ));
    };
    ensure!(
        variable.ty == expected,
        "DuckDB marker rekey rule `{rule_name}` has a variable with the wrong type"
    );
    Ok(variable)
}

fn id_var<'a>(
    rule_name: &str,
    term: &'a GenericAtomTerm<RuleVar, RuleValue>,
) -> Result<&'a RuleVar> {
    typed_var(rule_name, term, ColumnTy::Id)
}

fn same_var_value(expected: &RuleVar, actual: &RuleVar) -> bool {
    expected.id == actual.id && expected.ty == actual.ty
}

fn same_var(rule_name: &str, expected: &RuleVar, actual: &RuleVar, role: &str) -> Result<()> {
    ensure!(
        same_var_value(expected, actual),
        "DuckDB marker rekey rule `{rule_name}` has inconsistent {role} variables"
    );
    Ok(())
}

fn distinct_vars(rule_name: &str, variables: &[&RuleVar]) -> Result<()> {
    for (index, left) in variables.iter().enumerate() {
        ensure!(
            variables[index + 1..]
                .iter()
                .all(|right| left.id != right.id),
            "DuckDB marker rekey rule `{rule_name}` aliases structurally distinct variables"
        );
    }
    Ok(())
}

fn key_equality(left: &str, right: &str, n_keys: usize) -> String {
    debug_assert_ne!(n_keys, 0);
    (0..n_keys)
        .map(|column| format!("{left}.c{column} IS NOT DISTINCT FROM {right}.c{column}"))
        .collect::<Vec<_>>()
        .join(" AND ")
}
