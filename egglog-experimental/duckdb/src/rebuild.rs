//! Closed lowering for the two standard scalar term/proof rebuild rules.
//!
//! Admission is deliberately structural. Generated rule, function, table,
//! sort, variable, and proof names are never consulted. A matching outer
//! topology is either accepted in full or rejected as malformed; unrelated
//! marker, container, and custom-merge topologies fall through to the ordinary
//! closed rule compiler.

use anyhow::{Result, anyhow, bail, ensure};
use egglog_ast::core::{GenericAtomTerm, GenericCoreAction};
use egglog_ast::generic_ast::Change;
use egglog_backend_trait::{
    BaseValues, ColumnTy, DefaultVal, FunctionId, MergeAction, MergeFn, ReadMode, RuleActionCall,
    RuleBodyCall, RuleSpec, RuleValue, RuleVar,
};

use crate::storage::{ScalarSqlType, Storage, TableInfo, WriteCapability, sql_table};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum OrderedUnionOrientation {
    /// The carried payload proves `key = parent`.
    KeyToParent,
    /// The carried payload proves `eclass = term`.
    EclassToTerm,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OrderedUnionPlan {
    pub(crate) target: FunctionId,
    pub(crate) displaced_target: FunctionId,
    pub(crate) sym: FunctionId,
    pub(crate) trans: FunctionId,
    pub(crate) orientation: OrderedUnionOrientation,
    pub(crate) columns: Vec<ScalarSqlType>,
    pub(crate) n_keys: usize,
}

impl OrderedUnionPlan {
    pub(crate) fn arity(&self) -> usize {
        self.columns.len()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum StandardRebuildKind {
    EqKey {
        key_index: usize,
        child_index_sql: String,
        congr: FunctionId,
    },
    EclassOutput {
        sym: FunctionId,
        trans: FunctionId,
    },
}

impl StandardRebuildKind {
    pub(crate) fn head_fresh_slots(&self) -> u64 {
        match self {
            Self::EqKey { .. } => 1,
            Self::EclassOutput { .. } => 2,
        }
    }
}

/// A fully validated standard scalar rebuild rule.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StandardRebuildPlan {
    pub(crate) seminaive: bool,
    pub(crate) view: OrderedUnionPlan,
    /// The UF joined by the rule body to canonicalize the stale key/value.
    pub(crate) union_find: OrderedUnionPlan,
    /// The output-sort UF which receives collisions displaced by the View.
    /// This differs from `union_find` when an eq-key rule rebuilds a key whose
    /// sort differs from the View's output sort.
    pub(crate) displaced_union_find: OrderedUnionPlan,
    pub(crate) kind: StandardRebuildKind,
}

impl StandardRebuildPlan {
    pub(crate) fn materialize_sql(&self, stage: &str, watermark: u64) -> String {
        debug_assert!(safe_scratch_name(stage));
        let view = sql_table(self.view.target);
        let union_find = sql_table(self.union_find.target);
        let view_arity = self.view.arity();
        let stale_column = match self.kind {
            StandardRebuildKind::EqKey { key_index, .. } => key_index,
            StandardRebuildKind::EclassOutput { .. } => self.view.n_keys,
        };
        let freshness = if self.seminaive {
            format!(
                "AND (view_row.__generation >= CAST('{watermark}' AS UBIGINT)\n                       OR uf_row.__generation >= CAST('{watermark}' AS UBIGINT))"
            )
        } else {
            String::new()
        };
        let mut bindings = (0..view_arity)
            .map(|column| format!("view_row.c{column} AS c{column}"))
            .collect::<Vec<_>>();
        bindings.push(format!("uf_row.c1 AS c{view_arity}"));
        bindings.push(format!("uf_row.c2 AS c{}", view_arity + 1));
        let order = (0..view_arity + 2)
            .map(|column| format!("c{column}"))
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            "CREATE TEMP TABLE {stage} AS
             WITH bindings AS (
                 SELECT DISTINCT {}
                 FROM {view} AS view_row
                 JOIN {union_find} AS uf_row
                   ON view_row.c{stale_column} IS NOT DISTINCT FROM uf_row.c0
                 WHERE view_row.c{stale_column} IS DISTINCT FROM uf_row.c1
                   {freshness}
             )
             SELECT bindings.*,
                    row_number() OVER (ORDER BY {order}) AS __match_ordinal
             FROM bindings",
            bindings.join(", ")
        )
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum OuterShape {
    EqKey,
    EclassOutput,
}

/// Tri-state admission: `None` is a different outer topology, `Some` is a
/// completely validated standard rebuild plan, and `Err` is a malformed
/// instance of one of the two standard outer topologies.
pub(crate) fn compile_standard_rebuild(
    storage: &Storage,
    base_values: &BaseValues,
    rule: &RuleSpec,
) -> Result<Option<StandardRebuildPlan>> {
    let Some(shape) = outer_shape(rule) else {
        return Ok(None);
    };
    compile_selected(storage, base_values, rule, shape)
}

fn outer_shape(rule: &RuleSpec) -> Option<OuterShape> {
    if rule.core.body.atoms.len() != 3 {
        return None;
    }
    let table_atoms = rule
        .core
        .body
        .atoms
        .iter()
        .filter(|atom| matches!(atom.head, RuleBodyCall::Table { .. }))
        .count();
    let primitive_atoms = rule
        .core
        .body
        .atoms
        .iter()
        .filter(|atom| matches!(atom.head, RuleBodyCall::Primitive { .. }))
        .count();
    if table_atoms != 2 || primitive_atoms != 1 {
        return None;
    }
    match rule.core.head.0.as_slice() {
        [
            GenericCoreAction::Let(..),
            GenericCoreAction::LetAtomTerm(..),
            GenericCoreAction::Set(..),
            GenericCoreAction::Set(..),
            GenericCoreAction::Change(..),
        ] => Some(OuterShape::EqKey),
        [
            GenericCoreAction::Let(..),
            GenericCoreAction::LetAtomTerm(..),
            GenericCoreAction::Set(..),
            GenericCoreAction::Let(..),
            GenericCoreAction::LetAtomTerm(..),
            GenericCoreAction::Set(..),
            GenericCoreAction::Set(..),
        ] => Some(OuterShape::EclassOutput),
        _ => None,
    }
}

fn compile_selected(
    storage: &Storage,
    base_values: &BaseValues,
    rule: &RuleSpec,
    shape: OuterShape,
) -> Result<Option<StandardRebuildPlan>> {
    let mut table_atoms = rule
        .core
        .body
        .atoms
        .iter()
        .filter(|atom| matches!(atom.head, RuleBodyCall::Table { .. }));
    let first_table = table_atoms.next().expect("outer shape checked tables");
    let second_table = table_atoms.next().expect("outer shape checked tables");
    let inequality = rule
        .core
        .body
        .atoms
        .iter()
        .find(|atom| matches!(atom.head, RuleBodyCall::Primitive { .. }))
        .expect("outer shape checked primitive");
    let first_id = match first_table.head {
        RuleBodyCall::Table { id, .. } => id,
        RuleBodyCall::Primitive { .. } => unreachable!(),
    };
    let second_id = match second_table.head {
        RuleBodyCall::Table { id, .. } => id,
        RuleBodyCall::Primitive { .. } => unreachable!(),
    };
    let first_info = storage.table_info(first_id)?;
    let second_info = storage.table_info(second_id)?;
    let (view_atom, uf_atom) = match (first_info.can_subsume, second_info.can_subsume) {
        (true, false) => (first_table, second_table),
        (false, true) => (second_table, first_table),
        _ => return Ok(None),
    };
    let (view_id, view_read, view_terms) = table_atom_parts(view_atom);
    let (uf_id, uf_read, uf_terms) = table_atom_parts(uf_atom);

    let view_info = storage.table_info(view_id)?;
    let Some(view_displaced) = ordered_union_outer(&view_info.merge) else {
        return Ok(None);
    };
    let uf_info = storage.table_info(uf_id)?;
    if ordered_union_outer(&uf_info.merge).is_none() {
        return Ok(None);
    }
    let displaced_info = storage.table_info(view_displaced)?;
    if ordered_union_outer(&displaced_info.merge).is_none() {
        return Ok(None);
    }

    // Only the complete ordered-union family owns this tri-state branch. From
    // here onward, any deviation is a malformed standard rebuild rather than
    // a different custom/marker/container topology.
    ensure!(
        rule.seminaive && !rule.no_decomp,
        "DuckDB standard rebuild rule `{}` must be seminaive and decomposed",
        rule.name
    );
    ensure!(
        view_id != uf_id,
        "DuckDB standard rebuild rule `{}` aliases its View and UF tables",
        rule.name
    );
    ensure!(
        view_read == ReadMode::All && uf_read == ReadMode::All,
        "DuckDB standard rebuild rule `{}` requires All table atoms",
        rule.name
    );
    if shape == OuterShape::EclassOutput {
        ensure!(
            uf_id == view_displaced,
            "DuckDB eclass-output rebuild rule `{}` must join the View output UF",
            rule.name
        );
    }
    validate_view_table(base_values, &rule.name, &view_info)?;
    validate_union_find_table(base_values, &rule.name, &uf_info)?;
    validate_union_find_table(base_values, &rule.name, &displaced_info)?;

    ensure!(
        view_terms.len() == view_info.arity(),
        "DuckDB standard rebuild rule `{}` View atom has the wrong arity",
        rule.name
    );
    let mut key_vars = Vec::with_capacity(view_info.n_keys);
    for (term, &expected) in view_terms[..view_info.n_keys]
        .iter()
        .zip(&view_info.schema[..view_info.n_keys])
    {
        key_vars.push(typed_var(&rule.name, term, expected)?);
    }
    let view_identity = id_var(&rule.name, &view_terms[view_info.n_keys])?;
    let view_payload = id_var(&rule.name, &view_terms[view_info.n_keys + 1])?;

    let [uf_key_term, canonical_term, uf_payload_term] = uf_terms else {
        bail!(
            "DuckDB standard rebuild rule `{}` UF atom must have three Id variables",
            rule.name
        );
    };
    let uf_key = id_var(&rule.name, uf_key_term)?;
    let canonical = id_var(&rule.name, canonical_term)?;
    let uf_payload = id_var(&rule.name, uf_payload_term)?;

    let stale = match shape {
        OuterShape::EqKey => {
            let positions = key_vars
                .iter()
                .enumerate()
                .filter_map(|(index, key)| same_var_value(key, uf_key).then_some(index))
                .collect::<Vec<_>>();
            let [index] = positions.as_slice() else {
                bail!(
                    "DuckDB eq-key rebuild rule `{}` UF key must be exactly one View key",
                    rule.name
                );
            };
            (*index, key_vars[*index])
        }
        OuterShape::EclassOutput => {
            same_var(&rule.name, view_identity, uf_key, "value-to-UF join")?;
            (view_info.n_keys, view_identity)
        }
    };
    let inequality_result =
        validate_inequality(base_values, &rule.name, inequality, stale.1, canonical)?;

    let mut body_vars = key_vars.clone();
    body_vars.extend([
        view_identity,
        view_payload,
        canonical,
        uf_payload,
        inequality_result,
    ]);
    distinct_vars(&rule.name, &body_vars)?;

    let view_union = validate_ordered_union(
        base_values,
        storage,
        &rule.name,
        view_id,
        &view_info,
        None,
        OrderedUnionOrientation::EclassToTerm,
    )?;
    let uf_union = validate_ordered_union(
        base_values,
        storage,
        &rule.name,
        uf_id,
        &uf_info,
        Some(uf_id),
        OrderedUnionOrientation::KeyToParent,
    )?;
    let displaced_union = validate_ordered_union(
        base_values,
        storage,
        &rule.name,
        view_displaced,
        &displaced_info,
        Some(view_displaced),
        OrderedUnionOrientation::KeyToParent,
    )?;
    ensure!(
        view_union.plan.sym == uf_union.plan.sym
            && view_union.plan.trans == uf_union.plan.trans
            && view_union.fresh_label == uf_union.fresh_label
            && view_union.plan.sym == displaced_union.plan.sym
            && view_union.plan.trans == displaced_union.plan.trans
            && view_union.fresh_label == displaced_union.fresh_label,
        "DuckDB standard rebuild rule `{}` View and UF ordered-union blocks disagree",
        rule.name
    );

    let kind = match shape {
        OuterShape::EqKey => compile_eq_key_head(
            storage,
            base_values,
            rule,
            &view_info,
            view_id,
            stale.0,
            &key_vars,
            view_identity,
            view_payload,
            canonical,
            uf_payload,
            view_union.fresh_label,
            &body_vars,
        )?,
        OuterShape::EclassOutput => compile_eclass_head(
            storage,
            base_values,
            rule,
            view_id,
            &key_vars,
            view_payload,
            canonical,
            uf_payload,
            &view_union,
            &body_vars,
        )?,
    };

    Ok(Some(StandardRebuildPlan {
        seminaive: rule.seminaive,
        view: view_union.plan,
        union_find: uf_union.plan,
        displaced_union_find: displaced_union.plan,
        kind,
    }))
}

#[allow(clippy::too_many_arguments)]
fn compile_eq_key_head(
    storage: &Storage,
    base_values: &BaseValues,
    rule: &RuleSpec,
    view_info: &TableInfo,
    view: FunctionId,
    key_index: usize,
    key_vars: &[&RuleVar],
    view_identity: &RuleVar,
    view_payload: &RuleVar,
    canonical: &RuleVar,
    uf_payload: &RuleVar,
    merge_fresh_label: RuleValue,
    body_vars: &[&RuleVar],
) -> Result<StandardRebuildKind> {
    let [
        fresh_action,
        alias_action,
        congr_action,
        view_action,
        delete_action,
    ] = rule.core.head.0.as_slice()
    else {
        unreachable!("outer shape checked eq-key action arity");
    };
    let (fresh, fresh_label) = head_fresh(base_values, &rule.name, fresh_action)?;
    let alias = head_alias(&rule.name, alias_action, fresh)?;
    ensure!(
        fresh_label == merge_fresh_label,
        "DuckDB eq-key rebuild rule `{}` uses a different fresh label than its ordered unions",
        rule.name
    );

    let GenericCoreAction::Set(_, call, arguments, values) = congr_action else {
        unreachable!("outer shape checked Congr action kind");
    };
    let congr = table_action(&rule.name, call, "Congr proof Set")?;
    let congr_info = storage.table_info(congr)?;
    validate_assert_eq_table(
        base_values,
        &rule.name,
        &congr_info,
        &[
            ScalarSqlType::Id,
            ScalarSqlType::I64,
            ScalarSqlType::Id,
            ScalarSqlType::Id,
        ],
    )?;
    let [row_pf, child_index, edge_pf, proof_result] = arguments.as_slice() else {
        bail!(
            "DuckDB eq-key rebuild rule `{}` Congr Set must have four keys",
            rule.name
        );
    };
    same_var(
        &rule.name,
        view_payload,
        id_var(&rule.name, row_pf)?,
        "Congr row proof",
    )?;
    let child_index = literal(child_index).ok_or_else(|| {
        anyhow!(
            "DuckDB eq-key rebuild rule `{}` child index must be a typed literal",
            rule.name
        )
    })?;
    ensure!(
        ScalarSqlType::from_column(base_values, child_index.ty)? == ScalarSqlType::I64,
        "DuckDB eq-key rebuild rule `{}` child index must have i64 type",
        rule.name
    );
    let child_index_value = base_values.unwrap::<i64>(child_index.value);
    ensure!(
        usize::try_from(child_index_value).ok() == Some(key_index) && key_index < view_info.n_keys,
        "DuckDB eq-key rebuild rule `{}` child index does not name its rebuilt key",
        rule.name
    );
    let child_index_sql = ScalarSqlType::I64.sql_literal(base_values, child_index.value)?;
    same_var(
        &rule.name,
        uf_payload,
        id_var(&rule.name, edge_pf)?,
        "Congr UF proof",
    )?;
    same_var(
        &rule.name,
        alias,
        id_var(&rule.name, proof_result)?,
        "Congr result proof",
    )?;
    unit_value(base_values, &rule.name, values)?;

    validate_view_set(
        &rule.name,
        view_action,
        view,
        key_vars,
        Some((key_index, canonical)),
        view_identity,
        alias,
    )?;
    validate_view_delete(&rule.name, delete_action, view, key_vars)?;
    let mut all_vars = body_vars.to_vec();
    all_vars.extend([fresh, alias]);
    distinct_vars(&rule.name, &all_vars)?;

    Ok(StandardRebuildKind::EqKey {
        key_index,
        child_index_sql,
        congr,
    })
}

#[allow(clippy::too_many_arguments)]
fn compile_eclass_head(
    storage: &Storage,
    base_values: &BaseValues,
    rule: &RuleSpec,
    view: FunctionId,
    key_vars: &[&RuleVar],
    view_payload: &RuleVar,
    canonical: &RuleVar,
    uf_payload: &RuleVar,
    ordered_union: &ValidatedOrderedUnion,
    body_vars: &[&RuleVar],
) -> Result<StandardRebuildKind> {
    let [
        sym_fresh_action,
        sym_alias_action,
        sym_action,
        trans_fresh_action,
        trans_alias_action,
        trans_action,
        view_action,
    ] = rule.core.head.0.as_slice()
    else {
        unreachable!("outer shape checked eclass action arity");
    };
    let (sym_fresh, sym_label) = head_fresh(base_values, &rule.name, sym_fresh_action)?;
    let sym_alias = head_alias(&rule.name, sym_alias_action, sym_fresh)?;
    let (trans_fresh, trans_label) = head_fresh(base_values, &rule.name, trans_fresh_action)?;
    let trans_alias = head_alias(&rule.name, trans_alias_action, trans_fresh)?;
    ensure!(
        sym_label == trans_label && sym_label == ordered_union.fresh_label,
        "DuckDB eclass-output rebuild rule `{}` fresh labels disagree",
        rule.name
    );

    let sym = validate_head_proof_set(
        storage,
        base_values,
        &rule.name,
        sym_action,
        &[uf_payload, sym_alias],
        &[ScalarSqlType::Id, ScalarSqlType::Id],
    )?;
    let trans = validate_head_proof_set(
        storage,
        base_values,
        &rule.name,
        trans_action,
        &[sym_alias, view_payload, trans_alias],
        &[ScalarSqlType::Id, ScalarSqlType::Id, ScalarSqlType::Id],
    )?;
    ensure!(
        sym == ordered_union.plan.sym && trans == ordered_union.plan.trans,
        "DuckDB eclass-output rebuild rule `{}` proof targets disagree with its ordered unions",
        rule.name
    );
    validate_view_set(
        &rule.name,
        view_action,
        view,
        key_vars,
        None,
        canonical,
        trans_alias,
    )?;
    let mut all_vars = body_vars.to_vec();
    all_vars.extend([sym_fresh, sym_alias, trans_fresh, trans_alias]);
    distinct_vars(&rule.name, &all_vars)?;

    Ok(StandardRebuildKind::EclassOutput { sym, trans })
}

fn table_atom_parts(
    atom: &egglog_ast::core::GenericAtom<RuleBodyCall, RuleVar, RuleValue>,
) -> (FunctionId, ReadMode, &[GenericAtomTerm<RuleVar, RuleValue>]) {
    let RuleBodyCall::Table { id, read } = atom.head else {
        unreachable!("outer shape checked table atom")
    };
    (id, read, &atom.args)
}

fn validate_view_table(base_values: &BaseValues, rule_name: &str, info: &TableInfo) -> Result<()> {
    ensure!(
        info.n_vals == 2
            && info.arity() == info.n_keys + 2
            && info.n_keys <= 27
            && info.n_identity_vals == Some(1)
            && matches!(info.default, DefaultVal::Fail)
            && info.can_subsume,
        "DuckDB standard rebuild rule `{rule_name}` View has an incompatible configuration"
    );
    for &ty in &info.schema[..info.n_keys] {
        ScalarSqlType::from_column(base_values, ty)?;
    }
    ensure!(
        info.schema[info.n_keys..] == [ColumnTy::Id, ColumnTy::Id],
        "DuckDB standard rebuild rule `{rule_name}` View must end in two Id values"
    );
    Ok(())
}

fn validate_union_find_table(
    base_values: &BaseValues,
    rule_name: &str,
    info: &TableInfo,
) -> Result<()> {
    ensure!(
        info.schema == [ColumnTy::Id, ColumnTy::Id, ColumnTy::Id]
            && info.n_keys == 1
            && info.n_vals == 2
            && info.n_identity_vals == Some(1)
            && matches!(info.default, DefaultVal::Fail)
            && !info.can_subsume,
        "DuckDB standard rebuild rule `{rule_name}` UF has an incompatible configuration"
    );
    for &ty in &info.schema {
        ensure!(ScalarSqlType::from_column(base_values, ty)? == ScalarSqlType::Id);
    }
    Ok(())
}

struct ValidatedOrderedUnion {
    plan: OrderedUnionPlan,
    fresh_label: RuleValue,
}

/// Cheap family discriminator for the generated ordered-union merge. This is
/// intentionally limited to the outer action/result topology: once it matches,
/// the validator below checks every primitive, type, slot, argument, target,
/// and result. Custom View blocks with a different outer topology belong to the
/// ordinary fail-closed compiler rather than this standard-rebuild language.
fn ordered_union_outer(merge: &MergeFn) -> Option<FunctionId> {
    let MergeFn::Block { actions, result } = merge else {
        return None;
    };
    let [
        MergeAction::Let { .. },
        MergeAction::Let { .. },
        MergeAction::Let { .. },
        MergeAction::Set(_, _),
        MergeAction::Let { .. },
        MergeAction::Set(_, _),
        MergeAction::Set(displaced, displaced_arguments),
    ] = actions.as_slice()
    else {
        return None;
    };
    let MergeFn::Columns(results) = result.as_ref() else {
        return None;
    };
    (displaced_arguments.len() == 3 && results.len() == 2).then_some(*displaced)
}

fn validate_ordered_union(
    base_values: &BaseValues,
    storage: &Storage,
    rule_name: &str,
    target: FunctionId,
    info: &TableInfo,
    expected_displaced_target: Option<FunctionId>,
    orientation: OrderedUnionOrientation,
) -> Result<ValidatedOrderedUnion> {
    let MergeFn::Block { actions, result } = info.merge.as_ref() else {
        bail!("DuckDB standard rebuild rule `{rule_name}` target requires an ordered-union Block");
    };
    let [
        max_pf,
        min_pf,
        fresh_sym,
        set_sym,
        fresh_trans,
        set_trans,
        set_displaced,
    ] = actions.as_slice()
    else {
        bail!(
            "DuckDB standard rebuild rule `{rule_name}` ordered-union Block must have seven actions"
        );
    };
    expect_let_primitive(
        base_values,
        rule_name,
        max_pf,
        0,
        "proof-of-max",
        &[old(0), old(1), new(0), new(1)],
    )?;
    expect_let_primitive(
        base_values,
        rule_name,
        min_pf,
        1,
        "proof-of-min",
        &[old(0), old(1), new(0), new(1)],
    )?;
    let sym_label = expect_fresh_merge(base_values, rule_name, fresh_sym, 2)?;
    let sym_argument = match orientation {
        OrderedUnionOrientation::KeyToParent => let_var(0),
        OrderedUnionOrientation::EclassToTerm => let_var(1),
    };
    let sym = expect_merge_proof_set(
        base_values,
        storage,
        rule_name,
        set_sym,
        &[sym_argument, let_var(2), unit()],
        &[ScalarSqlType::Id, ScalarSqlType::Id],
    )?;
    let trans_label = expect_fresh_merge(base_values, rule_name, fresh_trans, 3)?;
    ensure!(sym_label == trans_label);
    let trans_arguments = match orientation {
        OrderedUnionOrientation::KeyToParent => [let_var(2), let_var(1), let_var(3), unit()],
        OrderedUnionOrientation::EclassToTerm => [let_var(0), let_var(2), let_var(3), unit()],
    };
    let trans = expect_merge_proof_set(
        base_values,
        storage,
        rule_name,
        set_trans,
        &trans_arguments,
        &[ScalarSqlType::Id, ScalarSqlType::Id, ScalarSqlType::Id],
    )?;

    let MergeAction::Set(actual_displaced, arguments) = set_displaced else {
        bail!("DuckDB standard rebuild rule `{rule_name}` ordered union must Set its UF target");
    };
    ensure!(
        arguments.len() == 3,
        "DuckDB standard rebuild rule `{rule_name}` ordered-union UF Set must have three arguments"
    );
    if let Some(expected) = expected_displaced_target {
        ensure!(
            *actual_displaced == expected,
            "DuckDB standard rebuild rule `{rule_name}` UF ordered union must displace into itself"
        );
    }
    expect_primitive(
        base_values,
        rule_name,
        &arguments[0],
        "ordering-max",
        &[old(0), new(0)],
    )?;
    expect_primitive(
        base_values,
        rule_name,
        &arguments[1],
        "ordering-min",
        &[old(0), new(0)],
    )?;
    expect_pattern(base_values, rule_name, &arguments[2], let_var(3))?;

    let MergeFn::Columns(results) = result.as_ref() else {
        bail!("DuckDB standard rebuild rule `{rule_name}` ordered-union result must be Columns");
    };
    let [identity, payload] = results.as_slice() else {
        bail!(
            "DuckDB standard rebuild rule `{rule_name}` ordered-union result must have two columns"
        );
    };
    expect_primitive(
        base_values,
        rule_name,
        identity,
        "ordering-min",
        &[old(0), new(0)],
    )?;
    expect_pattern(base_values, rule_name, payload, let_var(1))?;

    Ok(ValidatedOrderedUnion {
        plan: OrderedUnionPlan {
            target,
            displaced_target: *actual_displaced,
            sym,
            trans,
            orientation,
            columns: info.columns.clone(),
            n_keys: info.n_keys,
        },
        fresh_label: sym_label,
    })
}

fn validate_inequality<'a>(
    base_values: &BaseValues,
    rule_name: &str,
    atom: &'a egglog_ast::core::GenericAtom<RuleBodyCall, RuleVar, RuleValue>,
    stale: &RuleVar,
    canonical: &RuleVar,
) -> Result<&'a RuleVar> {
    let RuleBodyCall::Primitive { name, output, .. } = &atom.head else {
        bail!("DuckDB standard rebuild rule `{rule_name}` requires a typed inequality atom");
    };
    ensure!(
        name.as_ref() == "!="
            && ScalarSqlType::from_column(base_values, *output)? == ScalarSqlType::Unit,
        "DuckDB standard rebuild rule `{rule_name}` requires `!= (Id, Id) -> Unit`"
    );
    let [lhs, rhs, result] = atom.args.as_slice() else {
        bail!("DuckDB standard rebuild rule `{rule_name}` inequality has the wrong arity");
    };
    same_var(rule_name, stale, id_var(rule_name, lhs)?, "inequality lhs")?;
    same_var(
        rule_name,
        canonical,
        id_var(rule_name, rhs)?,
        "inequality rhs",
    )?;
    let result = var(result).ok_or_else(|| {
        anyhow!("DuckDB standard rebuild rule `{rule_name}` inequality output must be a variable")
    })?;
    ensure!(
        ScalarSqlType::from_column(base_values, result.ty)? == ScalarSqlType::Unit,
        "DuckDB standard rebuild rule `{rule_name}` inequality output must have Unit type"
    );
    Ok(result)
}

fn head_fresh<'a>(
    base_values: &BaseValues,
    rule_name: &str,
    action: &'a GenericCoreAction<RuleActionCall, RuleVar, RuleValue>,
) -> Result<(&'a RuleVar, RuleValue)> {
    let GenericCoreAction::Let(_, binding, call, arguments) = action else {
        bail!("DuckDB standard rebuild rule `{rule_name}` fresh action must be a Let");
    };
    let RuleActionCall::Primitive { name, output, .. } = call else {
        bail!("DuckDB standard rebuild rule `{rule_name}` fresh action must call a primitive");
    };
    ensure!(
        name.as_ref() == "get-fresh!" && *output == ColumnTy::Id && binding.ty == ColumnTy::Id,
        "DuckDB standard rebuild rule `{rule_name}` requires get-fresh! (String) -> Id"
    );
    let [argument] = arguments.as_slice() else {
        bail!("DuckDB standard rebuild rule `{rule_name}` get-fresh! must have one argument");
    };
    let label = literal(argument).ok_or_else(|| {
        anyhow!("DuckDB standard rebuild rule `{rule_name}` fresh label must be a literal")
    })?;
    ensure!(
        ScalarSqlType::from_column(base_values, label.ty)? == ScalarSqlType::String,
        "DuckDB standard rebuild rule `{rule_name}` fresh label must have String type"
    );
    Ok((binding, *label))
}

fn head_alias<'a>(
    rule_name: &str,
    action: &'a GenericCoreAction<RuleActionCall, RuleVar, RuleValue>,
    fresh: &RuleVar,
) -> Result<&'a RuleVar> {
    let GenericCoreAction::LetAtomTerm(_, alias, source) = action else {
        bail!("DuckDB standard rebuild rule `{rule_name}` fresh result must have one SSA alias");
    };
    ensure!(alias.ty == ColumnTy::Id);
    same_var(
        rule_name,
        fresh,
        id_var(rule_name, source)?,
        "fresh alias source",
    )?;
    Ok(alias)
}

fn validate_head_proof_set(
    storage: &Storage,
    base_values: &BaseValues,
    rule_name: &str,
    action: &GenericCoreAction<RuleActionCall, RuleVar, RuleValue>,
    expected_vars: &[&RuleVar],
    key_types: &[ScalarSqlType],
) -> Result<FunctionId> {
    let GenericCoreAction::Set(_, call, arguments, values) = action else {
        bail!("DuckDB standard rebuild rule `{rule_name}` proof action must be a Set");
    };
    let target = table_action(rule_name, call, "proof Set")?;
    let info = storage.table_info(target)?;
    validate_assert_eq_table(base_values, rule_name, &info, key_types)?;
    ensure!(arguments.len() == expected_vars.len());
    for (argument, expected) in arguments.iter().zip(expected_vars) {
        same_var(
            rule_name,
            expected,
            id_var(rule_name, argument)?,
            "proof Set argument",
        )?;
    }
    unit_value(base_values, rule_name, values)?;
    Ok(target)
}

fn validate_assert_eq_table(
    base_values: &BaseValues,
    rule_name: &str,
    info: &TableInfo,
    key_types: &[ScalarSqlType],
) -> Result<()> {
    ensure!(
        info.n_keys == key_types.len()
            && info.n_vals == 1
            && info.arity() == key_types.len() + 1
            && info.n_identity_vals.is_none()
            && matches!(info.default, DefaultVal::Fail)
            && info.write_capability == WriteCapability::AssertEq
            && !info.can_subsume,
        "DuckDB standard rebuild rule `{rule_name}` proof target is not the exact one-output AssertEq shape"
    );
    for (&ty, &expected) in info.schema[..info.n_keys].iter().zip(key_types) {
        ensure!(ScalarSqlType::from_column(base_values, ty)? == expected);
    }
    ensure!(
        ScalarSqlType::from_column(base_values, info.schema[info.n_keys])? == ScalarSqlType::Unit
    );
    Ok(())
}

fn validate_view_set(
    rule_name: &str,
    action: &GenericCoreAction<RuleActionCall, RuleVar, RuleValue>,
    view: FunctionId,
    key_vars: &[&RuleVar],
    replacement: Option<(usize, &RuleVar)>,
    identity: &RuleVar,
    payload: &RuleVar,
) -> Result<()> {
    let GenericCoreAction::Set(_, call, arguments, values) = action else {
        bail!("DuckDB standard rebuild rule `{rule_name}` canonical View action must be a Set");
    };
    ensure!(table_action(rule_name, call, "canonical View Set")? == view);
    ensure!(arguments.len() == key_vars.len());
    for (index, (argument, original)) in arguments.iter().zip(key_vars).enumerate() {
        let expected = replacement
            .filter(|(replacement_index, _)| *replacement_index == index)
            .map_or(*original, |(_, replacement)| replacement);
        same_var(
            rule_name,
            expected,
            typed_var(rule_name, argument, expected.ty)?,
            "canonical View key",
        )?;
    }
    let [actual_identity, actual_payload] = values.as_slice() else {
        bail!("DuckDB standard rebuild rule `{rule_name}` View Set must have two Id values");
    };
    same_var(
        rule_name,
        identity,
        id_var(rule_name, actual_identity)?,
        "canonical View identity",
    )?;
    same_var(
        rule_name,
        payload,
        id_var(rule_name, actual_payload)?,
        "canonical View payload",
    )
}

fn validate_view_delete(
    rule_name: &str,
    action: &GenericCoreAction<RuleActionCall, RuleVar, RuleValue>,
    view: FunctionId,
    key_vars: &[&RuleVar],
) -> Result<()> {
    let GenericCoreAction::Change(_, change, call, arguments) = action else {
        bail!("DuckDB eq-key rebuild rule `{rule_name}` final action must be Delete");
    };
    ensure!(*change == Change::Delete);
    ensure!(table_action(rule_name, call, "stale View Delete")? == view);
    ensure!(arguments.len() == key_vars.len());
    for (argument, expected) in arguments.iter().zip(key_vars) {
        same_var(
            rule_name,
            expected,
            typed_var(rule_name, argument, expected.ty)?,
            "stale View key",
        )?;
    }
    Ok(())
}

fn table_action(rule_name: &str, call: &RuleActionCall, role: &str) -> Result<FunctionId> {
    let RuleActionCall::Table { id, .. } = call else {
        bail!("DuckDB standard rebuild rule `{rule_name}` {role} must target a table");
    };
    Ok(*id)
}

fn expect_let_primitive(
    base_values: &BaseValues,
    rule_name: &str,
    action: &MergeAction,
    slot: usize,
    name: &str,
    arguments: &[MergePattern],
) -> Result<()> {
    let MergeAction::Let {
        slot: actual,
        value,
    } = action
    else {
        bail!("DuckDB standard rebuild rule `{rule_name}` merge slot {slot} must be a Let");
    };
    ensure!(*actual == slot);
    expect_primitive(base_values, rule_name, value, name, arguments)
}

fn expect_fresh_merge(
    base_values: &BaseValues,
    rule_name: &str,
    action: &MergeAction,
    slot: usize,
) -> Result<RuleValue> {
    let MergeAction::Let {
        slot: actual,
        value,
    } = action
    else {
        bail!("DuckDB standard rebuild rule `{rule_name}` merge fresh slot {slot} must be a Let");
    };
    ensure!(*actual == slot);
    let MergeFn::Primitive {
        name,
        input,
        output,
        args,
        ..
    } = value
    else {
        bail!("DuckDB standard rebuild rule `{rule_name}` merge fresh slot must call a primitive");
    };
    ensure!(
        name == "get-fresh!"
            && input.len() == 1
            && ScalarSqlType::from_column(base_values, input[0])? == ScalarSqlType::String
            && *output == ColumnTy::Id
            && args.len() == 1
    );
    let MergeFn::Const { value, ty } = &args[0] else {
        bail!(
            "DuckDB standard rebuild rule `{rule_name}` merge get-fresh! requires a typed constant"
        );
    };
    ensure!(ScalarSqlType::from_column(base_values, *ty)? == ScalarSqlType::String);
    Ok(RuleValue {
        value: *value,
        ty: *ty,
    })
}

fn expect_merge_proof_set(
    base_values: &BaseValues,
    storage: &Storage,
    rule_name: &str,
    action: &MergeAction,
    expected: &[MergePattern],
    key_types: &[ScalarSqlType],
) -> Result<FunctionId> {
    let MergeAction::Set(target, arguments) = action else {
        bail!("DuckDB standard rebuild rule `{rule_name}` merge proof action must be a Set");
    };
    ensure!(arguments.len() == expected.len());
    for (argument, expected) in arguments.iter().zip(expected) {
        expect_pattern(base_values, rule_name, argument, *expected)?;
    }
    let info = storage.table_info(*target)?;
    validate_assert_eq_table(base_values, rule_name, &info, key_types)?;
    Ok(*target)
}

fn expect_primitive(
    base_values: &BaseValues,
    rule_name: &str,
    merge: &MergeFn,
    expected_name: &str,
    expected_args: &[MergePattern],
) -> Result<()> {
    let MergeFn::Primitive {
        name,
        input,
        output,
        args,
        ..
    } = merge
    else {
        bail!(
            "DuckDB standard rebuild rule `{rule_name}` merge requires primitive `{expected_name}`"
        );
    };
    ensure!(
        name == expected_name
            && input.len() == expected_args.len()
            && input.iter().all(|ty| *ty == ColumnTy::Id)
            && *output == ColumnTy::Id
            && args.len() == expected_args.len(),
        "DuckDB standard rebuild rule `{rule_name}` primitive `{expected_name}` has an incompatible signature"
    );
    for (argument, expected) in args.iter().zip(expected_args) {
        expect_pattern(base_values, rule_name, argument, *expected)?;
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum MergePattern {
    Old(usize),
    New(usize),
    Let(usize),
    Unit,
}

const fn old(index: usize) -> MergePattern {
    MergePattern::Old(index)
}
const fn new(index: usize) -> MergePattern {
    MergePattern::New(index)
}
const fn let_var(slot: usize) -> MergePattern {
    MergePattern::Let(slot)
}
const fn unit() -> MergePattern {
    MergePattern::Unit
}

fn expect_pattern(
    base_values: &BaseValues,
    rule_name: &str,
    merge: &MergeFn,
    expected: MergePattern,
) -> Result<()> {
    let matches = match (merge, expected) {
        (MergeFn::OldCol(actual), MergePattern::Old(expected)) => *actual == expected,
        (MergeFn::NewCol(actual), MergePattern::New(expected)) => *actual == expected,
        (MergeFn::LetVar(actual), MergePattern::Let(expected)) => *actual == expected,
        (MergeFn::Const { ty, .. }, MergePattern::Unit) => {
            ScalarSqlType::from_column(base_values, *ty)? == ScalarSqlType::Unit
        }
        _ => false,
    };
    ensure!(
        matches,
        "DuckDB standard rebuild rule `{rule_name}` merge topology mismatch"
    );
    Ok(())
}

fn unit_value(
    base_values: &BaseValues,
    rule_name: &str,
    values: &[GenericAtomTerm<RuleVar, RuleValue>],
) -> Result<()> {
    let [value] = values else {
        bail!("DuckDB standard rebuild rule `{rule_name}` proof Set must have one Unit value");
    };
    let value = literal(value).ok_or_else(|| {
        anyhow!("DuckDB standard rebuild rule `{rule_name}` proof value must be a literal")
    })?;
    ensure!(ScalarSqlType::from_column(base_values, value.ty)? == ScalarSqlType::Unit);
    ScalarSqlType::Unit.sql_literal(base_values, value.value)?;
    Ok(())
}

fn var(term: &GenericAtomTerm<RuleVar, RuleValue>) -> Option<&RuleVar> {
    match term {
        GenericAtomTerm::Var(_, variable) => Some(variable),
        _ => None,
    }
}

fn literal(term: &GenericAtomTerm<RuleVar, RuleValue>) -> Option<&RuleValue> {
    match term {
        GenericAtomTerm::Literal(_, value) => Some(value),
        _ => None,
    }
}

fn typed_var<'a>(
    rule_name: &str,
    term: &'a GenericAtomTerm<RuleVar, RuleValue>,
    expected: ColumnTy,
) -> Result<&'a RuleVar> {
    let variable = var(term)
        .ok_or_else(|| anyhow!("DuckDB standard rebuild rule `{rule_name}` requires variables"))?;
    ensure!(
        variable.ty == expected,
        "DuckDB standard rebuild rule `{rule_name}` has a variable with the wrong type"
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
        "DuckDB standard rebuild rule `{rule_name}` has inconsistent {role} variables"
    );
    Ok(())
}

fn distinct_vars(rule_name: &str, variables: &[&RuleVar]) -> Result<()> {
    for (index, left) in variables.iter().enumerate() {
        ensure!(
            variables[index + 1..]
                .iter()
                .all(|right| left.id != right.id),
            "DuckDB standard rebuild rule `{rule_name}` aliases structurally distinct variables"
        );
    }
    Ok(())
}

pub(crate) fn safe_scratch_name(name: &str) -> bool {
    name.bytes()
        .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}
