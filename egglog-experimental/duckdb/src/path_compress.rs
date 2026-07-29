//! Closed, structural lowering for the proof-agnostic union-find path rule.
//!
//! The frontend emits the same typed rule and merge vocabulary for every
//! equality sort.  This module recognizes that vocabulary by topology,
//! concrete types, and authenticated native primitive tags. Generated rule, function,
//! variable, proof-sort, and table names are deliberately ignored.

use std::collections::{BTreeMap, BTreeSet};

use anyhow::{Result, anyhow, bail, ensure};
use egglog_ast::core::{GenericAtomTerm, GenericCoreAction};
use egglog_backend_trait::{
    BaseValues, ColumnTy, DefaultVal, ExternalFunctionId, FunctionId, MergeAction, MergeFn,
    NativePrimitive, ReadMode, RuleActionCall, RuleBodyCall, RuleSpec, RuleValue, RuleVar,
};
use egglog_numeric_id::NumericId;

use crate::storage::{ScalarSqlType, Storage, TableInfo, WriteCapability, sql_table};

/// A fully validated instance of the reached path-compression vocabulary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PathCompressionPlan {
    pub(crate) seminaive: bool,
    pub(crate) union_find: FunctionId,
    pub(crate) sym: FunctionId,
    pub(crate) trans: FunctionId,
}

impl PathCompressionPlan {
    pub(crate) fn materialize_sql(&self, stage: &str, watermark: u64) -> String {
        debug_assert!(safe_scratch_name(stage));
        let uf = sql_table(self.union_find);
        let freshness = if self.seminaive {
            format!(
                "AND (first.__generation >= CAST('{watermark}' AS UBIGINT)\n                       OR second.__generation >= CAST('{watermark}' AS UBIGINT))"
            )
        } else {
            String::new()
        };
        format!(
            "CREATE TEMP TABLE {stage} AS
             WITH bindings AS (
                 SELECT DISTINCT
                        first.c0 AS c0,
                        first.c1 AS c1,
                        first.c2 AS c2,
                        second.c1 AS c3,
                        second.c2 AS c4
                 FROM {uf} AS first
                 JOIN {uf} AS second
                   ON first.c1 IS NOT DISTINCT FROM second.c0
                 WHERE first.__subsumed = FALSE
                   AND second.__subsumed = FALSE
                   AND first.c1 IS DISTINCT FROM second.c1
                   {freshness}
             )
             SELECT bindings.*,
                    row_number() OVER (ORDER BY c0, c1, c2, c3, c4)
                        AS __match_ordinal
             FROM bindings"
        )
    }

    pub(crate) fn group_key(&self) -> (u32, u32, u32) {
        (self.union_find.rep(), self.sym.rep(), self.trans.rep())
    }
}

pub(crate) fn looks_like_path_compression(rule: &RuleSpec) -> bool {
    let [first, second, guard] = rule.core.body.atoms.as_slice() else {
        return false;
    };
    let (
        RuleBodyCall::Table {
            id: first_id,
            read: ReadMode::Live,
        },
        RuleBodyCall::Table {
            id: second_id,
            read: ReadMode::Live,
        },
        RuleBodyCall::Primitive { .. },
    ) = (&first.head, &second.head, &guard.head)
    else {
        return false;
    };
    if first_id != second_id {
        return false;
    }
    let [fresh, alias, proof, update] = rule.core.head.0.as_slice() else {
        return false;
    };
    matches!(
        (fresh, alias, proof, update),
        (
            GenericCoreAction::Let(_, _, RuleActionCall::Primitive { .. }, _),
            GenericCoreAction::LetAtomTerm(..),
            GenericCoreAction::Set(_, RuleActionCall::Table { .. }, _, _),
            GenericCoreAction::Set(
                _,
                RuleActionCall::Table { id, .. },
                _,
                _
            )
        ) if id == first_id
    )
}

/// Compile the exact reached typed shape.  A mismatch is an admission error;
/// callers invoke this only after the cheap arity discriminator above.
pub(crate) fn compile_path_compression(
    storage: &Storage,
    base_values: &BaseValues,
    native_primitives: &BTreeMap<ExternalFunctionId, NativePrimitive>,
    fresh_tokens: &BTreeSet<ExternalFunctionId>,
    rule: &RuleSpec,
) -> Result<PathCompressionPlan> {
    ensure!(
        rule.seminaive && !rule.no_decomp,
        "DuckDB four-action rule `{}` is not the supported seminaive path shape",
        rule.name
    );

    let [first, second, inequality] = rule.core.body.atoms.as_slice() else {
        unreachable!("candidate arity checked by caller");
    };
    let (union_find, first_terms) = live_table_atom(&rule.name, first)?;
    let (second_union_find, second_terms) = live_table_atom(&rule.name, second)?;
    ensure!(
        union_find == second_union_find,
        "DuckDB four-action rule `{}` reads two different candidate tables",
        rule.name
    );
    let uf_info = storage.table_info(union_find)?;
    validate_union_find_table(base_values, &rule.name, &uf_info)?;

    let [a, b, pb] = first_terms else {
        bail!(
            "DuckDB path rule `{}` first table atom must have three Id variables",
            rule.name
        );
    };
    let [second_b, c, pc] = second_terms else {
        bail!(
            "DuckDB path rule `{}` second table atom must have three Id variables",
            rule.name
        );
    };
    let a = id_var(&rule.name, a)?;
    let b = id_var(&rule.name, b)?;
    let pb = id_var(&rule.name, pb)?;
    let second_b = id_var(&rule.name, second_b)?;
    let c = id_var(&rule.name, c)?;
    let pc = id_var(&rule.name, pc)?;
    same_var(&rule.name, b, second_b, "path join")?;

    let RuleBodyCall::Primitive { id, name, output } = &inequality.head else {
        bail!(
            "DuckDB path rule `{}` third atom must be a typed primitive",
            rule.name
        );
    };
    ensure!(
        native_primitives.get(id) == Some(&NativePrimitive::ValueNeq)
            && scalar(base_values, *output)? == ScalarSqlType::Unit,
        "DuckDB path rule `{}` requires authenticated ValueNeq (diagnostic name `{name}`) with (Id, Id) -> Unit",
        rule.name,
    );
    let [neq_b, neq_c, neq_result] = inequality.args.as_slice() else {
        bail!(
            "DuckDB path rule `{}` inequality atom must have two inputs and one output",
            rule.name
        );
    };
    same_var(&rule.name, b, id_var(&rule.name, neq_b)?, "inequality lhs")?;
    same_var(&rule.name, c, id_var(&rule.name, neq_c)?, "inequality rhs")?;
    let neq_result = var(neq_result).ok_or_else(|| {
        anyhow!(
            "DuckDB path rule `{}` inequality output must be a variable",
            rule.name
        )
    })?;
    ensure!(
        neq_result.ty == *output && scalar(base_values, neq_result.ty)? == ScalarSqlType::Unit,
        "DuckDB path rule `{}` inequality output must have Unit type",
        rule.name
    );

    let [fresh_action, alias_action, trans_action, uf_action] = rule.core.head.0.as_slice() else {
        unreachable!("candidate arity checked by caller");
    };
    let (fresh, head_fresh_label) =
        head_fresh(base_values, fresh_tokens, &rule.name, fresh_action)?;
    ensure!(
        scalar(base_values, head_fresh_label.ty)? == ScalarSqlType::String,
        "DuckDB path rule `{}` get-fresh! source must be String",
        rule.name
    );
    let alias = head_alias(&rule.name, alias_action, fresh)?;
    // The second occurrence of `b` and the alias source are intentional
    // topology edges. Every semantic binding role itself must remain unique,
    // including otherwise type-incompatible roles such as the Unit result.
    distinct_vars(&rule.name, &[a, b, pb, c, pc, neq_result, fresh, alias])?;
    let trans = head_trans(
        base_values,
        storage,
        &rule.name,
        trans_action,
        pb,
        pc,
        alias,
    )?;
    head_union_find(&rule.name, uf_action, union_find, a, c, alias)?;

    let (sym, merge_trans, merge_fresh_label) = validate_union_find_merge(
        base_values,
        storage,
        native_primitives,
        fresh_tokens,
        &rule.name,
        union_find,
        uf_info.merge.as_ref(),
    )?;
    ensure!(
        trans == merge_trans,
        "DuckDB path rule `{}` head proof target must equal the merge Trans target",
        rule.name
    );
    ensure!(
        head_fresh_label == merge_fresh_label,
        "DuckDB path rule `{}` must use one opaque fresh-label constant",
        rule.name
    );

    Ok(PathCompressionPlan {
        seminaive: rule.seminaive,
        union_find,
        sym,
        trans,
    })
}

fn live_table_atom<'a>(
    rule_name: &str,
    atom: &'a egglog_ast::core::GenericAtom<RuleBodyCall, RuleVar, RuleValue>,
) -> Result<(FunctionId, &'a [GenericAtomTerm<RuleVar, RuleValue>])> {
    let RuleBodyCall::Table { id, read } = atom.head else {
        bail!("DuckDB path rule `{rule_name}` requires two leading table atoms");
    };
    ensure!(
        read == ReadMode::Live,
        "DuckDB path rule `{rule_name}` requires Live table atoms"
    );
    Ok((id, &atom.args))
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
        "DuckDB path rule `{rule_name}` candidate table is not the typed one-key/two-value identity-guard shape"
    );
    for ty in &info.schema {
        ensure!(scalar(base_values, *ty)? == ScalarSqlType::Id);
    }
    Ok(())
}

fn head_fresh<'a>(
    base_values: &BaseValues,
    fresh_tokens: &BTreeSet<ExternalFunctionId>,
    rule_name: &str,
    action: &'a GenericCoreAction<RuleActionCall, RuleVar, RuleValue>,
) -> Result<(&'a RuleVar, RuleValue)> {
    let GenericCoreAction::Let(_, binding, call, arguments) = action else {
        bail!("DuckDB path rule `{rule_name}` first action must bind get-fresh!");
    };
    let RuleActionCall::Primitive { id, name, output } = call else {
        bail!("DuckDB path rule `{rule_name}` first action must call a primitive");
    };
    ensure!(
        fresh_tokens.contains(id) && *output == ColumnTy::Id && binding.ty == ColumnTy::Id,
        "DuckDB path rule `{rule_name}` requires a live fresh token (diagnostic name `{name}`) with (String) -> Id"
    );
    let [argument] = arguments.as_slice() else {
        bail!("DuckDB path rule `{rule_name}` get-fresh! must have one argument");
    };
    let literal = literal(argument).ok_or_else(|| {
        anyhow!("DuckDB path rule `{rule_name}` get-fresh! argument must be a literal")
    })?;
    ensure!(scalar(base_values, literal.ty)? == ScalarSqlType::String);
    Ok((binding, *literal))
}

fn head_alias<'a>(
    rule_name: &str,
    action: &'a GenericCoreAction<RuleActionCall, RuleVar, RuleValue>,
    fresh: &RuleVar,
) -> Result<&'a RuleVar> {
    let GenericCoreAction::LetAtomTerm(_, alias, source) = action else {
        bail!("DuckDB path rule `{rule_name}` second action must be an SSA alias");
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

fn head_trans(
    base_values: &BaseValues,
    storage: &Storage,
    rule_name: &str,
    action: &GenericCoreAction<RuleActionCall, RuleVar, RuleValue>,
    pb: &RuleVar,
    pc: &RuleVar,
    alias: &RuleVar,
) -> Result<FunctionId> {
    let GenericCoreAction::Set(_, call, arguments, values) = action else {
        bail!("DuckDB path rule `{rule_name}` third action must set a proof relation");
    };
    let RuleActionCall::Table { id, .. } = call else {
        bail!("DuckDB path rule `{rule_name}` cannot set a primitive");
    };
    validate_proof_table(base_values, rule_name, storage, *id, 3)?;
    let [head_pb, head_pc, head_fresh] = arguments.as_slice() else {
        bail!("DuckDB path rule `{rule_name}` proof Set must have three Id keys");
    };
    same_var(rule_name, pb, id_var(rule_name, head_pb)?, "proof lhs")?;
    same_var(rule_name, pc, id_var(rule_name, head_pc)?, "proof rhs")?;
    same_var(
        rule_name,
        alias,
        id_var(rule_name, head_fresh)?,
        "proof output id",
    )?;
    unit_value(base_values, rule_name, values)?;
    Ok(*id)
}

fn head_union_find(
    rule_name: &str,
    action: &GenericCoreAction<RuleActionCall, RuleVar, RuleValue>,
    union_find: FunctionId,
    a: &RuleVar,
    c: &RuleVar,
    alias: &RuleVar,
) -> Result<()> {
    let GenericCoreAction::Set(_, call, arguments, values) = action else {
        bail!("DuckDB path rule `{rule_name}` fourth action must set its candidate table");
    };
    let RuleActionCall::Table { id, .. } = call else {
        bail!("DuckDB path rule `{rule_name}` cannot set a primitive");
    };
    ensure!(*id == union_find);
    let [key] = arguments.as_slice() else {
        bail!("DuckDB path rule `{rule_name}` final Set must have one key");
    };
    let [parent, proof] = values.as_slice() else {
        bail!("DuckDB path rule `{rule_name}` final Set must have two values");
    };
    same_var(rule_name, a, id_var(rule_name, key)?, "candidate key")?;
    same_var(rule_name, c, id_var(rule_name, parent)?, "candidate parent")?;
    same_var(
        rule_name,
        alias,
        id_var(rule_name, proof)?,
        "candidate proof",
    )
}

fn validate_union_find_merge(
    base_values: &BaseValues,
    storage: &Storage,
    native_primitives: &BTreeMap<ExternalFunctionId, NativePrimitive>,
    fresh_tokens: &BTreeSet<ExternalFunctionId>,
    rule_name: &str,
    union_find: FunctionId,
    merge: &MergeFn,
) -> Result<(FunctionId, FunctionId, RuleValue)> {
    let MergeFn::Block { actions, result } = merge else {
        bail!("DuckDB path rule `{rule_name}` candidate table requires a merge Block");
    };
    let [
        max_pf,
        min_pf,
        fresh_sym,
        set_sym,
        fresh_trans,
        set_trans,
        set_uf,
    ] = actions.as_slice()
    else {
        bail!("DuckDB path rule `{rule_name}` merge Block must have seven ordered actions");
    };
    expect_let_primitive(
        base_values,
        native_primitives,
        rule_name,
        max_pf,
        0,
        NativePrimitive::SelectMaxPayload,
        &[old(0), old(1), new(0), new(1)],
    )?;
    expect_let_primitive(
        base_values,
        native_primitives,
        rule_name,
        min_pf,
        1,
        NativePrimitive::SelectMinPayload,
        &[old(0), old(1), new(0), new(1)],
    )?;
    let (sym_fresh_token, sym_fresh_label) =
        expect_fresh_merge(base_values, fresh_tokens, rule_name, fresh_sym, 2)?;
    let sym = expect_proof_set(
        base_values,
        storage,
        rule_name,
        set_sym,
        &[let_var(0), let_var(2), unit()],
        2,
    )?;
    let (trans_fresh_token, trans_fresh_label) =
        expect_fresh_merge(base_values, fresh_tokens, rule_name, fresh_trans, 3)?;
    ensure!(
        sym_fresh_token == trans_fresh_token && sym_fresh_label == trans_fresh_label,
        "DuckDB path rule `{rule_name}` merge fresh sites must use one live token and label"
    );
    let trans = expect_proof_set(
        base_values,
        storage,
        rule_name,
        set_trans,
        &[let_var(2), let_var(1), let_var(3), unit()],
        3,
    )?;
    let MergeAction::Set(target, arguments) = set_uf else {
        bail!("DuckDB path rule `{rule_name}` merge action 6 must set its candidate table");
    };
    ensure!(*target == union_find && arguments.len() == 3);
    expect_primitive(
        base_values,
        native_primitives,
        rule_name,
        &arguments[0],
        NativePrimitive::OrderingMax,
        &[old(0), new(0)],
    )?;
    expect_primitive(
        base_values,
        native_primitives,
        rule_name,
        &arguments[1],
        NativePrimitive::OrderingMin,
        &[old(0), new(0)],
    )?;
    expect_pattern(base_values, rule_name, &arguments[2], let_var(3))?;

    let MergeFn::Columns(results) = result.as_ref() else {
        bail!("DuckDB path rule `{rule_name}` merge result must be Columns");
    };
    let [parent, proof] = results.as_slice() else {
        bail!("DuckDB path rule `{rule_name}` merge result must have two columns");
    };
    expect_primitive(
        base_values,
        native_primitives,
        rule_name,
        parent,
        NativePrimitive::OrderingMin,
        &[old(0), new(0)],
    )?;
    expect_pattern(base_values, rule_name, proof, let_var(1))?;
    Ok((sym, trans, sym_fresh_label))
}

fn expect_let_primitive(
    base_values: &BaseValues,
    native_primitives: &BTreeMap<ExternalFunctionId, NativePrimitive>,
    rule_name: &str,
    action: &MergeAction,
    slot: usize,
    primitive: NativePrimitive,
    arguments: &[MergePattern],
) -> Result<()> {
    let MergeAction::Let {
        slot: actual,
        value,
    } = action
    else {
        bail!("DuckDB path rule `{rule_name}` merge slot {slot} must be a Let");
    };
    ensure!(*actual == slot);
    expect_primitive(
        base_values,
        native_primitives,
        rule_name,
        value,
        primitive,
        arguments,
    )
}

fn expect_fresh_merge(
    base_values: &BaseValues,
    fresh_tokens: &BTreeSet<ExternalFunctionId>,
    rule_name: &str,
    action: &MergeAction,
    slot: usize,
) -> Result<(ExternalFunctionId, RuleValue)> {
    let MergeAction::Let {
        slot: actual,
        value,
    } = action
    else {
        bail!("DuckDB path rule `{rule_name}` merge fresh slot {slot} must be a Let");
    };
    ensure!(*actual == slot);
    let MergeFn::Primitive {
        id,
        name,
        input,
        output,
        args,
        ..
    } = value
    else {
        bail!("DuckDB path rule `{rule_name}` merge fresh slot must call a primitive");
    };
    ensure!(
        fresh_tokens.contains(id)
            && input.len() == 1
            && scalar(base_values, input[0])? == ScalarSqlType::String
            && *output == ColumnTy::Id
            && args.len() == 1,
        "DuckDB path rule `{rule_name}` merge primitive `{name}` requires a live registered get-fresh token with (String) -> Id"
    );
    let MergeFn::Const { value, ty } = &args[0] else {
        bail!("DuckDB path rule `{rule_name}` merge get-fresh! requires a typed constant");
    };
    ensure!(
        input[0] == *ty && scalar(base_values, *ty)? == ScalarSqlType::String,
        "DuckDB path rule `{rule_name}` merge fresh primitive `{name}` has mismatched typed input"
    );
    Ok((
        *id,
        RuleValue {
            value: *value,
            ty: *ty,
        },
    ))
}

fn expect_proof_set(
    base_values: &BaseValues,
    storage: &Storage,
    rule_name: &str,
    action: &MergeAction,
    expected: &[MergePattern],
    n_keys: usize,
) -> Result<FunctionId> {
    let MergeAction::Set(target, arguments) = action else {
        bail!("DuckDB path rule `{rule_name}` merge proof action must be a Set");
    };
    ensure!(arguments.len() == expected.len());
    for (argument, expected) in arguments.iter().zip(expected) {
        expect_pattern(base_values, rule_name, argument, *expected)?;
    }
    validate_proof_table(base_values, rule_name, storage, *target, n_keys)?;
    Ok(*target)
}

fn validate_proof_table(
    base_values: &BaseValues,
    rule_name: &str,
    storage: &Storage,
    target: FunctionId,
    n_keys: usize,
) -> Result<()> {
    let info = storage.table_info(target)?;
    ensure!(
        info.n_keys == n_keys
            && info.n_vals == 1
            && info.arity() == n_keys + 1
            && info.n_identity_vals.is_none()
            && matches!(info.default, DefaultVal::Fail)
            && info.write_capability == WriteCapability::AssertEq
            && !info.can_subsume,
        "DuckDB path rule `{rule_name}` proof target is not a one-output AssertEq table"
    );
    for (index, ty) in info.schema.iter().enumerate() {
        let expected = if index < n_keys {
            ScalarSqlType::Id
        } else {
            ScalarSqlType::Unit
        };
        ensure!(scalar(base_values, *ty)? == expected);
    }
    Ok(())
}

fn expect_primitive(
    base_values: &BaseValues,
    native_primitives: &BTreeMap<ExternalFunctionId, NativePrimitive>,
    rule_name: &str,
    merge: &MergeFn,
    expected: NativePrimitive,
    expected_args: &[MergePattern],
) -> Result<()> {
    let MergeFn::Primitive {
        id,
        name,
        input,
        output,
        args,
        ..
    } = merge
    else {
        bail!("DuckDB path rule `{rule_name}` merge requires native primitive {expected:?}");
    };
    ensure!(
        native_primitives.get(id) == Some(&expected)
            && input.len() == expected_args.len()
            && input.iter().all(|ty| *ty == ColumnTy::Id)
            && *output == ColumnTy::Id
            && args.len() == expected_args.len(),
        "DuckDB path rule `{rule_name}` primitive `{name}` is not authenticated as {expected:?} with the required typed signature"
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
            scalar(base_values, *ty)? == ScalarSqlType::Unit
        }
        _ => false,
    };
    ensure!(
        matches,
        "DuckDB path rule `{rule_name}` merge topology mismatch"
    );
    Ok(())
}

fn unit_value(
    base_values: &BaseValues,
    rule_name: &str,
    values: &[GenericAtomTerm<RuleVar, RuleValue>],
) -> Result<()> {
    let [value] = values else {
        bail!("DuckDB path rule `{rule_name}` proof Set must have one Unit value");
    };
    let value = literal(value)
        .ok_or_else(|| anyhow!("DuckDB path rule `{rule_name}` proof value must be a literal"))?;
    ensure!(scalar(base_values, value.ty)? == ScalarSqlType::Unit);
    Ok(())
}

fn scalar(base_values: &BaseValues, ty: ColumnTy) -> Result<ScalarSqlType> {
    ScalarSqlType::from_column(base_values, ty)
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

fn id_var<'a>(
    rule_name: &str,
    term: &'a GenericAtomTerm<RuleVar, RuleValue>,
) -> Result<&'a RuleVar> {
    let variable =
        var(term).ok_or_else(|| anyhow!("DuckDB path rule `{rule_name}` requires a variable"))?;
    ensure!(
        variable.ty == ColumnTy::Id,
        "DuckDB path rule `{rule_name}` requires Id variables"
    );
    Ok(variable)
}

fn same_var(rule_name: &str, expected: &RuleVar, actual: &RuleVar, role: &str) -> Result<()> {
    ensure!(
        expected.id == actual.id && expected.ty == actual.ty,
        "DuckDB path rule `{rule_name}` has inconsistent {role} variables"
    );
    Ok(())
}

fn distinct_vars(rule_name: &str, variables: &[&RuleVar]) -> Result<()> {
    for (index, left) in variables.iter().enumerate() {
        ensure!(
            variables[index + 1..]
                .iter()
                .all(|right| left.id != right.id),
            "DuckDB path rule `{rule_name}` aliases structurally distinct variables"
        );
    }
    Ok(())
}

pub(crate) fn safe_scratch_name(name: &str) -> bool {
    name.bytes()
        .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}
