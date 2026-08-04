//! Exact lowering for the reached proof-instrumented scalar rewrite family.
//!
//! This is intentionally not a general action interpreter. Admission owns only
//! the structurally generated 34-action family and records a closed, typed SQL
//! plan. DuckDB materializes matches, lookups, fresh slots, and effects; Rust
//! only schedules statements and observes scalar counts.

use std::collections::{BTreeMap, BTreeSet};

use crate::AuthorityRegistries;
use crate::rebuild::{
    OrderedUnionGraph, ordered_union_outer, validate_scalar_action_ordered_union,
    validate_scalar_mixed_ordered_union,
};
use crate::scalar_expr::{ScalarAuthority, ScalarExpression};
use crate::storage::{ScalarSqlType, Storage, TableInfo, WriteCapability, sql_table};
use anyhow::{Context, Result, anyhow, bail, ensure};
use egglog_ast::core::{GenericAtomTerm, GenericCoreAction};
use egglog_backend_trait::{
    BaseValues, ColumnTy, DefaultVal, ExternalFunctionId, FunctionId, MergeAction, MergeFn,
    NativePrimitive, NativeScalarPrimitive, ReadMode, RuleActionCall, RuleBodyCall, RuleSpec,
    RuleValue, RuleVar,
};
use egglog_numeric_id::NumericId;

const ACTION_COUNT: usize = 34;
const RAW_ACTION_COUNT: usize = 50;
const FRESH_COUNT: u64 = 14;
const DIRECT_EFFECT_COUNT: u64 = 15;

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

#[derive(Clone, Debug)]
enum ScalarSlotSource {
    Literal(ScalarLiteral),
    Lookup,
    Fresh {
        rank: u64,
        token: ExternalFunctionId,
        label: ScalarLiteral,
    },
    Alias(ScalarValueRef),
}

#[derive(Clone, Debug)]
struct ScalarSlotPlan {
    action_ordinal: usize,
    ty: ColumnTy,
    source: ScalarSlotSource,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ScalarEffectKind {
    AssertEq,
    KeepOld,
    OrderedUnion,
}

#[derive(Clone, Debug)]
pub(crate) struct ScalarEffectPlan {
    pub(crate) action_ordinal: usize,
    pub(crate) event_ordinal: u64,
    pub(crate) target: FunctionId,
    pub(crate) arity: usize,
    pub(crate) n_keys: usize,
    pub(crate) kind: ScalarEffectKind,
    arguments: Vec<ScalarValueRef>,
    values: Vec<ScalarValueRef>,
    condition_slot: Option<usize>,
}

#[derive(Clone, Debug)]
pub(crate) struct ScalarLookupPlan {
    pub(crate) target: FunctionId,
    pub(crate) n_keys: usize,
    keys: Vec<ScalarValueRef>,
}

#[derive(Clone, Debug)]
pub(crate) struct ScalarMixedPlan {
    seminaive: bool,
    body: FunctionId,
    body_schema: Vec<ColumnTy>,
    body_patterns: Vec<ScalarValueRef>,
    slots: Vec<ScalarSlotPlan>,
    lookup: ScalarLookupPlan,
    effects: Vec<ScalarEffectPlan>,
    graph: OrderedUnionGraph,
    fresh_token: ExternalFunctionId,
}

impl ScalarMixedPlan {
    pub(crate) fn fresh_slots(&self) -> u64 {
        FRESH_COUNT
    }

    pub(crate) fn direct_effects_per_match(&self) -> u64 {
        DIRECT_EFFECT_COUNT
    }

    pub(crate) fn action_count(&self) -> u64 {
        ACTION_COUNT as u64
    }

    pub(crate) fn lookup(&self) -> &ScalarLookupPlan {
        &self.lookup
    }

    pub(crate) fn effects(&self) -> &[ScalarEffectPlan] {
        &self.effects
    }

    pub(crate) fn graph(&self) -> &OrderedUnionGraph {
        &self.graph
    }

    pub(crate) fn materialize_match_sql(&self, stage: &str, watermark: u64) -> String {
        assert_scratch_name(stage);
        let projection = (0..self.body_schema.len())
            .map(|column| format!("source.c{column} AS b{column}"))
            .chain(std::iter::once(format!(
                "row_number() OVER (ORDER BY {}) AS __match_ordinal",
                std::iter::once("source.__generation".to_string())
                    .chain((0..self.body_schema.len()).map(|column| format!("source.c{column}")))
                    .collect::<Vec<_>>()
                    .join(", ")
            )))
            .collect::<Vec<_>>()
            .join(", ");
        let mut predicates = vec!["source.__subsumed = FALSE".to_string()];
        if self.seminaive {
            predicates.push(format!(
                "source.__generation >= CAST('{watermark}' AS UBIGINT)"
            ));
        }
        predicates.extend(
            self.body_patterns
                .iter()
                .enumerate()
                .filter_map(|(column, value)| match value {
                    ScalarValueRef::Literal(literal) => Some(format!(
                        "source.c{column} IS NOT DISTINCT FROM {}",
                        literal.sql
                    )),
                    ScalarValueRef::Body(_) => None,
                    ScalarValueRef::Slot(_) => {
                        unreachable!("body patterns cannot read action slots")
                    }
                }),
        );
        format!(
            "CREATE TEMP TABLE {stage} AS
             SELECT {projection}
             FROM {} AS source
             WHERE {}",
            sql_table(self.body),
            predicates.join(" AND ")
        )
    }

    pub(crate) fn lookup_cardinality_sql(&self, match_stage: &str) -> String {
        assert_scratch_name(match_stage);
        let equality = self.lookup_equality("matched", "existing");
        format!(
            "SELECT EXISTS (
                 SELECT 1
                 FROM {match_stage} AS matched
                 LEFT JOIN {} AS existing ON {equality}
                 GROUP BY matched.__match_ordinal
                 HAVING count(existing.__generation) <> 1
             )",
            sql_table(self.lookup.target)
        )
    }

    pub(crate) fn materialize_head_sql(
        &self,
        match_stage: &str,
        head_stage: &str,
        first_fresh: u64,
        match_count: u64,
    ) -> String {
        assert_scratch_name(match_stage);
        assert_scratch_name(head_stage);
        let equality = self.lookup_equality("matched", "existing");
        let mut projection = (0..self.body_schema.len())
            .map(|column| format!("matched.b{column} AS b{column}"))
            .collect::<Vec<_>>();
        projection.push("matched.__match_ordinal AS __match_ordinal".to_string());
        projection.extend(self.slots.iter().enumerate().map(|(slot, _)| {
            format!(
                "{} AS s{slot}",
                self.render_slot(slot, "matched", "existing", first_fresh, match_count)
            )
        }));
        format!(
            "CREATE TEMP TABLE {head_stage} AS
             SELECT {}
             FROM {match_stage} AS matched
             JOIN {} AS existing ON {equality}",
            projection.join(", "),
            sql_table(self.lookup.target)
        )
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
            .map(|(column, value)| {
                format!("{} AS c{column}", self.render_effect_ref(value, "head"))
            })
            .collect::<Vec<_>>();
        projection.push(format!(
            "CAST('{first_event}' AS UBIGINT) + head.__match_ordinal - 1 AS __ordinal"
        ));
        format!(
            "CREATE TEMP TABLE {effect_stage} AS
             SELECT {}
             FROM {head_stage} AS head
             ORDER BY head.__match_ordinal",
            projection.join(", ")
        )
    }

    fn lookup_equality(&self, matched: &str, existing: &str) -> String {
        self.lookup
            .keys
            .iter()
            .enumerate()
            .map(|(column, key)| {
                format!(
                    "{existing}.c{column} IS NOT DISTINCT FROM {}",
                    self.render_match_ref(key, matched)
                )
            })
            .collect::<Vec<_>>()
            .join(" AND ")
    }

    fn render_match_ref(&self, value: &ScalarValueRef, matched: &str) -> String {
        match value {
            ScalarValueRef::Body(column) => format!("{matched}.b{column}"),
            ScalarValueRef::Literal(literal) => literal.sql.clone(),
            ScalarValueRef::Slot(_) => {
                unreachable!("prewave lookup keys cannot read action slots")
            }
        }
    }

    fn render_slot(
        &self,
        slot: usize,
        matched: &str,
        existing: &str,
        first_fresh: u64,
        match_count: u64,
    ) -> String {
        let plan = &self.slots[slot];
        debug_assert!(plan.action_ordinal < ACTION_COUNT);
        match &plan.source {
            ScalarSlotSource::Literal(literal) => literal.sql.clone(),
            ScalarSlotSource::Lookup => {
                debug_assert_eq!(plan.ty, ColumnTy::Id);
                format!("{existing}.c{}", self.lookup.n_keys)
            }
            ScalarSlotSource::Fresh { rank, token, label } => {
                debug_assert_eq!(*token, self.fresh_token);
                debug_assert_eq!(label.scalar, ScalarSqlType::String);
                debug_assert_eq!(plan.ty, ColumnTy::Id);
                format!(
                    "CAST('{first_fresh}' AS UBIGINT)
                     + CAST('{rank}' AS UBIGINT) * CAST('{match_count}' AS UBIGINT)
                     + {matched}.__match_ordinal - 1"
                )
            }
            ScalarSlotSource::Alias(value) => {
                self.render_head_source_ref(value, matched, existing, first_fresh, match_count)
            }
        }
    }

    fn render_head_source_ref(
        &self,
        value: &ScalarValueRef,
        matched: &str,
        existing: &str,
        first_fresh: u64,
        match_count: u64,
    ) -> String {
        match value {
            ScalarValueRef::Body(column) => format!("{matched}.b{column}"),
            ScalarValueRef::Literal(literal) => literal.sql.clone(),
            ScalarValueRef::Slot(slot) => {
                self.render_slot(*slot, matched, existing, first_fresh, match_count)
            }
        }
    }

    fn render_effect_ref(&self, value: &ScalarValueRef, head: &str) -> String {
        match value {
            ScalarValueRef::Body(column) => format!("{head}.b{column}"),
            ScalarValueRef::Slot(slot) => format!("{head}.s{slot}"),
            ScalarValueRef::Literal(literal) => literal.sql.clone(),
        }
    }
}

#[derive(Clone)]
struct BoundValue {
    ty: ColumnTy,
    value: ScalarValueRef,
}

struct ScalarCompiler<'a> {
    storage: &'a Storage,
    base_values: &'a BaseValues,
    rule_name: &'a str,
    body_schema: Vec<ColumnTy>,
    body_patterns: Vec<ScalarValueRef>,
    bindings: BTreeMap<u32, BoundValue>,
    slots: Vec<ScalarSlotPlan>,
}

impl<'a> ScalarCompiler<'a> {
    fn new(
        storage: &'a Storage,
        base_values: &'a BaseValues,
        rule_name: &'a str,
        body_info: &TableInfo,
        body_args: &[GenericAtomTerm<RuleVar, RuleValue>],
    ) -> Result<Self> {
        let mut compiler = Self {
            storage,
            base_values,
            rule_name,
            body_schema: body_info.schema.clone(),
            body_patterns: Vec::with_capacity(body_info.arity()),
            bindings: BTreeMap::new(),
            slots: Vec::new(),
        };
        ensure!(
            body_args.len() == body_info.arity(),
            "DuckDB scalar-mixed rule `{rule_name}` body arity is incompatible with its View"
        );
        for (column, (term, &expected)) in body_args.iter().zip(&body_info.schema).enumerate() {
            let value = match term {
                GenericAtomTerm::Var(_, variable) => {
                    ensure!(
                        variable.ty == expected,
                        "DuckDB scalar-mixed rule `{rule_name}` body variable has the wrong type"
                    );
                    compiler.bind_body(variable, column)?;
                    ScalarValueRef::Body(column)
                }
                GenericAtomTerm::Literal(_, literal) => {
                    ensure!(
                        literal.ty == expected,
                        "DuckDB scalar-mixed rule `{rule_name}` body literal has the wrong type"
                    );
                    let scalar = ScalarSqlType::from_column(base_values, expected)?;
                    ScalarValueRef::Literal(ScalarLiteral {
                        value: *literal,
                        scalar,
                        sql: scalar.sql_literal(base_values, literal.value)?,
                    })
                }
                GenericAtomTerm::Global(..) => bail!(
                    "DuckDB scalar-mixed rule `{rule_name}` body contains an unsupported global"
                ),
            };
            compiler.body_patterns.push(value);
        }
        Ok(compiler)
    }

    fn bind_body(&mut self, variable: &RuleVar, column: usize) -> Result<()> {
        if self.bindings.contains_key(&variable.id) {
            bail!(
                "DuckDB scalar-mixed rule `{}` body rebinds SSA variable id {}",
                self.rule_name,
                variable.id
            );
        }
        self.bindings.insert(
            variable.id,
            BoundValue {
                ty: variable.ty,
                value: ScalarValueRef::Body(column),
            },
        );
        Ok(())
    }

    fn bind_passthrough_alias(
        &mut self,
        action_ordinal: usize,
        action: &GenericCoreAction<RuleActionCall, RuleVar, RuleValue>,
        expected: ScalarValueRef,
    ) -> Result<ScalarValueRef> {
        let GenericCoreAction::LetAtomTerm(_, binding, source) = action else {
            bail!(
                "DuckDB scalar-mixed rule `{}` action {action_ordinal} must be an SSA passthrough alias",
                self.rule_name
            );
        };
        let source = self.compile_term(source, binding.ty, "body-identity alias")?;
        ensure!(
            source == expected,
            "DuckDB scalar-mixed rule `{}` action {action_ordinal} aliases the wrong value",
            self.rule_name
        );
        if self.bindings.contains_key(&binding.id) {
            bail!(
                "DuckDB scalar-mixed rule `{}` action {action_ordinal} rebinds SSA variable id {}",
                self.rule_name,
                binding.id
            );
        }
        self.bindings.insert(
            binding.id,
            BoundValue {
                ty: binding.ty,
                value: source.clone(),
            },
        );
        Ok(source)
    }

    fn bind_slot(
        &mut self,
        action_ordinal: usize,
        variable: &RuleVar,
        source: ScalarSlotSource,
    ) -> Result<ScalarValueRef> {
        if self.bindings.contains_key(&variable.id) {
            bail!(
                "DuckDB scalar-mixed rule `{}` action {action_ordinal} rebinds SSA variable id {}",
                self.rule_name,
                variable.id
            );
        }
        let slot = self.slots.len();
        self.slots.push(ScalarSlotPlan {
            action_ordinal,
            ty: variable.ty,
            source,
        });
        let value = ScalarValueRef::Slot(slot);
        self.bindings.insert(
            variable.id,
            BoundValue {
                ty: variable.ty,
                value: value.clone(),
            },
        );
        Ok(value)
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
                    "DuckDB scalar-mixed rule `{}` {context} has a mistyped variable",
                    self.rule_name
                );
                let binding = self.bindings.get(&variable.id).ok_or_else(|| {
                    anyhow!(
                        "DuckDB scalar-mixed rule `{}` {context} uses variable id {} before binding",
                        self.rule_name,
                        variable.id
                    )
                })?;
                ensure!(
                    binding.ty == variable.ty,
                    "DuckDB scalar-mixed rule `{}` reuses variable id {} with inconsistent type metadata",
                    self.rule_name,
                    variable.id
                );
                Ok(binding.value.clone())
            }
            GenericAtomTerm::Literal(_, literal) => {
                ensure!(
                    literal.ty == expected,
                    "DuckDB scalar-mixed rule `{}` {context} has a mistyped literal",
                    self.rule_name
                );
                let scalar = ScalarSqlType::from_column(self.base_values, expected)?;
                let sql = scalar.sql_literal(self.base_values, literal.value)?;
                Ok(ScalarValueRef::Literal(ScalarLiteral {
                    value: *literal,
                    scalar,
                    sql,
                }))
            }
            GenericAtomTerm::Global(..) => bail!(
                "DuckDB scalar-mixed rule `{}` {context} contains an unsupported global",
                self.rule_name
            ),
        }
    }

    fn literal_slot(
        &mut self,
        action_ordinal: usize,
        action: &GenericCoreAction<RuleActionCall, RuleVar, RuleValue>,
        expected_scalar: ScalarSqlType,
    ) -> Result<ScalarValueRef> {
        let GenericCoreAction::LetAtomTerm(_, binding, source) = action else {
            bail!(
                "DuckDB scalar-mixed rule `{}` action {action_ordinal} must bind a typed literal",
                self.rule_name
            );
        };
        let value = self.compile_term(source, binding.ty, "literal binding")?;
        let ScalarValueRef::Literal(literal) = value else {
            bail!(
                "DuckDB scalar-mixed rule `{}` action {action_ordinal} must bind a literal",
                self.rule_name
            );
        };
        ensure!(
            literal.scalar == expected_scalar,
            "DuckDB scalar-mixed rule `{}` action {action_ordinal} binds the wrong scalar type",
            self.rule_name
        );
        self.bind_slot(action_ordinal, binding, ScalarSlotSource::Literal(literal))
    }

    fn lookup_slot(
        &mut self,
        action_ordinal: usize,
        action: &GenericCoreAction<RuleActionCall, RuleVar, RuleValue>,
        expected_key: ScalarValueRef,
    ) -> Result<(ScalarValueRef, ScalarLookupPlan)> {
        let GenericCoreAction::Let(_, binding, call, arguments) = action else {
            bail!(
                "DuckDB scalar-mixed rule `{}` action {action_ordinal} must be the action-side lookup",
                self.rule_name
            );
        };
        let RuleActionCall::Table { id: target, .. } = call else {
            bail!(
                "DuckDB scalar-mixed rule `{}` action {action_ordinal} must look up a table",
                self.rule_name
            );
        };
        let info = self.storage.table_info(*target).with_context(|| {
            format!(
                "DuckDB scalar-mixed rule `{}` has an invalid lookup target",
                self.rule_name
            )
        })?;
        validate_old_lookup(self.base_values, self.rule_name, &info)?;
        let [argument] = arguments.as_slice() else {
            bail!(
                "DuckDB scalar-mixed rule `{}` lookup must have one Id key",
                self.rule_name
            );
        };
        let key = self.compile_term(argument, ColumnTy::Id, "lookup key")?;
        ensure!(
            key == expected_key,
            "DuckDB scalar-mixed rule `{}` lookup must read the matched View identity",
            self.rule_name
        );
        ensure!(
            binding.ty == ColumnTy::Id,
            "DuckDB scalar-mixed rule `{}` lookup result must be Id",
            self.rule_name
        );
        let value = self.bind_slot(action_ordinal, binding, ScalarSlotSource::Lookup)?;
        Ok((
            value,
            ScalarLookupPlan {
                target: *target,
                n_keys: info.n_keys,
                keys: vec![key],
            },
        ))
    }

    fn fresh_slot(
        &mut self,
        action_ordinal: usize,
        action: &GenericCoreAction<RuleActionCall, RuleVar, RuleValue>,
        rank: u64,
        fresh_tokens: &BTreeSet<ExternalFunctionId>,
        expected_token: Option<ExternalFunctionId>,
    ) -> Result<(ScalarValueRef, ExternalFunctionId)> {
        let GenericCoreAction::Let(_, binding, call, arguments) = action else {
            bail!(
                "DuckDB scalar-mixed rule `{}` action {action_ordinal} must bind get-fresh!",
                self.rule_name
            );
        };
        let RuleActionCall::Primitive {
            id,
            name: _,
            output,
        } = call
        else {
            bail!(
                "DuckDB scalar-mixed rule `{}` action {action_ordinal} must call get-fresh!",
                self.rule_name
            );
        };
        ensure!(
            fresh_tokens.contains(id)
                && expected_token.is_none_or(|expected| *id == expected)
                && *output == ColumnTy::Id
                && binding.ty == ColumnTy::Id,
            "DuckDB scalar-mixed rule `{}` action {action_ordinal} has the wrong fresh token or signature",
            self.rule_name
        );
        let [argument] = arguments.as_slice() else {
            bail!(
                "DuckDB scalar-mixed rule `{}` action {action_ordinal} get-fresh! requires one String literal",
                self.rule_name
            );
        };
        let value = self.compile_term(argument, argument_ty(argument), "fresh label")?;
        let ScalarValueRef::Literal(label) = value else {
            bail!(
                "DuckDB scalar-mixed rule `{}` action {action_ordinal} fresh label must be literal",
                self.rule_name
            );
        };
        ensure!(
            label.scalar == ScalarSqlType::String,
            "DuckDB scalar-mixed rule `{}` action {action_ordinal} fresh label must be String",
            self.rule_name
        );
        Ok((
            self.bind_slot(
                action_ordinal,
                binding,
                ScalarSlotSource::Fresh {
                    rank,
                    token: *id,
                    label,
                },
            )?,
            *id,
        ))
    }

    fn alias_slot(
        &mut self,
        action_ordinal: usize,
        action: &GenericCoreAction<RuleActionCall, RuleVar, RuleValue>,
        expected: ScalarValueRef,
    ) -> Result<ScalarValueRef> {
        let GenericCoreAction::LetAtomTerm(_, binding, source) = action else {
            bail!(
                "DuckDB scalar-mixed rule `{}` action {action_ordinal} must be an SSA alias",
                self.rule_name
            );
        };
        let source = self.compile_term(source, binding.ty, "alias source")?;
        ensure!(
            source == expected,
            "DuckDB scalar-mixed rule `{}` action {action_ordinal} aliases the wrong value",
            self.rule_name
        );
        self.bind_slot(action_ordinal, binding, ScalarSlotSource::Alias(source))
    }

    fn set_effect(
        &self,
        action_ordinal: usize,
        action: &GenericCoreAction<RuleActionCall, RuleVar, RuleValue>,
        kind: ScalarEffectKind,
    ) -> Result<(ScalarEffectPlan, TableInfo)> {
        let GenericCoreAction::Set(_, call, arguments, values) = action else {
            bail!(
                "DuckDB scalar-mixed rule `{}` action {action_ordinal} must be a table Set",
                self.rule_name
            );
        };
        let RuleActionCall::Table { id: target, .. } = call else {
            bail!(
                "DuckDB scalar-mixed rule `{}` action {action_ordinal} cannot Set a primitive",
                self.rule_name
            );
        };
        let info = self.storage.table_info(*target).with_context(|| {
            format!(
                "DuckDB scalar-mixed rule `{}` action {action_ordinal} has an invalid target",
                self.rule_name
            )
        })?;
        ensure!(
            arguments.len() == info.n_keys && values.len() == info.n_vals,
            "DuckDB scalar-mixed rule `{}` action {action_ordinal} has the wrong Set arity",
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
        Ok((
            ScalarEffectPlan {
                action_ordinal,
                event_ordinal: u64::try_from(action_ordinal)?,
                target: *target,
                arity: info.arity(),
                n_keys: info.n_keys,
                kind,
                arguments,
                values,
                condition_slot: None,
            },
            info,
        ))
    }
}

pub(crate) fn compile_scalar_mixed(
    storage: &Storage,
    base_values: &BaseValues,
    native_primitives: &BTreeMap<ExternalFunctionId, NativePrimitive>,
    fresh_tokens: &BTreeSet<ExternalFunctionId>,
    rule: &RuleSpec,
) -> Result<Option<ScalarMixedPlan>> {
    let Some(body_target) = scalar_mixed_owner(storage, rule)? else {
        return Ok(None);
    };

    ensure!(
        rule.seminaive && !rule.no_decomp,
        "DuckDB scalar-mixed rule `{}` requires seminaive mode with decomposition enabled",
        rule.name
    );
    ensure!(
        rule.core.body.atoms.len() == 1,
        "DuckDB scalar-mixed rule `{}` must have exactly one body table",
        rule.name
    );
    let body_atom = &rule.core.body.atoms[0];
    let RuleBodyCall::Table { id: body, read } = body_atom.head else {
        bail!(
            "DuckDB scalar-mixed rule `{}` body must be one Live table",
            rule.name
        );
    };
    ensure!(
        body == body_target && read == ReadMode::Live,
        "DuckDB scalar-mixed rule `{}` body must be the selected Live View",
        rule.name
    );

    let graph = validate_scalar_mixed_ordered_union(
        base_values,
        storage,
        native_primitives,
        fresh_tokens,
        &rule.name,
        body,
    )?;
    ensure!(
        fresh_tokens.contains(&graph.fresh_token),
        "DuckDB scalar-mixed rule `{}` ordered-union graph does not use a live registered get-fresh token",
        rule.name
    );
    let body_info = storage.table_info(body)?;
    ensure!(
        rule.core.head.0.len() == RAW_ACTION_COUNT,
        "DuckDB scalar-mixed rule `{}` must have exactly {RAW_ACTION_COUNT} lowered actions (got {})",
        rule.name,
        rule.core.head.0.len()
    );
    let actions = &rule.core.head.0;
    let mut compiler = ScalarCompiler::new(
        storage,
        base_values,
        &rule.name,
        &body_info,
        &body_atom.args,
    )?;
    let identity = compiler.body_patterns[body_info.n_keys].clone();
    let body_payload = compiler.body_patterns[body_info.n_keys + 1].clone();
    ensure!(
        matches!(identity, ScalarValueRef::Body(_))
            && matches!(body_payload, ScalarValueRef::Body(_)),
        "DuckDB scalar-mixed rule `{}` must bind both View output columns",
        rule.name
    );

    // Core canonicalization prepends the substituted body identity and splits
    // every call-valued let into a call plus a passthrough alias. Validate and
    // collapse that exact 50-action scaffolding back to the 34 semantic actions
    // whose ordinals are observable in fresh/event allocation.
    let owner = compiler.bind_passthrough_alias(0, &actions[0], identity.clone())?;
    let rule_label = compiler.literal_slot(0, &actions[1], ScalarSqlType::String)?;
    let (lookup_value, lookup) = compiler.lookup_slot(1, &actions[2], owner.clone())?;
    compiler.bind_passthrough_alias(1, &actions[3], lookup_value.clone())?;
    let (f0, fresh_token) = compiler.fresh_slot(2, &actions[4], 0, fresh_tokens, None)?;
    compiler.bind_passthrough_alias(2, &actions[5], f0.clone())?;

    let mut effects = Vec::with_capacity(16);
    let (sym_first, sym_info) = compiler.set_effect(3, &actions[6], ScalarEffectKind::AssertEq)?;
    validate_assert_eq_unit(
        base_values,
        &rule.name,
        &sym_info,
        &[ColumnTy::Id, ColumnTy::Id],
    )?;
    expect_set(
        &rule.name,
        &sym_first,
        &[lookup_value.clone(), f0.clone()],
        true,
    )?;
    ensure!(sym_first.target == graph.root.sym);
    effects.push(sym_first);

    let (f1, _) = compiler.fresh_slot(4, &actions[7], 1, fresh_tokens, Some(fresh_token))?;
    compiler.bind_passthrough_alias(4, &actions[8], f1.clone())?;
    let (trans_first, trans_info) =
        compiler.set_effect(5, &actions[9], ScalarEffectKind::AssertEq)?;
    validate_assert_eq_unit(
        base_values,
        &rule.name,
        &trans_info,
        &[ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
    )?;
    expect_set(
        &rule.name,
        &trans_first,
        &[f0.clone(), body_payload, f1.clone()],
        true,
    )?;
    ensure!(trans_first.target == graph.root.trans);
    effects.push(trans_first);

    let (f2, _) = compiler.fresh_slot(6, &actions[10], 2, fresh_tokens, Some(fresh_token))?;
    compiler.bind_passthrough_alias(6, &actions[11], f2.clone())?;
    let (nil, nil_info) = compiler.set_effect(7, &actions[12], ScalarEffectKind::AssertEq)?;
    validate_assert_eq_unit(base_values, &rule.name, &nil_info, &[ColumnTy::Id])?;
    expect_set(&rule.name, &nil, std::slice::from_ref(&f2), true)?;
    effects.push(nil);

    let (f3, _) = compiler.fresh_slot(8, &actions[13], 3, fresh_tokens, Some(fresh_token))?;
    compiler.bind_passthrough_alias(8, &actions[14], f3.clone())?;
    let (cons, cons_info) = compiler.set_effect(9, &actions[15], ScalarEffectKind::AssertEq)?;
    validate_assert_eq_unit(
        base_values,
        &rule.name,
        &cons_info,
        &[ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
    )?;
    expect_set(
        &rule.name,
        &cons,
        &[f1.clone(), f2.clone(), f3.clone()],
        true,
    )?;
    effects.push(cons);
    let proof_list = compiler.alias_slot(10, &actions[16], f3.clone())?;

    let (f4, _) = compiler.fresh_slot(11, &actions[17], 4, fresh_tokens, Some(fresh_token))?;
    compiler.bind_passthrough_alias(11, &actions[18], f4.clone())?;
    let (term, term_info) = compiler.set_effect(12, &actions[19], ScalarEffectKind::AssertEq)?;
    ensure!(
        term.arguments.last() == Some(&f4),
        "DuckDB scalar-mixed rule `{}` constructor Set must end in its fresh Id",
        rule.name
    );
    let child_refs = term.arguments[..term.arguments.len() - 1].to_vec();
    validate_body_key_permutation(
        &rule.name,
        &child_refs,
        &compiler.body_patterns[..body_info.n_keys],
    )?;
    let mut term_keys = child_refs
        .iter()
        .map(|value| value_ty(value, &compiler))
        .collect::<Result<Vec<_>>>()?;
    term_keys.push(ColumnTy::Id);
    validate_assert_eq_unit(base_values, &rule.name, &term_info, &term_keys)?;
    expect_unit_value(&rule.name, &term)?;
    effects.push(term);

    let (f5, _) = compiler.fresh_slot(13, &actions[20], 5, fresh_tokens, Some(fresh_token))?;
    compiler.bind_passthrough_alias(13, &actions[21], f5.clone())?;
    let (ast_first, ast_info) =
        compiler.set_effect(14, &actions[22], ScalarEffectKind::AssertEq)?;
    validate_assert_eq_unit(
        base_values,
        &rule.name,
        &ast_info,
        &[ColumnTy::Id, ColumnTy::Id],
    )?;
    expect_set(&rule.name, &ast_first, &[f4.clone(), f5.clone()], true)?;
    effects.push(ast_first);

    let (f6, _) = compiler.fresh_slot(15, &actions[23], 6, fresh_tokens, Some(fresh_token))?;
    compiler.bind_passthrough_alias(15, &actions[24], f6.clone())?;
    let (ast_second, ast_second_info) =
        compiler.set_effect(16, &actions[25], ScalarEffectKind::AssertEq)?;
    validate_assert_eq_unit(
        base_values,
        &rule.name,
        &ast_second_info,
        &[ColumnTy::Id, ColumnTy::Id],
    )?;
    ensure!(ast_second.target == effects[5].target);
    expect_set(&rule.name, &ast_second, &[f4.clone(), f6.clone()], true)?;
    effects.push(ast_second);

    let (f7, _) = compiler.fresh_slot(17, &actions[26], 7, fresh_tokens, Some(fresh_token))?;
    compiler.bind_passthrough_alias(17, &actions[27], f7.clone())?;
    let (rule_first, rule_info) =
        compiler.set_effect(18, &actions[28], ScalarEffectKind::AssertEq)?;
    validate_assert_eq_unit(
        base_values,
        &rule.name,
        &rule_info,
        &[
            rule_value_ty(&rule_label, &compiler)?,
            ColumnTy::Id,
            ColumnTy::Id,
            ColumnTy::Id,
            ColumnTy::Id,
        ],
    )?;
    expect_set(
        &rule.name,
        &rule_first,
        &[
            rule_label.clone(),
            proof_list.clone(),
            f5.clone(),
            f6.clone(),
            f7.clone(),
        ],
        true,
    )?;
    effects.push(rule_first);

    let (old, old_info) = compiler.set_effect(19, &actions[29], ScalarEffectKind::KeepOld)?;
    validate_old_target(base_values, &rule.name, &old_info)?;
    ensure!(
        old.target == lookup.target,
        "DuckDB scalar-mixed rule `{}` action 19 must Set the action-1 Old lookup target",
        rule.name
    );
    expect_set(&rule.name, &old, &[f4.clone(), f7.clone()], false)?;
    effects.push(old);

    let (f8, _) = compiler.fresh_slot(20, &actions[30], 8, fresh_tokens, Some(fresh_token))?;
    compiler.bind_passthrough_alias(20, &actions[31], f8.clone())?;
    let (ast_third, ast_third_info) =
        compiler.set_effect(21, &actions[32], ScalarEffectKind::AssertEq)?;
    validate_assert_eq_unit(
        base_values,
        &rule.name,
        &ast_third_info,
        &[ColumnTy::Id, ColumnTy::Id],
    )?;
    ensure!(ast_third.target == effects[5].target);
    expect_set(&rule.name, &ast_third, &[owner.clone(), f8.clone()], true)?;
    effects.push(ast_third);

    let (f9, _) = compiler.fresh_slot(22, &actions[33], 9, fresh_tokens, Some(fresh_token))?;
    compiler.bind_passthrough_alias(22, &actions[34], f9.clone())?;
    let (ast_fourth, ast_fourth_info) =
        compiler.set_effect(23, &actions[35], ScalarEffectKind::AssertEq)?;
    validate_assert_eq_unit(
        base_values,
        &rule.name,
        &ast_fourth_info,
        &[ColumnTy::Id, ColumnTy::Id],
    )?;
    ensure!(ast_fourth.target == effects[5].target);
    expect_set(&rule.name, &ast_fourth, &[f4.clone(), f9.clone()], true)?;
    effects.push(ast_fourth);

    let (f10, _) = compiler.fresh_slot(24, &actions[36], 10, fresh_tokens, Some(fresh_token))?;
    compiler.bind_passthrough_alias(24, &actions[37], f10.clone())?;
    let (rule_second, rule_second_info) =
        compiler.set_effect(25, &actions[38], ScalarEffectKind::AssertEq)?;
    validate_assert_eq_unit(
        base_values,
        &rule.name,
        &rule_second_info,
        &[
            rule_value_ty(&rule_label, &compiler)?,
            ColumnTy::Id,
            ColumnTy::Id,
            ColumnTy::Id,
            ColumnTy::Id,
        ],
    )?;
    ensure!(rule_second.target == effects[7].target);
    expect_set(
        &rule.name,
        &rule_second,
        &[rule_label, proof_list, f8, f9, f10.clone()],
        true,
    )?;
    effects.push(rule_second);

    let (f11, _) = compiler.fresh_slot(26, &actions[39], 11, fresh_tokens, Some(fresh_token))?;
    compiler.bind_passthrough_alias(26, &actions[40], f11.clone())?;
    let (trans_second, trans_second_info) =
        compiler.set_effect(27, &actions[41], ScalarEffectKind::AssertEq)?;
    validate_assert_eq_unit(
        base_values,
        &rule.name,
        &trans_second_info,
        &[ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
    )?;
    ensure!(trans_second.target == graph.root.trans);
    expect_set(
        &rule.name,
        &trans_second,
        &[f10, f7.clone(), f11.clone()],
        true,
    )?;
    effects.push(trans_second);

    let (view, _) = compiler.set_effect(28, &actions[42], ScalarEffectKind::OrderedUnion)?;
    ensure!(
        view.target == body
            && view.arguments == child_refs
            && view.values == [owner.clone(), f11.clone()],
        "DuckDB scalar-mixed rule `{}` action 28 must Set the selected View with the constructed key and matched identity",
        rule.name
    );
    effects.push(view);
    let union_alias = compiler.alias_slot(29, &actions[43], owner.clone())?;
    ensure!(union_alias != owner);

    let (f12, _) = compiler.fresh_slot(30, &actions[44], 12, fresh_tokens, Some(fresh_token))?;
    compiler.bind_passthrough_alias(30, &actions[45], f12.clone())?;
    let (sym_second, sym_second_info) =
        compiler.set_effect(31, &actions[46], ScalarEffectKind::AssertEq)?;
    validate_assert_eq_unit(
        base_values,
        &rule.name,
        &sym_second_info,
        &[ColumnTy::Id, ColumnTy::Id],
    )?;
    ensure!(sym_second.target == graph.root.sym);
    expect_set(&rule.name, &sym_second, &[f11.clone(), f12.clone()], true)?;
    effects.push(sym_second);

    let (f13, _) = compiler.fresh_slot(32, &actions[47], 13, fresh_tokens, Some(fresh_token))?;
    compiler.bind_passthrough_alias(32, &actions[48], f13.clone())?;
    let (trans_third, trans_third_info) =
        compiler.set_effect(33, &actions[49], ScalarEffectKind::AssertEq)?;
    validate_assert_eq_unit(
        base_values,
        &rule.name,
        &trans_third_info,
        &[ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
    )?;
    ensure!(trans_third.target == graph.root.trans);
    expect_set(&rule.name, &trans_third, &[f7, f12, f13], true)?;
    effects.push(trans_third);

    validate_distinct_roles(&rule.name, &effects, &graph)?;
    ensure!(
        effects
            .iter()
            .filter(|effect| effect.kind != ScalarEffectKind::OrderedUnion)
            .count()
            == DIRECT_EFFECT_COUNT as usize
            && effects.len() == 16,
        "DuckDB scalar-mixed rule `{}` has the wrong effect topology",
        rule.name
    );

    Ok(Some(ScalarMixedPlan {
        seminaive: rule.seminaive,
        body,
        body_schema: body_info.schema,
        body_patterns: compiler.body_patterns,
        slots: compiler.slots,
        lookup,
        effects,
        graph,
        fresh_token,
    }))
}

fn scalar_mixed_owner(storage: &Storage, rule: &RuleSpec) -> Result<Option<FunctionId>> {
    if rule.core.head.0.len() <= 1 || rule.core.body.atoms.len() != 1 {
        return Ok(None);
    }
    let RuleBodyCall::Table {
        id: body,
        read: ReadMode::Live,
    } = rule.core.body.atoms[0].head
    else {
        return Ok(None);
    };
    let info = storage.table_info(body)?;
    if !info.can_subsume {
        return Ok(None);
    }
    let sets_body = rule.core.head.0.iter().any(|action| {
        matches!(
            action,
            GenericCoreAction::Set(
                _,
                RuleActionCall::Table { id: target, .. },
                _,
                _
            ) if *target == body
        )
    });
    if !sets_body {
        return Ok(None);
    }
    let Some(displaced) = ordered_union_outer(&info.merge) else {
        return Ok(None);
    };
    let displaced_info = storage.table_info(displaced)?;
    if ordered_union_outer(&displaced_info.merge).is_some() {
        return Ok(Some(body));
    }
    Ok(None)
}

fn argument_ty(term: &GenericAtomTerm<RuleVar, RuleValue>) -> ColumnTy {
    match term {
        GenericAtomTerm::Var(_, variable) => variable.ty,
        GenericAtomTerm::Literal(_, literal) => literal.ty,
        GenericAtomTerm::Global(_, global) => global.ty,
    }
}

fn validate_old_lookup(base_values: &BaseValues, rule_name: &str, info: &TableInfo) -> Result<()> {
    ensure!(
        info.schema == [ColumnTy::Id, ColumnTy::Id]
            && info.n_keys == 1
            && info.n_vals == 1
            && info.n_identity_vals.is_none()
            && matches!(info.default, DefaultVal::Fail)
            && matches!(info.merge.as_ref(), MergeFn::Old)
            && !info.can_subsume
            && info.write_capability == WriteCapability::KeepOld,
        "DuckDB scalar-mixed rule `{rule_name}` lookup must be exact Fail/Old [Id] -> Id"
    );
    let id = ScalarSqlType::from_column(base_values, ColumnTy::Id)?;
    ensure!(info.columns.iter().all(|&ty| ty == id));
    Ok(())
}

fn validate_old_target(base_values: &BaseValues, rule_name: &str, info: &TableInfo) -> Result<()> {
    validate_old_lookup(base_values, rule_name, info).map_err(|error| {
        anyhow!("DuckDB scalar-mixed rule `{rule_name}` Old target is incompatible: {error:#}")
    })
}

fn validate_assert_eq_unit(
    base_values: &BaseValues,
    rule_name: &str,
    info: &TableInfo,
    key_types: &[ColumnTy],
) -> Result<()> {
    ensure!(
        info.n_keys == key_types.len()
            && info.n_vals == 1
            && info.arity() == key_types.len() + 1
            && info.schema[..info.n_keys] == *key_types
            && ScalarSqlType::from_column(base_values, info.schema[info.n_keys])?
                == ScalarSqlType::Unit
            && info.n_identity_vals.is_none()
            && matches!(info.default, DefaultVal::Fail)
            && matches!(info.merge.as_ref(), MergeFn::AssertEq)
            && !info.can_subsume
            && info.write_capability == WriteCapability::AssertEq,
        "DuckDB scalar-mixed rule `{rule_name}` AssertEq/Unit target has an incompatible configuration"
    );
    Ok(())
}

fn expect_set(
    rule_name: &str,
    effect: &ScalarEffectPlan,
    expected_arguments: &[ScalarValueRef],
    unit_value: bool,
) -> Result<()> {
    if unit_value {
        ensure!(
            effect.arguments == expected_arguments,
            "DuckDB scalar-mixed rule `{rule_name}` action {} has the wrong typed dataflow",
            effect.action_ordinal
        );
        expect_unit_value(rule_name, effect)?;
    } else {
        ensure!(
            effect
                .arguments
                .iter()
                .chain(&effect.values)
                .eq(expected_arguments),
            "DuckDB scalar-mixed rule `{rule_name}` action {} has the wrong Old target dataflow",
            effect.action_ordinal
        );
    }
    Ok(())
}

fn expect_unit_value(rule_name: &str, effect: &ScalarEffectPlan) -> Result<()> {
    let [ScalarValueRef::Literal(literal)] = effect.values.as_slice() else {
        bail!(
            "DuckDB scalar-mixed rule `{rule_name}` action {} must Set a Unit literal",
            effect.action_ordinal
        );
    };
    ensure!(
        literal.scalar == ScalarSqlType::Unit,
        "DuckDB scalar-mixed rule `{rule_name}` action {} must Set Unit",
        effect.action_ordinal
    );
    Ok(())
}

fn validate_body_key_permutation(
    rule_name: &str,
    keys: &[ScalarValueRef],
    body_keys: &[ScalarValueRef],
) -> Result<()> {
    ensure!(
        keys.len() == body_keys.len(),
        "DuckDB scalar-mixed rule `{rule_name}` constructed key has the wrong arity"
    );
    let mut remaining = body_keys.to_vec();
    for key in keys {
        let Some(index) = remaining.iter().position(|body| body == key) else {
            bail!(
                "DuckDB scalar-mixed rule `{rule_name}` constructed View key must permute body keys"
            );
        };
        remaining.remove(index);
    }
    ensure!(
        remaining.is_empty(),
        "DuckDB scalar-mixed rule `{rule_name}` constructed View key must use every body key once"
    );
    Ok(())
}

fn value_ty(value: &ScalarValueRef, compiler: &ScalarCompiler<'_>) -> Result<ColumnTy> {
    Ok(match value {
        ScalarValueRef::Body(column) => compiler.body_schema[*column],
        ScalarValueRef::Slot(slot) => compiler.slots[*slot].ty,
        ScalarValueRef::Literal(literal) => literal.value.ty,
    })
}

fn rule_value_ty(value: &ScalarValueRef, compiler: &ScalarCompiler<'_>) -> Result<ColumnTy> {
    let ty = value_ty(value, compiler)?;
    ensure!(
        ScalarSqlType::from_column(compiler.base_values, ty)? == ScalarSqlType::String,
        "DuckDB scalar-mixed rule `{}` rule label must be String",
        compiler.rule_name
    );
    Ok(ty)
}

fn validate_distinct_roles(
    rule_name: &str,
    effects: &[ScalarEffectPlan],
    graph: &OrderedUnionGraph,
) -> Result<()> {
    let roles = [
        graph.root.sym,
        graph.root.trans,
        effects[2].target,
        effects[3].target,
        effects[4].target,
        effects[5].target,
        effects[7].target,
        effects[8].target,
        graph.root.target,
        graph.displaced.target,
    ];
    ensure!(
        roles.into_iter().collect::<BTreeSet<_>>().len() == roles.len(),
        "DuckDB scalar-mixed rule `{rule_name}` aliases distinct generated table roles"
    );
    Ok(())
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
    graphs: Vec<OrderedUnionGraph>,
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

    pub(crate) fn effects(&self) -> &[ScalarEffectPlan] {
        &self.effects
    }

    pub(crate) fn graphs(&self) -> &[OrderedUnionGraph] {
        &self.graphs
    }

    pub(crate) fn owner_checks(&self) -> Vec<(FunctionId, usize, bool)> {
        let mut checks = Vec::new();
        // A standalone UF aliases the effect target and displaced target. Both
        // occurrences must request the stronger non-subsumed owner invariant.
        let displaced_targets = self
            .graphs
            .iter()
            .map(|graph| graph.displaced.target)
            .collect::<BTreeSet<_>>();
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
        checks.extend(self.effects.iter().map(|effect| {
            (
                effect.target,
                effect.n_keys,
                displaced_targets.contains(&effect.target),
            )
        }));
        checks.extend(
            self.graphs
                .iter()
                .map(|graph| (graph.displaced.target, graph.displaced.n_keys, true)),
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
            ScalarActionSlotSource::Read(read) => {
                let (target, n_keys, keys, result_column, fallback, invalid, missing) = match read {
                    ScalarActionRead::SetIfEmpty {
                        target,
                        n_keys,
                        keys,
                        defaults,
                    } => (
                        *target,
                        *n_keys,
                        keys,
                        *n_keys,
                        Some(&defaults[0]),
                        "lookup.__owners > 1",
                        true,
                    ),
                    ScalarActionRead::ViewColumn {
                        target,
                        n_keys,
                        result_column,
                        keys,
                        fallback,
                    } => (
                        *target,
                        *n_keys,
                        keys,
                        *result_column,
                        Some(fallback),
                        "lookup.__owners > 1",
                        false,
                    ),
                    ScalarActionRead::Table { .. } => unreachable!("handled above"),
                };
                debug_assert_eq!(keys.len(), n_keys);
                let equality = render_read_equality(keys, n_keys, "prior");
                let value = fallback.map_or_else(
                    || "lookup.__value".to_string(),
                    |fallback| {
                        format!(
                            "CASE WHEN lookup.__owners = 0 THEN {} ELSE lookup.__value END",
                            render_general_ref(fallback, "prior")
                        )
                    },
                );
                let missing_projection =
                    missing.then(|| format!(", lookup.__owners = 0 AS __missing_s{slot_index}"));
                format!(
                    "CREATE TEMP TABLE {output_stage} AS
                     SELECT prior.*,
                            {value} AS s{slot_index},
                            {invalid} AS __invalid_s{slot_index}{}
                     FROM {input_stage} AS prior
                     LEFT JOIN LATERAL (
                         SELECT count(existing.__generation) AS __owners,
                                first(existing.c{result_column} ORDER BY existing.__generation)
                                    AS __value
                         FROM {} AS existing
                         WHERE {equality}
                     ) AS lookup ON TRUE",
                    missing_projection.unwrap_or_default(),
                    sql_table(target)
                )
            }
        }
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
        matches!(
            self.slots[slot_index].source,
            ScalarActionSlotSource::Read(
                ScalarActionRead::SetIfEmpty { .. } | ScalarActionRead::ViewColumn { .. }
            )
        )
        .then(|| format!("SELECT EXISTS (SELECT 1 FROM {stage} WHERE __invalid_s{slot_index})"))
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
        required_native_primitives: BTreeMap::new(),
        required_native_scalar_primitives: BTreeMap::new(),
    };

    for (atom_index, atom) in rule.core.body.atoms.iter().enumerate() {
        match &atom.head {
            RuleBodyCall::Table { id, read } => {
                ensure!(
                    *read == ReadMode::Live,
                    "DuckDB scalar rule `{}` requests {read:?}; only Live table reads are supported",
                    rule.name
                );
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
                plan.match_predicates
                    .push(format!("{alias}.__subsumed = FALSE"));
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

fn retain_native_merge_dependencies(
    merge: &MergeFn,
    native_primitives: &BTreeMap<ExternalFunctionId, NativePrimitive>,
    required: &mut BTreeMap<ExternalFunctionId, NativePrimitive>,
) {
    match merge {
        MergeFn::Primitive { id, args, .. } => {
            if let Some(&descriptor) = native_primitives.get(id) {
                required.insert(*id, descriptor);
            }
            for argument in args {
                retain_native_merge_dependencies(argument, native_primitives, required);
            }
        }
        MergeFn::Function(_, arguments) | MergeFn::Lookup(_, arguments) => {
            for argument in arguments {
                retain_native_merge_dependencies(argument, native_primitives, required);
            }
        }
        MergeFn::Columns(columns) => {
            for column in columns {
                retain_native_merge_dependencies(column, native_primitives, required);
            }
        }
        MergeFn::Block { actions, result } => {
            for action in actions {
                match action {
                    MergeAction::Set(_, arguments) => {
                        for argument in arguments {
                            retain_native_merge_dependencies(argument, native_primitives, required);
                        }
                    }
                    MergeAction::Let { value, .. } => {
                        retain_native_merge_dependencies(value, native_primitives, required);
                    }
                    MergeAction::Union(left, right) => {
                        retain_native_merge_dependencies(left, native_primitives, required);
                        retain_native_merge_dependencies(right, native_primitives, required);
                    }
                }
            }
            retain_native_merge_dependencies(result, native_primitives, required);
        }
        MergeFn::AssertEq
        | MergeFn::UnionId
        | MergeFn::Old
        | MergeFn::New
        | MergeFn::OldCol(_)
        | MergeFn::NewCol(_)
        | MergeFn::LetVar(_)
        | MergeFn::Const { .. } => {}
    }
}

struct GeneralScalarCompiler<'a> {
    storage: &'a Storage,
    base_values: &'a BaseValues,
    native_primitives: &'a BTreeMap<ExternalFunctionId, NativePrimitive>,
    native_scalar_primitives: &'a BTreeMap<ExternalFunctionId, NativeScalarPrimitive>,
    fresh_tokens: &'a BTreeSet<ExternalFunctionId>,
    fd_descriptors: &'a BTreeMap<ExternalFunctionId, FdDescriptor>,
    rule_name: &'a str,
    bindings: BTreeMap<u32, BoundValue>,
    slots: Vec<ScalarActionSlot>,
    effects: Vec<ScalarEffectPlan>,
    graphs: Vec<OrderedUnionGraph>,
    fresh_rank: u64,
    runtime_ordinal: u64,
    required_fresh_tokens: BTreeSet<ExternalFunctionId>,
    required_fd_descriptors: BTreeMap<ExternalFunctionId, FdDescriptor>,
    required_native_primitives: BTreeMap<ExternalFunctionId, NativePrimitive>,
    required_native_scalar_primitives: BTreeMap<ExternalFunctionId, NativeScalarPrimitive>,
}

impl<'a> GeneralScalarCompiler<'a> {
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
                let graph = validate_scalar_action_ordered_union(
                    self.base_values,
                    self.storage,
                    self.native_primitives,
                    self.fresh_tokens,
                    self.rule_name,
                    target,
                )?;
                self.required_fresh_tokens.insert(graph.fresh_token);
                retain_native_merge_dependencies(
                    info.merge.as_ref(),
                    self.native_primitives,
                    &mut self.required_native_primitives,
                );
                let displaced = self.storage.table_info(graph.displaced.target).with_context(|| {
                    format!(
                        "DuckDB scalar rule `{}` ordered-union graph references invalid displaced target {}",
                        self.rule_name,
                        graph.displaced.target.rep()
                    )
                })?;
                retain_native_merge_dependencies(
                    displaced.merge.as_ref(),
                    self.native_primitives,
                    &mut self.required_native_primitives,
                );
                if let Some(existing) = self
                    .graphs
                    .iter()
                    .find(|existing| existing.root.target == graph.root.target)
                {
                    ensure!(
                        existing == &graph,
                        "DuckDB scalar rule `{}` has inconsistent ordered-union graphs for target {}",
                        self.rule_name,
                        target.rep()
                    );
                } else {
                    self.graphs.push(graph);
                }
                ScalarEffectKind::OrderedUnion
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
            action_ordinal: raw_action_ordinal,
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
                                action_ordinal: raw_action_ordinal,
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
    let exact_transcript = looks_like_exact_scalar_transcript(rule);
    if exact_transcript && scalar_mixed_owner(storage, rule)?.is_some() {
        compile_scalar_mixed(storage, base_values, native_primitives, fresh_tokens, rule)?
            .context("DuckDB exact scalar transcript was not owned by its oracle")?;
    }
    if rule.core.head.0.is_empty()
        || !rule.core.body.atoms.iter().all(|atom| {
            matches!(
                atom.head,
                RuleBodyCall::Table {
                    read: ReadMode::Live,
                    ..
                } | RuleBodyCall::Primitive { .. }
            )
        })
        || !rule.core.head.0.iter().all(|action| {
            matches!(
                action,
                GenericCoreAction::Let(..)
                    | GenericCoreAction::LetAtomTerm(..)
                    | GenericCoreAction::Set(..)
            )
        })
    {
        return Ok(None);
    }
    let owns_deferred_single_set = match rule.core.head.0.as_slice() {
        [GenericCoreAction::Set(_, RuleActionCall::Table { id: target, .. }, _, _)] => {
            storage.table_info(*target)?.write_capability == WriteCapability::Deferred
        }
        _ => false,
    };
    let owns = rule.core.body.atoms.is_empty()
        || rule
            .core
            .body
            .atoms
            .iter()
            .any(|atom| matches!(atom.head, RuleBodyCall::Primitive { .. }))
        || rule.core.head.0.len() > 1
        || owns_deferred_single_set
        || rule.core.head.0.iter().any(|action| {
            matches!(
                action,
                GenericCoreAction::Let(..) | GenericCoreAction::LetAtomTerm(..)
            )
        });
    if !owns {
        return Ok(None);
    }

    // Preserve the reached 50-action compiler as a strict oracle for that
    // generated family, while executing its accepted transcript through the
    // general plan below.
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
        fresh_tokens,
        fd_descriptors,
        rule_name: &rule.name,
        bindings,
        slots: Vec::new(),
        effects: Vec::new(),
        graphs: Vec::new(),
        fresh_rank: 0,
        runtime_ordinal: 0,
        required_fresh_tokens: BTreeSet::new(),
        required_fd_descriptors: BTreeMap::new(),
        required_native_primitives: body.required_native_primitives,
        required_native_scalar_primitives: body.required_native_scalar_primitives,
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
            GenericCoreAction::Change(..)
            | GenericCoreAction::Union(..)
            | GenericCoreAction::Panic(..) => unreachable!("owner vocabulary checked above"),
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
    let required_authority_epochs = required_tokens
        .into_iter()
        .map(|token| {
            authority_epochs
                .get(&token)
                .copied()
                .map(|epoch| (token, epoch))
                .ok_or_else(|| {
                    anyhow!(
                        "DuckDB scalar rule `{}` has no live authority epoch for token {}",
                        rule.name,
                        token.rep()
                    )
                })
        })
        .collect::<Result<BTreeMap<_, _>>>()?;

    Ok(Some(ScalarActionPlan {
        seminaive: rule.seminaive,
        match_projection: body.match_projection,
        match_from: body.match_from,
        match_predicates: body.match_predicates,
        freshness_columns: body.freshness_columns,
        order_columns: body.order_columns,
        slots: compiler.slots,
        effects: compiler.effects,
        graphs: compiler.graphs,
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

fn looks_like_exact_scalar_transcript(rule: &RuleSpec) -> bool {
    (RAW_ACTION_COUNT - 1..=RAW_ACTION_COUNT).contains(&rule.core.head.0.len())
        && rule
            .core
            .head
            .0
            .iter()
            .filter(|action| matches!(action, GenericCoreAction::LetAtomTerm(..)))
            .count()
            >= 14
        && rule
            .core
            .head
            .0
            .iter()
            .filter(|action| matches!(action, GenericCoreAction::Let(..)))
            .count()
            >= 14
        && rule
            .core
            .head
            .0
            .iter()
            .filter(|action| matches!(action, GenericCoreAction::Set(..)))
            .count()
            >= 14
}
