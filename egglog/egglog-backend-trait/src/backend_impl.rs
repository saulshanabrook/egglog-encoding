//! `impl Backend for egglog_bridge::EGraph` — the in-memory reference backend.
//!
//! Every method is a thin passthrough to an inherent method on the bridge
//! `EGraph`. Lives in this crate (not in `egglog-bridge`) so the bridge stays
//! free of any dependency on the trait; the orphan rule permits it because the
//! [`Backend`] trait is local here.

use std::any::{Any, TypeId};
use std::collections::BTreeMap;
use std::sync::{Arc, RwLock};

use anyhow::{Result, bail};
use egglog_bridge::{
    ActionRegistry, CriterionCapturePremise as BridgeCriterionCapturePremise,
    CriterionCaptureSpec as BridgeCriterionCaptureSpec, EGraph,
    FiringCaptureBinding as BridgeFiringCaptureBinding,
    FiringCaptureSpec as BridgeFiringCaptureSpec, QueryEntry, RuleBuilder,
};

use egglog_ast::core::{GenericAtomTerm, GenericCoreAction};

use crate::{
    Backend, BaseValues, ColumnTy, ContainerValues, CriterionCapturePremise, ExecutionState,
    ExternalFunction, ExternalFunctionId, FiringCaptureBinding, FunctionConfig, FunctionId,
    FunctionReplaySpec, IterationReport, ReplayLiteral, ReplaySortId, ReplayTermId, ReportLevel,
    RuleActionCall, RuleBodyCall, RuleCaptureSpec, RuleId, RuleSetRun, RuleSpec, RuleValue,
    RuleVar, ScanEntry, TraceLifecycleError, Value,
};

fn rule_entry(
    builder: &mut RuleBuilder<'_>,
    variables: &mut BTreeMap<u32, QueryEntry>,
    term: &GenericAtomTerm<RuleVar, RuleValue>,
) -> Result<QueryEntry> {
    match term {
        GenericAtomTerm::Var(_, variable) => Ok(variables
            .entry(variable.id)
            .or_insert_with(|| builder.new_var_named(variable.ty, &variable.name))
            .clone()),
        GenericAtomTerm::Literal(_, constant) => Ok(QueryEntry::Const {
            val: constant.value,
            ty: constant.ty,
        }),
        GenericAtomTerm::Global(..) => bail!("globals must be desugared before backend lowering"),
    }
}

fn rule_entries(
    builder: &mut RuleBuilder<'_>,
    variables: &mut BTreeMap<u32, QueryEntry>,
    terms: &[GenericAtomTerm<RuleVar, RuleValue>],
) -> Result<Vec<QueryEntry>> {
    terms
        .iter()
        .map(|term| rule_entry(builder, variables, term))
        .collect()
}

fn build_rule(egraph: &mut EGraph, rule: RuleSpec) -> Result<RuleId> {
    let RuleSpec {
        name,
        seminaive,
        no_decomp,
        core,
        capture,
        owned_external_funcs,
    } = rule;
    let mut builder = egraph.new_rule(&name, seminaive);
    for func in owned_external_funcs {
        builder.own_external_func(func);
    }
    if let Some(RuleCaptureSpec::Source(capture)) = &capture {
        builder.set_source_capture(capture.source.clone());
    }
    builder.set_no_decomp(no_decomp);
    let mut variables = BTreeMap::new();
    let mut union_sorts = match &capture {
        Some(RuleCaptureSpec::Firing(capture)) => Some(capture.union_sorts.iter().copied()),
        Some(RuleCaptureSpec::Source(capture)) => Some(capture.union_sorts.iter().copied()),
        Some(RuleCaptureSpec::Criterion(_)) | None => None,
    };

    let mut body_atom_to_table_premise = vec![None; core.body.atoms.len()];
    let mut next_table_premise = 0;
    for (body_atom, atom) in core.body.atoms.iter().enumerate() {
        let entries = rule_entries(&mut builder, &mut variables, &atom.args)?;
        match &atom.head {
            RuleBodyCall::Table { id, read } => {
                builder.query_table(*id, &entries, read.is_subsumed())?;
                body_atom_to_table_premise[body_atom] = Some(next_table_premise);
                next_table_premise += 1;
            }
            RuleBodyCall::IndexTable { id, any_of, read } => {
                if capture.is_some() {
                    bail!("causal capture does not yet support occurrence-index rule bodies");
                }
                // An index is declared as the relation `(value, row…) -> Unit`, so
                // its atom carries the occurring value, the indexed function's row,
                // and the relation's own unit output. Only the row belongs to the
                // underlying function.
                let (indexed, rest) = entries
                    .split_first()
                    .expect("an index atom binds a value and a row");
                let (_unit, row) = rest
                    .split_last()
                    .expect("an index atom carries the relation's unit output");
                builder.query_table_by_occurrence(
                    *id,
                    row,
                    indexed.clone(),
                    any_of,
                    read.is_subsumed(),
                )?;
            }
            RuleBodyCall::Primitive {
                id, output, replay, ..
            } => {
                builder.query_prim_with_replay(
                    *id,
                    &entries,
                    *output,
                    replay.as_deref().cloned(),
                )?;
            }
        }
    }
    builder.finish_query();

    for action in &core.head.0 {
        match action {
            GenericCoreAction::Let(span, variable, call, arguments) => {
                let entries = rule_entries(&mut builder, &mut variables, arguments)?;
                let result: QueryEntry = match call {
                    RuleActionCall::Table { id, name } => {
                        let span = span.clone();
                        let name = name.clone();
                        builder
                            .lookup(*id, &entries, move || {
                                format!("{span}: lookup of function {name} failed")
                            })
                            .into()
                    }
                    RuleActionCall::Primitive {
                        id,
                        name,
                        output,
                        replay,
                    } => {
                        let span = span.clone();
                        let name = name.clone();
                        builder
                            .call_external_func_with_replay(
                                *id,
                                &entries,
                                *output,
                                replay.as_deref().cloned(),
                                move || format!("{span}: call of primitive {name} failed"),
                            )
                            .into()
                    }
                };
                variables.insert(variable.id, result);
            }
            GenericCoreAction::LetAtomTerm(_, variable, term) => {
                let entry = rule_entry(&mut builder, &mut variables, term)?;
                variables.insert(variable.id, entry);
            }
            GenericCoreAction::Set(_, call, arguments, values) => {
                let RuleActionCall::Table { id, .. } = call else {
                    bail!("cannot set a primitive")
                };
                let mut entries = rule_entries(&mut builder, &mut variables, arguments)?;
                entries.extend(rule_entries(&mut builder, &mut variables, values)?);
                builder.set(*id, &entries);
            }
            GenericCoreAction::Change(_, change, call, arguments) => {
                let RuleActionCall::Table { id, .. } = call else {
                    bail!("cannot delete or subsume a primitive")
                };
                let entries = rule_entries(&mut builder, &mut variables, arguments)?;
                match change {
                    egglog_ast::generic_ast::Change::Delete => builder.remove(*id, &entries),
                    egglog_ast::generic_ast::Change::Subsume => builder.subsume(*id, &entries),
                }
            }
            GenericCoreAction::Union(_, lhs, rhs) => {
                let lhs = rule_entry(&mut builder, &mut variables, lhs)?;
                let rhs = rule_entry(&mut builder, &mut variables, rhs)?;
                if let Some(sorts) = union_sorts.as_mut() {
                    let sort = sorts.next().ok_or_else(|| {
                        anyhow::anyhow!("capture metadata has fewer union sorts than union actions")
                    })?;
                    builder.union_with_replay(lhs, rhs, sort);
                } else {
                    builder.union(lhs, rhs);
                }
            }
            GenericCoreAction::Panic(_, message) => builder.panic(message.clone()),
        }
    }
    if union_sorts.is_some_and(|mut sorts| sorts.next().is_some()) {
        bail!("capture metadata has more union sorts than union actions");
    }

    match capture {
        Some(RuleCaptureSpec::Firing(capture)) => {
            let bindings = capture
                .bindings
                .iter()
                .map(|binding| match binding {
                    FiringCaptureBinding::Variable {
                        variable,
                        current_sort,
                    } => {
                        let entry = variables.get(&variable.id).cloned().ok_or_else(|| {
                            anyhow::anyhow!(
                                "firing capture binding `{}` was not lowered into the native rule",
                                variable.name
                            )
                        })?;
                        Ok(BridgeFiringCaptureBinding::Entry {
                            entry,
                            current_sort: *current_sort,
                        })
                    }
                    FiringCaptureBinding::Constant { term, sort } => {
                        Ok(BridgeFiringCaptureBinding::Constant {
                            term: *term,
                            sort: *sort,
                        })
                    }
                })
                .collect::<Result<Vec<_>>>()?;
            builder.set_firing_capture(BridgeFiringCaptureSpec {
                rule: capture.rule,
                bindings: bindings.into_boxed_slice(),
            });
        }
        Some(RuleCaptureSpec::Criterion(capture)) => {
            let premise =
                |source: CriterionCapturePremise| -> Result<BridgeCriterionCapturePremise> {
                    let logical_columns = core
                        .body
                        .atoms
                        .get(source.body_atom)
                        .map(|atom| atom.args.len())
                        .ok_or_else(|| {
                            anyhow::anyhow!(
                                "criterion capture endpoint cites missing body atom {}",
                                source.body_atom
                            )
                        })?;
                    let premise = body_atom_to_table_premise
                        .get(source.body_atom)
                        .copied()
                        .flatten()
                        .ok_or_else(|| {
                            anyhow::anyhow!(
                                "criterion capture endpoint body atom {} is not a table premise",
                                source.body_atom
                            )
                        })?;
                    if source.column >= logical_columns {
                        bail!(
                            "criterion capture endpoint body atom {} has no logical column {}",
                            source.body_atom,
                            source.column
                        );
                    }
                    Ok(BridgeCriterionCapturePremise {
                        premise,
                        column: source.column,
                        constructor: source.constructor,
                    })
                };
            let equalities = capture
                .equalities
                .iter()
                .map(|(left, right)| Ok((premise(*left)?, premise(*right)?)))
                .collect::<Result<Vec<_>>>()?;
            builder.set_criterion_capture(BridgeCriterionCaptureSpec {
                check: capture.check,
                equalities: equalities.into_boxed_slice(),
            });
        }
        Some(RuleCaptureSpec::Source(_)) | None => {}
    }

    Ok(builder.build())
}

// ---------------------------------------------------------------------------
// Backend for the bridge EGraph
// ---------------------------------------------------------------------------

impl Backend for EGraph {
    fn add_table(&mut self, config: FunctionConfig) -> FunctionId {
        EGraph::add_table(self, config)
    }

    fn try_add_table(&mut self, config: FunctionConfig) -> Result<FunctionId> {
        EGraph::try_add_table(self, config)
    }

    fn enable_trace(&mut self) -> Result<()> {
        EGraph::enable_trace(self)
    }

    fn register_function_replay(
        &mut self,
        func: FunctionId,
        spec: FunctionReplaySpec,
    ) -> Result<()> {
        EGraph::register_function_replay(self, func, spec)
    }

    fn register_container_replay_sort(
        &mut self,
        sort: ReplaySortId,
        container_type: TypeId,
        child_sorts: &[ReplaySortId],
    ) -> Result<()> {
        EGraph::register_container_replay_sort(self, sort, container_type, child_sorts)
    }

    fn intern_replay_literal(
        &self,
        sort: ReplaySortId,
        literal: ReplayLiteral,
        value: Value,
    ) -> Result<ReplayTermId> {
        EGraph::intern_replay_literal(self, sort, literal, value)
    }

    fn finalize_trace_wave(&mut self) -> std::result::Result<(), TraceLifecycleError> {
        EGraph::finalize_trace_wave(self)
    }

    fn set_trace_wave(&mut self, wave: u64) -> std::result::Result<(), TraceLifecycleError> {
        EGraph::set_trace_wave(self, wave)
    }

    fn peek_next_function_id(&self) -> FunctionId {
        EGraph::peek_next_function_id(self)
    }

    fn table_size(&self, table: FunctionId) -> usize {
        EGraph::table_size(self, table)
    }

    fn clear_table(&mut self, func: FunctionId) {
        EGraph::clear_table(self, func);
    }

    fn for_each_while_dyn(
        &self,
        table: FunctionId,
        f: &mut dyn for<'r> FnMut(ScanEntry<'r>) -> bool,
    ) {
        EGraph::for_each_while(self, table, f);
    }

    fn get_canon_repr(&self, val: Value, ty: ColumnTy) -> Value {
        EGraph::get_canon_repr(self, val, ty)
    }

    fn base_values(&self) -> &BaseValues {
        EGraph::base_values(self)
    }

    fn base_values_mut(&mut self) -> &mut BaseValues {
        EGraph::base_values_mut(self)
    }

    fn container_values(&self) -> &ContainerValues {
        EGraph::container_values(self)
    }

    fn lookup_row(&self, func: FunctionId, key: &[Value]) -> Option<Vec<Value>> {
        EGraph::lookup_row(self, func, key)
    }

    fn lookup_id(&self, func: FunctionId, key: &[Value]) -> Option<Value> {
        EGraph::lookup_id(self, func, key)
    }

    fn with_execution_state_tracked_dyn(&self, f: &mut dyn FnMut(&mut ExecutionState<'_>)) -> bool {
        EGraph::with_execution_state_tracked(self, |es| f(es)).1
    }

    fn add_rule(&mut self, rule: RuleSpec) -> Result<RuleId> {
        build_rule(self, rule)
    }

    fn fresh_id(&mut self) -> Value {
        EGraph::fresh_id(self)
    }

    fn add_values(&mut self, values: Vec<(FunctionId, Vec<Value>)>) {
        EGraph::add_values(self, values);
    }

    fn free_rule(&mut self, id: RuleId) {
        EGraph::free_rule(self, id);
    }

    fn run_rules(&mut self, run: RuleSetRun<'_>) -> Result<IterationReport> {
        EGraph::run_rules(self, run.rules)
    }

    fn flush_updates(&mut self) -> Result<bool> {
        EGraph::try_flush_updates(self)
    }

    fn register_external_func(
        &mut self,
        func: Box<dyn ExternalFunction + 'static>,
    ) -> ExternalFunctionId {
        EGraph::register_external_func(self, func)
    }

    fn free_external_func(&mut self, func: ExternalFunctionId) {
        EGraph::free_external_func(self, func);
    }

    fn new_panic(&mut self, message: String) -> ExternalFunctionId {
        EGraph::new_panic(self, message)
    }

    fn register_set_if_empty(
        &mut self,
        view_name: String,
        n_keys: usize,
        out_arity: usize,
    ) -> ExternalFunctionId {
        EGraph::register_set_if_empty(self, view_name, n_keys, out_arity)
    }

    fn register_view_column_read(
        &mut self,
        view_name: String,
        n_keys: usize,
        col_idx: usize,
    ) -> ExternalFunctionId {
        EGraph::register_view_column_read(self, view_name, n_keys, col_idx)
    }

    fn set_report_level(&mut self, level: ReportLevel) {
        EGraph::set_report_level(self, level);
    }

    fn dump_debug_info(&self) {
        EGraph::dump_debug_info(self);
    }

    fn clone_boxed(&self) -> Box<dyn Backend> {
        Box::new(self.clone())
    }

    fn action_registry(&self) -> Option<&Arc<RwLock<ActionRegistry>>> {
        Some(EGraph::action_registry(self))
    }

    fn id_counter(&self) -> Option<crate::CounterId> {
        Some(EGraph::id_counter(self))
    }

    fn supports_containers(&self) -> bool {
        true
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}
