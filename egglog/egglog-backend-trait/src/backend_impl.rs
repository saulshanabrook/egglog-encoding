//! `impl Backend for egglog_bridge::EGraph` — the in-memory reference backend.
//!
//! Every method is a thin passthrough to an inherent method on the bridge
//! `EGraph`. Lives in this crate (not in `egglog-bridge`) so the bridge stays
//! free of any dependency on the trait; the orphan rule permits it because the
//! [`Backend`] trait is local here.

use std::any::Any;
use std::collections::BTreeMap;
use std::sync::{Arc, RwLock};

use anyhow::{Result, bail};
use egglog_bridge::{ActionRegistry, EGraph, QueryEntry, RuleBuilder};

use egglog_ast::core::{GenericAtomTerm, GenericCoreAction};

use crate::{
    Backend, BaseValues, ColumnTy, ContainerValues, ExecutionState, ExternalFunction,
    ExternalFunctionId, FunctionConfig, FunctionId, IterationReport, ReportLevel, RuleActionCall,
    RuleBodyCall, RuleId, RuleSetRun, RuleSpec, RuleValue, RuleVar, ScanEntry, Value,
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
    } = rule;
    let mut builder = egraph.new_rule(&name, seminaive);
    builder.set_no_decomp(no_decomp);
    let mut variables = BTreeMap::new();

    for atom in &core.body.atoms {
        let entries = rule_entries(&mut builder, &mut variables, &atom.args)?;
        match &atom.head {
            RuleBodyCall::Table { id, read } => {
                builder.query_table(*id, &entries, read.is_subsumed())?;
            }
            RuleBodyCall::Primitive { id, output, .. } => {
                builder.query_prim(*id, &entries, *output)?;
            }
        }
    }

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
                        id, name, output, ..
                    } => {
                        let span = span.clone();
                        let name = name.clone();
                        builder
                            .call_external_func(*id, &entries, *output, move || {
                                format!("{span}: call of primitive {name} failed")
                            })
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
                builder.union(lhs, rhs);
            }
            GenericCoreAction::Panic(_, message) => builder.panic(message.clone()),
        }
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

    fn free_rule(&mut self, id: RuleId) {
        EGraph::free_rule(self, id);
    }

    fn run_rules(&mut self, run: RuleSetRun<'_>) -> Result<IterationReport> {
        EGraph::run_rules(self, run.rules)
    }

    fn flush_updates(&mut self) -> bool {
        EGraph::flush_updates(self)
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

    fn set_report_level(&mut self, level: ReportLevel) {
        EGraph::set_report_level(self, level);
    }

    fn set_phase_timing(&mut self, enabled: bool) {
        EGraph::set_phase_timing(self, enabled);
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
