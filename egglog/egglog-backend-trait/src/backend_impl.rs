//! `impl Backend for egglog_bridge::EGraph` — the in-memory reference backend.
//!
//! Every method is a thin passthrough to an inherent method on the bridge
//! `EGraph`. Lives in this crate (not in `egglog-bridge`) so the bridge stays
//! free of any dependency on the trait; the orphan rule permits it because the
//! [`Backend`] trait is local here.

use std::any::Any;
use std::sync::{Arc, RwLock};

use anyhow::Result;
use egglog_bridge::{ActionRegistry, EGraph, RuleBuilder};

use crate::{
    Backend, BaseValues, ColumnTy, ContainerValues, ExecutionState, ExternalFunction,
    ExternalFunctionId, FunctionConfig, FunctionId, IterationReport, PanicMsg, QueryEntry,
    ReportLevel, RuleBuilderOps, RuleId, ScanEntry, Value,
};

// ---------------------------------------------------------------------------
// RuleBuilderOps for the bridge's RuleBuilder
// ---------------------------------------------------------------------------

/// Trait-object wrapper around the bridge's [`RuleBuilder`]; every op delegates.
struct BridgeRuleBuilderOps<'a> {
    inner: RuleBuilder<'a>,
}

impl RuleBuilderOps for BridgeRuleBuilderOps<'_> {
    fn new_var(&mut self, ty: ColumnTy) -> QueryEntry {
        QueryEntry::Var(self.inner.new_var(ty))
    }

    fn new_var_named(&mut self, ty: ColumnTy, name: &str) -> QueryEntry {
        self.inner.new_var_named(ty, name)
    }

    fn base_values(&self) -> &BaseValues {
        self.inner.egraph().base_values()
    }

    fn query_table(
        &mut self,
        func: FunctionId,
        entries: &[QueryEntry],
        is_subsumed: Option<bool>,
    ) -> Result<()> {
        self.inner
            .query_table(func, entries, is_subsumed)
            .map(|_| ())
    }

    fn query_prim(
        &mut self,
        func: ExternalFunctionId,
        entries: &[QueryEntry],
        ret_ty: ColumnTy,
    ) -> Result<()> {
        self.inner.query_prim(func, entries, ret_ty)
    }

    fn call_external_func(
        &mut self,
        func: ExternalFunctionId,
        args: &[QueryEntry],
        ret_ty: ColumnTy,
        panic_msg: PanicMsg,
    ) -> QueryEntry {
        let var = self.inner.call_external_func(func, args, ret_ty, panic_msg);
        QueryEntry::Var(var)
    }

    fn lookup(
        &mut self,
        func: FunctionId,
        entries: &[QueryEntry],
        panic_msg: PanicMsg,
    ) -> QueryEntry {
        let var = self.inner.lookup(func, entries, panic_msg);
        QueryEntry::Var(var)
    }

    fn subsume(&mut self, func: FunctionId, entries: &[QueryEntry]) -> Result<()> {
        self.inner.subsume(func, entries);
        Ok(())
    }

    fn set(&mut self, func: FunctionId, entries: &[QueryEntry]) {
        self.inner.set(func, entries);
    }

    fn remove(&mut self, func: FunctionId, entries: &[QueryEntry]) {
        self.inner.remove(func, entries);
    }

    fn union(&mut self, l: QueryEntry, r: QueryEntry) {
        self.inner.union(l, r);
    }

    fn panic(&mut self, message: String) {
        self.inner.panic(message);
    }

    fn new_panic(&mut self, message: String) -> ExternalFunctionId {
        self.inner.new_panic(message)
    }

    fn set_no_decomp(&mut self, no_decomp: bool) {
        self.inner.set_no_decomp(no_decomp);
    }

    fn build(self: Box<Self>) -> Result<RuleId> {
        Ok(self.inner.build())
    }

    fn abort(self: Box<Self>) {
        self.inner.abort();
    }

    fn backend_any(&self) -> Option<&dyn Any> {
        Some(self.inner.egraph())
    }
}

// ---------------------------------------------------------------------------
// Backend for the bridge EGraph
// ---------------------------------------------------------------------------

impl Backend for EGraph {
    fn add_table(&mut self, config: FunctionConfig) -> FunctionId {
        EGraph::add_table(self, config)
    }

    fn table_size(&self, table: FunctionId) -> usize {
        EGraph::table_size(self, table)
    }

    fn clear_table(&mut self, func: FunctionId) {
        EGraph::clear_table(self, func);
    }

    fn for_each_dyn(&self, table: FunctionId, f: &mut dyn for<'r> FnMut(ScanEntry<'r>)) {
        EGraph::for_each(self, table, f);
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

    fn lookup_id(&self, func: FunctionId, key: &[Value]) -> Option<Value> {
        EGraph::lookup_id(self, func, key)
    }

    fn with_execution_state_dyn(&self, f: &mut dyn FnMut(&mut ExecutionState<'_>)) {
        EGraph::with_execution_state(self, |es| f(es));
    }

    fn with_execution_state_tracked_dyn(&self, f: &mut dyn FnMut(&mut ExecutionState<'_>)) -> bool {
        EGraph::with_execution_state_tracked(self, |es| f(es)).1
    }

    fn new_rule<'a>(&'a mut self, desc: &str, seminaive: bool) -> Box<dyn RuleBuilderOps + 'a> {
        let inner = EGraph::new_rule(self, desc, seminaive);
        Box::new(BridgeRuleBuilderOps { inner })
    }

    fn free_rule(&mut self, id: RuleId) {
        EGraph::free_rule(self, id);
    }

    fn run_rules(&mut self, rules: &[RuleId]) -> Result<IterationReport> {
        EGraph::run_rules(self, rules)
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

    fn dump_debug_info(&self) {
        EGraph::dump_debug_info(self);
    }

    fn clone_boxed(&self) -> Box<dyn Backend> {
        Box::new(self.clone())
    }

    fn action_registry(&self) -> &Arc<RwLock<ActionRegistry>> {
        EGraph::action_registry(self)
    }

    fn supports_containers(&self) -> bool {
        true
    }

    fn supports_action_registry(&self) -> bool {
        true
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}
