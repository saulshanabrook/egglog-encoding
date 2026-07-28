#![forbid(unsafe_code)]
//! Checkpoint 0/0.5 of a DuckDB-authoritative egglog backend.
//!
//! Function rows live only in typed DuckDB tables. This storage scaffold
//! deliberately stops before general [`RuleSpec`] lowering: focused executable
//! probes establish the safe SQL, transaction, input, and query-kernel boundary
//! before the rule compiler is committed to an IR shape. Those probes are SQL
//! feasibility checks, not a checkpoint-pass claim or a differential test of
//! production `RuleSpec` lowering against the main backend.

use std::any::Any;
use std::sync::{Arc, Mutex};

use anyhow::{Result, anyhow, bail};
use egglog_backend_trait::{
    Backend, BaseValues, ColumnTy, ContainerValues, CounterId, ExecutionState, ExternalFunction,
    ExternalFunctionId, FunctionConfig, FunctionId, IterationReport, MergeFn, ReportLevel, RuleId,
    RuleSetRun, RuleSpec, ScanEntry, Value,
};
use egglog_core_relations::Database;
use egglog_numeric_id::NumericId;

mod storage;

use storage::{InputMerge, InsertStats, Storage, for_each_scan_entry};

/// A DuckDB-authoritative backend skeleton on the current backend SPI.
///
/// `Database` is used only for base/container value registries, external
/// functions, and counters. It never receives a function table, match plan, or
/// merge action; all durable function rows are owned by `storage`'s DuckDB
/// connection.
pub struct EGraph {
    storage: Storage,
    registries: Database,
    id_counter: CounterId,
    deferred_panic: Arc<Mutex<Option<String>>>,
    last_insert: InsertStats,
    report_level: ReportLevel,
}

impl EGraph {
    pub fn new() -> Result<Self> {
        let storage = Storage::new()?;
        let mut registries = Database::new();
        let id_counter = registries.add_counter();
        Ok(Self {
            storage,
            registries,
            id_counter,
            deferred_panic: Arc::new(Mutex::new(None)),
            last_insert: InsertStats::default(),
            report_level: ReportLevel::default(),
        })
    }

    /// Version reported by the loaded engine, used to distinguish a crate pin
    /// from the actual runtime provenance.
    pub fn runtime_version(&self) -> Result<String> {
        self.storage.runtime_version()
    }

    /// Number of typed vertical DML targets in the latest `add_values` call.
    /// This is checkpoint evidence for the current multi-function input seam.
    pub fn last_input_target_statements(&self) -> usize {
        self.last_insert.target_statements
    }

    /// Number of logical rows in the latest `add_values` call.
    pub fn last_input_rows(&self) -> usize {
        self.last_insert.rows
    }

    /// Number of rows actually inserted by the latest `add_values` call after
    /// DuckDB applied the supported KeepOld conflict policy.
    pub fn last_input_inserted_rows(&self) -> usize {
        self.last_insert.inserted_rows
    }

    fn pending_panic_message(&self) -> Option<String> {
        self.deferred_panic
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .clone()
    }

    fn take_deferred_panic(&self) -> Result<()> {
        let message = self
            .deferred_panic
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .take();
        if let Some(message) = message {
            bail!(message);
        }
        Ok(())
    }
}

impl Default for EGraph {
    fn default() -> Self {
        Self::new().expect("failed to create in-memory DuckDB backend")
    }
}

#[derive(Clone)]
struct DeferredPanic {
    message: String,
    channel: Arc<Mutex<Option<String>>>,
}

impl ExternalFunction for DeferredPanic {
    fn invoke(&self, state: &mut ExecutionState<'_>, _args: &[Value]) -> Option<Value> {
        state.trigger_early_stop();
        let mut channel = self
            .channel
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if channel.is_none() {
            *channel = Some(self.message.clone());
        }
        None
    }
}

fn input_merge_policy(name: &str, n_vals: usize, merge: &MergeFn) -> Result<InputMerge> {
    match merge {
        // `add_values` is correct for this narrow policy: DuckDB retains the
        // first row for a key and ignores later conflicts. Rule execution and
        // every other merge form remain an explicit checkpoint boundary.
        MergeFn::Old if n_vals == 1 => Ok(InputMerge::KeepOld),
        MergeFn::Old => bail!(
            "DuckDB checkpoint 0.5 supports MergeFn::Old only for one output column; table `{name}` declares {n_vals}"
        ),
        _ => bail!(
            "DuckDB checkpoint 0.5 cannot register table `{name}`: only the one-column MergeFn::Old input policy is implemented"
        ),
    }
}

impl Backend for EGraph {
    fn add_table(&mut self, config: FunctionConfig) -> FunctionId {
        let FunctionConfig {
            schema,
            n_vals,
            n_identity_vals,
            default,
            merge,
            name,
            can_subsume,
        } = config;
        if let Some(identity_vals) = n_identity_vals
            && !(1..=n_vals).contains(&identity_vals)
        {
            panic!(
                "DuckDB add_table({name}) failed: identity-column count {identity_vals} is outside 1..={n_vals}"
            );
        }
        let input_merge = input_merge_policy(&name, n_vals, &merge)
            .unwrap_or_else(|error| panic!("DuckDB add_table({name}) failed: {error:#}"));
        // An identity guard cannot change KeepOld: a collision keeps the old
        // row whether or not the guarded value matches. Retain the field here
        // to make that deliberate rather than silently losing SPI metadata.
        let _identity_guard = n_identity_vals;
        // Defaults affect action-stream lookup-or-insert, which is unreachable
        // while production RuleSpec lowering fails closed. Direct lookup stays
        // pure by Backend contract, so no default is applied in this slice.
        let _deferred_default = default;
        self.storage
            .register_table(
                self.registries.base_values(),
                name.clone(),
                &schema,
                n_vals,
                can_subsume,
                input_merge,
            )
            .unwrap_or_else(|error| panic!("DuckDB add_table({name}) failed: {error:#}"))
    }

    fn peek_next_function_id(&self) -> FunctionId {
        self.storage.next_table_id()
    }

    fn table_size(&self, table: FunctionId) -> usize {
        self.storage
            .table_size(table)
            .unwrap_or_else(|error| panic!("DuckDB table_size failed: {error:#}"))
    }

    fn clear_table(&mut self, func: FunctionId) {
        self.storage
            .clear(func)
            .unwrap_or_else(|error| panic!("DuckDB clear_table failed: {error:#}"));
    }

    fn for_each_while_dyn(
        &self,
        table: FunctionId,
        f: &mut dyn for<'r> FnMut(ScanEntry<'r>) -> bool,
    ) {
        let rows = self
            .storage
            .scan(self.registries.base_values(), table)
            .unwrap_or_else(|error| panic!("DuckDB table scan failed: {error:#}"));
        for_each_scan_entry(&rows, f);
    }

    fn get_canon_repr(&self, val: Value, _ty: ColumnTy) -> Value {
        // The required term encoding represents canonicalization through
        // ordinary function tables. There is no hidden host union-find.
        val
    }

    fn base_values(&self) -> &BaseValues {
        self.registries.base_values()
    }

    fn base_values_mut(&mut self) -> &mut BaseValues {
        self.registries.base_values_mut()
    }

    fn container_values(&self) -> &ContainerValues {
        self.registries.container_values()
    }

    fn lookup_row(&self, func: FunctionId, key: &[Value]) -> Option<Vec<Value>> {
        self.storage
            .lookup(self.registries.base_values(), func, key)
            .unwrap_or_else(|error| panic!("DuckDB lookup failed: {error:#}"))
            .map(|row| row.values)
    }

    fn lookup_id(&self, func: FunctionId, key: &[Value]) -> Option<Value> {
        self.lookup_row(func, key)
            .and_then(|row| row.get(key.len()).copied())
    }

    fn id_counter(&self) -> Option<CounterId> {
        Some(self.id_counter)
    }

    fn fresh_id(&mut self) -> Value {
        Value::from_usize(self.registries.inc_counter(self.id_counter))
    }

    fn add_values(&mut self, values: Vec<(FunctionId, Vec<Value>)>) -> Result<()> {
        match self
            .storage
            .insert_batch(self.registries.base_values(), values)
        {
            Ok(stats) => {
                self.last_insert = stats;
                Ok(())
            }
            Err(error) => {
                self.last_insert = InsertStats::default();
                Err(error)
            }
        }
    }

    fn with_execution_state_tracked_dyn(&self, f: &mut dyn FnMut(&mut ExecutionState<'_>)) -> bool {
        self.registries
            .with_execution_state_tracked(|state| f(state))
            .1
    }

    fn add_rule(&mut self, rule: RuleSpec) -> Result<RuleId> {
        Err(anyhow!(
            "DuckDB checkpoint 0.5 does not yet lower production rule `{}`; selective and broad source shapes currently have safe-API SQL feasibility probes only",
            rule.name
        ))
    }

    fn free_rule(&mut self, _id: RuleId) {}

    fn run_rules(&mut self, run: RuleSetRun<'_>) -> Result<IterationReport> {
        self.take_deferred_panic()?;
        if run.rules.is_empty() {
            Ok(IterationReport::default())
        } else {
            Err(anyhow!(
                "DuckDB checkpoint 0.5 cannot execute a production RuleSpec yet"
            ))
        }
    }

    fn flush_updates(&mut self) -> bool {
        // `add_values` and direct table operations commit synchronously.
        false
    }

    fn register_external_func(
        &mut self,
        func: Box<dyn ExternalFunction + 'static>,
    ) -> ExternalFunctionId {
        self.registries.add_external_function(func)
    }

    fn free_external_func(&mut self, func: ExternalFunctionId) {
        self.registries.free_external_function(func);
    }

    fn new_panic(&mut self, message: String) -> ExternalFunctionId {
        self.register_external_func(Box::new(DeferredPanic {
            message,
            channel: Arc::clone(&self.deferred_panic),
        }))
    }

    fn set_report_level(&mut self, level: ReportLevel) {
        self.report_level = level;
    }

    fn dump_debug_info(&self) {
        eprintln!(
            "DuckDB backend checkpoint 0.5: runtime={:?}, next_table={}, deferred_panic={:?}",
            self.runtime_version(),
            self.peek_next_function_id().rep(),
            self.pending_panic_message()
        );
    }

    fn clone_boxed(&self) -> Box<dyn Backend> {
        panic!("DuckDB checkpoint 0.5 does not yet implement transactional push/pop snapshots")
    }

    fn requires_term_encoding(&self) -> bool {
        true
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

const _: () = {
    const fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<EGraph>();
};

#[cfg(test)]
mod tests {
    use super::*;
    use egglog_core_relations::Boxed;
    use ordered_float::OrderedFloat;

    #[test]
    fn keep_old_input_is_sql_native_and_other_merges_fail_closed() -> Result<()> {
        let mut backend = EGraph::new()?;
        backend.base_values_mut().register_type::<()>();
        backend.base_values_mut().register_type::<bool>();
        backend.base_values_mut().register_type::<i64>();
        backend
            .base_values_mut()
            .register_type::<Boxed<OrderedFloat<f64>>>();
        backend.base_values_mut().register_type::<Boxed<String>>();
        let i64_ty = backend.base_values().get_ty::<i64>();
        let table = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Base(i64_ty)],
            n_vals: 1,
            n_identity_vals: None,
            default: egglog_backend_trait::DefaultVal::Fail,
            merge: MergeFn::Old,
            name: "keep-old".to_string(),
            can_subsume: false,
        });
        let ten = backend.base_values().get(10_i64);
        let twenty = backend.base_values().get(20_i64);
        backend.add_values(vec![
            (table, vec![Value::new(7), ten]),
            (table, vec![Value::new(7), twenty]),
        ])?;
        assert!(!backend.flush_updates(), "add_values already committed");
        assert_eq!(backend.last_input_rows(), 2);
        assert_eq!(backend.last_input_inserted_rows(), 1);
        assert_eq!(backend.last_input_target_statements(), 1);
        assert_eq!(
            backend.lookup_row(table, &[Value::new(7)]),
            Some(vec![Value::new(7), ten])
        );

        assert!(
            input_merge_policy("unsupported", 1, &MergeFn::AssertEq)
                .unwrap_err()
                .to_string()
                .contains("only the one-column MergeFn::Old")
        );
        Ok(())
    }

    #[test]
    fn input_error_is_immediate_atomic_and_backend_remains_usable() -> Result<()> {
        let mut backend = EGraph::new()?;
        backend.base_values_mut().register_type::<()>();
        backend.base_values_mut().register_type::<bool>();
        backend.base_values_mut().register_type::<i64>();
        backend
            .base_values_mut()
            .register_type::<Boxed<OrderedFloat<f64>>>();
        backend.base_values_mut().register_type::<Boxed<String>>();
        let first = backend.add_table(FunctionConfig {
            schema: vec![
                ColumnTy::Id,
                ColumnTy::Base(backend.base_values().get_ty::<i64>()),
            ],
            n_vals: 1,
            n_identity_vals: None,
            default: egglog_backend_trait::DefaultVal::Fail,
            merge: MergeFn::Old,
            name: "first-target".to_string(),
            can_subsume: false,
        });
        let second = backend.add_table(FunctionConfig {
            schema: vec![
                ColumnTy::Id,
                ColumnTy::Base(backend.base_values().get_ty::<i64>()),
            ],
            n_vals: 1,
            n_identity_vals: None,
            default: egglog_backend_trait::DefaultVal::Fail,
            merge: MergeFn::Old,
            name: "second-target".to_string(),
            can_subsume: false,
        });
        let ten = backend.base_values().get(10_i64);

        let error = backend
            .add_values(vec![
                (first, vec![Value::new(1), ten]),
                (second, vec![Value::new(2)]),
            ])
            .unwrap_err();
        assert!(error.to_string().contains("expects 2 columns, got 1"));
        assert_eq!(backend.last_input_rows(), 0);
        assert_eq!(backend.table_size(first), 0);
        assert_eq!(backend.table_size(second), 0);

        backend.add_values(vec![
            (first, vec![Value::new(1), ten]),
            (second, vec![Value::new(2), ten]),
        ])?;
        assert_eq!(backend.table_size(first), 1);
        assert_eq!(backend.table_size(second), 1);
        assert!(!backend.flush_updates());
        Ok(())
    }

    #[test]
    fn diagnostics_do_not_consume_deferred_rule_panic() -> Result<()> {
        let mut backend = EGraph::new()?;
        let panic = backend.new_panic("deferred rule failure".to_string());
        let mut invoke = |state: &mut ExecutionState<'_>| {
            assert_eq!(state.call_external_func(panic, &[]), None);
        };
        backend.with_execution_state_tracked_dyn(&mut invoke);

        assert_eq!(backend.runtime_version()?, "v1.5.4");
        backend.dump_debug_info();
        assert_eq!(backend.peek_next_function_id().rep(), 0);
        assert_eq!(
            backend.pending_panic_message().as_deref(),
            Some("deferred rule failure")
        );

        let error = backend
            .run_rules(RuleSetRun {
                name: Some("deliver-deferred-panic"),
                rules: &[],
            })
            .unwrap_err();
        assert_eq!(error.to_string(), "deferred rule failure");
        assert!(backend.pending_panic_message().is_none());
        backend.run_rules(RuleSetRun {
            name: Some("after-deferred-panic"),
            rules: &[],
        })?;
        Ok(())
    }

    #[test]
    fn backend_starts_without_host_function_tables() -> Result<()> {
        let backend = EGraph::new()?;
        assert_eq!(backend.peek_next_function_id().rep(), 0);
        assert_eq!(backend.runtime_version()?, "v1.5.4");
        Ok(())
    }

    #[test]
    fn production_rule_boundary_fails_closed() -> Result<()> {
        let mut backend = EGraph::new()?;
        // The rule compiler owns construction of RuleSpec. Exercise both the
        // empty scheduling no-op and the explicit nonempty rejection without
        // fabricating a stale donor RuleSpec here.
        assert!(
            !backend
                .run_rules(RuleSetRun {
                    name: None,
                    rules: &[]
                })?
                .rule_set_report
                .changed
        );
        let error = backend
            .run_rules(RuleSetRun {
                name: Some("not-yet-lowered"),
                rules: &[RuleId::new(0)],
            })
            .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("cannot execute a production RuleSpec")
        );
        Ok(())
    }
}
