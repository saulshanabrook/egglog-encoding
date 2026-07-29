#![forbid(unsafe_code)]
//! A typed, DuckDB-authoritative egglog backend under incremental lowering.
//!
//! Function rows live only in typed DuckDB tables. The backend implements a
//! deliberately closed production [`RuleSpec`] subset:
//! Live table atoms with typed variables/literals and either one table Set, a
//! nonempty Delete-only head, or one complete-row body-bound Subsume, plus the
//! structural two-atom union-find path rule and its typed identity-guarded
//! merge Block, and the two standard scalar All-mode rebuild forms over exact
//! ordered-union Blocks. Matches, phased cleanup effects, constructor rows,
//! fresh allocation, and recursive merge candidates execute through staged
//! DuckDB SQL. Unsupported writes fail closed even though their complete
//! configurations remain registered for later lowering.

use std::any::Any;
use std::sync::{Arc, Mutex};

use anyhow::{Result, anyhow, bail};
use egglog_backend_trait::{
    Backend, BaseValues, ColumnTy, ContainerValues, ExecutionState, ExternalFunction,
    ExternalFunctionId, FunctionConfig, FunctionId, IterationReport, NativeInputValue, ReportLevel,
    RuleId, RuleSetRun, RuleSpec, ScanEntry, Value,
};
use egglog_core_relations::Database;
use egglog_numeric_id::NumericId;

#[cfg(test)]
mod cleanup_effect_tests;
mod path_compress;
#[cfg(test)]
mod path_compress_tests;
mod rebuild;
#[cfg(test)]
mod rebuild_tests;
mod rule_sql;
#[cfg(test)]
mod rule_sql_tests;
mod storage;

use rule_sql::{CompiledRule, RuleExecutionStats, compile_rule};
use storage::{InsertStats, Storage, for_each_scan_entry};

struct RegisteredRule {
    plan: CompiledRule,
    watermark: u64,
}

/// A DuckDB-authoritative backend skeleton on the current backend SPI.
///
/// `Database` is used only for base/container value registries, external
/// functions, and counters. It never receives a function table, match plan, or
/// merge action; all durable function rows are owned by `storage`'s DuckDB
/// connection.
pub struct EGraph {
    storage: Storage,
    registries: Database,
    deferred_panic: Arc<Mutex<Option<String>>>,
    rules: Vec<Option<RegisteredRule>>,
    last_insert: InsertStats,
    last_rule: RuleExecutionStats,
    report_level: ReportLevel,
}

impl EGraph {
    pub fn new() -> Result<Self> {
        let storage = Storage::new()?;
        let registries = Database::new();
        Ok(Self {
            storage,
            registries,
            deferred_panic: Arc::new(Mutex::new(None)),
            rules: Vec::new(),
            last_insert: InsertStats::default(),
            last_rule: RuleExecutionStats::default(),
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

    /// Number of DuckDB statements issued for the most recent bounded rule
    /// execution, including scalar count/counter statements and stage cleanup.
    pub fn last_rule_statement_count(&self) -> usize {
        self.last_rule.statement_count
    }

    /// Match cardinalities for scheduled rules in the most recent bounded run.
    pub fn last_rule_match_counts(&self) -> &[usize] {
        &self.last_rule.matched_rows
    }

    /// Set rows installed per scheduled rule in the most recent bounded run.
    /// Delete and Subsume rules report zero rather than laundering physical
    /// cleanup transitions into insert telemetry. Path-compression rules report
    /// only head Trans inserts, not recursive UF, Sym, or Trans effects.
    /// Standard rebuild rules likewise report only their independent head
    /// constructor inserts, never recursive ordered-union effects.
    pub fn last_rule_insert_counts(&self) -> &[usize] {
        &self.last_rule.inserted_rows
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

impl Backend for EGraph {
    fn add_table(&mut self, config: FunctionConfig) -> FunctionId {
        let name = config.name.clone();
        self.storage
            .register_table(self.registries.base_values(), config)
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

    fn supports_fresh_ids(&self) -> bool {
        true
    }

    fn fresh_id(&mut self) -> Value {
        self.storage
            .fresh_id()
            .unwrap_or_else(|error| panic!("DuckDB fresh_id failed: {error:#}"))
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

    fn add_values_with_fresh(
        &mut self,
        values: Vec<(FunctionId, Vec<NativeInputValue>)>,
    ) -> Result<()> {
        match self
            .storage
            .insert_batch_with_fresh(self.registries.base_values(), values)
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
        let plan = compile_rule(&self.storage, self.registries.base_values(), rule)?;
        let id = RuleId::new(self.rules.len() as u32);
        self.rules.push(Some(RegisteredRule { plan, watermark: 0 }));
        Ok(id)
    }

    fn free_rule(&mut self, id: RuleId) {
        if let Some(slot) = self.rules.get_mut(id.rep() as usize) {
            *slot = None;
        }
    }

    fn run_rules(&mut self, run: RuleSetRun<'_>) -> Result<IterationReport> {
        self.take_deferred_panic()?;
        if run.rules.is_empty() {
            self.last_rule = RuleExecutionStats::default();
            return Ok(IterationReport::default());
        }

        let scheduled = run
            .rules
            .iter()
            .map(|id| {
                self.rules
                    .get(id.rep() as usize)
                    .and_then(Option::as_ref)
                    .map(|registered| (&registered.plan, registered.watermark))
                    .ok_or_else(|| anyhow!("DuckDB cannot run freed or unknown rule {}", id.rep()))
            })
            .collect::<Result<Vec<_>>>()?;
        let stats = self.storage.execute_rules(&scheduled)?;
        drop(scheduled);

        for id in run.rules {
            let registered = self.rules[id.rep() as usize]
                .as_mut()
                .expect("validated rule disappeared during synchronous execution");
            registered.watermark = stats.watermark;
        }
        let mut report = IterationReport::default();
        report.rule_set_report.changed = stats.changed;
        self.last_rule = stats;
        Ok(report)
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

    fn register_get_fresh(&mut self) -> ExternalFunctionId {
        // This ID is a semantic token retained in typed rule IR. Executing it
        // as a host callback would move rule effects out of DuckDB's atomic SQL
        // transaction, so accidental host execution fails closed. Native rule
        // lowering reserves ids directly from the SQL counter instead.
        self.new_panic("DuckDB get-fresh requires native SQL lowering".to_string())
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
            "DuckDB backend checkpoint 0.5: runtime={:?}, next_table={}, rules={}, deferred_panic={:?}",
            self.runtime_version(),
            self.peek_next_function_id().rep(),
            self.rules.iter().flatten().count(),
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
    use std::panic::{AssertUnwindSafe, catch_unwind};

    use super::*;
    use egglog_backend_trait::{DefaultVal, MergeAction, MergeFn, NativeInputValue};
    use egglog_core_relations::Boxed;
    use ordered_float::OrderedFloat;

    #[test]
    fn assert_eq_equal_input_duplicates_are_idempotent() -> Result<()> {
        let mut backend = EGraph::new()?;
        backend.base_values_mut().register_type::<()>();
        backend.base_values_mut().register_type::<bool>();
        backend.base_values_mut().register_type::<i64>();
        backend
            .base_values_mut()
            .register_type::<Boxed<OrderedFloat<f64>>>();
        backend.base_values_mut().register_type::<Boxed<String>>();
        let table = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::AssertEq,
            name: "assert-eq-equal-duplicates".to_string(),
            can_subsume: false,
        });

        backend.add_values(vec![
            (table, vec![Value::new(1), Value::new(10)]),
            (table, vec![Value::new(1), Value::new(10)]),
        ])?;
        assert_eq!(backend.table_size(table), 1);
        assert_eq!(
            backend.lookup_row(table, &[Value::new(1)]),
            Some(vec![Value::new(1), Value::new(10)])
        );
        Ok(())
    }

    #[test]
    fn assert_eq_input_conflicts_are_setwise_atomic_and_recoverable() -> Result<()> {
        let mut backend = EGraph::new()?;
        backend.base_values_mut().register_type::<()>();
        backend.base_values_mut().register_type::<bool>();
        backend.base_values_mut().register_type::<i64>();
        backend
            .base_values_mut()
            .register_type::<Boxed<OrderedFloat<f64>>>();
        backend.base_values_mut().register_type::<Boxed<String>>();
        let early = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::Old,
            name: "early user target".to_string(),
            can_subsume: false,
        });
        let asserted = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id],
            n_vals: 1,
            n_identity_vals: Some(1),
            default: DefaultVal::Const(Value::new(99)),
            merge: MergeFn::AssertEq,
            name: "asserted user target; DROP TABLE".to_string(),
            can_subsume: true,
        });

        backend.add_values(vec![(asserted, vec![Value::new(1), Value::new(10)])])?;
        let original_generation = backend.storage.generation()?;
        let original_row_generation =
            backend.storage.scan(backend.base_values(), asserted)?[0].generation;
        backend.add_values(vec![
            (asserted, vec![Value::new(1), Value::new(10)]),
            (asserted, vec![Value::new(1), Value::new(10)]),
        ])?;
        assert_eq!(backend.last_input_inserted_rows(), 0);
        assert_eq!(backend.storage.generation()?, original_generation);
        assert_eq!(
            backend.storage.scan(backend.base_values(), asserted)?[0].generation,
            original_row_generation
        );

        let existing_error = backend
            .add_values(vec![(asserted, vec![Value::new(1), Value::new(11)])])
            .unwrap_err();
        assert!(existing_error.to_string().contains("AssertEq"));
        let intra_error = backend
            .add_values(vec![
                (asserted, vec![Value::new(2), Value::new(20)]),
                (asserted, vec![Value::new(2), Value::new(21)]),
            ])
            .unwrap_err();
        assert!(intra_error.to_string().contains("AssertEq"));
        assert_eq!(backend.table_size(asserted), 1);
        assert_eq!(backend.storage.generation()?, original_generation);

        backend.storage.with_connection(|connection| {
            connection.execute(
                &format!(
                    "UPDATE {} SET __subsumed = TRUE WHERE c0 = CAST('1' AS UBIGINT)",
                    crate::storage::sql_table(asserted)
                ),
                [],
            )?;
            Ok(())
        })?;
        backend.add_values(vec![(asserted, vec![Value::new(1), Value::new(10)])])?;
        let subsumed = backend.storage.scan(backend.base_values(), asserted)?;
        assert_eq!(subsumed.len(), 1);
        assert!(
            subsumed[0].subsumed,
            "equal duplicate must not revive a row"
        );
        assert_eq!(subsumed[0].generation, original_row_generation);
        assert!(
            backend
                .add_values(vec![(asserted, vec![Value::new(1), Value::new(12)],)])
                .unwrap_err()
                .to_string()
                .contains("AssertEq")
        );

        let nullary = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::AssertEq,
            name: "nullary-assert".to_string(),
            can_subsume: false,
        });
        backend.add_values(vec![
            (nullary, vec![Value::new(30)]),
            (nullary, vec![Value::new(30)]),
        ])?;
        assert_eq!(backend.table_size(nullary), 1);
        let generation_before_conflict = backend.storage.generation()?;
        assert!(
            backend
                .add_values(vec![
                    (nullary, vec![Value::new(31)]),
                    (nullary, vec![Value::new(32)]),
                ])
                .unwrap_err()
                .to_string()
                .contains("AssertEq")
        );
        assert_eq!(backend.storage.generation()?, generation_before_conflict);

        let heterogeneous_error = backend
            .add_values(vec![
                (early, vec![Value::new(7), Value::new(70)]),
                (asserted, vec![Value::new(1), Value::new(13)]),
            ])
            .unwrap_err();
        assert!(heterogeneous_error.to_string().contains("AssertEq"));
        assert_eq!(backend.table_size(early), 0);
        assert_eq!(backend.storage.generation()?, generation_before_conflict);
        assert_eq!(backend.last_input_rows(), 0);

        backend.add_values(vec![
            (early, vec![Value::new(7), Value::new(70)]),
            (asserted, vec![Value::new(1), Value::new(10)]),
        ])?;
        assert_eq!(backend.table_size(early), 1);
        assert_eq!(backend.table_size(asserted), 1);
        let generated = backend.storage.latest_input_sql();
        assert!(generated.iter().all(|sql| !sql.contains('?')));
        assert!(
            generated
                .iter()
                .all(|sql| !sql.contains("asserted user target"))
        );
        Ok(())
    }

    #[test]
    fn sql_fresh_ids_and_native_input_slots_are_one_atomic_domain() -> Result<()> {
        let mut backend = EGraph::new()?;
        backend.base_values_mut().register_type::<()>();
        backend.base_values_mut().register_type::<bool>();
        let int_ty = backend.base_values_mut().register_type::<i64>();
        backend
            .base_values_mut()
            .register_type::<Boxed<OrderedFloat<f64>>>();
        backend.base_values_mut().register_type::<Boxed<String>>();
        let keep_old = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::Old,
            name: "fresh-slot-target".to_string(),
            can_subsume: false,
        });
        let asserted = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::AssertEq,
            name: "fresh-slot-assert".to_string(),
            can_subsume: false,
        });
        let base_output = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Base(int_ty)],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::Old,
            name: "fresh-slot-base".to_string(),
            can_subsume: false,
        });

        assert!(Backend::id_counter(&backend).is_none());
        assert!(Backend::supports_fresh_ids(&backend));
        assert_eq!(Backend::fresh_id(&mut backend), Value::new(0));
        Backend::add_values_with_fresh(
            &mut backend,
            vec![
                (
                    keep_old,
                    vec![
                        NativeInputValue::Existing(Value::new(10)),
                        NativeInputValue::FreshSlot(0),
                    ],
                ),
                (
                    keep_old,
                    vec![
                        NativeInputValue::Existing(Value::new(11)),
                        NativeInputValue::FreshSlot(0),
                    ],
                ),
                (
                    keep_old,
                    vec![
                        NativeInputValue::Existing(Value::new(12)),
                        NativeInputValue::FreshSlot(1),
                    ],
                ),
            ],
        )?;
        assert_eq!(
            backend.lookup_id(keep_old, &[Value::new(10)]),
            Some(Value::new(1))
        );
        assert_eq!(
            backend.lookup_id(keep_old, &[Value::new(11)]),
            Some(Value::new(1))
        );
        assert_eq!(
            backend.lookup_id(keep_old, &[Value::new(12)]),
            Some(Value::new(2))
        );
        assert_eq!(backend.storage.next_fresh_id()?, 3);

        let generation_before_hostile = backend.storage.generation()?;
        let sparse = Backend::add_values_with_fresh(
            &mut backend,
            vec![(
                keep_old,
                vec![
                    NativeInputValue::Existing(Value::new(20)),
                    NativeInputValue::FreshSlot(1),
                ],
            )],
        )
        .unwrap_err();
        assert!(sparse.to_string().contains("dense"));
        let wrong_type = Backend::add_values_with_fresh(
            &mut backend,
            vec![(
                base_output,
                vec![
                    NativeInputValue::Existing(Value::new(20)),
                    NativeInputValue::FreshSlot(0),
                ],
            )],
        )
        .unwrap_err();
        assert!(wrong_type.to_string().contains("non-id"));
        let stale = Backend::add_values_with_fresh(
            &mut backend,
            vec![(
                keep_old,
                vec![
                    NativeInputValue::Existing(Value::new(21)),
                    NativeInputValue::Existing(Value::new(u32::MAX)),
                ],
            )],
        )
        .unwrap_err();
        assert!(stale.to_string().contains("stale Value sentinel"));
        assert_eq!(backend.lookup_id(keep_old, &[Value::new(21)]), None);
        assert_eq!(backend.storage.next_fresh_id()?, 3);
        assert_eq!(backend.storage.generation()?, generation_before_hostile);

        Backend::add_values(
            &mut backend,
            vec![(asserted, vec![Value::new(1), Value::new(100)])],
        )?;
        let generation_before_conflict = backend.storage.generation()?;
        let error = Backend::add_values_with_fresh(
            &mut backend,
            vec![
                (
                    keep_old,
                    vec![
                        NativeInputValue::Existing(Value::new(30)),
                        NativeInputValue::FreshSlot(0),
                    ],
                ),
                (
                    asserted,
                    vec![
                        NativeInputValue::Existing(Value::new(1)),
                        NativeInputValue::Existing(Value::new(101)),
                    ],
                ),
            ],
        )
        .unwrap_err();
        assert!(error.to_string().contains("AssertEq"));
        assert_eq!(backend.lookup_id(keep_old, &[Value::new(30)]), None);
        assert_eq!(backend.storage.next_fresh_id()?, 3);
        assert_eq!(backend.storage.generation()?, generation_before_conflict);

        Backend::add_values_with_fresh(
            &mut backend,
            vec![(
                keep_old,
                vec![
                    NativeInputValue::Existing(Value::new(30)),
                    NativeInputValue::FreshSlot(0),
                ],
            )],
        )?;
        assert_eq!(
            backend.lookup_id(keep_old, &[Value::new(30)]),
            Some(Value::new(3))
        );
        assert_eq!(backend.storage.next_fresh_id()?, 4);

        let token = Backend::register_get_fresh(&mut backend);
        let host_result = backend
            .registries
            .with_execution_state(|state| state.call_external_func(token, &[]));
        assert_eq!(host_result, None);
        let host_error = backend.take_deferred_panic().unwrap_err();
        assert!(host_error.to_string().contains("native SQL lowering"));
        assert_eq!(backend.storage.next_fresh_id()?, 4);
        assert_eq!(Backend::fresh_id(&mut backend), Value::new(4));

        let generation_before_idempotent = backend.storage.generation()?;
        Backend::add_values_with_fresh(
            &mut backend,
            vec![(
                keep_old,
                vec![
                    NativeInputValue::Existing(Value::new(30)),
                    NativeInputValue::FreshSlot(0),
                ],
            )],
        )?;
        assert_eq!(backend.storage.next_fresh_id()?, 6);
        assert_eq!(backend.storage.generation()?, generation_before_idempotent);
        assert_eq!(
            backend.lookup_id(keep_old, &[Value::new(30)]),
            Some(Value::new(3))
        );

        backend.storage.set_next_fresh_id(u32::MAX as u64 - 1)?;
        Backend::add_values_with_fresh(
            &mut backend,
            vec![(
                keep_old,
                vec![
                    NativeInputValue::Existing(Value::new(40)),
                    NativeInputValue::FreshSlot(0),
                ],
            )],
        )?;
        assert_eq!(
            backend.lookup_id(keep_old, &[Value::new(40)]),
            Some(Value::new(u32::MAX - 1))
        );
        let exhausted = Backend::add_values_with_fresh(
            &mut backend,
            vec![(
                keep_old,
                vec![
                    NativeInputValue::Existing(Value::new(41)),
                    NativeInputValue::FreshSlot(0),
                ],
            )],
        )
        .unwrap_err();
        assert!(exhausted.to_string().contains("usable Value domain"));
        assert_eq!(backend.storage.next_fresh_id()?, u32::MAX as u64);
        assert_eq!(backend.lookup_id(keep_old, &[Value::new(41)]), None);
        Ok(())
    }

    #[test]
    fn function_config_is_retained_and_deferred_preflight_preserves_ids() -> Result<()> {
        let mut backend = EGraph::new()?;
        backend.base_values_mut().register_type::<()>();
        backend.base_values_mut().register_type::<bool>();
        let int_ty = backend.base_values_mut().register_type::<i64>();
        backend
            .base_values_mut()
            .register_type::<Boxed<OrderedFloat<f64>>>();
        backend.base_values_mut().register_type::<Boxed<String>>();
        let executable = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::Old,
            name: "executable".to_string(),
            can_subsume: false,
        });
        let tuple_output = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
            n_vals: 2,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::Columns(vec![MergeFn::OldCol(0), MergeFn::OldCol(1)]),
            name: "tuple-output".to_string(),
            can_subsume: false,
        });
        let function_reader = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::Function(tuple_output, vec![MergeFn::Old, MergeFn::New]),
            name: "tuple-function-reader".to_string(),
            can_subsume: false,
        });
        let lookup_reader = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::Lookup(tuple_output, vec![MergeFn::Old]),
            name: "tuple-lookup-reader".to_string(),
            can_subsume: false,
        });
        assert!(matches!(
            backend.storage.table_info(function_reader)?.merge.as_ref(),
            MergeFn::Function(id, arguments) if *id == tuple_output && arguments.len() == 2
        ));
        assert!(matches!(
            backend.storage.table_info(lookup_reader)?.merge.as_ref(),
            MergeFn::Lookup(id, arguments) if *id == tuple_output && arguments.len() == 1
        ));
        let primitive = backend.register_external_func(Box::new(
            egglog_core_relations::make_external_func(|_, args| args.first().copied()),
        ));
        let typed_primitive = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Base(int_ty)],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Fail,
            merge: MergeFn::Primitive {
                id: primitive,
                name: "ordering-min".to_string(),
                input: vec![ColumnTy::Base(int_ty); 2],
                output: ColumnTy::Base(int_ty),
                args: vec![
                    MergeFn::Const {
                        value: backend.base_values().get(5i64),
                        ty: ColumnTy::Base(int_ty),
                    },
                    MergeFn::Old,
                ],
            },
            name: "typed-primitive-retention".to_string(),
            can_subsume: false,
        });
        let typed = backend.storage.table_info(typed_primitive)?;
        let MergeFn::Primitive {
            id,
            name,
            input,
            output,
            args,
        } = typed.merge.as_ref()
        else {
            panic!("typed primitive merge was not retained");
        };
        assert_eq!(*id, primitive);
        assert_eq!(name, "ordering-min");
        assert_eq!(input, &[ColumnTy::Base(int_ty); 2]);
        assert_eq!(*output, ColumnTy::Base(int_ty));
        assert!(matches!(
            args.as_slice(),
            [MergeFn::Const { ty, .. }, MergeFn::Old] if *ty == ColumnTy::Base(int_ty)
        ));
        let predicted = backend.peek_next_function_id();
        let deferred = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id, ColumnTy::Id],
            n_vals: 2,
            n_identity_vals: Some(1),
            default: DefaultVal::Const(Value::new(42)),
            merge: MergeFn::Block {
                actions: vec![
                    MergeAction::Let {
                        slot: 0,
                        value: MergeFn::Const {
                            value: Value::new(10),
                            ty: ColumnTy::Id,
                        },
                    },
                    MergeAction::Set(
                        predicted,
                        vec![
                            MergeFn::Const {
                                value: Value::new(5),
                                ty: ColumnTy::Id,
                            },
                            MergeFn::LetVar(0),
                            MergeFn::NewCol(1),
                        ],
                    ),
                ],
                result: Box::new(MergeFn::Columns(vec![
                    MergeFn::LetVar(0),
                    MergeFn::NewCol(1),
                ])),
            },
            name: "retained-self-write".to_string(),
            can_subsume: true,
        });
        assert_eq!(deferred, predicted);
        let info = backend.storage.table_info(deferred)?;
        assert_eq!(info.name, "retained-self-write");
        assert_eq!(info.schema, [ColumnTy::Id, ColumnTy::Id, ColumnTy::Id]);
        assert_eq!(info.n_keys, 1);
        assert_eq!(info.n_vals, 2);
        assert_eq!(info.n_identity_vals, Some(1));
        assert!(matches!(info.default, DefaultVal::Const(value) if value == Value::new(42)));
        assert!(info.can_subsume);
        let MergeFn::Block { actions, result } = info.merge.as_ref() else {
            panic!("full merge block was not retained");
        };
        assert_eq!(actions.len(), 2);
        assert!(matches!(actions[0], MergeAction::Let { slot: 0, .. }));
        assert!(matches!(actions[1], MergeAction::Set(id, _) if id == deferred));
        assert!(matches!(result.as_ref(), MergeFn::Columns(columns) if columns.len() == 2));

        let generation_before = backend.storage.generation()?;
        let error = backend
            .add_values(vec![
                (executable, vec![Value::new(1), Value::new(2)]),
                (deferred, vec![Value::new(3), Value::new(4), Value::new(5)]),
            ])
            .unwrap_err();
        assert!(error.to_string().contains("registered but deferred"));
        assert_eq!(backend.table_size(executable), 0);
        assert_eq!(backend.table_size(deferred), 0);
        assert_eq!(backend.storage.generation()?, generation_before);

        let next = backend.peek_next_function_id();
        let wrong_function_arity = catch_unwind(AssertUnwindSafe(|| {
            backend.add_table(FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id],
                n_vals: 1,
                n_identity_vals: None,
                default: DefaultVal::Fail,
                merge: MergeFn::Function(tuple_output, vec![MergeFn::Old]),
                name: "invalid-function-arity".to_string(),
                can_subsume: false,
            })
        }));
        assert!(wrong_function_arity.is_err());
        assert_eq!(backend.peek_next_function_id(), next);

        let nested = catch_unwind(AssertUnwindSafe(|| {
            backend.add_table(FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id],
                n_vals: 1,
                n_identity_vals: None,
                default: DefaultVal::Fail,
                merge: MergeFn::Columns(vec![MergeFn::Columns(vec![MergeFn::Old])]),
                name: "invalid-nested-columns".to_string(),
                can_subsume: false,
            })
        }));
        assert!(nested.is_err());
        assert_eq!(backend.peek_next_function_id(), next);

        let self_read = catch_unwind(AssertUnwindSafe(|| {
            backend.add_table(FunctionConfig {
                schema: vec![ColumnTy::Id, ColumnTy::Id],
                n_vals: 1,
                n_identity_vals: None,
                default: DefaultVal::Fail,
                merge: MergeFn::Function(next, vec![MergeFn::Old]),
                name: "invalid-self-read".to_string(),
                can_subsume: false,
            })
        }));
        assert!(self_read.is_err());
        assert_eq!(backend.peek_next_function_id(), next);

        let admitted = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Id],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::FreshId,
            merge: MergeFn::New,
            name: "admitted-after-invalid".to_string(),
            can_subsume: false,
        });
        assert_eq!(admitted, next, "invalid configs must not consume table ids");
        Ok(())
    }

    #[test]
    fn keep_old_input_is_sql_native_and_deferred_writes_fail_closed() -> Result<()> {
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

        let deferred = backend.add_table(FunctionConfig {
            schema: vec![ColumnTy::Id, ColumnTy::Base(i64_ty)],
            n_vals: 1,
            n_identity_vals: None,
            default: DefaultVal::Const(ten),
            merge: MergeFn::New,
            name: "deferred-new".to_string(),
            can_subsume: true,
        });
        let error = backend
            .add_values(vec![(deferred, vec![Value::new(1), twenty])])
            .unwrap_err();
        assert!(error.to_string().contains("registered but deferred"));
        assert_eq!(backend.table_size(deferred), 0);
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
    fn unknown_rule_boundary_fails_closed() -> Result<()> {
        let mut backend = EGraph::new()?;
        // Exercise both the empty scheduling no-op and strict rejection of an
        // id that was never admitted by the production rule compiler.
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
        assert!(error.to_string().contains("freed or unknown rule"));
        Ok(())
    }
}
