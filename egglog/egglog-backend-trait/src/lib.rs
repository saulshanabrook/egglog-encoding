//! # egglog-backend-trait
//!
//! A small, backend-agnostic interface for driving an egglog e-graph. The
//! frontend `egglog::EGraph` holds a `Box<dyn Backend>` and performs all state
//! access through the [`Backend`] trait, so a third party can plug in their own
//! execution engine (a relational database, a dataflow system, …) without
//! forking the frontend.
//!
//! ## What a backend must provide
//!
//! [`Backend`] is deliberately small. The *required* surface is the handful of
//! operations the frontend actually needs: register functions ([`Backend::add_table`]),
//! build and run rules ([`Backend::new_rule`] / [`Backend::run_rules`]), read
//! tables back ([`Backend::for_each_while_dyn`] / [`Backend::table_size`]),
//! canonicalize ids ([`Backend::get_canon_repr`]), reach the value registries
//! ([`Backend::base_values`] / [`Backend::container_values`]), and register
//! primitives ([`Backend::register_external_func`]).
//!
//! Rules are built through [`RuleBuilderOps`], which mirrors the reference
//! `egglog_bridge::RuleBuilder` one-for-one: a backend accumulates the calls
//! into its own IR and finalizes on [`RuleBuilderOps::build`].
//!
//! ## Rule execution contract
//!
//! A [`Backend::run_rules`] call is one bounded rule-iteration over the
//! backend's state. RHS effects are staged while matches are being evaluated and
//! are flushed into tables according to the same semantics as the reference
//! bridge backend. Rule bodies observe a stable read view for the iteration; a
//! row produced by an RHS `set`, `lookup`, `remove`, or `subsume` does not create
//! new matches for another rule body until a later `run_rules` call, although
//! RHS lookups in the same action stream may observe earlier staged
//! lookup-or-insert predictions.
//!
//! During the flush, deletions are applied before insertions/sets for the same
//! bounded iteration. This is observable for rebuild-style actions that emit
//! `delete old; set new`: if both target the same function key, the set is the
//! row retained after the flush. Subsumption actions are applied after sets, so a
//! row written and subsumed in the same iteration ends the iteration subsumed
//! rather than live.
//!
//! For function tables, `set` observes the current row for the function's input
//! key, if any, and folds conflicting output values through the configured
//! [`MergeFn`]. In each fold, `old` is the currently retained output value and
//! `new` is the incoming staged value. Implementations may choose their own
//! physical representation, but they must not derive `old`/`new` from unordered
//! table iteration; non-monotone merge expressions are already user-visible
//! undefined behavior, but backend-specific container ordering should not add an
//! extra source of divergence.
//!
//! Seminaive freshness is part of the observable execution model. If a row is
//! removed and later reinserted with the same logical columns, later rule
//! iterations must be able to treat that row as newly available, just as the
//! reference backend does with its hidden row timestamp. Backends that feed an
//! incremental engine must therefore track row generations or equivalent event
//! identity, not only end-state set membership.
//!
//! Subsumption is semantically a bit on a row, not a separate table. Ordinary
//! body atoms see only live rows; `query_table(..., is_subsumed = None)` sees
//! live and subsumed rows; `Some(true)` sees only subsumed rows. A subsumed row
//! remains the current row for lookup and merge purposes, so a later lookup or
//! `set` for the same key must find/merge with that row without making it live
//! again unless an explicit backend operation says otherwise.
//!
//! ## Advanced features are optional
//!
//! Capabilities that not every backend can offer — the seminaive-safe
//! [`ActionRegistry`] ([`Backend::action_registry`]), container sorts,
//! subsumption — are exposed as methods with **default** bodies (return `false`
//! / `unimplemented!`). An implementer overrides only what it supports and
//! advertises it through the `supports_*` flags; the frontend gates on those.
//!
//! ## Ergonomic sugar
//!
//! The object-safe [`Backend`] methods take erased closures (`&mut dyn FnMut(..)`)
//! and carry a `_dyn` suffix. Generic, ergonomic wrappers ([`BackendExt::for_each`],
//! [`BackendExt::with_execution_state`], [`BackendExt::base_value_constant`], …)
//! live on the [`BackendExt`] extension trait (a blanket impl over every
//! `Backend`), so call sites read naturally — import `BackendExt` to use them.
//!
//! ## Relationship to `egglog-bridge`
//!
//! This crate depends on `egglog-bridge` and re-exports its vocabulary types
//! ([`FunctionConfig`], [`MergeFn`], [`ColumnTy`], [`Value`], …) so an
//! implementer imports them from here. It also provides the reference
//! `impl Backend for egglog_bridge::EGraph` (see `backend_impl`). The only
//! change to the bridge itself is a one-line re-export of `Variable` /
//! `VariableId`, which a backend needs to construct [`QueryEntry::Var`].

use std::any::Any;
use std::sync::{Arc, RwLock};

use anyhow::Result;

mod backend_impl;

// ---------------------------------------------------------------------------
// Re-exports: the shared vocabulary a backend implementer works with.
// ---------------------------------------------------------------------------

pub use egglog_bridge::{
    ActionRegistry, ColumnTy, DefaultVal, FunctionConfig, FunctionId, MergeFn, QueryEntry, RuleId,
    ScanEntry, Variable, VariableId,
};
pub use egglog_core_relations::{
    BaseValue, BaseValueId, BaseValues, ContainerValue, ContainerValues, CounterId, ExecutionState,
    ExternalFunction, ExternalFunctionId, Value,
};
pub use egglog_reports::{IterationReport, ReportLevel};

/// A lazily-computed failure message for RHS lookups / external calls.
///
/// Only built if the lookup or call actually fails at runtime; deferring it
/// avoids formatting a `Span` (an `O(file)` scan) for every action in every
/// generated rule. Boxed so the trait stays object-safe.
pub type PanicMsg = Box<dyn FnOnce() -> String + Send>;

// ---------------------------------------------------------------------------
// The `Backend` trait
// ---------------------------------------------------------------------------

/// A backend that stores an egglog e-graph and runs rules over it.
///
/// The frontend holds a `Box<dyn Backend>` and drives everything through this
/// trait. Implementations: the in-memory reference `egglog_bridge::EGraph`
/// (this crate's `backend_impl`), and separate-crate engines such as the
/// Differential Dataflow backend in `egglog-experimental/dd`.
///
/// See the crate docs for which methods are required vs. optional and how the
/// ergonomic sugar on `dyn Backend` relates to the `_dyn` methods here.
pub trait Backend: Send + Sync {
    // -- table lifecycle ----------------------------------------------------

    /// Register a function / relation / constructor and return its handle.
    fn add_table(&mut self, config: FunctionConfig) -> FunctionId;

    /// Number of rows currently in the given function's table.
    fn table_size(&self, table: FunctionId) -> usize;

    /// Remove every row from the given function's table.
    fn clear_table(&mut self, func: FunctionId);

    // -- iteration (object-safe; see `for_each` / `for_each_while` sugar) ----

    /// Call `f` on every row in `table`. Object-safe form; prefer the
    /// [`BackendExt::for_each`] sugar.
    fn for_each_dyn(&self, table: FunctionId, f: &mut dyn for<'r> FnMut(ScanEntry<'r>));

    /// Iterate rows in `table`, stopping early when `f` returns `false`.
    /// Object-safe form; prefer the [`BackendExt::for_each_while`] sugar.
    fn for_each_while_dyn(
        &self,
        table: FunctionId,
        f: &mut dyn for<'r> FnMut(ScanEntry<'r>) -> bool,
    );

    // -- direct access ------------------------------------------------------

    /// Canonical representative of `val` under `ty` (union-find find for
    /// [`ColumnTy::Id`]; identity for a base value).
    fn get_canon_repr(&self, val: Value, ty: ColumnTy) -> Value;

    /// The backend's base-value (primitive) registry.
    fn base_values(&self) -> &BaseValues;

    /// Mutable base-value registry (used to register new base types).
    fn base_values_mut(&mut self) -> &mut BaseValues;

    /// The backend's container-value registry.
    fn container_values(&self) -> &ContainerValues;

    /// Mutable access to the backend's container-value registry, for backends
    /// that can execute container primitives without the bridge.
    fn container_values_mut_dyn(&mut self) -> Option<&mut ContainerValues> {
        None
    }

    /// Allocate a fresh counter for container-value ids, for backends that can
    /// execute container primitives without the bridge.
    fn new_container_id_counter(&mut self) -> Option<CounterId> {
        None
    }

    // -- execution state (object-safe; see `with_execution_state` sugar) -----

    /// Run `f` against a fresh execution state (for staging updates / calling
    /// primitives). Object-safe form; prefer [`BackendExt::with_execution_state`].
    fn with_execution_state_dyn(&self, f: &mut dyn FnMut(&mut ExecutionState<'_>));

    /// Like [`Backend::with_execution_state_dyn`], but returns whether `f`
    /// staged any mutation. Object-safe form; prefer
    /// [`BackendExt::with_execution_state_tracked`].
    fn with_execution_state_tracked_dyn(&self, f: &mut dyn FnMut(&mut ExecutionState<'_>)) -> bool;

    // -- rule management ----------------------------------------------------

    /// Begin building a rule. Populate via [`RuleBuilderOps`] and finalize with
    /// [`RuleBuilderOps::build`].
    fn new_rule<'a>(&'a mut self, desc: &str, seminaive: bool) -> Box<dyn RuleBuilderOps + 'a>;

    /// Drop a registered rule.
    fn free_rule(&mut self, id: RuleId);

    /// Run one bounded iteration of the given rule set.
    ///
    /// Implementations should evaluate rule bodies against a stable read view
    /// for this iteration and stage RHS effects until the rule firing is
    /// applied. The externally visible behavior must match the rule execution
    /// contract in the crate docs, especially for function `set`/`merge`,
    /// `remove`, `subsume`, and constructor lookup-or-insert effects.
    fn run_rules(&mut self, rules: &[RuleId]) -> Result<IterationReport>;

    /// Drain staged inserts and rebuild if the union-find changed. Returns
    /// whether the database changed.
    fn flush_updates(&mut self) -> bool;

    // -- primitives ---------------------------------------------------------

    /// Register a user-defined primitive (`ExternalFunction`).
    fn register_external_func(
        &mut self,
        func: Box<dyn ExternalFunction + 'static>,
    ) -> ExternalFunctionId;

    /// Drop a user-defined primitive.
    fn free_external_func(&mut self, func: ExternalFunctionId);

    /// Register a deferred-panic primitive; returns its id.
    fn new_panic(&mut self, message: String) -> ExternalFunctionId;

    // -- diagnostics --------------------------------------------------------

    /// Set the verbosity of the per-iteration timing report.
    fn set_report_level(&mut self, level: ReportLevel);

    /// Dump the database state to the log channel (debug only).
    fn dump_debug_info(&self);

    // -- cloning ------------------------------------------------------------

    /// Deep-clone the backend (used for push/pop snapshots).
    fn clone_boxed(&self) -> Box<dyn Backend>;

    // -- optional / advanced (default-provided) -----------------------------

    /// Handle to the seminaive-safe [`ActionRegistry`] that registry-backed
    /// primitives dispatch through.
    ///
    /// Only backends whose primitives run against an in-memory
    /// [`ExecutionState`] provide this (the reference bridge). Backends that
    /// have no such registry return [`Backend::supports_action_registry`] =
    /// `false` and leave this default (the frontend routes their primitives
    /// through a registry-free path).
    fn action_registry(&self) -> &Arc<RwLock<ActionRegistry>> {
        unimplemented!("this backend has no action registry")
    }

    /// Whether this backend supports `Vec` / `Set` / `Map` / `MultiSet`
    /// container sorts.
    fn supports_containers(&self) -> bool {
        true
    }

    /// Whether this backend exposes an in-memory [`ActionRegistry`]
    /// ([`Backend::action_registry`]).
    fn supports_action_registry(&self) -> bool {
        true
    }

    /// Whether this backend needs the frontend's term-encoding pipeline to be
    /// enabled. A backend without a native union-find, such as the experimental
    /// Differential Dataflow backend, relies on term encoding to lower
    /// congruence and rebuild to ordinary rules over `@uf` tables; running it in
    /// native mode would silently drop `union`s. The frontend refuses to run
    /// such a backend unless the e-graph was built with term encoding (via
    /// `EGraph::with_term_encoding`).
    fn requires_term_encoding(&self) -> bool {
        false
    }

    // -- concrete-backend access (escape hatch) -----------------------------

    /// `&self` as `&dyn Any`, to downcast to the concrete backend type. Used
    /// by the container-registration sugar to reach the reference bridge.
    /// Implementations return `self`.
    fn as_any(&self) -> &dyn Any;

    /// Mutable counterpart of [`Backend::as_any`]. Implementations return
    /// `self`.
    fn as_any_mut(&mut self) -> &mut dyn Any;
}

impl Clone for Box<dyn Backend> {
    fn clone(&self) -> Self {
        self.clone_boxed()
    }
}

// ---------------------------------------------------------------------------
// Ergonomic sugar: `BackendExt`
// ---------------------------------------------------------------------------

/// Ergonomic, generic wrappers over the object-safe [`Backend`] surface.
///
/// Provided by a blanket impl for every `B: Backend + ?Sized`, so the sugar is
/// available on `dyn Backend`, `Box<dyn Backend>`, and any concrete backend.
/// Import this trait to call `for_each` / `with_execution_state` /
/// `base_value_constant` / `register_container_ty` on a backend.
pub trait BackendExt {
    /// Call `f` on every row in `table`.
    fn for_each(&self, table: FunctionId, f: impl for<'r> FnMut(ScanEntry<'r>));

    /// Iterate rows in `table`, stopping when `f` returns `false`.
    fn for_each_while(&self, table: FunctionId, f: impl for<'r> FnMut(ScanEntry<'r>) -> bool);

    /// Run `f` against a fresh execution state and return its result.
    fn with_execution_state<R>(&self, f: impl FnOnce(&mut ExecutionState<'_>) -> R) -> R;

    /// Run `f` against a fresh execution state, also reporting whether `f`
    /// staged any mutation.
    fn with_execution_state_tracked<R>(
        &self,
        f: impl FnOnce(&mut ExecutionState<'_>) -> R,
    ) -> (R, bool);

    /// Build a [`QueryEntry`] constant for a typed base value.
    fn base_value_constant<T: BaseValue>(&self, x: T) -> QueryEntry;

    /// Register a container-value type `C`.
    ///
    /// Container registration wires the container into the backend's rebuild
    /// loop, which requires backend-internal state. Only the reference bridge
    /// implements it today; on a backend that does not support containers this
    /// is a no-op (such programs never construct containers).
    fn register_container_ty<C: ContainerValue>(&mut self);

    /// Intern a container value `C`, returning its `Value` handle.
    fn get_container_value<C: ContainerValue>(&mut self, val: C) -> Value;
}

impl<B: Backend + ?Sized> BackendExt for B {
    fn for_each(&self, table: FunctionId, mut f: impl for<'r> FnMut(ScanEntry<'r>)) {
        self.for_each_dyn(table, &mut f);
    }

    fn for_each_while(&self, table: FunctionId, mut f: impl for<'r> FnMut(ScanEntry<'r>) -> bool) {
        self.for_each_while_dyn(table, &mut f);
    }

    fn with_execution_state<R>(&self, f: impl FnOnce(&mut ExecutionState<'_>) -> R) -> R {
        let mut f = Some(f);
        let mut out: Option<R> = None;
        self.with_execution_state_dyn(&mut |es| {
            let f = f.take().expect("with_execution_state closure called once");
            out = Some(f(es));
        });
        out.expect("with_execution_state_dyn must invoke its closure exactly once")
    }

    fn with_execution_state_tracked<R>(
        &self,
        f: impl FnOnce(&mut ExecutionState<'_>) -> R,
    ) -> (R, bool) {
        let mut f = Some(f);
        let mut out: Option<R> = None;
        let mutated = self.with_execution_state_tracked_dyn(&mut |es| {
            let f = f
                .take()
                .expect("with_execution_state_tracked closure called once");
            out = Some(f(es));
        });
        (
            out.expect("with_execution_state_tracked_dyn must invoke its closure exactly once"),
            mutated,
        )
    }

    fn base_value_constant<T: BaseValue>(&self, x: T) -> QueryEntry {
        QueryEntry::Const {
            val: self.base_values().get(x),
            ty: ColumnTy::Base(self.base_values().get_ty::<T>()),
        }
    }

    fn register_container_ty<C: ContainerValue>(&mut self) {
        if let Some(bridge) = self.as_any_mut().downcast_mut::<egglog_bridge::EGraph>() {
            bridge.register_container_ty::<C>();
        } else if let Some(counter) = self.new_container_id_counter() {
            self.container_values_mut_dyn()
                .expect("backend returned a container counter without a container registry")
                .register_type::<C>(counter, |_state, old, new| std::cmp::min(old, new));
        } else {
            assert!(
                !self.supports_containers(),
                "backend advertises container support but does not route register_container_ty"
            );
        }
    }

    fn get_container_value<C: ContainerValue>(&mut self, val: C) -> Value {
        if let Some(bridge) = self.as_any_mut().downcast_mut::<egglog_bridge::EGraph>() {
            bridge.get_container_value::<C>(val)
        } else {
            panic!("get_container_value is only supported on the reference bridge backend")
        }
    }
}

// ---------------------------------------------------------------------------
// `RuleBuilderOps` — mirrors `egglog_bridge::RuleBuilder`
// ---------------------------------------------------------------------------

/// Operations on an in-progress rule. Mirrors the public surface of
/// `egglog_bridge::RuleBuilder`: the reference impl is a thin passthrough; a
/// custom backend accumulates these calls into its own IR and finalizes on
/// [`RuleBuilderOps::build`].
pub trait RuleBuilderOps {
    /// Bind a new variable of the given type.
    fn new_var(&mut self, ty: ColumnTy) -> QueryEntry;

    /// Bind a new variable of the given type with a display name.
    fn new_var_named(&mut self, ty: ColumnTy, name: &str) -> QueryEntry;

    /// The base-value registry, for building typed constants during rule
    /// construction. (Replaces reaching through the concrete backend.)
    fn base_values(&self) -> &BaseValues;

    /// Add a table body atom. The final entry is the function's return value.
    ///
    /// `is_subsumed` filters on the row's subsumption bit: `Some(false)` matches
    /// only live rows, `Some(true)` matches only subsumed rows, and `None`
    /// matches both.
    fn query_table(
        &mut self,
        func: FunctionId,
        entries: &[QueryEntry],
        is_subsumed: Option<bool>,
    ) -> Result<()>;

    /// Add a primitive body atom. The final entry is the return value.
    fn query_prim(
        &mut self,
        func: ExternalFunctionId,
        entries: &[QueryEntry],
        ret_ty: ColumnTy,
    ) -> Result<()>;

    /// Call an external function in the RHS, panicking with `panic_msg` (built
    /// lazily) on failure. Returns the result variable.
    fn call_external_func(
        &mut self,
        func: ExternalFunctionId,
        args: &[QueryEntry],
        ret_ty: ColumnTy,
        panic_msg: PanicMsg,
    ) -> QueryEntry;

    /// RHS: look up `func(entries)` with the function's configured default on
    /// miss.
    ///
    /// Constructor lookup-or-insert must consult the current function table,
    /// including subsumed rows and previously staged constructor creations that
    /// are visible to the same RHS evaluation, before minting a fresh id.
    fn lookup(
        &mut self,
        func: FunctionId,
        entries: &[QueryEntry],
        panic_msg: PanicMsg,
    ) -> QueryEntry;

    /// RHS: subsume the row keyed by `entries` in `func`.
    ///
    /// Subsumption hides the row from ordinary `Some(false)` body matches but
    /// keeps it as the current row for `lookup`, `set`, and
    /// `query_table(..., None)`. Subsumption is flushed after removes and sets
    /// from the same bounded iteration.
    fn subsume(&mut self, func: FunctionId, entries: &[QueryEntry]) -> Result<()>;

    /// RHS: set `func(entries[..n-1])` to `entries[n-1]`.
    ///
    /// For function tables, this stages a candidate output value for the input
    /// key. On conflict it is merged with the current retained value using the
    /// configured [`MergeFn`], where `old` is the retained value and `new` is this
    /// incoming value. A `set` of a currently subsumed key merges with the
    /// subsumed row and does not by itself make the row live again.
    fn set(&mut self, func: FunctionId, entries: &[QueryEntry]);

    /// RHS: remove the row keyed by `entries` from `func`.
    ///
    /// Removes the keyed row from the same logical table state that `set` and
    /// `lookup` observe, including any subsumed row with that key. Removes are
    /// flushed before sets from the same bounded iteration.
    fn remove(&mut self, func: FunctionId, entries: &[QueryEntry]);

    /// RHS: union two values in the union-find.
    fn union(&mut self, l: QueryEntry, r: QueryEntry);

    /// RHS: panic with the given message.
    fn panic(&mut self, message: String);

    /// Register a deferred-panic external function on the backend and return
    /// its id (used, e.g., to bake a panic id into a wrapped function).
    fn new_panic(&mut self, message: String) -> ExternalFunctionId;

    /// Skip tree-decomposition during query planning for this rule
    /// (`:no-decomp`). Default no-op for backends that don't decompose.
    fn set_no_decomp(&mut self, _no_decomp: bool) {}

    /// Finalize the rule, returning its [`RuleId`].
    fn build(self: Box<Self>) -> Result<RuleId>;

    // -- optional: bridge-only escape hatch ---------------------------------

    /// The underlying backend as `&dyn Any` during rule building, for
    /// bridge-only features such as `unstable-fn`'s `TableAction` capture.
    /// Returns `None` on backends that do not expose it.
    fn backend_any(&self) -> Option<&dyn std::any::Any> {
        None
    }
}
