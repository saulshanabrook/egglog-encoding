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
//! register and run rules ([`Backend::add_rule`] / [`Backend::run_rules`]), read
//! tables back ([`Backend::for_each_while_dyn`] / [`Backend::table_size`]),
//! canonicalize ids ([`Backend::get_canon_repr`]), reach the value registries
//! ([`Backend::base_values`] / [`Backend::container_values`]), and register
//! primitives ([`Backend::register_external_func`]).
//!
//! Rules cross the backend boundary as a complete [`RuleSpec`]. This lets each
//! backend lower or retain the shared logical rule without replaying a callback
//! builder API or reconstructing an equivalent IR.
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
//! Subsumption is semantically a bit on a row, not a separate table. Body atoms
//! using [`ReadMode::Live`] see only live rows, [`ReadMode::All`] sees live and
//! subsumed rows, and [`ReadMode::Subsumed`] sees only subsumed rows. A subsumed
//! row remains the current row for lookup and merge purposes, so a later lookup
//! or `set` for the same key must find/merge with that row without making it
//! live again unless an explicit backend operation says otherwise.
//!
//! ## Advanced features are optional
//!
//! Capabilities that not every backend can offer — the seminaive-safe
//! [`ActionRegistry`] ([`Backend::action_registry`]) and container sorts — are
//! exposed as methods with **default** bodies. An implementer overrides only
//! what it supports; the frontend gates on the returned capability.
//!
//! ## Ergonomic sugar
//!
//! The object-safe [`Backend`] methods take erased closures (`&mut dyn FnMut(..)`)
//! and carry a `_dyn` suffix. Generic, ergonomic wrappers ([`BackendExt::for_each`],
//! [`BackendExt::with_execution_state`], …) live on the [`BackendExt`] extension
//! trait (a blanket impl over every `Backend`), so call sites read naturally —
//! import `BackendExt` to use them.
//!
//! ## Relationship to `egglog-bridge`
//!
//! This crate depends on `egglog-bridge` and re-exports its vocabulary types
//! ([`FunctionConfig`], [`MergeFn`], [`ColumnTy`], [`Value`], …) so an
//! implementer imports them from here. It also provides the reference
//! `impl Backend for egglog_bridge::EGraph` (see `backend_impl`).

use std::any::{Any, TypeId};
use std::sync::{Arc, RwLock};

use anyhow::Result;

mod backend_impl;

// ---------------------------------------------------------------------------
// Re-exports: the shared vocabulary a backend implementer works with.
// ---------------------------------------------------------------------------

pub use egglog_bridge::{
    ActionRegistry, ColumnTy, DefaultVal, FunctionConfig, FunctionId, MergeAction, MergeFn, RuleId,
    ScanEntry,
};
pub use egglog_core_relations::{
    BaseValue, BaseValueId, BaseValues, ContainerValue, ContainerValues, CounterId, ExecutionState,
    ExternalFunction, ExternalFunctionId, Value,
};
pub use egglog_reports::{IterationReport, PreMergeTiming, ReportLevel};

/// Which subsumption view a table atom reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ReadMode {
    Live,
    Subsumed,
    All,
}

impl ReadMode {
    pub(crate) fn is_subsumed(self) -> Option<bool> {
        match self {
            Self::Live => Some(false),
            Self::Subsumed => Some(true),
            Self::All => None,
        }
    }
}

/// A typed variable in a backend rule.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RuleVar {
    pub id: u32,
    pub name: Box<str>,
    pub ty: ColumnTy,
}

/// A typed constant in a backend rule.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RuleValue {
    pub value: Value,
    pub ty: ColumnTy,
}

/// A call in a rule body.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RuleBodyCall {
    Table {
        id: FunctionId,
        read: ReadMode,
    },
    Primitive {
        id: ExternalFunctionId,
        name: Box<str>,
        output: ColumnTy,
    },
}

/// A call in a rule action stream.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RuleActionCall {
    Table {
        id: FunctionId,
        name: Box<str>,
    },
    Primitive {
        id: ExternalFunctionId,
        name: Box<str>,
        output: ColumnTy,
    },
}

pub type BackendCoreRule =
    egglog_ast::core::GenericCoreRule<RuleBodyCall, RuleActionCall, RuleVar, RuleValue>;

/// A complete logical rule supplied to a backend.
#[derive(Clone, Debug)]
pub struct RuleSpec {
    pub name: String,
    pub seminaive: bool,
    pub no_decomp: bool,
    pub core: BackendCoreRule,
}

/// One bounded invocation of a logical ruleset.
#[derive(Clone, Copy, Debug)]
pub struct RuleSetRun<'a> {
    pub name: Option<&'a str>,
    pub rules: &'a [RuleId],
}

/// Backend-selected policy for reconciling two ids that rebuild to the same
/// container value. The container type is supplied separately to
/// [`Backend::container_merge_fn`], so a backend may choose a different policy
/// for each registered [`ContainerValue`] type.
pub type ContainerMergeFn =
    Arc<dyn for<'a> Fn(&mut ExecutionState<'a>, Value, Value) -> Value + Send + Sync>;

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

    /// The id that the next [`Backend::add_table`] call will assign.
    ///
    /// Merge action blocks use this to write back into the table being
    /// declared. The caller must invoke `add_table` before registering any
    /// other table.
    fn peek_next_function_id(&self) -> FunctionId;

    /// Number of rows currently in the given function's table.
    fn table_size(&self, table: FunctionId) -> usize;

    /// Remove every row from the given function's table.
    fn clear_table(&mut self, func: FunctionId);

    // -- iteration (object-safe; see `for_each` / `for_each_while` sugar) ----

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

    /// Lookup one function row by its key, returning keys followed by every
    /// output column. Subsumed rows remain visible to this direct lookup.
    fn lookup_row(&self, func: FunctionId, key: &[Value]) -> Option<Vec<Value>>;

    /// Read the first output value for `key` without inserting a missing row.
    /// Subsumed rows remain lookup-visible.
    fn lookup_id(&self, func: FunctionId, key: &[Value]) -> Option<Value>;

    /// Allocate a fresh counter for container-value ids, for backends that can
    /// execute container primitives without the bridge.
    fn new_container_id_counter(&mut self) -> Option<CounterId> {
        None
    }

    /// Select the merge policy for a registered container type. Backends that
    /// advertise container support outside the reference bridge must provide
    /// this alongside a container registry and id counter.
    fn container_merge_fn(&self, _container_type: TypeId) -> Option<ContainerMergeFn> {
        None
    }

    // -- execution state (object-safe; see `with_execution_state` sugar) -----

    /// Run `f` against a fresh execution state and return whether it staged any
    /// mutation. Object-safe form; prefer
    /// [`BackendExt::with_execution_state_tracked`].
    fn with_execution_state_tracked_dyn(&self, f: &mut dyn FnMut(&mut ExecutionState<'_>)) -> bool;

    // -- rule management ----------------------------------------------------

    /// Register a complete logical rule.
    fn add_rule(&mut self, rule: RuleSpec) -> Result<RuleId>;

    /// Drop a registered rule.
    fn free_rule(&mut self, id: RuleId);

    /// Run one bounded iteration of the given rule set.
    ///
    /// Implementations should evaluate rule bodies against a stable read view
    /// for this iteration and stage RHS effects until the rule firing is
    /// applied. The externally visible behavior must match the rule execution
    /// contract in the crate docs, especially for function `set`/`merge`,
    /// `remove`, `subsume`, and constructor lookup-or-insert effects.
    fn run_rules(&mut self, run: RuleSetRun<'_>) -> Result<IterationReport>;

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

    /// Register a deferred-panic primitive and return its id.
    ///
    /// The registered function must ignore any arguments supplied by its call
    /// site, trigger the backend's normal early-stop path, and make the next
    /// [`Backend::run_rules`] return the provided message as an error.
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

    /// The seminaive-safe [`ActionRegistry`] used by registry-backed
    /// primitives, when this backend provides one.
    ///
    /// Backends without an in-memory action registry return `None`; the
    /// frontend routes unsupported primitive calls through
    /// [`Backend::new_panic`] so execution fails through the backend's normal
    /// error channel.
    fn action_registry(&self) -> Option<&Arc<RwLock<ActionRegistry>>> {
        None
    }

    /// Whether this backend supports `Vec` / `Set` / `Map` / `MultiSet`
    /// container sorts.
    fn supports_containers(&self) -> bool {
        false
    }

    /// Whether this backend needs the frontend's term-encoding pipeline to be
    /// enabled. A backend without a native union-find, such as the experimental
    /// Differential Dataflow backend, relies on term encoding to lower
    /// congruence and rebuild to ordinary rules over `@uf` tables. Native mode
    /// has no correct representation for those unions, so the frontend refuses
    /// to run such a backend unless the e-graph was built with term encoding
    /// (via `EGraph::with_term_encoding`).
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
/// `register_container_ty` on a backend.
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

    /// Register a container-value type `C`.
    ///
    /// Container registration wires the container into the backend's rebuild
    /// loop, which requires backend-internal state. The reference bridge handles
    /// this directly; another container-capable backend supplies its registry,
    /// id counter, and per-container merge policy through the capability methods
    /// on [`Backend`]. Registration is a no-op for backends that do not advertise
    /// container support.
    fn register_container_ty<C: ContainerValue>(&mut self);
}

impl<B: Backend + ?Sized> BackendExt for B {
    fn for_each(&self, table: FunctionId, mut f: impl for<'r> FnMut(ScanEntry<'r>)) {
        self.for_each_while_dyn(table, &mut |row| {
            f(row);
            true
        });
    }

    fn for_each_while(&self, table: FunctionId, mut f: impl for<'r> FnMut(ScanEntry<'r>) -> bool) {
        self.for_each_while_dyn(table, &mut f);
    }

    fn with_execution_state<R>(&self, f: impl FnOnce(&mut ExecutionState<'_>) -> R) -> R {
        self.with_execution_state_tracked(f).0
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

    fn register_container_ty<C: ContainerValue>(&mut self) {
        if let Some(bridge) = self.as_any_mut().downcast_mut::<egglog_bridge::EGraph>() {
            bridge.register_container_ty::<C>();
        } else if self.supports_containers() {
            let counter = self
                .new_container_id_counter()
                .expect("backend advertises container support without an id counter");
            let merge_fn = self
                .container_merge_fn(TypeId::of::<C>())
                .expect("backend advertises container support without merge semantics");
            self.container_values_mut_dyn()
                .expect("backend returned a container counter without a container registry")
                .register_type::<C>(counter, move |state, old, new| merge_fn(state, old, new));
        }
    }
}
