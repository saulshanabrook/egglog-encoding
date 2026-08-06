use std::hash::Hasher;

use crate::Context;
use crate::constraint::ResolvedBindingScope;
use crate::proofs::proof_container_rebuild::register_container_rebuild_from_spec;
use crate::{
    core::{CoreActionContext, CoreRule, GenericActionsExt, QueryConstraints, ResolvedCall},
    *,
};
use ast::{
    MappedExprExt, ResolvedAction, ResolvedExpr, ResolvedFact, ResolvedRule, ResolvedVar,
    ResolvedVarBinding, Rule, RuleEvalMode,
};
use core_relations::ExternalFunction;
use egglog_ast::generic_ast::GenericAction;
use egglog_bridge::ActionRegistry;
use enum_map::EnumMap;
use std::sync::{Arc, RwLock};

// `ExternalFunction` wrapper for `PurePrim`. Holds the primitive
// directly so the dispatch chain `external_funcs[id].invoke(...)` →
// `T::apply(...)` is just one vtable hop plus a direct call — no
// closure indirection that defeats inlining.
#[derive(Clone)]
struct PurePrimWrapper<T> {
    prim: T,
    /// The call-site [`Context`] this wrapper stamps onto the
    /// `PureState` before dispatching. `register_per_context` commits
    /// one wrapper per valid `Context` for the trait, so the
    /// typechecker's pick at each call site is encoded directly here.
    ctx: Context,
}

impl<T: PurePrim + Clone> ExternalFunction for PurePrimWrapper<T> {
    fn invoke(&self, exec_state: &mut ExecutionState, args: &[Value]) -> Option<Value> {
        self.prim.apply(PureState::wrap(exec_state, self.ctx), args)
    }
}

// `ExternalFunction` wrapper for primitives that need the
// `ActionRegistry` (`ReadPrim`, `WritePrim`, `FullPrim`). One generic
// over the `Wrap` strategy that knows how to construct the right
// state type and dispatch to the primitive's `apply`.
#[derive(Clone)]
struct RegistryPrimWrapper<T, S> {
    prim: T,
    registry: Arc<RwLock<ActionRegistry>>,
    /// Stamped onto the state wrapper.
    ctx: Context,
    _wrap: std::marker::PhantomData<fn() -> S>,
}

trait RegistryWrap<T>: Clone + Send + Sync {
    fn invoke(
        prim: &T,
        exec_state: &mut ExecutionState,
        ctx: Context,
        args: &[Value],
        registry: &ActionRegistry,
    ) -> Option<Value>;
}

#[derive(Clone)]
struct WrapRead;
impl<T: ReadPrim> RegistryWrap<T> for WrapRead {
    #[inline]
    fn invoke(
        prim: &T,
        exec_state: &mut ExecutionState,
        ctx: Context,
        args: &[Value],
        registry: &ActionRegistry,
    ) -> Option<Value> {
        prim.apply(ReadState::wrap(exec_state, registry, ctx), args)
    }
}
#[derive(Clone)]
struct WrapWrite;
impl<T: WritePrim> RegistryWrap<T> for WrapWrite {
    #[inline]
    fn invoke(
        prim: &T,
        exec_state: &mut ExecutionState,
        ctx: Context,
        args: &[Value],
        registry: &ActionRegistry,
    ) -> Option<Value> {
        prim.apply(WriteState::wrap(exec_state, registry, ctx), args)
    }
}
#[derive(Clone)]
struct WrapFull;
impl<T: FullPrim> RegistryWrap<T> for WrapFull {
    #[inline]
    fn invoke(
        prim: &T,
        exec_state: &mut ExecutionState,
        ctx: Context,
        args: &[Value],
        registry: &ActionRegistry,
    ) -> Option<Value> {
        prim.apply(FullState::wrap(exec_state, registry, ctx), args)
    }
}

impl<T: Clone + Send + Sync + 'static, S: RegistryWrap<T> + 'static> ExternalFunction
    for RegistryPrimWrapper<T, S>
{
    fn invoke(&self, exec_state: &mut ExecutionState, args: &[Value]) -> Option<Value> {
        let registry = self.registry.read().unwrap();
        S::invoke(&self.prim, exec_state, self.ctx, args, &registry)
    }
}

/// Deterministic frontend identity of one declared function table.
///
/// This is deliberately independent of backend function handles. Two
/// declarations remain distinct even when their names and schemas are equal.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunctionRegistrationId(u32);

impl FunctionRegistrationId {
    pub(crate) const fn new(ordinal: u32) -> Self {
        Self(ordinal)
    }

    pub const fn ordinal(self) -> u32 {
        self.0
    }
}

/// Deterministic frontend identity of one declared occurrence index.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IndexRegistrationId(u32);

impl IndexRegistrationId {
    pub(crate) const fn new(ordinal: u32) -> Self {
        Self(ordinal)
    }

    pub const fn ordinal(self) -> u32 {
        self.0
    }
}

/// Exact callable selected by type resolution.
///
/// Function and index registrations occupy separate nominal domains so an
/// index can never be mistaken for a same-shaped function table.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum CallableIdentity {
    Function(FunctionRegistrationId),
    Index(IndexRegistrationId),
}

#[derive(Clone, Debug)]
pub struct FuncType {
    pub identity: CallableIdentity,
    /// Diagnostic/display name. Resolution semantics use [`Self::identity`].
    pub name: String,
    pub subtype: FunctionSubtype,
    pub input: Vec<ArcSort>,
    /// The output (value-column) sorts, primary first. A tuple-output function has more than one;
    /// ordinary functions have exactly one. Always non-empty.
    pub outputs: Vec<ArcSort>,
}

impl FuncType {
    /// The primary (first) output sort.
    pub fn output(&self) -> &ArcSort {
        &self.outputs[0]
    }

    /// The number of output (value) columns.
    pub fn num_outputs(&self) -> usize {
        self.outputs.len()
    }

    /// Whether this function has more than one output column.
    pub fn is_tuple_output(&self) -> bool {
        self.outputs.len() > 1
    }
}

impl PartialEq for FuncType {
    fn eq(&self, other: &Self) -> bool {
        self.identity == other.identity
    }
}

impl Eq for FuncType {}

impl Hash for FuncType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.identity.hash(state);
    }
}

/// Validators take a termdag and arguments (as TermIds) and return
/// a newly computed TermId if the primitive application is valid,
/// or None if it is invalid.
pub type PrimitiveValidator = Arc<dyn Fn(&mut TermDag, &[TermId]) -> Option<TermId> + Send + Sync>;

/// Frontend-owned semantic authority for one primitive registration.
///
/// This is recorded at the registration site.  A compiler must never recover
/// one of these meanings from the primitive's display name, type signature,
/// registration order, or the schema of a nearby function.  Proof view names
/// are retained here only as exact unresolved references; snapshot capture
/// resolves them to nominal function identities before they become portable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum PrimitiveAuthority {
    Native(NativePrimitive),
    NativeScalar(NativeScalarPrimitive),
    GetFresh,
    SetIfEmpty {
        target_view: String,
    },
    ViewColumn {
        target_view: String,
        /// Zero-based value-column index, excluding key columns.
        value_column: usize,
    },
    /// The exact polymorphic value-equality registration used when core-rule
    /// canonicalization replaces duplicate resolved variables.
    ValueEq,
    /// An ordinary callback whose semantics are unavailable to a standalone
    /// compiler.  Its runtime token and context mask remain fully usable by
    /// normal backends, but standalone preflight must reject it if reached.
    Opaque,
}

/// Stable identity of one primitive registration inside a [`TypeInfo`].
///
/// This is frontend identity, not a backend callback token.  Independent
/// frontends that perform the same registrations in the same deterministic
/// order assign the same IDs, while two registrations remain distinct even
/// when their names and signatures are identical.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct PrimitiveRegistrationId(u32);

impl PrimitiveRegistrationId {
    #[allow(dead_code)]
    pub(crate) const fn ordinal(self) -> u32 {
        self.0
    }
}

#[derive(Clone)]
pub struct PrimitiveWithId {
    pub(crate) primitive: Arc<dyn Primitive>,
    pub(crate) validator: Option<PrimitiveValidator>,
    pub(crate) registration_id: PrimitiveRegistrationId,
    pub(crate) authority: PrimitiveAuthority,
    /// Runtime entrypoints for the contexts this primitive is valid in.
    /// The primitive definition is stored once, while each context keeps
    /// its own backend id so higher-order dispatch can still recover the
    /// application context at runtime.
    pub(crate) context_ids: EnumMap<Context, Option<ExternalFunctionId>>,
}

impl PrimitiveWithId {
    /// Takes the full signature of a primitive (both input and output types).
    /// Returns whether the primitive is compatible with this signature.
    pub fn accept(&self, tys: &[Arc<dyn Sort>], typeinfo: &TypeInfo) -> bool {
        let mut constraints = vec![];
        let lits: Vec<_> = (0..tys.len())
            .map(|i| AtomTerm::Literal(Span::Panic, Literal::Int(i as i64)))
            .collect();
        for (lit, ty) in lits.iter().zip(tys.iter()) {
            constraints.push(constraint::assign(lit.clone(), ty.clone()))
        }
        constraints.extend(
            self.primitive
                .get_type_constraints(&Span::Panic)
                .get(&lits, typeinfo),
        );
        let problem = Problem {
            constraints,
            range: HashSet::default(),
        };
        problem.solve(|sort| sort.name()).is_ok()
    }

    /// Returns whether this primitive has a runtime entrypoint for `context`.
    pub fn is_valid_in_context(&self, context: Context) -> bool {
        self.context_ids[context].is_some()
    }

    /// Return the semantic authority recorded by the registration site.
    pub(crate) fn authority(&self) -> &PrimitiveAuthority {
        &self.authority
    }

    /// Return this registration's frontend-owned identity.
    pub(crate) fn registration_id(&self) -> PrimitiveRegistrationId {
        self.registration_id
    }
}

impl Debug for PrimitiveWithId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Prim({})", self.primitive.name())
    }
}

/// Stores resolved typechecking information.
#[derive(Clone, Default)]
pub struct TypeInfo {
    mksorts: HashMap<String, MkSort>,
    // TODO(yz): I want to get rid of this as now we have user-defined primitives and constraint based type checking
    reserved_primitives: HashSet<&'static str>,
    pub(crate) sorts: HashMap<String, Arc<dyn Sort>>,
    primitives: HashMap<String, Vec<PrimitiveWithId>>,
    next_primitive_registration_id: u32,
    value_eq_registration_id: Option<PrimitiveRegistrationId>,
    func_types: HashMap<String, FuncType>,
    pub(crate) global_sorts: HashMap<String, ArcSort>,
    global_function_ids: HashMap<String, FunctionRegistrationId>,
    /// Every exact global registration produced by this frontend stream,
    /// including registrations whose diagnostic names have left scope after a
    /// `pop`. Resolved historical commands keep those identities, so proof
    /// admission must not fall back to their now-unbound names.
    global_function_identity_history: HashSet<FunctionRegistrationId>,
    /// Sorts that do not allow union (e.g., from `:no-union` sorts or relations).
    pub(crate) non_unionable_sorts: HashSet<String>,
    /// Declared indexes, by the name their atoms are written with.
    pub(crate) indexes: HashMap<String, IndexInfo>,
}

/// A declared index: a read-only relation over the rows of `function`, holding
/// each value appearing in `any_of` followed by the whole row.
#[derive(Clone, Debug)]
pub struct IndexInfo {
    #[allow(dead_code)] // consumed by the pending pure nominal snapshot mapper
    pub identity: IndexRegistrationId,
    /// Exact function table read by this index.
    #[allow(dead_code)] // consumed by the pending pure nominal snapshot mapper
    pub target: FunctionRegistrationId,
    /// Diagnostic/display name of [`Self::target`].
    pub function: String,
    /// Column indices of `function`'s row (its inputs then its outputs), read
    /// disjunctively.
    pub any_of: Vec<usize>,
}

/// Built-in polymorphic value equality.
///
/// Keeping this definition here lets its registration site attach
/// [`PrimitiveAuthority::ValueEq`] directly, instead of asking a later core
/// pass to guess which overload named `value-eq` was intended.
#[derive(Clone)]
struct ValueEqPrimitive;

impl Primitive for ValueEqPrimitive {
    fn name(&self) -> &str {
        "value-eq"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        AllEqualTypeConstraint::new(self.name(), span.clone())
            .with_exact_length(3)
            .with_output_sort(UnitSort.to_arcsort())
            .into_box()
    }
}

impl PurePrim for ValueEqPrimitive {
    fn apply<'a, 'db>(&self, state: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
        let [left, right] = args else {
            return None;
        };
        (left == right).then(|| state.base_values().get(()))
    }
}

// These methods need to be on the `EGraph` in order to
// register sorts and primitives with the backend.
impl EGraph {
    /// Add a user-defined sort to the e-graph.
    ///
    /// Also look at [`prelude::add_base_sort`] for a convenience method for adding user-defined sorts
    pub fn add_sort<S: Sort + 'static>(&mut self, sort: S, span: Span) -> Result<(), TypeError> {
        self.add_arcsort(Arc::new(sort), span)
    }

    /// Declare a sort. This corresponds to the `sort` keyword in egglog.
    /// It can either declares a new [`EqSort`] if `presort_and_args` is not provided,
    /// or an instantiation of a presort (e.g., containers like `Vec`).
    pub fn declare_sort(
        &mut self,
        name: impl Into<String>,
        presort_and_args: &Option<(String, Vec<Expr>)>,
        span: Span,
    ) -> Result<(), TypeError> {
        let name = name.into();
        if self.type_info.func_types.contains_key(&name) {
            return Err(TypeError::FunctionAlreadyBound(name, span));
        }

        let sort = match presort_and_args {
            None => Arc::new(EqSort { name }),
            Some((presort, args)) => {
                if let Some(mksort) = self.type_info.mksorts.get(presort) {
                    mksort(&mut self.type_info, name, args)?
                } else {
                    return Err(TypeError::PresortNotFound(presort.clone(), span));
                }
            }
        };

        self.add_arcsort(sort, span)
    }

    /// Add a user-defined sort to the e-graph.
    pub fn add_arcsort(&mut self, sort: ArcSort, span: Span) -> Result<(), TypeError> {
        self.backend.register_sort(&sort);

        let name = sort.name();
        match self.type_info.sorts.entry(name.to_owned()) {
            HEntry::Occupied(_) => Err(TypeError::SortAlreadyBound(name.to_owned(), span)),
            HEntry::Vacant(e) => {
                e.insert(sort.clone());
                // A sort's primitives already reach the term-encoding typechecker
                // through its OWN `add_arcsort` when it typechecks the sort
                // command, so don't propagate them again from here (that would
                // double-register and make primitive resolution ambiguous).
                // Detach the typechecker while the sort registers, so only direct
                // `add_*_primitive` calls propagate to it.
                let saved = self.proof_state.original_typechecking.take();
                sort.register_primitives(self);
                self.proof_state.original_typechecking = saved;
                Ok(())
            }
        }
    }

    /// Register a [`PurePrim`]. Pass `None` for the validator if not
    /// using the proof checker.
    ///
    /// Pick the trait whose state wrapper matches the body's needs:
    /// [`PurePrim`] for pure ops, [`WritePrim`] for writes,
    /// [`ReadPrim`] for table reads, [`FullPrim`] for both. The Rust
    /// type checker enforces the body only uses methods the chosen
    /// state allows.
    pub fn add_pure_primitive<T>(&mut self, x: T, validator: Option<PrimitiveValidator>)
    where
        T: PurePrim + Clone,
    {
        self.register_per_context(
            x,
            validator,
            PrimitiveAuthority::Opaque,
            PureState::valid_contexts(),
            |backend, x, ctx| {
                backend.register_external_func(Box::new(PurePrimWrapper { prim: x, ctx }))
            },
        );
    }

    /// Register the one primitive whose authority core canonicalization uses
    /// for resolved value equality.
    ///
    /// The standard frontend calls this at the built-in registration site.
    /// Ordinary user primitives, including same-name/same-schema decoys, stay
    /// opaque and cannot replace this authority.
    pub(crate) fn add_value_eq_primitive(&mut self) {
        self.register_per_context(
            ValueEqPrimitive,
            None,
            PrimitiveAuthority::ValueEq,
            PureState::valid_contexts(),
            |backend, x, ctx| {
                backend.register_external_func(Box::new(PurePrimWrapper { prim: x, ctx }))
            },
        );
    }

    /// Register a pure primitive whose runtime identity is meaningful to a
    /// native backend. The primitive definition retains frontend typechecking
    /// and proof validation; the backend receives only the shared semantic tag
    /// and supplies the context-specific runtime token.
    pub(crate) fn add_native_primitive<T>(
        &mut self,
        x: T,
        validator: Option<PrimitiveValidator>,
        native: NativePrimitive,
    ) where
        T: Primitive + Clone,
    {
        self.register_per_context(
            x,
            validator,
            PrimitiveAuthority::Native(native),
            PureState::valid_contexts(),
            move |backend, _x, _ctx| backend.register_native_primitive(native),
        );
    }

    /// Register a pure primitive whose decoded scalar semantics may be lowered
    /// by a native backend. The canonical per-context wrapper is still passed
    /// across the SPI, so every backend that keeps the default method executes
    /// the exact same implementation as an ordinary pure primitive.
    pub(crate) fn add_native_scalar_primitive<T>(
        &mut self,
        x: T,
        validator: Option<PrimitiveValidator>,
        native: NativeScalarPrimitive,
    ) where
        T: PurePrim + Clone,
    {
        self.register_per_context(
            x,
            validator,
            PrimitiveAuthority::NativeScalar(native),
            PureState::valid_contexts(),
            move |backend, x, ctx| {
                backend.register_native_scalar_primitive(
                    native,
                    Box::new(PurePrimWrapper { prim: x, ctx }),
                )
            },
        );
    }

    /// Register a [`WritePrim`]. Pass `None` for the validator if not
    /// using the proof checker.
    pub fn add_write_primitive<T>(&mut self, x: T, validator: Option<PrimitiveValidator>)
    where
        T: WritePrim + Clone,
    {
        self.register_registry_primitive::<T, WrapWrite>(
            x,
            validator,
            PrimitiveAuthority::Opaque,
            WriteState::valid_contexts(),
        );
    }

    /// Register a [`ReadPrim`]. Pass `None` for the validator if not
    /// using the proof checker.
    pub fn add_read_primitive<T>(&mut self, x: T, validator: Option<PrimitiveValidator>)
    where
        T: ReadPrim + Clone,
    {
        self.register_registry_primitive::<T, WrapRead>(
            x,
            validator,
            PrimitiveAuthority::Opaque,
            ReadState::valid_contexts(),
        );
    }

    /// Register a [`FullPrim`]. Pass `None` for the validator if not
    /// using the proof checker.
    pub fn add_full_primitive<T>(&mut self, x: T, validator: Option<PrimitiveValidator>)
    where
        T: FullPrim + Clone,
    {
        self.register_registry_primitive::<T, WrapFull>(
            x,
            validator,
            PrimitiveAuthority::Opaque,
            FullState::valid_contexts(),
        );
    }

    fn register_registry_primitive<T, S>(
        &mut self,
        x: T,
        validator: Option<PrimitiveValidator>,
        authority: PrimitiveAuthority,
        valid_ctxs: &[Context],
    ) where
        T: Primitive + Clone,
        S: RegistryWrap<T> + 'static,
    {
        self.register_per_context(x, validator, authority, valid_ctxs, |backend, x, ctx| {
            if let Some(registry) = backend.action_registry().cloned() {
                backend.register_external_func(Box::new(RegistryPrimWrapper::<T, S> {
                    prim: x,
                    registry,
                    ctx,
                    _wrap: std::marker::PhantomData,
                }))
            } else {
                let name = x.name().to_owned();
                backend.new_panic(format!(
                    "primitive {name} in {ctx:?} context requires a backend action registry"
                ))
            }
        });
    }

    /// Register a term-encoding op primitive whose runtime entrypoint the backend
    /// itself mints. `prim` supplies only the type constraints (its body is never
    /// invoked); `make_id` asks each backend on the typechecker chain for the
    /// [`ExternalFunctionId`] that services this op against that backend's own
    /// storage. Unlike [`Self::register_registry_primitive`], this works on
    /// backends without an action registry.
    pub(crate) fn add_backend_op_primitive<T, F>(
        &mut self,
        prim: T,
        authority: PrimitiveAuthority,
        valid_ctxs: &[Context],
        mut make_id: F,
    ) where
        T: Primitive + Clone,
        F: FnMut(&mut dyn Backend, Context) -> ExternalFunctionId,
    {
        self.register_per_context(
            prim,
            None,
            authority,
            valid_ctxs,
            move |backend, _x, ctx| make_id(backend, ctx),
        );
    }

    /// Shared registration engine. Stores one primitive definition, plus
    /// one runtime id per valid [`Context`]. Each wrapper carries its
    /// specific context stamped onto the state wrapper at invoke time.
    ///
    /// The typechecker filters by the context-id mask at each call site;
    /// an `unstable-fn` value built around the primitive bakes *all*
    /// signature-matching context ids, and `FunctionContainer::apply`
    /// picks the one whose context matches the application ctx — so
    /// values flow freely across contexts.
    fn register_per_context<T, F>(
        &mut self,
        x: T,
        validator: Option<PrimitiveValidator>,
        authority: PrimitiveAuthority,
        valid_ctxs: &[Context],
        mut build_wrapper: F,
    ) where
        T: Primitive + Clone,
        F: FnMut(&mut dyn Backend, T, Context) -> ExternalFunctionId,
    {
        // Register on this e-graph AND every term-encoding typechecker down the
        // chain. Each typechecker is a separate e-graph that typechecks the
        // encoded program (see `typecheck_program`); a primitive added after
        // construction is otherwise unknown to it and reported as unbound. A
        // typechecker only typechecks and never evaluates, so the wrapper's
        // runtime state is irrelevant there, and — since both e-graphs register
        // the same built-ins during construction — a primitive added to both
        // gets the same `ExternalFunctionId`.
        let mut eg: &mut EGraph = self;
        loop {
            let primitive: Arc<dyn Primitive> = Arc::new(x.clone());
            let name = primitive.name().to_owned();
            let context_ids = EnumMap::from_fn(|ctx| {
                valid_ctxs.contains(&ctx).then(|| {
                    eg.backend
                        .register_primitive(x.clone(), ctx, &mut build_wrapper)
                })
            });
            let registration_id =
                PrimitiveRegistrationId(eg.type_info.next_primitive_registration_id);
            eg.type_info.next_primitive_registration_id = eg
                .type_info
                .next_primitive_registration_id
                .checked_add(1)
                .expect("primitive registration identity space exhausted");
            if authority == PrimitiveAuthority::ValueEq {
                assert!(
                    eg.type_info
                        .value_eq_registration_id
                        .replace(registration_id)
                        .is_none(),
                    "value-eq authority registered more than once in one frontend"
                );
            }
            eg.type_info
                .primitives
                .entry(name)
                .or_default()
                .push(PrimitiveWithId {
                    primitive,
                    validator: validator.clone(),
                    registration_id,
                    authority: authority.clone(),
                    context_ids,
                });
            match eg.proof_state.original_typechecking.as_deref_mut() {
                Some(next) => eg = next,
                None => break,
            }
        }
    }
}

impl EGraph {
    pub(crate) fn typecheck_program(
        &mut self,
        program: &Vec<NCommand>,
    ) -> Result<Vec<ResolvedNCommand>, TypeError> {
        let mut result = vec![];
        for command in program {
            result.push(self.typecheck_command(command)?);
        }
        Ok(result)
    }

    /// Validate an index declaration and register it as a read-only relation
    /// `(value, <row of `function`>)`, so its atoms resolve like any other.
    fn typecheck_index(
        &mut self,
        span: &Span,
        name: &str,
        function: &str,
        any_of: &[usize],
        identity: IndexRegistrationId,
    ) -> Result<GenericIndexResolution<ResolvedCall>, TypeError> {
        if self.type_info.func_types.contains_key(name) {
            return Err(TypeError::FunctionAlreadyBound(
                name.to_owned(),
                span.clone(),
            ));
        }
        // An index is a view over a function's table; it has no table of its own
        // for a second index to read.
        if self.type_info.indexes.contains_key(function) {
            return Err(TypeError::IndexOfIndex(
                name.to_owned(),
                function.to_owned(),
                span.clone(),
            ));
        }
        let ft = self
            .type_info
            .get_func_type(function)
            .cloned()
            .ok_or_else(|| TypeError::UnboundFunction(function.to_owned(), span.clone()))?;
        let CallableIdentity::Function(target) = ft.identity else {
            return Err(TypeError::IndexOfIndex(
                name.to_owned(),
                function.to_owned(),
                span.clone(),
            ));
        };
        // The indexable row is the function's inputs followed by its outputs.
        let row: Vec<ArcSort> = ft.input.iter().chain(ft.outputs.iter()).cloned().collect();
        if any_of.is_empty() {
            return Err(TypeError::EmptyIndex(name.to_owned(), span.clone()));
        }
        let mut value_sort: Option<ArcSort> = None;
        for &col in any_of {
            let sort = row.get(col).ok_or_else(|| {
                TypeError::IndexColumnOutOfRange(name.to_owned(), col, row.len(), span.clone())
            })?;
            match &value_sort {
                None => value_sort = Some(sort.clone()),
                Some(prev) if prev.name() == sort.name() => {}
                Some(prev) => {
                    return Err(TypeError::IndexColumnSortMismatch(
                        name.to_owned(),
                        prev.name().to_owned(),
                        sort.name().to_owned(),
                        span.clone(),
                    ));
                }
            }
        }
        let mut input = vec![value_sort.expect("any_of is non-empty")];
        input.extend(row);
        let unit = self.type_info.sorts.get("Unit").expect("Unit sort").clone();
        let index = FuncType {
            identity: CallableIdentity::Index(identity),
            name: name.to_owned(),
            subtype: FunctionSubtype::Custom,
            input,
            outputs: vec![unit],
        };
        self.type_info
            .func_types
            .insert(name.to_owned(), index.clone());
        self.type_info.indexes.insert(
            name.to_owned(),
            IndexInfo {
                identity,
                target,
                function: function.to_owned(),
                any_of: any_of.to_vec(),
            },
        );
        Ok(GenericIndexResolution {
            index: ResolvedCall::Func(index),
            target: ResolvedCall::Func(ft),
        })
    }

    fn typecheck_command(&mut self, command: &NCommand) -> Result<ResolvedNCommand, TypeError> {
        let symbol_gen = &mut self.parser.symbol_gen;

        let command: ResolvedNCommand = match command {
            NCommand::Function(fdecl) => {
                let resolved = self.type_info.typecheck_function(symbol_gen, fdecl)?;
                // An FD view (function carrying `term_constructor` with a tuple
                // `(eclass, proof)` output) gets a `set-if-empty` primitive (+ a
                // proof-column reader) so the encoding can canonicalize a term to
                // the view's e-class at insertion time. Registered here so it
                // survives re-parse of the desugared program.
                if resolved.term_constructor.is_some()
                    && let ResolvedCall::Func(ft) = &resolved.resolved_schema
                    && ft.outputs.len() >= 2
                {
                    let (name, input, outputs) =
                        (resolved.name.clone(), ft.input.clone(), ft.outputs.clone());
                    crate::proofs::proof_fresh::register_set_if_empty(self, &name, input, outputs);
                }
                // If this is a let binding, add it to global_sorts
                // This preserves bahavior for lets after desugaring
                if resolved.internal_let {
                    let output_sort = self.type_info.sorts.get(fdecl.schema.output()).unwrap();
                    self.type_info
                        .global_sorts
                        .insert(fdecl.name.clone(), output_sort.clone());
                    let ResolvedCall::Func(func) = &resolved.resolved_schema else {
                        unreachable!("an internal-let declaration must be a function")
                    };
                    let CallableIdentity::Function(function) = func.identity else {
                        unreachable!("an internal-let declaration cannot be an index")
                    };
                    // Proof instrumentation prints the removed-global function
                    // and typechecks that generated declaration again in a new
                    // catalog stream. Make future global references use this
                    // stream's exact declaration, not the pre-instrumentation
                    // raw ID retained in `global_function_ids`.
                    self.type_info
                        .global_function_ids
                        .insert(fdecl.name.clone(), function);
                    self.type_info
                        .global_function_identity_history
                        .insert(function);
                    // Term/proof encoding represents a source global by an
                    // internal-let constructor view whose explicit
                    // `term_constructor` link names the source binding. Record
                    // that source name against this stream's exact view
                    // registration; never fall back to the same-named term
                    // table, whose schema and meaning are different.
                    if let Some(source_global) = &resolved.term_constructor
                        && self.type_info.global_sorts.contains_key(source_global)
                    {
                        self.type_info
                            .global_function_ids
                            .insert(source_global.clone(), function);
                    }
                }
                ResolvedNCommand::Function(resolved)
            }
            NCommand::NormRule { rule } => ResolvedNCommand::NormRule {
                rule: self
                    .type_info
                    .typecheck_rule(symbol_gen, rule, self.seminaive)?,
            },
            NCommand::Sort {
                span,
                name,
                presort_and_args,
                uf,
                proof_func,
                container_rebuild,
                proof_constructors,
                unionable,
            } => {
                // Note this is bad since typechecking should be pure and idempotent
                // Otherwise typechecking the same program twice will fail
                self.declare_sort(name.clone(), presort_and_args, span.clone())?;
                // Mark as non-unionable if the sort declaration says so
                if !unionable {
                    self.type_info.non_unionable_sorts.insert(name.clone());
                }
                // Record this sort's UF / proof tables in proof_state (as
                // run_command also does) so the container rebuild registration
                // below can recover them — including this container's own proof
                // table, which has not run yet.
                if let Some((uf_ctor, _uf_index)) = uf {
                    self.proof_state
                        .uf_parent
                        .insert(name.clone(), uf_ctor.clone());
                    // The rebuild rules canonicalize a term in their action
                    // through these, derived from the sort's `@UF_<S>` table.
                    crate::proofs::proof_container_rebuild::register_uf_canon(
                        self,
                        name,
                        uf_ctor,
                        proof_func.is_some(),
                    );
                }
                if let Some(pf) = proof_func {
                    self.proof_state
                        .proof_func_parent
                        .insert(name.clone(), pf.clone());
                }
                // The Proof sort records the global proof constructors; restore
                // them into proof_state so container rebuild can recover them
                // (the `Proof` datatype name is this sort's own name).
                if let Some(pc) = proof_constructors {
                    let names = &mut self.proof_state.proof_names;
                    names.proof_datatype = name.clone();
                    names.congr_constructor = pc.congr.clone();
                    names.congr_all_constructor = pc.congr_all.clone();
                    names.eq_trans_constructor = pc.trans.clone();
                    names.eq_sym_constructor = pc.sym.clone();
                    names.container_normalize_constructor = pc.normalize.clone();
                }
                // A container sort under the term/proof encoding carries a spec
                // for its rebuild primitives; register them here so they are
                // available both during encoding and when the desugared program
                // is re-parsed.
                if let Some(spec) = container_rebuild {
                    register_container_rebuild_from_spec(self, name, spec);
                }
                ResolvedNCommand::Sort {
                    span: span.clone(),
                    name: name.clone(),
                    presort_and_args: presort_and_args.clone(),
                    uf: uf.clone(),
                    proof_func: proof_func.clone(),
                    container_rebuild: container_rebuild.clone(),
                    proof_constructors: proof_constructors.clone(),
                    unionable: *unionable,
                }
            }
            NCommand::CoreAction(action @ Action::Let(span, var, _)) => {
                let mut action = self.type_info.typecheck_standalone_action(
                    symbol_gen,
                    action,
                    &Default::default(),
                    Context::Full,
                )?;
                let function = symbol_gen.fresh_function_registration_id();
                self.ensure_global_name_prefix(span, var)?;
                let ResolvedAction::Let(_, resolved_var, _) = &mut action else {
                    unreachable!("typechecking an Action::Let should return ResolvedAction::Let")
                };
                resolved_var.binding = ResolvedVarBinding::Global { function };
                self.type_info
                    .global_sorts
                    .entry(resolved_var.name.clone())
                    .or_insert_with(|| resolved_var.sort.clone());
                self.type_info
                    .global_function_ids
                    .entry(resolved_var.name.clone())
                    .or_insert(function);
                self.type_info
                    .global_function_identity_history
                    .insert(function);
                ResolvedNCommand::CoreAction(action)
            }
            NCommand::CoreAction(action) => {
                ResolvedNCommand::CoreAction(self.type_info.typecheck_standalone_action(
                    symbol_gen,
                    action,
                    &Default::default(),
                    Context::Full,
                )?)
            }
            NCommand::CoreActions(actions) => {
                ResolvedNCommand::CoreActions(self.type_info.typecheck_standalone_actions(
                    symbol_gen,
                    actions,
                    &Default::default(),
                    Context::Full,
                )?)
            }
            NCommand::LetBegin(span, name, actions) => {
                let resolved = self.type_info.typecheck_standalone_actions(
                    symbol_gen,
                    actions,
                    &Default::default(),
                    Context::Full,
                )?;
                let function = symbol_gen.fresh_function_registration_id();
                self.ensure_global_name_prefix(span, name)?;
                // The parser guarantees a trailing expression; its type is the
                // global's.
                let Some(ResolvedAction::Expr(_, value)) = resolved.0.last() else {
                    unreachable!("(let _ (begin ...)) must end with an expression")
                };
                let sort = value.output_type();
                self.type_info
                    .global_sorts
                    .entry(name.clone())
                    .or_insert_with(|| sort.clone());
                self.type_info
                    .global_function_ids
                    .entry(name.clone())
                    .or_insert(function);
                self.type_info
                    .global_function_identity_history
                    .insert(function);
                let resolved_var = ResolvedVar {
                    name: name.clone(),
                    sort,
                    binding: ResolvedVarBinding::Global { function },
                    is_global_ref: false,
                };
                ResolvedNCommand::LetBegin(span.clone(), resolved_var, resolved)
            }
            NCommand::Extract(span, expr, variants) => {
                // A tuple-output function returns more than one value, so it can't be extracted as a
                // single term; surface a clear error instead of a confusing arity mismatch.
                if let GenericExpr::Call(_, head, _) = expr
                    && self
                        .type_info
                        .get_func_type(head)
                        .is_some_and(|t| t.is_tuple_output())
                {
                    return Err(TypeError::CannotExtractTupleOutput(
                        head.clone(),
                        span.clone(),
                    ));
                }
                let res_expr = self.type_info.typecheck_standalone_expr(
                    symbol_gen,
                    expr,
                    &Default::default(),
                    Context::Full,
                )?;

                let res_variants = self.type_info.typecheck_standalone_expr(
                    symbol_gen,
                    variants,
                    &Default::default(),
                    Context::Full,
                )?;
                if res_variants.output_type().name() != I64Sort.name() {
                    return Err(TypeError::Mismatch {
                        expr: variants.clone(),
                        expected: I64Sort.to_arcsort(),
                        actual: res_variants.output_type(),
                    });
                }

                ResolvedNCommand::Extract(span.clone(), res_expr, res_variants)
            }
            NCommand::Check(span, facts) => ResolvedNCommand::Check(
                span.clone(),
                self.type_info.typecheck_facts(symbol_gen, facts)?,
            ),
            NCommand::Fail(span, cmds) => ResolvedNCommand::Fail(
                span.clone(),
                cmds.iter()
                    .map(|cmd| self.typecheck_command(cmd))
                    .collect::<Result<_, _>>()?,
            ),
            NCommand::RunSchedule(schedule) => ResolvedNCommand::RunSchedule(
                self.type_info.typecheck_schedule(symbol_gen, schedule)?,
            ),
            NCommand::Pop(span, n) => ResolvedNCommand::Pop(span.clone(), *n),
            NCommand::Push(n) => ResolvedNCommand::Push(*n),
            NCommand::Index {
                span,
                name,
                function,
                any_of,
                resolution,
            } => {
                assert!(
                    resolution.is_none(),
                    "an unresolved index command carried forged resolution authority"
                );
                let identity = symbol_gen.fresh_index_registration_id();
                let resolution = self.typecheck_index(span, name, function, any_of, identity)?;
                ResolvedNCommand::Index {
                    span: span.clone(),
                    name: name.clone(),
                    function: function.clone(),
                    any_of: any_of.clone(),
                    resolution: Some(resolution),
                }
            }
            NCommand::AddRuleset(span, ruleset) => {
                ResolvedNCommand::AddRuleset(span.clone(), ruleset.clone())
            }
            NCommand::UnstableCombinedRuleset(span, name, sub_rulesets) => {
                ResolvedNCommand::UnstableCombinedRuleset(
                    span.clone(),
                    name.clone(),
                    sub_rulesets.clone(),
                )
            }
            NCommand::PrintOverallStatistics(span, file) => {
                ResolvedNCommand::PrintOverallStatistics(span.clone(), file.clone())
            }
            NCommand::PrintFunction(span, table, size, file, mode) => {
                ResolvedNCommand::PrintFunction(
                    span.clone(),
                    table.clone(),
                    *size,
                    file.clone(),
                    *mode,
                )
            }
            NCommand::PrintSize(span, n) => {
                // Should probably also resolve the function symbol here
                ResolvedNCommand::PrintSize(span.clone(), n.clone())
            }
            NCommand::ProveExists(span, constructor) => {
                // prove-exists targets a table: a constructor, or its lowering to
                // a term relation (a function) under the term/proof encoding.
                // `get_func_type` already rejects primitives/unbound names.
                let func_type = self
                    .type_info
                    .get_func_type(constructor)
                    .ok_or_else(|| TypeError::UnboundFunction(constructor.clone(), span.clone()))?;
                ResolvedNCommand::ProveExists(span.clone(), ResolvedCall::Func(func_type.clone()))
            }
            NCommand::Output { span, file, exprs } => {
                let exprs = exprs
                    .iter()
                    .map(|expr| {
                        self.type_info.typecheck_standalone_expr(
                            symbol_gen,
                            expr,
                            &Default::default(),
                            Context::Full,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                ResolvedNCommand::Output {
                    span: span.clone(),
                    file: file.clone(),
                    exprs,
                }
            }
            NCommand::Input { span, name, file } => ResolvedNCommand::Input {
                span: span.clone(),
                name: name.clone(),
                file: file.clone(),
            },
            NCommand::UserDefined(span, name, exprs) => {
                ResolvedNCommand::UserDefined(span.clone(), name.clone(), exprs.clone())
            }
        };
        if let ResolvedNCommand::NormRule { rule } = &command {
            self.warn_for_prefixed_non_globals_in_rule(rule)?;
        }
        Ok(command)
    }

    fn warn_for_prefixed_non_globals_in_var(
        &mut self,
        span: &Span,
        var: &ResolvedVar,
    ) -> Result<(), TypeError> {
        if var.is_global_ref {
            return Ok(());
        }
        if var.name.starts_with(crate::GLOBAL_NAME_PREFIX) {
            self.warn_prefixed_non_globals(span, &var.name)?;
        }
        Ok(())
    }

    fn warn_for_prefixed_non_globals_in_rule(
        &mut self,
        rule: &ResolvedRule,
    ) -> Result<(), TypeError> {
        let mut res: Result<(), TypeError> = Ok(());

        for fact in &rule.body {
            fact.visit_vars(&mut |span, var| {
                if res.is_ok() {
                    res = self.warn_for_prefixed_non_globals_in_var(span, var);
                }
            });
        }

        rule.head.visit_vars(&mut |span, var| {
            if res.is_ok() {
                res = self.warn_for_prefixed_non_globals_in_var(span, var);
            }
        });
        res
    }
}

impl TypeInfo {
    /// Adds a sort constructor to the typechecker's known set of types.
    pub fn add_presort<S: Presort>(&mut self, span: Span) -> Result<(), TypeError> {
        let name = S::presort_name();
        match self.mksorts.entry(name.to_owned()) {
            HEntry::Occupied(_) => Err(TypeError::SortAlreadyBound(name.to_owned(), span)),
            HEntry::Vacant(e) => {
                e.insert(S::make_sort);
                self.reserved_primitives.extend(S::reserved_primitives());
                Ok(())
            }
        }
    }

    /// Returns all sorts that satisfy the type and predicate.
    pub fn get_sorts_by<S: Sort>(&self, pred: impl Fn(&Arc<S>) -> bool) -> Vec<Arc<S>> {
        let mut results = Vec::new();
        for sort in self.sorts.values() {
            let sort = sort.clone().as_arc_any();
            if let Ok(sort) = Arc::downcast(sort)
                && pred(&sort)
            {
                results.push(sort);
            }
        }
        results
    }

    /// Returns all sorts based on the type.
    pub fn get_sorts<S: Sort>(&self) -> Vec<Arc<S>> {
        self.get_sorts_by(|_| true)
    }

    /// Returns a sort that satisfies the type and predicate.
    pub fn get_sort_by<S: Sort>(&self, pred: impl Fn(&Arc<S>) -> bool) -> Arc<S> {
        let results = self.get_sorts_by(pred);
        assert_eq!(
            results.len(),
            1,
            "Expected exactly one sort for type {}",
            std::any::type_name::<S>()
        );
        results.into_iter().next().unwrap()
    }

    /// Returns a sort based on the type.
    pub fn get_sort<S: Sort>(&self) -> Arc<S> {
        self.get_sort_by(|_| true)
    }

    /// Returns all sorts that satisfy the predicate.
    pub fn get_arcsorts_by(&self, f: impl Fn(&ArcSort) -> bool) -> Vec<ArcSort> {
        self.sorts.values().filter(|&x| f(x)).cloned().collect()
    }

    /// Returns a sort based on the predicate.
    pub fn get_arcsort_by(&self, f: impl Fn(&ArcSort) -> bool) -> ArcSort {
        let results = self.get_arcsorts_by(f);
        assert_eq!(
            results.len(),
            1,
            "Expected exactly one sort matching the given predicate"
        );
        results.into_iter().next().unwrap()
    }

    /// Returns the unique sort whose runtime values have Rust type `T`.
    pub fn get_arcsort_for_value_type<T: 'static>(&self) -> ArcSort {
        let results = self.get_arcsorts_by(|s| s.value_type() == Some(std::any::TypeId::of::<T>()));
        assert_eq!(
            results.len(),
            1,
            "Expected exactly one sort for type `{}`",
            std::any::type_name::<T>()
        );
        results.into_iter().next().unwrap()
    }

    /// Check if a sort allows union operations.
    /// A sort is unionable if it's an eq_sort and not marked as non-unionable
    /// (e.g., from `(sort Foo :no-union)` or relation desugaring).
    pub fn is_sort_unionable(&self, sort: &ArcSort) -> bool {
        sort.is_eq_sort() && !self.non_unionable_sorts.contains(sort.name())
    }

    fn function_to_functype(
        &self,
        symbol_gen: &mut SymbolGen,
        func: &FunctionDecl,
    ) -> Result<FuncType, TypeError> {
        let resolve = |name: &String| -> Result<ArcSort, TypeError> {
            self.sorts
                .get(name)
                .cloned()
                .ok_or_else(|| TypeError::UndefinedSort(name.clone(), func.span.clone()))
        };
        let input = func
            .schema
            .input
            .iter()
            .map(&resolve)
            .collect::<Result<Vec<_>, _>>()?;
        let outputs = func
            .schema
            .outputs
            .iter()
            .map(&resolve)
            .collect::<Result<Vec<_>, _>>()?;

        Ok(FuncType {
            identity: CallableIdentity::Function(symbol_gen.fresh_function_registration_id()),
            name: func.name.clone(),
            subtype: func.subtype,
            input,
            outputs,
        })
    }

    fn typecheck_function(
        &mut self,
        symbol_gen: &mut SymbolGen,
        fdecl: &FunctionDecl,
    ) -> Result<ResolvedFunctionDecl, TypeError> {
        if self.sorts.contains_key(&fdecl.name) {
            return Err(TypeError::SortAlreadyBound(
                fdecl.name.clone(),
                fdecl.span.clone(),
            ));
        }
        if self.is_primitive(&fdecl.name) {
            return Err(TypeError::PrimitiveAlreadyBound(
                fdecl.name.clone(),
                fdecl.span.clone(),
            ));
        }
        // Reject before allocating a nominal identity or mutating the catalog.
        // The old insert-and-test shape replaced the authoritative descriptor
        // on an error, so later calls could silently resolve to the rejected
        // declaration.
        if self.func_types.contains_key(&fdecl.name) {
            return Err(TypeError::FunctionAlreadyBound(
                fdecl.name.clone(),
                fdecl.span.clone(),
            ));
        }
        // View tables (with term_constructor) must have at least one input (the e-class), except the
        // proof-mode functional-dependency tuple view `(children) -> (eclass, proof)`, which keys on
        // children only (a 0-arg constructor's view then has no inputs).
        if fdecl.term_constructor.is_some()
            && fdecl.schema.input.is_empty()
            && !fdecl.schema.is_tuple_output()
        {
            return Err(TypeError::TermConstructorNoInputs(
                fdecl.name.clone(),
                fdecl.span.clone(),
            ));
        }
        let ftype = self.function_to_functype(symbol_gen, fdecl)?;
        let outputs = ftype.outputs.clone();
        let is_tuple = fdecl.schema.is_tuple_output();

        // Tuple outputs are only meaningful for custom functions (which carry a functional
        // dependency from keys to a tuple of values). Constructors mint a single e-class id, so they
        // may not be tuple-output. Term-constructor *views* may be tuple-output: the proof-mode
        // encoder emits `(children) -> (eclass, proof)` views (an internal-only annotation, so this
        // can't be reached by user input).
        if is_tuple && fdecl.subtype == FunctionSubtype::Constructor {
            return Err(TypeError::TupleOutputNotAllowed(
                fdecl.name.clone(),
                fdecl.span.clone(),
            ));
        }
        if fdecl.subtype == FunctionSubtype::Constructor && !outputs[0].is_eq_sort() {
            return Err(TypeError::ConstructorOutputNotSort(
                fdecl.name.clone(),
                fdecl.span.clone(),
            ));
        }

        // Merge expressions may refer to the function being declared, so make
        // the exact descriptor visible only while validating the declaration.
        // Any failure removes it before returning; a rejected declaration never
        // becomes catalog authority or blocks a corrected redeclaration.
        let previous = self.func_types.insert(fdecl.name.clone(), ftype.clone());
        debug_assert!(previous.is_none(), "function duplicate precheck drifted");

        // For single-output functions the merge expression refers to `old`/`new`. For
        // tuple-output functions it refers to `old0`, `new0`, `old1`, `new1`, ... (one pair per
        // output column), and the whole merge is a `(values ...)` form.
        let mut bound_vars = IndexMap::default();
        let mut merge_bindings = ResolvedBindingScope::default();
        let tuple_var_names: Vec<(String, String)> = (0..outputs.len())
            .map(|i| (format!("old{i}"), format!("new{i}")))
            .collect();
        if is_tuple {
            for (i, (old_name, new_name)) in tuple_var_names.iter().enumerate() {
                bound_vars.insert(old_name.as_str(), (fdecl.span.clone(), outputs[i].clone()));
                bound_vars.insert(new_name.as_str(), (fdecl.span.clone(), outputs[i].clone()));
                merge_bindings
                    .bind_exact(old_name.clone(), ResolvedVarBinding::MergeOld { column: i });
                merge_bindings
                    .bind_exact(new_name.clone(), ResolvedVarBinding::MergeNew { column: i });
            }
        } else {
            bound_vars.insert("old", (fdecl.span.clone(), outputs[0].clone()));
            bound_vars.insert("new", (fdecl.span.clone(), outputs[0].clone()));
            merge_bindings.bind_exact("old", ResolvedVarBinding::MergeOld { column: 0 });
            merge_bindings.bind_exact("new", ResolvedVarBinding::MergeNew { column: 0 });
        }

        // A `:merge` is a value-producing action block: the `actions` run (writes are allowed, but
        // live DB reads would be untracked by seminaive rule execution), then `result` produces the
        // merged value(s). Both are typechecked with `old`/`new` (`old0`/`new0`/... for tuple)
        // bound; the actions go through the same action typechecker as rule bodies.
        let merge_result = (|| -> Result<Option<ResolvedMerge>, TypeError> {
            Ok(match &fdecl.merge {
                Some(merge) => {
                    let mut next_let_slot = 0usize;
                    let action_bindings = merge
                        .actions
                        .iter()
                        .map(|action| {
                            matches!(action, GenericAction::Let(..)).then(|| {
                                let binding = ResolvedVarBinding::MergeLet {
                                    slot: next_let_slot,
                                };
                                next_let_slot += 1;
                                binding
                            })
                        })
                        .collect::<Vec<_>>();
                    let actions = self.typecheck_standalone_actions_in_scope(
                        symbol_gen,
                        &merge.actions,
                        &bound_vars,
                        &mut merge_bindings,
                        &action_bindings,
                        Context::Write,
                    )?;
                    // The result is evaluated after the actions, so any `let`-bound variable is in
                    // scope for it. Extend the binding with each `let`'s solved type before checking
                    // the result. `let_bindings` owns the names so `result_scope` can borrow them.
                    let let_bindings: Vec<(String, Span, ArcSort)> = actions
                        .0
                        .iter()
                        .filter_map(|a| match a {
                            GenericAction::Let(span, var, _) => {
                                Some((var.name.as_str().to_owned(), span.clone(), var.sort.clone()))
                            }
                            _ => None,
                        })
                        .collect();
                    let mut result_scope = bound_vars.clone();
                    for (name, span, sort) in &let_bindings {
                        result_scope.insert(name.as_str(), (span.clone(), sort.clone()));
                    }
                    let result = if is_tuple {
                        self.typecheck_tuple_merge(
                            symbol_gen,
                            fdecl,
                            &merge.result,
                            &outputs,
                            &result_scope,
                            &mut merge_bindings,
                        )?
                    } else {
                        self.typecheck_standalone_expr_in_scope(
                            symbol_gen,
                            &merge.result,
                            &result_scope,
                            &mut merge_bindings,
                            Context::Write,
                        )?
                    };
                    if !is_tuple && result.output_type().name() != outputs[0].name() {
                        return Err(TypeError::Mismatch {
                            expr: merge.result.clone(),
                            expected: outputs[0].clone(),
                            actual: result.output_type(),
                        });
                    }
                    Some(ResolvedMerge { actions, result })
                }
                None => None,
            })
        })();
        let merge = match merge_result {
            Ok(merge) => merge,
            Err(error) => {
                let removed = self.func_types.remove(&fdecl.name);
                debug_assert_eq!(
                    removed.as_ref().map(|func| func.identity),
                    Some(ftype.identity)
                );
                return Err(error);
            }
        };

        Ok(ResolvedFunctionDecl {
            name: fdecl.name.clone(),
            subtype: fdecl.subtype,
            schema: fdecl.schema.clone(),
            resolved_schema: ResolvedCall::Func(ftype),
            merge,
            cost: fdecl.cost,
            unextractable: fdecl.unextractable,
            internal_hidden: fdecl.internal_hidden,
            internal_let: fdecl.internal_let,
            span: fdecl.span.clone(),
            term_constructor: fdecl.term_constructor.clone(),
            identity_vals: fdecl.identity_vals,
            internal_term_node: fdecl.internal_term_node,
        })
    }

    /// Typecheck the `(values e0 e1 ...)` merge of a tuple-output function. Each `ei` is checked
    /// with `old0`/`new0`/... bound to the corresponding output columns, and must have the type of
    /// output column `i`. The result is a resolved `values` call carrying the output sorts.
    fn typecheck_tuple_merge(
        &self,
        symbol_gen: &mut SymbolGen,
        fdecl: &FunctionDecl,
        merge: &Expr,
        outputs: &[ArcSort],
        bound_vars: &IndexMap<&str, (Span, ArcSort)>,
        resolved_bindings: &mut ResolvedBindingScope,
    ) -> Result<ResolvedExpr, TypeError> {
        let args = match merge {
            GenericExpr::Call(_, head, args) if head.as_str() == "values" => args,
            _ => {
                return Err(TypeError::TupleMergeNotValues(
                    fdecl.name.clone(),
                    fdecl.span.clone(),
                ));
            }
        };
        if args.len() != outputs.len() {
            return Err(TypeError::TupleMergeArity {
                name: fdecl.name.clone(),
                expected: outputs.len(),
                actual: args.len(),
                span: fdecl.span.clone(),
            });
        }
        let mut resolved_args = Vec::with_capacity(args.len());
        for (arg, expected) in args.iter().zip(outputs) {
            let resolved = self.typecheck_standalone_expr_in_scope(
                symbol_gen,
                arg,
                bound_vars,
                resolved_bindings,
                Context::Write,
            )?;
            let actual = resolved.output_type();
            if actual.name() != expected.name() {
                return Err(TypeError::Mismatch {
                    expr: arg.clone(),
                    expected: expected.clone(),
                    actual,
                });
            }
            resolved_args.push(resolved);
        }
        Ok(GenericExpr::Call(
            merge.span(),
            ResolvedCall::Values(outputs.to_vec()),
            resolved_args,
        ))
    }

    fn typecheck_schedule(
        &self,
        symbol_gen: &mut SymbolGen,
        schedule: &Schedule,
    ) -> Result<ResolvedSchedule, TypeError> {
        let schedule = match schedule {
            Schedule::Repeat(span, times, schedule) => ResolvedSchedule::Repeat(
                span.clone(),
                *times,
                Box::new(self.typecheck_schedule(symbol_gen, schedule)?),
            ),
            Schedule::Sequence(span, schedules) => {
                let schedules = schedules
                    .iter()
                    .map(|schedule| self.typecheck_schedule(symbol_gen, schedule))
                    .collect::<Result<Vec<_>, _>>()?;
                ResolvedSchedule::Sequence(span.clone(), schedules)
            }
            Schedule::Saturate(span, schedule) => ResolvedSchedule::Saturate(
                span.clone(),
                Box::new(self.typecheck_schedule(symbol_gen, schedule)?),
            ),
            Schedule::Run(span, RunConfig { ruleset, until }) => {
                let until = until
                    .as_ref()
                    .map(|facts| self.typecheck_facts(symbol_gen, facts))
                    .transpose()?;
                ResolvedSchedule::Run(
                    span.clone(),
                    ResolvedRunConfig {
                        ruleset: ruleset.clone(),
                        until,
                    },
                )
            }
        };

        Result::Ok(schedule)
    }

    fn typecheck_rule(
        &self,
        symbol_gen: &mut SymbolGen,
        rule: &Rule,
        global_seminaive: bool,
    ) -> Result<ResolvedRule, TypeError> {
        let Rule {
            span,
            head,
            body,
            name,
            ruleset,
            eval_mode,
            no_decomp,
            include_subsumed,
        } = rule;
        let mut constraints = vec![];

        // Compile with the permissive Read/Full primitive contexts (so the RHS
        // can read the database) when the whole EGraph is non-seminaive, or the
        // rule's own mode requires it (`:naive` / `:unsafe-seminaive`).
        let read_contexts = !global_seminaive
            || matches!(
                eval_mode,
                RuleEvalMode::Naive | RuleEvalMode::UnsafeSeminaive
            );
        let (query_ctx, action_ctx) = if read_contexts {
            (Context::Read, Context::Full)
        } else {
            (Context::Pure, Context::Write)
        };

        let (query, mapped_query) = Facts(body.clone()).to_query(self, symbol_gen);
        constraints.extend(query.get_constraints(self, query_ctx)?);

        let mut binding = query.vars().collect::<IndexSet<_>>();
        // We lower to core actions with `union_to_set_optimization`
        // later in the pipeline. For typechecking we do not need it.
        let mut ctx = CoreActionContext::new(self, &mut binding, symbol_gen, false);
        let (actions, mapped_action) = head.to_core_actions(&mut ctx)?;

        let mut problem = Problem::default();
        problem.add_rule(
            &CoreRule {
                span: span.clone(),
                body: query,
                head: actions,
            },
            self,
            symbol_gen,
            query_ctx,
            action_ctx,
        )?;

        let assignment = problem
            .solve(|sort: &ArcSort| sort.name())
            .map_err(|e| e.to_type_error())?;

        let mut resolved_bindings = ResolvedBindingScope::default();
        let body: Vec<ResolvedFact> = assignment.annotate_facts(
            &mapped_query,
            self,
            symbol_gen,
            &mut resolved_bindings,
            query_ctx,
        );
        let action_bindings = vec![None; mapped_action.len()];
        let actions: ResolvedActions = assignment.annotate_actions(
            &mapped_action,
            self,
            symbol_gen,
            &mut resolved_bindings,
            &action_bindings,
            action_ctx,
        )?;

        // Function lookups in actions need the `Full` action context; the
        // `Write` context (`!read_contexts`) can't express them.
        if !read_contexts {
            self.check_no_function_lookups_in_actions(&actions)?;
        }

        Ok(ResolvedRule {
            span: span.clone(),
            body,
            head: actions,
            name: name.clone(),
            ruleset: ruleset.clone(),
            eval_mode: *eval_mode,
            no_decomp: *no_decomp,
            include_subsumed: *include_subsumed,
        })
    }

    fn check_lookup_expr(&self, expr: &ResolvedExpr) -> Result<(), TypeError> {
        if let Some(span) = self.expr_has_function_lookup(expr) {
            return Err(TypeError::LookupInRuleDisallowed(
                "function".to_string(),
                span,
            ));
        }
        Ok(())
    }

    fn check_no_function_lookups_in_actions(
        &self,
        actions: &ResolvedActions,
    ) -> Result<(), TypeError> {
        for action in actions.iter() {
            match action {
                GenericAction::Let(_, _, rhs) => self.check_lookup_expr(rhs)?,
                GenericAction::Set(_, _, args, rhs) => {
                    for arg in args.iter() {
                        self.check_lookup_expr(arg)?;
                    }
                    self.check_lookup_expr(rhs)?;
                }
                GenericAction::Union(_, lhs, rhs) => {
                    self.check_lookup_expr(lhs)?;
                    self.check_lookup_expr(rhs)?;
                }
                GenericAction::Change(_, _, _, args) => {
                    for arg in args.iter() {
                        self.check_lookup_expr(arg)?;
                    }
                }
                GenericAction::Panic(..) => {}
                GenericAction::Expr(_, expr) => self.check_lookup_expr(expr)?,
            }
        }
        Ok(())
    }

    pub fn typecheck_facts(
        &self,
        symbol_gen: &mut SymbolGen,
        facts: &[Fact],
    ) -> Result<Vec<ResolvedFact>, TypeError> {
        let (query, mapped_facts) = Facts(facts.to_vec()).to_query(self, symbol_gen);
        let mut problem = Problem::default();
        // Top-level query-shaped commands (e.g. `check`) are read-only:
        // primitives may inspect the database but not write to it.
        problem.add_query(&query, self, Context::Read)?;
        let assignment = problem
            .solve(|sort: &ArcSort| sort.name())
            .map_err(|e| e.to_type_error())?;
        let mut resolved_bindings = ResolvedBindingScope::default();
        let annotated_facts = assignment.annotate_facts(
            &mapped_facts,
            self,
            symbol_gen,
            &mut resolved_bindings,
            Context::Read,
        );
        Ok(annotated_facts)
    }

    // Standalone expressions/actions use action lowering. Top-level commands
    // pass `Full`; function `:merge` reuses this path with `Write` because
    // merge expressions run during table updates.
    fn typecheck_standalone_actions(
        &self,
        symbol_gen: &mut SymbolGen,
        actions: &Actions,
        binding: &IndexMap<&str, (Span, ArcSort)>,
        context: Context,
    ) -> Result<ResolvedActions, TypeError> {
        let mut resolved_bindings = ResolvedBindingScope::default();
        for var in binding.keys() {
            resolved_bindings.bind_lexical(*var, symbol_gen);
        }
        let action_bindings = vec![None; actions.len()];
        self.typecheck_standalone_actions_in_scope(
            symbol_gen,
            actions,
            binding,
            &mut resolved_bindings,
            &action_bindings,
            context,
        )
    }

    fn typecheck_standalone_actions_in_scope(
        &self,
        symbol_gen: &mut SymbolGen,
        actions: &Actions,
        binding: &IndexMap<&str, (Span, ArcSort)>,
        resolved_bindings: &mut ResolvedBindingScope,
        action_bindings: &[Option<ResolvedVarBinding>],
        context: Context,
    ) -> Result<ResolvedActions, TypeError> {
        let mut binding_set: IndexSet<String> =
            binding.keys().copied().map(str::to_string).collect();
        // We lower to core actions with `union_to_set_optimization`
        // later in the pipeline. For typechecking we do not need it.
        let mut ctx = CoreActionContext::new(self, &mut binding_set, symbol_gen, false);
        let (actions, mapped_action) = actions.to_core_actions(&mut ctx)?;
        let mut problem = Problem::default();

        problem.add_actions(&actions, self, symbol_gen, context)?;

        // add bindings from the context
        for (var, (span, sort)) in binding {
            problem.assign_local_var_type(var, span.clone(), sort.clone())?;
        }

        let assignment = problem
            .solve(|sort: &ArcSort| sort.name())
            .map_err(|e| e.to_type_error())?;

        let annotated_actions = assignment.annotate_actions(
            &mapped_action,
            self,
            symbol_gen,
            resolved_bindings,
            action_bindings,
            context,
        )?;
        Ok(annotated_actions)
    }

    fn typecheck_standalone_expr(
        &self,
        symbol_gen: &mut SymbolGen,
        expr: &Expr,
        binding: &IndexMap<&str, (Span, ArcSort)>,
        context: Context,
    ) -> Result<ResolvedExpr, TypeError> {
        let mut resolved_bindings = ResolvedBindingScope::default();
        for var in binding.keys() {
            resolved_bindings.bind_lexical(*var, symbol_gen);
        }
        self.typecheck_standalone_expr_in_scope(
            symbol_gen,
            expr,
            binding,
            &mut resolved_bindings,
            context,
        )
    }

    fn typecheck_standalone_expr_in_scope(
        &self,
        symbol_gen: &mut SymbolGen,
        expr: &Expr,
        binding: &IndexMap<&str, (Span, ArcSort)>,
        resolved_bindings: &mut ResolvedBindingScope,
        context: Context,
    ) -> Result<ResolvedExpr, TypeError> {
        let action = Action::Expr(expr.span(), expr.clone());
        let typechecked_action = self.typecheck_standalone_actions_in_scope(
            symbol_gen,
            &Actions::singleton(action),
            binding,
            resolved_bindings,
            &[None],
            context,
        )?;
        let typechecked_action = typechecked_action.0.into_iter().next().unwrap();
        match typechecked_action {
            ResolvedAction::Expr(_, expr) => Ok(expr),
            _ => unreachable!(),
        }
    }

    pub(crate) fn typecheck_expr_with_output(
        &self,
        symbol_gen: &mut SymbolGen,
        expr: &Expr,
        binding: &IndexMap<&str, (Span, ArcSort)>,
        output_sort: ArcSort,
        context: Context,
    ) -> Result<ResolvedExpr, TypeError> {
        let action = Action::Expr(expr.span(), expr.clone());
        let mut binding_set: IndexSet<String> =
            binding.keys().copied().map(str::to_string).collect();
        let mut ctx = CoreActionContext::new(self, &mut binding_set, symbol_gen, false);
        let (actions, mapped_action) = Actions::singleton(action).to_core_actions(&mut ctx)?;
        let mut problem = Problem::default();

        problem.add_actions(&actions, self, symbol_gen, context)?;

        for (var, (span, sort)) in binding {
            problem.assign_local_var_type(var, span.clone(), sort.clone())?;
        }

        let [GenericAction::Expr(_, mapped_expr)] = mapped_action.0.as_slice() else {
            unreachable!("typechecking an expression should produce one expression action")
        };
        let output_atom = mapped_expr.get_corresponding_var_or_lit_in_scope(self, &binding_set);
        problem.add_binding(output_atom, output_sort.clone());

        let assignment = problem
            .solve(|sort: &ArcSort| sort.name())
            .map_err(|e| e.to_type_error())?;

        let mut resolved_bindings = ResolvedBindingScope::default();
        for var in binding.keys() {
            resolved_bindings.bind_lexical(*var, symbol_gen);
        }
        let annotated_actions = assignment.annotate_actions(
            &mapped_action,
            self,
            symbol_gen,
            &mut resolved_bindings,
            &[None],
            context,
        )?;
        match annotated_actions.0.into_iter().next().unwrap() {
            ResolvedAction::Expr(_, resolved_expr) => {
                let actual = resolved_expr.output_type();
                if actual.name() != output_sort.name() {
                    return Err(TypeError::Mismatch {
                        expr: expr.clone(),
                        expected: output_sort,
                        actual,
                    });
                }
                Ok(resolved_expr)
            }
            _ => unreachable!(),
        }
    }

    fn typecheck_standalone_action(
        &self,
        symbol_gen: &mut SymbolGen,
        action: &Action,
        binding: &IndexMap<&str, (Span, ArcSort)>,
        context: Context,
    ) -> Result<ResolvedAction, TypeError> {
        self.typecheck_standalone_actions(
            symbol_gen,
            &Actions::singleton(action.clone()),
            binding,
            context,
        )
        .map(|v| {
            assert_eq!(v.len(), 1);
            v.0.into_iter().next().unwrap()
        })
    }

    pub fn get_sort_by_name(&self, sym: &str) -> Option<&ArcSort> {
        self.sorts.get(sym)
    }

    pub fn get_prims(&self, sym: &str) -> Option<&[PrimitiveWithId]> {
        self.primitives.get(sym).map(Vec::as_slice)
    }

    pub fn is_primitive(&self, sym: &str) -> bool {
        self.primitives.contains_key(sym) || self.reserved_primitives.contains(sym)
    }

    pub fn primitive_has_validator(&self, id: ExternalFunctionId) -> bool {
        self.primitives
            .values()
            .flat_map(|v| v.iter())
            .any(|p| p.context_ids.iter().any(|(_, pid)| *pid == Some(id)) && p.validator.is_some())
    }

    pub fn get_func_type(&self, sym: &str) -> Option<&FuncType> {
        self.func_types.get(sym)
    }

    pub fn is_constructor(&self, sym: &str) -> bool {
        self.func_types
            .get(sym)
            .is_some_and(|f| f.subtype == FunctionSubtype::Constructor)
    }

    pub fn get_global_sort(&self, sym: &str) -> Option<&ArcSort> {
        self.global_sorts.get(sym)
    }

    pub(crate) fn get_global_function_id(&self, sym: &str) -> Option<FunctionRegistrationId> {
        self.global_function_ids.get(sym).copied()
    }

    /// Return the exact registration selected as core value equality.
    pub(crate) fn value_eq_primitive(&self) -> Option<&PrimitiveWithId> {
        let identity = self.value_eq_registration_id?;
        self.primitives
            .values()
            .flatten()
            .find(|primitive| primitive.registration_id() == identity)
    }

    pub fn is_global(&self, sym: &str) -> bool {
        self.global_sorts.contains_key(sym)
    }

    /// Whether this exact callable registration is owned by a global binding.
    pub(crate) fn is_global_function_identity(&self, identity: CallableIdentity) -> bool {
        matches!(
            identity,
            CallableIdentity::Function(identity)
                if self.global_function_identity_history.contains(&identity)
        )
    }

    /// Preserve exact global authority for already-resolved commands when an
    /// e-graph scope is popped. Current name lookup is still restored from the
    /// outer snapshot; only the monotone identity census crosses the boundary.
    pub(crate) fn preserve_global_function_identity_history_from(&mut self, newer: &Self) {
        self.global_function_identity_history
            .extend(newer.global_function_identity_history.iter().copied());
    }

    /// Check if an expression contains non-global function lookups (FunctionSubtype::Custom calls).
    /// Global function calls are allowed since they get desugared to constructors.
    /// Returns Some(span) if a lookup is found, None otherwise.
    pub fn expr_has_function_lookup(&self, expr: &ResolvedExpr) -> Option<Span> {
        use ast::GenericExpr;

        expr.find(&mut |e| {
            if let GenericExpr::Call(span, ResolvedCall::Func(func_type), _) = e
                && func_type.subtype == FunctionSubtype::Custom
                && !self.is_global_function_identity(func_type.identity)
            {
                return Some(span.clone());
            }
            None
        })
    }
}

#[derive(Debug, Clone, Error)]
pub enum TypeError {
    #[error("{}\nArity mismatch, expected {expected} args: {expr}", .expr.span())]
    Arity { expr: Expr, expected: usize },
    #[error(
        "{}\n Expect expression {expr} to have type {}, but get type {}",
        .expr.span(), .expected.name(), .actual.name(),
    )]
    Mismatch {
        expr: Expr,
        expected: ArcSort,
        actual: ArcSort,
    },
    #[error("{1}\nIndex {0} lists no columns to index")]
    EmptyIndex(String, Span),
    #[error("{3}\nIndex {0} refers to column {1}, but the indexed row has {2} columns")]
    IndexColumnOutOfRange(String, usize, usize, Span),
    #[error("{3}\nIndex {0} mixes columns of sort {1} and {2}; an index reads one sort")]
    IndexColumnSortMismatch(String, String, String, Span),
    #[error(
        "{2}\nIndex {0} is looked up by {1}, which no other function atom binds. An index atom is probed, so its value must be bound elsewhere in the query by a function's rows; a body primitive runs after the join, so it cannot bind it."
    )]
    IndexValueUnbound(String, String, Span),
    #[error("{1}\nIndex {0} is maintained by the database and cannot be written to")]
    IndexIsReadOnly(String, Span),
    #[error(
        "{2}\nIndex {0} indexes {1}, which is itself an index; an index has no rows of its own"
    )]
    IndexOfIndex(String, String, Span),
    #[error("{1}\nUnbound symbol {0}")]
    Unbound(String, Span),
    #[error(
        "{1}\nVariable {0} is ungrounded. A variable is grounded when it appears as an argument to a constructor or function in the query, not just under primitives or equalities."
    )]
    Ungrounded(String, Span),
    #[error("{1}\nUndefined sort {0}")]
    UndefinedSort(String, Span),
    #[error("{1}\nUnbound function {0}")]
    UnboundFunction(String, Span),
    #[error("{1}\nFunction already bound {0}")]
    FunctionAlreadyBound(String, Span),
    #[error("{1}\nSort {0} already declared.")]
    SortAlreadyBound(String, Span),
    #[error("{1}\nPrimitive {0} already declared.")]
    PrimitiveAlreadyBound(String, Span),
    #[error("Function type mismatch: expected {} => {}, actual {} => {}", .1.iter().map(|s| s.name().to_string()).collect::<Vec<_>>().join(", "), .0.name(), .3.iter().map(|s| s.name().to_string()).collect::<Vec<_>>().join(", "), .2.name())]
    FunctionTypeMismatch(ArcSort, Vec<ArcSort>, ArcSort, Vec<ArcSort>),
    #[error("{1}\nPresort {0} not found.")]
    PresortNotFound(String, Span),
    #[error("{}\nFailed to infer a type for: {}", .0.span(), .0)]
    InferenceFailure(Expr),
    #[error("{1}\nVariable {0} was already defined")]
    AlreadyDefined(String, Span),
    #[error("{1}\nThe output type of constructor function {0} must be sort")]
    ConstructorOutputNotSort(String, Span),
    #[error("{1}\nValue lookup of non-constructor function {0} in rule is disallowed.")]
    LookupInRuleDisallowed(String, Span),
    #[error("{1}\nCannot set constructor {0}. Use `union` instead or declare {0} as a function.")]
    SetConstructorDisallowed(String, Span),
    #[error("All alternative definitions considered failed\n{}", .0.iter().map(|e| format!("  {e}\n")).collect::<Vec<_>>().join(""))]
    AllAlternativeFailed(Vec<TypeError>),
    #[error("{}\nCannot union values of sort {}", .1, .0.name())]
    NonEqsortUnion(ArcSort, Span),
    #[error("{}\nCannot union values of sort {} because it is marked as non-unionable (e.g. from a relation)", .1, .0.name())]
    NonUnionableSort(ArcSort, Span),
    #[error(
        "{1}\nView table {0} with :internal-term-constructor must have at least one input (the e-class)."
    )]
    TermConstructorNoInputs(String, Span),
    #[error(
        "{span}\nNon-global variable `{name}` must not start with `{}`.",
        crate::GLOBAL_NAME_PREFIX
    )]
    NonGlobalPrefixed { name: String, span: Span },
    #[error(
        "{span}\nGlobal `{name}` must start with `{}`.",
        crate::GLOBAL_NAME_PREFIX
    )]
    GlobalMissingPrefix { name: String, span: Span },
    #[error(
        "{1}\nFunction {0} has a tuple output, which is only allowed for plain functions (not constructors, relations, or view tables)."
    )]
    TupleOutputNotAllowed(String, Span),
    #[error(
        "{1}\nThe :merge of tuple-output function {0} must be a `(values ...)` form with one expression per output column."
    )]
    TupleMergeNotValues(String, Span),
    #[error(
        "{span}\nThe :merge of tuple-output function {name} has {actual} columns but the function has {expected} output columns."
    )]
    TupleMergeArity {
        name: String,
        expected: usize,
        actual: usize,
        span: Span,
    },
    #[error(
        "{1}\nCannot extract tuple-output function {0}: extraction yields a single term, but a tuple-output function has more than one output column. Read its columns in a rule with `(= (values ...) ({0} ...))` instead."
    )]
    CannotExtractTupleOutput(String, Span),
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{EGraph, Error};

    fn desugar_program(egraph: &mut EGraph, program: &str) -> Vec<NCommand> {
        let parsed = egraph.parse_program(None, program).unwrap();
        let mut desugared = Vec::new();
        for command in parsed {
            desugared
                .extend(ast::desugar::desugar_command(command, &mut egraph.parser, false).unwrap());
        }
        desugared
    }

    fn function_identity(func: &FuncType) -> FunctionRegistrationId {
        let CallableIdentity::Function(identity) = func.identity else {
            panic!("expected a function identity, got {:?}", func.identity);
        };
        identity
    }

    fn resolved_func(call: &ResolvedCall) -> &FuncType {
        let ResolvedCall::Func(func) = call else {
            panic!("expected a resolved function call, got {call:?}");
        };
        func
    }

    #[test]
    fn test_arity_mismatch() {
        let mut egraph = EGraph::default();

        let prog = "
            (relation f (i64 i64))
            (rule ((f a b c)) ())
       ";
        let res = egraph.parse_and_run_program(None, prog);
        match res {
            Err(Error::TypeError(TypeError::Arity {
                expected: 2,
                expr: e,
            })) => {
                assert_eq!(e.span().string(), "(f a b c)");
            }
            _ => panic!("Expected arity mismatch, got: {res:?}"),
        }
    }

    #[test]
    fn callable_identity_distinguishes_same_schema_functions_and_index() {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(
                None,
                r#"
                (function left (i64) i64 :merge old)
                (function right (i64) i64 :merge old)
                (index LeftOccurrence left (any 0 1))
                "#,
            )
            .unwrap();

        let left = egraph.type_info.get_func_type("left").unwrap();
        let right = egraph.type_info.get_func_type("right").unwrap();
        let index = egraph.type_info.get_func_type("LeftOccurrence").unwrap();
        let left_identity = function_identity(left);
        assert_ne!(left.identity, right.identity);
        assert!(matches!(index.identity, CallableIdentity::Index(_)));
        assert_ne!(left.identity, index.identity);

        // Display metadata and schema-shaped decoys do not define equality.
        let mut renamed_left = left.clone();
        renamed_left.name = "diagnostic-only".to_owned();
        assert_eq!(left, &renamed_left);
        let mut same_name_right = right.clone();
        same_name_right.name = left.name.clone();
        assert_ne!(left, &same_name_right);

        let index_info = &egraph.type_info.indexes["LeftOccurrence"];
        assert_eq!(index.identity, CallableIdentity::Index(index_info.identity));
        assert_eq!(index_info.target, left_identity);
    }

    #[test]
    fn desugared_index_has_no_finalized_resolution_authority() {
        let mut egraph = EGraph::default();
        let desugared = desugar_program(&mut egraph, "(index Occurrence edge (any 0 1))");
        let [NCommand::Index { resolution, .. }] = desugared.as_slice() else {
            panic!("expected one desugared index command, got {desugared:?}");
        };
        assert!(resolution.is_none());
    }

    #[test]
    fn resolved_indexes_carry_exact_identity_and_target_authority() {
        let mut egraph = EGraph::default();
        let desugared = desugar_program(
            &mut egraph,
            r#"
            (function left (i64) i64 :merge old)
            (function right (i64) i64 :merge old)
            (index LeftOccurrence left (any 0 1))
            (index RightOccurrence right (any 0 1))
            "#,
        );
        let source_index_renderings = desugared
            .iter()
            .filter(|command| matches!(command, NCommand::Index { .. }))
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        let mut resolved = egraph.typecheck_program(&desugared).unwrap();
        let left_target = CallableIdentity::Function(function_identity(
            egraph.type_info.get_func_type("left").unwrap(),
        ));
        let right_target = CallableIdentity::Function(function_identity(
            egraph.type_info.get_func_type("right").unwrap(),
        ));

        let (left_index, left_carried_target, right_index, right_carried_target) = {
            let indexes = resolved
                .iter()
                .filter_map(|command| match command {
                    ResolvedNCommand::Index {
                        name,
                        function,
                        resolution: Some(resolution),
                        ..
                    } => Some((name, function, resolution)),
                    ResolvedNCommand::Index {
                        resolution: None, ..
                    } => panic!("a resolved index command lacked nominal authority"),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(indexes.len(), 2);
            assert_eq!(indexes[0].0, "LeftOccurrence");
            assert_eq!(indexes[0].1, "left");
            assert_eq!(indexes[1].0, "RightOccurrence");
            assert_eq!(indexes[1].1, "right");

            let left_index = resolved_func(&indexes[0].2.index);
            let right_index = resolved_func(&indexes[1].2.index);
            let left_carried_target = resolved_func(&indexes[0].2.target);
            let right_carried_target = resolved_func(&indexes[1].2.target);
            assert_eq!(
                left_index
                    .input
                    .iter()
                    .map(|sort| sort.name())
                    .collect::<Vec<_>>(),
                right_index
                    .input
                    .iter()
                    .map(|sort| sort.name())
                    .collect::<Vec<_>>()
            );
            assert_eq!(
                left_index
                    .outputs
                    .iter()
                    .map(|sort| sort.name())
                    .collect::<Vec<_>>(),
                right_index
                    .outputs
                    .iter()
                    .map(|sort| sort.name())
                    .collect::<Vec<_>>()
            );
            (
                left_index.identity,
                left_carried_target.identity,
                right_index.identity,
                right_carried_target.identity,
            )
        };

        assert!(matches!(left_index, CallableIdentity::Index(_)));
        assert!(matches!(right_index, CallableIdentity::Index(_)));
        assert_ne!(left_index, right_index);
        assert_eq!(left_carried_target, left_target);
        assert_eq!(right_carried_target, right_target);
        assert_ne!(left_carried_target, right_carried_target);
        assert_eq!(
            resolved
                .iter()
                .filter(|command| matches!(command, ResolvedNCommand::Index { .. }))
                .map(ToString::to_string)
                .collect::<Vec<_>>(),
            source_index_renderings
        );

        let left_command = resolved
            .iter_mut()
            .find(|command| {
                matches!(
                    command,
                    ResolvedNCommand::Index { name, .. } if name == "LeftOccurrence"
                )
            })
            .unwrap();
        let ResolvedNCommand::Index {
            name,
            function,
            resolution: Some(resolution),
            ..
        } = left_command
        else {
            unreachable!()
        };
        *name = "diagnostic-index-decoy".to_owned();
        *function = "right".to_owned();
        let ResolvedCall::Func(index) = &mut resolution.index else {
            unreachable!()
        };
        index.name = "diagnostic-index-head-decoy".to_owned();
        let ResolvedCall::Func(target) = &mut resolution.target else {
            unreachable!()
        };
        target.name = "diagnostic-target-head-decoy".to_owned();

        assert_eq!(index.identity, left_index);
        assert_eq!(target.identity, left_target);
        assert_ne!(target.identity, right_target);
    }

    #[test]
    fn rejected_duplicate_preserves_registered_function_identity() {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(None, "(function stable (i64) i64 :merge old)")
            .unwrap();
        let registered = egraph.type_info.get_func_type("stable").unwrap().clone();

        let error = egraph
            .parse_and_run_program(None, "(function stable (i64) i64 :merge new)")
            .unwrap_err();
        assert!(matches!(
            error,
            Error::TypeError(TypeError::FunctionAlreadyBound(name, _)) if name == "stable"
        ));
        assert_eq!(
            egraph.type_info.get_func_type("stable").unwrap().identity,
            registered.identity
        );
    }

    #[test]
    fn global_lowering_reuses_the_declared_function_identity() {
        let mut egraph = EGraph::new_compile_only(false);
        let resolved = egraph
            .resolve_program_compile_only(None, "(let $global 1)")
            .unwrap();
        let mut declaration = None;
        let mut initialization = None;
        for command in &resolved.execution {
            match &command.command {
                ResolvedNCommand::Function(function) if function.name == "$global" => {
                    let ResolvedCall::Func(func) = &function.resolved_schema else {
                        panic!("global declaration did not resolve to a function")
                    };
                    declaration = Some(func.identity);
                }
                ResolvedNCommand::CoreAction(GenericAction::Set(_, func, args, _))
                    if func.name() == "$global" && args.is_empty() =>
                {
                    let ResolvedCall::Func(func) = func else {
                        panic!("global initializer did not target a function")
                    };
                    initialization = Some(func.identity);
                }
                _ => {}
            }
        }

        assert_eq!(declaration, initialization);
        assert!(matches!(declaration, Some(CallableIdentity::Function(_))));
    }

    #[test]
    fn proof_retypechecking_updates_global_identity_to_its_new_catalog() {
        let mut egraph = EGraph::new_compile_only(true);
        egraph
            .resolve_program_compile_only(None, "(datatype Expr (Num i64))\n(let $global (Num 1))")
            .unwrap();
        let term_table = function_identity(
            egraph
                .type_info
                .get_func_type("$global")
                .expect("proof-instrumented global term table"),
        );
        let registered = egraph
            .type_info
            .get_global_function_id("$global")
            .expect("source global must map to its exact encoded view");
        assert_ne!(registered, term_table);
        assert!(
            egraph
                .type_info
                .func_types
                .values()
                .any(
                    |function| function.identity == CallableIdentity::Function(registered)
                        && function.subtype == FunctionSubtype::Custom
                )
        );
    }

    #[test]
    fn callable_identity_high_water_survives_pop() {
        let mut egraph = EGraph::default();
        egraph.push();
        egraph
            .parse_and_run_program(None, "(function scoped (i64) i64 :merge old)")
            .unwrap();
        let scoped = function_identity(egraph.type_info.get_func_type("scoped").unwrap());
        egraph.pop().unwrap();
        egraph
            .parse_and_run_program(None, "(function later (i64) i64 :merge old)")
            .unwrap();
        let later = function_identity(egraph.type_info.get_func_type("later").unwrap());

        assert_ne!(scoped, later);
        assert!(later.ordinal() > scoped.ordinal());
    }

    #[test]
    fn exact_global_identity_history_survives_pop_without_restoring_its_name() {
        let mut egraph = EGraph::default();
        egraph.push();
        egraph
            .parse_and_run_program(None, "(let $scoped 1)")
            .unwrap();
        let scoped = egraph
            .type_info
            .get_global_function_id("$scoped")
            .expect("scoped global registration");
        egraph.pop().unwrap();

        assert!(egraph.type_info.get_global_sort("$scoped").is_none());
        assert!(egraph.type_info.get_global_function_id("$scoped").is_none());
        assert!(
            egraph
                .type_info
                .is_global_function_identity(CallableIdentity::Function(scoped))
        );
    }

    #[test]
    fn resolved_lexical_identity_ignores_diagnostic_name() {
        let sort = I64Sort.to_arcsort();
        let binding = ResolvedVarBinding::Lexical {
            id: ResolvedBindingId::new(17),
        };
        let original = ResolvedVar {
            name: "source-name".to_owned(),
            sort: sort.clone(),
            binding,
            is_global_ref: false,
        };
        let mut renamed = original.clone();
        renamed.name = "diagnostic-decoy".to_owned();
        assert_eq!(original, renamed);

        let mut set = crate::util::HashSet::default();
        set.insert(original);
        assert!(set.contains(&renamed));

        let same_binding_different_sort = ResolvedVar {
            name: "also-diagnostic".to_owned(),
            sort: StringSort.to_arcsort(),
            binding,
            is_global_ref: false,
        };
        assert_eq!(renamed, same_binding_different_sort);

        let distinct = ResolvedVar {
            name: renamed.name.clone(),
            sort,
            binding: ResolvedVarBinding::Lexical {
                id: ResolvedBindingId::new(18),
            },
            is_global_ref: false,
        };
        assert_ne!(renamed, distinct);
    }

    #[test]
    #[should_panic(expected = "one resolved binding authority was assigned incompatible sorts")]
    fn binding_scope_rejects_one_authority_with_different_sorts() {
        let mut scope = ResolvedBindingScope::default();
        let binding = ResolvedVarBinding::Lexical {
            id: ResolvedBindingId::new(23),
        };
        scope.observe_sort(binding, &I64Sort.to_arcsort());
        scope.observe_sort(binding, &StringSort.to_arcsort());
    }

    #[test]
    fn resolved_query_lowering_uses_binding_not_diagnostic_name() {
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(None, "(let $global 1)")
            .unwrap();
        let global_function = egraph
            .type_info
            .get_global_function_id("$global")
            .expect("declared global identity");

        let mut lexical = ResolvedVar {
            name: "ordinary".to_owned(),
            sort: I64Sort.to_arcsort(),
            binding: ResolvedVarBinding::Lexical {
                id: egraph.parser.symbol_gen.fresh_resolved_binding_id(),
            },
            // Deliberately stale metadata must not change authority either.
            is_global_ref: true,
        };
        lexical.name = "$global".to_owned();
        let mut exact_global = ResolvedVar {
            name: "$global".to_owned(),
            sort: I64Sort.to_arcsort(),
            binding: ResolvedVarBinding::Global {
                function: global_function,
            },
            is_global_ref: false,
        };
        exact_global.name = "diagnostic-decoy".to_owned();

        let facts = crate::ast::Facts(vec![
            ResolvedFact::Eq(
                Span::Panic,
                ResolvedExpr::Var(Span::Panic, lexical.clone()),
                ResolvedExpr::Lit(Span::Panic, Literal::Int(1)),
            ),
            ResolvedFact::Eq(
                Span::Panic,
                ResolvedExpr::Var(Span::Panic, exact_global.clone()),
                ResolvedExpr::Lit(Span::Panic, Literal::Int(1)),
            ),
        ]);
        let (query, _) = facts.to_query(&egraph.type_info, &mut egraph.parser.symbol_gen);

        assert!(matches!(
            &query.atoms[0].args[0],
            crate::core::GenericAtomTerm::Var(_, var) if var.binding == lexical.binding
        ));
        assert!(matches!(
            &query.atoms[1].args[0],
            crate::core::GenericAtomTerm::Global(_, var) if var.binding == exact_global.binding
        ));
    }

    #[test]
    fn global_removal_uses_binding_not_legacy_ref_flag() {
        let global_function = FunctionRegistrationId::new(41);
        let global = ResolvedVar {
            name: "$global".to_owned(),
            sort: I64Sort.to_arcsort(),
            binding: ResolvedVarBinding::Global {
                function: global_function,
            },
            is_global_ref: false,
        };
        let lexical = ResolvedVar {
            name: "$global".to_owned(),
            sort: I64Sort.to_arcsort(),
            binding: ResolvedVarBinding::Lexical {
                id: ResolvedBindingId::new(42),
            },
            is_global_ref: true,
        };

        let removed =
            crate::ast::remove_globals::remove_globals_expr(ResolvedExpr::Var(Span::Panic, global));
        let ResolvedExpr::Call(_, ResolvedCall::Func(function), arguments) = removed else {
            panic!("exact global authority was not eliminated");
        };
        assert_eq!(
            function.identity,
            CallableIdentity::Function(global_function)
        );
        assert!(arguments.is_empty());

        let unchanged = crate::ast::remove_globals::remove_globals_expr(ResolvedExpr::Var(
            Span::Panic,
            lexical.clone(),
        ));
        assert!(matches!(
            unchanged,
            ResolvedExpr::Var(_, var) if var.binding == lexical.binding
        ));
    }

    #[test]
    fn rule_scope_shares_identity_and_distinct_rules_do_not_alias() {
        fn rule_vars(rule: &ResolvedRule) -> Vec<ResolvedVar> {
            let mut vars = vec![];
            for fact in &rule.body {
                fact.clone().visit_exprs(&mut |expr| {
                    if let GenericExpr::Var(_, var) = &expr {
                        vars.push(var.clone());
                    }
                    expr
                });
            }
            for action in &rule.head.0 {
                if let GenericAction::Let(_, var, _) = action {
                    vars.push(var.clone());
                }
                action.clone().visit_exprs(&mut |expr| {
                    if let GenericExpr::Var(_, var) = &expr {
                        vars.push(var.clone());
                    }
                    expr
                });
            }
            vars
        }

        let mut egraph = EGraph::default();
        let desugared = desugar_program(
            &mut egraph,
            r#"
            (relation source (i64))
            (relation sink (i64))
            (rule ((source x))
                  ((let y (+ x 1))
                   (sink y))
                  :name "first")
            (rule ((source x))
                  ((sink x))
                  :name "second")
            "#,
        );
        let resolved = egraph.typecheck_program(&desugared).unwrap();
        let rules = resolved
            .iter()
            .filter_map(|command| match command {
                ResolvedNCommand::NormRule { rule } => Some(rule),
                _ => None,
            })
            .collect::<Vec<_>>();
        let [first, second] = rules.as_slice() else {
            panic!("expected two rules, got {rules:?}");
        };

        let first_vars = rule_vars(first);
        let first_x = first_vars
            .iter()
            .filter(|var| var.name == "x")
            .collect::<Vec<_>>();
        assert!(
            first_x.len() >= 2,
            "x must occur in body and head: {first_vars:?}"
        );
        assert!(first_x.iter().all(|var| var.binding == first_x[0].binding));
        let first_y = first_vars
            .iter()
            .filter(|var| var.name == "y")
            .collect::<Vec<_>>();
        assert!(
            first_y.len() >= 2,
            "y must occur as binder and use: {first_vars:?}"
        );
        assert!(first_y.iter().all(|var| var.binding == first_y[0].binding));
        assert_ne!(first_x[0].binding, first_y[0].binding);

        let second_vars = rule_vars(second);
        let second_x = second_vars
            .iter()
            .find(|var| var.name == "x")
            .expect("second rule x");
        assert_ne!(first_x[0].binding, second_x.binding);
    }

    #[test]
    fn generated_symbols_and_binding_ids_are_unique_and_survive_pop() {
        let mut symbols = SymbolGen::new("@".to_owned());
        let first = symbols.fresh("f1");
        let second = symbols.fresh("f");
        let third = symbols.fresh("f");
        assert_eq!(
            crate::util::HashSet::from_iter([first, second, third]).len(),
            3,
            "different fresh-name hints must not converge on one diagnostic name"
        );

        let call = ResolvedCall::Func(FuncType {
            identity: CallableIdentity::Function(symbols.fresh_function_registration_id()),
            name: "temp".to_owned(),
            subtype: FunctionSubtype::Custom,
            input: vec![],
            outputs: vec![I64Sort.to_arcsort()],
        });
        let left = <SymbolGen as FreshGen<ResolvedCall, ResolvedVar>>::fresh(&mut symbols, &call);
        let right = <SymbolGen as FreshGen<ResolvedCall, ResolvedVar>>::fresh(&mut symbols, &call);
        assert_ne!(left.name, right.name);
        assert_ne!(left.binding, right.binding);

        let mut egraph = EGraph::default();
        egraph.push();
        let scoped = egraph.parser.symbol_gen.fresh_resolved_binding_id();
        egraph.pop().unwrap();
        let later = egraph.parser.symbol_gen.fresh_resolved_binding_id();
        assert!(later.ordinal() > scoped.ordinal());
    }

    #[test]
    fn tuple_merge_stamps_asymmetric_columns_and_let_slot() {
        let mut egraph = EGraph::new_compile_only(false);
        let resolved = egraph
            .resolve_program_compile_only(
                None,
                r#"
                (function asymmetric (i64) (i64 i64)
                  :merge ((let chosen (max old0 new0))
                          (values chosen old1)))
                "#,
            )
            .unwrap();
        let merge = resolved
            .execution
            .iter()
            .find_map(|command| match &command.command {
                ResolvedNCommand::Function(function) if function.name == "asymmetric" => {
                    function.merge.as_ref()
                }
                _ => None,
            })
            .expect("resolved asymmetric merge");

        let [GenericAction::Let(_, let_var, GenericExpr::Call(_, _, let_args))] =
            merge.actions.0.as_slice()
        else {
            panic!("expected one resolved merge let: {:?}", merge.actions);
        };
        assert_eq!(let_var.binding, ResolvedVarBinding::MergeLet { slot: 0 });
        let [GenericExpr::Var(_, old0), GenericExpr::Var(_, new0)] = let_args.as_slice() else {
            panic!("expected old0/new0 operands: {let_args:?}");
        };
        assert_eq!(old0.binding, ResolvedVarBinding::MergeOld { column: 0 });
        assert_eq!(new0.binding, ResolvedVarBinding::MergeNew { column: 0 });

        let GenericExpr::Call(_, ResolvedCall::Values(_), result_columns) = &merge.result else {
            panic!("expected tuple merge result: {:?}", merge.result);
        };
        let [GenericExpr::Var(_, chosen), GenericExpr::Var(_, old1)] = result_columns.as_slice()
        else {
            panic!("expected asymmetric chosen/old1 result: {result_columns:?}");
        };
        assert_eq!(chosen.binding, ResolvedVarBinding::MergeLet { slot: 0 });
        assert_eq!(old1.binding, ResolvedVarBinding::MergeOld { column: 1 });
    }

    #[test]
    fn merge_let_shadowing_a_global_preserves_rhs_global_authority() {
        let mut egraph = EGraph::new_compile_only(false);
        let resolved = egraph
            .resolve_program_compile_only(
                None,
                r#"
                (let $g 7)
                (function f (i64) i64
                  :merge ((let $g (+ $g 1)) $g))
                "#,
            )
            .unwrap();
        let merge = resolved
            .execution
            .iter()
            .find_map(|command| match &command.command {
                ResolvedNCommand::Function(function) if function.name == "f" => {
                    function.merge.as_ref()
                }
                _ => None,
            })
            .expect("resolved merge");

        let [GenericAction::Let(_, binding, rhs)] = merge.actions.0.as_slice() else {
            panic!("expected one merge let: {:?}", merge.actions);
        };
        assert_eq!(binding.binding, ResolvedVarBinding::MergeLet { slot: 0 });
        let GenericExpr::Call(_, ResolvedCall::Primitive(_), arguments) = rhs else {
            panic!("expected the resolved addition RHS: {rhs:?}");
        };
        let [
            GenericExpr::Call(_, ResolvedCall::Func(global), global_args),
            GenericExpr::Lit(..),
        ] = arguments.as_slice()
        else {
            panic!("expected the earlier global to lower to a nullary call: {arguments:?}");
        };
        assert_eq!(global.name, "$g");
        assert!(global_args.is_empty());
        let GenericExpr::Var(_, result) = &merge.result else {
            panic!(
                "expected the merge result to use its local binding: {:?}",
                merge.result
            );
        };
        assert_eq!(result.binding, ResolvedVarBinding::MergeLet { slot: 0 });
    }

    #[test]
    fn merge_let_shadowing_a_different_sort_global_resolves_locally() {
        let mut egraph = EGraph::new_compile_only(false);
        let resolved = egraph
            .resolve_program_compile_only(
                None,
                r#"
                (let $g "global")
                (function f (i64) i64
                  :merge ((let $g old) $g))
                "#,
            )
            .unwrap();
        let merge = resolved
            .execution
            .iter()
            .find_map(|command| match &command.command {
                ResolvedNCommand::Function(function) if function.name == "f" => {
                    function.merge.as_ref()
                }
                _ => None,
            })
            .expect("resolved merge");

        let [GenericAction::Let(_, binder, GenericExpr::Var(_, old))] = merge.actions.0.as_slice()
        else {
            panic!("expected one merge let over old: {:?}", merge.actions);
        };
        assert_eq!(old.binding, ResolvedVarBinding::MergeOld { column: 0 });
        assert_eq!(old.sort.name(), "i64");
        assert_eq!(binder.binding, ResolvedVarBinding::MergeLet { slot: 0 });
        assert_eq!(binder.sort.name(), "i64");
        let GenericExpr::Var(_, result) = &merge.result else {
            panic!("expected merge-local result: {:?}", merge.result);
        };
        assert_eq!(result.binding, binder.binding);
        assert_eq!(result.sort.name(), "i64");
    }

    #[test]
    fn nested_merge_expression_specializes_from_local_not_same_named_global() {
        let mut egraph = EGraph::new_compile_only(false);
        let resolved = egraph
            .resolve_program_compile_only(
                None,
                r#"
                (let $g "global")
                (function f (i64) i64
                  :merge ((let $g old) (+ $g 1)))
                "#,
            )
            .unwrap();
        let merge = resolved
            .execution
            .iter()
            .find_map(|command| match &command.command {
                ResolvedNCommand::Function(function) if function.name == "f" => {
                    function.merge.as_ref()
                }
                _ => None,
            })
            .expect("resolved merge");
        let [GenericAction::Let(_, binder, _)] = merge.actions.0.as_slice() else {
            panic!("expected one merge let: {:?}", merge.actions);
        };
        let GenericExpr::Call(_, ResolvedCall::Primitive(add), arguments) = &merge.result else {
            panic!("expected resolved local addition: {:?}", merge.result);
        };
        let [GenericExpr::Var(_, local), GenericExpr::Lit(..)] = arguments.as_slice() else {
            panic!("expected merge-local addition arguments: {arguments:?}");
        };
        assert_eq!(local.binding, binder.binding);
        assert_eq!(local.sort.name(), "i64");
        assert_eq!(
            add.input()
                .iter()
                .map(|sort| sort.name())
                .collect::<Vec<_>>(),
            ["i64", "i64"]
        );
        assert_eq!(add.output().name(), "i64");
    }

    #[test]
    fn rejected_global_shadow_preserves_first_sort_and_function_authority() {
        let mut egraph = EGraph::default();
        egraph.parse_and_run_program(None, "(let $g 1)").unwrap();
        let first_sort = egraph
            .type_info
            .get_global_sort("$g")
            .unwrap()
            .name()
            .to_owned();
        let first_function = egraph.type_info.get_global_function_id("$g").unwrap();

        let error = egraph
            .parse_and_run_program(None, "(let $g \"rejected\")")
            .unwrap_err();
        assert!(matches!(error, Error::Shadowing(..)));
        assert_eq!(
            egraph.type_info.get_global_sort("$g").unwrap().name(),
            first_sort
        );
        assert_eq!(
            egraph.type_info.get_global_function_id("$g"),
            Some(first_function)
        );
        egraph
            .parse_and_run_program(None, "(check (= $g 1))")
            .unwrap();
    }

    #[test]
    fn rejected_function_declaration_does_not_publish_catalog_authority() {
        let mut egraph = EGraph::default();
        let invalid = desugar_program(&mut egraph, "(function retry (i64) (i64 i64) :merge old0)");
        let error = egraph.typecheck_program(&invalid).unwrap_err();
        assert!(matches!(error, TypeError::TupleMergeNotValues(name, _) if name == "retry"));
        assert!(egraph.type_info.get_func_type("retry").is_none());

        let corrected = desugar_program(
            &mut egraph,
            "(function retry (i64) (i64 i64) :merge (values old0 new1))",
        );
        egraph.typecheck_program(&corrected).unwrap();
        assert!(egraph.type_info.get_func_type("retry").is_some());
    }

    #[test]
    fn value_eq_authority_ignores_same_name_registration_decoy() {
        use crate::core::ResolvedRuleExt;

        let mut egraph = EGraph::new_compile_only(false);
        let exact = egraph
            .type_info
            .value_eq_primitive()
            .expect("built-in value-eq authority")
            .registration_id();

        // Same implementation, spelling, and polymorphic schema; only the
        // explicit registration authority differs.
        egraph.add_pure_primitive(ValueEqPrimitive, None);
        let overloads = egraph.type_info.primitives.get_mut("value-eq").unwrap();
        let decoy = overloads.pop().expect("newly appended decoy");
        assert_ne!(decoy.registration_id(), exact);
        overloads.insert(0, decoy);
        assert_eq!(
            egraph
                .type_info
                .value_eq_primitive()
                .expect("authority survives decoy")
                .registration_id(),
            exact
        );
        assert_ne!(
            egraph.type_info.get_prims("value-eq").unwrap()[0].registration_id(),
            exact,
            "the test must put the decoy in the legacy positional slot"
        );

        let resolved = egraph
            .resolve_program_compile_only(None, "(rule ((= 1 2)) ())")
            .unwrap();
        let rule = resolved
            .execution
            .iter()
            .find_map(|command| match &command.command {
                ResolvedNCommand::NormRule { rule } => Some(rule),
                _ => None,
            })
            .expect("resolved literal-equality rule");
        let mut fresh = egraph.parser.symbol_gen.clone();
        let core = rule
            .to_canonicalized_core_rule(&egraph.type_info, &mut fresh, false)
            .unwrap();
        let [atom] = core.body.atoms.as_slice() else {
            panic!(
                "expected one canonical value-eq atom: {:?}",
                core.body.atoms
            );
        };
        let ResolvedCall::Primitive(value_eq) = &atom.head else {
            panic!("expected canonical value-eq primitive: {:?}", atom.head);
        };
        assert_eq!(value_eq.registration_id(), exact);
    }
}
