use std::hash::Hasher;

use crate::Context;
use crate::proofs::proof_container_rebuild::register_container_rebuild_from_spec;
use crate::{
    core::{CoreActionContext, CoreRule, GenericActionsExt, ResolvedCall},
    *,
};
use ast::{
    MappedExprExt, ResolvedAction, ResolvedExpr, ResolvedFact, ResolvedRule, ResolvedVar, Rule,
    RuleEvalMode,
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

#[derive(Clone, Debug)]
pub struct FuncType {
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
        if self.name == other.name
            && self.subtype == other.subtype
            && self.num_outputs() == other.num_outputs()
            && self
                .outputs
                .iter()
                .zip(other.outputs.iter())
                .all(|(a, b)| a.name() == b.name())
        {
            if self.input.len() != other.input.len() {
                return false;
            }
            for (a, b) in self.input.iter().zip(other.input.iter()) {
                if a.name() != b.name() {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }
}

impl Eq for FuncType {}

impl Hash for FuncType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.subtype.hash(state);
        for out in &self.outputs {
            out.name().hash(state);
        }
        for inp in &self.input {
            inp.name().hash(state);
        }
    }
}
/// Validators take a termdag and arguments (as TermIds) and return
/// a newly computed TermId if the primitive application is valid,
/// or None if it is invalid.
pub type PrimitiveValidator = Arc<dyn Fn(&mut TermDag, &[TermId]) -> Option<TermId> + Send + Sync>;

#[derive(Clone)]
pub struct PrimitiveWithId {
    pub(crate) primitive: Arc<dyn Primitive>,
    pub(crate) validator: Option<PrimitiveValidator>,
    /// Runtime entrypoints for the contexts this primitive is valid in.
    /// The primitive definition is stored once, while each context keeps
    /// its own runtime id so higher-order dispatch can still recover the
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
    func_types: HashMap<String, Arc<FuncType>>,
    /// Monotonic, name-local invalidation stamps for exact call-resolution
    /// caches. Only registrations for a head advance that head's stamp.
    call_generations: HashMap<String, u64>,
    /// Monotonic invalidation stamp for primitive constraints, which receive
    /// the complete `TypeInfo` and may therefore depend on registrations under
    /// names other than their own head.
    semantic_epoch: u64,
    pub(crate) global_sorts: HashMap<String, ArcSort>,
    /// Sorts that do not allow union (e.g., from `:no-union` sorts or relations).
    pub(crate) non_unionable_sorts: HashSet<String>,
    /// Declared indexes, by the name their atoms are written with.
    pub(crate) indexes: HashMap<String, IndexInfo>,
}

/// A declared index: a read-only relation over the rows of `function`, holding
/// each value appearing in `any_of` followed by the whole row.
#[derive(Clone, Debug)]
pub struct IndexInfo {
    pub function: String,
    /// Column indices of `function`'s row (its inputs then its outputs), read
    /// disjunctively.
    pub any_of: Vec<usize>,
}

/// Fully validated state for one index declaration. Keeping construction
/// separate from commit makes the no-partial-registration boundary explicit
/// for both source commands and the generated binder.
pub(crate) struct PreparedIndex {
    function_type: Arc<FuncType>,
    info: IndexInfo,
}

pub(crate) struct SortDeclarationMetadata<'a> {
    pub(crate) span: &'a Span,
    pub(crate) name: &'a str,
    pub(crate) uf: &'a Option<(String, Option<String>)>,
    pub(crate) container_rebuild: &'a Option<ContainerRebuildSpec>,
    pub(crate) proof_constructors: &'a Option<ProofConstructorNames>,
    pub(crate) unionable: bool,
}

// These methods need to be on the `EGraph` in order to register sorts and
// primitives with the runtime.
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
        let sort = self.prepare_sort_declaration(name.into(), presort_and_args, &span)?;
        self.commit_arcsort(sort, span)
    }

    /// Validate and construct a declared sort without mutating the backend.
    /// The currently registered presort constructors only inspect `TypeInfo`;
    /// presort construction deliberately precedes duplicate-sort detection to
    /// preserve the source language's existing error ordering.
    pub(crate) fn prepare_sort_declaration(
        &mut self,
        name: String,
        presort_and_args: &Option<(String, Vec<Expr>)>,
        span: &Span,
    ) -> Result<ArcSort, TypeError> {
        if self.type_info.func_types.contains_key(&name) {
            return Err(TypeError::FunctionAlreadyBound(name, span.clone()));
        }

        let sort = match presort_and_args {
            None => Arc::new(EqSort { name }),
            Some((presort, args)) => {
                if let Some(mksort) = self.type_info.mksorts.get(presort) {
                    mksort(&mut self.type_info, name, args, span.clone())?
                } else {
                    return Err(TypeError::PresortNotFound(presort.clone(), span.clone()));
                }
            }
        };
        if self.type_info.sorts.contains_key(sort.name()) {
            return Err(TypeError::SortAlreadyBound(
                sort.name().to_owned(),
                span.clone(),
            ));
        }
        Ok(sort)
    }

    /// Add a user-defined sort to the e-graph.
    pub fn add_arcsort(&mut self, sort: ArcSort, span: Span) -> Result<(), TypeError> {
        if self.type_info.sorts.contains_key(sort.name()) {
            return Err(TypeError::SortAlreadyBound(sort.name().to_owned(), span));
        }
        self.commit_arcsort(sort, span)
    }

    /// Commit one fully prepared sort. Duplicate detection is repeated here so
    /// every caller is guaranteed to fail before `register_type` mutates the
    /// backend, even if preparation and commit are separated by other work.
    fn commit_arcsort(&mut self, sort: ArcSort, span: Span) -> Result<(), TypeError> {
        let name = sort.name().to_owned();
        if self.type_info.sorts.contains_key(&name) {
            return Err(TypeError::SortAlreadyBound(name, span));
        }
        sort.register_type(&mut self.backend);
        self.type_info.sorts.insert(name, sort.clone());
        self.type_info.bump_semantic_epoch();
        // A sort's primitives already reach the term-encoding typechecker
        // through its OWN `add_arcsort` when it typechecks the sort command, so
        // don't propagate them again from here (that would double-register and
        // make primitive resolution ambiguous). Detach only while the sort
        // installs its own primitives; declaration-specific UF/container
        // primitives are registered after restoration and intentionally
        // propagate through the checker chain.
        let saved = self.proof_state.original_typechecking.take();
        sort.register_primitives(self);
        self.proof_state.original_typechecking = saved;
        Ok(())
    }

    /// Commit a prepared sort and all metadata carried by a normalized sort
    /// declaration. Intrinsic sort primitives are installed with the source
    /// checker detached by `commit_arcsort`; declaration-specific UF and
    /// container primitives run after it has been restored and therefore
    /// propagate through the complete proof-mode checker chain.
    pub(crate) fn register_prepared_sort_declaration(
        &mut self,
        sort: ArcSort,
        metadata: SortDeclarationMetadata<'_>,
    ) -> Result<(), TypeError> {
        debug_assert_eq!(
            sort.name(),
            metadata.name,
            "prepared sort name must be stable"
        );
        self.commit_arcsort(sort, metadata.span.clone())?;

        if !metadata.unionable {
            self.type_info
                .non_unionable_sorts
                .insert(metadata.name.to_owned());
            self.type_info.bump_semantic_epoch();
        }
        if let Some((uf_ctor, _uf_index)) = metadata.uf {
            self.proof_state
                .uf_parent
                .insert(metadata.name.to_owned(), uf_ctor.clone());
            let proofs = self
                .type_info
                .sorts
                .contains_key(&self.proof_state.proof_names.proof_datatype);
            crate::proofs::proof_container_rebuild::register_uf_canon(
                self,
                metadata.name,
                uf_ctor,
                proofs,
            );
        }
        if let Some(pc) = metadata.proof_constructors {
            let names = &mut self.proof_state.proof_names;
            names.proof_datatype = metadata.name.to_owned();
            names.congr_constructor = pc.congr.clone();
            names.congr_all_constructor = pc.congr_all.clone();
            names.eq_trans_constructor = pc.trans.clone();
            names.eq_sym_constructor = pc.sym.clone();
            names.container_normalize_constructor = pc.normalize.clone();
            names.fiat_prefix = pc.fiat.clone();
            names.proj_constructor = pc.proj.clone();
            names.proj_all_prefix = pc.proj_all.clone();
        }
        if let Some(spec) = metadata.container_rebuild {
            register_container_rebuild_from_spec(self, metadata.name, spec);
        }
        Ok(())
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
            PureState::valid_contexts(),
            |egraph, x, ctx| {
                egraph.register_external_func(Box::new(PurePrimWrapper { prim: x, ctx }))
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
            WriteState::valid_contexts(),
        );
    }

    /// Register a [`ReadPrim`]. Pass `None` for the validator if not
    /// using the proof checker.
    pub fn add_read_primitive<T>(&mut self, x: T, validator: Option<PrimitiveValidator>)
    where
        T: ReadPrim + Clone,
    {
        self.register_registry_primitive::<T, WrapRead>(x, validator, ReadState::valid_contexts());
    }

    /// Register a [`FullPrim`]. Pass `None` for the validator if not
    /// using the proof checker.
    pub fn add_full_primitive<T>(&mut self, x: T, validator: Option<PrimitiveValidator>)
    where
        T: FullPrim + Clone,
    {
        self.register_registry_primitive::<T, WrapFull>(x, validator, FullState::valid_contexts());
    }

    fn register_registry_primitive<T, S>(
        &mut self,
        x: T,
        validator: Option<PrimitiveValidator>,
        valid_ctxs: &[Context],
    ) where
        T: Primitive + Clone,
        S: RegistryWrap<T> + 'static,
    {
        self.register_per_context(x, validator, valid_ctxs, |egraph, x, ctx| {
            let registry = egraph.action_registry().clone();
            egraph.register_external_func(Box::new(RegistryPrimWrapper::<T, S> {
                prim: x,
                registry,
                ctx,
                _wrap: std::marker::PhantomData,
            }))
        });
    }

    /// Register an internal term-encoding primitive. `prim` supplies only the
    /// type constraints; `make_id` creates its runtime entrypoint on each
    /// e-graph in the typechecker chain.
    pub(crate) fn add_internal_primitive<T, F>(
        &mut self,
        prim: T,
        valid_ctxs: &[Context],
        mut make_id: F,
    ) where
        T: Primitive + Clone,
        F: FnMut(&mut egglog_bridge::EGraph, Context) -> ExternalFunctionId,
    {
        self.register_per_context(prim, None, valid_ctxs, move |egraph, _x, ctx| {
            make_id(egraph, ctx)
        });
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
        valid_ctxs: &[Context],
        mut build_wrapper: F,
    ) where
        T: Primitive + Clone,
        F: FnMut(&mut egglog_bridge::EGraph, T, Context) -> ExternalFunctionId,
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
                valid_ctxs
                    .contains(&ctx)
                    .then(|| build_wrapper(&mut eg.backend, x.clone(), ctx))
            });
            eg.type_info
                .primitives
                .entry(name.clone())
                .or_default()
                .push(PrimitiveWithId {
                    primitive,
                    validator: validator.clone(),
                    context_ids,
                });
            eg.type_info.bump_call_generation(&name);
            eg.type_info.bump_semantic_epoch();
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
    pub(crate) fn prepare_index_declaration(
        &self,
        span: &Span,
        name: &str,
        function: &str,
        any_of: &[usize],
    ) -> Result<PreparedIndex, TypeError> {
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
            .ok_or_else(|| TypeError::UnboundFunction(function.to_owned(), span.clone()))?;
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
        Ok(PreparedIndex {
            function_type: Arc::new(FuncType {
                name: name.to_owned(),
                subtype: FunctionSubtype::Custom,
                input,
                outputs: vec![unit],
            }),
            info: IndexInfo {
                function: function.to_owned(),
                any_of: any_of.to_vec(),
            },
        })
    }

    /// Commit a fully validated index. The duplicate check is repeated so a
    /// caller that separates preparation from commit still cannot replace a
    /// declaration or advance its generation.
    pub(crate) fn commit_index_declaration(
        &mut self,
        span: &Span,
        prepared: PreparedIndex,
    ) -> Result<(), TypeError> {
        let name = prepared.function_type.name.clone();
        if self.type_info.func_types.contains_key(&name) {
            return Err(TypeError::FunctionAlreadyBound(name, span.clone()));
        }
        self.type_info
            .func_types
            .insert(name.clone(), prepared.function_type);
        self.type_info.bump_call_generation(&name);
        self.type_info.bump_semantic_epoch();
        self.type_info.indexes.insert(name, prepared.info);
        self.type_info.bump_semantic_epoch();
        Ok(())
    }

    /// Validate and register a function declaration, including the generated
    /// proof-encoding primitives and global metadata attached to special
    /// internal functions. The registration is intentionally shared by source
    /// typechecking and the exact-key generated binder.
    pub(crate) fn register_function_declaration(
        &mut self,
        fdecl: &FunctionDecl,
    ) -> Result<ResolvedFunctionDecl, TypeError> {
        let resolved = self
            .type_info
            .typecheck_function(&mut self.parser.symbol_gen, fdecl)?;
        self.register_resolved_function_metadata(&resolved);
        Ok(resolved)
    }

    /// Install the runtime primitives and global metadata implied by an
    /// already committed function type. Both source typechecking and the
    /// generated binder call this after their respective merge binders have
    /// committed the declaration.
    pub(crate) fn register_resolved_function_metadata(&mut self, resolved: &ResolvedFunctionDecl) {
        // An FD view (function carrying `term_constructor` with a tuple
        // `(eclass, proof)` output) gets a `set-if-empty` primitive (+ a
        // proof-column reader) so the encoding can canonicalize a term to
        // the view's e-class at insertion time. Registered here so it survives
        // re-parse of the desugared program.
        if resolved.term_constructor.is_some()
            && let ResolvedCall::Func(ft) = &resolved.resolved_schema
            && ft.outputs.len() >= 2
        {
            let (name, input, outputs) =
                (resolved.name.clone(), ft.input.clone(), ft.outputs.clone());
            crate::proofs::proof_fresh::register_set_if_empty(self, &name, input, outputs);
        }
        // A term-node relation (a term or proof node, whose last input is
        // the minted id) gets a mint primitive, so the encoding writes a
        // node in one statement. Registered here for the same reason as
        // `set-if-empty` above.
        if resolved.internal_term_node
            && let ResolvedCall::Func(ft) = &resolved.resolved_schema
            && let Some((id_sort, arg_sorts)) = ft.input.split_last()
            && id_sort.is_eq_sort()
        {
            // `register_mint` stages one `Unit` value column, so a term-node
            // relation must declare exactly that.
            debug_assert!(
                matches!(ft.outputs.as_slice(), [out] if out.name() == "Unit"),
                "term-node relation `{}` must declare one `Unit` value column, got {:?}",
                resolved.name,
                ft.outputs.iter().map(|out| out.name()).collect::<Vec<_>>(),
            );
            let (name, id_sort, arg_sorts) =
                (resolved.name.clone(), id_sort.clone(), arg_sorts.to_vec());
            crate::proofs::proof_fresh::register_mint(self, &name, arg_sorts, id_sort);
        }
        // If this is a let binding, add it to global_sorts. This preserves
        // behavior for lets after desugaring.
        if resolved.internal_let {
            let output_sort = self
                .type_info
                .sorts
                .get(resolved.schema.output())
                .cloned()
                .unwrap();
            self.type_info
                .register_global_sort(resolved.name.clone(), output_sort);
        }
    }

    fn typecheck_command(&mut self, command: &NCommand) -> Result<ResolvedNCommand, TypeError> {
        if let NCommand::Function(fdecl) = command {
            return Ok(ResolvedNCommand::Function(
                self.register_function_declaration(fdecl)?,
            ));
        }
        let symbol_gen = &mut self.parser.symbol_gen;

        let command: ResolvedNCommand = match command {
            NCommand::Function(_) => unreachable!("function declarations return above"),
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
                container_rebuild,
                proof_constructors,
                unionable,
            } => {
                // Note this is bad since typechecking should be pure and idempotent
                // Otherwise typechecking the same program twice will fail
                let sort = self.prepare_sort_declaration(name.clone(), presort_and_args, span)?;
                self.register_prepared_sort_declaration(
                    sort,
                    SortDeclarationMetadata {
                        span,
                        name,
                        uf,
                        container_rebuild,
                        proof_constructors,
                        unionable: *unionable,
                    },
                )?;
                ResolvedNCommand::Sort {
                    span: span.clone(),
                    name: name.clone(),
                    presort_and_args: presort_and_args.clone(),
                    uf: uf.clone(),
                    container_rebuild: container_rebuild.clone(),
                    proof_constructors: proof_constructors.clone(),
                    unionable: *unionable,
                }
            }
            NCommand::CoreAction(action @ Action::Let(span, var, _)) => {
                let action = self.type_info.typecheck_standalone_action(
                    symbol_gen,
                    action,
                    &Default::default(),
                    Context::Full,
                )?;
                self.ensure_global_name_prefix(span, var)?;
                let ResolvedAction::Let(_, resolved_var, _) = &action else {
                    unreachable!("typechecking an Action::Let should return ResolvedAction::Let")
                };
                self.type_info
                    .register_global_sort(resolved_var.name.clone(), resolved_var.sort.clone());
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
                self.ensure_global_name_prefix(span, name)?;
                // The parser guarantees a trailing expression; its type is the
                // global's.
                let Some(ResolvedAction::Expr(_, value)) = resolved.0.last() else {
                    unreachable!("(let _ (begin ...)) must end with an expression")
                };
                let sort = value.output_type();
                self.type_info
                    .register_global_sort(name.clone(), sort.clone());
                let resolved_var = ResolvedVar {
                    name: name.clone(),
                    sort,
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
            NCommand::Push(span, n) => ResolvedNCommand::Push(span.clone(), *n),
            NCommand::Index {
                span,
                name,
                function,
                any_of,
            } => {
                let prepared = self.prepare_index_declaration(span, name, function, any_of)?;
                self.commit_index_declaration(span, prepared)?;
                ResolvedNCommand::Index {
                    span: span.clone(),
                    name: name.clone(),
                    function: function.clone(),
                    any_of: any_of.clone(),
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
            self.validate_rule_variable_prefixes(rule)?;
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

    pub(crate) fn validate_rule_variable_prefixes(
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
    fn bump_semantic_epoch(&mut self) {
        self.semantic_epoch = self
            .semantic_epoch
            .checked_add(1)
            .expect("type-info semantic epoch overflow");
    }

    fn bump_call_generation(&mut self, head: &str) {
        let generation = self.call_generations.entry(head.to_owned()).or_default();
        *generation = generation
            .checked_add(1)
            .expect("call-resolution generation overflow");
    }

    /// Return the complete invalidation stamp for one exact-call cache entry.
    /// Function-only resolutions depend on the head-local generation, while
    /// primitive constraints may additionally observe any TypeInfo mutation.
    pub(crate) fn call_cache_stamp(
        &self,
        head: &str,
        primitive_sensitive: bool,
    ) -> (u64, Option<u64>) {
        (
            self.call_generations.get(head).copied().unwrap_or_default(),
            primitive_sensitive.then_some(self.semantic_epoch),
        )
    }

    /// Register a global and advance the primitive-resolution epoch as one
    /// indivisible mutation boundary. Primitive constraints receive all of
    /// `TypeInfo`, so even a global under an unrelated name can change which
    /// overload accepts an otherwise identical signature. Replacement bumps
    /// unconditionally: a custom constraint can observe the registered
    /// `ArcSort`, not merely its name, so equal-looking values are not a sound
    /// cache-equivalence test.
    pub(crate) fn register_global_sort(&mut self, name: String, sort: ArcSort) {
        self.global_sorts.insert(name, sort);
        self.bump_semantic_epoch();
    }

    /// Adds a sort constructor to the typechecker's known set of types.
    pub fn add_presort<S: Presort>(&mut self, span: Span) -> Result<(), TypeError> {
        let name = S::presort_name();
        match self.mksorts.entry(name.to_owned()) {
            HEntry::Occupied(_) => Err(TypeError::SortAlreadyBound(name.to_owned(), span)),
            HEntry::Vacant(e) => {
                e.insert(S::make_sort);
                self.reserved_primitives.extend(S::reserved_primitives());
                self.bump_semantic_epoch();
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

    /// Validate all declaration metadata that does not depend on the merge and
    /// construct its portable schema in this checker universe. No provisional
    /// function entry is installed until the caller begins merge binding.
    pub(crate) fn prepare_function_type(
        &self,
        func: &FunctionDecl,
    ) -> Result<Arc<FuncType>, TypeError> {
        if self.sorts.contains_key(&func.name) {
            return Err(TypeError::SortAlreadyBound(
                func.name.clone(),
                func.span.clone(),
            ));
        }
        if self.is_primitive(&func.name) {
            return Err(TypeError::PrimitiveAlreadyBound(
                func.name.clone(),
                func.span.clone(),
            ));
        }
        // View tables (with term_constructor) must have at least one input (the e-class), except
        // proof-mode functional-dependency tuple views, which key on children only.
        if func.term_constructor.is_some()
            && func.schema.input.is_empty()
            && !func.schema.is_tuple_output()
        {
            return Err(TypeError::TermConstructorNoInputs(
                func.name.clone(),
                func.span.clone(),
            ));
        }
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

        let ftype = Arc::new(FuncType {
            name: func.name.clone(),
            subtype: func.subtype,
            input,
            outputs,
        });
        if self.func_types.contains_key(&func.name) {
            return Err(TypeError::FunctionAlreadyBound(
                func.name.clone(),
                func.span.clone(),
            ));
        }
        if func.schema.is_tuple_output() && func.subtype == FunctionSubtype::Constructor {
            return Err(TypeError::TupleOutputNotAllowed(
                func.name.clone(),
                func.span.clone(),
            ));
        }
        if func.subtype == FunctionSubtype::Constructor && !ftype.outputs[0].is_eq_sort() {
            return Err(TypeError::ConstructorOutputNotSort(
                func.name.clone(),
                func.span.clone(),
            ));
        }
        Ok(ftype)
    }

    /// Make a prepared function visible while its merge is bound, then either
    /// roll the entry back on error or commit it and advance that head's call
    /// generation. Insertion and rollback also advance the semantic epoch
    /// because primitive constraints may inspect the provisional function. The
    /// closure receives an immutable checker so it cannot accidentally perform
    /// unrelated registration inside the provisional window.
    pub(crate) fn bind_with_provisional_function<T, E>(
        &mut self,
        ftype: Arc<FuncType>,
        bind: impl FnOnce(&TypeInfo) -> Result<T, E>,
    ) -> Result<T, E> {
        let name = ftype.name.clone();
        let previous = self.func_types.insert(name.clone(), ftype);
        self.bump_semantic_epoch();
        debug_assert!(
            previous.is_none(),
            "function preparation rejects duplicates"
        );
        match bind(self) {
            Ok(value) => {
                self.bump_call_generation(&name);
                Ok(value)
            }
            Err(error) => {
                let removed = self.func_types.remove(&name);
                debug_assert!(removed.is_some(), "provisional function must exist");
                self.bump_semantic_epoch();
                Err(error)
            }
        }
    }

    fn typecheck_function(
        &mut self,
        symbol_gen: &mut SymbolGen,
        fdecl: &FunctionDecl,
    ) -> Result<ResolvedFunctionDecl, TypeError> {
        let ftype = self.prepare_function_type(fdecl)?;
        let outputs = ftype.outputs.clone();
        let is_tuple = fdecl.schema.is_tuple_output();
        let merge = if let Some(merge) = &fdecl.merge {
            let symbol_gen_checkpoint = symbol_gen.checkpoint();

            // For single-output functions the merge expression refers to `old`/`new`. For
            // tuple-output functions it refers to `old0`, `new0`, `old1`, ... (one pair per
            // output column), and the whole merge is a `(values ...)` form.
            let mut bound_vars = IndexMap::default();
            let tuple_var_names: Vec<(String, String)> = (0..outputs.len())
                .map(|i| (format!("old{i}"), format!("new{i}")))
                .collect();
            if is_tuple {
                for (i, (old_name, new_name)) in tuple_var_names.iter().enumerate() {
                    bound_vars.insert(old_name.as_str(), (fdecl.span.clone(), outputs[i].clone()));
                    bound_vars.insert(new_name.as_str(), (fdecl.span.clone(), outputs[i].clone()));
                }
            } else {
                bound_vars.insert("old", (fdecl.span.clone(), outputs[0].clone()));
                bound_vars.insert("new", (fdecl.span.clone(), outputs[0].clone()));
            }

            // A `:merge` is a value-producing action block: the `actions` run (writes are
            // allowed, but live DB reads would be untracked by seminaive rule execution), then
            // `result` produces the merged value(s).
            let merge_result = self.bind_with_provisional_function(
                ftype.clone(),
                |type_info| -> Result<Option<ResolvedMerge>, TypeError> {
                    let actions = type_info.typecheck_standalone_actions(
                        symbol_gen,
                        &merge.actions,
                        &bound_vars,
                        Context::Write,
                    )?;
                    let let_bindings: Vec<(String, Span, ArcSort)> = actions
                        .0
                        .iter()
                        .filter_map(|action| match action {
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
                        type_info.typecheck_tuple_merge(
                            symbol_gen,
                            fdecl,
                            &merge.result,
                            &outputs,
                            &result_scope,
                        )?
                    } else {
                        type_info.typecheck_standalone_expr(
                            symbol_gen,
                            &merge.result,
                            &result_scope,
                            Context::Write,
                        )?
                    };
                    Ok(Some(ResolvedMerge { actions, result }))
                },
            );
            match merge_result {
                Ok(merge) => {
                    symbol_gen.commit(symbol_gen_checkpoint);
                    merge
                }
                Err(error) => {
                    symbol_gen.rollback(symbol_gen_checkpoint);
                    return Err(error);
                }
            }
        } else {
            self.bind_with_provisional_function(ftype.clone(), |_| {
                Ok::<Option<ResolvedMerge>, TypeError>(None)
            })?
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
            let resolved =
                self.typecheck_standalone_expr(symbol_gen, arg, bound_vars, Context::Write)?;
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

    pub(crate) fn typecheck_schedule(
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

    pub(crate) fn typecheck_rule(
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

        let body: Vec<ResolvedFact> = assignment.annotate_facts(&mapped_query, self, query_ctx)?;
        let actions: ResolvedActions =
            assignment.annotate_actions(&mapped_action, self, action_ctx)?;

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

    pub(crate) fn check_no_function_lookups_in_actions(
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
        let annotated_facts = assignment.annotate_facts(&mapped_facts, self, Context::Read)?;
        Ok(annotated_facts)
    }

    // Standalone expressions/actions use action lowering. Top-level commands
    // pass `Full`; function `:merge` reuses this path with `Write` because
    // merge expressions run during table updates.
    pub(crate) fn typecheck_standalone_actions(
        &self,
        symbol_gen: &mut SymbolGen,
        actions: &Actions,
        binding: &IndexMap<&str, (Span, ArcSort)>,
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

        let annotated_actions = assignment.annotate_actions(&mapped_action, self, context)?;
        Ok(annotated_actions)
    }

    pub(crate) fn typecheck_standalone_expr(
        &self,
        symbol_gen: &mut SymbolGen,
        expr: &Expr,
        binding: &IndexMap<&str, (Span, ArcSort)>,
        context: Context,
    ) -> Result<ResolvedExpr, TypeError> {
        let action = Action::Expr(expr.span(), expr.clone());
        let typechecked_action =
            self.typecheck_standalone_action(symbol_gen, &action, binding, context)?;
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
        let output_atom = mapped_expr.get_corresponding_var_or_lit(self);
        problem.add_binding(output_atom, output_sort.clone());

        let assignment = problem
            .solve(|sort: &ArcSort| sort.name())
            .map_err(|e| e.to_type_error())?;

        let annotated_actions = assignment.annotate_actions(&mapped_action, self, context)?;
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

    pub fn get_func_type(&self, sym: &str) -> Option<&Arc<FuncType>> {
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

    pub fn is_global(&self, sym: &str) -> bool {
        self.global_sorts.contains_key(sym)
    }

    /// Check if an expression contains non-global function lookups (FunctionSubtype::Custom calls).
    /// Global function calls are allowed since they get desugared to constructors.
    /// Returns Some(span) if a lookup is found, None otherwise.
    pub fn expr_has_function_lookup(&self, expr: &ResolvedExpr) -> Option<Span> {
        use ast::GenericExpr;

        expr.find(&mut |e| {
            if let GenericExpr::Call(span, ResolvedCall::Func(func_type), _) = e
                && func_type.subtype == FunctionSubtype::Custom
                && !self.is_global(&func_type.name)
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
    #[error("{1}\nInvalid arguments to sort constructor `{0}`")]
    BadPresortArguments(String, Span),
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
    #[error(
        "{span}\nAmbiguous primitive resolution for `{name}` in {ctx:?} context: multiple registered primitives match the same signature."
    )]
    AmbiguousPrimitive {
        name: String,
        ctx: crate::Context,
        span: Span,
    },
    #[error("{span}\nNo resolution for `{name}` in {ctx:?} context.")]
    UnresolvedPrimitive {
        name: String,
        ctx: crate::Context,
        span: Span,
    },
}

#[cfg(test)]
mod test {
    use std::any::Any;
    use std::collections::hash_map::DefaultHasher;
    use std::fmt::Debug;
    use std::hash::{Hash, Hasher};
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use crate::sort::Sort;
    use crate::util::FreshGen;
    use crate::{ArcSort, EGraph, Error, ResolvedCall, Span, typechecking::TypeError};

    #[derive(Clone, Debug)]
    struct CountingSort {
        name: String,
        registrations: Arc<AtomicUsize>,
    }

    impl Sort for CountingSort {
        fn name(&self) -> &str {
            &self.name
        }

        fn column_ty(&self, _egraph: &egglog_bridge::EGraph) -> egglog_bridge::ColumnTy {
            egglog_bridge::ColumnTy::Id
        }

        fn register_type(&self, _egraph: &mut egglog_bridge::EGraph) {
            self.registrations.fetch_add(1, Ordering::SeqCst);
        }

        fn value_type(&self) -> Option<std::any::TypeId> {
            None
        }

        fn as_arc_any(self: Arc<Self>) -> Arc<dyn Any + Send + Sync + 'static> {
            self
        }
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
    fn function_registration_errors_leave_registry_and_generation_unchanged() {
        let mut egraph = EGraph::default();

        let invalid_constructor = "invalid-constructor";
        let constructor_generation = egraph
            .type_info
            .call_cache_stamp(invalid_constructor, false)
            .0;
        let Error::TypeError(error) = egraph
            .resolve_program(None, "(constructor invalid-constructor (i64) i64)")
            .unwrap_err()
        else {
            panic!("invalid constructor should fail during source typechecking")
        };
        assert!(matches!(error, TypeError::ConstructorOutputNotSort(..)));
        assert!(
            egraph
                .type_info
                .get_func_type(invalid_constructor)
                .is_none()
        );
        assert_eq!(
            egraph
                .type_info
                .call_cache_stamp(invalid_constructor, false)
                .0,
            constructor_generation
        );

        let invalid_merge = "invalid-merge";
        let merge_generation = egraph.type_info.call_cache_stamp(invalid_merge, false).0;
        let symbol_gen_before = egraph.parser.symbol_gen.clone();
        let expected_next_name = {
            let mut expected = symbol_gen_before.clone();
            expected.fresh("after-invalid-merge")
        };
        let Error::TypeError(error) = egraph
            .resolve_program(
                None,
                "(function invalid-merge (i64) i64 \
                 :merge ((let staged (+ old new)) \
                         (missing-merge-primitive staged)))",
            )
            .unwrap_err()
        else {
            panic!("invalid merge should fail during source typechecking")
        };
        match &error {
            TypeError::UnboundFunction(name, _) | TypeError::UnresolvedPrimitive { name, .. } => {
                assert_eq!(name, "missing-merge-primitive");
            }
            _ => panic!("unexpected merge error: {error:?}"),
        }
        assert!(egraph.type_info.get_func_type(invalid_merge).is_none());
        assert_eq!(
            egraph.type_info.call_cache_stamp(invalid_merge, false).0,
            merge_generation
        );
        assert_eq!(egraph.parser.symbol_gen, symbol_gen_before);
        assert_eq!(
            egraph.parser.symbol_gen.fresh("after-invalid-merge"),
            expected_next_name
        );

        let recursive_merge = "recursive-merge";
        let recursive_generation = egraph.type_info.call_cache_stamp(recursive_merge, false).0;
        egraph
            .resolve_program(
                None,
                "(function recursive-merge (i64) i64 \
                 :merge (recursive-merge old))",
            )
            .unwrap();
        assert!(egraph.type_info.get_func_type(recursive_merge).is_some());
        assert!(egraph.type_info.call_cache_stamp(recursive_merge, false).0 > recursive_generation);
        // A successful merge must close its transaction before returning.
        let _symbol_gen_after_successful_merge = egraph.parser.symbol_gen.clone();

        let declaration = "stable-function";
        let generation_before = egraph.type_info.call_cache_stamp(declaration, false).0;
        let symbol_gen_before_no_merge = egraph.parser.symbol_gen.clone();
        egraph
            .resolve_program(None, "(function stable-function (i64) i64 :no-merge)")
            .unwrap();
        assert_eq!(egraph.parser.symbol_gen, symbol_gen_before_no_merge);
        // The no-merge path never needs a SymbolGen transaction.
        let _symbol_gen_after_no_merge = egraph.parser.symbol_gen.clone();
        let registered = egraph.type_info.get_func_type(declaration).unwrap().clone();
        let generation = egraph.type_info.call_cache_stamp(declaration, false).0;
        assert!(generation > generation_before);
        let Error::TypeError(error) = egraph
            .resolve_program(None, "(function stable-function (String) String :no-merge)")
            .unwrap_err()
        else {
            panic!("duplicate function should fail during source typechecking")
        };
        assert!(matches!(error, TypeError::FunctionAlreadyBound(..)));
        let after = egraph.type_info.get_func_type(declaration).unwrap();
        assert!(Arc::ptr_eq(&registered, after));
        assert!(Arc::ptr_eq(&registered.input[0], &after.input[0]));
        assert!(Arc::ptr_eq(&registered.outputs[0], &after.outputs[0]));
        assert_eq!(
            egraph.type_info.call_cache_stamp(declaration, false).0,
            generation
        );
    }

    #[test]
    fn resolved_function_calls_share_signatures_with_their_registry() {
        let program = "(function shared-scalar (i64) i64 :no-merge)\n\
             (function shared-tuple (i64) (i64 String) :no-merge)";

        let mut first = EGraph::default();
        let commands = first.parse_program(None, program).unwrap();
        let mut first_resolved = Vec::new();
        for command in commands {
            first_resolved.extend(first.resolve_command_before_proofs(command).unwrap());
        }
        let scalar_first_decl = first_resolved
            .iter()
            .find_map(|command| match command {
                crate::ast::GenericNCommand::Function(decl) if decl.name == "shared-scalar" => {
                    Some(decl)
                }
                _ => None,
            })
            .unwrap();
        let tuple_first_decl = first_resolved
            .iter()
            .find_map(|command| match command {
                crate::ast::GenericNCommand::Function(decl) if decl.name == "shared-tuple" => {
                    Some(decl)
                }
                _ => None,
            })
            .unwrap();
        let ResolvedCall::Func(scalar_first) = &scalar_first_decl.resolved_schema else {
            panic!("scalar declaration should have a resolved function schema")
        };
        let ResolvedCall::Func(tuple_first) = &tuple_first_decl.resolved_schema else {
            panic!("tuple declaration should have a resolved function schema")
        };
        assert!(Arc::ptr_eq(
            scalar_first,
            first.type_info.get_func_type("shared-scalar").unwrap()
        ));
        assert!(Arc::ptr_eq(
            tuple_first,
            first.type_info.get_func_type("shared-tuple").unwrap()
        ));
        let i64_sort = first.type_info.get_sort_by_name("i64").unwrap().clone();
        let ResolvedCall::Func(scalar_resolved) = ResolvedCall::from_resolution_func_types(
            "shared-scalar",
            std::slice::from_ref(&i64_sort),
            &first.type_info,
        )
        .unwrap() else {
            panic!("scalar call should resolve as a function")
        };
        let ResolvedCall::Func(tuple_resolved) = ResolvedCall::from_resolution_func_types(
            "shared-tuple",
            std::slice::from_ref(&i64_sort),
            &first.type_info,
        )
        .unwrap() else {
            panic!("tuple call should resolve as a function")
        };
        assert!(Arc::ptr_eq(scalar_first, &scalar_resolved));
        assert!(Arc::ptr_eq(tuple_first, &tuple_resolved));

        let ResolvedCall::Func(scalar_resolved) = ResolvedCall::from_resolution(
            "shared-scalar",
            &[i64_sort.clone(), i64_sort.clone()],
            &first.type_info,
            crate::Context::Read,
            &Span::Panic,
        )
        .unwrap() else {
            panic!("full scalar signature should resolve as a function")
        };
        let string_sort = first.type_info.get_sort_by_name("String").unwrap().clone();
        let ResolvedCall::Func(tuple_resolved) = ResolvedCall::from_resolution(
            "shared-tuple",
            &[i64_sort.clone(), i64_sort, string_sort],
            &first.type_info,
            crate::Context::Read,
            &Span::Panic,
        )
        .unwrap() else {
            panic!("full tuple signature should resolve as a function")
        };
        assert!(Arc::ptr_eq(scalar_first, &scalar_resolved));
        assert!(Arc::ptr_eq(tuple_first, &tuple_resolved));

        let ResolvedCall::Func(scalar_cloned) = scalar_first_decl.resolved_schema.clone() else {
            panic!("scalar call clone should remain a function")
        };
        let ResolvedCall::Func(tuple_cloned) = tuple_first_decl.resolved_schema.clone() else {
            panic!("tuple call clone should remain a function")
        };
        assert!(Arc::ptr_eq(scalar_first, &scalar_cloned));
        assert!(Arc::ptr_eq(tuple_first, &tuple_cloned));
        assert_eq!(
            scalar_first
                .outputs
                .iter()
                .map(|sort| sort.name())
                .collect::<Vec<_>>(),
            ["i64"]
        );
        assert_eq!(
            tuple_first
                .outputs
                .iter()
                .map(|sort| sort.name())
                .collect::<Vec<_>>(),
            ["i64", "String"]
        );

        let scalar_before_push = first
            .type_info
            .get_func_type("shared-scalar")
            .unwrap()
            .clone();
        first.push();
        assert!(Arc::ptr_eq(
            &scalar_before_push,
            first.type_info.get_func_type("shared-scalar").unwrap()
        ));
        first
            .resolve_program(None, "(function scoped (i64) i64 :no-merge)")
            .unwrap();
        assert!(first.type_info.get_func_type("scoped").is_some());
        first.pop().unwrap();
        assert!(Arc::ptr_eq(
            &scalar_before_push,
            first.type_info.get_func_type("shared-scalar").unwrap()
        ));
        assert!(first.type_info.get_func_type("scoped").is_none());

        let mut second = EGraph::default();
        let commands = second.parse_program(None, program).unwrap();
        let mut second_resolved = Vec::new();
        for command in commands {
            second_resolved.extend(second.resolve_command_before_proofs(command).unwrap());
        }
        let scalar_second_decl = second_resolved
            .iter()
            .find_map(|command| match command {
                crate::ast::GenericNCommand::Function(decl) if decl.name == "shared-scalar" => {
                    Some(decl)
                }
                _ => None,
            })
            .unwrap();
        let tuple_second_decl = second_resolved
            .iter()
            .find_map(|command| match command {
                crate::ast::GenericNCommand::Function(decl) if decl.name == "shared-tuple" => {
                    Some(decl)
                }
                _ => None,
            })
            .unwrap();
        let ResolvedCall::Func(scalar_second) = &scalar_second_decl.resolved_schema else {
            panic!("scalar declaration should have a resolved function schema")
        };
        let ResolvedCall::Func(tuple_second) = &tuple_second_decl.resolved_schema else {
            panic!("tuple declaration should have a resolved function schema")
        };

        assert!(!Arc::ptr_eq(scalar_first, scalar_second));
        assert!(!Arc::ptr_eq(tuple_first, tuple_second));
        assert_eq!(
            scalar_first_decl.resolved_schema,
            scalar_second_decl.resolved_schema
        );
        assert_eq!(
            tuple_first_decl.resolved_schema,
            tuple_second_decl.resolved_schema
        );

        let mut scalar_first_hash = DefaultHasher::new();
        scalar_first_decl
            .resolved_schema
            .hash(&mut scalar_first_hash);
        let mut scalar_second_hash = DefaultHasher::new();
        scalar_second_decl
            .resolved_schema
            .hash(&mut scalar_second_hash);
        assert_eq!(scalar_first_hash.finish(), scalar_second_hash.finish());

        let mut tuple_first_hash = DefaultHasher::new();
        tuple_first_decl.resolved_schema.hash(&mut tuple_first_hash);
        let mut tuple_second_hash = DefaultHasher::new();
        tuple_second_decl
            .resolved_schema
            .hash(&mut tuple_second_hash);
        assert_eq!(tuple_first_hash.finish(), tuple_second_hash.finish());
    }

    #[test]
    fn duplicate_sort_is_rejected_before_backend_registration_and_preserves_error_order() {
        let mut egraph = EGraph::default();
        egraph.resolve_program(None, "(sort Stable)").unwrap();
        let original = egraph.type_info.get_sort_by_name("Stable").unwrap().clone();

        let Error::TypeError(error) = egraph
            .resolve_program(None, "(sort Stable (Vec))")
            .unwrap_err()
        else {
            panic!("invalid presort arguments should fail")
        };
        assert!(matches!(error, TypeError::BadPresortArguments(name, _) if name == "Vec"));
        assert!(Arc::ptr_eq(
            &original,
            egraph.type_info.get_sort_by_name("Stable").unwrap()
        ));

        let Error::TypeError(error) = egraph
            .resolve_program(None, "(sort Stable (Vec i64))")
            .unwrap_err()
        else {
            panic!("valid duplicate sort should fail as a duplicate")
        };
        assert!(matches!(error, TypeError::SortAlreadyBound(name, _) if name == "Stable"));

        let mut function_collision = EGraph::default();
        function_collision
            .resolve_program(None, "(function Stable () Unit :no-merge)")
            .unwrap();
        let Error::TypeError(error) = function_collision
            .resolve_program(None, "(sort Stable (Vec))")
            .unwrap_err()
        else {
            panic!("function collision must precede presort validation")
        };
        assert!(matches!(error, TypeError::FunctionAlreadyBound(name, _) if name == "Stable"));

        let first_count = Arc::new(AtomicUsize::new(0));
        let duplicate_count = Arc::new(AtomicUsize::new(0));
        let mut direct = EGraph::default();
        direct
            .add_arcsort(
                Arc::new(CountingSort {
                    name: "Counted".to_owned(),
                    registrations: first_count.clone(),
                }) as ArcSort,
                Span::Panic,
            )
            .unwrap();
        assert_eq!(first_count.load(Ordering::SeqCst), 1);
        let error = direct
            .add_arcsort(
                Arc::new(CountingSort {
                    name: "Counted".to_owned(),
                    registrations: duplicate_count.clone(),
                }) as ArcSort,
                Span::Panic,
            )
            .unwrap_err();
        assert!(matches!(error, TypeError::SortAlreadyBound(name, _) if name == "Counted"));
        assert_eq!(duplicate_count.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn invalid_index_does_not_register_or_advance_generation() {
        let mut egraph = EGraph::default();
        egraph
            .resolve_program(None, "(function indexed (i64 String) i64 :no-merge)")
            .unwrap();
        let generation = egraph.type_info.call_cache_stamp("Occ", false).0;
        let Error::TypeError(error) = egraph
            .resolve_program(None, "(index Occ indexed (any 0 1))")
            .unwrap_err()
        else {
            panic!("mixed-sort index should fail")
        };
        assert!(matches!(
            error,
            TypeError::IndexColumnSortMismatch(name, left, right, _)
                if name == "Occ" && left == "i64" && right == "String"
        ));
        assert!(egraph.type_info.get_func_type("Occ").is_none());
        assert!(!egraph.type_info.indexes.contains_key("Occ"));
        assert_eq!(
            egraph.type_info.call_cache_stamp("Occ", false).0,
            generation
        );

        egraph
            .resolve_program(None, "(index Occ indexed (any 0 2))")
            .unwrap();
        let registered = egraph.type_info.get_func_type("Occ").unwrap().clone();
        let info = egraph.type_info.indexes.get("Occ").unwrap().clone();
        let committed_generation = egraph.type_info.call_cache_stamp("Occ", false).0;
        assert!(committed_generation > generation);
        assert_eq!(
            registered
                .input
                .iter()
                .map(|sort| sort.name())
                .collect::<Vec<_>>(),
            ["i64", "i64", "String", "i64"]
        );
        assert_eq!(info.function, "indexed");
        assert_eq!(info.any_of, [0, 2]);

        let Error::TypeError(error) = egraph
            .resolve_program(None, "(index Occ Missing (any))")
            .unwrap_err()
        else {
            panic!("duplicate index name should fail before target validation")
        };
        assert!(matches!(error, TypeError::FunctionAlreadyBound(name, _) if name == "Occ"));
        assert_eq!(
            egraph.type_info.call_cache_stamp("Occ", false).0,
            committed_generation
        );
        assert_eq!(
            egraph.type_info.indexes.get("Occ").unwrap().function,
            "indexed"
        );
    }

    #[test]
    fn sort_registration_preserves_term_encoding_checker_propagation() {
        let mut egraph = EGraph::new_with_term_encoding();
        egraph
            .parse_and_run_program(
                None,
                "(sort E) \
                 (constructor Mk () E) \
                 (sort VE (Vec E)) \
                 (constructor Hold (VE) E) \
                 (Hold (vec-of (Mk))) \
                 (check (Hold (vec-of (Mk))))",
            )
            .unwrap();
    }
}
