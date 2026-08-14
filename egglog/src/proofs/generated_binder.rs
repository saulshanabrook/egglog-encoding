//! Portable typed-command foundation for generated proof instrumentation.
//!
//! The production generated driver remains unchanged unless the temporary
//! shadow-probe environment switch is present. Under that switch this module
//! defines the complete normalized command envelope, verifies emitter-owned
//! invariants, and binds portable keys against the outer execution e-graph so
//! the result can be compared exactly with the legacy frontend on a clone.

#![allow(dead_code)]

use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, OnceLock};
use std::time::{Duration, Instant};

use enum_map::EnumMap;
use thiserror::Error;

use super::proof_encoding::{GeneratedCommandOrigin, GeneratedFamily, TaggedGeneratedCommand};
use crate::ast::{
    ContainerRebuildSpec, Expr, FunctionDecl, FunctionSubtype, GenericAction, GenericActions,
    GenericExpr, GenericFact, GenericFunctionDecl, GenericMerge, GenericRule, GenericRunConfig,
    GenericSchedule, Literal, PrintFunctionMode, ProofConstructorNames, ResolvedAction,
    ResolvedActions, ResolvedExpr, ResolvedFact, ResolvedFunctionDecl, ResolvedNCommand,
    ResolvedRule, ResolvedRunConfig, ResolvedSchedule, RuleEvalMode, Schema, Span,
};
use crate::core::{ResolvedCall, resolve_call};
use crate::remove_globals;
use crate::typechecking::{SortDeclarationMetadata, TypeError, TypeInfo};
use crate::util::{HashMap, HashSet};
use crate::{ArcSort, CommandOutput, Context, EGraph, Error as EgglogError, ResolvedVar};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GeneratedRole {
    Header,
    PendingDeclaration,
    SourceDerived,
    Maintenance,
    ExtractionSetup,
    ControlWrapper,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct GeneratedOrigin {
    family: GeneratedFamily,
    role: GeneratedRole,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum SortSemanticClass {
    Eq,
    EqContainer,
    Value,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct SortKey {
    name: String,
    class: SortSemanticClass,
}

impl SortKey {
    fn from_sort(sort: &ArcSort) -> Self {
        Self {
            name: sort.name().to_owned(),
            class: if sort.is_eq_container_sort() {
                SortSemanticClass::EqContainer
            } else if sort.is_eq_sort() {
                SortSemanticClass::Eq
            } else {
                SortSemanticClass::Value
            },
        }
    }

    fn matches_sort(&self, sort: &ArcSort) -> bool {
        self.name == sort.name()
            && self.class
                == if sort.is_eq_container_sort() {
                    SortSemanticClass::EqContainer
                } else if sort.is_eq_sort() {
                    SortSemanticClass::Eq
                } else {
                    SortSemanticClass::Value
                }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum ValueShape {
    Scalar(SortKey),
    Tuple(Vec<SortKey>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct FunctionKey {
    name: String,
    subtype: FunctionSubtype,
    inputs: Vec<SortKey>,
    output: ValueShape,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct PrimitiveKey {
    name: String,
    inputs: Vec<SortKey>,
    output: SortKey,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum CallKey {
    Function(FunctionKey),
    Primitive(PrimitiveKey),
    Values(Vec<SortKey>),
}

impl Display for CallKey {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Function(key) => f.write_str(&key.name),
            Self::Primitive(key) => f.write_str(&key.name),
            Self::Values(_) => f.write_str("values"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CallKind {
    Function,
    Primitive,
    Values,
}

impl Display for CallKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Function => f.write_str("function"),
            Self::Primitive => f.write_str("primitive"),
            Self::Values => f.write_str("values"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct LocalId(u32);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct GeneratedVar {
    id: LocalId,
    name: String,
    sort: SortKey,
}

impl Display for GeneratedVar {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.name)
    }
}

type GeneratedExpr = GenericExpr<CallKey, GeneratedVar>;
type GeneratedFact = GenericFact<CallKey, GeneratedVar>;
type GeneratedAction = GenericAction<CallKey, GeneratedVar>;
type GeneratedActions = GenericActions<CallKey, GeneratedVar>;
type GeneratedMerge = GenericMerge<CallKey, GeneratedVar>;
type GeneratedRule = GenericRule<CallKey, GeneratedVar>;
type GeneratedSchedule = GenericSchedule<CallKey, GeneratedVar>;
type GeneratedFunctionDecl = GenericFunctionDecl<CallKey, GeneratedVar>;

#[derive(Clone, Debug)]
struct GeneratedSortDecl {
    span: Span,
    key: SortKey,
    presort_and_args: Option<(String, Vec<Expr>)>,
    uf: Option<(String, Option<String>)>,
    container_rebuild: Option<ContainerRebuildSpec>,
    proof_constructors: Option<ProofConstructorNames>,
    unionable: bool,
}

#[derive(Clone, Debug)]
struct GeneratedIndexDecl {
    span: Span,
    name: String,
    function: FunctionKey,
    any_of: Vec<usize>,
}

#[derive(Clone, Debug)]
struct GeneratedCommand {
    origin: GeneratedOrigin,
    kind: GeneratedCommandKind,
}

#[derive(Clone, Debug)]
enum GeneratedCommandKind {
    Sort(GeneratedSortDecl),
    Function(GeneratedFunctionDecl),
    Index(GeneratedIndexDecl),
    AddRuleset(Span, String),
    CombinedRuleset(Span, String, Vec<String>),
    Rule(GeneratedRule),
    Action(GeneratedAction),
    Actions(GeneratedActions),
    Extract(Span, GeneratedExpr, GeneratedExpr),
    Schedule(GeneratedSchedule),
    PrintOverallStatistics(Span, Option<String>),
    Check(Span, Vec<GeneratedFact>),
    PrintFunction(
        Span,
        String,
        Option<usize>,
        Option<String>,
        PrintFunctionMode,
    ),
    ProveExists(Span, FunctionKey),
    PrintSize(Span, Option<String>),
    Output {
        span: Span,
        file: String,
        exprs: Vec<GeneratedExpr>,
    },
    Push(usize),
    Pop(Span, usize),
    Fail(Span, Vec<GeneratedCommand>),
    Input {
        span: Span,
        name: String,
        file: String,
    },
}

#[derive(Clone, Debug)]
struct GeneratedBatch {
    commands: Vec<GeneratedCommand>,
}

#[derive(Debug)]
struct BoundCommand {
    origins: Vec<GeneratedOrigin>,
    command: ResolvedNCommand,
}

/// A resolved batch is tied to the exact e-graph universe that produced its
/// handles and can only be consumed by executing it on that same e-graph.
struct BoundBatch<'a> {
    egraph: &'a mut EGraph,
    commands: Vec<BoundCommand>,
    stats: GeneratedBindStats,
    profile: GeneratedBindProfile,
}

impl std::fmt::Debug for BoundBatch<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BoundBatch")
            .field("commands", &self.commands)
            .field("stats", &self.stats)
            .field("profile", &self.profile)
            .finish_non_exhaustive()
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct GeneratedFamilyBindProfile {
    commands: usize,
    elapsed: Duration,
    verifier_elapsed: Duration,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct GeneratedBindProfile {
    elapsed: Duration,
    families: [GeneratedFamilyBindProfile; 4],
}

#[derive(Debug)]
struct BoundExecution {
    outputs: Vec<CommandOutput>,
    origins: Vec<GeneratedOrigin>,
    stats: GeneratedBindStats,
}

impl BoundBatch<'_> {
    fn execute(self) -> Result<BoundExecution, EgglogError> {
        let mut outputs = Vec::new();
        let mut origins = Vec::with_capacity(self.commands.len());
        for bound in self.commands {
            origins.extend(bound.origins);
            outputs.extend(self.egraph.run_command(bound.command)?);
        }
        Ok(BoundExecution {
            outputs,
            origins,
            stats: self.stats,
        })
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct GeneratedBindStats {
    unique_sort_keys: usize,
    unique_resolution_keys: usize,
    sort_cache_hits: usize,
    sort_cache_misses: usize,
    call_cache_hits: usize,
    call_cache_misses: usize,
    resolver_invocations: usize,
    registration_receipt_hits: usize,
    resolver_invocations_by_context: EnumMap<Context, usize>,
    registration_receipt_hits_by_context: EnumMap<Context, usize>,
    declarations_registered: usize,
    commands_bound: usize,
    verifier_elapsed: Duration,
}

#[derive(Debug, Error)]
enum GeneratedBindError {
    #[error(transparent)]
    Type(#[from] TypeError),
    #[error(
        "{span}\nsort `{name}` has class {actual:?}, but the generated key requires {expected:?}"
    )]
    SortClassMismatch {
        name: String,
        expected: SortSemanticClass,
        actual: SortSemanticClass,
        span: Span,
    },
    #[error("{span}\nprepared sort `{actual}` does not match generated key `{expected}`")]
    SortNameMismatch {
        expected: String,
        actual: String,
        span: Span,
    },
    #[error("{span}\nexpected `{head}` to resolve as {expected}, but it resolved as {actual}")]
    WrongCallKind {
        head: String,
        expected: CallKind,
        actual: CallKind,
        span: Span,
    },
    #[error(
        "{span}\nfunction `{name}` has subtype {actual}, but the generated key requires {expected}"
    )]
    FunctionSubtypeMismatch {
        name: String,
        expected: FunctionSubtype,
        actual: FunctionSubtype,
        span: Span,
    },
    #[error("{span}\ngenerated call expected {expected} arguments, got {actual}")]
    CallArity {
        expected: usize,
        actual: usize,
        span: Span,
    },
    #[error("{span}\ngenerated value has shape {actual}, but {expected} was required")]
    ShapeMismatch {
        expected: String,
        actual: String,
        span: Span,
    },
    #[error("{span}\ngenerated expression references undeclared local `{name}` ({id})")]
    UndeclaredLocal { id: u32, name: String, span: Span },
    #[error("{span}\ngenerated local id {id} was reused with incompatible metadata")]
    InconsistentLocalId { id: u32, span: Span },
    #[error("{span}\ngenerated local name `{name}` was reused with a different id")]
    InconsistentLocalName { name: String, span: Span },
    #[error("{span}\ngenerated local `{name}` was defined more than once")]
    DuplicateLocal { name: String, span: Span },
    #[error("{span}\n`values` and tuple shapes must carry at least two columns, got {actual}")]
    InvalidTupleArity { actual: usize, span: Span },
    #[error("{span}\ngenerated function metadata does not match exact key `{name}`")]
    FunctionMetadataMismatch { name: String, span: Span },
    #[error("{span}\ntuple merge for `{name}` must return an exact `values` expression")]
    TupleMergeResult { name: String, span: Span },
    #[error("{span}\nmerge variable `{name}` is not valid for this function output")]
    InvalidMergeVariable { name: String, span: Span },
    #[error("{span}\ntop-level generated `let` is forbidden")]
    TopLevelLet { span: Span },
    #[error("{span}\ngenerated `fail` must contain at least one normalized command")]
    EmptyFail { span: Span },
    #[error("{span}\nextract requires a scalar value, got {actual}")]
    CannotExtractTuple { actual: String, span: Span },
    #[error("{span}\nresolved generated command `{command}` is outside the portable envelope")]
    UnsupportedResolvedCommand { command: &'static str, span: Span },
    #[error("{span}\nresolved generated head `{head}` is not a function")]
    ExpectedResolvedFunction { head: String, span: Span },
    #[error("{span}\nresolved generated local `{name}` changed sort within one lexical scope")]
    PortableLocalSortMismatch { name: String, span: Span },
}

impl From<GeneratedBindError> for EgglogError {
    fn from(error: GeneratedBindError) -> Self {
        match error {
            GeneratedBindError::Type(error) => EgglogError::TypeError(error),
            error => EgglogError::DesugarError(
                crate::span!(),
                format!("generated binder shadow probe failed: {error}"),
            ),
        }
    }
}

#[derive(Clone)]
struct CachedSort {
    sort: ArcSort,
    id: u64,
}

#[derive(Clone)]
struct CachedResolvedCall {
    key: CallKey,
    call: Arc<ResolvedCall>,
    id: u64,
}

#[derive(Clone, Default)]
struct HeadCallCache {
    generation: Option<u64>,
    by_context: EnumMap<Context, Vec<CachedResolvedCall>>,
    function_receipt: Option<(FunctionKey, Arc<ResolvedCall>)>,
}

#[derive(Clone, Default)]
struct PersistentBindingCache {
    sort_cache: HashMap<SortKey, CachedSort>,
    call_cache: HashMap<String, HeadCallCache>,
    next_sort_id: u64,
    next_call_id: u64,
}

#[derive(Default)]
struct BindingState {
    sort_cache: HashMap<SortKey, CachedSort>,
    call_cache: HashMap<String, HeadCallCache>,
    next_sort_id: u64,
    next_call_id: u64,
    seen_sort_ids: HashSet<u64>,
    seen_resolution_ids: HashSet<u64>,
    stats: GeneratedBindStats,
    suppress_detailed_stats: bool,
}

impl BindingState {
    fn from_persistent_cache(cache: PersistentBindingCache) -> Self {
        Self {
            sort_cache: cache.sort_cache,
            call_cache: cache.call_cache,
            next_sort_id: cache.next_sort_id,
            next_call_id: cache.next_call_id,
            suppress_detailed_stats: !SHADOW_PROBE_DETAILED.load(Ordering::Relaxed),
            ..Default::default()
        }
    }

    fn resolve_sort(
        &mut self,
        type_info: &TypeInfo,
        key: &SortKey,
        span: &Span,
    ) -> Result<ArcSort, GeneratedBindError> {
        if let Some(cached) = self.sort_cache.get(key) {
            if !self.suppress_detailed_stats {
                self.seen_sort_ids.insert(cached.id);
                self.stats.sort_cache_hits += 1;
            }
            return Ok(cached.sort.clone());
        }
        if !self.suppress_detailed_stats {
            self.stats.sort_cache_misses += 1;
        }
        let sort = type_info
            .get_sort_by_name(&key.name)
            .cloned()
            .ok_or_else(|| TypeError::UndefinedSort(key.name.clone(), span.clone()))?;
        let actual = SortKey::from_sort(&sort).class;
        if !key.matches_sort(&sort) {
            return Err(GeneratedBindError::SortClassMismatch {
                name: key.name.clone(),
                expected: key.class,
                actual,
                span: span.clone(),
            });
        }
        let id = self.next_sort_id;
        self.next_sort_id = self
            .next_sort_id
            .checked_add(1)
            .unwrap_or_else(|| panic!("generated binder exhausted persistent sort cache ids"));
        if !self.suppress_detailed_stats {
            self.seen_sort_ids.insert(id);
        }
        self.sort_cache.insert(
            key.clone(),
            CachedSort {
                sort: sort.clone(),
                id,
            },
        );
        Ok(sort)
    }

    fn resolve_call(
        &mut self,
        type_info: &TypeInfo,
        key: &CallKey,
        context: Context,
        span: &Span,
    ) -> Result<ResolvedCall, GeneratedBindError> {
        let (head, head_generation) = match key {
            CallKey::Function(key) => (key.name.as_str(), type_info.call_generation(&key.name)),
            CallKey::Primitive(key) => (key.name.as_str(), type_info.call_generation(&key.name)),
            CallKey::Values(_) => ("values", 0),
        };
        let cached = self
            .call_cache
            .get(head)
            .filter(|cache| cache.generation == Some(head_generation))
            .and_then(|cache| {
                cache.by_context[context]
                    .iter()
                    .find(|cached| &cached.key == key)
            })
            .map(|cached| (cached.id, Arc::clone(&cached.call)));
        if let Some((id, call)) = cached {
            if !self.suppress_detailed_stats {
                self.seen_resolution_ids.insert(id);
                self.stats.call_cache_hits += 1;
            }
            return Ok((*call).clone());
        }
        if !self.suppress_detailed_stats {
            self.stats.call_cache_misses += 1;
        }
        let registration_receipt = self
            .call_cache
            .get(head)
            .filter(|cache| cache.generation == Some(head_generation))
            .and_then(|cache| cache.function_receipt.as_ref())
            .filter(|(receipt_key, _)| {
                matches!(key, CallKey::Function(function) if function == receipt_key)
            })
            .map(|(_, call)| Arc::clone(call));
        let id = self.next_call_id;
        self.next_call_id = self
            .next_call_id
            .checked_add(1)
            .unwrap_or_else(|| panic!("generated binder exhausted persistent call cache ids"));
        if !self.suppress_detailed_stats {
            self.seen_resolution_ids.insert(id);
        }

        if let Some(call) = registration_receipt {
            if !self.suppress_detailed_stats {
                self.stats.registration_receipt_hits += 1;
                self.stats.registration_receipt_hits_by_context[context] += 1;
            }
            self.call_cache
                .get_mut(head)
                .expect("a matching registration receipt has a head cache")
                .by_context[context]
                .push(CachedResolvedCall {
                    key: key.clone(),
                    call: Arc::clone(&call),
                    id,
                });
            return Ok((*call).clone());
        }

        let resolved = Arc::new(match key {
            CallKey::Function(function) => {
                let mut signature = function
                    .inputs
                    .iter()
                    .map(|sort| self.resolve_sort(type_info, sort, span))
                    .collect::<Result<Vec<_>, _>>()?;
                match &function.output {
                    ValueShape::Scalar(sort) => {
                        signature.push(self.resolve_sort(type_info, sort, span)?);
                    }
                    ValueShape::Tuple(sorts) => {
                        if sorts.len() < 2 {
                            return Err(GeneratedBindError::InvalidTupleArity {
                                actual: sorts.len(),
                                span: span.clone(),
                            });
                        }
                        signature.extend(
                            sorts
                                .iter()
                                .map(|sort| self.resolve_sort(type_info, sort, span))
                                .collect::<Result<Vec<_>, _>>()?,
                        );
                    }
                }
                if !self.suppress_detailed_stats {
                    self.stats.resolver_invocations += 1;
                    self.stats.resolver_invocations_by_context[context] += 1;
                }
                let call = resolve_call(head, &signature, type_info, context, span)?;
                match &call {
                    ResolvedCall::Func(actual) if actual.subtype != function.subtype => {
                        return Err(GeneratedBindError::FunctionSubtypeMismatch {
                            name: function.name.clone(),
                            expected: function.subtype,
                            actual: actual.subtype,
                            span: span.clone(),
                        });
                    }
                    ResolvedCall::Func(_) => {}
                    ResolvedCall::Primitive(_) => {
                        return Err(GeneratedBindError::WrongCallKind {
                            head: function.name.clone(),
                            expected: CallKind::Function,
                            actual: CallKind::Primitive,
                            span: span.clone(),
                        });
                    }
                    ResolvedCall::Values(_) => unreachable!("resolver never creates values"),
                }
                call
            }
            CallKey::Primitive(primitive) => {
                let mut signature = primitive
                    .inputs
                    .iter()
                    .map(|sort| self.resolve_sort(type_info, sort, span))
                    .collect::<Result<Vec<_>, _>>()?;
                signature.push(self.resolve_sort(type_info, &primitive.output, span)?);
                if !self.suppress_detailed_stats {
                    self.stats.resolver_invocations += 1;
                    self.stats.resolver_invocations_by_context[context] += 1;
                }
                let call = resolve_call(head, &signature, type_info, context, span)?;
                match &call {
                    ResolvedCall::Primitive(_) => {}
                    ResolvedCall::Func(_) => {
                        return Err(GeneratedBindError::WrongCallKind {
                            head: primitive.name.clone(),
                            expected: CallKind::Primitive,
                            actual: CallKind::Function,
                            span: span.clone(),
                        });
                    }
                    ResolvedCall::Values(_) => unreachable!("resolver never creates values"),
                }
                call
            }
            CallKey::Values(sorts) => {
                if sorts.len() < 2 {
                    return Err(GeneratedBindError::InvalidTupleArity {
                        actual: sorts.len(),
                        span: span.clone(),
                    });
                }
                ResolvedCall::Values(
                    sorts
                        .iter()
                        .map(|sort| self.resolve_sort(type_info, sort, span))
                        .collect::<Result<_, _>>()?,
                )
            }
        });
        let cache = self.call_cache.entry(head.to_owned()).or_default();
        if cache.generation != Some(head_generation) {
            cache.generation = Some(head_generation);
            cache.by_context = EnumMap::default();
            cache.function_receipt = None;
        }
        cache.by_context[context].push(CachedResolvedCall {
            key: key.clone(),
            call: Arc::clone(&resolved),
            id,
        });
        Ok((*resolved).clone())
    }

    /// Seed the exact, generation-scoped function result produced by a
    /// successful declaration commit. Context entries remain lazy so unused
    /// generated declarations do not pay four deep `FuncType` clones.
    fn record_function_receipt(
        &mut self,
        type_info: &TypeInfo,
        key: FunctionKey,
        call: ResolvedCall,
    ) {
        debug_assert!(matches!(&call, ResolvedCall::Func(function) if function.name == key.name));
        let generation = type_info.call_generation(&key.name);
        let cache = self.call_cache.entry(key.name.clone()).or_default();
        cache.generation = Some(generation);
        cache.by_context = EnumMap::default();
        cache.function_receipt = Some((key, Arc::new(call)));
    }

    fn finish(mut self) -> GeneratedBindStats {
        self.stats.unique_sort_keys = self.seen_sort_ids.len();
        self.stats.unique_resolution_keys = self.seen_resolution_ids.len();
        self.stats
    }

    fn finish_with_persistent_cache(mut self) -> (GeneratedBindStats, PersistentBindingCache) {
        self.stats.unique_sort_keys = self.seen_sort_ids.len();
        self.stats.unique_resolution_keys = self.seen_resolution_ids.len();
        (
            self.stats,
            PersistentBindingCache {
                sort_cache: self.sort_cache,
                call_cache: self.call_cache,
                next_sort_id: self.next_sort_id,
                next_call_id: self.next_call_id,
            },
        )
    }
}

#[derive(Clone, Default)]
struct LocalScope {
    by_id: HashMap<LocalId, ResolvedVar>,
    by_name: HashMap<String, LocalId>,
}

impl LocalScope {
    fn declare(
        &mut self,
        generated: &GeneratedVar,
        resolved: ResolvedVar,
        span: &Span,
    ) -> Result<(), GeneratedBindError> {
        if let Some(existing) = self.by_id.get(&generated.id) {
            if existing.name == generated.name && existing.sort.name() == resolved.sort.name() {
                return Ok(());
            }
            return Err(GeneratedBindError::InconsistentLocalId {
                id: generated.id.0,
                span: span.clone(),
            });
        }
        if let Some(existing_id) = self.by_name.get(&generated.name)
            && *existing_id != generated.id
        {
            return Err(GeneratedBindError::InconsistentLocalName {
                name: generated.name.clone(),
                span: span.clone(),
            });
        }
        self.by_name.insert(generated.name.clone(), generated.id);
        self.by_id.insert(generated.id, resolved);
        Ok(())
    }
}

#[derive(Clone, Default)]
struct PortableScope {
    by_id: HashMap<LocalId, GeneratedVar>,
    by_name: HashMap<String, LocalId>,
}

impl PortableScope {
    fn observe(&mut self, variable: &GeneratedVar, span: &Span) -> Result<(), GeneratedBindError> {
        if let Some(existing) = self.by_id.get(&variable.id) {
            if existing.name != variable.name || existing.sort != variable.sort {
                return Err(GeneratedBindError::InconsistentLocalId {
                    id: variable.id.0,
                    span: span.clone(),
                });
            }
            return Ok(());
        }
        if let Some(existing_id) = self.by_name.get(&variable.name)
            && *existing_id != variable.id
        {
            return Err(GeneratedBindError::InconsistentLocalName {
                name: variable.name.clone(),
                span: span.clone(),
            });
        }
        self.by_name.insert(variable.name.clone(), variable.id);
        self.by_id.insert(variable.id, variable.clone());
        Ok(())
    }

    fn declare_new(
        &mut self,
        variable: &GeneratedVar,
        span: &Span,
    ) -> Result<(), GeneratedBindError> {
        if self.by_id.contains_key(&variable.id) || self.by_name.contains_key(&variable.name) {
            return Err(GeneratedBindError::DuplicateLocal {
                name: variable.name.clone(),
                span: span.clone(),
            });
        }
        self.by_name.insert(variable.name.clone(), variable.id);
        self.by_id.insert(variable.id, variable.clone());
        Ok(())
    }

    fn require(&self, variable: &GeneratedVar, span: &Span) -> Result<(), GeneratedBindError> {
        let Some(existing) = self.by_id.get(&variable.id) else {
            if variable.name.starts_with(crate::GLOBAL_NAME_PREFIX) {
                return Ok(());
            }
            return Err(GeneratedBindError::UndeclaredLocal {
                id: variable.id.0,
                name: variable.name.clone(),
                span: span.clone(),
            });
        };
        if existing.name != variable.name || existing.sort != variable.sort {
            return Err(GeneratedBindError::InconsistentLocalId {
                id: variable.id.0,
                span: span.clone(),
            });
        }
        Ok(())
    }
}

fn visit_expr_vars(
    expr: &GeneratedExpr,
    visit: &mut impl FnMut(&Span, &GeneratedVar) -> Result<(), GeneratedBindError>,
) -> Result<(), GeneratedBindError> {
    match expr {
        GenericExpr::Var(span, variable) => visit(span, variable),
        GenericExpr::Lit(..) => Ok(()),
        GenericExpr::Call(_, _, args) => {
            for arg in args {
                visit_expr_vars(arg, visit)?;
            }
            Ok(())
        }
    }
}

fn visit_fact_vars(
    fact: &GeneratedFact,
    visit: &mut impl FnMut(&Span, &GeneratedVar) -> Result<(), GeneratedBindError>,
) -> Result<(), GeneratedBindError> {
    match fact {
        GenericFact::Eq(_, left, right) => {
            visit_expr_vars(left, visit)?;
            visit_expr_vars(right, visit)
        }
        GenericFact::Fact(expr) => visit_expr_vars(expr, visit),
    }
}

fn visit_action_vars(
    action: &GeneratedAction,
    visit: &mut impl FnMut(&Span, &GeneratedVar) -> Result<(), GeneratedBindError>,
) -> Result<(), GeneratedBindError> {
    match action {
        GenericAction::Let(span, variable, expr) => {
            visit(span, variable)?;
            visit_expr_vars(expr, visit)
        }
        GenericAction::Set(_, _, args, value) => {
            for arg in args {
                visit_expr_vars(arg, visit)?;
            }
            visit_expr_vars(value, visit)
        }
        GenericAction::Change(_, _, _, args) => {
            for arg in args {
                visit_expr_vars(arg, visit)?;
            }
            Ok(())
        }
        GenericAction::Union(_, left, right) => {
            visit_expr_vars(left, visit)?;
            visit_expr_vars(right, visit)
        }
        GenericAction::Panic(..) => Ok(()),
        GenericAction::Expr(_, expr) => visit_expr_vars(expr, visit),
    }
}

#[derive(Clone, Copy)]
enum VerifiedValueShape<'a> {
    Scalar(&'a SortKey),
    Literal(&'static str),
    Tuple(&'a [SortKey]),
}

impl VerifiedValueShape<'_> {
    fn same_shape(self, other: Self) -> bool {
        match (self, other) {
            (Self::Scalar(left), Self::Scalar(right)) => left == right,
            (Self::Scalar(sort), Self::Literal(name))
            | (Self::Literal(name), Self::Scalar(sort)) => {
                sort.name == name && sort.class == SortSemanticClass::Value
            }
            (Self::Literal(left), Self::Literal(right)) => left == right,
            (Self::Tuple(left), Self::Tuple(right)) => left == right,
            _ => false,
        }
    }

    fn stable_name(self) -> String {
        match self {
            Self::Scalar(sort) => sort.name.clone(),
            Self::Literal(name) => name.to_owned(),
            Self::Tuple(sorts) => format!(
                "({})",
                sorts
                    .iter()
                    .map(|sort| sort.name.as_str())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        }
    }

    fn is_tuple(self) -> bool {
        matches!(self, Self::Tuple(_))
    }
}

struct LinearVerifier;

impl LinearVerifier {
    fn verify_value_shape(shape: &ValueShape, span: &Span) -> Result<(), GeneratedBindError> {
        if let ValueShape::Tuple(sorts) = shape
            && sorts.len() < 2
        {
            return Err(GeneratedBindError::InvalidTupleArity {
                actual: sorts.len(),
                span: span.clone(),
            });
        }
        Ok(())
    }

    fn literal_sort_name(literal: &Literal) -> &'static str {
        match literal {
            Literal::Int(_) => "i64",
            Literal::Float(_) => "f64",
            Literal::String(_) => "String",
            Literal::Bool(_) => "bool",
            Literal::Unit => "Unit",
        }
    }

    fn verify_expr<'a>(
        expr: &'a GeneratedExpr,
        scope: &PortableScope,
    ) -> Result<VerifiedValueShape<'a>, GeneratedBindError> {
        match expr {
            GenericExpr::Var(span, variable) => {
                scope.require(variable, span)?;
                Ok(VerifiedValueShape::Scalar(&variable.sort))
            }
            GenericExpr::Lit(_, literal) => Ok(VerifiedValueShape::Literal(
                Self::literal_sort_name(literal),
            )),
            GenericExpr::Call(span, key, args) => {
                let (inputs, output) = match key {
                    CallKey::Function(function) => {
                        Self::verify_value_shape(&function.output, span)?;
                        (
                            &function.inputs,
                            match &function.output {
                                ValueShape::Scalar(sort) => VerifiedValueShape::Scalar(sort),
                                ValueShape::Tuple(sorts) => VerifiedValueShape::Tuple(sorts),
                            },
                        )
                    }
                    CallKey::Primitive(primitive) => (
                        &primitive.inputs,
                        VerifiedValueShape::Scalar(&primitive.output),
                    ),
                    CallKey::Values(sorts) => {
                        if sorts.len() < 2 {
                            return Err(GeneratedBindError::InvalidTupleArity {
                                actual: sorts.len(),
                                span: span.clone(),
                            });
                        }
                        (sorts, VerifiedValueShape::Tuple(sorts))
                    }
                };
                if args.len() != inputs.len() {
                    return Err(GeneratedBindError::CallArity {
                        expected: inputs.len(),
                        actual: args.len(),
                        span: span.clone(),
                    });
                }
                for (arg, expected) in args.iter().zip(inputs) {
                    let actual = Self::verify_expr(arg, scope)?;
                    let expected = VerifiedValueShape::Scalar(expected);
                    if !actual.same_shape(expected) {
                        return Err(GeneratedBindError::ShapeMismatch {
                            expected: expected.stable_name(),
                            actual: actual.stable_name(),
                            span: span.clone(),
                        });
                    }
                }
                Ok(output)
            }
        }
    }

    fn verify_fact(fact: &GeneratedFact, scope: &PortableScope) -> Result<(), GeneratedBindError> {
        match fact {
            GenericFact::Eq(span, left, right) => {
                let left = Self::verify_expr(left, scope)?;
                let right = Self::verify_expr(right, scope)?;
                if !left.same_shape(right) {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: left.stable_name(),
                        actual: right.stable_name(),
                        span: span.clone(),
                    });
                }
            }
            GenericFact::Fact(expr) => {
                // A fact asserts that an expression has a value; relation
                // constructors therefore return their private non-unionable
                // sort, not `Unit`. The ordinary typechecker accepts every
                // well-typed fact expression and so must the generated verifier.
                Self::verify_expr(expr, scope)?;
            }
        }
        Ok(())
    }

    fn verify_action(
        action: &GeneratedAction,
        scope: &mut PortableScope,
    ) -> Result<(), GeneratedBindError> {
        match action {
            GenericAction::Let(span, variable, expr) => {
                let actual = Self::verify_expr(expr, scope)?;
                let expected = VerifiedValueShape::Scalar(&variable.sort);
                if !actual.same_shape(expected) {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: expected.stable_name(),
                        actual: actual.stable_name(),
                        span: span.clone(),
                    });
                }
                scope.declare_new(variable, span)?;
            }
            GenericAction::Set(span, head, args, value) => {
                let CallKey::Function(function) = head else {
                    return Err(GeneratedBindError::WrongCallKind {
                        head: head.to_string(),
                        expected: CallKind::Function,
                        actual: match head {
                            CallKey::Primitive(_) => CallKind::Primitive,
                            CallKey::Values(_) => CallKind::Values,
                            CallKey::Function(_) => unreachable!(),
                        },
                        span: span.clone(),
                    });
                };
                if args.len() != function.inputs.len() {
                    return Err(GeneratedBindError::CallArity {
                        expected: function.inputs.len(),
                        actual: args.len(),
                        span: span.clone(),
                    });
                }
                for (arg, expected) in args.iter().zip(&function.inputs) {
                    let actual = Self::verify_expr(arg, scope)?;
                    let expected = VerifiedValueShape::Scalar(expected);
                    if !actual.same_shape(expected) {
                        return Err(GeneratedBindError::ShapeMismatch {
                            expected: expected.stable_name(),
                            actual: actual.stable_name(),
                            span: span.clone(),
                        });
                    }
                }
                let actual = Self::verify_expr(value, scope)?;
                let expected = match &function.output {
                    ValueShape::Scalar(sort) => VerifiedValueShape::Scalar(sort),
                    ValueShape::Tuple(sorts) => VerifiedValueShape::Tuple(sorts),
                };
                if !actual.same_shape(expected) {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: expected.stable_name(),
                        actual: actual.stable_name(),
                        span: span.clone(),
                    });
                }
            }
            GenericAction::Change(span, _, head, args) => {
                let CallKey::Function(function) = head else {
                    return Err(GeneratedBindError::WrongCallKind {
                        head: head.to_string(),
                        expected: CallKind::Function,
                        actual: match head {
                            CallKey::Primitive(_) => CallKind::Primitive,
                            CallKey::Values(_) => CallKind::Values,
                            CallKey::Function(_) => unreachable!(),
                        },
                        span: span.clone(),
                    });
                };
                if args.len() != function.inputs.len() {
                    return Err(GeneratedBindError::CallArity {
                        expected: function.inputs.len(),
                        actual: args.len(),
                        span: span.clone(),
                    });
                }
                for (arg, expected) in args.iter().zip(&function.inputs) {
                    let actual = Self::verify_expr(arg, scope)?;
                    let expected = VerifiedValueShape::Scalar(expected);
                    if !actual.same_shape(expected) {
                        return Err(GeneratedBindError::ShapeMismatch {
                            expected: expected.stable_name(),
                            actual: actual.stable_name(),
                            span: span.clone(),
                        });
                    }
                }
            }
            GenericAction::Union(span, left, right) => {
                let left = Self::verify_expr(left, scope)?;
                let right = Self::verify_expr(right, scope)?;
                if !left.same_shape(right) {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: left.stable_name(),
                        actual: right.stable_name(),
                        span: span.clone(),
                    });
                }
            }
            GenericAction::Panic(..) => {}
            GenericAction::Expr(_, expr) => {
                let span = match expr {
                    GenericExpr::Var(span, _)
                    | GenericExpr::Call(span, _, _)
                    | GenericExpr::Lit(span, _) => span,
                };
                let shape = Self::verify_expr(expr, scope)?;
                if shape.is_tuple() {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: "scalar action expression".to_owned(),
                        actual: shape.stable_name(),
                        span: span.clone(),
                    });
                }
            }
        }
        Ok(())
    }

    fn verify_actions(
        actions: &GeneratedActions,
        scope: &mut PortableScope,
    ) -> Result<(), GeneratedBindError> {
        for action in &actions.0 {
            Self::verify_action(action, scope)?;
        }
        Ok(())
    }

    fn query_scope(facts: &[GeneratedFact]) -> Result<PortableScope, GeneratedBindError> {
        let mut scope = PortableScope::default();
        for fact in facts {
            visit_fact_vars(fact, &mut |span, variable| {
                if variable.name.starts_with(crate::GLOBAL_NAME_PREFIX) {
                    Ok(())
                } else {
                    scope.observe(variable, span)
                }
            })?;
        }
        Ok(scope)
    }

    fn verify_rule(rule: &GeneratedRule) -> Result<(), GeneratedBindError> {
        let scope = Self::query_scope(&rule.body)?;
        for fact in &rule.body {
            Self::verify_fact(fact, &scope)?;
        }
        let mut head_scope = scope;
        Self::verify_actions(&rule.head, &mut head_scope)
    }

    fn verify_merge(
        name: &str,
        output: &ValueShape,
        merge: &GeneratedMerge,
        span: &Span,
    ) -> Result<(), GeneratedBindError> {
        let canonical: HashMap<String, SortKey> = match output {
            ValueShape::Scalar(sort) => [
                ("old".to_owned(), sort.clone()),
                ("new".to_owned(), sort.clone()),
            ]
            .into_iter()
            .collect(),
            ValueShape::Tuple(sorts) => sorts
                .iter()
                .enumerate()
                .flat_map(|(index, sort)| {
                    [
                        (format!("old{index}"), sort.clone()),
                        (format!("new{index}"), sort.clone()),
                    ]
                })
                .collect(),
        };
        let mut scope = PortableScope::default();
        for action in &merge.actions.0 {
            visit_action_vars(action, &mut |var_span, variable| {
                if let Some(expected) = canonical.get(&variable.name) {
                    if expected != &variable.sort {
                        return Err(GeneratedBindError::InvalidMergeVariable {
                            name: variable.name.clone(),
                            span: var_span.clone(),
                        });
                    }
                    scope.observe(variable, var_span)
                } else {
                    Ok(())
                }
            })?;
        }
        visit_expr_vars(&merge.result, &mut |var_span, variable| {
            if let Some(expected) = canonical.get(&variable.name) {
                if expected != &variable.sort {
                    return Err(GeneratedBindError::InvalidMergeVariable {
                        name: variable.name.clone(),
                        span: var_span.clone(),
                    });
                }
                scope.observe(variable, var_span)
            } else {
                Ok(())
            }
        })?;
        Self::verify_actions(&merge.actions, &mut scope)?;
        let result = Self::verify_expr(&merge.result, &scope)?;
        if let ValueShape::Tuple(sorts) = output
            && !matches!(
                &merge.result,
                GenericExpr::Call(_, CallKey::Values(result_sorts), _)
                    if result_sorts == sorts
            )
        {
            return Err(GeneratedBindError::TupleMergeResult {
                name: name.to_owned(),
                span: span.clone(),
            });
        }
        let expected = match output {
            ValueShape::Scalar(sort) => VerifiedValueShape::Scalar(sort),
            ValueShape::Tuple(sorts) => VerifiedValueShape::Tuple(sorts),
        };
        if !result.same_shape(expected) {
            return Err(GeneratedBindError::ShapeMismatch {
                expected: expected.stable_name(),
                actual: result.stable_name(),
                span: span.clone(),
            });
        }
        Ok(())
    }

    fn verify_function(decl: &GeneratedFunctionDecl) -> Result<(), GeneratedBindError> {
        let CallKey::Function(key) = &decl.resolved_schema else {
            return Err(GeneratedBindError::FunctionMetadataMismatch {
                name: decl.name.clone(),
                span: decl.span.clone(),
            });
        };
        Self::verify_value_shape(&key.output, &decl.span)?;
        let outputs = match &key.output {
            ValueShape::Scalar(sort) => vec![sort.name.clone()],
            ValueShape::Tuple(sorts) => sorts.iter().map(|sort| sort.name.clone()).collect(),
        };
        let expected_schema = Schema::new_tuple(
            key.inputs.iter().map(|sort| sort.name.clone()).collect(),
            outputs,
        );
        if decl.name != key.name
            || decl.subtype != key.subtype
            || decl.schema != expected_schema
            || (decl.subtype == FunctionSubtype::Constructor && decl.merge.is_some())
        {
            return Err(GeneratedBindError::FunctionMetadataMismatch {
                name: decl.name.clone(),
                span: decl.span.clone(),
            });
        }
        if let Some(merge) = &decl.merge {
            Self::verify_merge(&decl.name, &key.output, merge, &decl.span)?;
        }
        Ok(())
    }

    fn verify_schedule(schedule: &GeneratedSchedule) -> Result<(), GeneratedBindError> {
        match schedule {
            GenericSchedule::Saturate(_, schedule) | GenericSchedule::Repeat(_, _, schedule) => {
                Self::verify_schedule(schedule)
            }
            GenericSchedule::Sequence(_, schedules) => {
                for schedule in schedules {
                    Self::verify_schedule(schedule)?;
                }
                Ok(())
            }
            GenericSchedule::Run(_, config) => {
                if let Some(facts) = &config.until {
                    let scope = Self::query_scope(facts)?;
                    for fact in facts {
                        Self::verify_fact(fact, &scope)?;
                    }
                }
                Ok(())
            }
        }
    }

    /// Verify exactly one lexical command. `Fail` children are deliberately
    /// excluded: the binder invokes this method separately for each child just
    /// before binding it, so earlier declaration commits remain visible if a
    /// later child is invalid.
    fn verify_command(kind: &GeneratedCommandKind) -> Result<(), GeneratedBindError> {
        match kind {
            GeneratedCommandKind::Sort(decl) => {
                if decl.key.name.is_empty() {
                    return Err(
                        TypeError::UndefinedSort(decl.key.name.clone(), decl.span.clone()).into(),
                    );
                }
            }
            GeneratedCommandKind::Function(decl) => Self::verify_function(decl)?,
            GeneratedCommandKind::Index(_) => {}
            GeneratedCommandKind::Rule(rule) => Self::verify_rule(rule)?,
            GeneratedCommandKind::Action(GenericAction::Let(span, _, _)) => {
                return Err(GeneratedBindError::TopLevelLet { span: span.clone() });
            }
            GeneratedCommandKind::Action(action) => {
                Self::verify_action(action, &mut PortableScope::default())?;
            }
            GeneratedCommandKind::Actions(actions) => {
                Self::verify_actions(actions, &mut PortableScope::default())?;
            }
            GeneratedCommandKind::Extract(_, expr, variants) => {
                let expr_shape = Self::verify_expr(expr, &PortableScope::default())?;
                if expr_shape.is_tuple() {
                    return Err(GeneratedBindError::CannotExtractTuple {
                        actual: expr_shape.stable_name(),
                        span: match expr {
                            GenericExpr::Var(span, _)
                            | GenericExpr::Call(span, _, _)
                            | GenericExpr::Lit(span, _) => span.clone(),
                        },
                    });
                }
                let variants_shape = Self::verify_expr(variants, &PortableScope::default())?;
                if !variants_shape.same_shape(VerifiedValueShape::Literal("i64")) {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: "i64".to_owned(),
                        actual: variants_shape.stable_name(),
                        span: match variants {
                            GenericExpr::Var(span, _)
                            | GenericExpr::Call(span, _, _)
                            | GenericExpr::Lit(span, _) => span.clone(),
                        },
                    });
                }
            }
            GeneratedCommandKind::Schedule(schedule) => Self::verify_schedule(schedule)?,
            GeneratedCommandKind::Check(_, facts) => {
                let scope = Self::query_scope(facts)?;
                for fact in facts {
                    Self::verify_fact(fact, &scope)?;
                }
            }
            GeneratedCommandKind::ProveExists(_, function) => {
                Self::verify_value_shape(&function.output, &Span::Panic)?;
            }
            GeneratedCommandKind::Output { exprs, .. } => {
                for expr in exprs {
                    let span = match expr {
                        GenericExpr::Var(span, _)
                        | GenericExpr::Call(span, _, _)
                        | GenericExpr::Lit(span, _) => span,
                    };
                    let shape = Self::verify_expr(expr, &PortableScope::default())?;
                    if shape.is_tuple() {
                        return Err(GeneratedBindError::ShapeMismatch {
                            expected: "scalar output expression".to_owned(),
                            actual: shape.stable_name(),
                            span: span.clone(),
                        });
                    }
                }
            }
            GeneratedCommandKind::Fail(span, commands) if commands.is_empty() => {
                return Err(GeneratedBindError::EmptyFail { span: span.clone() });
            }
            GeneratedCommandKind::Fail(..)
            | GeneratedCommandKind::AddRuleset(..)
            | GeneratedCommandKind::CombinedRuleset(..)
            | GeneratedCommandKind::PrintOverallStatistics(..)
            | GeneratedCommandKind::PrintFunction(..)
            | GeneratedCommandKind::PrintSize(..)
            | GeneratedCommandKind::Push(..)
            | GeneratedCommandKind::Pop(..)
            | GeneratedCommandKind::Input { .. } => {}
        }
        Ok(())
    }
}

struct ExpressionBinder<'a> {
    type_info: &'a TypeInfo,
    state: &'a mut BindingState,
}

impl ExpressionBinder<'_> {
    fn bind_variable(
        &mut self,
        span: &Span,
        variable: GeneratedVar,
        scope: &LocalScope,
    ) -> Result<ResolvedVar, GeneratedBindError> {
        if let Some(resolved) = scope.by_id.get(&variable.id) {
            if resolved.name != variable.name || !variable.sort.matches_sort(&resolved.sort) {
                return Err(GeneratedBindError::InconsistentLocalId {
                    id: variable.id.0,
                    span: span.clone(),
                });
            }
            return Ok(ResolvedVar {
                name: variable.name,
                sort: resolved.sort.clone(),
                is_global_ref: resolved.is_global_ref,
            });
        }
        if let Some(global) = self.type_info.get_global_sort(&variable.name) {
            if !variable.sort.matches_sort(global) {
                return Err(GeneratedBindError::ShapeMismatch {
                    expected: variable.sort.name,
                    actual: global.name().to_owned(),
                    span: span.clone(),
                });
            }
            return Ok(ResolvedVar {
                name: variable.name,
                sort: global.clone(),
                is_global_ref: true,
            });
        }
        Err(GeneratedBindError::UndeclaredLocal {
            id: variable.id.0,
            name: variable.name,
            span: span.clone(),
        })
    }

    fn prepare_query_scope(
        &mut self,
        facts: &[GeneratedFact],
    ) -> Result<LocalScope, GeneratedBindError> {
        let mut scope = LocalScope::default();
        for fact in facts {
            visit_fact_vars(fact, &mut |span, variable| {
                if let Some(existing) = scope.by_id.get(&variable.id) {
                    if existing.name != variable.name || !variable.sort.matches_sort(&existing.sort)
                    {
                        return Err(GeneratedBindError::InconsistentLocalId {
                            id: variable.id.0,
                            span: span.clone(),
                        });
                    }
                    return Ok(());
                }
                if let Some(global) = self.type_info.get_global_sort(&variable.name) {
                    if !variable.sort.matches_sort(global) {
                        return Err(GeneratedBindError::ShapeMismatch {
                            expected: variable.sort.name.clone(),
                            actual: global.name().to_owned(),
                            span: span.clone(),
                        });
                    }
                    return Ok(());
                }
                let expected = self
                    .state
                    .resolve_sort(self.type_info, &variable.sort, span)?;
                scope.declare(
                    variable,
                    ResolvedVar {
                        name: variable.name.clone(),
                        sort: expected,
                        is_global_ref: false,
                    },
                    span,
                )
            })?;
        }
        Ok(scope)
    }

    fn prepare_merge_scope(
        &mut self,
        merge: &GeneratedMerge,
        output: &ValueShape,
    ) -> Result<LocalScope, GeneratedBindError> {
        let canonical: HashSet<String> = match output {
            ValueShape::Scalar(_) => ["old".to_owned(), "new".to_owned()].into_iter().collect(),
            ValueShape::Tuple(sorts) => (0..sorts.len())
                .flat_map(|index| [format!("old{index}"), format!("new{index}")])
                .collect(),
        };
        let mut scope = LocalScope::default();
        let mut observe = |span: &Span, variable: &GeneratedVar| {
            if !canonical.contains(&variable.name) {
                return Ok(());
            }
            if let Some(existing) = scope.by_id.get(&variable.id) {
                if existing.name != variable.name || !variable.sort.matches_sort(&existing.sort) {
                    return Err(GeneratedBindError::InconsistentLocalId {
                        id: variable.id.0,
                        span: span.clone(),
                    });
                }
                return Ok(());
            }
            let sort = self
                .state
                .resolve_sort(self.type_info, &variable.sort, span)?;
            scope.declare(
                variable,
                ResolvedVar {
                    name: variable.name.clone(),
                    sort,
                    is_global_ref: false,
                },
                span,
            )
        };
        for action in &merge.actions.0 {
            visit_action_vars(action, &mut observe)?;
        }
        visit_expr_vars(&merge.result, &mut observe)?;
        Ok(scope)
    }

    fn bind_expr(
        &mut self,
        expr: GeneratedExpr,
        scope: &LocalScope,
        context: Context,
    ) -> Result<ResolvedExpr, GeneratedBindError> {
        match expr {
            GenericExpr::Var(span, variable) => {
                let resolved = self.bind_variable(&span, variable, scope)?;
                Ok(GenericExpr::Var(span, resolved))
            }
            GenericExpr::Lit(span, literal) => Ok(GenericExpr::Lit(span, literal)),
            GenericExpr::Call(span, key, args) => {
                let (call, args) = self.bind_call_application(&span, &key, args, scope, context)?;
                Ok(GenericExpr::Call(span, call, args))
            }
        }
    }

    fn bind_call_application(
        &mut self,
        span: &Span,
        key: &CallKey,
        args: Vec<GeneratedExpr>,
        scope: &LocalScope,
        context: Context,
    ) -> Result<(ResolvedCall, Vec<ResolvedExpr>), GeneratedBindError> {
        let args = args
            .into_iter()
            .map(|arg| self.bind_expr(arg, scope, context))
            .collect::<Result<Vec<_>, _>>()?;
        let call = self
            .state
            .resolve_call(self.type_info, key, context, span)?;
        Ok((call, args))
    }

    /// Recover the universe-local output sort from an expression that the
    /// linear verifier has already proven scalar. This avoids a second keyed
    /// sort lookup for every generated `let` while retaining unionability
    /// checks against the actual target universe.
    fn resolved_verified_scalar_sort(expr: &ResolvedExpr) -> ArcSort {
        match expr {
            GenericExpr::Var(_, variable) => variable.sort.clone(),
            GenericExpr::Lit(_, literal) => crate::sort::literal_sort(literal),
            GenericExpr::Call(_, ResolvedCall::Func(function), _) => {
                debug_assert_eq!(function.outputs.len(), 1);
                function.output().clone()
            }
            GenericExpr::Call(_, ResolvedCall::Primitive(primitive), _) => {
                primitive.output().clone()
            }
            GenericExpr::Call(_, ResolvedCall::Values(_), _) => {
                unreachable!("linear verifier rejects tuple-valued scalar expressions")
            }
        }
    }

    fn bind_fact(
        &mut self,
        fact: GeneratedFact,
        scope: &LocalScope,
        context: Context,
    ) -> Result<ResolvedFact, GeneratedBindError> {
        match fact {
            GenericFact::Eq(span, left, right) => {
                let left = self.bind_expr(left, scope, context)?;
                let right = self.bind_expr(right, scope, context)?;
                Ok(GenericFact::Eq(span, left, right))
            }
            GenericFact::Fact(expr) => Ok(GenericFact::Fact(self.bind_expr(expr, scope, context)?)),
        }
    }

    fn bind_action(
        &mut self,
        action: GeneratedAction,
        scope: &mut LocalScope,
        context: Context,
    ) -> Result<ResolvedAction, GeneratedBindError> {
        match action {
            GenericAction::Let(span, variable, expr) => {
                if scope.by_id.contains_key(&variable.id)
                    || scope.by_name.contains_key(&variable.name)
                {
                    return Err(GeneratedBindError::DuplicateLocal {
                        name: variable.name,
                        span,
                    });
                }
                let expr = self.bind_expr(expr, scope, context)?;
                let sort = Self::resolved_verified_scalar_sort(&expr);
                let resolved = ResolvedVar {
                    name: variable.name.clone(),
                    sort,
                    is_global_ref: false,
                };
                scope.declare(&variable, resolved.clone(), &span)?;
                Ok(GenericAction::Let(span, resolved, expr))
            }
            GenericAction::Set(span, head, args, value) => {
                let CallKey::Function(function) = &head else {
                    unreachable!("linear verifier rejects non-function set targets")
                };
                if function.subtype == FunctionSubtype::Constructor {
                    return Err(
                        TypeError::SetConstructorDisallowed(function.name.clone(), span).into(),
                    );
                }
                let (call, args) =
                    self.bind_call_application(&span, &head, args, scope, context)?;
                let value = self.bind_expr(value, scope, context)?;
                Ok(GenericAction::Set(span, call, args, value))
            }
            GenericAction::Change(span, change, head, args) => {
                let (call, args) =
                    self.bind_call_application(&span, &head, args, scope, context)?;
                Ok(GenericAction::Change(span, change, call, args))
            }
            GenericAction::Union(span, left, right) => {
                let left = self.bind_expr(left, scope, context)?;
                let right = self.bind_expr(right, scope, context)?;
                let sort = Self::resolved_verified_scalar_sort(&left);
                if !self.type_info.is_sort_unionable(&sort) {
                    return if sort.is_eq_sort() {
                        Err(TypeError::NonUnionableSort(sort, span).into())
                    } else {
                        Err(TypeError::NonEqsortUnion(sort, span).into())
                    };
                }
                Ok(GenericAction::Union(span, left, right))
            }
            GenericAction::Panic(span, message) => Ok(GenericAction::Panic(span, message)),
            GenericAction::Expr(span, expr) => {
                let expr = self.bind_expr(expr, scope, context)?;
                Ok(GenericAction::Expr(span, expr))
            }
        }
    }

    fn bind_actions(
        &mut self,
        actions: GeneratedActions,
        scope: &mut LocalScope,
        context: Context,
    ) -> Result<ResolvedActions, GeneratedBindError> {
        let mut resolved = Vec::with_capacity(actions.0.len());
        for action in actions.0 {
            resolved.push(self.bind_action(action, scope, context)?);
        }
        Ok(GenericActions(resolved))
    }

    fn bind_rule(
        &mut self,
        rule: GeneratedRule,
        global_seminaive: bool,
    ) -> Result<ResolvedRule, GeneratedBindError> {
        let use_read_contexts = !global_seminaive
            || matches!(
                rule.eval_mode,
                RuleEvalMode::Naive | RuleEvalMode::UnsafeSeminaive
            );
        let (query_context, action_context) = if use_read_contexts {
            (Context::Read, Context::Full)
        } else {
            (Context::Pure, Context::Write)
        };
        let scope = self.prepare_query_scope(&rule.body)?;
        let body = rule
            .body
            .into_iter()
            .map(|fact| self.bind_fact(fact, &scope, query_context))
            .collect::<Result<Vec<_>, _>>()?;
        let mut head_scope = scope;
        let head = self.bind_actions(rule.head, &mut head_scope, action_context)?;
        if action_context == Context::Write {
            self.type_info.check_no_function_lookups_in_actions(&head)?;
        }
        Ok(GenericRule {
            span: rule.span,
            head,
            body,
            name: rule.name,
            ruleset: rule.ruleset,
            eval_mode: rule.eval_mode,
            no_decomp: rule.no_decomp,
            include_subsumed: rule.include_subsumed,
        })
    }

    fn bind_query_facts(
        &mut self,
        facts: Vec<GeneratedFact>,
        context: Context,
    ) -> Result<Vec<ResolvedFact>, GeneratedBindError> {
        let scope = self.prepare_query_scope(&facts)?;
        facts
            .into_iter()
            .map(|fact| self.bind_fact(fact, &scope, context))
            .collect()
    }

    fn bind_schedule(
        &mut self,
        schedule: GeneratedSchedule,
    ) -> Result<ResolvedSchedule, GeneratedBindError> {
        match schedule {
            GenericSchedule::Saturate(span, schedule) => Ok(GenericSchedule::Saturate(
                span,
                Box::new(self.bind_schedule(*schedule)?),
            )),
            GenericSchedule::Repeat(span, count, schedule) => Ok(GenericSchedule::Repeat(
                span,
                count,
                Box::new(self.bind_schedule(*schedule)?),
            )),
            GenericSchedule::Sequence(span, schedules) => Ok(GenericSchedule::Sequence(
                span,
                schedules
                    .into_iter()
                    .map(|schedule| self.bind_schedule(schedule))
                    .collect::<Result<_, _>>()?,
            )),
            GenericSchedule::Run(span, config) => Ok(GenericSchedule::Run(
                span,
                ResolvedRunConfig {
                    ruleset: config.ruleset,
                    until: config
                        .until
                        .map(|facts| self.bind_query_facts(facts, Context::Read))
                        .transpose()?,
                },
            )),
        }
    }
}

struct GeneratedBinder<'a> {
    egraph: &'a mut EGraph,
    state: BindingState,
}

impl GeneratedBinder<'_> {
    fn bind_sort(
        &mut self,
        decl: GeneratedSortDecl,
    ) -> Result<ResolvedNCommand, GeneratedBindError> {
        let sort = self.egraph.prepare_sort_declaration(
            decl.key.name.clone(),
            &decl.presort_and_args,
            &decl.span,
        )?;
        if sort.name() != decl.key.name {
            return Err(GeneratedBindError::SortNameMismatch {
                expected: decl.key.name,
                actual: sort.name().to_owned(),
                span: decl.span,
            });
        }
        let actual = if sort.is_eq_container_sort() {
            SortSemanticClass::EqContainer
        } else if sort.is_eq_sort() {
            SortSemanticClass::Eq
        } else {
            SortSemanticClass::Value
        };
        if actual != decl.key.class {
            return Err(GeneratedBindError::SortClassMismatch {
                name: decl.key.name,
                expected: decl.key.class,
                actual,
                span: decl.span,
            });
        }
        self.egraph.register_prepared_sort_declaration(
            sort,
            SortDeclarationMetadata {
                span: &decl.span,
                name: &decl.key.name,
                uf: &decl.uf,
                container_rebuild: &decl.container_rebuild,
                proof_constructors: &decl.proof_constructors,
                unionable: decl.unionable,
            },
        )?;
        // Resolve through the ordinary cache after commit so later siblings
        // observe exactly the same universe-local ArcSort as all other keys.
        self.state
            .resolve_sort(self.egraph.type_info(), &decl.key, &decl.span)?;
        if !self.state.suppress_detailed_stats {
            self.state.stats.declarations_registered += 1;
        }
        Ok(ResolvedNCommand::Sort {
            span: decl.span,
            name: decl.key.name,
            presort_and_args: decl.presort_and_args,
            uf: decl.uf,
            container_rebuild: decl.container_rebuild,
            proof_constructors: decl.proof_constructors,
            unionable: decl.unionable,
        })
    }

    fn source_function_metadata(decl: &GeneratedFunctionDecl) -> FunctionDecl {
        FunctionDecl {
            name: decl.name.clone(),
            subtype: decl.subtype,
            schema: decl.schema.clone(),
            resolved_schema: String::new(),
            merge: None,
            cost: decl.cost,
            unextractable: decl.unextractable,
            internal_hidden: decl.internal_hidden,
            internal_let: decl.internal_let,
            span: decl.span.clone(),
            term_constructor: decl.term_constructor.clone(),
            identity_vals: decl.identity_vals,
            internal_term_node: decl.internal_term_node,
        }
    }

    fn bind_function(
        &mut self,
        decl: GeneratedFunctionDecl,
    ) -> Result<ResolvedNCommand, GeneratedBindError> {
        let CallKey::Function(key) = decl.resolved_schema.clone() else {
            unreachable!("linear verifier checks function schema heads")
        };
        let source = Self::source_function_metadata(&decl);
        let ftype = self.egraph.type_info().prepare_function_type(&source)?;
        let generated_merge = decl.merge;
        let state = &mut self.state;
        let merge =
            self.egraph
                .type_info()
                .bind_with_provisional_function(ftype.clone(), |type_info| {
                    let Some(generated_merge) = generated_merge else {
                        return Ok::<_, GeneratedBindError>(None);
                    };
                    let mut binder = ExpressionBinder { type_info, state };
                    let mut scope = binder.prepare_merge_scope(&generated_merge, &key.output)?;
                    let actions =
                        binder.bind_actions(generated_merge.actions, &mut scope, Context::Write)?;
                    let result =
                        binder.bind_expr(generated_merge.result, &scope, Context::Write)?;
                    Ok::<_, GeneratedBindError>(Some(crate::ast::ResolvedMerge { actions, result }))
                })?;
        let resolved = ResolvedFunctionDecl {
            name: decl.name,
            subtype: decl.subtype,
            schema: decl.schema,
            resolved_schema: ResolvedCall::Func(ftype),
            merge,
            cost: decl.cost,
            unextractable: decl.unextractable,
            internal_hidden: decl.internal_hidden,
            internal_let: decl.internal_let,
            span: decl.span,
            term_constructor: decl.term_constructor,
            identity_vals: decl.identity_vals,
            internal_term_node: decl.internal_term_node,
        };
        let receipt_call = resolved.resolved_schema.clone();
        self.egraph.register_resolved_function_metadata(&resolved);
        self.state
            .record_function_receipt(self.egraph.type_info(), key, receipt_call);
        if !self.state.suppress_detailed_stats {
            self.state.stats.declarations_registered += 1;
        }
        Ok(ResolvedNCommand::Function(resolved))
    }

    fn bind_index(
        &mut self,
        decl: GeneratedIndexDecl,
    ) -> Result<ResolvedNCommand, GeneratedBindError> {
        self.state.resolve_call(
            self.egraph.type_info(),
            &CallKey::Function(decl.function.clone()),
            Context::Read,
            &decl.span,
        )?;
        let prepared = self.egraph.prepare_index_declaration(
            &decl.span,
            &decl.name,
            &decl.function.name,
            &decl.any_of,
        )?;
        self.egraph.commit_index_declaration(&decl.span, prepared)?;
        let index_type = self
            .egraph
            .type_info()
            .get_func_type(&decl.name)
            .expect("committed index must expose its function type")
            .clone();
        self.state.record_function_receipt(
            self.egraph.type_info(),
            ResolvedPortableizer::function_key(&index_type),
            ResolvedCall::Func(index_type),
        );
        if !self.state.suppress_detailed_stats {
            self.state.stats.declarations_registered += 1;
        }
        Ok(ResolvedNCommand::Index {
            span: decl.span,
            name: decl.name,
            function: decl.function.name,
            any_of: decl.any_of,
        })
    }

    fn bind_command(
        &mut self,
        generated: GeneratedCommand,
    ) -> Result<BoundCommand, GeneratedBindError> {
        if self.state.suppress_detailed_stats {
            LinearVerifier::verify_command(&generated.kind)?;
        } else {
            let verifier_timer = Instant::now();
            LinearVerifier::verify_command(&generated.kind)?;
            self.state.stats.verifier_elapsed += verifier_timer.elapsed();
        }
        let origin = generated.origin;
        let mut nested_origins = Vec::new();
        let command = match generated.kind {
            GeneratedCommandKind::Sort(decl) => self.bind_sort(decl)?,
            GeneratedCommandKind::Function(decl) => self.bind_function(decl)?,
            GeneratedCommandKind::Index(decl) => self.bind_index(decl)?,
            GeneratedCommandKind::AddRuleset(span, name) => {
                ResolvedNCommand::AddRuleset(span, name)
            }
            GeneratedCommandKind::CombinedRuleset(span, name, rulesets) => {
                ResolvedNCommand::UnstableCombinedRuleset(span, name, rulesets)
            }
            GeneratedCommandKind::Rule(rule) => {
                let global_seminaive = self.egraph.seminaive;
                let type_info = self.egraph.type_info();
                let mut binder = ExpressionBinder {
                    type_info,
                    state: &mut self.state,
                };
                ResolvedNCommand::NormRule {
                    rule: binder.bind_rule(rule, global_seminaive)?,
                }
            }
            GeneratedCommandKind::Action(action) => {
                let type_info = self.egraph.type_info();
                let mut binder = ExpressionBinder {
                    type_info,
                    state: &mut self.state,
                };
                ResolvedNCommand::CoreAction(binder.bind_action(
                    action,
                    &mut LocalScope::default(),
                    Context::Full,
                )?)
            }
            GeneratedCommandKind::Actions(actions) => {
                let type_info = self.egraph.type_info();
                let mut binder = ExpressionBinder {
                    type_info,
                    state: &mut self.state,
                };
                ResolvedNCommand::CoreActions(binder.bind_actions(
                    actions,
                    &mut LocalScope::default(),
                    Context::Full,
                )?)
            }
            GeneratedCommandKind::Extract(span, expr, variants) => {
                let type_info = self.egraph.type_info();
                let mut binder = ExpressionBinder {
                    type_info,
                    state: &mut self.state,
                };
                let expr = binder.bind_expr(expr, &LocalScope::default(), Context::Full)?;
                let variants = binder.bind_expr(variants, &LocalScope::default(), Context::Full)?;
                ResolvedNCommand::Extract(span, expr, variants)
            }
            GeneratedCommandKind::Schedule(schedule) => {
                let type_info = self.egraph.type_info();
                let mut binder = ExpressionBinder {
                    type_info,
                    state: &mut self.state,
                };
                ResolvedNCommand::RunSchedule(binder.bind_schedule(schedule)?)
            }
            GeneratedCommandKind::PrintOverallStatistics(span, file) => {
                ResolvedNCommand::PrintOverallStatistics(span, file)
            }
            GeneratedCommandKind::Check(span, facts) => {
                let type_info = self.egraph.type_info();
                let mut binder = ExpressionBinder {
                    type_info,
                    state: &mut self.state,
                };
                ResolvedNCommand::Check(span, binder.bind_query_facts(facts, Context::Read)?)
            }
            GeneratedCommandKind::PrintFunction(span, name, limit, file, mode) => {
                ResolvedNCommand::PrintFunction(span, name, limit, file, mode)
            }
            GeneratedCommandKind::ProveExists(span, function) => {
                let call = self.state.resolve_call(
                    self.egraph.type_info(),
                    &CallKey::Function(function),
                    Context::Read,
                    &span,
                )?;
                ResolvedNCommand::ProveExists(span, call)
            }
            GeneratedCommandKind::PrintSize(span, name) => ResolvedNCommand::PrintSize(span, name),
            GeneratedCommandKind::Output { span, file, exprs } => {
                let type_info = self.egraph.type_info();
                let mut binder = ExpressionBinder {
                    type_info,
                    state: &mut self.state,
                };
                let exprs = exprs
                    .into_iter()
                    .map(|expr| binder.bind_expr(expr, &LocalScope::default(), Context::Full))
                    .collect::<Result<_, _>>()?;
                ResolvedNCommand::Output { span, file, exprs }
            }
            GeneratedCommandKind::Push(count) => ResolvedNCommand::Push(count),
            GeneratedCommandKind::Pop(span, count) => ResolvedNCommand::Pop(span, count),
            GeneratedCommandKind::Fail(span, commands) => {
                let mut resolved = Vec::with_capacity(commands.len());
                for child in commands {
                    let child = self.bind_command(child)?;
                    nested_origins.extend(child.origins);
                    resolved.push(child.command);
                }
                ResolvedNCommand::Fail(span, resolved)
            }
            GeneratedCommandKind::Input { span, name, file } => {
                ResolvedNCommand::Input { span, name, file }
            }
        };
        if !self.state.suppress_detailed_stats {
            self.state.stats.commands_bound += 1;
        }
        let mut origins = Vec::with_capacity(1 + nested_origins.len());
        origins.push(origin);
        origins.extend(nested_origins);
        Ok(BoundCommand { origins, command })
    }
}

fn bind_generated_batch(
    egraph: &mut EGraph,
    batch: GeneratedBatch,
) -> Result<BoundBatch<'_>, GeneratedBindError> {
    let batch_timer = Instant::now();
    let mut profile = GeneratedBindProfile::default();
    let persistent_cache =
        std::mem::take(egraph.extension_state_or_default::<PersistentBindingCache>());
    let mut binder = GeneratedBinder {
        egraph,
        state: BindingState::from_persistent_cache(persistent_cache),
    };
    let mut commands = Vec::with_capacity(batch.commands.len());
    if binder.state.suppress_detailed_stats {
        for command in batch.commands {
            commands.push(binder.bind_command(command)?);
        }
    } else {
        for command in batch.commands {
            let family = command.origin.family;
            let verifier_before = binder.state.stats.verifier_elapsed;
            let command_timer = Instant::now();
            commands.push(binder.bind_command(command)?);
            let elapsed = command_timer.elapsed();
            let verifier_elapsed = binder
                .state
                .stats
                .verifier_elapsed
                .saturating_sub(verifier_before);
            let family_index = match family {
                GeneratedFamily::ActionsGlobalsExtraction => 0,
                GeneratedFamily::RulesRebuildSubsumption => 1,
                GeneratedFamily::DeclarationsIndexes => 2,
                GeneratedFamily::MiscChecksSchedulesWrappers => 3,
            };
            let family = &mut profile.families[family_index];
            family.commands += 1;
            family.elapsed += elapsed;
            family.verifier_elapsed += verifier_elapsed;
        }
    }
    profile.elapsed = batch_timer.elapsed();
    let (stats, persistent_cache) = binder.state.finish_with_persistent_cache();
    *binder
        .egraph
        .extension_state_or_default::<PersistentBindingCache>() = persistent_cache;
    Ok(BoundBatch {
        egraph: binder.egraph,
        commands,
        stats,
        profile,
    })
}

#[derive(Default)]
struct ResolvedPortableScope {
    by_name: HashMap<String, GeneratedVar>,
}

struct ResolvedPortableizer<'a> {
    type_info: &'a TypeInfo,
    next_local_id: u32,
}

impl ResolvedPortableizer<'_> {
    fn sort_key(sort: &ArcSort) -> SortKey {
        SortKey::from_sort(sort)
    }

    fn value_shape(sorts: &[ArcSort]) -> ValueShape {
        if sorts.len() == 1 {
            ValueShape::Scalar(Self::sort_key(&sorts[0]))
        } else {
            ValueShape::Tuple(sorts.iter().map(Self::sort_key).collect())
        }
    }

    fn function_key(ftype: &crate::typechecking::FuncType) -> FunctionKey {
        FunctionKey {
            name: ftype.name.clone(),
            subtype: ftype.subtype,
            inputs: ftype.input.iter().map(Self::sort_key).collect(),
            output: Self::value_shape(&ftype.outputs),
        }
    }

    fn call_key(call: &ResolvedCall) -> CallKey {
        match call {
            ResolvedCall::Func(ftype) => CallKey::Function(Self::function_key(ftype)),
            ResolvedCall::Primitive(primitive) => CallKey::Primitive(PrimitiveKey {
                name: primitive.name().to_owned(),
                inputs: primitive.input().iter().map(Self::sort_key).collect(),
                output: Self::sort_key(primitive.output()),
            }),
            ResolvedCall::Values(sorts) => {
                CallKey::Values(sorts.iter().map(Self::sort_key).collect())
            }
        }
    }

    fn variable(
        &mut self,
        span: &Span,
        variable: ResolvedVar,
        scope: &mut ResolvedPortableScope,
    ) -> Result<GeneratedVar, GeneratedBindError> {
        let sort = Self::sort_key(&variable.sort);
        if let Some(existing) = scope.by_name.get(&variable.name) {
            if existing.sort != sort {
                return Err(GeneratedBindError::PortableLocalSortMismatch {
                    name: variable.name,
                    span: span.clone(),
                });
            }
            return Ok(existing.clone());
        }
        let generated = GeneratedVar {
            id: LocalId(self.next_local_id),
            name: variable.name.clone(),
            sort,
        };
        self.next_local_id = self.next_local_id.checked_add(1).unwrap_or_else(|| {
            panic!("generated binder shadow probe exhausted portable local ids")
        });
        scope.by_name.insert(variable.name, generated.clone());
        Ok(generated)
    }

    fn expr(
        &mut self,
        expr: ResolvedExpr,
        scope: &mut ResolvedPortableScope,
    ) -> Result<GeneratedExpr, GeneratedBindError> {
        match expr {
            GenericExpr::Var(span, variable) => Ok(GenericExpr::Var(
                span.clone(),
                self.variable(&span, variable, scope)?,
            )),
            GenericExpr::Lit(span, literal) => Ok(GenericExpr::Lit(span, literal)),
            GenericExpr::Call(span, call, args) => Ok(GenericExpr::Call(
                span,
                Self::call_key(&call),
                args.into_iter()
                    .map(|arg| self.expr(arg, scope))
                    .collect::<Result<_, _>>()?,
            )),
        }
    }

    fn fact(
        &mut self,
        fact: ResolvedFact,
        scope: &mut ResolvedPortableScope,
    ) -> Result<GeneratedFact, GeneratedBindError> {
        match fact {
            GenericFact::Eq(span, left, right) => Ok(GenericFact::Eq(
                span,
                self.expr(left, scope)?,
                self.expr(right, scope)?,
            )),
            GenericFact::Fact(expr) => Ok(GenericFact::Fact(self.expr(expr, scope)?)),
        }
    }

    fn facts(
        &mut self,
        facts: Vec<ResolvedFact>,
        scope: &mut ResolvedPortableScope,
    ) -> Result<Vec<GeneratedFact>, GeneratedBindError> {
        facts
            .into_iter()
            .map(|fact| self.fact(fact, scope))
            .collect()
    }

    fn action(
        &mut self,
        action: ResolvedAction,
        scope: &mut ResolvedPortableScope,
    ) -> Result<GeneratedAction, GeneratedBindError> {
        match action {
            GenericAction::Let(span, variable, expr) => {
                let expr = self.expr(expr, scope)?;
                let variable = self.variable(&span, variable, scope)?;
                Ok(GenericAction::Let(span, variable, expr))
            }
            GenericAction::Set(span, call, args, value) => Ok(GenericAction::Set(
                span,
                Self::call_key(&call),
                args.into_iter()
                    .map(|arg| self.expr(arg, scope))
                    .collect::<Result<_, _>>()?,
                self.expr(value, scope)?,
            )),
            GenericAction::Change(span, change, call, args) => Ok(GenericAction::Change(
                span,
                change,
                Self::call_key(&call),
                args.into_iter()
                    .map(|arg| self.expr(arg, scope))
                    .collect::<Result<_, _>>()?,
            )),
            GenericAction::Union(span, left, right) => Ok(GenericAction::Union(
                span,
                self.expr(left, scope)?,
                self.expr(right, scope)?,
            )),
            GenericAction::Panic(span, message) => Ok(GenericAction::Panic(span, message)),
            GenericAction::Expr(span, expr) => {
                Ok(GenericAction::Expr(span, self.expr(expr, scope)?))
            }
        }
    }

    fn actions(
        &mut self,
        actions: ResolvedActions,
        scope: &mut ResolvedPortableScope,
    ) -> Result<GeneratedActions, GeneratedBindError> {
        Ok(GenericActions(
            actions
                .0
                .into_iter()
                .map(|action| self.action(action, scope))
                .collect::<Result<_, _>>()?,
        ))
    }

    fn rule(&mut self, rule: ResolvedRule) -> Result<GeneratedRule, GeneratedBindError> {
        let mut scope = ResolvedPortableScope::default();
        let body = self.facts(rule.body, &mut scope)?;
        let head = self.actions(rule.head, &mut scope)?;
        Ok(GenericRule {
            span: rule.span,
            head,
            body,
            name: rule.name,
            ruleset: rule.ruleset,
            eval_mode: rule.eval_mode,
            no_decomp: rule.no_decomp,
            include_subsumed: rule.include_subsumed,
        })
    }

    fn schedule(
        &mut self,
        schedule: ResolvedSchedule,
    ) -> Result<GeneratedSchedule, GeneratedBindError> {
        match schedule {
            GenericSchedule::Saturate(span, schedule) => Ok(GenericSchedule::Saturate(
                span,
                Box::new(self.schedule(*schedule)?),
            )),
            GenericSchedule::Repeat(span, count, schedule) => Ok(GenericSchedule::Repeat(
                span,
                count,
                Box::new(self.schedule(*schedule)?),
            )),
            GenericSchedule::Sequence(span, schedules) => Ok(GenericSchedule::Sequence(
                span,
                schedules
                    .into_iter()
                    .map(|schedule| self.schedule(schedule))
                    .collect::<Result<_, _>>()?,
            )),
            GenericSchedule::Run(span, config) => {
                let until = config
                    .until
                    .map(|facts| self.facts(facts, &mut ResolvedPortableScope::default()))
                    .transpose()?;
                Ok(GenericSchedule::Run(
                    span,
                    GenericRunConfig {
                        ruleset: config.ruleset,
                        until,
                    },
                ))
            }
        }
    }

    fn function(
        &mut self,
        decl: ResolvedFunctionDecl,
    ) -> Result<GeneratedFunctionDecl, GeneratedBindError> {
        let ResolvedCall::Func(ftype) = &decl.resolved_schema else {
            return Err(GeneratedBindError::ExpectedResolvedFunction {
                head: decl.resolved_schema.name().to_owned(),
                span: decl.span,
            });
        };
        let merge = decl
            .merge
            .map(|merge| {
                let mut scope = ResolvedPortableScope::default();
                Ok::<_, GeneratedBindError>(crate::ast::GenericMerge {
                    actions: self.actions(merge.actions, &mut scope)?,
                    result: self.expr(merge.result, &mut scope)?,
                })
            })
            .transpose()?;
        Ok(GenericFunctionDecl {
            name: decl.name,
            subtype: decl.subtype,
            schema: decl.schema,
            resolved_schema: CallKey::Function(Self::function_key(ftype)),
            merge,
            cost: decl.cost,
            unextractable: decl.unextractable,
            internal_hidden: decl.internal_hidden,
            internal_let: decl.internal_let,
            span: decl.span,
            term_constructor: decl.term_constructor,
            identity_vals: decl.identity_vals,
            internal_term_node: decl.internal_term_node,
        })
    }

    fn command(
        &mut self,
        command: ResolvedNCommand,
        origin: GeneratedOrigin,
    ) -> Result<GeneratedCommand, GeneratedBindError> {
        let kind = match command {
            ResolvedNCommand::Sort {
                span,
                name,
                presort_and_args,
                uf,
                container_rebuild,
                proof_constructors,
                unionable,
            } => {
                let sort = self
                    .type_info
                    .get_sort_by_name(&name)
                    .ok_or_else(|| TypeError::UndefinedSort(name.clone(), span.clone()))?;
                GeneratedCommandKind::Sort(GeneratedSortDecl {
                    span,
                    key: Self::sort_key(sort),
                    presort_and_args,
                    uf,
                    container_rebuild,
                    proof_constructors,
                    unionable,
                })
            }
            ResolvedNCommand::Function(decl) => {
                GeneratedCommandKind::Function(self.function(decl)?)
            }
            ResolvedNCommand::Index {
                span,
                name,
                function,
                any_of,
            } => {
                let ftype = self
                    .type_info
                    .get_func_type(&function)
                    .ok_or_else(|| TypeError::UnboundFunction(function.clone(), span.clone()))?;
                GeneratedCommandKind::Index(GeneratedIndexDecl {
                    span,
                    name,
                    function: Self::function_key(ftype),
                    any_of,
                })
            }
            ResolvedNCommand::AddRuleset(span, name) => {
                GeneratedCommandKind::AddRuleset(span, name)
            }
            ResolvedNCommand::UnstableCombinedRuleset(span, name, members) => {
                GeneratedCommandKind::CombinedRuleset(span, name, members)
            }
            ResolvedNCommand::NormRule { rule } => GeneratedCommandKind::Rule(self.rule(rule)?),
            ResolvedNCommand::CoreAction(action) => GeneratedCommandKind::Action(
                self.action(action, &mut ResolvedPortableScope::default())?,
            ),
            ResolvedNCommand::CoreActions(actions) => GeneratedCommandKind::Actions(
                self.actions(actions, &mut ResolvedPortableScope::default())?,
            ),
            ResolvedNCommand::LetBegin(span, ..) => {
                return Err(GeneratedBindError::UnsupportedResolvedCommand {
                    command: "let-begin",
                    span,
                });
            }
            ResolvedNCommand::Extract(span, expr, variants) => {
                let mut scope = ResolvedPortableScope::default();
                GeneratedCommandKind::Extract(
                    span,
                    self.expr(expr, &mut scope)?,
                    self.expr(variants, &mut scope)?,
                )
            }
            ResolvedNCommand::RunSchedule(schedule) => {
                GeneratedCommandKind::Schedule(self.schedule(schedule)?)
            }
            ResolvedNCommand::PrintOverallStatistics(span, file) => {
                GeneratedCommandKind::PrintOverallStatistics(span, file)
            }
            ResolvedNCommand::Check(span, facts) => GeneratedCommandKind::Check(
                span,
                self.facts(facts, &mut ResolvedPortableScope::default())?,
            ),
            ResolvedNCommand::PrintFunction(span, name, limit, file, mode) => {
                GeneratedCommandKind::PrintFunction(span, name, limit, file, mode)
            }
            ResolvedNCommand::ProveExists(span, call) => {
                let ResolvedCall::Func(ftype) = call else {
                    return Err(GeneratedBindError::ExpectedResolvedFunction {
                        head: call.name().to_owned(),
                        span,
                    });
                };
                GeneratedCommandKind::ProveExists(span, Self::function_key(&ftype))
            }
            ResolvedNCommand::PrintSize(span, name) => GeneratedCommandKind::PrintSize(span, name),
            ResolvedNCommand::Output { span, file, exprs } => {
                let mut scope = ResolvedPortableScope::default();
                GeneratedCommandKind::Output {
                    span,
                    file,
                    exprs: exprs
                        .into_iter()
                        .map(|expr| self.expr(expr, &mut scope))
                        .collect::<Result<_, _>>()?,
                }
            }
            ResolvedNCommand::Push(count) => GeneratedCommandKind::Push(count),
            ResolvedNCommand::Pop(span, count) => GeneratedCommandKind::Pop(span, count),
            ResolvedNCommand::Fail(span, commands) => GeneratedCommandKind::Fail(
                span,
                commands
                    .into_iter()
                    .map(|command| self.command(command, origin))
                    .collect::<Result<_, _>>()?,
            ),
            ResolvedNCommand::Input { span, name, file } => {
                GeneratedCommandKind::Input { span, name, file }
            }
            ResolvedNCommand::UserDefined(span, ..) => {
                return Err(GeneratedBindError::UnsupportedResolvedCommand {
                    command: "user-defined",
                    span,
                });
            }
        };
        Ok(GeneratedCommand { origin, kind })
    }
}

#[derive(Clone, Debug, Default)]
struct ShadowFamilyRecord {
    surface_commands: usize,
    normalized_commands: usize,
    legacy_desugar: Duration,
    legacy_typecheck: Duration,
    legacy_global_removal: Duration,
    portableize: Duration,
    bind_elapsed: Duration,
    verifier_elapsed: Duration,
}

#[derive(Clone, Debug, Default)]
struct ShadowBatchRecord {
    sequence: usize,
    shadow_clone: Duration,
    differential_check: Duration,
    nested_fail_wrappers: usize,
    families: [ShadowFamilyRecord; 4],
    command_kinds: BTreeMap<&'static str, usize>,
    bind_stats: GeneratedBindStats,
    bind_profile: GeneratedBindProfile,
}

#[derive(Default)]
struct ShadowProbeSummary {
    batches: Vec<ShadowBatchRecord>,
}

static SHADOW_PROBE_ENABLED: AtomicBool = AtomicBool::new(false);
static SHADOW_PROBE_DETAILED: AtomicBool = AtomicBool::new(true);
static SHADOW_PROBE_SUMMARY: OnceLock<Mutex<ShadowProbeSummary>> = OnceLock::new();

pub(crate) fn enable_shadow_probe(fast_ablation: bool) {
    SHADOW_PROBE_ENABLED.store(true, Ordering::Relaxed);
    SHADOW_PROBE_DETAILED.store(!fast_ablation, Ordering::Relaxed);
    SHADOW_PROBE_SUMMARY.get_or_init(|| Mutex::new(ShadowProbeSummary::default()));
}

pub(crate) fn shadow_probe_enabled() -> bool {
    SHADOW_PROBE_ENABLED.load(Ordering::Relaxed)
}

fn record_command_kinds(
    command: &GeneratedCommandKind,
    counts: &mut BTreeMap<&'static str, usize>,
) {
    let name = match command {
        GeneratedCommandKind::Sort(_) => "sort",
        GeneratedCommandKind::Function(_) => "function",
        GeneratedCommandKind::Index(_) => "index",
        GeneratedCommandKind::AddRuleset(..) => "add_ruleset",
        GeneratedCommandKind::CombinedRuleset(..) => "combined_ruleset",
        GeneratedCommandKind::Rule(_) => "rule",
        GeneratedCommandKind::Action(_) => "action",
        GeneratedCommandKind::Actions(_) => "actions",
        GeneratedCommandKind::Extract(..) => "extract",
        GeneratedCommandKind::Schedule(_) => "schedule",
        GeneratedCommandKind::PrintOverallStatistics(..) => "print_overall_statistics",
        GeneratedCommandKind::Check(..) => "check",
        GeneratedCommandKind::PrintFunction(..) => "print_function",
        GeneratedCommandKind::ProveExists(..) => "prove_exists",
        GeneratedCommandKind::PrintSize(..) => "print_size",
        GeneratedCommandKind::Output { .. } => "output",
        GeneratedCommandKind::Push(..) => "push",
        GeneratedCommandKind::Pop(..) => "pop",
        GeneratedCommandKind::Fail(..) => "fail",
        GeneratedCommandKind::Input { .. } => "input",
    };
    *counts.entry(name).or_default() += 1;
    if let GeneratedCommandKind::Fail(_, children) = command {
        for child in children {
            record_command_kinds(&child.kind, counts);
        }
    }
}

/// Opt-in migration probe. The exact legacy generated frontend runs on an
/// isolated clone, its resolved AST is stripped down to portable names/sorts,
/// and only then is the portable batch bound into the real execution universe.
/// The returned commands are required to equal the legacy shadow commands.
pub(crate) fn resolve_with_shadow_probe(
    egraph: &mut EGraph,
    generated: Vec<TaggedGeneratedCommand>,
) -> Result<Vec<ResolvedNCommand>, EgglogError> {
    let clone_timer = Instant::now();
    let mut shadow = egraph.clone();
    let mut record = ShadowBatchRecord {
        shadow_clone: clone_timer.elapsed(),
        ..Default::default()
    };
    let mut legacy_commands = Vec::new();
    let mut portable_commands = Vec::new();

    for tagged in generated {
        let (family, family_option) = match tagged.origin {
            GeneratedCommandOrigin::Family(family) => (family, Some(family)),
            GeneratedCommandOrigin::NestedFail { .. } => {
                record.nested_fail_wrappers += 1;
                (GeneratedFamily::MiscChecksSchedulesWrappers, None)
            }
        };
        let family_index = match family {
            GeneratedFamily::ActionsGlobalsExtraction => 0,
            GeneratedFamily::RulesRebuildSubsumption => 1,
            GeneratedFamily::DeclarationsIndexes => 2,
            GeneratedFamily::MiscChecksSchedulesWrappers => 3,
        };
        record.families[family_index].surface_commands += 1;

        let desugar_timer = Instant::now();
        let desugared = crate::ast::desugar::desugar_command(
            tagged.command,
            &mut shadow.parser,
            shadow.proof_state.proof_testing,
        )?;
        let desugar_elapsed = desugar_timer.elapsed();
        record.families[family_index].legacy_desugar += desugar_elapsed;
        if let Some(attribution) = egraph.proof_state.generated_frontend_attribution.as_mut() {
            attribution.record_desugar(family_option, desugar_elapsed, desugared.len());
        }

        let typecheck_timer = Instant::now();
        let typechecked = shadow.typecheck_program(&desugared)?;
        let typecheck_elapsed = typecheck_timer.elapsed();
        record.families[family_index].legacy_typecheck += typecheck_elapsed;
        egraph.overall_report.typecheck += typecheck_elapsed;
        if let Some(attribution) = egraph.proof_state.generated_frontend_attribution.as_mut() {
            attribution.record_typecheck(family_option, typecheck_elapsed);
        }

        let global_removal_timer = Instant::now();
        let typechecked =
            remove_globals::remove_globals(typechecked, &mut shadow.parser.symbol_gen);
        let global_removal_elapsed = global_removal_timer.elapsed();
        record.families[family_index].legacy_global_removal += global_removal_elapsed;
        if let Some(attribution) = egraph.proof_state.generated_frontend_attribution.as_mut() {
            attribution.record_global_removal(family_option, global_removal_elapsed);
        }

        let origin = GeneratedOrigin {
            family,
            role: match family {
                GeneratedFamily::ActionsGlobalsExtraction => GeneratedRole::SourceDerived,
                GeneratedFamily::RulesRebuildSubsumption => GeneratedRole::Maintenance,
                GeneratedFamily::DeclarationsIndexes => GeneratedRole::PendingDeclaration,
                GeneratedFamily::MiscChecksSchedulesWrappers => GeneratedRole::ControlWrapper,
            },
        };
        for command in typechecked {
            let portableize_timer = Instant::now();
            let portable = ResolvedPortableizer {
                type_info: shadow.type_info(),
                next_local_id: 0,
            }
            .command(command.clone(), origin)?;
            record.families[family_index].portableize += portableize_timer.elapsed();
            record.families[family_index].normalized_commands += 1;
            record_command_kinds(&portable.kind, &mut record.command_kinds);
            legacy_commands.push(command);
            portable_commands.push(portable);
        }
    }

    // The shadow consumed precisely the fresh symbols the old real path would
    // have consumed. Carry only that deterministic counter state back; all type
    // registrations must come from the portable binder below.
    egraph.parser.symbol_gen = shadow.parser.symbol_gen;

    let BoundBatch {
        egraph: _,
        commands,
        stats,
        profile,
    } = bind_generated_batch(
        egraph,
        GeneratedBatch {
            commands: portable_commands,
        },
    )?;
    for (target, source) in record.families.iter_mut().zip(&profile.families) {
        target.bind_elapsed = source.elapsed;
        target.verifier_elapsed = source.verifier_elapsed;
    }
    record.bind_stats = stats;
    record.bind_profile = profile;

    let rebound_commands = commands
        .into_iter()
        .map(|bound| bound.command)
        .collect::<Vec<_>>();
    let differential_timer = Instant::now();
    if legacy_commands != rebound_commands {
        let mismatch = legacy_commands
            .iter()
            .zip(&rebound_commands)
            .position(|(legacy, rebound)| legacy != rebound)
            .unwrap_or_else(|| legacy_commands.len().min(rebound_commands.len()));
        let legacy = legacy_commands
            .get(mismatch)
            .map(|command| command.to_command().to_string())
            .unwrap_or_else(|| "<missing>".to_owned());
        let rebound = rebound_commands
            .get(mismatch)
            .map(|command| command.to_command().to_string())
            .unwrap_or_else(|| "<missing>".to_owned());
        return Err(EgglogError::DesugarError(
            crate::span!(),
            format!(
                "generated binder shadow probe diverged at normalized command {mismatch}:\nlegacy: {legacy}\nrebound: {rebound}"
            ),
        ));
    }
    record.differential_check = differential_timer.elapsed();

    let summary = SHADOW_PROBE_SUMMARY.get_or_init(|| Mutex::new(ShadowProbeSummary::default()));
    let mut summary = summary
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    record.sequence = summary.batches.len();
    summary.batches.push(record);
    Ok(rebound_commands)
}

#[cfg(feature = "bin")]
pub(crate) fn shadow_probe_json() -> serde_json::Value {
    let summary = SHADOW_PROBE_SUMMARY.get_or_init(|| Mutex::new(ShadowProbeSummary::default()));
    let summary = summary
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let nanos = |duration: Duration| duration.as_nanos().min(u64::MAX as u128) as u64;
    let family_names = [
        "actions_globals_extraction",
        "rules_rebuild_subsumption",
        "declarations_indexes",
        "misc_checks_schedules_wrappers",
    ];
    let mut total_clone = Duration::ZERO;
    let mut total_differential = Duration::ZERO;
    let mut total_bind = Duration::ZERO;
    let mut total_verifier = Duration::ZERO;
    let mut total_portableize = Duration::ZERO;
    let batches = summary
        .batches
        .iter()
        .map(|batch| {
            total_clone += batch.shadow_clone;
            total_differential += batch.differential_check;
            total_bind += batch.bind_profile.elapsed;
            total_verifier += batch.bind_stats.verifier_elapsed;
            let mut families = serde_json::Map::new();
            for (name, family) in family_names.iter().zip(&batch.families) {
                total_portableize += family.portableize;
                families.insert(
                    (*name).to_owned(),
                    serde_json::json!({
                        "surface_commands": family.surface_commands,
                        "normalized_commands": family.normalized_commands,
                        "legacy_desugar_ns": nanos(family.legacy_desugar),
                        "legacy_typecheck_ns": nanos(family.legacy_typecheck),
                        "legacy_global_removal_ns": nanos(family.legacy_global_removal),
                        "portableize_probe_only_ns": nanos(family.portableize),
                        "verifier_ns": nanos(family.verifier_elapsed),
                        "binding_and_registration_ns": nanos(
                            family.bind_elapsed.saturating_sub(family.verifier_elapsed)
                        ),
                    }),
                );
            }
            let command_kinds = batch
                .command_kinds
                .iter()
                .map(|(kind, count)| ((*kind).to_owned(), serde_json::Value::from(*count)))
                .collect::<serde_json::Map<_, _>>();
            serde_json::json!({
                "sequence": batch.sequence,
                "shadow_clone_probe_only_ns": nanos(batch.shadow_clone),
                "differential_check_probe_only_ns": nanos(batch.differential_check),
                "nested_fail_wrappers": batch.nested_fail_wrappers,
                "command_kinds_including_fail_children": command_kinds,
                "families": families,
                "binder": {
                    "elapsed_ns": nanos(batch.bind_profile.elapsed),
                    "verifier_ns": nanos(batch.bind_stats.verifier_elapsed),
                    "binding_registration_and_orchestration_ns": nanos(
                        batch.bind_profile.elapsed.saturating_sub(batch.bind_stats.verifier_elapsed)
                    ),
                    "unique_sort_keys": batch.bind_stats.unique_sort_keys,
                    "unique_resolution_keys": batch.bind_stats.unique_resolution_keys,
                    "sort_cache_hits": batch.bind_stats.sort_cache_hits,
                    "sort_cache_misses": batch.bind_stats.sort_cache_misses,
                    "call_cache_hits": batch.bind_stats.call_cache_hits,
                    "call_cache_misses": batch.bind_stats.call_cache_misses,
                    "resolver_invocations": batch.bind_stats.resolver_invocations,
                    "registration_receipt_hits": batch.bind_stats.registration_receipt_hits,
                    "registration_receipt_hits_by_context": {
                        "pure": batch.bind_stats.registration_receipt_hits_by_context[Context::Pure],
                        "write": batch.bind_stats.registration_receipt_hits_by_context[Context::Write],
                        "read": batch.bind_stats.registration_receipt_hits_by_context[Context::Read],
                        "full": batch.bind_stats.registration_receipt_hits_by_context[Context::Full],
                    },
                    "resolver_invocations_by_context": {
                        "pure": batch.bind_stats.resolver_invocations_by_context[Context::Pure],
                        "write": batch.bind_stats.resolver_invocations_by_context[Context::Write],
                        "read": batch.bind_stats.resolver_invocations_by_context[Context::Read],
                        "full": batch.bind_stats.resolver_invocations_by_context[Context::Full],
                    },
                    "declarations_registered": batch.bind_stats.declarations_registered,
                    "commands_bound_including_fail_children": batch.bind_stats.commands_bound,
                },
                "differential_parity": true,
            })
        })
        .collect::<Vec<_>>();
    serde_json::json!({
        "schema_version": 1,
        "units": "nanoseconds",
        "mode": "legacy_frontend_on_shadow_then_portable_bind_on_real_outer",
        "detailed_per_command_profile": SHADOW_PROBE_DETAILED.load(Ordering::Relaxed),
        "measurement_boundary": {
            "projected_residual_includes": ["linear_verifier", "sort_and_call_binding", "declaration_registration", "binder_orchestration"],
            "projected_residual_excludes_probe_only": ["egraph_clone", "legacy_frontend", "resolved_ast_portableization", "differential_check"],
        },
        "batches": batches,
        "totals": {
            "batch_count": summary.batches.len(),
            "shadow_clone_probe_only_ns": nanos(total_clone),
            "portableize_probe_only_ns": nanos(total_portableize),
            "differential_check_probe_only_ns": nanos(total_differential),
            "projected_binder_residual_ns": nanos(total_bind),
            "verifier_ns": nanos(total_verifier),
            "binding_registration_and_orchestration_ns": nanos(total_bind.saturating_sub(total_verifier)),
        },
    })
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use crate::ast::{Change, GenericRunConfig};
    use crate::constraint::{SimpleTypeConstraint, TypeConstraint};
    use crate::prelude::BaseSort;
    use crate::sort::I64Sort;
    use crate::{
        Core, Primitive, PurePrim, PureState, ReadPrim, ReadState, Value, WritePrim, WriteState,
    };

    use super::*;

    fn value_sort(name: &str) -> SortKey {
        SortKey {
            name: name.to_owned(),
            class: SortSemanticClass::Value,
        }
    }

    fn eq_sort(name: &str) -> SortKey {
        SortKey {
            name: name.to_owned(),
            class: SortSemanticClass::Eq,
        }
    }

    fn function_key(name: &str, inputs: Vec<SortKey>, output: ValueShape) -> FunctionKey {
        FunctionKey {
            name: name.to_owned(),
            subtype: FunctionSubtype::Custom,
            inputs,
            output,
        }
    }

    fn constructor_key(name: &str, inputs: Vec<SortKey>, output: SortKey) -> FunctionKey {
        FunctionKey {
            name: name.to_owned(),
            subtype: FunctionSubtype::Constructor,
            inputs,
            output: ValueShape::Scalar(output),
        }
    }

    fn primitive_key(name: &str, inputs: Vec<SortKey>, output: SortKey) -> CallKey {
        CallKey::Primitive(PrimitiveKey {
            name: name.to_owned(),
            inputs,
            output,
        })
    }

    fn variable(id: u32, name: &str, sort: SortKey) -> GeneratedVar {
        GeneratedVar {
            id: LocalId(id),
            name: name.to_owned(),
            sort,
        }
    }

    fn origin(family: GeneratedFamily, role: GeneratedRole) -> GeneratedOrigin {
        GeneratedOrigin { family, role }
    }

    fn command(kind: GeneratedCommandKind) -> GeneratedCommand {
        GeneratedCommand {
            origin: origin(
                GeneratedFamily::MiscChecksSchedulesWrappers,
                GeneratedRole::ControlWrapper,
            ),
            kind,
        }
    }

    fn function_decl(key: FunctionKey, merge: Option<GeneratedMerge>) -> GeneratedFunctionDecl {
        let outputs = match &key.output {
            ValueShape::Scalar(sort) => vec![sort.name.clone()],
            ValueShape::Tuple(sorts) => sorts.iter().map(|sort| sort.name.clone()).collect(),
        };
        GeneratedFunctionDecl {
            name: key.name.clone(),
            subtype: key.subtype,
            schema: Schema::new_tuple(
                key.inputs.iter().map(|sort| sort.name.clone()).collect(),
                outputs,
            ),
            resolved_schema: CallKey::Function(key),
            merge,
            cost: None,
            unextractable: true,
            internal_hidden: false,
            internal_let: false,
            span: Span::Panic,
            term_constructor: None,
            identity_vals: None,
            internal_term_node: false,
        }
    }

    fn literal_i64(value: i64) -> GeneratedExpr {
        GenericExpr::Lit(Span::Panic, Literal::Int(value))
    }

    fn var_expr(variable: &GeneratedVar) -> GeneratedExpr {
        GenericExpr::Var(Span::Panic, variable.clone())
    }

    fn call(key: CallKey, args: Vec<GeneratedExpr>) -> GeneratedExpr {
        GenericExpr::Call(Span::Panic, key, args)
    }

    fn stable_projection(batch: &BoundBatch<'_>) -> Vec<String> {
        batch
            .commands
            .iter()
            .map(|bound| bound.command.to_command().to_string())
            .collect()
    }

    #[derive(Clone)]
    struct ReadEcho(&'static str);

    impl Primitive for ReadEcho {
        fn name(&self) -> &str {
            self.0
        }

        fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
            SimpleTypeConstraint::new(
                self.name(),
                vec![I64Sort.to_arcsort(), I64Sort.to_arcsort()],
                span.clone(),
            )
            .into_box()
        }
    }

    impl ReadPrim for ReadEcho {
        fn apply<'a, 'db>(&self, _state: ReadState<'a, 'db>, args: &[Value]) -> Option<Value> {
            Some(args[0])
        }
    }

    #[derive(Clone)]
    struct WriteEcho(&'static str);

    impl Primitive for WriteEcho {
        fn name(&self) -> &str {
            self.0
        }

        fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
            SimpleTypeConstraint::new(
                self.name(),
                vec![I64Sort.to_arcsort(), I64Sort.to_arcsort()],
                span.clone(),
            )
            .into_box()
        }
    }

    impl WritePrim for WriteEcho {
        fn apply<'a, 'db>(&self, _state: WriteState<'a, 'db>, args: &[Value]) -> Option<Value> {
            Some(args[0])
        }
    }

    #[derive(Clone)]
    struct DuplicateUnary(&'static str);

    impl Primitive for DuplicateUnary {
        fn name(&self) -> &str {
            self.0
        }

        fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
            SimpleTypeConstraint::new(
                self.name(),
                vec![I64Sort.to_arcsort(), I64Sort.to_arcsort()],
                span.clone(),
            )
            .into_box()
        }
    }

    impl PurePrim for DuplicateUnary {
        fn apply<'a, 'db>(&self, state: PureState<'a, 'db>, args: &[Value]) -> Option<Value> {
            let value = state.base_values().unwrap::<i64>(args[0]);
            Some(state.base_values().get(value))
        }
    }

    #[test]
    fn typed_merges_support_self_reference_sequential_lets_and_tuple_values() {
        let i64_key = value_sort("i64");
        let string_key = value_sort("String");
        let unit_key = value_sort("Unit");
        let meta_e = eq_sort("MergeMetaE");
        let scalar_key = function_key(
            "self-merge",
            vec![i64_key.clone()],
            ValueShape::Scalar(i64_key.clone()),
        );
        let old = variable(0, "old", i64_key.clone());
        let scalar_merge = GenericMerge {
            actions: GenericActions(vec![]),
            result: call(CallKey::Function(scalar_key.clone()), vec![var_expr(&old)]),
        };

        let tuple_key = function_key(
            "tuple-merge",
            vec![i64_key.clone()],
            ValueShape::Tuple(vec![i64_key.clone(), string_key.clone()]),
        );
        let old0 = variable(1, "old0", i64_key.clone());
        let new0 = variable(2, "new0", i64_key.clone());
        let old1 = variable(3, "old1", string_key.clone());
        let old_count = variable(4, "old_count", i64_key.clone());
        let staged = variable(5, "staged", i64_key.clone());
        let plus = primitive_key("+", vec![i64_key.clone(), i64_key.clone()], i64_key.clone());
        let tuple_merge = GenericMerge {
            actions: GenericActions(vec![
                GenericAction::Let(
                    Span::Panic,
                    old_count.clone(),
                    call(plus.clone(), vec![var_expr(&old0), var_expr(&new0)]),
                ),
                GenericAction::Let(
                    Span::Panic,
                    staged.clone(),
                    call(plus, vec![var_expr(&old_count), literal_i64(0)]),
                ),
            ]),
            result: call(
                CallKey::Values(vec![i64_key.clone(), string_key.clone()]),
                vec![var_expr(&staged), var_expr(&old1)],
            ),
        };
        let mut tuple_decl = function_decl(tuple_key.clone(), Some(tuple_merge));
        tuple_decl.identity_vals = Some(1);
        tuple_decl.internal_hidden = true;

        let fd_view_key = function_key(
            "fd-view-meta",
            vec![i64_key.clone()],
            ValueShape::Tuple(vec![meta_e.clone(), unit_key.clone()]),
        );
        let mut fd_view_decl = function_decl(fd_view_key, None);
        fd_view_decl.cost = Some(7);
        fd_view_decl.unextractable = false;
        fd_view_decl.internal_hidden = true;
        fd_view_decl.term_constructor = Some("MetaTerm".to_owned());
        fd_view_decl.identity_vals = Some(1);

        let global_key = function_key(
            "$generated-global-meta",
            vec![],
            ValueShape::Scalar(i64_key.clone()),
        );
        let mut global_decl = function_decl(global_key, None);
        global_decl.internal_let = true;

        let term_node_key = function_key(
            "term-node-meta",
            vec![i64_key.clone(), meta_e.clone()],
            ValueShape::Scalar(unit_key),
        );
        let mut term_node_decl = function_decl(term_node_key, None);
        term_node_decl.internal_term_node = true;

        let generation_before = EGraph::default().type_info().call_generation("self-merge");
        let mut egraph = EGraph::default();
        let batch = GeneratedBatch {
            commands: vec![
                command(GeneratedCommandKind::Sort(GeneratedSortDecl {
                    span: Span::Panic,
                    key: meta_e,
                    presort_and_args: None,
                    uf: None,
                    container_rebuild: None,
                    proof_constructors: None,
                    unionable: true,
                })),
                command(GeneratedCommandKind::Function(function_decl(
                    scalar_key,
                    Some(scalar_merge),
                ))),
                command(GeneratedCommandKind::Function(tuple_decl)),
                command(GeneratedCommandKind::Function(fd_view_decl)),
                command(GeneratedCommandKind::Function(global_decl)),
                command(GeneratedCommandKind::Function(term_node_decl)),
                command(GeneratedCommandKind::Action(GenericAction::Set(
                    Span::Panic,
                    CallKey::Function(tuple_key),
                    vec![literal_i64(0)],
                    call(
                        CallKey::Values(vec![i64_key, string_key]),
                        vec![
                            literal_i64(1),
                            GenericExpr::Lit(Span::Panic, Literal::String("value".to_owned())),
                        ],
                    ),
                ))),
            ],
        };
        let bound = bind_generated_batch(&mut egraph, batch).unwrap();
        assert_eq!(bound.stats.declarations_registered, 6);
        assert!(bound.egraph.type_info().call_generation("self-merge") > generation_before);
        let ResolvedNCommand::Function(scalar) = &bound.commands[1].command else {
            panic!("expected scalar function")
        };
        let scalar_result = &scalar.merge.as_ref().unwrap().result;
        assert!(matches!(
            scalar_result,
            GenericExpr::Call(_, ResolvedCall::Func(function), _)
                if function.name == "self-merge"
        ));
        let ResolvedNCommand::Function(tuple) = &bound.commands[2].command else {
            panic!("expected tuple function")
        };
        assert_eq!(tuple.identity_vals, Some(1));
        assert!(tuple.internal_hidden);
        let merge = tuple.merge.as_ref().unwrap();
        assert!(matches!(
            merge.actions.0.as_slice(),
            [GenericAction::Let(..), GenericAction::Let(..)]
        ));
        assert!(matches!(
            &merge.result,
            GenericExpr::Call(_, ResolvedCall::Values(sorts), _) if sorts.len() == 2
        ));
        let ResolvedNCommand::Function(fd_view) = &bound.commands[3].command else {
            panic!("expected FD view function")
        };
        assert_eq!(fd_view.cost, Some(7));
        assert!(!fd_view.unextractable);
        assert!(fd_view.internal_hidden);
        assert_eq!(fd_view.term_constructor.as_deref(), Some("MetaTerm"));
        assert_eq!(fd_view.identity_vals, Some(1));
        let ResolvedNCommand::Function(global) = &bound.commands[4].command else {
            panic!("expected generated global function")
        };
        assert!(global.internal_let);
        assert_eq!(
            bound
                .egraph
                .type_info()
                .get_global_sort("$generated-global-meta")
                .unwrap()
                .name(),
            "i64"
        );
        let ResolvedNCommand::Function(term_node) = &bound.commands[5].command else {
            panic!("expected term-node function")
        };
        assert!(term_node.internal_term_node);
        assert!(
            bound
                .egraph
                .type_info()
                .get_prims(&crate::proofs::proof_fresh::set_if_empty_prim_name(
                    "fd-view-meta"
                ))
                .is_some()
        );
        assert!(
            bound
                .egraph
                .type_info()
                .get_prims(&crate::proofs::proof_fresh::mint_prim_name(
                    "term-node-meta"
                ))
                .is_some()
        );
        let ResolvedNCommand::CoreAction(GenericAction::Set(_, _, _, value)) =
            &bound.commands[6].command
        else {
            panic!("expected tuple set action")
        };
        assert!(matches!(
            value,
            GenericExpr::Call(_, ResolvedCall::Values(sorts), _) if sorts.len() == 2
        ));
    }

    #[test]
    fn one_column_tuple_shapes_are_rejected_before_resolution() {
        let i64_key = value_sort("i64");
        let key = function_key(
            "one-column-tuple",
            vec![i64_key.clone()],
            ValueShape::Tuple(vec![i64_key.clone()]),
        );
        let mut egraph = EGraph::default();
        let error = bind_generated_batch(
            &mut egraph,
            GeneratedBatch {
                commands: vec![command(GeneratedCommandKind::Function(function_decl(
                    key, None,
                )))],
            },
        )
        .unwrap_err();
        assert!(matches!(
            error,
            GeneratedBindError::InvalidTupleArity { actual: 1, .. }
        ));
        assert!(
            egraph
                .type_info()
                .get_func_type("one-column-tuple")
                .is_none()
        );

        let error = bind_generated_batch(
            &mut egraph,
            GeneratedBatch {
                commands: vec![command(GeneratedCommandKind::Action(GenericAction::Expr(
                    Span::Panic,
                    call(CallKey::Values(vec![i64_key]), vec![literal_i64(0)]),
                )))],
            },
        )
        .unwrap_err();
        assert!(matches!(
            error,
            GeneratedBindError::InvalidTupleArity { actual: 1, .. }
        ));
    }

    #[test]
    fn action_block_covers_all_normalized_actions_with_sequential_scope() {
        let i64_key = value_sort("i64");
        let e_key = eq_sort("E");
        let score = function_key(
            "score",
            vec![i64_key.clone()],
            ValueShape::Scalar(i64_key.clone()),
        );
        let node = constructor_key("Node", vec![i64_key.clone()], e_key.clone());
        let local = variable(10, "local", i64_key.clone());
        let actions = GenericActions(vec![
            GenericAction::Let(Span::Panic, local.clone(), literal_i64(1)),
            GenericAction::Set(
                Span::Panic,
                CallKey::Function(score.clone()),
                vec![literal_i64(0)],
                var_expr(&local),
            ),
            GenericAction::Change(
                Span::Panic,
                Change::Delete,
                CallKey::Function(score.clone()),
                vec![literal_i64(0)],
            ),
            GenericAction::Change(
                Span::Panic,
                Change::Subsume,
                CallKey::Function(score),
                vec![literal_i64(0)],
            ),
            GenericAction::Union(
                Span::Panic,
                call(CallKey::Function(node.clone()), vec![literal_i64(0)]),
                call(CallKey::Function(node), vec![literal_i64(1)]),
            ),
            GenericAction::Panic(Span::Panic, "not executed".to_owned()),
            GenericAction::Expr(Span::Panic, var_expr(&local)),
        ]);
        let batch = GeneratedBatch {
            commands: vec![
                command(GeneratedCommandKind::Sort(GeneratedSortDecl {
                    span: Span::Panic,
                    key: e_key,
                    presort_and_args: None,
                    uf: None,
                    container_rebuild: None,
                    proof_constructors: None,
                    unionable: true,
                })),
                command(GeneratedCommandKind::Function(function_decl(
                    function_key(
                        "score",
                        vec![i64_key.clone()],
                        ValueShape::Scalar(i64_key.clone()),
                    ),
                    None,
                ))),
                command(GeneratedCommandKind::Function(function_decl(
                    constructor_key("Node", vec![i64_key], eq_sort("E")),
                    None,
                ))),
                command(GeneratedCommandKind::Actions(actions)),
            ],
        };
        let mut egraph = EGraph::default();
        let bound = bind_generated_batch(&mut egraph, batch).unwrap();
        let ResolvedNCommand::CoreActions(actions) = &bound.commands[3].command else {
            panic!("expected action block")
        };
        assert_eq!(actions.0.len(), 7);
        assert!(matches!(actions.0[0], GenericAction::Let(..)));
        assert!(matches!(actions.0[1], GenericAction::Set(..)));
        assert!(matches!(
            actions.0[2],
            GenericAction::Change(_, Change::Delete, ..)
        ));
        assert!(matches!(
            actions.0[3],
            GenericAction::Change(_, Change::Subsume, ..)
        ));
        assert!(matches!(actions.0[4], GenericAction::Union(..)));
        assert!(matches!(actions.0[5], GenericAction::Panic(..)));
        assert!(matches!(actions.0[6], GenericAction::Expr(..)));
    }

    fn unary_rule(
        name: &str,
        body_call: CallKey,
        head_call: CallKey,
        eval_mode: RuleEvalMode,
    ) -> GeneratedRule {
        let x = variable(20, "x", value_sort("i64"));
        GenericRule {
            span: Span::Panic,
            head: GenericActions(vec![GenericAction::Expr(
                Span::Panic,
                call(head_call, vec![var_expr(&x)]),
            )]),
            body: vec![GenericFact::Eq(
                Span::Panic,
                call(body_call, vec![var_expr(&x)]),
                var_expr(&x),
            )],
            name: name.to_owned(),
            ruleset: String::new(),
            eval_mode,
            no_decomp: false,
            include_subsumed: false,
        }
    }

    fn context_egraph(seminaive: bool) -> EGraph {
        let mut egraph = EGraph {
            seminaive,
            ..EGraph::default()
        };
        egraph.add_pure_primitive(DuplicateUnary("pure-echo"), None);
        egraph.add_read_primitive(ReadEcho("read-echo"), None);
        egraph.add_write_primitive(WriteEcho("write-echo"), None);
        egraph
    }

    fn unary_key(name: &str) -> CallKey {
        let i64_key = value_sort("i64");
        primitive_key(name, vec![i64_key.clone()], i64_key)
    }

    #[test]
    fn rule_contexts_are_structural_and_wrong_context_canaries_fail() {
        let mut seminaive = context_egraph(true);
        let batch = GeneratedBatch {
            commands: vec![command(GeneratedCommandKind::Rule(unary_rule(
                "seminaive",
                unary_key("pure-echo"),
                unary_key("write-echo"),
                RuleEvalMode::Seminaive,
            )))],
        };
        let bound = bind_generated_batch(&mut seminaive, batch).unwrap();
        assert_eq!(
            bound.stats.resolver_invocations_by_context[Context::Pure],
            1
        );
        assert_eq!(
            bound.stats.resolver_invocations_by_context[Context::Write],
            1
        );
        assert_eq!(bound.stats.resolver_invocations, 2);

        for (mode, global_seminaive) in [
            (RuleEvalMode::Naive, true),
            (RuleEvalMode::UnsafeSeminaive, true),
            (RuleEvalMode::Seminaive, false),
        ] {
            let mut egraph = context_egraph(global_seminaive);
            let batch = GeneratedBatch {
                commands: vec![command(GeneratedCommandKind::Rule(unary_rule(
                    "read-full",
                    unary_key("read-echo"),
                    unary_key("write-echo"),
                    mode,
                )))],
            };
            let bound = bind_generated_batch(&mut egraph, batch).unwrap();
            assert_eq!(
                bound.stats.resolver_invocations_by_context[Context::Read],
                1,
                "body context for {mode:?}, global seminaive={global_seminaive}"
            );
            assert_eq!(
                bound.stats.resolver_invocations_by_context[Context::Full],
                1,
                "head context for {mode:?}, global seminaive={global_seminaive}"
            );
        }

        let mut wrong_body = context_egraph(true);
        let error = bind_generated_batch(
            &mut wrong_body,
            GeneratedBatch {
                commands: vec![command(GeneratedCommandKind::Rule(unary_rule(
                    "wrong-body",
                    unary_key("read-echo"),
                    unary_key("write-echo"),
                    RuleEvalMode::Seminaive,
                )))],
            },
        )
        .unwrap_err();
        assert!(matches!(
            error,
            GeneratedBindError::Type(TypeError::UnresolvedPrimitive {
                name,
                ctx: Context::Pure,
                ..
            }) if name == "read-echo"
        ));

        let mut wrong_head = context_egraph(true);
        let error = bind_generated_batch(
            &mut wrong_head,
            GeneratedBatch {
                commands: vec![command(GeneratedCommandKind::Rule(unary_rule(
                    "wrong-head",
                    unary_key("pure-echo"),
                    unary_key("read-echo"),
                    RuleEvalMode::Seminaive,
                )))],
            },
        )
        .unwrap_err();
        assert!(matches!(
            error,
            GeneratedBindError::Type(TypeError::UnresolvedPrimitive {
                name,
                ctx: Context::Write,
                ..
            }) if name == "read-echo"
        ));
    }

    #[test]
    fn cache_keys_include_context_and_head_generation_without_global_thrashing() {
        let key = unary_key("overloaded");
        let unaffected = unary_key("pure-echo");
        let mut egraph = EGraph::default();
        egraph.add_pure_primitive(DuplicateUnary("overloaded"), None);
        egraph.add_pure_primitive(DuplicateUnary("pure-echo"), None);
        let mut state = BindingState::default();

        state
            .resolve_call(egraph.type_info(), &key, Context::Pure, &Span::Panic)
            .unwrap();
        state
            .resolve_call(egraph.type_info(), &key, Context::Pure, &Span::Panic)
            .unwrap();
        let pure = state
            .resolve_call(egraph.type_info(), &unaffected, Context::Pure, &Span::Panic)
            .unwrap();
        let write = state
            .resolve_call(
                egraph.type_info(),
                &unaffected,
                Context::Write,
                &Span::Panic,
            )
            .unwrap();
        assert!(matches!(pure, ResolvedCall::Primitive(_)));
        assert!(matches!(write, ResolvedCall::Primitive(_)));
        egraph.add_pure_primitive(DuplicateUnary("overloaded"), None);
        let error = state
            .resolve_call(egraph.type_info(), &key, Context::Pure, &Span::Panic)
            .unwrap_err();
        assert!(matches!(
            error,
            GeneratedBindError::Type(TypeError::AmbiguousPrimitive { name, .. })
                if name == "overloaded"
        ));
        state
            .resolve_call(egraph.type_info(), &unaffected, Context::Pure, &Span::Panic)
            .unwrap();
        let stats = state.finish();
        assert_eq!(stats.unique_resolution_keys, 4);
        assert_eq!(stats.call_cache_misses, 4);
        assert_eq!(stats.call_cache_hits, 2);
        assert_eq!(stats.resolver_invocations, 4);
    }

    #[test]
    fn exact_resolution_cache_persists_across_batches_with_name_local_invalidation() {
        let key = unary_key("persisted-echo");
        let batch = || GeneratedBatch {
            commands: vec![command(GeneratedCommandKind::Action(GenericAction::Expr(
                Span::Panic,
                call(key.clone(), vec![literal_i64(1)]),
            )))],
        };
        let mut egraph = EGraph::default();
        egraph.add_pure_primitive(DuplicateUnary("persisted-echo"), None);

        let first = bind_generated_batch(&mut egraph, batch()).unwrap();
        assert_eq!(first.stats.resolver_invocations, 1);
        drop(first);
        let second = bind_generated_batch(&mut egraph, batch()).unwrap();
        assert_eq!(second.stats.resolver_invocations, 0);
        assert_eq!(second.stats.call_cache_hits, 1);
        drop(second);

        egraph.add_pure_primitive(DuplicateUnary("unrelated-echo"), None);
        let unrelated_registration = bind_generated_batch(&mut egraph, batch()).unwrap();
        assert_eq!(unrelated_registration.stats.resolver_invocations, 0);
        drop(unrelated_registration);

        egraph.add_pure_primitive(DuplicateUnary("persisted-echo"), None);
        let error = bind_generated_batch(&mut egraph, batch()).unwrap_err();
        assert!(matches!(
            error,
            GeneratedBindError::Type(TypeError::AmbiguousPrimitive { name, .. })
                if name == "persisted-echo"
        ));
    }

    #[test]
    fn function_and_index_registration_receipts_are_exact_lazy_and_name_local() {
        let i64_key = value_sort("i64");
        let table = function_key(
            "receipt-table",
            vec![i64_key.clone()],
            ValueShape::Scalar(i64_key.clone()),
        );
        let index = function_key(
            "receipt-index",
            vec![i64_key.clone(), i64_key.clone(), i64_key.clone()],
            ValueShape::Scalar(value_sort("Unit")),
        );
        let index_fact = || {
            GenericFact::Fact(call(
                CallKey::Function(index.clone()),
                vec![literal_i64(1), literal_i64(1), literal_i64(1)],
            ))
        };
        let mut egraph = EGraph::default();
        let first = bind_generated_batch(
            &mut egraph,
            GeneratedBatch {
                commands: vec![
                    command(GeneratedCommandKind::Function(function_decl(
                        table.clone(),
                        None,
                    ))),
                    command(GeneratedCommandKind::Index(GeneratedIndexDecl {
                        span: Span::Panic,
                        name: index.name.clone(),
                        function: table.clone(),
                        any_of: vec![0],
                    })),
                    command(GeneratedCommandKind::Check(
                        Span::Panic,
                        vec![index_fact(), index_fact()],
                    )),
                ],
            },
        )
        .unwrap();
        assert_eq!(first.stats.registration_receipt_hits, 2);
        assert_eq!(first.stats.resolver_invocations, 0);
        assert_eq!(first.stats.call_cache_hits, 1);
        drop(first);

        egraph.add_pure_primitive(DuplicateUnary("unrelated-receipt-head"), None);
        let unrelated_registration = bind_generated_batch(
            &mut egraph,
            GeneratedBatch {
                commands: vec![command(GeneratedCommandKind::Action(GenericAction::Expr(
                    Span::Panic,
                    call(CallKey::Function(table.clone()), vec![literal_i64(1)]),
                )))],
            },
        )
        .unwrap();
        assert_eq!(unrelated_registration.stats.registration_receipt_hits, 1);
        assert_eq!(unrelated_registration.stats.resolver_invocations, 0);
        drop(unrelated_registration);

        egraph.add_pure_primitive(DuplicateUnary("receipt-table"), None);
        let same_name_registration = bind_generated_batch(
            &mut egraph,
            GeneratedBatch {
                commands: vec![command(GeneratedCommandKind::Action(GenericAction::Expr(
                    Span::Panic,
                    call(CallKey::Function(table), vec![literal_i64(1)]),
                )))],
            },
        )
        .unwrap();
        assert_eq!(same_name_registration.stats.registration_receipt_hits, 0);
        assert_eq!(same_name_registration.stats.resolver_invocations, 1);
    }

    #[test]
    fn fail_binding_is_prefix_committing_and_prebinds_every_child() {
        let i64_key = value_sort("i64");
        let prefix = function_key(
            "prefix-committed",
            vec![i64_key.clone()],
            ValueShape::Scalar(i64_key.clone()),
        );
        let illegal = variable(99, "illegal", i64_key.clone());
        let mut egraph = EGraph::default();
        let error = bind_generated_batch(
            &mut egraph,
            GeneratedBatch {
                commands: vec![command(GeneratedCommandKind::Fail(
                    Span::Panic,
                    vec![
                        command(GeneratedCommandKind::Function(function_decl(prefix, None))),
                        command(GeneratedCommandKind::Action(GenericAction::Let(
                            Span::Panic,
                            illegal,
                            literal_i64(1),
                        ))),
                    ],
                ))],
            },
        )
        .unwrap_err();
        assert!(matches!(error, GeneratedBindError::TopLevelLet { .. }));
        assert!(
            egraph
                .type_info()
                .get_func_type("prefix-committed")
                .is_some()
        );

        let late = function_key(
            "prebound-after-runtime-failure",
            vec![i64_key.clone()],
            ValueShape::Scalar(i64_key),
        );
        let bound = bind_generated_batch(
            &mut egraph,
            GeneratedBatch {
                commands: vec![command(GeneratedCommandKind::Fail(
                    Span::Panic,
                    vec![
                        command(GeneratedCommandKind::Action(GenericAction::Panic(
                            Span::Panic,
                            "runtime stop".to_owned(),
                        ))),
                        command(GeneratedCommandKind::Function(function_decl(late, None))),
                    ],
                ))],
            },
        )
        .unwrap();
        assert!(
            bound
                .egraph
                .type_info()
                .get_func_type("prebound-after-runtime-failure")
                .is_some()
        );
        assert_eq!(bound.stats.commands_bound, 3);
        drop(bound);

        let execution = bind_generated_batch(
            &mut egraph,
            GeneratedBatch {
                commands: vec![
                    command(GeneratedCommandKind::Fail(
                        Span::Panic,
                        vec![command(GeneratedCommandKind::Action(GenericAction::Panic(
                            Span::Panic,
                            "expected".to_owned(),
                        )))],
                    )),
                    command(GeneratedCommandKind::Push(1)),
                    command(GeneratedCommandKind::Pop(Span::Panic, 1)),
                ],
            },
        )
        .unwrap()
        .execute()
        .unwrap();
        assert!(execution.outputs.is_empty());
        assert_eq!(execution.origins.len(), 4);
        assert_eq!(execution.stats.commands_bound, 4);
    }

    #[test]
    fn complete_command_envelope_binds_and_preserves_name_only_targets_and_origins() {
        let i64_key = value_sort("i64");
        let table = function_key(
            "envelope-table",
            vec![i64_key.clone()],
            ValueShape::Scalar(i64_key.clone()),
        );
        let mut commands = vec![
            command(GeneratedCommandKind::Sort(GeneratedSortDecl {
                span: Span::Panic,
                key: eq_sort("EnvelopeE"),
                presort_and_args: None,
                uf: None,
                container_rebuild: None,
                proof_constructors: None,
                unionable: true,
            })),
            command(GeneratedCommandKind::Function(function_decl(
                table.clone(),
                None,
            ))),
            command(GeneratedCommandKind::Index(GeneratedIndexDecl {
                span: Span::Panic,
                name: "envelope-index".to_owned(),
                function: table.clone(),
                any_of: vec![0],
            })),
            command(GeneratedCommandKind::AddRuleset(
                Span::Panic,
                "rules".to_owned(),
            )),
            command(GeneratedCommandKind::CombinedRuleset(
                Span::Panic,
                "combined".to_owned(),
                vec!["rules".to_owned()],
            )),
            command(GeneratedCommandKind::Rule(GenericRule {
                span: Span::Panic,
                head: GenericActions(vec![]),
                body: vec![],
                name: "empty-rule".to_owned(),
                ruleset: "rules".to_owned(),
                eval_mode: RuleEvalMode::Seminaive,
                no_decomp: true,
                include_subsumed: true,
            })),
            command(GeneratedCommandKind::Action(GenericAction::Expr(
                Span::Panic,
                literal_i64(0),
            ))),
            command(GeneratedCommandKind::Actions(GenericActions(vec![
                GenericAction::Panic(Span::Panic, "not run".to_owned()),
            ]))),
            command(GeneratedCommandKind::Extract(
                Span::Panic,
                literal_i64(0),
                literal_i64(1),
            )),
            command(GeneratedCommandKind::Schedule(GenericSchedule::Run(
                Span::Panic,
                GenericRunConfig {
                    ruleset: "rules".to_owned(),
                    until: Some(vec![]),
                },
            ))),
            command(GeneratedCommandKind::PrintOverallStatistics(
                Span::Panic,
                None,
            )),
            command(GeneratedCommandKind::Check(Span::Panic, vec![])),
            command(GeneratedCommandKind::PrintFunction(
                Span::Panic,
                "envelope-table".to_owned(),
                Some(1),
                None,
                PrintFunctionMode::Default,
            )),
            command(GeneratedCommandKind::ProveExists(Span::Panic, table)),
            command(GeneratedCommandKind::PrintSize(
                Span::Panic,
                Some("envelope-table".to_owned()),
            )),
            command(GeneratedCommandKind::Output {
                span: Span::Panic,
                file: "unused.out".to_owned(),
                exprs: vec![literal_i64(0)],
            }),
            command(GeneratedCommandKind::Push(1)),
            command(GeneratedCommandKind::Pop(Span::Panic, 1)),
            command(GeneratedCommandKind::Fail(
                Span::Panic,
                vec![command(GeneratedCommandKind::Action(GenericAction::Panic(
                    Span::Panic,
                    "nested".to_owned(),
                )))],
            )),
            command(GeneratedCommandKind::Input {
                span: Span::Panic,
                name: "envelope-table".to_owned(),
                file: "unused.csv".to_owned(),
            }),
        ];
        commands[0].origin = origin(GeneratedFamily::DeclarationsIndexes, GeneratedRole::Header);
        commands[1].origin = origin(
            GeneratedFamily::DeclarationsIndexes,
            GeneratedRole::PendingDeclaration,
        );
        commands[5].origin = origin(
            GeneratedFamily::RulesRebuildSubsumption,
            GeneratedRole::Maintenance,
        );
        commands[8].origin = origin(
            GeneratedFamily::ActionsGlobalsExtraction,
            GeneratedRole::ExtractionSetup,
        );
        commands[12].origin = origin(
            GeneratedFamily::MiscChecksSchedulesWrappers,
            GeneratedRole::SourceDerived,
        );

        let mut egraph = EGraph::default();
        let bound = bind_generated_batch(&mut egraph, GeneratedBatch { commands }).unwrap();
        assert_eq!(bound.commands.len(), 20);
        assert_eq!(bound.stats.commands_bound, 21);
        assert_eq!(bound.stats.declarations_registered, 3);
        assert_eq!(
            bound.commands[0].origins[0],
            origin(GeneratedFamily::DeclarationsIndexes, GeneratedRole::Header)
        );
        assert!(matches!(
            bound.commands[3].command,
            ResolvedNCommand::AddRuleset(_, ref name) if name == "rules"
        ));
        assert!(matches!(
            bound.commands[4].command,
            ResolvedNCommand::UnstableCombinedRuleset(_, ref name, ref members)
                if name == "combined" && members == &["rules"]
        ));
        assert!(matches!(
            bound.commands[12].command,
            ResolvedNCommand::PrintFunction(_, ref name, ..) if name == "envelope-table"
        ));
        assert!(matches!(
            bound.commands[19].command,
            ResolvedNCommand::Input { ref name, .. } if name == "envelope-table"
        ));
        assert_eq!(bound.commands[18].origins.len(), 2);

        let resolved = bound
            .commands
            .iter()
            .map(|command| command.command.clone())
            .collect::<Vec<_>>();
        let origins = bound
            .commands
            .iter()
            .map(|command| command.origins[0])
            .collect::<Vec<_>>();
        let portable = {
            let type_info = bound.egraph.type_info();
            resolved
                .iter()
                .cloned()
                .zip(origins)
                .map(|(command, origin)| {
                    ResolvedPortableizer {
                        type_info,
                        next_local_id: 0,
                    }
                    .command(command, origin)
                })
                .collect::<Result<Vec<_>, _>>()
                .unwrap()
        };
        drop(bound);

        let mut rebound_egraph = EGraph::default();
        let rebound =
            bind_generated_batch(&mut rebound_egraph, GeneratedBatch { commands: portable })
                .unwrap();
        assert_eq!(
            resolved,
            rebound
                .commands
                .iter()
                .map(|command| command.command.clone())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn shadow_probe_round_trips_real_frontend_shapes_in_all_call_contexts_and_fail() {
        let mut egraph = EGraph::default();
        let parsed = egraph
            .parse_program(
                None,
                r#"
                    (sort ShadowE)
                    (constructor ShadowNode (i64) ShadowE)
                    (function shadow-score (i64) i64 :merge old)
                    (relation shadow-input (i64))
                    (ruleset shadow-rules)
                    (set (shadow-score 1) 2)
                    (shadow-input 1)
                    (rule ((shadow-input x) (= (+ x 0) 1))
                          ((set (shadow-score x) (+ x 1)))
                          :ruleset shadow-rules
                          :name "shadow-contexts")
                    (check (= (shadow-score 1) 2))
                    (fail (check (= (shadow-score 1) 3)))
                "#,
            )
            .unwrap();
        let families = [
            GeneratedFamily::DeclarationsIndexes,
            GeneratedFamily::ActionsGlobalsExtraction,
            GeneratedFamily::RulesRebuildSubsumption,
            GeneratedFamily::MiscChecksSchedulesWrappers,
        ];
        let generated = parsed
            .into_iter()
            .enumerate()
            .map(|(index, command)| TaggedGeneratedCommand {
                origin: GeneratedCommandOrigin::Family(families[index % families.len()]),
                command,
            })
            .collect();
        let resolved = resolve_with_shadow_probe(&mut egraph, generated).unwrap();
        for command in resolved {
            egraph.run_command(command).unwrap();
        }

        let summary = SHADOW_PROBE_SUMMARY.get().unwrap().lock().unwrap();
        let batch = summary.batches.last().unwrap();
        assert_eq!(batch.command_kinds.get("fail"), Some(&1));
        for context in [Context::Pure, Context::Write, Context::Read, Context::Full] {
            assert!(
                batch.bind_stats.resolver_invocations_by_context[context]
                    + batch.bind_stats.registration_receipt_hits_by_context[context]
                    > 0
            );
        }
    }

    fn portable_universe_batch() -> GeneratedBatch {
        let i64_key = value_sort("i64");
        let local_e = eq_sort("PortableE");
        let local_vec = SortKey {
            name: "PortableVec".to_owned(),
            class: SortSemanticClass::EqContainer,
        };
        let marker = function_key(
            "portable-marker",
            vec![local_vec.clone()],
            ValueShape::Scalar(local_vec.clone()),
        );
        let score = function_key(
            "portable-score",
            vec![i64_key.clone()],
            ValueShape::Scalar(i64_key.clone()),
        );
        GeneratedBatch {
            commands: vec![
                command(GeneratedCommandKind::Sort(GeneratedSortDecl {
                    span: Span::Panic,
                    key: local_e,
                    presort_and_args: None,
                    uf: None,
                    container_rebuild: None,
                    proof_constructors: None,
                    unionable: true,
                })),
                command(GeneratedCommandKind::Sort(GeneratedSortDecl {
                    span: Span::Panic,
                    key: local_vec,
                    presort_and_args: Some((
                        "Vec".to_owned(),
                        vec![GenericExpr::Var(Span::Panic, "PortableE".to_owned())],
                    )),
                    uf: None,
                    container_rebuild: None,
                    proof_constructors: None,
                    unionable: true,
                })),
                command(GeneratedCommandKind::Function(function_decl(marker, None))),
                command(GeneratedCommandKind::Function(function_decl(
                    score.clone(),
                    None,
                ))),
                command(GeneratedCommandKind::Action(GenericAction::Set(
                    Span::Panic,
                    CallKey::Function(score),
                    vec![literal_i64(0)],
                    call(unary_key("pure-echo"), vec![literal_i64(1)]),
                ))),
                command(GeneratedCommandKind::Rule(unary_rule(
                    "portable-rule",
                    unary_key("pure-echo"),
                    unary_key("write-echo"),
                    RuleEvalMode::Seminaive,
                ))),
                command(GeneratedCommandKind::Check(
                    Span::Panic,
                    vec![GenericFact::Eq(
                        Span::Panic,
                        call(unary_key("read-echo"), vec![literal_i64(1)]),
                        literal_i64(1),
                    )],
                )),
            ],
        }
    }

    fn seed_portable_primitives(egraph: &mut EGraph) {
        egraph.add_pure_primitive(DuplicateUnary("pure-echo"), None);
        egraph.add_read_primitive(ReadEcho("read-echo"), None);
        egraph.add_write_primitive(WriteEcho("write-echo"), None);
    }

    fn universe_projection(
        egraph: &mut EGraph,
        batch: GeneratedBatch,
    ) -> (Vec<String>, ArcSort, ArcSort, ArcSort) {
        let bound = bind_generated_batch(egraph, batch).unwrap();
        let projection = stable_projection(&bound);
        let ResolvedNCommand::Function(marker) = &bound.commands[2].command else {
            panic!("expected marker function")
        };
        let ResolvedCall::Func(marker_type) = &marker.resolved_schema else {
            panic!("expected resolved marker schema")
        };
        let marker_sort = marker_type.input[0].clone();
        let ResolvedNCommand::CoreAction(GenericAction::Set(_, _, _, value)) =
            &bound.commands[4].command
        else {
            panic!("expected set action")
        };
        let GenericExpr::Call(_, ResolvedCall::Primitive(primitive), _) = value else {
            panic!("expected rebound primitive")
        };
        let primitive_sort = primitive.output().clone();
        let ResolvedNCommand::NormRule { rule } = &bound.commands[5].command else {
            panic!("expected rule")
        };
        let GenericFact::Eq(_, GenericExpr::Call(_, _, args), _) = &rule.body[0] else {
            panic!("expected rule body call")
        };
        let GenericExpr::Var(_, variable) = &args[0] else {
            panic!("expected local variable")
        };
        (
            projection,
            marker_sort,
            primitive_sort,
            variable.sort.clone(),
        )
    }

    #[test]
    fn portable_batch_rebinds_all_handles_and_uses_real_proof_mode_checker_chain() {
        let batch = portable_universe_batch();
        let mut left = EGraph::default();
        let mut right = EGraph::default();
        seed_portable_primitives(&mut left);
        seed_portable_primitives(&mut right);
        let (left_projection, left_marker, left_primitive, left_local) =
            universe_projection(&mut left, batch.clone());
        let (right_projection, right_marker, right_primitive, right_local) =
            universe_projection(&mut right, batch.clone());
        assert_eq!(left_projection, right_projection);
        assert!(!Arc::ptr_eq(&left_marker, &right_marker));
        assert!(!Arc::ptr_eq(&left_primitive, &right_primitive));
        assert!(!Arc::ptr_eq(&left_local, &right_local));

        let mut proof_outer = EGraph::new_with_term_encoding();
        seed_portable_primitives(&mut proof_outer);
        assert!(proof_outer.type_info().get_prims("read-echo").is_some());
        assert!(
            proof_outer
                .proof_state
                .original_typechecking
                .as_mut()
                .unwrap()
                .type_info()
                .get_prims("read-echo")
                .is_some(),
            "post-construction primitive registration must propagate to the proof checker"
        );
        let mut proof_checker = *proof_outer
            .proof_state
            .original_typechecking
            .take()
            .unwrap();
        let (checker_projection, ..) = universe_projection(&mut proof_checker, batch.clone());
        let (outer_projection, ..) = universe_projection(&mut proof_outer, batch);
        assert_eq!(checker_projection, outer_projection);
    }
}
