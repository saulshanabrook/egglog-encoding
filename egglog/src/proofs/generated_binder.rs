//! Portable typed-command foundation for generated proof instrumentation.
//!
//! This module deliberately remains private and is not wired to the generated
//! driver yet. It defines the complete normalized command envelope, verifies
//! emitter-owned invariants, and binds portable keys exactly once against the
//! outer execution e-graph before a one-shot batch can execute.

#![allow(dead_code)]

use std::fmt::{Display, Formatter};

use enum_map::EnumMap;
use thiserror::Error;

use super::proof_encoding::GeneratedFamily;
use crate::ast::{
    ContainerRebuildSpec, Expr, FunctionDecl, FunctionSubtype, GenericAction, GenericActions,
    GenericExpr, GenericFact, GenericFunctionDecl, GenericMerge, GenericRule, GenericSchedule,
    Literal, PrintFunctionMode, ProofConstructorNames, ResolvedAction, ResolvedActions,
    ResolvedExpr, ResolvedFact, ResolvedFunctionDecl, ResolvedNCommand, ResolvedRule,
    ResolvedRunConfig, ResolvedSchedule, RuleEvalMode, Schema, Span,
};
use crate::core::{ResolvedCall, resolve_call};
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
}

impl std::fmt::Debug for BoundBatch<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BoundBatch")
            .field("commands", &self.commands)
            .field("stats", &self.stats)
            .finish_non_exhaustive()
    }
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
    resolver_invocations_by_context: EnumMap<Context, usize>,
    declarations_registered: usize,
    commands_bound: usize,
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
    #[error("{span}\ngenerated fact must return scalar `Unit`, got {actual}")]
    FactOutput { actual: String, span: Span },
    #[error("{span}\nextract requires a scalar value, got {actual}")]
    CannotExtractTuple { actual: String, span: Span },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct CallCacheKey {
    call: CallKey,
    context: Context,
    head_generation: u64,
}

#[derive(Default)]
struct BindingState {
    sort_cache: HashMap<SortKey, ArcSort>,
    call_cache: HashMap<CallCacheKey, ResolvedCall>,
    seen_sort_keys: HashSet<SortKey>,
    seen_resolution_keys: HashSet<CallCacheKey>,
    stats: GeneratedBindStats,
}

impl BindingState {
    fn resolve_sort(
        &mut self,
        type_info: &TypeInfo,
        key: &SortKey,
        span: &Span,
    ) -> Result<ArcSort, GeneratedBindError> {
        self.seen_sort_keys.insert(key.clone());
        if let Some(sort) = self.sort_cache.get(key) {
            self.stats.sort_cache_hits += 1;
            return Ok(sort.clone());
        }
        self.stats.sort_cache_misses += 1;
        let sort = type_info
            .get_sort_by_name(&key.name)
            .cloned()
            .ok_or_else(|| TypeError::UndefinedSort(key.name.clone(), span.clone()))?;
        let actual = if sort.is_eq_container_sort() {
            SortSemanticClass::EqContainer
        } else if sort.is_eq_sort() {
            SortSemanticClass::Eq
        } else {
            SortSemanticClass::Value
        };
        if actual != key.class {
            return Err(GeneratedBindError::SortClassMismatch {
                name: key.name.clone(),
                expected: key.class,
                actual,
                span: span.clone(),
            });
        }
        self.sort_cache.insert(key.clone(), sort.clone());
        Ok(sort)
    }

    fn resolve_value_shape(
        &mut self,
        type_info: &TypeInfo,
        shape: &ValueShape,
        span: &Span,
    ) -> Result<BoundValueShape, GeneratedBindError> {
        match shape {
            ValueShape::Scalar(sort) => Ok(BoundValueShape::Scalar(
                self.resolve_sort(type_info, sort, span)?,
            )),
            ValueShape::Tuple(sorts) => {
                if sorts.len() < 2 {
                    return Err(GeneratedBindError::InvalidTupleArity {
                        actual: sorts.len(),
                        span: span.clone(),
                    });
                }
                Ok(BoundValueShape::Tuple(
                    sorts
                        .iter()
                        .map(|sort| self.resolve_sort(type_info, sort, span))
                        .collect::<Result<_, _>>()?,
                ))
            }
        }
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
        let cache_key = CallCacheKey {
            call: key.clone(),
            context,
            head_generation,
        };
        self.seen_resolution_keys.insert(cache_key.clone());
        if let Some(call) = self.call_cache.get(&cache_key) {
            self.stats.call_cache_hits += 1;
            return Ok(call.clone());
        }
        self.stats.call_cache_misses += 1;

        let resolved = match key {
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
                self.stats.resolver_invocations += 1;
                self.stats.resolver_invocations_by_context[context] += 1;
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
                self.stats.resolver_invocations += 1;
                self.stats.resolver_invocations_by_context[context] += 1;
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
        };
        self.call_cache.insert(cache_key, resolved.clone());
        Ok(resolved)
    }

    fn finish(mut self) -> GeneratedBindStats {
        self.stats.unique_sort_keys = self.seen_sort_keys.len();
        self.stats.unique_resolution_keys = self.seen_resolution_keys.len();
        self.stats
    }
}

#[derive(Clone)]
enum BoundValueShape {
    Scalar(ArcSort),
    Tuple(Vec<ArcSort>),
}

impl BoundValueShape {
    fn stable_name(&self) -> String {
        match self {
            Self::Scalar(sort) => sort.name().to_owned(),
            Self::Tuple(sorts) => format!(
                "({})",
                sorts
                    .iter()
                    .map(|sort| sort.name())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        }
    }

    fn same_sorts(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Scalar(left), Self::Scalar(right)) => left.name() == right.name(),
            (Self::Tuple(left), Self::Tuple(right)) => {
                left.len() == right.len()
                    && left.iter().zip(right).all(|(a, b)| a.name() == b.name())
            }
            _ => false,
        }
    }
}

struct BoundExpr {
    expr: ResolvedExpr,
    shape: BoundValueShape,
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

    fn literal_shape(literal: &Literal) -> ValueShape {
        let name = match literal {
            Literal::Int(_) => "i64",
            Literal::Float(_) => "f64",
            Literal::String(_) => "String",
            Literal::Bool(_) => "bool",
            Literal::Unit => "Unit",
        };
        ValueShape::Scalar(SortKey {
            name: name.to_owned(),
            class: SortSemanticClass::Value,
        })
    }

    fn verify_expr(
        expr: &GeneratedExpr,
        scope: &PortableScope,
    ) -> Result<ValueShape, GeneratedBindError> {
        match expr {
            GenericExpr::Var(span, variable) => {
                scope.require(variable, span)?;
                Ok(ValueShape::Scalar(variable.sort.clone()))
            }
            GenericExpr::Lit(_, literal) => Ok(Self::literal_shape(literal)),
            GenericExpr::Call(span, key, args) => {
                let (inputs, output) = match key {
                    CallKey::Function(function) => {
                        Self::verify_value_shape(&function.output, span)?;
                        (&function.inputs, function.output.clone())
                    }
                    CallKey::Primitive(primitive) => (
                        &primitive.inputs,
                        ValueShape::Scalar(primitive.output.clone()),
                    ),
                    CallKey::Values(sorts) => {
                        if sorts.len() < 2 {
                            return Err(GeneratedBindError::InvalidTupleArity {
                                actual: sorts.len(),
                                span: span.clone(),
                            });
                        }
                        (sorts, ValueShape::Tuple(sorts.clone()))
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
                    let expected = ValueShape::Scalar(expected.clone());
                    if actual != expected {
                        return Err(GeneratedBindError::ShapeMismatch {
                            expected: format!("{expected:?}"),
                            actual: format!("{actual:?}"),
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
                if left != right {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: format!("{left:?}"),
                        actual: format!("{right:?}"),
                        span: span.clone(),
                    });
                }
            }
            GenericFact::Fact(expr) => {
                let span = match expr {
                    GenericExpr::Var(span, _)
                    | GenericExpr::Call(span, _, _)
                    | GenericExpr::Lit(span, _) => span,
                };
                let actual = Self::verify_expr(expr, scope)?;
                let unit = ValueShape::Scalar(SortKey {
                    name: "Unit".to_owned(),
                    class: SortSemanticClass::Value,
                });
                if actual != unit {
                    return Err(GeneratedBindError::FactOutput {
                        actual: format!("{actual:?}"),
                        span: span.clone(),
                    });
                }
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
                let expected = ValueShape::Scalar(variable.sort.clone());
                if actual != expected {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: format!("{expected:?}"),
                        actual: format!("{actual:?}"),
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
                    let expected = ValueShape::Scalar(expected.clone());
                    if actual != expected {
                        return Err(GeneratedBindError::ShapeMismatch {
                            expected: format!("{expected:?}"),
                            actual: format!("{actual:?}"),
                            span: span.clone(),
                        });
                    }
                }
                let actual = Self::verify_expr(value, scope)?;
                if actual != function.output {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: format!("{:?}", function.output),
                        actual: format!("{actual:?}"),
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
                    let expected = ValueShape::Scalar(expected.clone());
                    if actual != expected {
                        return Err(GeneratedBindError::ShapeMismatch {
                            expected: format!("{expected:?}"),
                            actual: format!("{actual:?}"),
                            span: span.clone(),
                        });
                    }
                }
            }
            GenericAction::Union(span, left, right) => {
                let left = Self::verify_expr(left, scope)?;
                let right = Self::verify_expr(right, scope)?;
                if left != right {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: format!("{left:?}"),
                        actual: format!("{right:?}"),
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
                if matches!(shape, ValueShape::Tuple(_)) {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: "scalar action expression".to_owned(),
                        actual: format!("{shape:?}"),
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
        if &result != output {
            return Err(GeneratedBindError::ShapeMismatch {
                expected: format!("{output:?}"),
                actual: format!("{result:?}"),
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
                Self::verify_expr(expr, &PortableScope::default())?;
                Self::verify_expr(variants, &PortableScope::default())?;
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
                    if matches!(shape, ValueShape::Tuple(_)) {
                        return Err(GeneratedBindError::ShapeMismatch {
                            expected: "scalar output expression".to_owned(),
                            actual: format!("{shape:?}"),
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
            if resolved.name != variable.name {
                return Err(GeneratedBindError::InconsistentLocalId {
                    id: variable.id.0,
                    span: span.clone(),
                });
            }
            let expected = self
                .state
                .resolve_sort(self.type_info, &variable.sort, span)?;
            if resolved.sort.name() != expected.name() {
                return Err(GeneratedBindError::InconsistentLocalId {
                    id: variable.id.0,
                    span: span.clone(),
                });
            }
            return Ok(resolved.clone());
        }
        if let Some(global) = self.type_info.get_global_sort(&variable.name) {
            let expected = self
                .state
                .resolve_sort(self.type_info, &variable.sort, span)?;
            if global.name() != expected.name() {
                return Err(GeneratedBindError::ShapeMismatch {
                    expected: expected.name().to_owned(),
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
                let expected = self
                    .state
                    .resolve_sort(self.type_info, &variable.sort, span)?;
                if let Some(global) = self.type_info.get_global_sort(&variable.name) {
                    if global.name() != expected.name() {
                        return Err(GeneratedBindError::ShapeMismatch {
                            expected: expected.name().to_owned(),
                            actual: global.name().to_owned(),
                            span: span.clone(),
                        });
                    }
                    return Ok(());
                }
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
    ) -> Result<BoundExpr, GeneratedBindError> {
        match expr {
            GenericExpr::Var(span, variable) => {
                let resolved = self.bind_variable(&span, variable, scope)?;
                Ok(BoundExpr {
                    shape: BoundValueShape::Scalar(resolved.sort.clone()),
                    expr: GenericExpr::Var(span, resolved),
                })
            }
            GenericExpr::Lit(span, literal) => {
                let ValueShape::Scalar(key) = LinearVerifier::literal_shape(&literal) else {
                    unreachable!("literal shapes are scalar")
                };
                let sort = self.state.resolve_sort(self.type_info, &key, &span)?;
                Ok(BoundExpr {
                    expr: GenericExpr::Lit(span, literal),
                    shape: BoundValueShape::Scalar(sort),
                })
            }
            GenericExpr::Call(span, key, args) => {
                let (call, args, shape) =
                    self.bind_call_application(&span, &key, args, scope, context)?;
                Ok(BoundExpr {
                    expr: GenericExpr::Call(span, call, args),
                    shape,
                })
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
    ) -> Result<(ResolvedCall, Vec<ResolvedExpr>, BoundValueShape), GeneratedBindError> {
        let (inputs, output) = match key {
            CallKey::Function(function) => (&function.inputs, function.output.clone()),
            CallKey::Primitive(primitive) => (
                &primitive.inputs,
                ValueShape::Scalar(primitive.output.clone()),
            ),
            CallKey::Values(sorts) => (sorts, ValueShape::Tuple(sorts.clone())),
        };
        if args.len() != inputs.len() {
            return Err(GeneratedBindError::CallArity {
                expected: inputs.len(),
                actual: args.len(),
                span: span.clone(),
            });
        }
        let mut resolved_args = Vec::with_capacity(args.len());
        for (arg, expected) in args.into_iter().zip(inputs) {
            let arg = self.bind_expr(arg, scope, context)?;
            let expected =
                BoundValueShape::Scalar(self.state.resolve_sort(self.type_info, expected, span)?);
            if !arg.shape.same_sorts(&expected) {
                return Err(GeneratedBindError::ShapeMismatch {
                    expected: expected.stable_name(),
                    actual: arg.shape.stable_name(),
                    span: span.clone(),
                });
            }
            resolved_args.push(arg.expr);
        }
        let call = self
            .state
            .resolve_call(self.type_info, key, context, span)?;
        let output = self
            .state
            .resolve_value_shape(self.type_info, &output, span)?;
        Ok((call, resolved_args, output))
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
                if !left.shape.same_sorts(&right.shape) {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: left.shape.stable_name(),
                        actual: right.shape.stable_name(),
                        span,
                    });
                }
                Ok(GenericFact::Eq(span, left.expr, right.expr))
            }
            GenericFact::Fact(expr) => {
                let span = match &expr {
                    GenericExpr::Var(span, _)
                    | GenericExpr::Call(span, _, _)
                    | GenericExpr::Lit(span, _) => span.clone(),
                };
                let expr = self.bind_expr(expr, scope, context)?;
                if !matches!(&expr.shape, BoundValueShape::Scalar(sort) if sort.name() == "Unit") {
                    return Err(GeneratedBindError::FactOutput {
                        actual: expr.shape.stable_name(),
                        span,
                    });
                }
                Ok(GenericFact::Fact(expr.expr))
            }
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
                let expected = BoundValueShape::Scalar(self.state.resolve_sort(
                    self.type_info,
                    &variable.sort,
                    &span,
                )?);
                if !expr.shape.same_sorts(&expected) {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: expected.stable_name(),
                        actual: expr.shape.stable_name(),
                        span,
                    });
                }
                let resolved = ResolvedVar {
                    name: variable.name.clone(),
                    sort: match expected {
                        BoundValueShape::Scalar(sort) => sort,
                        BoundValueShape::Tuple(_) => unreachable!(),
                    },
                    is_global_ref: false,
                };
                scope.declare(&variable, resolved.clone(), &span)?;
                Ok(GenericAction::Let(span, resolved, expr.expr))
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
                let (call, args, output) =
                    self.bind_call_application(&span, &head, args, scope, context)?;
                let value = self.bind_expr(value, scope, context)?;
                if !output.same_sorts(&value.shape) {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: output.stable_name(),
                        actual: value.shape.stable_name(),
                        span,
                    });
                }
                Ok(GenericAction::Set(span, call, args, value.expr))
            }
            GenericAction::Change(span, change, head, args) => {
                let (call, args, _) =
                    self.bind_call_application(&span, &head, args, scope, context)?;
                Ok(GenericAction::Change(span, change, call, args))
            }
            GenericAction::Union(span, left, right) => {
                let left = self.bind_expr(left, scope, context)?;
                let right = self.bind_expr(right, scope, context)?;
                if !left.shape.same_sorts(&right.shape) {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: left.shape.stable_name(),
                        actual: right.shape.stable_name(),
                        span,
                    });
                }
                let BoundValueShape::Scalar(sort) = &left.shape else {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: "scalar unionable eq sort".to_owned(),
                        actual: left.shape.stable_name(),
                        span,
                    });
                };
                if !self.type_info.is_sort_unionable(sort) {
                    return if sort.is_eq_sort() {
                        Err(TypeError::NonUnionableSort(sort.clone(), span).into())
                    } else {
                        Err(TypeError::NonEqsortUnion(sort.clone(), span).into())
                    };
                }
                Ok(GenericAction::Union(span, left.expr, right.expr))
            }
            GenericAction::Panic(span, message) => Ok(GenericAction::Panic(span, message)),
            GenericAction::Expr(span, expr) => {
                let expr = self.bind_expr(expr, scope, context)?;
                Ok(GenericAction::Expr(span, expr.expr))
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
        self.state.stats.declarations_registered += 1;
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
        for input in &key.inputs {
            self.state
                .resolve_sort(self.egraph.type_info(), input, &decl.span)?;
        }
        match &key.output {
            ValueShape::Scalar(sort) => {
                self.state
                    .resolve_sort(self.egraph.type_info(), sort, &decl.span)?;
            }
            ValueShape::Tuple(sorts) => {
                for sort in sorts {
                    self.state
                        .resolve_sort(self.egraph.type_info(), sort, &decl.span)?;
                }
            }
        }

        let source = Self::source_function_metadata(&decl);
        let ftype = self.egraph.type_info().prepare_function_type(&source)?;
        let generated_merge = decl.merge;
        let state = &mut self.state;
        let merge =
            self.egraph
                .type_info()
                .bind_with_provisional_function(ftype.clone(), |type_info| {
                    let Some(generated_merge) = generated_merge else {
                        return Ok(None);
                    };
                    let mut binder = ExpressionBinder { type_info, state };
                    let mut scope = binder.prepare_merge_scope(&generated_merge, &key.output)?;
                    let actions =
                        binder.bind_actions(generated_merge.actions, &mut scope, Context::Write)?;
                    let result =
                        binder.bind_expr(generated_merge.result, &scope, Context::Write)?;
                    let expected =
                        binder
                            .state
                            .resolve_value_shape(type_info, &key.output, &decl.span)?;
                    if !result.shape.same_sorts(&expected) {
                        return Err(GeneratedBindError::ShapeMismatch {
                            expected: expected.stable_name(),
                            actual: result.shape.stable_name(),
                            span: decl.span.clone(),
                        });
                    }
                    Ok(Some(crate::ast::ResolvedMerge {
                        actions,
                        result: result.expr,
                    }))
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
        self.egraph.register_resolved_function_metadata(&resolved);
        self.state.stats.declarations_registered += 1;
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
        self.state.stats.declarations_registered += 1;
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
        LinearVerifier::verify_command(&generated.kind)?;
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
                if matches!(expr.shape, BoundValueShape::Tuple(_)) {
                    return Err(GeneratedBindError::CannotExtractTuple {
                        actual: expr.shape.stable_name(),
                        span,
                    });
                }
                let variants = binder.bind_expr(variants, &LocalScope::default(), Context::Full)?;
                if !matches!(&variants.shape, BoundValueShape::Scalar(sort) if sort.name() == "i64")
                {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: "i64".to_owned(),
                        actual: variants.shape.stable_name(),
                        span,
                    });
                }
                ResolvedNCommand::Extract(span, expr.expr, variants.expr)
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
                    .map(|expr| {
                        binder
                            .bind_expr(expr, &LocalScope::default(), Context::Full)
                            .map(|expr| expr.expr)
                    })
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
        self.state.stats.commands_bound += 1;
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
    let mut binder = GeneratedBinder {
        egraph,
        state: BindingState::default(),
    };
    let mut commands = Vec::with_capacity(batch.commands.len());
    for command in batch.commands {
        commands.push(binder.bind_command(command)?);
    }
    let stats = binder.state.finish();
    Ok(BoundBatch {
        egraph: binder.egraph,
        commands,
        stats,
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
