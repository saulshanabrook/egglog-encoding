//! Typed-command foundation for generated proof instrumentation.
//!
//! Proof instrumentation constructs portable typed nodes and binds them once,
//! directly into the destination e-graph universe. Generated commands never
//! re-enter the source parser, desugarer, or general-purpose typechecker.

use std::fmt::{Display, Formatter};
use std::sync::Arc;

use enum_map::EnumMap;
use thiserror::Error;

use crate::ast::{
    ContainerRebuildSpec, Expr, FunctionDecl, FunctionSubtype, GenericAction, GenericActions,
    GenericExpr, GenericFact, GenericFunctionDecl, GenericMerge, GenericRule, GenericSchedule,
    Literal, PrintFunctionMode, ProofConstructorNames, ResolvedAction, ResolvedActions,
    ResolvedExpr, ResolvedFact, ResolvedFunctionDecl, ResolvedNCommand, ResolvedRule,
    ResolvedRunConfig, ResolvedSchedule, RuleEvalMode, Schema, Span,
};
use crate::core::ResolvedCall;
use crate::proofs::proof_encoding::declaration_direct::TypedDeclarationEntry;
use crate::typechecking::{SortDeclarationMetadata, TypeError, TypeInfo};
use crate::util::SymbolGen;
use crate::util::{FreshGen, HashMap, HashSet};
use crate::{ArcSort, Context, EGraph, Error as EgglogError, ResolvedExprExt, ResolvedVar};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum SortSemanticClass {
    Eq,
    EqContainer,
    Value,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct SortKey {
    pub(super) name: String,
    pub(super) class: SortSemanticClass,
}

impl SortKey {
    pub(super) fn from_sort(sort: &ArcSort) -> Self {
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
pub(super) enum ValueShape {
    Scalar(SortKey),
    Tuple(Vec<SortKey>),
}

impl ValueShape {
    fn stable_name(&self) -> String {
        match self {
            Self::Scalar(sort) => sort.name.clone(),
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
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct FunctionKey {
    pub(super) name: String,
    pub(super) subtype: FunctionSubtype,
    pub(super) inputs: Vec<SortKey>,
    pub(super) output: ValueShape,
}

fn function_key(ftype: &crate::typechecking::FuncType) -> FunctionKey {
    let output = if ftype.outputs.len() == 1 {
        ValueShape::Scalar(SortKey::from_sort(&ftype.outputs[0]))
    } else {
        ValueShape::Tuple(ftype.outputs.iter().map(SortKey::from_sort).collect())
    };
    FunctionKey {
        name: ftype.name.clone(),
        subtype: ftype.subtype,
        inputs: ftype.input.iter().map(SortKey::from_sort).collect(),
        output,
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct PrimitiveKey {
    pub(super) name: String,
    pub(super) inputs: Vec<SortKey>,
    pub(super) output: SortKey,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum CallKey {
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

impl CallKey {
    /// Convert a checker-universe call into its portable, exact-signature key.
    ///
    /// The returned key deliberately retains only stable names, semantic sort
    /// classes, function metadata, and concrete primitive specialization.  In
    /// particular it carries no `ArcSort`, `FuncType`, primitive registration,
    /// or external-function identifier from the source checker universe.
    pub(super) fn from_resolved(call: &ResolvedCall) -> Self {
        match call {
            ResolvedCall::Func(function) => Self::Function(function_key(function)),
            ResolvedCall::Primitive(primitive) => Self::Primitive(PrimitiveKey {
                name: primitive.name().to_owned(),
                inputs: primitive.input().iter().map(SortKey::from_sort).collect(),
                output: SortKey::from_sort(primitive.output()),
            }),
            ResolvedCall::Values(sorts) => {
                Self::Values(sorts.iter().map(SortKey::from_sort).collect())
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CallKind {
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
pub(super) struct LocalId(pub(super) u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum GeneratedVarRole {
    Local,
    Global,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct GeneratedVar {
    pub(super) id: LocalId,
    pub(super) name: String,
    pub(super) sort: SortKey,
    pub(super) role: GeneratedVarRole,
}

impl Display for GeneratedVar {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.name)
    }
}

pub(super) type GeneratedExpr = GenericExpr<CallKey, GeneratedVar>;
pub(super) type GeneratedFact = GenericFact<CallKey, GeneratedVar>;
pub(super) type GeneratedAction = GenericAction<CallKey, GeneratedVar>;
pub(super) type GeneratedActions = GenericActions<CallKey, GeneratedVar>;
pub(super) type GeneratedMerge = GenericMerge<CallKey, GeneratedVar>;
pub(super) type GeneratedRule = GenericRule<CallKey, GeneratedVar>;
pub(super) type GeneratedSchedule = GenericSchedule<CallKey, GeneratedVar>;
pub(super) type GeneratedFunctionDecl = GenericFunctionDecl<CallKey, GeneratedVar>;

/// One source-level top-level `let` captured before global removal. Extraction
/// staging binds these in order and lowers each to its hidden nullary function
/// plus `set`, without making that synthetic function part of the persistent
/// call catalog.
#[derive(Clone, Debug)]
pub(super) struct ExtractionScratch {
    pub(super) span: Span,
    pub(super) variable: GeneratedVar,
    pub(super) value: GeneratedExpr,
}

#[derive(Clone, Debug)]
pub(super) enum GeneratedExtractionStep {
    Scratch(ExtractionScratch),
    Action(GeneratedAction),
}

/// A portable presort application. Unlike the source [`Expr`] payload, every
/// referenced sort carries its semantic class and can therefore be checked
/// after the ordinary presort constructor has established the source error
/// boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct GeneratedPresort {
    pub(super) name: String,
    pub(super) args: Vec<GeneratedPresortArg>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum GeneratedPresortArg {
    Sort(SortKey),
    SortList(Vec<SortKey>),
}

impl GeneratedPresort {
    fn source_payload(&self, span: &Span) -> (String, Vec<Expr>) {
        let args = self
            .args
            .iter()
            .map(|arg| match arg {
                GeneratedPresortArg::Sort(sort) => {
                    GenericExpr::Var(span.clone(), sort.name.clone())
                }
                GeneratedPresortArg::SortList(sorts) if sorts.is_empty() => {
                    GenericExpr::Lit(span.clone(), Literal::Unit)
                }
                GeneratedPresortArg::SortList(sorts) => {
                    let mut sorts = sorts.iter();
                    let first = sorts
                        .next()
                        .expect("nonempty portable presort sort list")
                        .name
                        .clone();
                    GenericExpr::Call(
                        span.clone(),
                        first,
                        sorts
                            .map(|sort| GenericExpr::Var(span.clone(), sort.name.clone()))
                            .collect(),
                    )
                }
            })
            .collect();
        (self.name.clone(), args)
    }
}

#[derive(Clone, Debug)]
pub(super) struct GeneratedSortDecl {
    pub(super) span: Span,
    pub(super) key: SortKey,
    pub(super) presort: Option<GeneratedPresort>,
    pub(super) uf: Option<(String, Option<String>)>,
    pub(super) container_rebuild: Option<ContainerRebuildSpec>,
    pub(super) proof_constructors: Option<ProofConstructorNames>,
    pub(super) unionable: bool,
}

#[derive(Clone, Debug)]
pub(super) struct GeneratedIndexDecl {
    pub(super) span: Span,
    pub(super) name: String,
    pub(super) function: FunctionKey,
    pub(super) any_of: Vec<usize>,
}

#[derive(Clone, Debug)]
pub(super) enum GeneratedCommand {
    Sort(GeneratedSortDecl),
    Function(GeneratedFunctionDecl),
    Index(GeneratedIndexDecl),
    AddRuleset(Span, String),
    CombinedRuleset(Span, String, Vec<String>),
    Rule(GeneratedRule),
    Actions(GeneratedActions),
    Extraction {
        span: Span,
        setup: Vec<GeneratedExtractionStep>,
        rebuild: GeneratedSchedule,
        expr: GeneratedExpr,
        variants: GeneratedExpr,
    },
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
    Push(Span, usize),
    Pop(Span, usize),
    Input {
        span: Span,
        name: String,
        file: String,
    },
}

#[derive(Clone, Debug)]
pub(super) enum GeneratedEntry {
    Command(Box<GeneratedCommand>),
    Declaration(Box<TypedDeclarationEntry>),
    Rule(GeneratedRule),
    Fail(Span, Vec<GeneratedEntry>),
}

#[derive(Clone, Debug)]
pub(crate) struct GeneratedBatch {
    pub(super) entries: Vec<GeneratedEntry>,
}

/// Portable signatures known while generated commands are being constructed.
/// The catalog deliberately contains no handles from either checker universe.
#[derive(Clone, Debug, Default)]
pub(super) struct GeneratedSignatureCatalog {
    sorts: HashMap<String, SortKey>,
    functions: HashMap<String, FunctionKey>,
    indexes: HashSet<String>,
    primitives: HashSet<PrimitiveKey>,
}

impl GeneratedSignatureCatalog {
    /// Register one already-portable call and every sort its exact signature
    /// mentions.  This is the construction-time counterpart of the binder's
    /// single shared resolver: producers never need to repeat sort-registration
    /// order or inspect checker-universe handles.
    pub(super) fn register_call_key(
        &mut self,
        key: &CallKey,
        span: &Span,
    ) -> Result<(), GeneratedBindError> {
        let mut register_sort = |sort: &SortKey| self.register_sort(sort.clone(), span).map(|_| ());
        match key {
            CallKey::Function(function) => {
                for sort in &function.inputs {
                    register_sort(sort)?;
                }
                match &function.output {
                    ValueShape::Scalar(sort) => register_sort(sort)?,
                    ValueShape::Tuple(sorts) => {
                        for sort in sorts {
                            register_sort(sort)?;
                        }
                    }
                }
                self.register_function(function.clone(), span)?;
            }
            CallKey::Primitive(primitive) => {
                for sort in &primitive.inputs {
                    register_sort(sort)?;
                }
                register_sort(&primitive.output)?;
                self.register_primitive(primitive.clone(), span)?;
            }
            CallKey::Values(sorts) => {
                for sort in sorts {
                    register_sort(sort)?;
                }
                self.values_call(sorts.clone(), span)?;
            }
        }
        Ok(())
    }

    pub(super) fn register_sort(
        &mut self,
        key: SortKey,
        span: &Span,
    ) -> Result<SortKey, GeneratedBindError> {
        if let Some(existing) = self.sorts.get(&key.name) {
            if existing == &key {
                return Ok(existing.clone());
            }
            return Err(GeneratedBindError::CatalogSignatureConflict {
                kind: "sort",
                name: key.name,
                span: span.clone(),
            });
        }
        self.sorts.insert(key.name.clone(), key.clone());
        Ok(key)
    }

    pub(super) fn register_function(
        &mut self,
        key: FunctionKey,
        span: &Span,
    ) -> Result<CallKey, GeneratedBindError> {
        if let Some(existing) = self.functions.get(&key.name) {
            if existing == &key {
                return Ok(CallKey::Function(existing.clone()));
            }
            return Err(GeneratedBindError::CatalogSignatureConflict {
                kind: "function",
                name: key.name,
                span: span.clone(),
            });
        }
        for sort in key.inputs.iter().chain(match &key.output {
            ValueShape::Scalar(sort) => std::slice::from_ref(sort),
            ValueShape::Tuple(sorts) => sorts,
        }) {
            self.require_sort(sort, span)?;
        }
        self.functions.insert(key.name.clone(), key.clone());
        Ok(CallKey::Function(key))
    }

    /// Register one index declaration in the shared function namespace and
    /// validate its column projection against the portable target signature.
    /// Unlike reusable call signatures, a second index declaration is always
    /// an error, even when textually identical.
    pub(super) fn register_index(
        &mut self,
        name: String,
        function: &FunctionKey,
        any_of: &[usize],
        span: &Span,
    ) -> Result<(), GeneratedBindError> {
        if self.functions.contains_key(&name) || self.indexes.contains(&name) {
            return Err(GeneratedBindError::CatalogSignatureConflict {
                kind: "function or index",
                name,
                span: span.clone(),
            });
        }
        match self.functions.get(&function.name) {
            Some(registered) if registered == function => {}
            Some(_) => {
                return Err(GeneratedBindError::CatalogSignatureConflict {
                    kind: "index target",
                    name: function.name.clone(),
                    span: span.clone(),
                });
            }
            None => {
                return Err(GeneratedBindError::MissingCatalogSignature {
                    kind: "index target",
                    name: function.name.clone(),
                    span: span.clone(),
                });
            }
        }
        let row = function
            .inputs
            .iter()
            .chain(match &function.output {
                ValueShape::Scalar(sort) => std::slice::from_ref(sort),
                ValueShape::Tuple(sorts) => sorts,
            })
            .collect::<Vec<_>>();
        let Some((&first, rest)) = any_of.split_first() else {
            return Err(TypeError::EmptyIndex(name, span.clone()).into());
        };
        let Some(first_sort) = row.get(first) else {
            return Err(
                TypeError::IndexColumnOutOfRange(name, first, row.len(), span.clone()).into(),
            );
        };
        for &column in rest {
            let Some(sort) = row.get(column) else {
                return Err(TypeError::IndexColumnOutOfRange(
                    name,
                    column,
                    row.len(),
                    span.clone(),
                )
                .into());
            };
            if sort != first_sort {
                return Err(TypeError::IndexColumnSortMismatch(
                    name,
                    first_sort.name.clone(),
                    sort.name.clone(),
                    span.clone(),
                )
                .into());
            }
        }
        let unit = self.sorts.get("Unit").cloned().ok_or_else(|| {
            GeneratedBindError::MissingCatalogSignature {
                kind: "sort",
                name: "Unit".to_owned(),
                span: span.clone(),
            }
        })?;
        let mut inputs = vec![(*first_sort).clone()];
        inputs.extend(function.inputs.iter().cloned());
        match &function.output {
            ValueShape::Scalar(sort) => inputs.push(sort.clone()),
            ValueShape::Tuple(sorts) => inputs.extend(sorts.iter().cloned()),
        }
        self.functions.insert(
            name.clone(),
            FunctionKey {
                name: name.clone(),
                subtype: FunctionSubtype::Custom,
                inputs,
                output: ValueShape::Scalar(unit),
            },
        );
        self.indexes.insert(name);
        Ok(())
    }

    pub(super) fn register_primitive(
        &mut self,
        key: PrimitiveKey,
        span: &Span,
    ) -> Result<CallKey, GeneratedBindError> {
        for sort in key.inputs.iter().chain(std::iter::once(&key.output)) {
            self.require_sort(sort, span)?;
        }
        self.primitives.insert(key.clone());
        Ok(CallKey::Primitive(key))
    }

    #[cfg(test)]
    pub(super) fn function_call(
        &self,
        name: &str,
        span: &Span,
    ) -> Result<CallKey, GeneratedBindError> {
        self.functions
            .get(name)
            .cloned()
            .map(CallKey::Function)
            .ok_or_else(|| GeneratedBindError::MissingCatalogSignature {
                kind: "function",
                name: name.to_owned(),
                span: span.clone(),
            })
    }

    pub(super) fn values_call(
        &self,
        sorts: Vec<SortKey>,
        span: &Span,
    ) -> Result<CallKey, GeneratedBindError> {
        if sorts.len() < 2 {
            return Err(GeneratedBindError::InvalidTupleArity {
                actual: sorts.len(),
                span: span.clone(),
            });
        }
        for sort in &sorts {
            self.require_sort(sort, span)?;
        }
        Ok(CallKey::Values(sorts))
    }

    fn require_sort(&self, key: &SortKey, span: &Span) -> Result<(), GeneratedBindError> {
        match self.sorts.get(&key.name) {
            Some(existing) if existing == key => Ok(()),
            Some(_) => Err(GeneratedBindError::CatalogSignatureConflict {
                kind: "sort",
                name: key.name.clone(),
                span: span.clone(),
            }),
            None => Err(GeneratedBindError::MissingCatalogSignature {
                kind: "sort",
                name: key.name.clone(),
                span: span.clone(),
            }),
        }
    }
}

/// Assigns rule-local IDs at first lexical observation and rejects a later use
/// of the same spelling with a different generated sort.
#[derive(Debug, Default)]
pub(super) struct GeneratedRuleBuilder {
    variables: HashMap<(String, GeneratedVarRole), GeneratedVar>,
    next_local_id: u32,
}

impl GeneratedRuleBuilder {
    pub(super) fn variable(
        &mut self,
        name: impl Into<String>,
        sort: SortKey,
        role: GeneratedVarRole,
        span: &Span,
    ) -> Result<GeneratedVar, GeneratedBindError> {
        let name = name.into();
        let identity = (name.clone(), role);
        if let Some(existing) = self.variables.get(&identity) {
            if existing.sort == sort {
                return Ok(existing.clone());
            }
            return Err(GeneratedBindError::RuleBuilderSortMismatch {
                name,
                span: span.clone(),
            });
        }
        let id = LocalId(self.next_local_id);
        self.next_local_id = self.next_local_id.checked_add(1).ok_or_else(|| {
            GeneratedBindError::InternalInvariant {
                message: "generated rule builder exhausted local ids",
                span: span.clone(),
            }
        })?;
        let variable = GeneratedVar {
            id,
            name: name.clone(),
            sort,
            role,
        };
        self.variables.insert(identity, variable.clone());
        Ok(variable)
    }
}

#[derive(Debug, Error)]
pub(super) enum GeneratedBindError {
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
    #[error("{span}\ngenerated rule retained live global `{name}` after source global removal")]
    UnexpectedRuleGlobal { name: String, span: Span },
    #[error("{span}\ngenerated local id {id} was reused with incompatible metadata")]
    InconsistentLocalId { id: u32, span: Span },
    #[error("{span}\ngenerated local name `{name}` was reused with a different id")]
    InconsistentLocalName { name: String, span: Span },
    #[error("{span}\ngenerated local `{name}` was defined more than once")]
    DuplicateLocal { name: String, span: Span },
    #[error("{span}\ngenerated rule-local `{name}` was reused with a different sort")]
    RuleBuilderSortMismatch { name: String, span: Span },
    #[error("{span}\ngenerated {kind} signature `{name}` conflicts with its catalog entry")]
    CatalogSignatureConflict {
        kind: &'static str,
        name: String,
        span: Span,
    },
    #[error("{span}\ngenerated {kind} signature `{name}` is missing from the catalog")]
    MissingCatalogSignature {
        kind: &'static str,
        name: String,
        span: Span,
    },
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
    #[error("{span}\nextract requires a scalar value, got {actual}")]
    CannotExtractTuple { actual: String, span: Span },
    #[error("{span}\ngenerated binder invariant failed: {message}")]
    InternalInvariant { message: &'static str, span: Span },
}

impl From<GeneratedBindError> for EgglogError {
    fn from(error: GeneratedBindError) -> Self {
        match error {
            GeneratedBindError::Type(error) => EgglogError::TypeError(error),
            error => EgglogError::DesugarError(
                crate::span!(),
                format!("generated binder failed: {error}"),
            ),
        }
    }
}

#[derive(Clone)]
enum ResolvedValueShape {
    Scalar(ArcSort),
    Tuple(Vec<ArcSort>),
}

impl ResolvedValueShape {
    fn from_expr(expr: &ResolvedExpr) -> Self {
        match expr {
            GenericExpr::Var(_, variable) => Self::Scalar(variable.sort.clone()),
            GenericExpr::Lit(_, literal) => Self::Scalar(crate::sort::literal_sort(literal)),
            GenericExpr::Call(_, ResolvedCall::Func(function), _) => {
                if function.outputs.len() == 1 {
                    Self::Scalar(function.outputs[0].clone())
                } else {
                    Self::Tuple(function.outputs.clone())
                }
            }
            GenericExpr::Call(_, ResolvedCall::Primitive(primitive), _) => {
                Self::Scalar(primitive.output().clone())
            }
            GenericExpr::Call(_, ResolvedCall::Values(sorts), _) => Self::Tuple(sorts.clone()),
        }
    }

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

    fn matches(&self, expected: &ValueShape) -> bool {
        match (self, expected) {
            (Self::Scalar(actual), ValueShape::Scalar(expected)) => expected.matches_sort(actual),
            (Self::Tuple(actual), ValueShape::Tuple(expected)) => {
                actual.len() == expected.len()
                    && actual
                        .iter()
                        .zip(expected)
                        .all(|(actual, expected)| expected.matches_sort(actual))
            }
            _ => false,
        }
    }

    fn same_as(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Scalar(left), Self::Scalar(right)) => {
                SortKey::from_sort(left) == SortKey::from_sort(right)
            }
            (Self::Tuple(left), Self::Tuple(right)) => {
                left.len() == right.len()
                    && left
                        .iter()
                        .zip(right)
                        .all(|(left, right)| SortKey::from_sort(left) == SortKey::from_sort(right))
            }
            _ => false,
        }
    }
}

#[derive(Clone)]
struct CachedSort {
    sort: ArcSort,
}

#[derive(Clone)]
struct CachedResolvedCall {
    key: CallKey,
    call: Arc<ResolvedCall>,
}

#[derive(Clone, Default)]
struct HeadCallCache {
    generation: Option<u64>,
    primitive_epoch: Option<u64>,
    by_context: EnumMap<Context, Vec<CachedResolvedCall>>,
    function_receipt: Option<(FunctionKey, Arc<ResolvedCall>)>,
}

impl HeadCallCache {
    /// Synchronize the two independent invalidation domains. Registrations for
    /// this head discard every cached interpretation, while unrelated
    /// TypeInfo mutations discard only primitive results: function results and
    /// declaration receipts depend solely on their name-local generation.
    fn prepare_for_resolution(&mut self, generation: u64, primitive_epoch: Option<u64>) {
        if self.generation != Some(generation) {
            self.generation = Some(generation);
            self.primitive_epoch = primitive_epoch;
            self.by_context = EnumMap::default();
            self.function_receipt = None;
            return;
        }
        if let Some(epoch) = primitive_epoch
            && self.primitive_epoch != Some(epoch)
        {
            for (_, entries) in self.by_context.iter_mut() {
                entries.retain(|cached| !matches!(&cached.key, CallKey::Primitive(_)));
            }
            self.primitive_epoch = Some(epoch);
        }
    }
}

#[derive(Clone, Default)]
struct BindingState {
    sort_cache: HashMap<SortKey, CachedSort>,
    call_cache: HashMap<String, HeadCallCache>,
}

impl BindingState {
    fn resolve_sort(
        &mut self,
        type_info: &TypeInfo,
        key: &SortKey,
        span: &Span,
    ) -> Result<ArcSort, GeneratedBindError> {
        if let Some(cached) = self.sort_cache.get(key) {
            return Ok(cached.sort.clone());
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
        self.sort_cache
            .insert(key.clone(), CachedSort { sort: sort.clone() });
        Ok(sort)
    }

    fn resolve_call(
        &mut self,
        type_info: &TypeInfo,
        key: &CallKey,
        context: Context,
        span: &Span,
    ) -> Result<ResolvedCall, GeneratedBindError> {
        let head = match key {
            CallKey::Function(key) => key.name.as_str(),
            CallKey::Primitive(key) => key.name.as_str(),
            CallKey::Values(_) => "values",
        };
        let (head_generation, primitive_epoch) = match key {
            CallKey::Function(_) => type_info.call_cache_stamp(head, false),
            CallKey::Primitive(_) => type_info.call_cache_stamp(head, true),
            CallKey::Values(_) => (0, None),
        };
        if let Some(cache) = self.call_cache.get_mut(head) {
            cache.prepare_for_resolution(head_generation, primitive_epoch);
        }
        let cached = self
            .call_cache
            .get(head)
            .filter(|cache| cache.generation == Some(head_generation))
            .and_then(|cache| {
                cache.by_context[context]
                    .iter()
                    .find(|cached| &cached.key == key)
            })
            .map(|cached| Arc::clone(&cached.call));
        if let Some(call) = cached {
            return Ok((*call).clone());
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
        if let Some(call) = registration_receipt {
            let Some(cache) = self.call_cache.get_mut(head) else {
                return Err(GeneratedBindError::InternalInvariant {
                    message: "a matching registration receipt lost its head cache",
                    span: span.clone(),
                });
            };
            cache.by_context[context].push(CachedResolvedCall {
                key: key.clone(),
                call: Arc::clone(&call),
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
                let call =
                    ResolvedCall::from_resolution(head, &signature, type_info, context, span)?;
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
                    ResolvedCall::Values(_) => {
                        return Err(GeneratedBindError::WrongCallKind {
                            head: function.name.clone(),
                            expected: CallKind::Function,
                            actual: CallKind::Values,
                            span: span.clone(),
                        });
                    }
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
                let call =
                    ResolvedCall::from_resolution(head, &signature, type_info, context, span)?;
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
                    ResolvedCall::Values(_) => {
                        return Err(GeneratedBindError::WrongCallKind {
                            head: primitive.name.clone(),
                            expected: CallKind::Primitive,
                            actual: CallKind::Values,
                            span: span.clone(),
                        });
                    }
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
        cache.prepare_for_resolution(head_generation, primitive_epoch);
        cache.by_context[context].push(CachedResolvedCall {
            key: key.clone(),
            call: Arc::clone(&resolved),
        });
        Ok((*resolved).clone())
    }

    /// Seed the exact, generation-scoped function result produced by a
    /// successful declaration commit. Context entries remain lazy so unused
    /// generated declarations do not pay four resolved-call clones.
    fn record_function_receipt(
        &mut self,
        type_info: &TypeInfo,
        key: FunctionKey,
        call: ResolvedCall,
    ) {
        debug_assert!(matches!(&call, ResolvedCall::Func(function) if function.name == key.name));
        let (generation, _) = type_info.call_cache_stamp(&key.name, false);
        let cache = self.call_cache.entry(key.name.clone()).or_default();
        cache.generation = Some(generation);
        cache.primitive_epoch = None;
        cache.by_context = EnumMap::default();
        cache.function_receipt = Some((key, Arc::new(call)));
    }
}

#[derive(Clone, Default)]
struct LocalScope {
    by_id: HashMap<LocalId, ResolvedVar>,
    by_name: HashMap<String, LocalId>,
    roles_by_id: HashMap<LocalId, GeneratedVarRole>,
}

#[derive(Clone)]
struct SyntheticGlobal {
    variable: GeneratedVar,
    sort: ArcSort,
    call: ResolvedCall,
}

type SyntheticGlobals = HashMap<LocalId, SyntheticGlobal>;

/// Generated command expressions may directly materialize live globals as
/// ephemeral nullary calls. Generated rules use the stricter variant because
/// source global removal has to add a query lookup before a head can consume a
/// global; silently emitting an action-side lookup would change seminaive
/// behavior.
#[derive(Clone, Copy)]
enum GlobalBinding<'a> {
    Nullary {
        synthetic: Option<&'a SyntheticGlobals>,
    },
    MustAlreadyBeRemoved,
}

impl LocalScope {
    fn declare(
        &mut self,
        generated: &GeneratedVar,
        resolved: ResolvedVar,
        span: &Span,
    ) -> Result<(), GeneratedBindError> {
        if let Some(existing) = self.by_id.get(&generated.id) {
            if existing.name == generated.name
                && existing.sort.name() == resolved.sort.name()
                && !existing.is_global_ref
                && self.roles_by_id.get(&generated.id) == Some(&generated.role)
            {
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
        self.roles_by_id.insert(generated.id, generated.role);
        self.by_id.insert(generated.id, resolved);
        Ok(())
    }
}

fn visit_expr_vars<E>(
    expr: &GeneratedExpr,
    visit: &mut impl FnMut(&Span, &GeneratedVar) -> Result<(), E>,
) -> Result<(), E> {
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

/// Visit exactly the portable locals that source `Facts::to_query` places in
/// query atoms. An equality contributes both expression roots, while a bare
/// `(Fact var)` produces no atom at all; only children of a fact call are
/// represented as atom terms. The signature catalog and binder share this
/// boundary so malformed producer IR cannot acquire a direct-only binding.
fn visit_query_binding_vars<E>(
    facts: &[GeneratedFact],
    visit: &mut impl FnMut(&Span, &GeneratedVar) -> Result<(), E>,
) -> Result<(), E> {
    for fact in facts {
        match fact {
            GenericFact::Eq(_, left, right) => {
                visit_expr_vars(left, visit)?;
                visit_expr_vars(right, visit)?;
            }
            GenericFact::Fact(GenericExpr::Call(_, _, args)) => {
                for arg in args {
                    visit_expr_vars(arg, visit)?;
                }
            }
            GenericFact::Fact(GenericExpr::Var(..) | GenericExpr::Lit(..)) => {}
        }
    }
    Ok(())
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

fn rule_call_contexts(global_seminaive: bool, eval_mode: &RuleEvalMode) -> (Context, Context) {
    if !global_seminaive
        || matches!(
            eval_mode,
            RuleEvalMode::Naive | RuleEvalMode::UnsafeSeminaive
        )
    {
        (Context::Read, Context::Full)
    } else {
        (Context::Pure, Context::Write)
    }
}

struct GeneratedTupleDestructure<'a> {
    values_args: &'a [GeneratedExpr],
    function_head: &'a CallKey,
    function_span: &'a Span,
    function_args: &'a [GeneratedExpr],
}

fn match_generated_tuple_destructure<'a>(
    left: &'a GeneratedExpr,
    right: &'a GeneratedExpr,
    type_info: &TypeInfo,
) -> Option<GeneratedTupleDestructure<'a>> {
    for (values, function) in [(left, right), (right, left)] {
        let GenericExpr::Call(_, CallKey::Values(_), values_args) = values else {
            continue;
        };
        let GenericExpr::Call(function_span, function_head, function_args) = function else {
            continue;
        };
        let function_name = match function_head {
            CallKey::Function(function) => function.name.as_str(),
            CallKey::Primitive(primitive) => primitive.name.as_str(),
            CallKey::Values(_) => "values",
        };
        if type_info
            .get_func_type(function_name)
            .is_some_and(|function| function.is_tuple_output())
        {
            return Some(GeneratedTupleDestructure {
                values_args,
                function_head,
                function_span,
                function_args,
            });
        }
    }
    None
}

/// Replays the observable rule-frontend effects at the traversal point where
/// the source frontend produced them. This deliberately derives its events
/// from the portable AST and the live checker registry: a flat success trace
/// cannot preserve the prefix when a later query/action validation fails.
struct RuleFrontendEffects<'a> {
    type_info: &'a TypeInfo,
    symbol_gen: &'a mut SymbolGen,
    scope: HashSet<String>,
    expr_outputs: HashMap<usize, String>,
    action_outputs: HashMap<usize, Vec<String>>,
    synthetic: Option<&'a SyntheticGlobals>,
    query_context: Context,
    action_context: Context,
}

impl RuleFrontendEffects<'_> {
    fn variable_is_bound(&self, variable: &GeneratedVar) -> bool {
        if self.synthetic.is_some_and(|synthetic| {
            synthetic.get(&variable.id).is_some_and(|existing| {
                existing.variable.name == variable.name
                    && existing.variable.sort == variable.sort
                    && existing.variable.role == variable.role
            })
        }) {
            return true;
        }
        match variable.role {
            GeneratedVarRole::Global => self.type_info.is_global(&variable.name),
            GeneratedVarRole::Local => self.scope.contains(&variable.name),
        }
    }

    fn observe_query_binding(&mut self, variable: &GeneratedVar) {
        if self.synthetic.is_some_and(|synthetic| {
            synthetic.get(&variable.id).is_some_and(|existing| {
                existing.variable.name == variable.name
                    && existing.variable.sort == variable.sort
                    && existing.variable.role == variable.role
            })
        }) {
            return;
        }
        match variable.role {
            GeneratedVarRole::Global => {}
            GeneratedVarRole::Local => {
                self.scope.insert(variable.name.clone());
            }
        }
    }

    /// Convert a portable call back to the unresolved head spelling used as
    /// the source `SymbolGen` hint, then return the actual minted name. The
    /// returned spelling matters because expression-call outputs enter the
    /// source action/query binding scope.
    fn fresh_source_call(&mut self, call: &CallKey) -> String {
        let hint = match call {
            CallKey::Function(function) => function.name.as_str(),
            CallKey::Primitive(primitive) => primitive.name.as_str(),
            CallKey::Values(_) => "values",
        };
        self.symbol_gen.fresh(hint)
    }

    /// Reproduce the source solver's stable ambiguity payload without
    /// invoking source inference. Exact generated keys already carry the full
    /// concrete signature; only indistinguishable primitive registrations can
    /// leave the source solver unable to name a type for the minted output.
    fn validate_diagnostic_resolution(
        &self,
        call: &CallKey,
        context: Context,
        span: &Span,
        output: &str,
    ) -> Result<(), TypeError> {
        let name = match call {
            CallKey::Function(function) => function.name.as_str(),
            CallKey::Primitive(primitive) => primitive.name.as_str(),
            CallKey::Values(_) => return Ok(()),
        };
        let context_valid_primitives = self
            .type_info
            .get_prims(name)
            .into_iter()
            .flatten()
            .filter(|primitive| primitive.is_valid_in_context(context))
            .count();
        if context_valid_primitives <= 1
            && (context_valid_primitives == 0 || self.type_info.get_func_type(name).is_none())
        {
            return Ok(());
        }

        let resolve_sort = |key: &SortKey| {
            self.type_info
                .get_sort_by_name(&key.name)
                .filter(|sort| key.matches_sort(sort))
                .cloned()
        };
        let mut signature = match call {
            CallKey::Function(function) => function
                .inputs
                .iter()
                .map(resolve_sort)
                .collect::<Option<Vec<_>>>(),
            CallKey::Primitive(primitive) => primitive
                .inputs
                .iter()
                .map(resolve_sort)
                .collect::<Option<Vec<_>>>(),
            CallKey::Values(_) => unreachable!("values returned before diagnostic resolution"),
        };
        let Some(ref mut signature) = signature else {
            return Ok(());
        };
        match call {
            CallKey::Function(function) => match &function.output {
                ValueShape::Scalar(sort) => {
                    let Some(sort) = resolve_sort(sort) else {
                        return Ok(());
                    };
                    signature.push(sort);
                }
                ValueShape::Tuple(sorts) => {
                    let Some(sorts) = sorts.iter().map(resolve_sort).collect::<Option<Vec<_>>>()
                    else {
                        return Ok(());
                    };
                    signature.extend(sorts);
                }
            },
            CallKey::Primitive(primitive) => {
                let Some(sort) = resolve_sort(&primitive.output) else {
                    return Ok(());
                };
                signature.push(sort);
            }
            CallKey::Values(_) => unreachable!("values returned before diagnostic resolution"),
        }

        match ResolvedCall::from_resolution(name, signature, self.type_info, context, span) {
            Err(TypeError::AmbiguousPrimitive { .. })
            | Err(TypeError::UnresolvedPrimitive { .. }) => Err(TypeError::InferenceFailure(
                Expr::Var(span.clone(), output.to_owned()),
            )),
            Err(error) => Err(error),
            Ok(_) => Ok(()),
        }
    }

    /// Match the eager failure boundary of atom-constraint construction. At
    /// this point source typechecking only requires some function or a
    /// context-valid primitive with this head; signature defects are solved
    /// later and are impossible for producer-owned typed IR.
    fn validate_query_or_action_head(
        &self,
        call: &CallKey,
        context: Context,
        span: &Span,
    ) -> Result<(), TypeError> {
        let name = match call {
            CallKey::Function(function) => function.name.as_str(),
            CallKey::Primitive(primitive) => primitive.name.as_str(),
            CallKey::Values(_) => "values",
        };
        let has_candidate = self.type_info.get_func_type(name).is_some()
            || self.type_info.get_prims(name).is_some_and(|primitives| {
                primitives
                    .iter()
                    .any(|primitive| primitive.is_valid_in_context(context))
            });
        if has_candidate {
            Ok(())
        } else {
            Err(TypeError::UnboundFunction(name.to_owned(), span.clone()))
        }
    }

    /// Preserve the source constraint solver's arity error when a retained
    /// pre-encoding function expression is replayed against its encoded table.
    /// An expression atom has one synthetic result column, so the displayed
    /// source arity is the live function's total row width minus that column.
    /// A context-valid primitive keeps the original XOR alternative alive and
    /// must be left to diagnostic resolution below.
    fn validate_source_expression_arity(
        &self,
        expr: &GeneratedExpr,
        call: &CallKey,
        args: &[GeneratedExpr],
        context: Context,
    ) -> Result<(), TypeError> {
        let name = match call {
            CallKey::Function(function) => function.name.as_str(),
            CallKey::Primitive(primitive) => primitive.name.as_str(),
            CallKey::Values(_) => return Ok(()),
        };
        if self.type_info.get_prims(name).is_some_and(|primitives| {
            primitives
                .iter()
                .any(|primitive| primitive.is_valid_in_context(context))
        }) {
            return Ok(());
        }
        let Some(function) = self.type_info.get_func_type(name) else {
            return Ok(());
        };
        let expected_row_width = function.input.len() + function.num_outputs();
        if expected_row_width == args.len() + 1 {
            return Ok(());
        }
        let source_expr = expr.clone().map_symbols(
            &mut |head| match head {
                CallKey::Function(function) => function.name,
                CallKey::Primitive(primitive) => primitive.name,
                CallKey::Values(_) => "values".to_owned(),
            },
            &mut |variable| variable.name,
        );
        Err(TypeError::Arity {
            expr: source_expr,
            expected: expected_row_width - 1,
        })
    }

    fn lower_query_expr(&mut self, expr: &GeneratedExpr) {
        match expr {
            GenericExpr::Var(..) => {}
            GenericExpr::Lit(..) => {}
            GenericExpr::Call(_, call, args) => {
                // `GenericExprExt::to_query` mints the output before walking
                // children, even though it appends the resulting atom after
                // its children's atoms.
                let output = self.fresh_source_call(call);
                self.expr_outputs
                    .insert(expr as *const GeneratedExpr as usize, output.clone());
                self.scope.insert(output);
                for arg in args {
                    self.lower_query_expr(arg);
                }
            }
        }
    }

    fn lower_query_fact(&mut self, fact: &GeneratedFact) {
        match fact {
            GenericFact::Eq(_, left, right) => {
                if let Some(tuple) = match_generated_tuple_destructure(left, right, self.type_info)
                {
                    // Tuple destructuring bypasses both outer expression calls:
                    // it lowers inputs, then outputs, then mints two mapped-AST
                    // correspondence names that never enter the query scope.
                    for arg in tuple.function_args {
                        self.lower_query_expr(arg);
                    }
                    for value in tuple.values_args {
                        self.lower_query_expr(value);
                    }
                    let _ = self.fresh_source_call(tuple.function_head);
                    let _ = self.fresh_source_call(tuple.function_head);
                } else {
                    self.lower_query_expr(left);
                    self.lower_query_expr(right);
                }
            }
            GenericFact::Fact(expr) => self.lower_query_expr(expr),
        }
    }

    fn validate_query_expr_candidates(&self, expr: &GeneratedExpr) -> Result<(), TypeError> {
        match expr {
            GenericExpr::Var(..) | GenericExpr::Lit(..) => Ok(()),
            GenericExpr::Call(span, call, args) => {
                for arg in args {
                    self.validate_query_expr_candidates(arg)?;
                }
                self.validate_query_or_action_head(call, self.query_context, span)
            }
        }
    }

    fn resolve_query_expr_diagnostics(&self, expr: &GeneratedExpr) -> Result<(), TypeError> {
        match expr {
            GenericExpr::Var(..) | GenericExpr::Lit(..) => Ok(()),
            GenericExpr::Call(span, call, args) => {
                for arg in args {
                    self.resolve_query_expr_diagnostics(arg)?;
                }
                self.validate_source_expression_arity(expr, call, args, self.query_context)?;
                let output = self
                    .expr_outputs
                    .get(&(expr as *const GeneratedExpr as usize))
                    .expect("query call lowering must mint its output before validation");
                self.validate_diagnostic_resolution(call, self.query_context, span, output)
            }
        }
    }

    fn validate_query_fact_candidates(&self, fact: &GeneratedFact) -> Result<(), TypeError> {
        match fact {
            GenericFact::Eq(_, left, right) => {
                if let Some(tuple) = match_generated_tuple_destructure(left, right, self.type_info)
                {
                    for arg in tuple.function_args {
                        self.validate_query_expr_candidates(arg)?;
                    }
                    for value in tuple.values_args {
                        self.validate_query_expr_candidates(value)?;
                    }
                    self.validate_query_or_action_head(
                        tuple.function_head,
                        self.query_context,
                        tuple.function_span,
                    )
                } else {
                    self.validate_query_expr_candidates(left)?;
                    self.validate_query_expr_candidates(right)
                }
            }
            GenericFact::Fact(expr) => self.validate_query_expr_candidates(expr),
        }
    }

    fn resolve_query_fact_diagnostics(&self, fact: &GeneratedFact) -> Result<(), TypeError> {
        match fact {
            GenericFact::Eq(_, left, right) => {
                if let Some(tuple) = match_generated_tuple_destructure(left, right, self.type_info)
                {
                    for arg in tuple.function_args {
                        self.resolve_query_expr_diagnostics(arg)?;
                    }
                    for value in tuple.values_args {
                        self.resolve_query_expr_diagnostics(value)?;
                    }
                    Ok(())
                } else {
                    self.resolve_query_expr_diagnostics(left)?;
                    self.resolve_query_expr_diagnostics(right)
                }
            }
            GenericFact::Fact(expr) => self.resolve_query_expr_diagnostics(expr),
        }
    }

    fn lower_action_expr(&mut self, expr: &GeneratedExpr) -> Result<(), TypeError> {
        match expr {
            GenericExpr::Var(span, variable) => {
                if self.variable_is_bound(variable) {
                    Ok(())
                } else {
                    Err(TypeError::Unbound(variable.name.clone(), span.clone()))
                }
            }
            GenericExpr::Lit(..) => Ok(()),
            GenericExpr::Call(_, call, args) => {
                for arg in args {
                    self.lower_action_expr(arg)?;
                }
                // Action lowering is postorder and makes expression-call
                // outputs visible to subsequent actions.
                let output = self.fresh_source_call(call);
                self.expr_outputs
                    .insert(expr as *const GeneratedExpr as usize, output.clone());
                self.scope.insert(output);
                Ok(())
            }
        }
    }

    fn lower_action(&mut self, action: &GeneratedAction) -> Result<(), TypeError> {
        match action {
            GenericAction::Let(span, variable, expr) => {
                if self.scope.contains(&variable.name) {
                    return Err(TypeError::AlreadyDefined(
                        variable.name.clone(),
                        span.clone(),
                    ));
                }
                self.lower_action_expr(expr)?;
                self.scope.insert(variable.name.clone());
            }
            GenericAction::Set(_, head, args, value) => {
                for arg in args {
                    self.lower_action_expr(arg)?;
                }
                if let GenericExpr::Call(_, CallKey::Values(_), values) = value {
                    for value in values {
                        self.lower_action_expr(value)?;
                    }
                    let _: String = self.symbol_gen.fresh("values");
                } else {
                    self.lower_action_expr(value)?;
                }
                let output = self.fresh_source_call(head);
                self.action_outputs
                    .insert(action as *const GeneratedAction as usize, vec![output]);
            }
            GenericAction::Change(_, _, head, args) => {
                for arg in args {
                    self.lower_action_expr(arg)?;
                }
                let output = self.fresh_source_call(head);
                self.action_outputs
                    .insert(action as *const GeneratedAction as usize, vec![output]);
            }
            GenericAction::Union(_, left, right) => {
                self.lower_action_expr(left)?;
                self.lower_action_expr(right)?;
            }
            GenericAction::Panic(..) => {}
            GenericAction::Expr(_, expr) => self.lower_action_expr(expr)?,
        }
        Ok(())
    }

    fn validate_action_expr_candidates(&self, expr: &GeneratedExpr) -> Result<(), TypeError> {
        match expr {
            GenericExpr::Var(..) | GenericExpr::Lit(..) => Ok(()),
            GenericExpr::Call(span, call, args) => {
                for arg in args {
                    self.validate_action_expr_candidates(arg)?;
                }
                self.validate_query_or_action_head(call, self.action_context, span)
            }
        }
    }

    fn resolve_action_expr_diagnostics(&self, expr: &GeneratedExpr) -> Result<(), TypeError> {
        match expr {
            GenericExpr::Var(..) | GenericExpr::Lit(..) => Ok(()),
            GenericExpr::Call(span, call, args) => {
                for arg in args {
                    self.resolve_action_expr_diagnostics(arg)?;
                }
                self.validate_source_expression_arity(expr, call, args, self.action_context)?;
                let output = self
                    .expr_outputs
                    .get(&(expr as *const GeneratedExpr as usize))
                    .expect("action call lowering must mint its output before validation");
                self.validate_diagnostic_resolution(call, self.action_context, span, output)
            }
        }
    }

    fn validate_action_candidates(&mut self, action: &GeneratedAction) -> Result<(), TypeError> {
        match action {
            GenericAction::Let(_, _, expr) | GenericAction::Expr(_, expr) => {
                self.validate_action_expr_candidates(expr)?;
            }
            GenericAction::Set(span, head, args, value) => {
                for arg in args {
                    self.validate_action_expr_candidates(arg)?;
                }
                if let GenericExpr::Call(_, CallKey::Values(_), values) = value {
                    for value in values {
                        self.validate_action_expr_candidates(value)?;
                    }
                } else {
                    self.validate_action_expr_candidates(value)?;
                }
                let name = match head {
                    CallKey::Function(function) => function.name.as_str(),
                    CallKey::Primitive(primitive) => primitive.name.as_str(),
                    CallKey::Values(_) => "values",
                };
                if self.type_info.is_constructor(name) {
                    return Err(TypeError::SetConstructorDisallowed(
                        name.to_owned(),
                        span.clone(),
                    ));
                }
                self.validate_query_or_action_head(head, self.action_context, span)?;
            }
            GenericAction::Change(span, _, head, args) => {
                for arg in args {
                    self.validate_action_expr_candidates(arg)?;
                }
                let name = match head {
                    CallKey::Function(function) => function.name.as_str(),
                    CallKey::Primitive(primitive) => primitive.name.as_str(),
                    CallKey::Values(_) => "values",
                };
                let output_count = self
                    .type_info
                    .get_func_type(name)
                    .map(|function| function.num_outputs())
                    .unwrap_or(1);
                let mut outputs = Vec::with_capacity(output_count);
                for _ in 0..output_count {
                    outputs.push(self.fresh_source_call(head));
                }
                self.action_outputs
                    .insert(action as *const GeneratedAction as usize, outputs);
                self.validate_query_or_action_head(head, self.action_context, span)?;
            }
            GenericAction::Union(_, left, right) => {
                self.validate_action_expr_candidates(left)?;
                self.validate_action_expr_candidates(right)?;
            }
            GenericAction::Panic(..) => {}
        }
        Ok(())
    }

    fn resolve_action_diagnostics(&self, action: &GeneratedAction) -> Result<(), TypeError> {
        match action {
            GenericAction::Let(_, _, expr) | GenericAction::Expr(_, expr) => {
                self.resolve_action_expr_diagnostics(expr)?;
            }
            GenericAction::Set(span, head, args, value) => {
                for arg in args {
                    self.resolve_action_expr_diagnostics(arg)?;
                }
                if let GenericExpr::Call(_, CallKey::Values(_), values) = value {
                    for value in values {
                        self.resolve_action_expr_diagnostics(value)?;
                    }
                } else {
                    self.resolve_action_expr_diagnostics(value)?;
                }
                let output = self
                    .action_outputs
                    .get(&(action as *const GeneratedAction as usize))
                    .and_then(|outputs| outputs.first())
                    .expect("set lowering must mint its table-call output before validation");
                self.validate_diagnostic_resolution(head, self.action_context, span, output)?;
            }
            GenericAction::Change(span, _, head, args) => {
                for arg in args {
                    self.resolve_action_expr_diagnostics(arg)?;
                }
                let output = self
                    .action_outputs
                    .get(&(action as *const GeneratedAction as usize))
                    .and_then(|outputs| outputs.first())
                    .expect("change validation must mint at least one output");
                self.validate_diagnostic_resolution(head, self.action_context, span, output)?;
            }
            GenericAction::Union(_, left, right) => {
                self.resolve_action_expr_diagnostics(left)?;
                self.resolve_action_expr_diagnostics(right)?;
            }
            GenericAction::Panic(..) => {}
        }
        Ok(())
    }

    fn replay(&mut self, rule: &GeneratedRule) -> Result<(), TypeError> {
        // Query candidate construction precedes head lowering. Constraint
        // ambiguity and inference errors do not surface until after the whole
        // head has lowered and every query/head constraint has been built.
        for fact in &rule.body {
            self.lower_query_fact(fact);
        }
        visit_query_binding_vars(&rule.body, &mut |_, variable| {
            self.observe_query_binding(variable);
            Ok::<(), TypeError>(())
        })?;
        for fact in &rule.body {
            self.validate_query_fact_candidates(fact)?;
        }
        for action in &rule.head.0 {
            self.lower_action(action)?;
        }
        for action in &rule.head.0 {
            self.validate_action_candidates(action)?;
        }
        for fact in &rule.body {
            self.resolve_query_fact_diagnostics(fact)?;
        }
        for action in &rule.head.0 {
            self.resolve_action_diagnostics(action)?;
        }
        Ok(())
    }
}

fn replay_direct_rule_frontend_effects(
    egraph: &mut EGraph,
    rule: &GeneratedRule,
) -> Result<(), TypeError> {
    let (query_context, action_context) = rule_call_contexts(egraph.seminaive, &rule.eval_mode);
    let mut effects = RuleFrontendEffects {
        type_info: &egraph.type_info,
        symbol_gen: &mut egraph.parser.symbol_gen,
        scope: HashSet::default(),
        expr_outputs: HashMap::default(),
        action_outputs: HashMap::default(),
        synthetic: None,
        query_context,
        action_context,
    };
    effects.replay(rule)
}

fn replay_generated_actions_effects(
    type_info: &TypeInfo,
    symbol_gen: &mut SymbolGen,
    actions: &GeneratedActions,
    synthetic: Option<&SyntheticGlobals>,
    scope: HashSet<String>,
    context: Context,
) -> Result<(), TypeError> {
    let mut effects = RuleFrontendEffects {
        type_info,
        symbol_gen,
        scope,
        expr_outputs: HashMap::default(),
        action_outputs: HashMap::default(),
        synthetic,
        query_context: Context::Read,
        action_context: context,
    };
    // Lower the complete block, build every candidate constraint in source
    // order, then surface deferred solver diagnostics.
    for action in &actions.0 {
        effects.lower_action(action)?;
    }
    for action in &actions.0 {
        effects.validate_action_candidates(action)?;
    }
    for action in &actions.0 {
        effects.resolve_action_diagnostics(action)?;
    }
    Ok(())
}

fn replay_generated_expr_effects(
    type_info: &TypeInfo,
    symbol_gen: &mut SymbolGen,
    expr: &GeneratedExpr,
    synthetic: Option<&SyntheticGlobals>,
    scope: HashSet<String>,
    context: Context,
) -> Result<(), TypeError> {
    let mut effects = RuleFrontendEffects {
        type_info,
        symbol_gen,
        scope,
        expr_outputs: HashMap::default(),
        action_outputs: HashMap::default(),
        synthetic,
        query_context: Context::Read,
        action_context: context,
    };
    effects.lower_action_expr(expr)?;
    effects.validate_action_expr_candidates(expr)?;
    effects.resolve_action_expr_diagnostics(expr)
}

fn replay_direct_facts_frontend_effects(
    egraph: &mut EGraph,
    facts: &[GeneratedFact],
    synthetic: Option<&SyntheticGlobals>,
) -> Result<(), TypeError> {
    let mut effects = RuleFrontendEffects {
        type_info: &egraph.type_info,
        symbol_gen: &mut egraph.parser.symbol_gen,
        scope: HashSet::default(),
        expr_outputs: HashMap::default(),
        action_outputs: HashMap::default(),
        synthetic,
        query_context: Context::Read,
        action_context: Context::Full,
    };
    for fact in facts {
        effects.lower_query_fact(fact);
    }
    visit_query_binding_vars(facts, &mut |_, variable| {
        effects.observe_query_binding(variable);
        Ok::<(), TypeError>(())
    })?;
    for fact in facts {
        effects.validate_query_fact_candidates(fact)?;
    }
    for fact in facts {
        effects.resolve_query_fact_diagnostics(fact)?;
    }
    Ok(())
}

fn replay_direct_schedule_frontend_effects(
    egraph: &mut EGraph,
    schedule: &GeneratedSchedule,
    synthetic: Option<&SyntheticGlobals>,
) -> Result<(), TypeError> {
    match schedule {
        GenericSchedule::Saturate(_, schedule) | GenericSchedule::Repeat(_, _, schedule) => {
            replay_direct_schedule_frontend_effects(egraph, schedule, synthetic)
        }
        GenericSchedule::Sequence(_, schedules) => {
            for schedule in schedules {
                replay_direct_schedule_frontend_effects(egraph, schedule, synthetic)?;
            }
            Ok(())
        }
        GenericSchedule::Run(_, config) => match &config.until {
            Some(facts) => replay_direct_facts_frontend_effects(egraph, facts, synthetic),
            None => Ok(()),
        },
    }
}

/// Bind portable typed expressions through exact cached call/sort resolution,
/// the current lexical scope, and the command's explicit global policy.
struct ExpressionBinder<'a> {
    type_info: &'a TypeInfo,
    state: &'a mut BindingState,
    globals: GlobalBinding<'a>,
}

impl ExpressionBinder<'_> {
    fn bind_global_variable(
        &self,
        span: Span,
        variable: GeneratedVar,
        global: &ArcSort,
    ) -> Result<ResolvedExpr, GeneratedBindError> {
        if !variable.sort.matches_sort(global) {
            return Err(GeneratedBindError::ShapeMismatch {
                expected: variable.sort.name,
                actual: global.name().to_owned(),
                span,
            });
        }
        match self.globals {
            GlobalBinding::Nullary { .. } => Ok(GenericExpr::Call(
                span,
                ResolvedCall::global_ref(variable.name, global.clone()),
                vec![],
            )),
            GlobalBinding::MustAlreadyBeRemoved => Err(GeneratedBindError::UnexpectedRuleGlobal {
                name: variable.name,
                span,
            }),
        }
    }

    fn bind_variable(
        &mut self,
        span: &Span,
        variable: GeneratedVar,
        scope: &LocalScope,
    ) -> Result<ResolvedVar, GeneratedBindError> {
        if let Some(resolved) = scope.by_id.get(&variable.id) {
            if resolved.name != variable.name
                || !variable.sort.matches_sort(&resolved.sort)
                || resolved.is_global_ref
                || scope.roles_by_id.get(&variable.id) != Some(&variable.role)
            {
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
        visit_query_binding_vars(facts, &mut |span, variable| {
            if variable.role == GeneratedVarRole::Global {
                let Some(global) = self.type_info.get_global_sort(&variable.name) else {
                    return Err(GeneratedBindError::UndeclaredLocal {
                        id: variable.id.0,
                        name: variable.name.clone(),
                        span: span.clone(),
                    });
                };
                if !variable.sort.matches_sort(global) {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: variable.sort.name.clone(),
                        actual: global.name().to_owned(),
                        span: span.clone(),
                    });
                }
                return match self.globals {
                    GlobalBinding::Nullary { .. } => Ok(()),
                    GlobalBinding::MustAlreadyBeRemoved => {
                        Err(GeneratedBindError::UnexpectedRuleGlobal {
                            name: variable.name.clone(),
                            span: span.clone(),
                        })
                    }
                };
            }
            if let Some(existing) = scope.by_id.get(&variable.id) {
                if existing.name != variable.name
                    || !variable.sort.matches_sort(&existing.sort)
                    || existing.is_global_ref
                    || scope.roles_by_id.get(&variable.id) != Some(&variable.role)
                {
                    return Err(GeneratedBindError::InconsistentLocalId {
                        id: variable.id.0,
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
        Ok(scope)
    }

    fn prepare_merge_scope(
        &mut self,
        actions: &GeneratedActions,
        output: &ValueShape,
    ) -> Result<LocalScope, GeneratedBindError> {
        let canonical: HashMap<String, SortKey> = match output {
            ValueShape::Scalar(sort) => [
                ("old".to_owned(), sort.clone()),
                ("new".to_owned(), sort.clone()),
            ]
            .into_iter()
            .collect(),
            ValueShape::Tuple(sorts) => (0..sorts.len())
                .flat_map(|index| {
                    [
                        (format!("old{index}"), sorts[index].clone()),
                        (format!("new{index}"), sorts[index].clone()),
                    ]
                })
                .collect(),
        };
        let mut scope = LocalScope::default();
        let mut observe = |span: &Span, variable: &GeneratedVar| {
            if variable.role == GeneratedVarRole::Global {
                return Ok(());
            }
            let Some(expected) = canonical.get(&variable.name) else {
                return Ok(());
            };
            if expected != &variable.sort {
                return Err(GeneratedBindError::InvalidMergeVariable {
                    name: variable.name.clone(),
                    span: span.clone(),
                });
            }
            if let Some(existing) = scope.by_id.get(&variable.id) {
                if existing.name != variable.name
                    || !variable.sort.matches_sort(&existing.sort)
                    || existing.is_global_ref
                    || scope.roles_by_id.get(&variable.id) != Some(&variable.role)
                {
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
        for action in &actions.0 {
            visit_action_vars(action, &mut observe)?;
        }
        Ok(scope)
    }

    /// Extend an already action-bound merge scope only when the result phase
    /// begins. This prevents a malformed later result ID from preempting an
    /// earlier action type or binding error.
    fn observe_merge_result_scope(
        &mut self,
        result: &GeneratedExpr,
        output: &ValueShape,
        scope: &mut LocalScope,
    ) -> Result<(), GeneratedBindError> {
        let canonical: HashMap<String, SortKey> = match output {
            ValueShape::Scalar(sort) => [
                ("old".to_owned(), sort.clone()),
                ("new".to_owned(), sort.clone()),
            ]
            .into_iter()
            .collect(),
            ValueShape::Tuple(sorts) => (0..sorts.len())
                .flat_map(|index| {
                    [
                        (format!("old{index}"), sorts[index].clone()),
                        (format!("new{index}"), sorts[index].clone()),
                    ]
                })
                .collect(),
        };
        visit_expr_vars(result, &mut |span, variable| {
            if variable.role == GeneratedVarRole::Global {
                return Ok(());
            }
            let Some(expected) = canonical.get(&variable.name) else {
                return Ok(());
            };
            if expected != &variable.sort {
                return Err(GeneratedBindError::InvalidMergeVariable {
                    name: variable.name.clone(),
                    span: span.clone(),
                });
            }
            if let Some(existing) = scope.by_id.get(&variable.id) {
                if existing.name != variable.name
                    || !variable.sort.matches_sort(&existing.sort)
                    || existing.is_global_ref
                    || scope.roles_by_id.get(&variable.id) != Some(&variable.role)
                {
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
        })
    }

    fn bind_expr(
        &mut self,
        expr: GeneratedExpr,
        scope: &LocalScope,
        context: Context,
    ) -> Result<ResolvedExpr, GeneratedBindError> {
        match expr {
            GenericExpr::Var(span, variable) => {
                let synthetic = match self.globals {
                    GlobalBinding::Nullary { synthetic } => {
                        synthetic.and_then(|globals| globals.get(&variable.id))
                    }
                    GlobalBinding::MustAlreadyBeRemoved => None,
                };
                if let Some(synthetic) = synthetic {
                    if synthetic.variable.name != variable.name
                        || synthetic.variable.sort != variable.sort
                        || synthetic.variable.role != variable.role
                        || !variable.sort.matches_sort(&synthetic.sort)
                    {
                        return Err(GeneratedBindError::InconsistentLocalId {
                            id: variable.id.0,
                            span,
                        });
                    }
                    return Ok(GenericExpr::Call(span, synthetic.call.clone(), vec![]));
                }
                match variable.role {
                    GeneratedVarRole::Global => {
                        let Some(global) = self.type_info.get_global_sort(&variable.name) else {
                            return Err(GeneratedBindError::UndeclaredLocal {
                                id: variable.id.0,
                                name: variable.name,
                                span,
                            });
                        };
                        self.bind_global_variable(span, variable, global)
                    }
                    GeneratedVarRole::Local => {
                        let resolved = self.bind_variable(&span, variable, scope)?;
                        Ok(GenericExpr::Var(span, resolved))
                    }
                }
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
        let inputs = match key {
            CallKey::Function(function) => &function.inputs,
            CallKey::Primitive(primitive) => &primitive.inputs,
            CallKey::Values(sorts) => {
                if sorts.len() < 2 {
                    return Err(GeneratedBindError::InvalidTupleArity {
                        actual: sorts.len(),
                        span: span.clone(),
                    });
                }
                sorts
            }
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
            let actual = ResolvedValueShape::from_expr(&arg);
            if !matches!(&actual, ResolvedValueShape::Scalar(sort) if expected.matches_sort(sort)) {
                return Err(GeneratedBindError::ShapeMismatch {
                    expected: expected.name.clone(),
                    actual: actual.stable_name(),
                    span: span.clone(),
                });
            }
            resolved_args.push(arg);
        }
        let call = self
            .state
            .resolve_call(self.type_info, key, context, span)?;
        Ok((call, resolved_args))
    }

    fn require_scalar_sort(
        expr: &ResolvedExpr,
        expected: &str,
        span: &Span,
    ) -> Result<ArcSort, GeneratedBindError> {
        match ResolvedValueShape::from_expr(expr) {
            ResolvedValueShape::Scalar(sort) => Ok(sort),
            actual @ ResolvedValueShape::Tuple(_) => Err(GeneratedBindError::ShapeMismatch {
                expected: expected.to_owned(),
                actual: actual.stable_name(),
                span: span.clone(),
            }),
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
                let left_shape = ResolvedValueShape::from_expr(&left);
                let right_shape = ResolvedValueShape::from_expr(&right);
                if !left_shape.same_as(&right_shape) {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: left_shape.stable_name(),
                        actual: right_shape.stable_name(),
                        span: span.clone(),
                    });
                }
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
                if variable.role != GeneratedVarRole::Local {
                    return Err(GeneratedBindError::InternalInvariant {
                        message: "generated let target is not explicitly local",
                        span,
                    });
                }
                if scope.by_id.contains_key(&variable.id)
                    || scope.by_name.contains_key(&variable.name)
                {
                    return Err(GeneratedBindError::DuplicateLocal {
                        name: variable.name,
                        span,
                    });
                }
                let expr = self.bind_expr(expr, scope, context)?;
                let sort = Self::require_scalar_sort(&expr, &variable.sort.name, &span)?;
                if !variable.sort.matches_sort(&sort) {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: variable.sort.name,
                        actual: sort.name().to_owned(),
                        span,
                    });
                }
                let resolved = ResolvedVar {
                    name: variable.name.clone(),
                    sort,
                    is_global_ref: false,
                };
                scope.declare(&variable, resolved.clone(), &span)?;
                Ok(GenericAction::Let(span, resolved, expr))
            }
            GenericAction::Set(span, head, args, value) => {
                let function = match &head {
                    CallKey::Function(function) => function,
                    CallKey::Primitive(_) => {
                        return Err(GeneratedBindError::WrongCallKind {
                            head: head.to_string(),
                            expected: CallKind::Function,
                            actual: CallKind::Primitive,
                            span,
                        });
                    }
                    CallKey::Values(_) => {
                        return Err(GeneratedBindError::WrongCallKind {
                            head: head.to_string(),
                            expected: CallKind::Function,
                            actual: CallKind::Values,
                            span,
                        });
                    }
                };
                if function.subtype == FunctionSubtype::Constructor {
                    return Err(
                        TypeError::SetConstructorDisallowed(function.name.clone(), span).into(),
                    );
                }
                let (call, args) =
                    self.bind_call_application(&span, &head, args, scope, context)?;
                let value = self.bind_expr(value, scope, context)?;
                let actual = ResolvedValueShape::from_expr(&value);
                if !actual.matches(&function.output) {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: function.output.stable_name(),
                        actual: actual.stable_name(),
                        span,
                    });
                }
                Ok(GenericAction::Set(span, call, args, value))
            }
            GenericAction::Change(span, change, head, args) => {
                match &head {
                    CallKey::Function(_) => {}
                    CallKey::Primitive(_) => {
                        return Err(GeneratedBindError::WrongCallKind {
                            head: head.to_string(),
                            expected: CallKind::Function,
                            actual: CallKind::Primitive,
                            span,
                        });
                    }
                    CallKey::Values(_) => {
                        return Err(GeneratedBindError::WrongCallKind {
                            head: head.to_string(),
                            expected: CallKind::Function,
                            actual: CallKind::Values,
                            span,
                        });
                    }
                }
                let (call, args) =
                    self.bind_call_application(&span, &head, args, scope, context)?;
                Ok(GenericAction::Change(span, change, call, args))
            }
            GenericAction::Union(span, left, right) => {
                let left = self.bind_expr(left, scope, context)?;
                let right = self.bind_expr(right, scope, context)?;
                let left_shape = ResolvedValueShape::from_expr(&left);
                let right_shape = ResolvedValueShape::from_expr(&right);
                if !left_shape.same_as(&right_shape) {
                    return Err(GeneratedBindError::ShapeMismatch {
                        expected: left_shape.stable_name(),
                        actual: right_shape.stable_name(),
                        span,
                    });
                }
                let sort = Self::require_scalar_sort(&left, "scalar union value", &span)?;
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
                Self::require_scalar_sort(&expr, "scalar action expression", &span)?;
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
        let (query_context, action_context) = rule_call_contexts(global_seminaive, &rule.eval_mode);
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
        if decl.key.name.is_empty() {
            return Err(TypeError::UndefinedSort(decl.key.name, decl.span).into());
        }
        let presort_and_args = decl
            .presort
            .as_ref()
            .map(|presort| presort.source_payload(&decl.span));
        let sort = self.egraph.prepare_sort_declaration(
            decl.key.name.clone(),
            &presort_and_args,
            &decl.span,
        )?;
        if let Some(presort) = &decl.presort {
            for expected in presort.args.iter().flat_map(|arg| match arg {
                GeneratedPresortArg::Sort(sort) => std::slice::from_ref(sort),
                GeneratedPresortArg::SortList(sorts) => sorts.as_slice(),
            }) {
                let actual = self
                    .egraph
                    .type_info()
                    .get_sort_by_name(&expected.name)
                    .ok_or_else(|| {
                        TypeError::UndefinedSort(expected.name.clone(), decl.span.clone())
                    })?;
                if !expected.matches_sort(actual) {
                    let actual = if actual.is_eq_container_sort() {
                        SortSemanticClass::EqContainer
                    } else if actual.is_eq_sort() {
                        SortSemanticClass::Eq
                    } else {
                        SortSemanticClass::Value
                    };
                    return Err(GeneratedBindError::SortClassMismatch {
                        name: expected.name.clone(),
                        expected: expected.class,
                        actual,
                        span: decl.span,
                    });
                }
            }
        }
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
        Ok(ResolvedNCommand::Sort {
            span: decl.span,
            name: decl.key.name,
            presort_and_args,
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
        let CallKey::Function(key) = &decl.resolved_schema else {
            return Err(GeneratedBindError::FunctionMetadataMismatch {
                name: decl.name,
                span: decl.span,
            });
        };
        let key = key.clone();
        if let ValueShape::Tuple(sorts) = &key.output
            && sorts.len() < 2
        {
            return Err(GeneratedBindError::InvalidTupleArity {
                actual: sorts.len(),
                span: decl.span,
            });
        }
        let source = Self::source_function_metadata(&decl);
        let ftype = self.egraph.type_info().prepare_function_type(&source)?;
        if function_key(&ftype) != key
            || (decl.subtype == FunctionSubtype::Constructor && decl.merge.is_some())
        {
            return Err(GeneratedBindError::FunctionMetadataMismatch {
                name: decl.name,
                span: decl.span,
            });
        }
        let generated_merge = decl.merge;
        let state = &mut self.state;
        let egraph = &mut *self.egraph;
        let symbol_gen = &mut egraph.parser.symbol_gen;
        let symbol_gen_checkpoint = generated_merge.as_ref().map(|_| symbol_gen.checkpoint());
        let outputs = ftype.outputs.clone();
        let merge_result =
            egraph
                .type_info
                .bind_with_provisional_function(ftype.clone(), |type_info| {
                    let Some(generated_merge) = generated_merge else {
                        return Ok::<_, GeneratedBindError>(None);
                    };
                    let tuple_var_names: Vec<(String, String)> = (0..outputs.len())
                        .map(|index| (format!("old{index}"), format!("new{index}")))
                        .collect();
                    let mut merge_bound_names = HashSet::default();
                    if matches!(&key.output, ValueShape::Tuple(_)) {
                        for (old, new) in &tuple_var_names {
                            merge_bound_names.insert(old.clone());
                            merge_bound_names.insert(new.clone());
                        }
                    } else {
                        merge_bound_names.insert("old".to_owned());
                        merge_bound_names.insert("new".to_owned());
                    }
                    replay_generated_actions_effects(
                        type_info,
                        symbol_gen,
                        &generated_merge.actions,
                        None,
                        merge_bound_names.clone(),
                        Context::Write,
                    )?;
                    let mut binder = ExpressionBinder {
                        type_info,
                        state,
                        globals: GlobalBinding::Nullary { synthetic: None },
                    };
                    let mut scope =
                        binder.prepare_merge_scope(&generated_merge.actions, &key.output)?;
                    let actions = binder.bind_actions(
                        generated_merge.actions.clone(),
                        &mut scope,
                        Context::Write,
                    )?;

                    let result = match &key.output {
                        ValueShape::Scalar(_) => {
                            replay_generated_expr_effects(
                                type_info,
                                symbol_gen,
                                &generated_merge.result,
                                None,
                                scope
                                    .by_name
                                    .keys()
                                    .cloned()
                                    .chain(merge_bound_names.iter().cloned())
                                    .collect(),
                                Context::Write,
                            )?;
                            binder.observe_merge_result_scope(
                                &generated_merge.result,
                                &key.output,
                                &mut scope,
                            )?;
                            binder.bind_expr(generated_merge.result, &scope, Context::Write)?
                        }
                        ValueShape::Tuple(expected_keys) => {
                            let GenericExpr::Call(result_span, result_head, result_args) =
                                &generated_merge.result
                            else {
                                return Err(TypeError::TupleMergeNotValues(
                                    key.name.clone(),
                                    source.span.clone(),
                                )
                                .into());
                            };
                            let result_head_is_values = match result_head {
                                CallKey::Function(function) => function.name == "values",
                                CallKey::Primitive(primitive) => primitive.name == "values",
                                CallKey::Values(_) => true,
                            };
                            if !result_head_is_values {
                                return Err(TypeError::TupleMergeNotValues(
                                    key.name.clone(),
                                    source.span.clone(),
                                )
                                .into());
                            }
                            if result_args.len() != outputs.len() {
                                return Err(TypeError::TupleMergeArity {
                                    name: key.name.clone(),
                                    expected: outputs.len(),
                                    actual: result_args.len(),
                                    span: source.span.clone(),
                                }
                                .into());
                            }
                            let portable_values_matches = matches!(
                                result_head,
                                CallKey::Values(result_keys) if result_keys == expected_keys
                            );
                            let mut resolved_args = Vec::with_capacity(result_args.len());
                            for (arg, expected) in result_args.iter().zip(&outputs) {
                                replay_generated_expr_effects(
                                    type_info,
                                    symbol_gen,
                                    arg,
                                    None,
                                    scope
                                        .by_name
                                        .keys()
                                        .cloned()
                                        .chain(merge_bound_names.iter().cloned())
                                        .collect(),
                                    Context::Write,
                                )?;
                                binder.observe_merge_result_scope(arg, &key.output, &mut scope)?;
                                let resolved =
                                    binder.bind_expr(arg.clone(), &scope, Context::Write)?;
                                let actual = resolved.output_type();
                                if actual.name() != expected.name() {
                                    let source_arg = arg.clone().map_symbols(
                                        &mut |head| match head {
                                            CallKey::Function(function) => function.name,
                                            CallKey::Primitive(primitive) => primitive.name,
                                            CallKey::Values(_) => "values".to_owned(),
                                        },
                                        &mut |variable| variable.name,
                                    );
                                    return Err(TypeError::Mismatch {
                                        expr: source_arg,
                                        expected: expected.clone(),
                                        actual,
                                    }
                                    .into());
                                }
                                resolved_args.push(resolved);
                            }
                            if !portable_values_matches {
                                return Err(GeneratedBindError::TupleMergeResult {
                                    name: key.name.clone(),
                                    span: source.span.clone(),
                                });
                            }
                            GenericExpr::Call(
                                result_span.clone(),
                                ResolvedCall::Values(outputs.clone()),
                                resolved_args,
                            )
                        }
                    };
                    Ok::<_, GeneratedBindError>(Some(crate::ast::ResolvedMerge { actions, result }))
                });
        let merge = match merge_result {
            Ok(merge) => {
                if let Some(checkpoint) = symbol_gen_checkpoint {
                    symbol_gen.commit(checkpoint);
                }
                merge
            }
            Err(error) => {
                if let Some(checkpoint) = symbol_gen_checkpoint {
                    symbol_gen.rollback(checkpoint);
                }
                // The provisional insertion deliberately does not advance the
                // head generation. A self-reference may therefore have filled
                // this generation's exact-call cache before a later merge
                // error removed the function from TypeInfo.
                state.call_cache.remove(&key.name);
                return Err(error);
            }
        };
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
        Ok(ResolvedNCommand::Function(resolved))
    }

    fn bind_index(
        &mut self,
        decl: GeneratedIndexDecl,
    ) -> Result<ResolvedNCommand, GeneratedBindError> {
        let prepared = self.egraph.prepare_index_declaration(
            &decl.span,
            &decl.name,
            &decl.function.name,
            &decl.any_of,
        )?;
        // Preserve the source frontend's declaration-error order before
        // validating the portable exact signature.
        self.state.resolve_call(
            self.egraph.type_info(),
            &CallKey::Function(decl.function.clone()),
            Context::Read,
            &decl.span,
        )?;
        self.egraph.commit_index_declaration(&decl.span, prepared)?;
        let index_type = self
            .egraph
            .type_info()
            .get_func_type(&decl.name)
            .ok_or_else(|| GeneratedBindError::InternalInvariant {
                message: "a committed index did not expose its function type",
                span: decl.span.clone(),
            })?
            .clone();
        self.state.record_function_receipt(
            self.egraph.type_info(),
            function_key(&index_type),
            ResolvedCall::Func(index_type),
        );
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
    ) -> Result<ResolvedNCommand, GeneratedBindError> {
        let command = match generated {
            GeneratedCommand::Sort(decl) => self.bind_sort(decl)?,
            GeneratedCommand::Function(decl) => self.bind_function(decl)?,
            GeneratedCommand::Index(decl) => self.bind_index(decl)?,
            GeneratedCommand::AddRuleset(span, name) => ResolvedNCommand::AddRuleset(span, name),
            GeneratedCommand::CombinedRuleset(span, name, rulesets) => {
                ResolvedNCommand::UnstableCombinedRuleset(span, name, rulesets)
            }
            GeneratedCommand::Rule(_) => {
                unreachable!("rules use the dedicated generated-rule binding boundary")
            }
            GeneratedCommand::Actions(actions) => {
                let type_info = self.egraph.type_info();
                let mut binder = ExpressionBinder {
                    type_info,
                    state: &mut self.state,
                    globals: GlobalBinding::Nullary { synthetic: None },
                };
                ResolvedNCommand::CoreActions(binder.bind_actions(
                    actions,
                    &mut LocalScope::default(),
                    Context::Full,
                )?)
            }
            GeneratedCommand::Extraction { span, .. } => {
                return Err(GeneratedBindError::InternalInvariant {
                    message: "extraction plan reached ordinary generated-command binding",
                    span,
                });
            }
            GeneratedCommand::Schedule(schedule) => {
                let type_info = self.egraph.type_info();
                let mut binder = ExpressionBinder {
                    type_info,
                    state: &mut self.state,
                    globals: GlobalBinding::Nullary { synthetic: None },
                };
                ResolvedNCommand::RunSchedule(binder.bind_schedule(schedule)?)
            }
            GeneratedCommand::PrintOverallStatistics(span, file) => {
                ResolvedNCommand::PrintOverallStatistics(span, file)
            }
            GeneratedCommand::Check(span, facts) => {
                let type_info = self.egraph.type_info();
                let mut binder = ExpressionBinder {
                    type_info,
                    state: &mut self.state,
                    globals: GlobalBinding::Nullary { synthetic: None },
                };
                ResolvedNCommand::Check(span, binder.bind_query_facts(facts, Context::Read)?)
            }
            GeneratedCommand::PrintFunction(span, name, limit, file, mode) => {
                ResolvedNCommand::PrintFunction(span, name, limit, file, mode)
            }
            GeneratedCommand::ProveExists(span, function) => {
                let call = self.state.resolve_call(
                    self.egraph.type_info(),
                    &CallKey::Function(function),
                    Context::Read,
                    &span,
                )?;
                ResolvedNCommand::ProveExists(span, call)
            }
            GeneratedCommand::PrintSize(span, name) => ResolvedNCommand::PrintSize(span, name),
            GeneratedCommand::Output { span, file, exprs } => {
                let type_info = self.egraph.type_info();
                let mut binder = ExpressionBinder {
                    type_info,
                    state: &mut self.state,
                    globals: GlobalBinding::Nullary { synthetic: None },
                };
                let mut resolved = Vec::with_capacity(exprs.len());
                for expr in exprs {
                    let expr = binder.bind_expr(expr, &LocalScope::default(), Context::Full)?;
                    ExpressionBinder::require_scalar_sort(
                        &expr,
                        "scalar output expression",
                        &span,
                    )?;
                    resolved.push(expr);
                }
                let exprs = resolved;
                ResolvedNCommand::Output { span, file, exprs }
            }
            GeneratedCommand::Push(span, count) => ResolvedNCommand::Push(span, count),
            GeneratedCommand::Pop(span, count) => ResolvedNCommand::Pop(span, count),
            GeneratedCommand::Input { span, name, file } => {
                ResolvedNCommand::Input { span, name, file }
            }
        };
        Ok(command)
    }
}

impl GeneratedBinder<'_> {
    fn bind_direct_rule(
        &mut self,
        rule: GeneratedRule,
    ) -> Result<ResolvedNCommand, GeneratedBindError> {
        let global_seminaive = self.egraph.seminaive;
        let type_info = self.egraph.type_info();
        let mut binder = ExpressionBinder {
            type_info,
            state: &mut self.state,
            globals: GlobalBinding::MustAlreadyBeRemoved,
        };
        let rule = binder.bind_rule(rule, global_seminaive)?;
        Ok(ResolvedNCommand::NormRule { rule })
    }

    /// Run the typed rule boundary. A generated rule never enters source
    /// parsing, desugaring, inference, or global removal; this method owns the
    /// ordered freshness, binding, and prefix-validation contract shared by
    /// top-level and nested entries.
    fn typecheck_direct_rule(
        &mut self,
        rule: GeneratedRule,
    ) -> Result<ResolvedNCommand, EgglogError> {
        let rule_span = rule.span.clone();
        replay_direct_rule_frontend_effects(self.egraph, &rule)?;
        let direct = self.bind_direct_rule(rule)?;
        let ResolvedNCommand::NormRule { rule } = &direct else {
            return Err(GeneratedBindError::InternalInvariant {
                message: "direct rule binding produced a non-rule command",
                span: rule_span,
            }
            .into());
        };
        self.egraph.validate_rule_variable_prefixes(rule)?;
        Ok(direct)
    }

    fn typecheck_direct_extraction(
        &mut self,
        span: Span,
        setup: Vec<GeneratedExtractionStep>,
        rebuild: GeneratedSchedule,
        expr: GeneratedExpr,
        variants: GeneratedExpr,
    ) -> Result<Vec<ResolvedNCommand>, EgglogError> {
        let mut synthetic_globals = SyntheticGlobals::default();
        let mut resolved = Vec::with_capacity(setup.len() * 2 + 2);

        for step in setup {
            match step {
                GeneratedExtractionStep::Scratch(scratch) => {
                    let generated_action = GenericAction::Let(
                        scratch.span.clone(),
                        scratch.variable.clone(),
                        scratch.value.clone(),
                    );
                    let generated_actions = GenericActions(vec![generated_action]);
                    replay_generated_actions_effects(
                        &self.egraph.type_info,
                        &mut self.egraph.parser.symbol_gen,
                        &generated_actions,
                        Some(&synthetic_globals),
                        HashSet::default(),
                        Context::Full,
                    )?;

                    if synthetic_globals.contains_key(&scratch.variable.id)
                        || synthetic_globals
                            .values()
                            .any(|existing| existing.variable.name == scratch.variable.name)
                    {
                        return Err(GeneratedBindError::DuplicateLocal {
                            name: scratch.variable.name,
                            span: scratch.span,
                        }
                        .into());
                    }
                    let value = {
                        let type_info = self.egraph.type_info();
                        let mut binder = ExpressionBinder {
                            type_info,
                            state: &mut self.state,
                            globals: GlobalBinding::Nullary {
                                synthetic: Some(&synthetic_globals),
                            },
                        };
                        binder.bind_expr(scratch.value, &LocalScope::default(), Context::Full)?
                    };
                    let sort = ExpressionBinder::require_scalar_sort(
                        &value,
                        &scratch.variable.sort.name,
                        &scratch.span,
                    )?;
                    if !scratch.variable.sort.matches_sort(&sort) {
                        return Err(GeneratedBindError::ShapeMismatch {
                            expected: scratch.variable.sort.name,
                            actual: sort.name().to_owned(),
                            span: scratch.span,
                        }
                        .into());
                    }
                    // The source extraction setup was a top-level `let` until
                    // global removal. Its successful frontend path performed
                    // the one-shot global-prefix check after validating the
                    // value and before publishing the global sort. Preserve
                    // both that ordering and strict-mode failure boundary.
                    self.egraph
                        .ensure_global_name_prefix(&scratch.span, &scratch.variable.name)?;
                    self.egraph
                        .type_info
                        .register_global_sort(scratch.variable.name.clone(), sort.clone());
                    let function = Arc::new(crate::typechecking::FuncType {
                        name: scratch.variable.name.clone(),
                        subtype: FunctionSubtype::Custom,
                        input: vec![],
                        outputs: vec![sort.clone()],
                    });
                    let call = ResolvedCall::Func(function);
                    resolved.push(ResolvedNCommand::Function(ResolvedFunctionDecl {
                        name: scratch.variable.name.clone(),
                        subtype: FunctionSubtype::Custom,
                        schema: Schema {
                            input: vec![],
                            outputs: vec![sort.name().to_owned()],
                        },
                        resolved_schema: call.clone(),
                        merge: None,
                        cost: None,
                        unextractable: true,
                        internal_hidden: false,
                        internal_let: true,
                        span: scratch.span.clone(),
                        term_constructor: None,
                        identity_vals: None,
                        internal_term_node: false,
                    }));
                    resolved.push(ResolvedNCommand::CoreAction(GenericAction::Set(
                        scratch.span.clone(),
                        call.clone(),
                        vec![],
                        value,
                    )));
                    synthetic_globals.insert(
                        scratch.variable.id,
                        SyntheticGlobal {
                            variable: scratch.variable,
                            sort,
                            call,
                        },
                    );
                }
                GeneratedExtractionStep::Action(GenericAction::Let(span, _, _)) => {
                    return Err(GeneratedBindError::TopLevelLet { span }.into());
                }
                GeneratedExtractionStep::Action(action) => {
                    let generated_actions = GenericActions(vec![action.clone()]);
                    replay_generated_actions_effects(
                        &self.egraph.type_info,
                        &mut self.egraph.parser.symbol_gen,
                        &generated_actions,
                        Some(&synthetic_globals),
                        HashSet::default(),
                        Context::Full,
                    )?;
                    let action = {
                        let type_info = self.egraph.type_info();
                        let mut binder = ExpressionBinder {
                            type_info,
                            state: &mut self.state,
                            globals: GlobalBinding::Nullary {
                                synthetic: Some(&synthetic_globals),
                            },
                        };
                        binder.bind_action(action, &mut LocalScope::default(), Context::Full)?
                    };
                    resolved.push(ResolvedNCommand::CoreAction(action));
                }
            }
        }

        replay_direct_schedule_frontend_effects(self.egraph, &rebuild, Some(&synthetic_globals))?;
        let schedule = {
            let type_info = self.egraph.type_info();
            let mut binder = ExpressionBinder {
                type_info,
                state: &mut self.state,
                globals: GlobalBinding::Nullary {
                    synthetic: Some(&synthetic_globals),
                },
            };
            binder.bind_schedule(rebuild)?
        };
        resolved.push(ResolvedNCommand::RunSchedule(schedule));

        if let GenericExpr::Call(_, CallKey::Function(function), _) = &expr
            && self
                .egraph
                .type_info
                .get_func_type(&function.name)
                .is_some_and(|ftype| ftype.is_tuple_output())
        {
            return Err(TypeError::CannotExtractTupleOutput(function.name.clone(), span).into());
        }

        replay_generated_expr_effects(
            &self.egraph.type_info,
            &mut self.egraph.parser.symbol_gen,
            &expr,
            Some(&synthetic_globals),
            HashSet::default(),
            Context::Full,
        )?;
        let expr = {
            let type_info = self.egraph.type_info();
            let mut binder = ExpressionBinder {
                type_info,
                state: &mut self.state,
                globals: GlobalBinding::Nullary {
                    synthetic: Some(&synthetic_globals),
                },
            };
            let expr = binder.bind_expr(expr, &LocalScope::default(), Context::Full)?;
            let expr_shape = ResolvedValueShape::from_expr(&expr);
            if matches!(expr_shape, ResolvedValueShape::Tuple(_)) {
                return Err(GeneratedBindError::CannotExtractTuple {
                    actual: expr_shape.stable_name(),
                    span,
                }
                .into());
            }
            expr
        };

        replay_generated_expr_effects(
            &self.egraph.type_info,
            &mut self.egraph.parser.symbol_gen,
            &variants,
            Some(&synthetic_globals),
            HashSet::default(),
            Context::Full,
        )?;
        let resolved_variants = {
            let type_info = self.egraph.type_info();
            let mut binder = ExpressionBinder {
                type_info,
                state: &mut self.state,
                globals: GlobalBinding::Nullary {
                    synthetic: Some(&synthetic_globals),
                },
            };
            binder.bind_expr(variants.clone(), &LocalScope::default(), Context::Full)?
        };
        let expected = self
            .egraph
            .type_info
            .get_sort_by_name("i64")
            .expect("the built-in i64 sort is registered")
            .clone();
        let actual = resolved_variants.output_type();
        if actual.name() != expected.name() {
            let source_variants = variants.map_symbols(
                &mut |head| match head {
                    CallKey::Function(function) => function.name,
                    CallKey::Primitive(primitive) => primitive.name,
                    CallKey::Values(_) => "values".to_owned(),
                },
                &mut |variable| variable.name,
            );
            return Err(TypeError::Mismatch {
                expr: source_variants,
                expected,
                actual,
            }
            .into());
        }
        resolved.push(ResolvedNCommand::Extract(span, expr, resolved_variants));
        Ok(resolved)
    }

    fn typecheck_direct_command(
        &mut self,
        generated: GeneratedCommand,
    ) -> Result<Vec<ResolvedNCommand>, EgglogError> {
        let generated = match generated {
            GeneratedCommand::Extraction {
                span,
                setup,
                rebuild,
                expr,
                variants,
            } => {
                return self.typecheck_direct_extraction(span, setup, rebuild, expr, variants);
            }
            generated => generated,
        };
        let mut output_checkpoint = None;
        match &generated {
            GeneratedCommand::Rule(rule) => {
                return self
                    .typecheck_direct_rule(rule.clone())
                    .map(|rule| vec![rule]);
            }
            GeneratedCommand::Actions(actions) => {
                replay_generated_actions_effects(
                    &self.egraph.type_info,
                    &mut self.egraph.parser.symbol_gen,
                    actions,
                    None,
                    HashSet::default(),
                    Context::Full,
                )?;
            }
            GeneratedCommand::Sort(_)
            | GeneratedCommand::Function(_)
            | GeneratedCommand::Index(_)
            | GeneratedCommand::AddRuleset(..)
            | GeneratedCommand::CombinedRuleset(..)
            | GeneratedCommand::PrintOverallStatistics(..)
            | GeneratedCommand::PrintFunction(..)
            | GeneratedCommand::ProveExists(..)
            | GeneratedCommand::PrintSize(..)
            | GeneratedCommand::Push(..)
            | GeneratedCommand::Pop(..)
            | GeneratedCommand::Input { .. } => {}
            GeneratedCommand::Extraction { .. } => {
                unreachable!("extraction plans return before ordinary command binding")
            }
            GeneratedCommand::Schedule(schedule) => {
                replay_direct_schedule_frontend_effects(self.egraph, schedule, None)?;
            }
            GeneratedCommand::Check(_, facts) => {
                replay_direct_facts_frontend_effects(self.egraph, facts, None)?;
            }
            GeneratedCommand::Output { exprs, .. } => {
                let checkpoint = self.egraph.parser.symbol_gen.checkpoint();
                let result = exprs.iter().try_for_each(|expr| {
                    replay_generated_expr_effects(
                        &self.egraph.type_info,
                        &mut self.egraph.parser.symbol_gen,
                        expr,
                        None,
                        HashSet::default(),
                        Context::Full,
                    )
                });
                if let Err(error) = result {
                    self.egraph.parser.symbol_gen.commit(checkpoint);
                    return Err(error.into());
                }
                output_checkpoint = Some(checkpoint);
            }
        }
        let bound = match self.bind_command(generated) {
            Ok(bound) => {
                if let Some(checkpoint) = output_checkpoint {
                    self.egraph.parser.symbol_gen.commit(checkpoint);
                }
                bound
            }
            Err(error) => {
                if let Some(checkpoint) = output_checkpoint {
                    self.egraph.parser.symbol_gen.rollback(checkpoint);
                }
                return Err(error.into());
            }
        };
        Ok(vec![bound])
    }

    /// Bind one declaration and publish its source-role layout only after the
    /// declaration's own TypeInfo transaction has committed. A later sibling
    /// failure deliberately keeps this prefix update, while an error returned
    /// here leaves the receipt unapplied alongside the rolled-back declaration.
    fn typecheck_direct_declaration(
        &mut self,
        entry: TypedDeclarationEntry,
    ) -> Result<Vec<ResolvedNCommand>, EgglogError> {
        let TypedDeclarationEntry {
            command,
            layout_commit,
        } = entry;
        let commands = self.typecheck_direct_command(command)?;
        if let Some(receipt) = layout_commit {
            self.egraph.proof_state.encoded_functions.commit(receipt);
        }
        Ok(commands)
    }

    fn typecheck_entries(
        &mut self,
        entries: Vec<GeneratedEntry>,
    ) -> Result<Vec<ResolvedNCommand>, EgglogError> {
        let mut commands = Vec::with_capacity(entries.len());
        for entry in entries {
            match entry {
                GeneratedEntry::Command(command) => {
                    commands.extend(self.typecheck_direct_command(*command)?);
                }
                GeneratedEntry::Declaration(declaration) => {
                    commands.extend(self.typecheck_direct_declaration(*declaration)?);
                }
                GeneratedEntry::Rule(rule) => commands.push(self.typecheck_direct_rule(rule)?),
                GeneratedEntry::Fail(span, children) => {
                    if children.is_empty() {
                        return Err(EgglogError::DesugarError(
                            span,
                            "the commands inside (fail ...) expand to no commands".to_owned(),
                        ));
                    }
                    let children = self.typecheck_entries(children)?;
                    if children.is_empty() {
                        return Err(EgglogError::DesugarError(
                            span,
                            "the commands inside (fail ...) expand to no commands".to_owned(),
                        ));
                    }
                    commands.push(ResolvedNCommand::Fail(span, children));
                }
            }
        }
        Ok(commands)
    }
}

pub(crate) fn resolve_generated_batch(
    egraph: &mut EGraph,
    batch: GeneratedBatch,
) -> Result<Vec<ResolvedNCommand>, EgglogError> {
    let state = std::mem::take(egraph.extension_state_or_default::<BindingState>());
    let mut binder = GeneratedBinder { egraph, state };
    let result = binder.typecheck_entries(batch.entries);
    let state = std::mem::take(&mut binder.state);
    *binder.egraph.extension_state_or_default::<BindingState>() = state;
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rule_frontend_defers_query_ambiguity_until_after_rhs_candidates() {
        let mut source_egraph = EGraph::default();
        crate::add_primitive!(&mut source_egraph, "!=" = |a: #, b: #| -?> () {
            (a != b).then_some(())
        });
        let mut direct_egraph = source_egraph.clone();
        let mut expected_symbols = source_egraph.parser.symbol_gen.clone();
        let _: String = expected_symbols.fresh("!=");
        let _: String = expected_symbols.fresh("missing");

        let span = crate::span!();
        let source_rule = GenericRule {
            span: span.clone(),
            body: vec![GenericFact::Fact(GenericExpr::Call(
                span.clone(),
                "!=".to_owned(),
                vec![
                    GenericExpr::Var(span.clone(), "x".to_owned()),
                    GenericExpr::Var(span.clone(), "x".to_owned()),
                ],
            ))],
            head: GenericActions(vec![GenericAction::Expr(
                span.clone(),
                GenericExpr::Call(
                    span.clone(),
                    "missing".to_owned(),
                    vec![GenericExpr::Var(span.clone(), "x".to_owned())],
                ),
            )]),
            name: "source-order".to_owned(),
            ruleset: String::new(),
            eval_mode: RuleEvalMode::Seminaive,
            no_decomp: false,
            include_subsumed: false,
        };
        let source_type_info = source_egraph.type_info().clone();
        let source_error = source_type_info
            .typecheck_rule(
                &mut source_egraph.parser.symbol_gen,
                &source_rule,
                source_egraph.seminaive,
            )
            .unwrap_err();

        let i64_key = SortKey {
            name: "i64".to_owned(),
            class: SortSemanticClass::Value,
        };
        let unit_key = SortKey {
            name: "Unit".to_owned(),
            class: SortSemanticClass::Value,
        };
        let x = GeneratedVar {
            id: LocalId(0),
            name: "x".to_owned(),
            sort: i64_key.clone(),
            role: GeneratedVarRole::Local,
        };
        let direct_rule = GenericRule {
            span: span.clone(),
            body: vec![GenericFact::Fact(GenericExpr::Call(
                span.clone(),
                CallKey::Primitive(PrimitiveKey {
                    name: "!=".to_owned(),
                    inputs: vec![i64_key.clone(), i64_key.clone()],
                    output: unit_key.clone(),
                }),
                vec![
                    GenericExpr::Var(span.clone(), x.clone()),
                    GenericExpr::Var(span.clone(), x.clone()),
                ],
            ))],
            head: GenericActions(vec![GenericAction::Expr(
                span.clone(),
                GenericExpr::Call(
                    span.clone(),
                    CallKey::Function(FunctionKey {
                        name: "missing".to_owned(),
                        subtype: FunctionSubtype::Custom,
                        inputs: vec![i64_key],
                        output: ValueShape::Scalar(unit_key),
                    }),
                    vec![GenericExpr::Var(span.clone(), x)],
                ),
            )]),
            name: "direct-order".to_owned(),
            ruleset: String::new(),
            eval_mode: RuleEvalMode::Seminaive,
            no_decomp: false,
            include_subsumed: false,
        };
        let direct_error =
            replay_direct_rule_frontend_effects(&mut direct_egraph, &direct_rule).unwrap_err();

        assert!(matches!(
            source_error,
            TypeError::UnboundFunction(ref name, _) if name == "missing"
        ));
        assert!(matches!(
            direct_error,
            TypeError::UnboundFunction(ref name, _) if name == "missing"
        ));
        assert_eq!(source_egraph.parser.symbol_gen, expected_symbols);
        assert_eq!(direct_egraph.parser.symbol_gen, expected_symbols);
    }

    #[test]
    fn standalone_actions_defer_ambiguity_until_after_all_candidates() {
        let mut source_egraph = EGraph::default();
        crate::add_primitive!(&mut source_egraph, "!=" = |a: #, b: #| -?> () {
            (a != b).then_some(())
        });
        let mut direct_egraph = source_egraph.clone();
        let mut expected_symbols = source_egraph.parser.symbol_gen.clone();
        let _: String = expected_symbols.fresh("!=");
        let _: String = expected_symbols.fresh("missing");

        let span = crate::span!();
        let source_actions = GenericActions(vec![
            GenericAction::Expr(
                span.clone(),
                GenericExpr::Call(
                    span.clone(),
                    "!=".to_owned(),
                    vec![
                        GenericExpr::Lit(span.clone(), Literal::Int(1)),
                        GenericExpr::Lit(span.clone(), Literal::Int(1)),
                    ],
                ),
            ),
            GenericAction::Expr(
                span.clone(),
                GenericExpr::Call(span.clone(), "missing".to_owned(), vec![]),
            ),
        ]);
        let source_type_info = source_egraph.type_info().clone();
        let source_error = source_type_info
            .typecheck_standalone_actions(
                &mut source_egraph.parser.symbol_gen,
                &source_actions,
                &Default::default(),
                Context::Full,
            )
            .unwrap_err();

        let i64_key = SortKey {
            name: "i64".to_owned(),
            class: SortSemanticClass::Value,
        };
        let unit_key = SortKey {
            name: "Unit".to_owned(),
            class: SortSemanticClass::Value,
        };
        let direct_actions = GenericActions(vec![
            GenericAction::Expr(
                span.clone(),
                GenericExpr::Call(
                    span.clone(),
                    CallKey::Primitive(PrimitiveKey {
                        name: "!=".to_owned(),
                        inputs: vec![i64_key.clone(), i64_key],
                        output: unit_key.clone(),
                    }),
                    vec![
                        GenericExpr::Lit(span.clone(), Literal::Int(1)),
                        GenericExpr::Lit(span.clone(), Literal::Int(1)),
                    ],
                ),
            ),
            GenericAction::Expr(
                span.clone(),
                GenericExpr::Call(
                    span.clone(),
                    CallKey::Function(FunctionKey {
                        name: "missing".to_owned(),
                        subtype: FunctionSubtype::Custom,
                        inputs: vec![],
                        output: ValueShape::Scalar(unit_key),
                    }),
                    vec![],
                ),
            ),
        ]);
        let direct_error = replay_generated_actions_effects(
            &direct_egraph.type_info,
            &mut direct_egraph.parser.symbol_gen,
            &direct_actions,
            None,
            HashSet::default(),
            Context::Full,
        )
        .unwrap_err();

        assert!(matches!(
            source_error,
            TypeError::UnboundFunction(ref name, _) if name == "missing"
        ));
        assert!(matches!(
            direct_error,
            TypeError::UnboundFunction(ref name, _) if name == "missing"
        ));
        assert_eq!(source_egraph.parser.symbol_gen, expected_symbols);
        assert_eq!(direct_egraph.parser.symbol_gen, expected_symbols);
    }
}
