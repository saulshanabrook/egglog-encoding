//! Typed-command foundation for generated proof instrumentation.
//!
//! Proof instrumentation constructs portable typed nodes and binds them once,
//! directly into the destination e-graph universe. Generated commands never
//! re-enter the source parser, desugarer, or general-purpose typechecker.

use std::fmt::{Display, Formatter};
use std::marker::PhantomData;
use std::sync::Arc;

use enum_map::EnumMap;
use thiserror::Error;

use crate::ast::{
    Change, ContainerRebuildSpec, Expr, FunctionDecl, FunctionSubtype, GenericAction,
    GenericActions, GenericExpr, GenericFact, GenericFunctionDecl, GenericMerge, GenericRule,
    GenericSchedule, Literal, PrintFunctionMode, ProofConstructorNames, ResolvedAction,
    ResolvedActions, ResolvedExpr, ResolvedFact, ResolvedFunctionDecl, ResolvedNCommand,
    ResolvedRule, ResolvedRunConfig, ResolvedSchedule, RuleEvalMode, Schema, Span,
};
use crate::core::ResolvedCall;
use crate::proofs::proof_encoding::declaration_direct::TypedDeclarationEntry;
use crate::typechecking::{SortDeclarationMetadata, TypeError, TypeInfo};
use crate::util::{HashMap, HashSet};
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

/// Construction boundary for generated rules.
///
/// Producers supply semantic signatures and variable names; this emitter owns
/// their canonical catalog registration, one lexical local-ID namespace, the
/// default generated span, and head-action order. Any failure here is a bug in
/// a generated-code producer rather than a source-program diagnostic, so the
/// boundary deliberately converts [`GeneratedBindError`] into one panic.
struct GeneratedSemanticEmitter<'a> {
    catalog: &'a mut GeneratedSignatureCatalog,
    span: Span,
    variables: GeneratedRuleBuilder,
    head: Vec<GeneratedAction>,
}

impl<'a> GeneratedSemanticEmitter<'a> {
    fn new(catalog: &'a mut GeneratedSignatureCatalog, span: &Span) -> Self {
        Self {
            catalog,
            span: span.clone(),
            variables: GeneratedRuleBuilder::default(),
            head: Vec::new(),
        }
    }

    fn producer_value<T>(result: Result<T, GeneratedBindError>) -> T {
        result.unwrap_or_else(|error| panic!("invalid generated semantic emission: {error}"))
    }

    fn sort(&mut self, key: SortKey) -> SortKey {
        Self::producer_value(self.catalog.register_sort(key, &self.span))
    }

    fn local(&mut self, name: impl Into<String>, sort: SortKey) -> GeneratedVar {
        Self::producer_value(self.variables.variable(
            name,
            sort,
            GeneratedVarRole::Local,
            &self.span,
        ))
    }

    fn set(&mut self, function: CallKey, args: Vec<GeneratedExpr>, value: GeneratedExpr) {
        self.head
            .push(GenericAction::Set(self.span.clone(), function, args, value));
    }

    fn change(&mut self, change: Change, function: CallKey, args: Vec<GeneratedExpr>) {
        self.head.push(GenericAction::Change(
            self.span.clone(),
            change,
            function,
            args,
        ));
    }

    fn finish_rule(
        self,
        body: Vec<GeneratedFact>,
        name: String,
        ruleset: String,
        eval_mode: RuleEvalMode,
        include_subsumed: bool,
    ) -> GeneratedRule {
        GenericRule {
            span: self.span,
            body,
            head: GenericActions(self.head),
            name,
            ruleset,
            eval_mode,
            no_decomp: false,
            include_subsumed,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Branded<'id, Kind>(usize, PhantomData<(fn(&'id ()) -> &'id (), Kind)>);

macro_rules! branded_refs {
    ($($name:ident => $tag:ident),+ $(,)?) => {$(
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub(super) struct $tag;
        pub(super) type $name<'id> = Branded<'id, $tag>;
    )+};
}
branded_refs!(
    SortRef => SortTag, FunctionRef => FunctionTag, PrimitiveRef => PrimitiveTag,
    ValuesRef => ValuesTag, ExprRef => ExprTag
);

pub(super) trait CallTag: Copy {}
impl CallTag for FunctionTag {}
impl CallTag for PrimitiveTag {}
impl CallTag for ValuesTag {}

enum ExprNode {
    Var(GeneratedVar),
    Lit(Literal),
    Call(usize, Vec<usize>),
}

pub(super) struct RuleMode;

pub(super) struct MergeMode {
    expected: [SortKey; 2],
    inputs_declared: bool,
}

pub(super) trait CheckedMode {
    fn check_action(&self, _: &str, _: &Span) {}
}

impl CheckedMode for RuleMode {}

impl CheckedMode for MergeMode {
    fn check_action(&self, name: &str, span: &Span) {
        assert!(
            self.inputs_declared
                && (name.is_empty() || !matches!(name, "old0" | "old1" | "new0" | "new1")),
            "invalid generated semantic emission: invalid checked merge action at {span}"
        );
    }
}

/// Closure-scoped adapter from branded append-only IDs to the current AST.
/// Handle creation registers signatures; the boundary materializes the result.
pub(super) struct CheckedBuilder<'catalog, 'id, Mode> {
    emitter: GeneratedSemanticEmitter<'catalog>,
    sorts: Vec<SortKey>,
    calls: Vec<CallKey>,
    expressions: Vec<ExprNode>,
    body: Vec<GeneratedFact>,
    mode: Mode,
    brand: PhantomData<fn(&'id ()) -> &'id ()>,
}

pub(super) type CheckedRuleBuilder<'catalog, 'id> = CheckedBuilder<'catalog, 'id, RuleMode>;
pub(super) type CheckedMergeBuilder<'catalog, 'id> = CheckedBuilder<'catalog, 'id, MergeMode>;

impl<'catalog, 'id, Mode: CheckedMode> CheckedBuilder<'catalog, 'id, Mode> {
    fn new(catalog: &'catalog mut GeneratedSignatureCatalog, span: &Span, mode: Mode) -> Self {
        Self {
            emitter: GeneratedSemanticEmitter::new(catalog, span),
            sorts: Vec::new(),
            calls: Vec::new(),
            expressions: Vec::new(),
            body: Vec::new(),
            mode,
            brand: PhantomData,
        }
    }

    fn check_shape(&self, actual: &ValueShape, expected: &ValueShape) {
        assert_eq!(
            actual, expected,
            "invalid generated semantic emission: shape mismatch at {}",
            self.emitter.span
        );
    }

    fn register_call<Tag>(&mut self, key: CallKey) -> Branded<'id, Tag> {
        GeneratedSemanticEmitter::producer_value(
            self.emitter
                .catalog
                .register_call_key(&key, &self.emitter.span),
        );
        let id = self.calls.len();
        self.calls.push(key);
        Branded(id, PhantomData)
    }

    fn push_expr(&mut self, node: ExprNode) -> ExprRef<'id> {
        let id = self.expressions.len();
        self.expressions.push(node);
        Branded(id, PhantomData)
    }

    fn expression_shape(&self, expression: usize) -> ValueShape {
        match &self.expressions[expression] {
            ExprNode::Var(variable) => ValueShape::Scalar(variable.sort.clone()),
            ExprNode::Lit(literal) => {
                ValueShape::Scalar(SortKey::from_sort(&crate::sort::literal_sort(literal)))
            }
            ExprNode::Call(call, _) => match &self.calls[*call] {
                CallKey::Function(function) => function.output.clone(),
                CallKey::Primitive(primitive) => ValueShape::Scalar(primitive.output.clone()),
                CallKey::Values(sorts) => ValueShape::Tuple(sorts.clone()),
            },
        }
    }

    fn checked_args<Call: CallTag>(
        &self,
        call: Branded<'id, Call>,
        args: impl AsRef<[ExprRef<'id>]>,
    ) -> Vec<usize> {
        let args = args.as_ref().iter().map(|arg| arg.0).collect::<Vec<_>>();
        let inputs = match &self.calls[call.0] {
            CallKey::Function(function) => &function.inputs,
            CallKey::Primitive(primitive) => &primitive.inputs,
            CallKey::Values(sorts) => sorts,
        };
        assert_eq!(
            args.len(),
            inputs.len(),
            "invalid generated semantic emission: wrong arity at {}",
            self.emitter.span
        );
        for (expected, arg) in inputs.iter().zip(args.iter().copied()) {
            let actual = self.expression_shape(arg);
            self.check_shape(&actual, &ValueShape::Scalar(expected.clone()));
        }
        args
    }

    pub(super) fn sort(&mut self, key: SortKey) -> SortRef<'id> {
        let key = self.emitter.sort(key);
        let id = self.sorts.len();
        self.sorts.push(key);
        Branded(id, PhantomData)
    }

    pub(super) fn values(&mut self, sorts: impl AsRef<[SortRef<'id>]>) -> ValuesRef<'id> {
        let sorts = sorts
            .as_ref()
            .iter()
            .map(|sort| self.sorts[sort.0].clone())
            .collect::<Vec<_>>();
        self.register_call(CallKey::Values(sorts))
    }

    pub(super) fn function(&mut self, key: FunctionKey) -> FunctionRef<'id> {
        self.register_call(CallKey::Function(key))
    }

    pub(super) fn primitive(
        &mut self,
        name: impl Into<String>,
        inputs: impl AsRef<[SortRef<'id>]>,
        output: SortRef<'id>,
    ) -> PrimitiveRef<'id> {
        let inputs = inputs
            .as_ref()
            .iter()
            .map(|sort| self.sorts[sort.0].clone())
            .collect::<Vec<_>>();
        let output = self.sorts[output.0].clone();
        self.register_call(CallKey::Primitive(PrimitiveKey {
            name: name.into(),
            inputs,
            output,
        }))
    }

    pub(super) fn lit(&mut self, literal: Literal) -> ExprRef<'id> {
        let sort = SortKey::from_sort(&crate::sort::literal_sort(&literal));
        GeneratedSemanticEmitter::producer_value(
            self.emitter.catalog.require_sort(&sort, &self.emitter.span),
        );
        self.push_expr(ExprNode::Lit(literal))
    }

    pub(super) fn apply<Call: CallTag>(
        &mut self,
        call: Branded<'id, Call>,
        args: impl AsRef<[ExprRef<'id>]>,
    ) -> ExprRef<'id> {
        let args = self.checked_args(call, args);
        self.push_expr(ExprNode::Call(call.0, args))
    }

    pub(super) fn bind(&mut self, name: impl Into<String>, value: ExprRef<'id>) -> ExprRef<'id> {
        let shape = self.expression_shape(value.0);
        let ValueShape::Scalar(sort) = shape else {
            panic!(
                "invalid generated semantic emission: cannot bind tuple at {}",
                self.emitter.span,
            );
        };
        let name = name.into();
        self.mode.check_action(&name, &self.emitter.span);
        let next = LocalId(self.emitter.variables.next_local_id);
        let variable = self.emitter.local(name, sort);
        assert_eq!(
            variable.id, next,
            "invalid generated semantic emission: duplicate local `{}` at {}",
            &variable.name, self.emitter.span
        );
        self.emitter.head.push(GenericAction::Let(
            self.emitter.span.clone(),
            variable.clone(),
            self.materialize(value.0),
        ));
        self.push_expr(ExprNode::Var(variable))
    }

    pub(super) fn set(
        &mut self,
        function: FunctionRef<'id>,
        args: impl AsRef<[ExprRef<'id>]>,
        value: ExprRef<'id>,
    ) {
        let CallKey::Function(key) = &self.calls[function.0] else {
            unreachable!("function handle must carry a function")
        };
        if key.subtype == FunctionSubtype::Constructor {
            panic!(
                "invalid generated semantic emission: {}",
                TypeError::SetConstructorDisallowed(key.name.clone(), self.emitter.span.clone())
            );
        }
        let args = self.checked_args(function, args);
        self.check_shape(&self.expression_shape(value.0), &key.output);
        self.mode.check_action("", &self.emitter.span);
        let args = args.into_iter().map(|arg| self.materialize(arg)).collect();
        let value = self.materialize(value.0);
        self.emitter
            .set(self.calls[function.0].clone(), args, value);
    }

    fn materialize(&self, expression: usize) -> GeneratedExpr {
        let span = &self.emitter.span;
        match &self.expressions[expression] {
            ExprNode::Var(variable) => GenericExpr::Var(span.clone(), variable.clone()),
            ExprNode::Lit(literal) => GenericExpr::Lit(span.clone(), literal.clone()),
            ExprNode::Call(call, args) => GenericExpr::Call(
                span.clone(),
                self.calls[*call].clone(),
                args.iter().map(|&arg| self.materialize(arg)).collect(),
            ),
        }
    }
}

impl<'catalog, 'id> CheckedRuleBuilder<'catalog, 'id> {
    pub(super) fn local(&mut self, name: impl Into<String>, sort: SortRef<'id>) -> ExprRef<'id> {
        let variable = self.emitter.local(name, self.sorts[sort.0].clone());
        self.push_expr(ExprNode::Var(variable))
    }

    pub(super) fn change(
        &mut self,
        change: Change,
        function: FunctionRef<'id>,
        args: impl AsRef<[ExprRef<'id>]>,
    ) {
        let args = self.checked_args(function, args);
        let args = args.into_iter().map(|arg| self.materialize(arg)).collect();
        self.emitter
            .change(change, self.calls[function.0].clone(), args);
    }

    pub(super) fn eq(&mut self, left: ExprRef<'id>, right: ExprRef<'id>) {
        let expected = self.expression_shape(left.0);
        self.check_shape(&self.expression_shape(right.0), &expected);
        self.body.push(GenericFact::Eq(
            self.emitter.span.clone(),
            self.materialize(left.0),
            self.materialize(right.0),
        ));
    }

    pub(super) fn fact(&mut self, expr: ExprRef<'id>) {
        self.body.push(GenericFact::Fact(self.materialize(expr.0)));
    }
}

impl<'catalog, 'id> CheckedMergeBuilder<'catalog, 'id> {
    pub(super) fn inputs<const N: usize>(
        &mut self,
        sorts: [SortRef<'id>; N],
    ) -> ([ExprRef<'id>; N], [ExprRef<'id>; N]) {
        assert!(
            !self.mode.inputs_declared
                && N > 0
                && N <= self.mode.expected.len()
                && sorts
                    .iter()
                    .enumerate()
                    .all(|(index, sort)| self.sorts[sort.0] == self.mode.expected[index]),
            "invalid generated semantic emission: invalid merge inputs at {}",
            self.emitter.span
        );
        self.mode.inputs_declared = true;
        let mut make = |names: [&str; 2]| -> [ExprRef<'id>; N] {
            std::array::from_fn(|index| {
                let variable = self
                    .emitter
                    .local(names[index], self.sorts[sorts[index].0].clone());
                self.push_expr(ExprNode::Var(variable))
            })
        };
        (make(["old0", "old1"]), make(["new0", "new1"]))
    }
}

fn validate_rule_scope(body: &[GeneratedFact], head: &[GeneratedAction], span: &Span) {
    let mut bound = Vec::new();
    visit_query_binding_vars(body, &mut |_, variable| {
        let index = variable.id.0 as usize;
        bound.resize(bound.len().max(index + 1), false);
        bound[index] = true;
        Ok::<_, ()>(())
    })
    .unwrap();
    let require = |bound: &[bool], variable: &GeneratedVar| {
        let declared = bound.get(variable.id.0 as usize).copied().unwrap_or(false);
        let name = &variable.name;
        assert!(
            declared,
            "invalid generated semantic emission: undeclared local `{name}` at {span}"
        );
    };
    for fact in body {
        fact.visit_vars(&mut |_, variable| require(&bound, variable));
    }
    for action in head {
        let mut require = |_: &Span, variable: &GeneratedVar| {
            require(&bound, variable);
            Ok(())
        };
        if let GenericAction::Let(_, variable, value) = action {
            visit_expr_vars(value, &mut require).unwrap();
            let index = variable.id.0 as usize;
            let name = &variable.name;
            assert!(
                !bound.get(index).copied().unwrap_or(false),
                "invalid generated semantic emission: duplicate local `{name}` at {span}"
            );
            bound.resize(bound.len().max(index + 1), false);
            bound[index] = true;
        } else {
            visit_action_vars(action, &mut require).unwrap();
        }
    }
}

pub(super) fn build_checked_rule(
    catalog: &mut GeneratedSignatureCatalog,
    span: &Span,
    metadata: (String, String, RuleEvalMode, bool),
    build: impl for<'id> FnOnce(&mut CheckedRuleBuilder<'_, 'id>),
) -> GeneratedRule {
    let mut builder = CheckedBuilder::new(catalog, span, RuleMode);
    build(&mut builder);
    validate_rule_scope(&builder.body, &builder.emitter.head, span);
    let (name, ruleset, eval_mode, include_subsumed) = metadata;
    builder
        .emitter
        .finish_rule(builder.body, name, ruleset, eval_mode, include_subsumed)
}

pub(super) fn build_checked_merge(
    catalog: &mut GeneratedSignatureCatalog,
    span: &Span,
    expected: [SortKey; 2],
    build: impl for<'id> FnOnce(&mut CheckedMergeBuilder<'_, 'id>) -> ExprRef<'id>,
) -> GeneratedMerge {
    let mode = MergeMode {
        expected,
        inputs_declared: false,
    };
    let mut builder = CheckedBuilder::new(catalog, span, mode);
    let result = build(&mut builder);
    assert!(
        builder.mode.inputs_declared
            && matches!(builder.expressions.get(result.0), Some(ExprNode::Call(call, _))
                if matches!(&builder.calls[*call], CallKey::Values(sorts)
                    if sorts == &builder.mode.expected)),
        "invalid generated semantic emission: merge result values at {span}"
    );
    let result = builder.materialize(result.0);
    GenericMerge {
        actions: GenericActions(builder.emitter.head),
        result,
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
        let outputs = ftype.outputs.clone();
        let merge_result =
            egraph
                .type_info
                .bind_with_provisional_function(ftype.clone(), |type_info| {
                    let Some(generated_merge) = generated_merge else {
                        return Ok::<_, GeneratedBindError>(None);
                    };
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
            Ok(merge) => merge,
            Err(error) => {
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
    /// binding and prefix-validation contract shared by top-level and nested
    /// entries. Generated binding does not consume source-parser freshness.
    fn typecheck_direct_rule(
        &mut self,
        rule: GeneratedRule,
    ) -> Result<ResolvedNCommand, EgglogError> {
        let rule_span = rule.span.clone();
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
        match generated {
            GeneratedCommand::Extraction {
                span,
                setup,
                rebuild,
                expr,
                variants,
            } => self.typecheck_direct_extraction(span, setup, rebuild, expr, variants),
            GeneratedCommand::Rule(rule) => self.typecheck_direct_rule(rule).map(|rule| vec![rule]),
            generated => {
                let bound = self.bind_command(generated)?;
                Ok(vec![bound])
            }
        }
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
mod checked_builder_tests {
    use std::panic::{AssertUnwindSafe, catch_unwind};

    use super::*;

    fn assert_rejected<T>(expected: &str, span: &Span, run: impl FnOnce() -> T) {
        let panic = catch_unwind(AssertUnwindSafe(run))
            .map(|_| ())
            .expect_err("invalid checked construction must panic");
        let message = panic
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| panic.downcast_ref::<&str>().copied())
            .expect("checked builder panic must contain text");
        assert!(message.contains(expected), "unexpected panic: {message}");
        assert!(
            message.contains(&span.to_string()),
            "checked builder panic omitted its span: {message}"
        );
    }

    fn rejected(expected: &str, build: impl for<'id> FnOnce(&mut CheckedRuleBuilder<'_, 'id>)) {
        let span = crate::span!();
        let mut catalog = GeneratedSignatureCatalog::default();
        assert_rejected(expected, &span, || {
            build_checked_rule(
                &mut catalog,
                &span,
                (
                    "invalid".to_owned(),
                    "rules".to_owned(),
                    RuleEvalMode::Seminaive,
                    false,
                ),
                build,
            )
        });
    }

    fn rejected_merge(
        expected: &str,
        build: impl for<'id> FnOnce(
            &mut CheckedMergeBuilder<'_, 'id>,
            SortRef<'id>,
            SortRef<'id>,
        ) -> ExprRef<'id>,
    ) {
        let span = crate::span!();
        let mut catalog = GeneratedSignatureCatalog::default();
        let key = SortKey {
            name: "i64".to_owned(),
            class: SortSemanticClass::Value,
        };
        let expected_sorts = [key.clone(), key.clone()];
        assert_rejected(expected, &span, || {
            build_checked_merge(&mut catalog, &span, expected_sorts, move |builder| {
                let sort = builder.sort(key);
                let bool_sort = builder.sort(SortKey {
                    name: "bool".to_owned(),
                    class: SortSemanticClass::Value,
                });
                build(builder, sort, bool_sort)
            })
        });
    }

    #[test]
    fn checked_builder_preserves_generic_action_order_and_local_ids() {
        let span = crate::span!();
        let i64_key = SortKey {
            name: "i64".to_owned(),
            class: SortSemanticClass::Value,
        };
        let function = FunctionKey {
            name: "f".to_owned(),
            subtype: FunctionSubtype::Custom,
            inputs: vec![i64_key.clone()],
            output: ValueShape::Scalar(i64_key.clone()),
        };
        let mut catalog = GeneratedSignatureCatalog::default();
        let rule = build_checked_rule(
            &mut catalog,
            &span,
            (
                "order".to_owned(),
                "rules".to_owned(),
                RuleEvalMode::Seminaive,
                false,
            ),
            move |builder| {
                let i64_sort = builder.sort(i64_key);
                let function = builder.function(function);
                let x = builder.local("x", i64_sort);
                let one = builder.lit(Literal::Int(1));
                builder.eq(x, x);
                builder.set(function, [x], one);
                builder.change(Change::Delete, function, [x]);
            },
        );
        assert!(matches!(
            rule.body.as_slice(),
            [GenericFact::Eq(_, GenericExpr::Var(_, left), GenericExpr::Var(_, right))]
                if left.id == LocalId(0) && right.id == LocalId(0)
        ));
        let [
            GenericAction::Set(set_span, _, set_args, _),
            GenericAction::Change(delete_span, Change::Delete, _, delete_args),
        ] = rule.head.0.as_slice()
        else {
            panic!("generic action order changed: {:?}", rule.head)
        };
        assert_eq!((set_span, delete_span), (&span, &span));
        for args in [set_args, delete_args] {
            let [GenericExpr::Var(expr_span, variable)] = args.as_slice() else {
                panic!("action target must be the original local: {args:?}")
            };
            assert_eq!((expr_span, variable.id), (&span, LocalId(0)));
        }
    }

    #[test]
    fn checked_builder_rejects_arity_sort_shape_set_target_and_duplicate_bind() {
        rejected("wrong arity", |builder| {
            let i64_sort = builder.sort(SortKey {
                name: "i64".to_owned(),
                class: SortSemanticClass::Value,
            });
            let values = builder.values([i64_sort, i64_sort]);
            let x = builder.local("x", i64_sort);
            builder.apply(values, [x]);
        });
        rejected("shape mismatch", |builder| {
            let i64_key = SortKey {
                name: "i64".to_owned(),
                class: SortSemanticClass::Value,
            };
            let i64_sort = builder.sort(i64_key.clone());
            let bool_sort = builder.sort(SortKey {
                name: "bool".to_owned(),
                class: SortSemanticClass::Value,
            });
            let primitive = builder.primitive("identity", [i64_sort], i64_sort);
            let value = builder.local("value", bool_sort);
            builder.apply(primitive, [value]);
        });
        rejected("shape mismatch", |builder| {
            let i64_key = SortKey {
                name: "i64".to_owned(),
                class: SortSemanticClass::Value,
            };
            let i64_sort = builder.sort(i64_key.clone());
            let function = builder.function(FunctionKey {
                name: "scalar".to_owned(),
                subtype: FunctionSubtype::Custom,
                inputs: vec![i64_key.clone()],
                output: ValueShape::Scalar(i64_key),
            });
            let values = builder.values([i64_sort, i64_sort]);
            let x = builder.local("x", i64_sort);
            let tuple = builder.apply(values, [x, x]);
            builder.apply(function, [tuple]);
        });
        rejected("Cannot set constructor", |builder| {
            let i64_key = SortKey {
                name: "i64".to_owned(),
                class: SortSemanticClass::Value,
            };
            let i64_sort = builder.sort(i64_key.clone());
            let constructor = builder.function(FunctionKey {
                name: "Constructor".to_owned(),
                subtype: FunctionSubtype::Constructor,
                inputs: vec![],
                output: ValueShape::Scalar(i64_key),
            });
            let value = builder.local("value", i64_sort);
            builder.set(constructor, [], value);
        });
        rejected("duplicate local", |builder| {
            let i64_sort = builder.sort(SortKey {
                name: "i64".to_owned(),
                class: SortSemanticClass::Value,
            });
            let identity = builder.primitive("identity", [i64_sort], i64_sort);
            let x = builder.local("x", i64_sort);
            builder.eq(x, x);
            let first = builder.apply(identity, [x]);
            builder.bind("bound", first);
            let second = builder.apply(identity, [x]);
            builder.bind("bound", second);
        });
        rejected("undeclared local", |builder| {
            let i64_key = SortKey {
                name: "i64".to_owned(),
                class: SortSemanticClass::Value,
            };
            let i64_sort = builder.sort(i64_key.clone());
            let function = builder.function(FunctionKey {
                name: "f".to_owned(),
                subtype: FunctionSubtype::Custom,
                inputs: vec![i64_key.clone()],
                output: ValueShape::Scalar(i64_key),
            });
            let x = builder.local("x", i64_sort);
            builder.set(function, [x], x);
        });
        rejected("duplicate local", |builder| {
            let i64_sort = builder.sort(SortKey {
                name: "i64".to_owned(),
                class: SortSemanticClass::Value,
            });
            let x = builder.local("x", i64_sort);
            builder.eq(x, x);
            builder.bind("x", x);
        });
    }

    #[test]
    fn checked_builder_rejects_bare_variable_fact() {
        rejected("undeclared local", |builder| {
            let i64_sort = builder.sort(SortKey {
                name: "i64".to_owned(),
                class: SortSemanticClass::Value,
            });
            let x = builder.local("x", i64_sort);
            builder.fact(x);
        });
    }

    #[test]
    fn checked_merge_owns_its_values_result() {
        let span = crate::span!();
        let mut catalog = GeneratedSignatureCatalog::default();
        let key = SortKey {
            name: "i64".to_owned(),
            class: SortSemanticClass::Value,
        };
        let expected = [key.clone(), key.clone()];
        let merge = build_checked_merge(&mut catalog, &span, expected, move |builder| {
            let sort = builder.sort(key);
            let values = builder.values([sort, sort]);
            let ([old], [new]) = builder.inputs([sort]);
            let identity = builder.primitive("identity", [sort], sort);
            let selected = builder.apply(identity, [old]);
            let selected = builder.bind("selected", selected);
            builder.apply(values, [selected, new])
        });
        let [GenericAction::Let(let_span, selected, _)] = merge.actions.0.as_slice() else {
            panic!("checked merge action order changed: {:?}", merge.actions)
        };
        assert_eq!((let_span, selected.id), (&span, LocalId(2)));
        assert!(matches!(
            &merge.result,
            GenericExpr::Call(actual, CallKey::Values(sorts), args)
                if actual == &span && sorts.len() == 2 && args.len() == 2
        ));
    }

    #[test]
    fn checked_merge_rejects_input_bind_and_result_escapes() {
        rejected_merge("merge result values", |builder, _, _| {
            builder.lit(Literal::Int(0))
        });
        rejected_merge("invalid merge inputs", |builder, _, bool_sort| {
            let ([old], _) = builder.inputs([bool_sort]);
            old
        });
        rejected_merge("invalid merge inputs", |builder, sort, _| {
            let ([old], _) = builder.inputs([sort]);
            builder.inputs([sort]);
            old
        });
        rejected_merge("cannot bind tuple", |builder, sort, _| {
            let values = builder.values([sort, sort]);
            let ([old], [new]) = builder.inputs([sort]);
            let tuple = builder.apply(values, [old, new]);
            builder.bind("old1", tuple)
        });
        rejected_merge("invalid checked merge action", |builder, sort, _| {
            let ([old], _) = builder.inputs([sort]);
            builder.bind("old1", old)
        });
        rejected_merge("merge result values", |builder, sort, bool_sort| {
            let values = builder.values([sort, bool_sort]);
            let ([old], _) = builder.inputs([sort]);
            let flag = builder.lit(Literal::Bool(false));
            builder.apply(values, [old, flag])
        });
        rejected_merge("merge result values", |builder, sort, _| {
            let ([old], _) = builder.inputs([sort]);
            old
        });
    }
}
