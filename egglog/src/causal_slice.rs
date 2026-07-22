//! A deliberately narrow dynamic causal slicer for positive relation programs.
//!
//! This module is a feasibility spike, not a general egglog provenance API. It
//! records match-time bindings from one ordinary reference-backend execution,
//! reconstructs exact relation tuples for a monotone fragment, and emits a
//! source program whose only schedule leaves are guarded manual rule batches.

use std::{
    cell::RefCell,
    path::Path,
    sync::Arc,
    time::{Duration, Instant},
};

use thiserror::Error;

use crate::{
    EGraph, Error as EgglogError, TermDag,
    ast::{
        Action, Actions, Command, Expr, Fact, FunctionSubtype, GenericAction, GenericExpr,
        GenericFact, GenericPackedRuleGroup, GenericPackedRunRuleBatch, GenericPackedWitnessNode,
        GenericPackedWitnesses, Literal, PackedRuleFire, ResolvedAction, ResolvedExpr,
        ResolvedExprExt, ResolvedFact, ResolvedNCommand, ResolvedRule, ResolvedVar, Rewrite, Rule,
        RuleEvalMode, Ruleset, RunRuleConfig, Schedule, Span, Subdatatypes,
    },
    core::{
        GenericAtomTerm, GenericCoreAction, ResolvedCall, ResolvedCoreActions, SpecializedPrimitive,
    },
    core_relations::{
        ExternalFunctionId, PrimitiveApplication, RuleExecutionTrace, RuleMatch, TableApplication,
        TableId, TableMutationCause, TableMutationOutcome, TableMutationReceipt, UnionOutcome,
        UnionReceipt, Value,
    },
    literal_to_value,
    util::{HashMap, HashSet, IndexMap, IndexSet},
};

/// The result of one traced ordinary execution and its two replay projections.
#[derive(Clone, Debug)]
pub struct CausalSlice {
    /// The Bronze backward slice rooted at all positive checks.
    pub source: String,
    /// Every captured grounding, useful for separating replay from slicing.
    pub full_transcript_source: String,
    pub stats: CausalSliceStats,
    /// Source-to-registered-rule identities validated during emission.
    pub rule_mapping: Vec<SourceRuleMapping>,
}

/// The retained replay projection from one traced ordinary execution.
///
/// Unlike [`CausalSlice`], this result does not construct the diagnostic full
/// transcript. Production replay uses this form so discarded firings are not
/// rendered and reparsed merely to throw them away.
#[derive(Clone, Debug)]
pub struct CausalReplay {
    pub source: String,
    pub stats: CausalSliceStats,
    pub rule_mapping: Vec<SourceRuleMapping>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ReplaySourceProjection {
    /// Preserve the accepted source envelope for debugging and compatibility.
    Legacy,
    /// Keep only positive-check proof roots and their dynamic/static support.
    PositiveChecks,
}

#[derive(Clone, Debug, Default)]
pub struct CausalSliceStats {
    pub original_bytes: usize,
    pub source_facts: usize,
    pub observation_count: usize,
    pub waves: usize,
    /// Groundings that survived query/action filters and could be elaborated
    /// as replay candidates. The current debug API retains every raw trace
    /// batch through the run; a production tracer should elaborate and
    /// discard them wave by wave.
    pub pending_firings: usize,
    /// Raw match lanes materialized by the native join before query/action
    /// filters and head-effect classification.
    pub matched_applications: usize,
    /// Replayable applications with at least one effective relation,
    /// constructor, equality, or mutable-state effect.
    pub effective_applications: usize,
    pub effective_output_rows: usize,
    /// Replay-eligible pending applications without an effective state change.
    pub no_op_applications: usize,
    /// Persistent fire events, including conservative no-op events promoted
    /// by a Prefix dependency.
    pub promoted_events: usize,
    pub retained_applications: usize,
    /// Unique source-row events. Source commands themselves remain unsliced
    /// in v0.
    pub source_events: usize,
    pub dependency_nodes: usize,
    pub witness_nodes: usize,
    /// Distinct closed witness expressions shared by compact per-wave replay
    /// batches.
    pub shared_replay_witnesses: usize,
    pub equality_edges: usize,
    pub prefix_fallbacks: usize,
    /// Source-variable pairs captured for scheduled rule applications.
    pub captured_bindings: usize,
    pub observation_matches: usize,
    /// Source-variable pairs captured for observation matches.
    pub observation_bindings: usize,
    pub max_batch_matches: usize,
    /// All binding tuples in the low-level native trace, including private
    /// planner variables such as timestamps.
    pub raw_trace_bindings: usize,
    /// A lower bound covering `RuleMatch` headers and binding tuples only; it
    /// excludes Vec capacities and shared string allocations.
    pub raw_trace_lower_bound_bytes: usize,
    /// Parse, declaration collection, deterministic naming, and static model
    /// validation before the native execution begins.
    pub preparation_time: Duration,
    pub traced_run_time: Duration,
    /// Trace summarization, witness metadata collection, and event-arena
    /// elaboration after the native run.
    pub elaboration_time: Duration,
    /// Observation-root construction, backward reachability, and retained
    /// unsupported-prerequisite validation.
    pub slicing_time: Duration,
    /// Source rendering for the requested replay projection(s).
    pub emission_time: Duration,
    /// Parse-and-mapping validation of every emitted program.
    pub emitted_validation_time: Duration,
    /// End-to-end generator time through emitted-source validation and final
    /// counter calculation. The small difference from the named stages is
    /// bookkeeping between stage boundaries.
    pub total_time: Duration,
    /// Diagnostic full-transcript bytes, or zero when only the retained replay
    /// projection was requested.
    pub full_transcript_bytes: usize,
    pub sliced_bytes: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceRuleMapping {
    pub source_command_index: usize,
    pub source_location: String,
    pub original_name: Option<String>,
    pub registered_name: String,
    /// A normalized copy of the complete logical definition and source
    /// planner flags. The registered name and spans are intentionally
    /// excluded.
    pub semantic_definition: String,
}

#[derive(Debug, Error)]
pub enum CausalSliceError {
    #[error(transparent)]
    Egglog(#[from] EgglogError),
    #[error("{location}\ncausal slice v0 does not support {reason}")]
    Unsupported { location: String, reason: String },
    #[error("causal slice v0 invariant failed: {0}")]
    Invariant(String),
}

#[derive(Clone, Debug)]
struct RelationDecl {
    sorts: Vec<String>,
    opaque_sort: Option<String>,
}

#[derive(Clone, Debug)]
struct ConstructorDecl {
    inputs: Vec<String>,
    output: String,
    opaque_sort: Option<String>,
}

#[derive(Clone, Debug)]
struct MutableFunctionDecl {
    inputs: Vec<String>,
    output: String,
    opaque_sort: Option<String>,
    merge: MutableMergeKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MutableMergeKind {
    AssertEq,
    ExactNew,
    BigRatMin,
    BigRatMax,
}

type CollectedDeclarations = (
    IndexMap<String, RelationDecl>,
    IndexMap<String, ConstructorDecl>,
    IndexMap<String, MutableFunctionDecl>,
);

struct ModelDeclarations<'a> {
    relations: &'a IndexMap<String, RelationDecl>,
    constructors: &'a IndexMap<String, ConstructorDecl>,
    mutable_functions: &'a IndexMap<String, MutableFunctionDecl>,
}

struct ResolvedSourceModel {
    rules: IndexMap<String, ResolvedRule>,
    actions: Vec<ResolvedAction>,
    checks: Vec<Vec<ResolvedFact>>,
}

#[derive(Clone, Debug)]
struct AtomTemplate {
    relation: String,
    args: Vec<AtomArg>,
}

#[derive(Clone, Debug)]
enum AtomArg {
    Var(Span, String),
    Global {
        name: String,
        sort: String,
    },
    Lit(Literal),
    App {
        function: String,
        args: Vec<AtomArg>,
        input_sorts: Vec<String>,
        output_sort: String,
        primitive: Option<PrimitiveReplayCapability>,
    },
}

#[derive(Clone, Debug)]
struct RuleModel {
    span: Span,
    body: Vec<AtomTemplate>,
    /// Source body equalities that are neither constructor/function lookups
    /// nor primitive calls. Equal-sort endpoints retain their union causes;
    /// scalar aliases are checked exactly after grounding.
    body_equalities: Vec<EqualityTemplate>,
    body_lookups: Vec<ConstructorLookupTemplate>,
    body_functions: Vec<FunctionLookupTemplate>,
    body_primitives: Vec<QueryPrimitiveTemplate>,
    /// Typed source-local bindings in source action order. These are not
    /// match variables and therefore never appear in replay selectors. The
    /// registered canonical core head remains the operational lowering.
    head_lets: Vec<HeadLetTemplate>,
    head: Vec<AtomTemplate>,
    head_constructors: Vec<AtomArg>,
    head_sets: Vec<FunctionSetTemplate>,
    /// Constructor applications hidden as a complete-head side effect. V0
    /// admits these only when each target exactly aliases a live constructor
    /// lookup in the same body and one independent union promotes the fire.
    head_subsumes: Vec<AtomArg>,
    head_primitives: Vec<AtomArg>,
    head_unions: Vec<EqualityTemplate>,
    var_order: Vec<String>,
    replay_var_order: Vec<String>,
    /// Compiler-generated replay roots that source typing proves are direct
    /// aliases of ordinary match variables. Registration must independently
    /// confirm that both names canonicalize to the same core binding.
    derived_replay_aliases: IndexMap<String, String>,
    var_sorts: IndexMap<String, String>,
    global_uses: IndexMap<String, String>,
    opaque: Option<OpaqueRulePolicy>,
}

#[derive(Clone, Debug)]
struct HeadLetTemplate {
    name: String,
    sort: String,
    value: AtomArg,
}

#[derive(Clone, Debug)]
enum OpaqueRulePolicy {
    /// The rule may execute during tracing, but retaining one of its effects
    /// must surface the original source-located modeling boundary.
    Reject(DeferredUnsupported),
    /// A premise-free rule containing only local constructor lets and
    /// relation/constructor inserts. Its complete head can be replayed with
    /// an empty exact grounding even though the narrow structured model does
    /// not represent head-local variables.
    EmptyBodyInitializer,
    /// A rule whose only head action is `panic`. A completed traced run proves
    /// that no captured pre-filter candidate reached this head, so it has no
    /// replayable state effect and must not become a prefix event.
    UnreachedPanicHead,
    /// This particular otherwise-modeled grounding projected a source
    /// variable before the native action boundary. Its complete modeled head
    /// may be observed for reachability, but replay must fail if retained
    /// because exact premise rows are unavailable.
    ProjectedGrounding(DeferredUnsupported),
    /// This particular otherwise-modeled grounding contains an equality-sort
    /// endpoint for which the ordinary trace has no immutable replay syntax.
    /// Its effects may still be classified for reachability, but retaining the
    /// firing must surface the missing match-time witness.
    UnreplayableGrounding(DeferredUnsupported),
}

#[derive(Clone, Copy, Debug)]
struct RulePrimitiveMeta {
    function: ExternalFunctionId,
    logical_query: bool,
    query_auxiliary: Option<QueryAuxiliaryPrimitive>,
}

#[derive(Clone, Copy, Debug)]
enum QueryAuxiliaryPrimitive {
    BigInt,
    BigRat,
}

#[derive(Clone, Debug, Default)]
struct ResolvedRulePrimitives {
    body: Vec<RulePrimitiveMeta>,
    head: Vec<RulePrimitiveMeta>,
    /// The exact canonical action stream registered in the native backend.
    /// It is the authority for table/primitive instruction interleaving and
    /// compiler-emitted zero-receipt aliases.
    core_head: ResolvedCoreActions,
    /// Exact source-to-canonical aliases produced while lowering the rule.
    /// Query-result source bindings use the inverse variable edge to seed the
    /// canonical head input created by the compiler.
    substitutions: Box<[(ResolvedVar, crate::core::ResolvedAtomTerm)]>,
}

#[derive(Clone, Debug)]
struct CheckModel {
    atoms: Vec<AtomTemplate>,
    equalities: Vec<EqualityTemplate>,
    var_sorts: IndexMap<String, String>,
    global_uses: IndexMap<String, String>,
}

#[derive(Clone, Debug)]
struct EqualityTemplate {
    span: Span,
    left: AtomArg,
    right: AtomArg,
    sort: String,
}

#[derive(Clone, Debug)]
struct ConstructorLookupTemplate {
    span: Span,
    application: AtomArg,
    output: AtomArg,
    sort: String,
}

#[derive(Clone, Debug)]
struct QueryPrimitiveTemplate {
    span: Span,
    application: AtomArg,
    /// `Some` for a logical equality/predicate output and `None` when the
    /// primitive is an intermediate inside a typed body application.
    output: Option<AtomArg>,
    sort: String,
    capability: PrimitiveReplayCapability,
}

#[derive(Clone, Debug)]
struct PrimitiveReplayCapability {
    specialization: SpecializedPrimitive,
}

#[derive(Clone, Debug)]
struct FunctionLookupTemplate {
    span: Span,
    function: String,
    keys: Vec<AtomArg>,
    output: AtomArg,
    input_sorts: Vec<String>,
    output_sort: String,
}

#[derive(Clone, Debug)]
struct FunctionSetTemplate {
    span: Span,
    function: String,
    keys: Vec<AtomArg>,
    value: AtomArg,
    input_sorts: Vec<String>,
    output_sort: String,
}

#[derive(Clone, Debug)]
struct SourceFact {
    id: SourceFactId,
    command_index: usize,
    /// One input command expands to one independently sliceable source fact
    /// per TSV row. Ordinary source actions use `None`.
    expansion_index: Option<usize>,
    kind: SourceFactKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct SourceFactId(u32);

#[derive(Clone, Debug)]
enum SourceFactKind {
    Relation(AtomTemplate),
    Constructor(AtomArg),
    GlobalConstructor { name: String, sort: String },
    FunctionSet(FunctionSetTemplate),
}

#[derive(Clone, Debug)]
struct SourceRuleOrigin {
    source_command_index: usize,
    source_location: String,
    original_name: Option<String>,
    derived_replay_vars: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct TypedEndpoint {
    sort: String,
    value: Value,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct RowKey {
    relation: String,
    args: Vec<TypedEndpoint>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct FunctionRowKey {
    function: String,
    keys: Vec<TypedEndpoint>,
}

#[derive(Clone, Debug)]
struct FunctionRowState {
    output: TypedEndpoint,
    dependency: DepId,
    deferred_error: Option<DeferredUnsupported>,
}

type SourceCommandExpansions = IndexMap<usize, Vec<Command>>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct DepId(u32);

impl DepId {
    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct EventId(u32);

impl EventId {
    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct WitnessId(u32);

impl WitnessId {
    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct SyntaxId(u32);

#[derive(Clone, Debug, PartialEq, Eq)]
enum DepNode {
    Empty,
    Event(EventId),
    And(DepId, DepId),
    /// Resolve the unique successful-union path only if backward slicing
    /// reaches this equality. Ordinary elaboration needs only the cheap raw
    /// connectivity check.
    Eq {
        left: TypedEndpoint,
        right: TypedEndpoint,
    },
    /// Conservatively retain every source/effective event through this
    /// commit boundary when the native trace exposes an exact equality edge
    /// but not the constructor/merge cause that produced it.
    Prefix(EventId),
    /// Fail closed only if backward reachability consumes this current-state
    /// support. This lets an unsupported mutable transition disappear with an
    /// irrelevant branch instead of rejecting the whole traced execution.
    Unsupported {
        location: String,
        reason: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct DepArena {
    nodes: Vec<DepNode>,
}

impl Default for DepArena {
    fn default() -> Self {
        Self {
            nodes: vec![DepNode::Empty],
        }
    }
}

impl DepArena {
    const EMPTY: DepId = DepId(0);

    fn push(&mut self, node: DepNode) -> Result<DepId, CausalSliceError> {
        let id = u32::try_from(self.nodes.len()).map_err(|_| {
            CausalSliceError::Invariant("dependency arena exceeded u32 capacity".to_owned())
        })?;
        self.nodes.push(node);
        Ok(DepId(id))
    }

    fn event(&mut self, event: EventId) -> Result<DepId, CausalSliceError> {
        self.push(DepNode::Event(event))
    }

    fn prefix(&mut self, last_event: Option<EventId>) -> Result<DepId, CausalSliceError> {
        match last_event {
            Some(event) => self.push(DepNode::Prefix(event)),
            None => Ok(Self::EMPTY),
        }
    }

    fn unsupported(&mut self, location: String, reason: String) -> Result<DepId, CausalSliceError> {
        self.push(DepNode::Unsupported { location, reason })
    }

    fn and(&mut self, left: DepId, right: DepId) -> Result<DepId, CausalSliceError> {
        if left == Self::EMPTY {
            Ok(right)
        } else if right == Self::EMPTY || left == right {
            Ok(left)
        } else {
            self.push(DepNode::And(left, right))
        }
    }

    fn equality(
        &mut self,
        left: TypedEndpoint,
        right: TypedEndpoint,
    ) -> Result<DepId, CausalSliceError> {
        if left == right {
            Ok(Self::EMPTY)
        } else {
            self.push(DepNode::Eq { left, right })
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum WitnessNode {
    Literal {
        sort: String,
        value: Literal,
    },
    App {
        sort: String,
        function: String,
        children: Vec<WitnessId>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum WitnessSyntaxNode {
    Literal {
        sort: String,
        value: Literal,
    },
    App {
        sort: String,
        function: String,
        children: Vec<SyntaxId>,
    },
}

#[derive(Clone, Debug)]
struct WitnessRecord {
    node: WitnessNode,
    syntax: SyntaxId,
    original_value: Option<Value>,
    availability: DepId,
    contains_bigrat_primitive: bool,
}

#[derive(Clone, Debug, Default)]
struct WitnessArena {
    nodes: Vec<WitnessRecord>,
    ids: IndexMap<WitnessNode, WitnessId>,
    syntax_nodes: Vec<WitnessSyntaxNode>,
    syntax_ids: IndexMap<WitnessSyntaxNode, SyntaxId>,
    syntax_instances: IndexMap<SyntaxId, Vec<WitnessId>>,
    app_instances: IndexMap<(String, String), Vec<WitnessId>>,
    endpoints: IndexMap<TypedEndpoint, WitnessId>,
    endpoint_instances: IndexMap<TypedEndpoint, Vec<WitnessId>>,
    endpoint_sorts: IndexMap<Value, Vec<String>>,
    /// Current causal support for a typed container endpoint. Firings copy the
    /// immutable DepId they observe; rebuild replaces only this sidecar
    /// pointer, so later syntax aliases inherit the new temporal support.
    current_container_support: IndexMap<TypedEndpoint, DepId>,
    /// Definition-time endpoints retained to explain later canonicalized uses.
    globals: IndexMap<String, TypedEndpoint>,
    global_witnesses: IndexMap<String, WitnessId>,
    /// Exact values read from the native pre-state for the batch currently
    /// being elaborated.
    current_globals: IndexMap<String, TypedEndpoint>,
}

#[derive(Clone, Debug, Default)]
struct WitnessSnapshot {
    node_count: usize,
    endpoints: IndexMap<TypedEndpoint, WitnessId>,
    app_instance_lengths: IndexMap<(String, String), usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct CanonicalAppSignature {
    children: Box<[TypedEndpoint]>,
    output: TypedEndpoint,
}

#[derive(Debug, Default)]
struct AppGroupIndex {
    synced_len: usize,
    buckets: HashMap<CanonicalAppSignature, Vec<usize>>,
    unresolved: Vec<usize>,
}

#[derive(Debug, Default)]
struct WaveAppIndex {
    groups: HashMap<(String, String), AppGroupIndex>,
}

impl WaveAppIndex {
    fn synchronize_group(
        &mut self,
        key: &(String, String),
        witnesses: &WitnessArena,
        equality_forest: &EqualityForest,
    ) -> Result<(), CausalSliceError> {
        let instances = witnesses
            .app_instances
            .get(key)
            .map(Vec::as_slice)
            .unwrap_or_default();
        let group = self.groups.entry(key.clone()).or_default();
        if group.synced_len > instances.len() {
            return Err(CausalSliceError::Invariant(format!(
                "wave application index for `{}::{}` observed a shrinking append-only witness group",
                key.0, key.1
            )));
        }

        let mut pending = std::mem::take(&mut group.unresolved);
        pending.extend(group.synced_len..instances.len());
        group.synced_len = instances.len();
        for position in pending {
            let witness = instances[position];
            let Some(signature) = canonical_app_signature(
                witnesses,
                &witnesses.nodes[witness.index()].node,
                witnesses.endpoint(witness),
                equality_forest,
            ) else {
                group.unresolved.push(position);
                continue;
            };
            let bucket = group.buckets.entry(signature).or_default();
            if let Err(insertion) = bucket.binary_search(&position) {
                bucket.insert(insertion, position);
            }
        }
        Ok(())
    }
}

impl WitnessArena {
    fn snapshot(&self) -> WitnessSnapshot {
        WitnessSnapshot {
            node_count: self.nodes.len(),
            endpoints: self.endpoints.clone(),
            app_instance_lengths: self
                .app_instances
                .iter()
                .map(|(application, instances)| (application.clone(), instances.len()))
                .collect(),
        }
    }

    fn intern_syntax(&mut self, node: &WitnessNode) -> Result<SyntaxId, CausalSliceError> {
        let syntax = match node {
            WitnessNode::Literal { sort, value } => WitnessSyntaxNode::Literal {
                sort: sort.clone(),
                value: value.clone(),
            },
            WitnessNode::App {
                sort,
                function,
                children,
            } => WitnessSyntaxNode::App {
                sort: sort.clone(),
                function: function.clone(),
                children: children
                    .iter()
                    .map(|child| self.nodes[child.index()].syntax)
                    .collect(),
            },
        };
        if let Some(id) = self.syntax_ids.get(&syntax) {
            return Ok(*id);
        }
        let id = SyntaxId(u32::try_from(self.syntax_nodes.len()).map_err(|_| {
            CausalSliceError::Invariant("witness syntax arena exceeded u32 capacity".to_owned())
        })?);
        self.syntax_nodes.push(syntax.clone());
        self.syntax_ids.insert(syntax, id);
        Ok(id)
    }

    fn intern_literal(
        &mut self,
        sort: &str,
        value: Literal,
    ) -> Result<WitnessId, CausalSliceError> {
        let node = WitnessNode::Literal {
            sort: sort.to_owned(),
            value,
        };
        if let Some(id) = self.ids.get(&node) {
            return Ok(*id);
        }
        let id = WitnessId(u32::try_from(self.nodes.len()).map_err(|_| {
            CausalSliceError::Invariant("witness arena exceeded u32 capacity".to_owned())
        })?);
        let syntax = self.intern_syntax(&node)?;
        self.nodes.push(WitnessRecord {
            node: node.clone(),
            syntax,
            original_value: None,
            availability: DepArena::EMPTY,
            contains_bigrat_primitive: false,
        });
        self.ids.insert(node, id);
        Ok(id)
    }

    fn intern_app(
        &mut self,
        sort: &str,
        function: &str,
        children: Vec<WitnessId>,
        endpoint: Value,
        availability: DepId,
        allow_endpoint_alias: bool,
    ) -> Result<WitnessId, CausalSliceError> {
        let node = WitnessNode::App {
            sort: sort.to_owned(),
            function: function.to_owned(),
            children,
        };
        let id = if let Some(id) = self.ids.get(&node).copied() {
            match self.endpoint(id) {
                Some(previous) if previous != endpoint && allow_endpoint_alias => {
                    return self.alias_app_endpoint(node, endpoint, availability);
                }
                _ => id,
            }
        } else {
            let id = WitnessId(u32::try_from(self.nodes.len()).map_err(|_| {
                CausalSliceError::Invariant("witness arena exceeded u32 capacity".to_owned())
            })?);
            let syntax = self.intern_syntax(&node)?;
            let contains_bigrat_primitive = self.node_contains_bigrat_primitive(&node);
            self.nodes.push(WitnessRecord {
                node: node.clone(),
                syntax,
                original_value: Some(endpoint),
                availability,
                contains_bigrat_primitive,
            });
            self.ids.insert(node, id);
            id
        };
        self.bind_endpoint_with_alias(sort, endpoint, id, allow_endpoint_alias)?;
        self.record_endpoint_instance(sort, endpoint, id);
        Ok(id)
    }

    fn intern_syntax_app(
        &mut self,
        sort: &str,
        function: &str,
        children: Vec<WitnessId>,
    ) -> Result<WitnessId, CausalSliceError> {
        let node = WitnessNode::App {
            sort: sort.to_owned(),
            function: function.to_owned(),
            children,
        };
        if let Some(id) = self.ids.get(&node) {
            return Ok(*id);
        }
        let id = WitnessId(u32::try_from(self.nodes.len()).map_err(|_| {
            CausalSliceError::Invariant("witness arena exceeded u32 capacity".to_owned())
        })?);
        let syntax = self.intern_syntax(&node)?;
        let contains_bigrat_primitive = self.node_contains_bigrat_primitive(&node);
        self.nodes.push(WitnessRecord {
            node: node.clone(),
            syntax,
            original_value: None,
            availability: DepArena::EMPTY,
            contains_bigrat_primitive,
        });
        self.ids.insert(node, id);
        Ok(id)
    }

    fn bind_endpoint(
        &mut self,
        sort: &str,
        endpoint: Value,
        id: WitnessId,
    ) -> Result<(), CausalSliceError> {
        self.bind_endpoint_with_alias(sort, endpoint, id, false)?;
        self.record_endpoint_instance(sort, endpoint, id);
        Ok(())
    }

    fn bind_endpoint_alias(
        &mut self,
        sort: &str,
        endpoint: Value,
        id: WitnessId,
    ) -> Result<(), CausalSliceError> {
        self.bind_endpoint_with_alias(sort, endpoint, id, true)?;
        self.record_endpoint_instance(sort, endpoint, id);
        Ok(())
    }

    fn bind_endpoint_with_alias(
        &mut self,
        sort: &str,
        endpoint: Value,
        id: WitnessId,
        allow_endpoint_alias: bool,
    ) -> Result<(), CausalSliceError> {
        let key = TypedEndpoint {
            sort: sort.to_owned(),
            value: endpoint,
        };
        if let Some(previous) = self.endpoints.get(&key) {
            if *previous != id {
                if allow_endpoint_alias {
                    match self.nodes[id.index()].original_value {
                        Some(previous) if previous != endpoint => {
                            return Err(CausalSliceError::Invariant(format!(
                                "aliased `{sort}` replay syntax changed runtime endpoints"
                            )));
                        }
                        Some(_) => {}
                        None => self.nodes[id.index()].original_value = Some(endpoint),
                    }
                    return Ok(());
                }
                return Err(CausalSliceError::Unsupported {
                    location: format!("captured `{sort}` value"),
                    reason: "one runtime endpoint with conflicting replay witnesses".to_owned(),
                });
            }
            return Ok(());
        }
        if let Some(previous) = self.nodes[id.index()].original_value {
            if previous != endpoint {
                if allow_endpoint_alias {
                    self.endpoints.insert(key, id);
                    return Ok(());
                }
                return Err(CausalSliceError::Unsupported {
                    location: format!("captured `{sort}` constructor application"),
                    reason: "one source term producing distinct runtime endpoints in the same no-equality trace"
                        .to_owned(),
                });
            }
        } else {
            self.nodes[id.index()].original_value = Some(endpoint);
        }
        self.endpoints.insert(key, id);
        Ok(())
    }

    fn by_endpoint(&self, sort: &str, endpoint: Value) -> Option<WitnessId> {
        self.endpoints
            .get(&TypedEndpoint {
                sort: sort.to_owned(),
                value: endpoint,
            })
            .copied()
    }

    fn by_endpoint_at(
        &self,
        sort: &str,
        endpoint: Value,
        snapshot: Option<&WitnessSnapshot>,
    ) -> Option<WitnessId> {
        let Some(snapshot) = snapshot else {
            return self.by_endpoint(sort, endpoint);
        };
        let key = TypedEndpoint {
            sort: sort.to_owned(),
            value: endpoint,
        };
        snapshot
            .endpoints
            .get(&key)
            .copied()
            .filter(|witness| self.endpoint(*witness) == Some(endpoint))
    }

    fn prefer_endpoint_witness(
        &mut self,
        sort: &str,
        endpoint: Value,
        witness: WitnessId,
    ) -> Result<(), CausalSliceError> {
        if self.endpoint(witness) != Some(endpoint) {
            return Err(CausalSliceError::Invariant(format!(
                "preferred `{sort}` witness does not denote its captured endpoint"
            )));
        }
        self.endpoints.insert(
            TypedEndpoint {
                sort: sort.to_owned(),
                value: endpoint,
            },
            witness,
        );
        Ok(())
    }

    fn alias_app_endpoint(
        &mut self,
        node: WitnessNode,
        endpoint: Value,
        availability: DepId,
    ) -> Result<WitnessId, CausalSliceError> {
        let sort = match &node {
            WitnessNode::App { sort, .. } => sort.clone(),
            WitnessNode::Literal { .. } => {
                return Err(CausalSliceError::Invariant(
                    "only constructor syntax may receive an endpoint alias".to_owned(),
                ));
            }
        };
        if let Some(witness) = self.ids.get(&node).copied()
            && self.endpoint(witness) == Some(endpoint)
        {
            self.prefer_endpoint_witness(&sort, endpoint, witness)?;
            self.record_endpoint_instance(&sort, endpoint, witness);
            return Ok(witness);
        }
        let id = WitnessId(u32::try_from(self.nodes.len()).map_err(|_| {
            CausalSliceError::Invariant("witness arena exceeded u32 capacity".to_owned())
        })?);
        let syntax = self.intern_syntax(&node)?;
        let contains_bigrat_primitive = self.node_contains_bigrat_primitive(&node);
        self.nodes.push(WitnessRecord {
            node: node.clone(),
            syntax,
            original_value: Some(endpoint),
            availability,
            contains_bigrat_primitive,
        });
        self.ids.insert(node, id);
        self.prefer_endpoint_witness(&sort, endpoint, id)?;
        self.record_endpoint_instance(&sort, endpoint, id);
        Ok(id)
    }

    fn record_endpoint_instance(&mut self, sort: &str, endpoint: Value, id: WitnessId) {
        if self.endpoint(id) != Some(endpoint) {
            return;
        }
        let sorts = self.endpoint_sorts.entry(endpoint).or_default();
        if !sorts.iter().any(|candidate| candidate == sort) {
            sorts.push(sort.to_owned());
        }
        let instances = self
            .endpoint_instances
            .entry(TypedEndpoint {
                sort: sort.to_owned(),
                value: endpoint,
            })
            .or_default();
        if !instances.contains(&id) {
            instances.push(id);
        }
        let syntax = self.nodes[id.index()].syntax;
        let syntax_instances = self.syntax_instances.entry(syntax).or_default();
        if !syntax_instances.contains(&id) {
            syntax_instances.push(id);
        }
        if let WitnessNode::App { sort, function, .. } = &self.nodes[id.index()].node {
            let instances = self
                .app_instances
                .entry((sort.clone(), function.clone()))
                .or_default();
            if !instances.contains(&id) {
                instances.push(id);
            }
        }
    }

    fn instance_by_node_endpoint(
        &self,
        sort: &str,
        endpoint: Value,
        node: &WitnessNode,
    ) -> Option<WitnessId> {
        self.endpoint_instances
            .get(&TypedEndpoint {
                sort: sort.to_owned(),
                value: endpoint,
            })?
            .iter()
            .copied()
            .find(|id| &self.nodes[id.index()].node == node)
    }

    fn node_contains_bigrat_primitive(&self, node: &WitnessNode) -> bool {
        match node {
            WitnessNode::App {
                sort,
                function,
                children,
            } => {
                (sort == "BigRat" && replay_safe_bigrat_primitive_arity(function).is_some())
                    || children
                        .iter()
                        .any(|child| self.nodes[child.index()].contains_bigrat_primitive)
            }
            WitnessNode::Literal { .. } => false,
        }
    }

    fn bind_global(
        &mut self,
        name: &str,
        sort: &str,
        endpoint: Value,
        witness: WitnessId,
    ) -> Result<(), CausalSliceError> {
        if self.endpoint(witness) != Some(endpoint) {
            return Err(CausalSliceError::Invariant(format!(
                "source global `{name}` witness did not denote its definition-time endpoint"
            )));
        }
        let value = TypedEndpoint {
            sort: sort.to_owned(),
            value: endpoint,
        };
        if let Some(previous) = self.globals.get(name) {
            if previous != &value {
                return Err(CausalSliceError::Invariant(format!(
                    "source global `{name}` was rebound while elaborating the trace"
                )));
            }
        } else {
            self.globals.insert(name.to_owned(), value.clone());
            self.global_witnesses.insert(name.to_owned(), witness);
        }
        self.current_globals.insert(name.to_owned(), value);
        Ok(())
    }

    fn global_witness(&self, name: &str, sort: &str) -> Result<WitnessId, CausalSliceError> {
        let endpoint = self.globals.get(name).ok_or_else(|| {
            CausalSliceError::Invariant(format!(
                "source global `{name}` has no definition-time endpoint"
            ))
        })?;
        if endpoint.sort != sort {
            return Err(CausalSliceError::Invariant(format!(
                "source global `{name}` was modeled as `{sort}` but defined as `{}`",
                endpoint.sort
            )));
        }
        let witness = self.global_witnesses.get(name).copied().ok_or_else(|| {
            CausalSliceError::Invariant(format!("source global `{name}` lost its replay witness"))
        })?;
        if self.endpoint(witness) != Some(endpoint.value) {
            return Err(CausalSliceError::Invariant(format!(
                "source global `{name}` replay witness changed endpoints"
            )));
        }
        Ok(witness)
    }

    fn load_current_globals(
        &mut self,
        globals: &[(std::sync::Arc<str>, Value)],
    ) -> Result<(), CausalSliceError> {
        if globals.len() != self.globals.len() {
            return Err(CausalSliceError::Invariant(format!(
                "native trace captured {} globals after {} source definitions",
                globals.len(),
                self.globals.len()
            )));
        }
        self.current_globals.clear();
        for (name, value) in globals {
            let definition = self.globals.get(name.as_ref()).ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "native trace captured unknown source global `{name}`"
                ))
            })?;
            if self
                .current_globals
                .insert(
                    name.to_string(),
                    TypedEndpoint {
                        sort: definition.sort.clone(),
                        value: *value,
                    },
                )
                .is_some()
            {
                return Err(CausalSliceError::Invariant(format!(
                    "native trace captured duplicate source global `{name}`"
                )));
            }
        }
        Ok(())
    }

    fn global(&self, name: &str, sort: &str) -> Result<Value, CausalSliceError> {
        let endpoint = self.current_globals.get(name).ok_or_else(|| {
            CausalSliceError::Invariant(format!(
                "source global `{name}` was used without a native pre-state snapshot"
            ))
        })?;
        if endpoint.sort != sort {
            return Err(CausalSliceError::Invariant(format!(
                "source global `{name}` was modeled as `{sort}` but captured as `{}`",
                endpoint.sort
            )));
        }
        Ok(endpoint.value)
    }

    fn global_endpoints(
        &self,
        name: &str,
        sort: &str,
    ) -> Result<(&TypedEndpoint, &TypedEndpoint), CausalSliceError> {
        let definition = self.globals.get(name).ok_or_else(|| {
            CausalSliceError::Invariant(format!(
                "source global `{name}` has no definition-time endpoint"
            ))
        })?;
        let current = self.current_globals.get(name).ok_or_else(|| {
            CausalSliceError::Invariant(format!(
                "source global `{name}` has no native pre-state snapshot"
            ))
        })?;
        if definition.sort != sort || current.sort != sort {
            return Err(CausalSliceError::Invariant(format!(
                "source global `{name}` endpoint sort diverged from modeled sort `{sort}`"
            )));
        }
        Ok((definition, current))
    }

    fn set_availability(&mut self, id: WitnessId, availability: DepId) {
        let record = &mut self.nodes[id.index()];
        if record.availability == DepArena::EMPTY {
            record.availability = availability;
        }
    }

    fn current_container_support(&self, endpoint: &TypedEndpoint) -> Option<DepId> {
        self.current_container_support.get(endpoint).copied()
    }

    fn replace_current_container_support(&mut self, endpoint: TypedEndpoint, availability: DepId) {
        self.current_container_support
            .insert(endpoint, availability);
    }

    fn availability(&self, id: WitnessId) -> DepId {
        let record = &self.nodes[id.index()];
        let Some(value) = record.original_value else {
            return record.availability;
        };
        let sort = match &record.node {
            WitnessNode::Literal { sort, .. } | WitnessNode::App { sort, .. } => sort,
        };
        self.current_container_support
            .get(&TypedEndpoint {
                sort: sort.clone(),
                value,
            })
            .copied()
            .unwrap_or(record.availability)
    }

    fn endpoint(&self, id: WitnessId) -> Option<Value> {
        self.nodes[id.index()].original_value
    }
}

#[derive(Clone, Copy, Debug)]
struct BindingWitness {
    syntax: WitnessId,
    endpoint: Value,
}

#[derive(Clone, Debug)]
struct GroundedFire {
    rule: String,
    wave: u32,
    ordinal: u32,
    bindings: IndexMap<String, BindingWitness>,
    selector: ReplaySelector,
}

#[derive(Clone, Debug)]
enum ReplaySelector {
    /// Filled once every successful grounding for this rule and wave is known.
    Unplanned,
    /// The ordered source variables that uniquely identify this grounding.
    Key(Arc<[String]>),
    /// Kept on the firing so an irrelevant unsupported group can slice away.
    Unsupported(Arc<DeferredUnsupported>),
}

impl GroundedFire {
    fn selector_variables(&self) -> Result<&Arc<[String]>, CausalSliceError> {
        match &self.selector {
            ReplaySelector::Key(variables) => Ok(variables),
            ReplaySelector::Unsupported(error) => Err((**error).clone().into_error()),
            ReplaySelector::Unplanned => Err(CausalSliceError::Invariant(format!(
                "grounded firing of `{}` in wave {} reached emission before replay-key planning",
                self.rule, self.wave
            ))),
        }
    }
}

#[derive(Clone, Debug)]
struct PendingFire {
    grounding: GroundedFire,
    effective: bool,
}

#[derive(Clone, Debug)]
enum EventKind {
    Source { fact: SourceFactId },
    Fire(GroundedFire),
    OpaqueFire,
}

#[derive(Clone, Debug)]
struct ReplayEvent {
    kind: EventKind,
    prerequisites: DepId,
    deferred_prerequisite_error: Option<DeferredUnsupported>,
    effective_outputs: Vec<RowKey>,
}

#[derive(Clone, Debug)]
struct DeferredUnsupported {
    location: String,
    reason: String,
}

impl DeferredUnsupported {
    fn into_error(self) -> CausalSliceError {
        CausalSliceError::Unsupported {
            location: self.location,
            reason: self.reason,
        }
    }
}

enum BindingReconstructionError {
    Projected(DeferredUnsupported),
    Other(CausalSliceError),
}

impl BindingReconstructionError {
    fn into_error(self) -> CausalSliceError {
        match self {
            Self::Projected(error) => error.into_error(),
            Self::Other(error) => error,
        }
    }
}

impl From<CausalSliceError> for BindingReconstructionError {
    fn from(error: CausalSliceError) -> Self {
        Self::Other(error)
    }
}

#[derive(Clone, Debug, Default)]
struct EventArena {
    events: Vec<ReplayEvent>,
}

impl EventArena {
    fn push(&mut self, event: ReplayEvent) -> Result<EventId, CausalSliceError> {
        let id = EventId(u32::try_from(self.events.len()).map_err(|_| {
            CausalSliceError::Invariant("event arena exceeded u32 capacity".to_owned())
        })?);
        self.events.push(event);
        Ok(id)
    }
}

struct Elaboration {
    pending_fires: Vec<PendingFire>,
    opaque_pending_firings: usize,
    opaque_promoted_events: usize,
    events: EventArena,
    dependencies: DepArena,
    producers: IndexMap<RowKey, DepId>,
    source_events: usize,
    equality_forest: EqualityForest,
    opaque_equality_error: Option<DeferredUnsupported>,
    causal_prefix_fallbacks: usize,
}

struct PrefixElaboration {
    replay_fires: Vec<CompactReplayFire>,
    pending_firings: usize,
    captured_bindings: usize,
    effective_applications: usize,
    effective_output_rows: usize,
    source_events: usize,
    witness_nodes: usize,
    equality_edges: usize,
}

/// Prefix fallback can retain hundreds of thousands of effective firings. A
/// compact rule index plus witness IDs keeps those firings available for a
/// source-sharing pass without retaining their expanded syntax or per-variable
/// hash maps.
struct CompactReplayFire {
    rule_index: u32,
    wave: u32,
    ordinal: u32,
    bindings: Box<[WitnessId]>,
    /// Prefix-only replay uses the rule model's complete variable list. A
    /// causal grounding stores its deterministic projected replay key here.
    selector_variables: Option<Arc<[String]>>,
}

/// A compact stable grouping from one match origin to indices in a trace
/// payload. This avoids allocating one `Vec` per match in very large waves.
struct OriginIndex {
    offsets: Vec<u32>,
    item_indices: Vec<u32>,
}

impl OriginIndex {
    fn build<T>(
        origin_count: usize,
        items: &[T],
        mut origin: impl FnMut(&T) -> Option<usize>,
        context: &str,
    ) -> Result<Self, CausalSliceError> {
        let mut offsets = vec![0u32; origin_count + 1];
        for item in items {
            let Some(item_origin) = origin(item) else {
                continue;
            };
            let Some(count) = offsets.get_mut(item_origin + 1) else {
                return Err(CausalSliceError::Invariant(format!(
                    "{context} origin {item_origin} exceeded {origin_count} matches"
                )));
            };
            *count = count.checked_add(1).ok_or_else(|| {
                CausalSliceError::Invariant(format!("{context} grouping exceeded u32 capacity"))
            })?;
        }
        for index in 1..offsets.len() {
            offsets[index] = offsets[index]
                .checked_add(offsets[index - 1])
                .ok_or_else(|| {
                    CausalSliceError::Invariant(format!("{context} grouping exceeded u32 capacity"))
                })?;
        }

        let total = offsets.last().copied().unwrap_or(0) as usize;
        let mut item_indices = vec![0u32; total];
        let mut cursors = offsets[..origin_count].to_vec();
        for (item_index, item) in items.iter().enumerate() {
            let Some(item_origin) = origin(item) else {
                continue;
            };
            let position = cursors[item_origin] as usize;
            item_indices[position] = u32::try_from(item_index).map_err(|_| {
                CausalSliceError::Invariant(format!("{context} index exceeded u32 capacity"))
            })?;
            cursors[item_origin] += 1;
        }
        Ok(Self {
            offsets,
            item_indices,
        })
    }

    fn for_origin(&self, origin: usize) -> &[u32] {
        let start = self.offsets[origin] as usize;
        let end = self.offsets[origin + 1] as usize;
        &self.item_indices[start..end]
    }
}

#[derive(Clone, Debug)]
struct EqualityEdge {
    sort: String,
    parent: Value,
    child: Value,
    dependency: DepId,
}

#[derive(Clone, Debug)]
struct AppliedEquality {
    left: TypedEndpoint,
    right: TypedEndpoint,
    parent: Value,
    child: Value,
    commit_ordinal: usize,
}

#[derive(Clone, Copy, Debug)]
struct OrderedUnionReceipt<'a> {
    commit_ordinal: usize,
    receipt: &'a UnionReceipt,
}

#[derive(Clone, Debug, Default)]
struct EqualityForest {
    edges: Vec<EqualityEdge>,
    /// Immutable native commit forest. Unlike the compressed lookup sidecar,
    /// these edges retain the exact path on which causal labels live.
    commit_parents: IndexMap<Value, Value>,
    edge_causes: IndexMap<Value, (String, DepId)>,
    /// Raw native union-find parent changes, including successful receipts
    /// whose equality sort or replay cause is intentionally unavailable.
    /// Constructor IDs come from the backend-global ID counter, so the raw
    /// values are stable across equality sorts within one execution.
    canonical_parents: RefCell<IndexMap<Value, Value>>,
}

impl EqualityForest {
    fn observe_receipt(&mut self, receipt: &UnionReceipt) -> Result<(), CausalSliceError> {
        let UnionOutcome::Applied { parent, child } = receipt.outcome else {
            return Ok(());
        };
        let left_root = self.canonical_value(receipt.lhs);
        let right_root = self.canonical_value(receipt.rhs);
        if parent == child
            || !((left_root == parent && right_root == child)
                || (left_root == child && right_root == parent))
        {
            return Err(CausalSliceError::Invariant(format!(
                "successful raw union endpoints {:?} and {:?} had reported representatives parent={parent:?}, child={child:?} inconsistent with the commit-order roots {left_root:?} and {right_root:?}",
                receipt.lhs, receipt.rhs
            )));
        }
        if self
            .canonical_parents
            .borrow_mut()
            .insert(child, parent)
            .is_some()
        {
            return Err(CausalSliceError::Invariant(
                "successful raw union reparented a non-representative equality endpoint".to_owned(),
            ));
        }
        if self.commit_parents.insert(child, parent).is_some() {
            return Err(CausalSliceError::Invariant(
                "successful raw union duplicated one commit-forest child".to_owned(),
            ));
        }
        Ok(())
    }

    fn add_explanation(
        &mut self,
        equality: AppliedEquality,
        dependency: DepId,
    ) -> Result<(), CausalSliceError> {
        let AppliedEquality {
            left,
            right,
            parent,
            child,
            commit_ordinal: _,
        } = equality;
        if left.sort != right.sort {
            return Err(CausalSliceError::Invariant(format!(
                "successful union crossed runtime sorts `{}` and `{}`",
                left.sort, right.sort
            )));
        }
        if self.canonical_value(left.value) != parent || self.canonical_value(right.value) != parent
        {
            return Err(CausalSliceError::Invariant(format!(
                "typed equality endpoints {left:?} and {right:?} were not both canonicalized to the reported native parent {parent:?} after committing child {child:?}"
            )));
        }
        if self.commit_parents.get(&child) != Some(&parent) {
            return Err(CausalSliceError::Invariant(format!(
                "typed equality cause for child {child:?} did not match its raw commit parent {parent:?}"
            )));
        }
        if self
            .edge_causes
            .insert(child, (left.sort.clone(), dependency))
            .is_some()
        {
            return Err(CausalSliceError::Invariant(
                "one raw commit-forest edge received two typed causes".to_owned(),
            ));
        }
        self.edges.push(EqualityEdge {
            sort: left.sort,
            parent,
            child,
            dependency,
        });
        Ok(())
    }

    fn canonical_value(&self, value: Value) -> Value {
        let mut parents = self.canonical_parents.borrow_mut();
        let mut current = value;
        let mut path = Vec::new();
        while let Some(parent) = parents.get(&current).copied() {
            path.push(current);
            current = parent;
        }
        for child in path {
            parents.insert(child, current);
        }
        current
    }

    #[cfg(test)]
    fn raw_parent_count(&self) -> usize {
        self.canonical_parents.borrow().len()
    }

    fn canonical_endpoint(&self, endpoint: &TypedEndpoint) -> TypedEndpoint {
        TypedEndpoint {
            sort: endpoint.sort.clone(),
            value: self.typed_canonical_value(&endpoint.sort, endpoint.value),
        }
    }

    fn are_equal(&self, left: &TypedEndpoint, right: &TypedEndpoint) -> bool {
        left.sort == right.sort
            && self.typed_canonical_value(&left.sort, left.value)
                == self.typed_canonical_value(&right.sort, right.value)
    }

    fn typed_canonical_value(&self, sort: &str, value: Value) -> Value {
        let mut current = value;
        while let Some(parent) = self.commit_parents.get(&current).copied() {
            let Some((edge_sort, _)) = self.edge_causes.get(&current) else {
                break;
            };
            if edge_sort != sort {
                break;
            }
            current = parent;
        }
        current
    }

    fn explain(&self, left: &TypedEndpoint, right: &TypedEndpoint) -> Option<Vec<DepId>> {
        if left == right {
            return Some(Vec::new());
        }
        if left.sort != right.sort {
            return None;
        }
        let mut left_paths = IndexMap::default();
        let mut current = left.value;
        let mut path = Vec::new();
        let mut complete = true;
        left_paths.insert(current, Some(path.clone()));
        while let Some(parent) = self.commit_parents.get(&current).copied() {
            match self.edge_causes.get(&current) {
                Some((sort, dependency)) if sort == &left.sort => path.push(*dependency),
                _ => complete = false,
            }
            current = parent;
            left_paths.insert(current, complete.then(|| path.clone()));
        }

        current = right.value;
        path.clear();
        complete = true;
        loop {
            if let Some(left_path) = left_paths.get(&current) {
                let mut explanation = left_path.as_ref()?.clone();
                if !complete {
                    return None;
                }
                explanation.extend(path.iter().copied());
                return Some(explanation);
            }
            let parent = self.commit_parents.get(&current).copied()?;
            match self.edge_causes.get(&current) {
                Some((sort, dependency)) if sort == &right.sort => path.push(*dependency),
                _ => complete = false,
            }
            current = parent;
        }
    }

    fn edge_count(&self) -> usize {
        debug_assert!(self.edges.iter().all(|edge| {
            self.commit_parents.get(&edge.child) == Some(&edge.parent)
                && self.edge_causes.get(&edge.child) == Some(&(edge.sort.clone(), edge.dependency))
        }));
        self.edges.len()
    }
}

struct ProgramModel {
    rules: IndexMap<String, RuleModel>,
    checks: Vec<CheckModel>,
    source_facts: Vec<SourceFact>,
    constructors: IndexMap<String, ConstructorDecl>,
    mutable_functions: IndexMap<String, MutableFunctionDecl>,
    source_expansions: SourceCommandExpansions,
    schedule_indices: Vec<usize>,
    regions: Vec<ProgramRegion>,
    prefix_fallbacks: usize,
}

#[derive(Clone, Debug)]
struct ProgramRegion {
    schedule_indices: Vec<usize>,
    check_indices: Vec<usize>,
    check_command_indices: Vec<usize>,
    source_command_indices: IndexSet<usize>,
    /// A scoped region is elaborated immediately before this command executes,
    /// while its pushed native database is still available.
    pop_command_index: Option<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TraceFunctionKind {
    Relation,
    Constructor,
    Mutable,
}

#[derive(Clone, Debug)]
struct TraceFunctionMeta {
    name: String,
    input_sorts: Vec<String>,
    output_sort: String,
    kind: TraceFunctionKind,
    mutable_merge: Option<MutableMergeKind>,
}

struct ElaborationInput<'a> {
    egraph: &'a EGraph,
    rules: &'a IndexMap<String, RuleModel>,
    rule_primitives: &'a IndexMap<String, ResolvedRulePrimitives>,
    relations: &'a IndexMap<String, RelationDecl>,
    source_facts: &'a [SourceFact],
    source_traces: &'a IndexMap<usize, SourceExecutionTrace>,
    batches: &'a [RuleExecutionTrace],
    trace_functions: &'a IndexMap<TableId, TraceFunctionMeta>,
    prefix_fallback: bool,
}

struct PrefixElaborationInput<'a> {
    egraph: &'a EGraph,
    rules: &'a IndexMap<String, RuleModel>,
    rule_primitives: &'a IndexMap<String, ResolvedRulePrimitives>,
    relations: &'a IndexMap<String, RelationDecl>,
    source_facts: &'a [SourceFact],
    source_traces: &'a IndexMap<usize, SourceExecutionTrace>,
    batches: Vec<RuleExecutionTrace>,
    trace_functions: &'a IndexMap<TableId, TraceFunctionMeta>,
}

struct ObservationInput<'a> {
    egraph: &'a EGraph,
    checks: &'a [CheckModel],
    relations: &'a IndexMap<String, RelationDecl>,
    constructors: &'a IndexMap<String, ConstructorDecl>,
    traces: &'a [Vec<RuleExecutionTrace>],
    producers: &'a IndexMap<RowKey, DepId>,
    equality_forest: &'a EqualityForest,
    opaque_equality_error: Option<&'a DeferredUnsupported>,
}

struct SourceExecutionTrace {
    batches: Vec<RuleExecutionTrace>,
    global_endpoint: Option<Value>,
}

/// Trace one ordinary reference-backend execution and emit a guarded manual
/// replay slice. The accepted language is intentionally fail-closed; see
/// [`CausalSliceError::Unsupported`] for source-located boundary diagnostics.
pub fn causal_slice_program(
    filename: Option<String>,
    input: &str,
) -> Result<CausalSlice, CausalSliceError> {
    causal_slice_program_with_egraph(filename, input, EGraph::default())
}

/// Trace and slice a program while constructing only the retained replay
/// projection used by ordinary or proof-mode execution.
pub fn causal_slice_replay_program(
    filename: Option<String>,
    input: &str,
) -> Result<CausalReplay, CausalSliceError> {
    causal_slice_replay_program_with_egraph(filename, input, EGraph::default())
}

/// Trace and slice a program while resolving supported scalar relation inputs
/// relative to `fact_directory`. Input rows are embedded as ordinary source
/// facts in both replay projections, so the emitted programs are independent
/// of the external files.
pub fn causal_slice_program_with_fact_directory(
    filename: Option<String>,
    input: &str,
    fact_directory: Option<&Path>,
) -> Result<CausalSlice, CausalSliceError> {
    let egraph = EGraph {
        fact_directory: fact_directory.map(Path::to_path_buf),
        ..EGraph::default()
    };
    causal_slice_program_with_egraph(filename, input, egraph)
}

/// Trace and slice using a fresh ordinary reference-backed `EGraph` whose
/// parser, sorts, primitives, and commands may have been configured by a
/// downstream crate. The graph is consumed and must not contain source
/// program state or have term/proof encoding enabled.
pub fn causal_slice_program_with_egraph(
    filename: Option<String>,
    input: &str,
    egraph: EGraph,
) -> Result<CausalSlice, CausalSliceError> {
    let generated = generate_causal_slice(
        filename,
        input,
        egraph,
        true,
        ReplaySourceProjection::Legacy,
    )?;
    Ok(CausalSlice {
        source: generated.source,
        full_transcript_source: generated
            .full_transcript_source
            .expect("the diagnostic projection was requested"),
        stats: generated.stats,
        rule_mapping: generated.rule_mapping,
    })
}

/// Trace and slice a program while resolving supported scalar relation inputs
/// relative to `fact_directory`, without constructing the discarded full
/// transcript projection.
pub fn causal_slice_replay_program_with_fact_directory(
    filename: Option<String>,
    input: &str,
    fact_directory: Option<&Path>,
) -> Result<CausalReplay, CausalSliceError> {
    let egraph = EGraph {
        fact_directory: fact_directory.map(Path::to_path_buf),
        ..EGraph::default()
    };
    causal_slice_replay_program_with_egraph(filename, input, egraph)
}

/// Construct only the retained replay projection using a fresh configured
/// ordinary reference-backed `EGraph`. See
/// [`causal_slice_program_with_egraph`] for the template contract.
pub fn causal_slice_replay_program_with_egraph(
    filename: Option<String>,
    input: &str,
    egraph: EGraph,
) -> Result<CausalReplay, CausalSliceError> {
    let generated = generate_causal_slice(
        filename,
        input,
        egraph,
        false,
        ReplaySourceProjection::Legacy,
    )?;
    Ok(CausalReplay {
        source: generated.source,
        stats: generated.stats,
        rule_mapping: generated.rule_mapping,
    })
}

/// Trace one ordinary run and emit the source-minimized replay intended for
/// strict proof testing. Positive checks are the only observation roots.
pub fn causal_slice_proof_replay_program(
    filename: Option<String>,
    input: &str,
) -> Result<CausalReplay, CausalSliceError> {
    causal_slice_proof_replay_program_with_egraph(filename, input, EGraph::default())
}

/// Proof-oriented replay with scalar relation inputs resolved from a fact
/// directory and embedded only when retained by the causal slice.
pub fn causal_slice_proof_replay_program_with_fact_directory(
    filename: Option<String>,
    input: &str,
    fact_directory: Option<&Path>,
) -> Result<CausalReplay, CausalSliceError> {
    let egraph = EGraph {
        fact_directory: fact_directory.map(Path::to_path_buf),
        ..EGraph::default()
    };
    causal_slice_proof_replay_program_with_egraph(filename, input, egraph)
}

/// Proof-oriented replay using a configured reference-backend template.
pub fn causal_slice_proof_replay_program_with_egraph(
    filename: Option<String>,
    input: &str,
    egraph: EGraph,
) -> Result<CausalReplay, CausalSliceError> {
    let generated = generate_causal_slice(
        filename,
        input,
        egraph,
        false,
        ReplaySourceProjection::PositiveChecks,
    )?;
    Ok(CausalReplay {
        source: generated.source,
        stats: generated.stats,
        rule_mapping: generated.rule_mapping,
    })
}

struct GeneratedCausalSlice {
    source: String,
    full_transcript_source: Option<String>,
    stats: CausalSliceStats,
    rule_mapping: Vec<SourceRuleMapping>,
}

struct ScopedGenerationInput<'a> {
    filename: Option<String>,
    input: &'a str,
    source_name: &'a str,
    egraph: EGraph,
    validation_template: EGraph,
    commands: Vec<Command>,
    rules: IndexMap<String, RuleModel>,
    checks: Vec<CheckModel>,
    source_facts: Vec<SourceFact>,
    source_expansions: SourceCommandExpansions,
    schedule_indices: Vec<usize>,
    regions: Vec<ProgramRegion>,
    relations: IndexMap<String, RelationDecl>,
    constructors: IndexMap<String, ConstructorDecl>,
    mutable_functions: IndexMap<String, MutableFunctionDecl>,
    rule_mapping: Vec<SourceRuleMapping>,
    preparation_time: Duration,
    include_full_transcript: bool,
    source_projection: ReplaySourceProjection,
    total_start: Instant,
}

struct RegionSliceInput<'a> {
    egraph: &'a EGraph,
    commands: &'a [Command],
    source_name: &'a str,
    region: &'a ProgramRegion,
    rules: &'a IndexMap<String, RuleModel>,
    checks: &'a [CheckModel],
    relations: &'a IndexMap<String, RelationDecl>,
    constructors: &'a IndexMap<String, ConstructorDecl>,
    source_facts: &'a [SourceFact],
    source_traces: &'a IndexMap<usize, SourceExecutionTrace>,
    schedule_batches: &'a [RuleExecutionTrace],
    check_batches: &'a [Vec<RuleExecutionTrace>],
    trace_functions: &'a IndexMap<TableId, TraceFunctionMeta>,
    rule_primitives: &'a IndexMap<String, ResolvedRulePrimitives>,
    include_full_transcript: bool,
}

struct RegionProjection {
    replay_commands: String,
    full_transcript_commands: Option<String>,
    stats: CausalSliceStats,
    retained_source_facts: IndexSet<SourceFactId>,
    retained_rule_names: IndexSet<String>,
    retained_witness_callables: IndexSet<String>,
}

fn slice_region(input: RegionSliceInput<'_>) -> Result<RegionProjection, CausalSliceError> {
    let RegionSliceInput {
        egraph,
        commands,
        source_name,
        region,
        rules,
        checks,
        relations,
        constructors,
        source_facts,
        source_traces,
        schedule_batches,
        check_batches,
        trace_functions,
        rule_primitives,
        include_full_transcript,
    } = input;
    let selected_source_facts = source_facts
        .iter()
        .filter(|fact| region.source_command_indices.contains(&fact.command_index))
        .cloned()
        .collect::<Vec<_>>();
    let selected_checks = region
        .check_indices
        .iter()
        .map(|index| checks[*index].clone())
        .collect::<Vec<_>>();
    if selected_checks.len() != check_batches.len() {
        return Err(CausalSliceError::Invariant(format!(
            "scoped region captured {} check traces for {} modeled checks",
            check_batches.len(),
            selected_checks.len()
        )));
    }
    let schedule_index = *region.schedule_indices.first().ok_or_else(|| {
        CausalSliceError::Invariant("scoped region lost its computation schedule".to_owned())
    })?;
    let schedule_span = command_schedule_span(&commands[schedule_index])
        .ok_or_else(|| CausalSliceError::Invariant("schedule command lost its span".to_owned()))?;

    let observation_matches = check_batches
        .iter()
        .flat_map(|batches| batches.iter())
        .map(|batch| batch.matches.len())
        .sum::<usize>();
    let observation_trace_bindings = check_batches
        .iter()
        .flat_map(|batches| batches.iter())
        .flat_map(|batch| &batch.matches)
        .map(|event| event.bindings.len())
        .sum::<usize>();
    let schedule_trace_bindings = schedule_batches
        .iter()
        .flat_map(|batch| &batch.matches)
        .map(|event| event.bindings.len())
        .sum::<usize>();
    let matched_applications = schedule_batches
        .iter()
        .map(|batch| batch.matches.len())
        .sum::<usize>();
    let total_raw_matches = schedule_batches
        .iter()
        .map(|batch| batch.matches.len())
        .sum::<usize>()
        + observation_matches;
    let raw_trace_bindings = schedule_trace_bindings + observation_trace_bindings;
    let max_batch_matches = schedule_batches
        .iter()
        .chain(check_batches.iter().flat_map(|batches| batches.iter()))
        .map(|batch| batch.matches.len())
        .max()
        .unwrap_or(0);

    let elaboration_start = Instant::now();
    let mut witnesses = WitnessArena::default();
    let Elaboration {
        pending_fires,
        opaque_pending_firings,
        opaque_promoted_events,
        events,
        mut dependencies,
        producers,
        source_events,
        equality_forest,
        opaque_equality_error,
        causal_prefix_fallbacks,
    } = elaborate_events(
        ElaborationInput {
            egraph,
            rules,
            rule_primitives,
            relations,
            source_facts: &selected_source_facts,
            source_traces,
            batches: schedule_batches,
            trace_functions,
            prefix_fallback: false,
        },
        &mut witnesses,
    )?;
    let elaboration_time = elaboration_start.elapsed();

    let slicing_start = Instant::now();
    let roots = observation_roots(
        ObservationInput {
            egraph,
            checks: &selected_checks,
            relations,
            constructors,
            traces: check_batches,
            producers: &producers,
            equality_forest: &equality_forest,
            opaque_equality_error: opaque_equality_error.as_ref(),
        },
        &mut dependencies,
        &mut witnesses,
    )?;
    let (retained, retained_prefix_fallbacks) =
        backward_slice(&events, &dependencies, &equality_forest, roots)?;
    debug_assert!(retained_prefix_fallbacks <= causal_prefix_fallbacks);
    let retained_source_facts = retained
        .iter()
        .filter_map(|event| match events.events[event.index()].kind {
            EventKind::Source { fact } => Some(fact),
            EventKind::Fire(_) | EventKind::OpaqueFire => None,
        })
        .collect();
    let retained_rule_names = retained
        .iter()
        .filter_map(|event| match &events.events[event.index()].kind {
            EventKind::Fire(fire) => Some(fire.rule.clone()),
            EventKind::Source { .. } | EventKind::OpaqueFire => None,
        })
        .collect();
    if let Some(error) = retained.iter().find_map(|event| {
        events.events[event.index()]
            .deferred_prerequisite_error
            .clone()
    }) {
        return Err(error.into_error());
    }
    if include_full_transcript && opaque_pending_firings > 0 {
        return Err(CausalSliceError::Unsupported {
            location: source_name.to_owned(),
            reason: "a diagnostic full transcript containing opaque rule groundings; use the retained replay projection so unreachable unsupported rules can be sliced away"
                .to_owned(),
        });
    }
    let slicing_time = slicing_start.elapsed();

    let emission_start = Instant::now();
    let full_transcript_commands = if include_full_transcript {
        Some(
            render_replay_commands(
                commands,
                &schedule_span,
                rules,
                pending_fires.iter().map(|fire| &fire.grounding),
                &witnesses,
            )?
            .0,
        )
    } else {
        None
    };
    let replay_fires = retained
        .iter()
        .filter_map(|event| match &events.events[event.index()].kind {
            EventKind::Source { .. } => None,
            EventKind::Fire(fire) => Some(fire),
            EventKind::OpaqueFire => None,
        })
        .collect::<Vec<_>>();
    let retained_witness_callables =
        replay_witness_callables(replay_fires.iter().copied(), &witnesses)?;
    let (replay_commands, shared_replay_witnesses) =
        render_replay_commands(commands, &schedule_span, rules, replay_fires, &witnesses)?;
    let emission_time = emission_start.elapsed();

    let effective_applications =
        pending_fires.iter().filter(|fire| fire.effective).count() + opaque_promoted_events;
    let retained_applications = retained
        .iter()
        .filter(|event| {
            matches!(
                events.events[event.index()].kind,
                EventKind::Fire(_) | EventKind::OpaqueFire
            )
        })
        .count();
    let promoted_events = events
        .events
        .iter()
        .filter(|event| matches!(event.kind, EventKind::Fire(_) | EventKind::OpaqueFire))
        .count();
    let effective_output_rows = events
        .events
        .iter()
        .filter(|event| matches!(event.kind, EventKind::Fire(_) | EventKind::OpaqueFire))
        .map(|event| event.effective_outputs.len())
        .sum::<usize>();
    let captured_bindings = pending_fires
        .iter()
        .map(|fire| fire.grounding.bindings.len())
        .sum();
    let observation_bindings = check_batches
        .iter()
        .zip(&selected_checks)
        .map(|(batches, check)| {
            batches
                .iter()
                .map(|batch| batch.matches.len())
                .sum::<usize>()
                * check.var_sorts.len()
        })
        .sum();
    let pending_firings = pending_fires.len() + opaque_pending_firings;
    let stats = CausalSliceStats {
        source_facts: selected_source_facts.len(),
        observation_count: selected_checks.len(),
        waves: schedule_batches.len(),
        pending_firings,
        matched_applications,
        effective_applications,
        effective_output_rows,
        no_op_applications: pending_firings - effective_applications,
        promoted_events,
        retained_applications,
        source_events,
        dependency_nodes: dependencies.nodes.len(),
        witness_nodes: witnesses.nodes.len(),
        shared_replay_witnesses,
        equality_edges: equality_forest.edge_count(),
        prefix_fallbacks: retained_prefix_fallbacks,
        captured_bindings,
        observation_matches,
        observation_bindings,
        max_batch_matches,
        raw_trace_bindings,
        raw_trace_lower_bound_bytes: total_raw_matches * std::mem::size_of::<RuleMatch>()
            + raw_trace_bindings * std::mem::size_of::<(std::sync::Arc<str>, Value)>(),
        elaboration_time,
        slicing_time,
        emission_time,
        full_transcript_bytes: full_transcript_commands.as_ref().map_or(0, String::len),
        sliced_bytes: replay_commands.len(),
        ..CausalSliceStats::default()
    };
    Ok(RegionProjection {
        replay_commands,
        full_transcript_commands,
        stats,
        retained_source_facts,
        retained_rule_names,
        retained_witness_callables,
    })
}

fn add_region_stats(total: &mut CausalSliceStats, part: &CausalSliceStats) {
    total.source_facts += part.source_facts;
    total.observation_count += part.observation_count;
    total.waves += part.waves;
    total.pending_firings += part.pending_firings;
    total.matched_applications += part.matched_applications;
    total.effective_applications += part.effective_applications;
    total.effective_output_rows += part.effective_output_rows;
    total.no_op_applications += part.no_op_applications;
    total.promoted_events += part.promoted_events;
    total.retained_applications += part.retained_applications;
    total.source_events += part.source_events;
    total.dependency_nodes += part.dependency_nodes;
    total.witness_nodes += part.witness_nodes;
    total.shared_replay_witnesses += part.shared_replay_witnesses;
    total.equality_edges += part.equality_edges;
    total.prefix_fallbacks += part.prefix_fallbacks;
    total.captured_bindings += part.captured_bindings;
    total.observation_matches += part.observation_matches;
    total.observation_bindings += part.observation_bindings;
    total.max_batch_matches = total.max_batch_matches.max(part.max_batch_matches);
    total.raw_trace_bindings += part.raw_trace_bindings;
    total.raw_trace_lower_bound_bytes += part.raw_trace_lower_bound_bytes;
    total.elaboration_time += part.elaboration_time;
    total.slicing_time += part.slicing_time;
    total.emission_time += part.emission_time;
}

fn generate_scoped_causal_slice(
    input: ScopedGenerationInput<'_>,
) -> Result<GeneratedCausalSlice, CausalSliceError> {
    let ScopedGenerationInput {
        filename,
        input,
        source_name,
        mut egraph,
        validation_template,
        commands,
        mut rules,
        checks,
        source_facts,
        source_expansions,
        schedule_indices,
        regions,
        relations,
        constructors,
        mutable_functions,
        rule_mapping,
        preparation_time,
        include_full_transcript,
        source_projection,
        total_start,
    } = input;
    let mut schedule_regions = HashMap::default();
    let mut check_regions = HashMap::default();
    let mut pop_regions = HashMap::default();
    for (region_index, region) in regions.iter().enumerate() {
        for schedule in &region.schedule_indices {
            if schedule_regions.insert(*schedule, region_index).is_some() {
                return Err(CausalSliceError::Invariant(
                    "one schedule belongs to two scoped regions".to_owned(),
                ));
            }
        }
        for check in &region.check_command_indices {
            if check_regions.insert(*check, region_index).is_some() {
                return Err(CausalSliceError::Invariant(
                    "one check belongs to two scoped regions".to_owned(),
                ));
            }
        }
        let pop = region.pop_command_index.ok_or_else(|| {
            CausalSliceError::Invariant("scoped region lost its pop boundary".to_owned())
        })?;
        if pop_regions.insert(pop, region_index).is_some() {
            return Err(CausalSliceError::Invariant(
                "one pop belongs to two scoped regions".to_owned(),
            ));
        }
    }

    let mut schedule_batches = (0..regions.len())
        .map(|_| Vec::new())
        .collect::<Vec<Vec<RuleExecutionTrace>>>();
    let mut check_batches = (0..regions.len())
        .map(|_| Vec::new())
        .collect::<Vec<Vec<Vec<RuleExecutionTrace>>>>();
    let mut projections = (0..regions.len())
        .map(|_| None)
        .collect::<Vec<Option<RegionProjection>>>();
    let mut source_traces = IndexMap::default();
    let mut traced_run_time = Duration::ZERO;

    for (command_index, command) in commands.iter().cloned().enumerate() {
        if let Some(region_index) = schedule_regions.get(&command_index).copied() {
            let start = Instant::now();
            let batches = run_one_traced_command(&mut egraph, command, &mutable_functions)?;
            traced_run_time += start.elapsed();
            schedule_batches[region_index].extend(batches);
        } else if let Some(region_index) = check_regions.get(&command_index).copied() {
            let start = Instant::now();
            let batches = run_one_traced_command(&mut egraph, command, &mutable_functions)?;
            traced_run_time += start.elapsed();
            check_batches[region_index].push(batches);
        } else if let Some(region_index) = pop_regions.get(&command_index).copied() {
            let trace_functions =
                trace_function_metadata(&egraph, &relations, &constructors, &mutable_functions)?;
            let rule_primitives = resolve_rule_primitives(&egraph, &mut rules)?;
            let projection = slice_region(RegionSliceInput {
                egraph: &egraph,
                commands: &commands,
                source_name,
                region: &regions[region_index],
                rules: &rules,
                checks: &checks,
                relations: &relations,
                constructors: &constructors,
                source_facts: &source_facts,
                source_traces: &source_traces,
                schedule_batches: &schedule_batches[region_index],
                check_batches: &check_batches[region_index],
                trace_functions: &trace_functions,
                rule_primitives: &rule_primitives,
                include_full_transcript,
            })?;
            projections[region_index] = Some(projection);
            let start = Instant::now();
            egraph.run_program(vec![command])?;
            traced_run_time += start.elapsed();
        } else if let Some(expansion) = source_expansions.get(&command_index) {
            let start = Instant::now();
            egraph.run_program(expansion.clone())?;
            traced_run_time += start.elapsed();
        } else if matches!(command, Command::Action(..)) {
            let global_name = match &command {
                Command::Action(Action::Let(_, name, _)) => Some(name.clone()),
                _ => None,
            };
            let start = Instant::now();
            let batches = run_one_traced_command(&mut egraph, command, &mutable_functions)?;
            traced_run_time += start.elapsed();
            let global_endpoint = global_name
                .map(|name| {
                    let function = egraph.functions.get(&name).ok_or_else(|| {
                        CausalSliceError::Invariant(format!(
                            "source global `{name}` was not registered by its defining action"
                        ))
                    })?;
                    egraph
                        .backend
                        .lookup_id(function.backend_id, &[])
                        .ok_or_else(|| {
                            CausalSliceError::Invariant(format!(
                                "source global `{name}` has no value after its defining action"
                            ))
                        })
                })
                .transpose()?;
            source_traces.insert(
                command_index,
                SourceExecutionTrace {
                    batches,
                    global_endpoint,
                },
            );
        } else {
            let start = Instant::now();
            egraph.run_program(vec![command])?;
            traced_run_time += start.elapsed();
        }
    }

    let mut replay_by_schedule = IndexMap::default();
    let mut full_by_schedule = IndexMap::default();
    let mut stats = CausalSliceStats {
        original_bytes: input.len(),
        preparation_time,
        traced_run_time,
        ..CausalSliceStats::default()
    };
    let mut retained_source_facts = IndexSet::default();
    let mut retained_rule_names = IndexSet::default();
    let mut retained_witness_callables = IndexSet::default();
    for (region, projection) in regions.iter().zip(projections) {
        let projection = projection.ok_or_else(|| {
            CausalSliceError::Invariant("scoped region was never elaborated".to_owned())
        })?;
        let first_schedule = *region.schedule_indices.first().ok_or_else(|| {
            CausalSliceError::Invariant("scoped region lost its first schedule".to_owned())
        })?;
        replay_by_schedule.insert(first_schedule, projection.replay_commands);
        if let Some(full) = projection.full_transcript_commands {
            full_by_schedule.insert(first_schedule, full);
        }
        retained_source_facts.extend(projection.retained_source_facts);
        retained_rule_names.extend(projection.retained_rule_names);
        retained_witness_callables.extend(projection.retained_witness_callables);
        add_region_stats(&mut stats, &projection.stats);
    }

    let emission_start = Instant::now();
    let source = match source_projection {
        ReplaySourceProjection::Legacy => emit_program_with_replay_regions(
            &commands,
            &schedule_indices,
            &replay_by_schedule,
            &source_expansions,
        ),
        ReplaySourceProjection::PositiveChecks => emit_proof_program_with_replay_regions(
            &commands,
            &schedule_indices,
            &replay_by_schedule,
            &source_expansions,
            RetainedProofSource {
                facts: &source_facts,
                fact_ids: &retained_source_facts,
                rule_names: &retained_rule_names,
                witness_callables: &retained_witness_callables,
            },
        )?,
    };
    let full_transcript_source = include_full_transcript.then(|| {
        emit_program_with_replay_regions(
            &commands,
            &schedule_indices,
            &full_by_schedule,
            &source_expansions,
        )
    });
    stats.emission_time += emission_start.elapsed();

    let validation_start = Instant::now();
    if let Some(full) = &full_transcript_source {
        validate_emitted_program(
            &validation_template,
            filename.clone(),
            full,
            &rules,
            &rule_mapping,
            false,
        )?;
    }
    let emitted_mapping =
        filter_rule_mapping(&rule_mapping, source_projection, &retained_rule_names);
    validate_emitted_program(
        &validation_template,
        filename,
        &source,
        &rules,
        &emitted_mapping,
        source_projection == ReplaySourceProjection::PositiveChecks,
    )?;
    stats.emitted_validation_time = validation_start.elapsed();
    stats.sliced_bytes = source.len();
    stats.full_transcript_bytes = full_transcript_source.as_ref().map_or(0, String::len);
    stats.total_time = total_start.elapsed();
    Ok(GeneratedCausalSlice {
        source,
        full_transcript_source,
        stats,
        rule_mapping: emitted_mapping,
    })
}

fn generate_causal_slice(
    filename: Option<String>,
    input: &str,
    mut egraph: EGraph,
    include_full_transcript: bool,
    source_projection: ReplaySourceProjection,
) -> Result<GeneratedCausalSlice, CausalSliceError> {
    let total_start = Instant::now();
    let preparation_start = Instant::now();
    let validation_template = egraph.clone();
    let fact_directory = egraph.fact_directory.clone();
    let registered_presorts = egraph
        .type_info()
        .presort_names()
        .map(str::to_owned)
        .collect::<HashSet<_>>();
    // The in-place native trace currently requires one factorized join bag.
    // This changes only the physical plan used by the traced ordinary run;
    // emitted rule definitions retain their original source flags.
    egraph.no_decomp = true;
    egraph = egraph.with_union_to_set_optimization(false);
    let commands = normalize_parser_wildcards(egraph.parse_program(filename.clone(), input)?);
    let source_name = filename.as_deref().unwrap_or("<input>");
    let (mut commands, source_rule_origins) = lower_rewrites(commands, source_name)?;

    let (relations, constructors, mutable_functions) =
        collect_declarations(&commands, source_name, &registered_presorts)?;
    let rule_mapping = name_and_prepare_rules(&mut commands, source_name, &source_rule_origins)?;
    let resolved_source = if commands
        .iter()
        .any(|command| matches!(command, Command::Rule { .. }))
    {
        let mut modeling_egraph = egraph.clone();
        resolved_source_model_for_modeling(
            &commands,
            modeling_egraph.resolve_commands_for_modeling(commands.clone())?,
        )?
    } else {
        ResolvedSourceModel {
            rules: IndexMap::default(),
            actions: Vec::new(),
            checks: Vec::new(),
        }
    };
    let ProgramModel {
        mut rules,
        checks,
        source_facts,
        constructors,
        mutable_functions,
        source_expansions,
        schedule_indices,
        regions,
        prefix_fallbacks,
    } = validate_and_model(
        &commands,
        &resolved_source,
        ModelDeclarations {
            relations: &relations,
            constructors: &constructors,
            mutable_functions: &mutable_functions,
        },
        &source_rule_origins,
        &registered_presorts,
        source_name,
        fact_directory.as_deref(),
    )?;
    if source_projection == ReplaySourceProjection::PositiveChecks && checks.is_empty() {
        return Err(CausalSliceError::Unsupported {
            location: source_name.to_owned(),
            reason: "proof-oriented source projection without a positive check".to_owned(),
        });
    }
    let preparation_time = preparation_start.elapsed();

    if regions
        .iter()
        .any(|region| region.pop_command_index.is_some())
    {
        return generate_scoped_causal_slice(ScopedGenerationInput {
            filename: filename.clone(),
            input,
            source_name,
            egraph,
            validation_template,
            commands,
            rules,
            checks,
            source_facts,
            source_expansions,
            schedule_indices,
            regions,
            relations,
            constructors,
            mutable_functions,
            rule_mapping,
            preparation_time,
            include_full_transcript,
            source_projection,
            total_start,
        });
    }

    let trace_start = Instant::now();
    let mut schedule_batches = Vec::new();
    let mut check_batches = Vec::new();
    let mut source_traces = IndexMap::default();

    for (command_index, command) in commands.iter().cloned().enumerate() {
        if schedule_indices.contains(&command_index) {
            let batches = run_one_traced_command(&mut egraph, command, &mutable_functions)?;
            schedule_batches.extend(batches);
        } else if matches!(command, Command::Check(..)) {
            check_batches.push(run_one_traced_command(
                &mut egraph,
                command,
                &mutable_functions,
            )?);
        } else if let Some(expansion) = source_expansions.get(&command_index) {
            egraph.run_program(expansion.clone())?;
        } else if matches!(command, Command::Action(..)) {
            let global_name = match &command {
                Command::Action(Action::Let(_, name, _)) => Some(name.clone()),
                _ => None,
            };
            let batches = run_one_traced_command(&mut egraph, command, &mutable_functions)?;
            let global_endpoint = global_name
                .map(|name| {
                    let function = egraph.functions.get(&name).ok_or_else(|| {
                        CausalSliceError::Invariant(format!(
                            "source global `{name}` was not registered by its defining action"
                        ))
                    })?;
                    egraph
                        .backend
                        .lookup_id(function.backend_id, &[])
                        .ok_or_else(|| {
                            CausalSliceError::Invariant(format!(
                                "source global `{name}` has no value after its defining action"
                            ))
                        })
                })
                .transpose()?;
            source_traces.insert(
                command_index,
                SourceExecutionTrace {
                    batches,
                    global_endpoint,
                },
            );
        } else {
            egraph.run_program(vec![command])?;
        }
    }
    let traced_run_time = trace_start.elapsed();
    let elaboration_start = Instant::now();
    let schedule_index = *schedule_indices
        .first()
        .ok_or_else(|| CausalSliceError::Invariant("validated schedules disappeared".to_owned()))?;
    let waves = schedule_batches.len();
    let observation_matches = check_batches
        .iter()
        .flat_map(|batches| batches.iter())
        .map(|batch| batch.matches.len())
        .sum::<usize>();
    let observation_trace_bindings = check_batches
        .iter()
        .flat_map(|batches| batches.iter())
        .flat_map(|batch| &batch.matches)
        .map(|event| event.bindings.len())
        .sum::<usize>();
    let schedule_trace_bindings = schedule_batches
        .iter()
        .flat_map(|batch| &batch.matches)
        .map(|event| event.bindings.len())
        .sum::<usize>();
    let matched_applications = schedule_batches
        .iter()
        .map(|batch| batch.matches.len())
        .sum::<usize>();
    let max_batch_matches = schedule_batches
        .iter()
        .chain(check_batches.iter().flat_map(|batches| batches.iter()))
        .map(|batch| batch.matches.len())
        .max()
        .unwrap_or(0);
    let total_raw_matches = schedule_batches
        .iter()
        .map(|batch| batch.matches.len())
        .sum::<usize>()
        + observation_matches;
    let raw_trace_bindings = schedule_trace_bindings + observation_trace_bindings;
    let raw_trace_lower_bound_bytes = total_raw_matches * std::mem::size_of::<RuleMatch>()
        + raw_trace_bindings * std::mem::size_of::<(std::sync::Arc<str>, Value)>();

    let trace_functions =
        trace_function_metadata(&egraph, &relations, &constructors, &mutable_functions)?;
    let rule_primitives = resolve_rule_primitives(&egraph, &mut rules)?;
    let mut witnesses = WitnessArena::default();
    let schedule_span = command_schedule_span(&commands[schedule_index])
        .ok_or_else(|| CausalSliceError::Invariant("schedule command lost its span".to_owned()))?;
    if prefix_fallbacks > 0 && !include_full_transcript {
        if !checks.is_empty() || !check_batches.is_empty() {
            return Err(CausalSliceError::Invariant(
                "a Prefix-only replay unexpectedly retained positive-check traces".to_owned(),
            ));
        }
        let PrefixElaboration {
            replay_fires,
            pending_firings,
            captured_bindings,
            effective_applications,
            effective_output_rows,
            source_events,
            witness_nodes,
            equality_edges,
        } = elaborate_prefix_replay(
            PrefixElaborationInput {
                egraph: &egraph,
                rules: &rules,
                rule_primitives: &rule_primitives,
                relations: &relations,
                source_facts: &source_facts,
                source_traces: &source_traces,
                batches: schedule_batches,
                trace_functions: &trace_functions,
            },
            &mut witnesses,
        )?;
        let elaboration_time = elaboration_start.elapsed();
        let slicing_time = Duration::ZERO;

        let emission_start = Instant::now();
        let (replay_commands, shared_replay_witnesses) = emit_prefix_replay_commands(
            &commands,
            &schedule_span,
            &rules,
            &replay_fires,
            &witnesses,
        )?;
        let source = emit_program_with_replay_commands(
            &commands,
            &schedule_indices,
            &replay_commands,
            &source_expansions,
        );
        let emission_time = emission_start.elapsed();

        let emitted_validation_start = Instant::now();
        validate_emitted_program(
            &validation_template,
            filename,
            &source,
            &rules,
            &rule_mapping,
            false,
        )?;
        let emitted_validation_time = emitted_validation_start.elapsed();
        let total_time = total_start.elapsed();
        let stats = CausalSliceStats {
            original_bytes: input.len(),
            source_facts: source_facts.len(),
            observation_count: 0,
            waves,
            pending_firings,
            matched_applications,
            effective_applications,
            effective_output_rows,
            no_op_applications: pending_firings - effective_applications,
            promoted_events: replay_fires.len(),
            retained_applications: replay_fires.len(),
            source_events,
            dependency_nodes: 0,
            witness_nodes,
            shared_replay_witnesses,
            equality_edges,
            prefix_fallbacks,
            captured_bindings,
            observation_matches,
            observation_bindings: 0,
            max_batch_matches,
            raw_trace_bindings,
            raw_trace_lower_bound_bytes,
            preparation_time,
            traced_run_time,
            elaboration_time,
            slicing_time,
            emission_time,
            emitted_validation_time,
            total_time,
            full_transcript_bytes: 0,
            sliced_bytes: source.len(),
        };
        return Ok(GeneratedCausalSlice {
            source,
            full_transcript_source: None,
            stats,
            rule_mapping,
        });
    }
    let Elaboration {
        pending_fires,
        opaque_pending_firings,
        opaque_promoted_events,
        events,
        mut dependencies,
        producers: final_producers,
        source_events,
        equality_forest,
        opaque_equality_error,
        causal_prefix_fallbacks,
    } = elaborate_events(
        ElaborationInput {
            egraph: &egraph,
            rules: &rules,
            rule_primitives: &rule_primitives,
            relations: &relations,
            source_facts: &source_facts,
            source_traces: &source_traces,
            batches: &schedule_batches,
            trace_functions: &trace_functions,
            prefix_fallback: prefix_fallbacks > 0,
        },
        &mut witnesses,
    )?;
    let elaboration_time = elaboration_start.elapsed();
    let slicing_start = Instant::now();
    let roots = observation_roots(
        ObservationInput {
            egraph: &egraph,
            checks: &checks,
            relations: &relations,
            constructors: &constructors,
            traces: &check_batches,
            producers: &final_producers,
            equality_forest: &equality_forest,
            opaque_equality_error: opaque_equality_error.as_ref(),
        },
        &mut dependencies,
        &mut witnesses,
    )?;
    let captured_bindings = pending_fires
        .iter()
        .map(|fire| fire.grounding.bindings.len())
        .sum();
    let observation_bindings = check_batches
        .iter()
        .zip(&checks)
        .map(|(batches, check)| {
            batches
                .iter()
                .map(|batch| batch.matches.len())
                .sum::<usize>()
                * check.var_sorts.len()
        })
        .sum();
    let (retained, retained_causal_prefix_fallbacks) = if prefix_fallbacks > 0 {
        let mut retained = IndexSet::default();
        for index in 0..events.events.len() {
            retained.insert(EventId(u32::try_from(index).map_err(|_| {
                CausalSliceError::Invariant("event index exceeded u32 capacity".to_owned())
            })?));
        }
        (retained, 0)
    } else {
        backward_slice(&events, &dependencies, &equality_forest, roots)?
    };
    debug_assert!(retained_causal_prefix_fallbacks <= causal_prefix_fallbacks);
    if prefix_fallbacks == 0
        && let Some(error) = retained.iter().find_map(|event| {
            events.events[event.index()]
                .deferred_prerequisite_error
                .clone()
        })
    {
        return Err(error.into_error());
    }
    let retained_source_facts = retained
        .iter()
        .filter_map(|event| match events.events[event.index()].kind {
            EventKind::Source { fact } => Some(fact),
            EventKind::Fire(_) | EventKind::OpaqueFire => None,
        })
        .collect::<IndexSet<_>>();
    let retained_rule_names = retained
        .iter()
        .filter_map(|event| match &events.events[event.index()].kind {
            EventKind::Fire(fire) => Some(fire.rule.clone()),
            EventKind::Source { .. } | EventKind::OpaqueFire => None,
        })
        .collect::<IndexSet<_>>();
    if include_full_transcript && opaque_pending_firings > 0 {
        return Err(CausalSliceError::Unsupported {
            location: source_name.to_owned(),
            reason: "a diagnostic full transcript containing opaque rule groundings; use the retained replay projection so unreachable unsupported rules can be sliced away"
                .to_owned(),
        });
    }
    drop(schedule_batches);
    drop(check_batches);
    let slicing_time = slicing_start.elapsed();

    let emission_start = Instant::now();
    let full_transcript_source = if include_full_transcript {
        Some(
            emit_program(
                &commands,
                &schedule_indices,
                &schedule_span,
                &rules,
                pending_fires.iter().map(|fire| &fire.grounding),
                &witnesses,
                &source_expansions,
            )?
            .0,
        )
    } else {
        None
    };
    let replay_fires = retained
        .iter()
        .filter_map(|event| match &events.events[event.index()].kind {
            EventKind::Source { .. } => None,
            EventKind::Fire(fire) => Some(fire),
            EventKind::OpaqueFire => None,
        })
        .collect::<Vec<_>>();
    let retained_witness_callables =
        replay_witness_callables(replay_fires.iter().copied(), &witnesses)?;
    let (replay_commands, shared_replay_witnesses) =
        render_replay_commands(&commands, &schedule_span, &rules, replay_fires, &witnesses)?;
    let source = match source_projection {
        ReplaySourceProjection::Legacy => emit_program_with_replay_commands(
            &commands,
            &schedule_indices,
            &replay_commands,
            &source_expansions,
        ),
        ReplaySourceProjection::PositiveChecks => {
            let mut replay_by_schedule = IndexMap::default();
            replay_by_schedule.insert(schedule_index, replay_commands);
            emit_proof_program_with_replay_regions(
                &commands,
                &schedule_indices,
                &replay_by_schedule,
                &source_expansions,
                RetainedProofSource {
                    facts: &source_facts,
                    fact_ids: &retained_source_facts,
                    rule_names: &retained_rule_names,
                    witness_callables: &retained_witness_callables,
                },
            )?
        }
    };
    let emission_time = emission_start.elapsed();

    let emitted_validation_start = Instant::now();
    if let Some(full_transcript_source) = &full_transcript_source {
        validate_emitted_program(
            &validation_template,
            filename.clone(),
            full_transcript_source,
            &rules,
            &rule_mapping,
            false,
        )?;
    }
    let emitted_mapping =
        filter_rule_mapping(&rule_mapping, source_projection, &retained_rule_names);
    validate_emitted_program(
        &validation_template,
        filename,
        &source,
        &rules,
        &emitted_mapping,
        source_projection == ReplaySourceProjection::PositiveChecks,
    )?;
    let emitted_validation_time = emitted_validation_start.elapsed();

    let effective_applications =
        pending_fires.iter().filter(|fire| fire.effective).count() + opaque_promoted_events;
    let retained_applications = retained
        .iter()
        .filter(|event| {
            matches!(
                events.events[event.index()].kind,
                EventKind::Fire(_) | EventKind::OpaqueFire
            )
        })
        .count();
    let promoted_events = events
        .events
        .iter()
        .filter(|event| matches!(event.kind, EventKind::Fire(_) | EventKind::OpaqueFire))
        .count();
    let effective_output_rows = events
        .events
        .iter()
        .filter(|event| matches!(event.kind, EventKind::Fire(_) | EventKind::OpaqueFire))
        .map(|event| event.effective_outputs.len())
        .sum::<usize>();
    let total_time = total_start.elapsed();
    let stats = CausalSliceStats {
        original_bytes: input.len(),
        source_facts: source_facts.len(),
        observation_count: checks.len(),
        waves,
        pending_firings: pending_fires.len() + opaque_pending_firings,
        matched_applications,
        effective_applications,
        effective_output_rows,
        no_op_applications: pending_fires.len() + opaque_pending_firings - effective_applications,
        promoted_events,
        retained_applications,
        source_events,
        dependency_nodes: dependencies.nodes.len(),
        witness_nodes: witnesses.nodes.len(),
        shared_replay_witnesses,
        equality_edges: equality_forest.edge_count(),
        prefix_fallbacks: prefix_fallbacks + retained_causal_prefix_fallbacks,
        captured_bindings,
        observation_matches,
        observation_bindings,
        max_batch_matches,
        raw_trace_bindings,
        raw_trace_lower_bound_bytes,
        preparation_time,
        traced_run_time,
        elaboration_time,
        slicing_time,
        emission_time,
        emitted_validation_time,
        total_time,
        full_transcript_bytes: full_transcript_source.as_ref().map_or(0, String::len),
        sliced_bytes: source.len(),
    };

    Ok(GeneratedCausalSlice {
        source,
        full_transcript_source,
        stats,
        rule_mapping: emitted_mapping,
    })
}

fn resolved_source_model_for_modeling(
    source_commands: &[Command],
    commands: Vec<ResolvedNCommand>,
) -> Result<ResolvedSourceModel, CausalSliceError> {
    let mut rules = IndexMap::default();
    let mut actions = Vec::new();
    let mut checks = Vec::new();
    for command in commands {
        match command {
            ResolvedNCommand::NormRule { rule } => {
                let name = rule.name.clone();
                if rules.insert(name.clone(), rule).is_some() {
                    return Err(CausalSliceError::Invariant(format!(
                        "typed source model produced duplicate rule `{name}`"
                    )));
                }
            }
            ResolvedNCommand::Check(_, facts) => checks.push(facts),
            ResolvedNCommand::CoreAction(action) => actions.push(action),
            _ => {}
        }
    }
    let expected = source_commands
        .iter()
        .filter_map(|command| match command {
            Command::Rule { rule } => Some(rule.name.as_str()),
            _ => None,
        })
        .collect::<IndexSet<_>>();
    let actual = rules.keys().map(String::as_str).collect::<IndexSet<_>>();
    if actual != expected {
        return Err(CausalSliceError::Invariant(format!(
            "typed source rule identities diverged: expected {expected:?}, found {actual:?}"
        )));
    }
    let expected_checks = source_commands
        .iter()
        .filter(|command| matches!(command, Command::Check(..)))
        .count();
    if checks.len() != expected_checks {
        return Err(CausalSliceError::Invariant(format!(
            "typed source check count diverged: expected {expected_checks}, found {}",
            checks.len()
        )));
    }
    let expected_actions = source_commands
        .iter()
        .filter(|command| matches!(command, Command::Action(..)))
        .count();
    if actions.len() != expected_actions {
        return Err(CausalSliceError::Invariant(format!(
            "typed source action count diverged: expected {expected_actions}, found {}",
            actions.len()
        )));
    }
    Ok(ResolvedSourceModel {
        rules,
        actions,
        checks,
    })
}

fn normalize_parser_wildcards(commands: Vec<Command>) -> Vec<Command> {
    fn is_parser_wildcard(symbol: &str) -> bool {
        symbol.strip_prefix("@_").is_some_and(|suffix| {
            suffix.is_empty() || suffix.bytes().all(|byte| byte.is_ascii_digit())
        })
    }

    let mut used = HashSet::default();
    for command in &commands {
        let mut heads = Vec::new();
        let mut leaves = Vec::new();
        command.clone().map_symbols(
            &mut |head| {
                heads.push(head.clone());
                head
            },
            &mut |leaf| {
                if !is_parser_wildcard(&leaf) {
                    leaves.push(leaf.clone());
                }
                leaf
            },
        );
        used.extend(heads);
        used.extend(leaves);
        command.clone().map_string_symbols(&mut |symbol| {
            used.insert(symbol.clone());
            symbol
        });
    }

    let mut replacements = IndexMap::<String, String>::default();
    let mut ordinal = 0usize;
    commands
        .into_iter()
        .map(|command| {
            command.map_symbols(&mut |head| head, &mut |leaf| {
                if !is_parser_wildcard(&leaf) {
                    return leaf;
                }
                if let Some(replacement) = replacements.get(&leaf) {
                    return replacement.clone();
                }
                loop {
                    let candidate = format!("__causal_slice_v0_wildcard_{ordinal}");
                    ordinal += 1;
                    if used.insert(candidate.clone()) {
                        replacements.insert(leaf, candidate.clone());
                        return candidate;
                    }
                }
            })
        })
        .collect()
}

fn run_one_traced_command(
    egraph: &mut EGraph,
    command: Command,
    mutable_functions: &IndexMap<String, MutableFunctionDecl>,
) -> Result<Vec<RuleExecutionTrace>, CausalSliceError> {
    let trace_check_constructor_rows = matches!(&command, Command::Check(..));
    let globals = egraph
        .functions
        .iter()
        .filter(|(_, function)| function.is_let_binding())
        .map(|(name, function)| {
            (
                std::sync::Arc::<str>::from(name.as_str()),
                function.backend_id,
            )
        })
        .collect();
    let mutation_functions = egraph
        .functions
        .iter()
        .filter(|(name, function)| {
            mutable_functions.contains_key(*name)
                && function.subtype() == FunctionSubtype::Custom
                && !function.is_let_binding()
                && !function.is_hidden()
                && function.term_constructor().is_none()
        })
        .map(|(_, function)| function.backend_id)
        .collect();
    let native = egraph
        .backend
        .as_any_mut()
        .downcast_mut::<egglog_bridge::EGraph>()
        .ok_or_else(|| {
            CausalSliceError::Invariant(
                "causal tracing is implemented only by the reference backend".to_owned(),
            )
        })?;
    native
        .begin_rule_match_trace_with_globals_and_mutations(globals, mutation_functions)
        .map_err(|error| CausalSliceError::Invariant(error.to_string()))?;

    egraph.trace_check_constructor_rows = trace_check_constructor_rows;
    let result = egraph.run_program(vec![command]);
    egraph.trace_check_constructor_rows = false;
    let mut batches = egraph
        .backend
        .as_any_mut()
        .downcast_mut::<egglog_bridge::EGraph>()
        .expect("the backend type cannot change during one command")
        .take_rule_match_trace()
        .expect("the trace was started immediately above");
    result?;
    restore_projected_source_bindings(egraph, &mut batches)?;
    Ok(batches)
}

fn restore_projected_source_bindings(
    egraph: &EGraph,
    batches: &mut [RuleExecutionTrace],
) -> Result<(), CausalSliceError> {
    for batch in batches {
        for captured in &mut batch.matches {
            let Some(substitutions) = egraph.rulesets.values().find_map(|ruleset| match ruleset {
                Ruleset::Rules(rules) => rules
                    .get(captured.rule.as_ref())
                    .map(|registered| registered.substitutions.as_ref()),
                Ruleset::Combined(..) => None,
            }) else {
                // Command-level source actions use a synthetic native rule
                // name and have no source-rule canonicalization aliases.
                continue;
            };
            let mut values = captured
                .bindings
                .iter()
                .map(|(name, value)| (name.to_string(), *value))
                .collect::<HashMap<_, _>>();
            for (source, _) in substitutions {
                if values.contains_key(&source.name) {
                    continue;
                }
                let Some(value) = resolve_substitution_value(
                    source,
                    substitutions,
                    &values,
                    egraph.backend.base_values(),
                ) else {
                    continue;
                };
                captured
                    .bindings
                    .push((std::sync::Arc::from(source.name.as_str()), value));
                values.insert(source.name.clone(), value);
            }
        }
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum RegisteredAliasTarget {
    Variable { name: String, sort: String },
    Literal { literal: Literal, sort: String },
}

fn registered_alias_target(
    rule_name: &str,
    source_name: &str,
    source_sort: &str,
    substitutions: &[(ResolvedVar, crate::core::ResolvedAtomTerm)],
) -> Result<RegisteredAliasTarget, CausalSliceError> {
    let mut name = source_name.to_owned();
    let mut sort = source_sort.to_owned();
    let mut visited = HashSet::default();
    for _ in 0..=substitutions.len() {
        if !visited.insert((name.clone(), sort.clone())) {
            return Err(CausalSliceError::Invariant(format!(
                "registered substitutions for rule `{rule_name}` contain a cycle at `{name}`"
            )));
        }
        let mut matching = substitutions
            .iter()
            .filter(|(candidate, _)| candidate.name == name && candidate.sort.name() == sort);
        let Some((_, target)) = matching.next() else {
            return Ok(RegisteredAliasTarget::Variable { name, sort });
        };
        if matching.next().is_some() {
            return Err(CausalSliceError::Invariant(format!(
                "registered substitutions for rule `{rule_name}` contain multiple targets for `{name}`"
            )));
        }
        match target {
            crate::core::GenericAtomTerm::Var(_, variable) => {
                name = variable.name.clone();
                sort = variable.sort.name().to_owned();
            }
            crate::core::GenericAtomTerm::Literal(_, literal) => {
                return Ok(RegisteredAliasTarget::Literal {
                    literal: literal.clone(),
                    sort,
                });
            }
            crate::core::GenericAtomTerm::Global(_, variable) => {
                return Err(CausalSliceError::Unsupported {
                    location: format!("registered rule `{rule_name}`"),
                    reason: format!(
                        "replay binding `{source_name}` resolves to unsupported global alias `{}`",
                        variable.name
                    ),
                });
            }
        }
    }
    Err(CausalSliceError::Invariant(format!(
        "registered substitutions for rule `{rule_name}` exceed their finite alias chain"
    )))
}

fn validate_registered_replay_aliases(
    rule_name: &str,
    model: &RuleModel,
    substitutions: &[(ResolvedVar, crate::core::ResolvedAtomTerm)],
) -> Result<(), CausalSliceError> {
    for (derived, expected) in &model.derived_replay_aliases {
        let derived_sort = model.var_sorts.get(derived).ok_or_else(|| {
            CausalSliceError::Invariant(format!(
                "typed source model lost sort for derived replay variable `{derived}` in rule `{rule_name}`"
            ))
        })?;
        let expected_sort = model.var_sorts.get(expected).ok_or_else(|| {
            CausalSliceError::Invariant(format!(
                "typed source model lost sort for replay alias `{expected}` in rule `{rule_name}`"
            ))
        })?;
        if derived_sort != expected_sort {
            return Err(CausalSliceError::Invariant(format!(
                "typed replay alias `{derived}` -> `{expected}` changes sort in rule `{rule_name}`"
            )));
        }
        let actual = registered_alias_target(rule_name, derived, derived_sort, substitutions)?;
        let expected = registered_alias_target(rule_name, expected, expected_sort, substitutions)?;
        if actual != expected {
            return Err(CausalSliceError::Invariant(format!(
                "typed replay alias `{derived}` does not match the registered substitution in rule `{rule_name}`: expected {expected:?}, found {actual:?}"
            )));
        }
    }
    Ok(())
}

fn resolve_rule_primitives(
    egraph: &EGraph,
    rules: &mut IndexMap<String, RuleModel>,
) -> Result<IndexMap<String, ResolvedRulePrimitives>, CausalSliceError> {
    let mut resolved = IndexMap::default();
    let rule_names = rules.keys().cloned().collect::<Vec<_>>();
    for rule_name in &rule_names {
        let resolution = (|| -> Result<ResolvedRulePrimitives, CausalSliceError> {
            let model = &rules[rule_name];
            if model.opaque.is_some() {
                return Ok(ResolvedRulePrimitives::default());
            }
            let registered = egraph
                .rulesets
                .values()
                .find_map(|ruleset| match ruleset {
                    Ruleset::Rules(registered) => registered.get(rule_name),
                    Ruleset::Combined(..) => None,
                })
                .ok_or_else(|| {
                    CausalSliceError::Invariant(format!(
                        "modeled rule `{rule_name}` was not registered by the traced program"
                    ))
                })?;
            validate_registered_replay_aliases(rule_name, model, &registered.substitutions)?;
            let registered_body = registered
                .core
                .body
                .atoms
                .iter()
                .filter_map(|atom| match &atom.head {
                    ResolvedCall::Primitive(primitive) => Some(primitive),
                    _ => None,
                })
                .collect::<Vec<_>>();
            let mut body = Vec::with_capacity(registered_body.len());
            let mut expected = model.body_primitives.iter().peekable();
            for primitive in registered_body {
                let exact_logical = expected
                    .peek()
                    .is_some_and(|expected| expected.capability.matches(primitive));
                let query_auxiliary = resolved_auxiliary_scalar_primitive(primitive);
                if (!exact_logical && query_auxiliary.is_none())
                    || primitive.validator().is_none()
                    || primitive.effect() != crate::PrimitiveEffect::Pure
                    || !primitive.is_replay_safe()
                {
                    return unsupported(
                        &model.span,
                        format!(
                            "rule `{rule_name}` query primitive without an exact deterministic proof-validating specialization"
                        ),
                    );
                }
                if exact_logical {
                    let _ = expected.next();
                }
                body.push(RulePrimitiveMeta {
                    function: primitive.external_id(crate::Context::Pure),
                    logical_query: exact_logical,
                    query_auxiliary,
                });
            }
            if let Some(expected) = expected.next() {
                return unsupported(
                    &model.span,
                    format!(
                        "rule `{rule_name}` lost modeled query primitive `{}` ({:?} -> {}) during lowering",
                        expected.capability.specialization.name(),
                        expected
                            .capability
                            .specialization
                            .input()
                            .iter()
                            .map(|sort| sort.name())
                            .collect::<Vec<_>>(),
                        expected.capability.specialization.output().name(),
                    ),
                );
            }

            let registered_head = registered
                .core
                .head
                .0
                .iter()
                .filter_map(|action| match action {
                    GenericCoreAction::Let(_, _, ResolvedCall::Primitive(primitive), _)
                    | GenericCoreAction::Set(_, ResolvedCall::Primitive(primitive), _, _)
                    | GenericCoreAction::Change(_, _, ResolvedCall::Primitive(primitive), _) => {
                        Some(primitive)
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            let mut head = Vec::with_capacity(registered_head.len());
            let mut expected_head = model.head_primitives.iter().peekable();
            for primitive in registered_head {
                let exact_source_occurrence = expected_head.peek().is_some_and(|expected| {
                    matches!(
                        expected,
                        AtomArg::App {
                            primitive: Some(capability),
                            ..
                        } if capability.matches(primitive)
                    )
                });
                if exact_source_occurrence {
                    let _ = expected_head.next();
                    head.push(RulePrimitiveMeta {
                        function: primitive.external_id(crate::Context::Write),
                        logical_query: false,
                        query_auxiliary: None,
                    });
                    continue;
                }
                let legacy_bigrat_occurrence = expected_head.peek().is_some_and(|expected| {
                    matches!(
                        expected,
                        AtomArg::App {
                            function,
                            input_sorts,
                            output_sort,
                            primitive: None,
                            ..
                        } if primitive.name() == function
                            && replay_safe_bigrat_primitive_arity(function)
                                == Some(input_sorts.len())
                            && primitive.input().len() == input_sorts.len()
                            && primitive
                                .input()
                                .iter()
                                .zip(input_sorts)
                                .all(|(actual, expected)| actual.name() == expected)
                            && primitive.output().name() == output_sort
                            && primitive.effect() == crate::PrimitiveEffect::Pure
                            && primitive.validator().is_some()
                            && primitive.is_replay_safe()
                    )
                });
                if legacy_bigrat_occurrence {
                    let _ = expected_head.next();
                    head.push(RulePrimitiveMeta {
                        function: primitive.external_id(crate::Context::Write),
                        logical_query: false,
                        query_auxiliary: None,
                    });
                    continue;
                }
                if let Some(query_auxiliary) = resolved_auxiliary_scalar_primitive(primitive) {
                    if primitive.effect() != crate::PrimitiveEffect::Pure
                        || primitive.validator().is_none()
                        || !primitive.is_replay_safe()
                    {
                        return unsupported(
                            &model.span,
                            format!(
                                "rule `{rule_name}` auxiliary head primitive without a deterministic proof validator"
                            ),
                        );
                    }
                    head.push(RulePrimitiveMeta {
                        function: primitive.external_id(crate::Context::Write),
                        logical_query: false,
                        query_auxiliary: Some(query_auxiliary),
                    });
                    continue;
                }
                return unsupported(
                    &model.span,
                    format!(
                        "rule `{rule_name}` lowered primitive `{}` ({:?} -> {}) without an exact typed source occurrence",
                        primitive.name(),
                        primitive
                            .input()
                            .iter()
                            .map(|sort| sort.name())
                            .collect::<Vec<_>>(),
                        primitive.output().name(),
                    ),
                );
            }
            if expected_head.next().is_some() {
                return Err(CausalSliceError::Invariant(format!(
                    "rule `{rule_name}` lost a modeled head primitive during lowering"
                )));
            }
            Ok(ResolvedRulePrimitives {
                body,
                head,
                core_head: registered.core.head.clone(),
                substitutions: registered.substitutions.clone(),
            })
        })();
        match resolution {
            Ok(metadata) => {
                resolved.insert(rule_name.clone(), metadata);
            }
            Err(CausalSliceError::Unsupported { location, reason }) => {
                let model = &rules[rule_name];
                if !lowering_mismatch_can_be_deferred(egraph, rule_name, model) {
                    return Err(CausalSliceError::Unsupported { location, reason });
                }
                log::debug!(
                    "causal lowering model deferred rule `{rule_name}` at {location}: {reason}"
                );
                rules
                    .get_mut(rule_name)
                    .expect("rule name came from this map")
                    .opaque = Some(OpaqueRulePolicy::Reject(DeferredUnsupported {
                    location,
                    reason,
                }));
                resolved.insert(rule_name.clone(), ResolvedRulePrimitives::default());
            }
            Err(error) => return Err(error),
        }
    }
    Ok(resolved)
}

fn lowering_mismatch_can_be_deferred(egraph: &EGraph, rule_name: &str, model: &RuleModel) -> bool {
    if !model.head_subsumes.is_empty() {
        return false;
    }
    let Some(registered) = egraph.rulesets.values().find_map(|ruleset| match ruleset {
        Ruleset::Rules(rules) => rules.get(rule_name),
        Ruleset::Combined(..) => None,
    }) else {
        return false;
    };
    let body_primitives = registered.core.body.atoms.iter().filter_map(|atom| {
        if let ResolvedCall::Primitive(primitive) = &atom.head {
            Some(primitive)
        } else {
            None
        }
    });
    let head_primitives = registered
        .core
        .head
        .0
        .iter()
        .filter_map(|action| match action {
            GenericCoreAction::Let(_, _, ResolvedCall::Primitive(primitive), _)
            | GenericCoreAction::Set(_, ResolvedCall::Primitive(primitive), _, _)
            | GenericCoreAction::Change(_, _, ResolvedCall::Primitive(primitive), _) => {
                Some(primitive)
            }
            _ => None,
        });
    body_primitives.chain(head_primitives).all(|primitive| {
        primitive.effect() == crate::PrimitiveEffect::Pure
            && primitive.validator().is_some()
            && primitive.is_replay_safe()
    })
}

fn resolved_auxiliary_scalar_primitive(
    primitive: &crate::core::SpecializedPrimitive,
) -> Option<QueryAuxiliaryPrimitive> {
    match primitive.name() {
        "bigint" => (primitive.input().len() == 1
            && primitive.input()[0].name() == "i64"
            && primitive.output().name() == "BigInt")
            .then_some(QueryAuxiliaryPrimitive::BigInt),
        "bigrat" => (primitive.input().len() == 2
            && primitive.input().iter().all(|sort| sort.name() == "BigInt")
            && primitive.output().name() == "BigRat")
            .then_some(QueryAuxiliaryPrimitive::BigRat),
        _ => None,
    }
}

fn resolve_auxiliary_scalar_function(
    egraph: &EGraph,
    function: &str,
    context: crate::Context,
) -> Result<(QueryAuxiliaryPrimitive, ExternalFunctionId), CausalSliceError> {
    let (kind, signature) = match function {
        "bigint" => (QueryAuxiliaryPrimitive::BigInt, &["i64", "BigInt"][..]),
        "bigrat" => (
            QueryAuxiliaryPrimitive::BigRat,
            &["BigInt", "BigInt", "BigRat"][..],
        ),
        _ => {
            return Err(CausalSliceError::Invariant(format!(
                "`{function}` is not an auxiliary scalar constructor"
            )));
        }
    };
    let sorts = signature
        .iter()
        .map(|name| {
            egraph.get_sort_by_name(name).cloned().ok_or_else(|| {
                CausalSliceError::Invariant(format!("runtime sort `{name}` disappeared"))
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut candidates = egraph
        .type_info
        .get_prims(function)
        .into_iter()
        .flatten()
        .filter(|primitive| {
            primitive.context_ids[context].is_some()
                && primitive.validator.is_some()
                && primitive.accept(&sorts, &egraph.type_info)
        });
    let Some(candidate) = candidates.next() else {
        return Err(CausalSliceError::Invariant(format!(
            "auxiliary scalar constructor `{function}` has no exact proof-validating runtime specialization"
        )));
    };
    if candidates.next().is_some() {
        return Err(CausalSliceError::Invariant(format!(
            "auxiliary scalar constructor `{function}` has ambiguous runtime specializations"
        )));
    }
    Ok((
        kind,
        candidate.context_ids[context].expect("filtered as present"),
    ))
}

fn resolve_substitution_value(
    source: &crate::ast::ResolvedVar,
    substitutions: &[(crate::ast::ResolvedVar, crate::core::ResolvedAtomTerm)],
    values: &HashMap<String, Value>,
    base_values: &crate::core_relations::BaseValues,
) -> Option<Value> {
    let mut current = substitutions
        .iter()
        .find(|(candidate, _)| candidate == source)
        .map(|(_, target)| target)?;
    for _ in 0..=substitutions.len() {
        match current {
            crate::core::GenericAtomTerm::Var(_, variable)
            | crate::core::GenericAtomTerm::Global(_, variable) => {
                if let Some(value) = values.get(variable.name.as_str()) {
                    return Some(*value);
                }
                current = substitutions
                    .iter()
                    .find(|(candidate, _)| candidate == variable)
                    .map(|(_, target)| target)?;
            }
            crate::core::GenericAtomTerm::Literal(_, literal) => {
                return Some(literal_to_value(base_values, literal));
            }
        }
    }
    None
}

fn trace_function_metadata(
    egraph: &EGraph,
    relations: &IndexMap<String, RelationDecl>,
    constructors: &IndexMap<String, ConstructorDecl>,
    mutable_functions: &IndexMap<String, MutableFunctionDecl>,
) -> Result<IndexMap<TableId, TraceFunctionMeta>, CausalSliceError> {
    let native = egraph
        .backend
        .as_any()
        .downcast_ref::<egglog_bridge::EGraph>()
        .ok_or_else(|| {
            CausalSliceError::Invariant(
                "causal tracing is implemented only by the reference backend".to_owned(),
            )
        })?;
    let mut result = IndexMap::default();
    for (name, function) in egraph.functions_iter() {
        let kind = if relations.contains_key(name) {
            TraceFunctionKind::Relation
        } else if constructors.contains_key(name) {
            TraceFunctionKind::Constructor
        } else if mutable_functions.contains_key(name) {
            TraceFunctionKind::Mutable
        } else {
            continue;
        };
        if function.is_hidden()
            || function.is_let_binding()
            || function.term_constructor().is_some()
        {
            return Err(CausalSliceError::Unsupported {
                location: format!("declaration `{name}`"),
                reason: "a hidden, global, or encoded view table in constructor tracing".to_owned(),
            });
        }
        if function.schema().outputs.len() != 1 {
            return Err(CausalSliceError::Unsupported {
                location: format!("declaration `{name}`"),
                reason: "a tuple-output table in constructor tracing".to_owned(),
            });
        }
        let input_sorts = function
            .schema()
            .input
            .iter()
            .map(|sort| sort.name().to_owned())
            .collect::<Vec<_>>();
        let output_sort = function.schema().output().name().to_owned();
        match kind {
            TraceFunctionKind::Relation => {
                let expected = &relations[name].sorts;
                if &input_sorts != expected {
                    return Err(CausalSliceError::Invariant(format!(
                        "runtime schema for relation `{name}` differs from its parsed declaration: inputs {input_sorts:?} vs {expected:?}"
                    )));
                }
            }
            TraceFunctionKind::Constructor => {
                let expected = &constructors[name];
                if input_sorts != expected.inputs || output_sort != expected.output {
                    return Err(CausalSliceError::Invariant(format!(
                        "runtime schema for constructor `{name}` differs from its parsed declaration"
                    )));
                }
            }
            TraceFunctionKind::Mutable => {
                let expected = &mutable_functions[name];
                if input_sorts != expected.inputs || output_sort != expected.output {
                    return Err(CausalSliceError::Invariant(format!(
                        "runtime schema for mutable function `{name}` differs from its parsed declaration"
                    )));
                }
            }
        }
        let table = native.function_table_id(function.backend_id);
        if result
            .insert(
                table,
                TraceFunctionMeta {
                    name: name.clone(),
                    input_sorts,
                    output_sort,
                    kind,
                    mutable_merge: mutable_functions.get(name).map(|decl| decl.merge),
                },
            )
            .is_some()
        {
            return Err(CausalSliceError::Invariant(format!(
                "two source functions share traced table {table:?}"
            )));
        }
    }
    Ok(result)
}

fn schema_only_registered_presort(presort: &str, registered_presorts: &HashSet<String>) -> bool {
    registered_presorts.contains(presort)
}

fn collect_declarations(
    commands: &[Command],
    source_name: &str,
    registered_presorts: &HashSet<String>,
) -> Result<CollectedDeclarations, CausalSliceError> {
    let mut relations = IndexMap::default();
    let mut constructors = IndexMap::default();
    let mut mutable_functions = IndexMap::default();
    let mut datatype_sorts = HashSet::default();
    let mut opaque_sorts = HashSet::default();
    for command in commands {
        match command {
            Command::Datatype { name, .. } => {
                datatype_sorts.insert(name.clone());
            }
            Command::Datatypes { datatypes, .. } => {
                for (_, name, definition) in datatypes {
                    match definition {
                        Subdatatypes::Variants(_) => {
                            datatype_sorts.insert(name.clone());
                        }
                        Subdatatypes::NewSort(presort, _)
                            if schema_only_registered_presort(presort, registered_presorts) =>
                        {
                            opaque_sorts.insert(name.clone());
                        }
                        Subdatatypes::NewSort(_, _) => {}
                    }
                }
            }
            Command::Sort {
                name,
                presort_and_args: Some((presort, _)),
                ..
            } if schema_only_registered_presort(presort, registered_presorts) => {
                opaque_sorts.insert(name.clone());
            }
            _ => {}
        }
    }
    let eq_sorts = commands
        .iter()
        .filter_map(|command| match command {
            Command::Sort {
                name,
                presort_and_args: None,
                uf: None,
                proof_func: None,
                container_rebuild: None,
                proof_constructors: None,
                unionable: true,
                ..
            } => Some(name.clone()),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let supported_sort = |sort: &str| {
        matches!(
            sort,
            "i64" | "String" | "bool" | "f64" | "Unit" | "BigInt" | "BigRat"
        ) || datatype_sorts.contains(sort)
            || eq_sorts.contains(sort)
            || opaque_sorts.contains(sort)
    };
    for (index, command) in commands.iter().enumerate() {
        match command {
            Command::Datatype {
                span,
                name,
                variants,
            } => {
                for variant in variants {
                    for sort in &variant.types {
                        if !supported_sort(sort) {
                            return unsupported(
                                &variant.span,
                                format!(
                                    "datatype constructor `{}` with unsupported input sort `{sort}`",
                                    variant.name
                                ),
                            );
                        }
                    }
                    if constructors
                        .insert(
                            variant.name.clone(),
                            ConstructorDecl {
                                inputs: variant.types.clone(),
                                output: name.clone(),
                                opaque_sort: variant
                                    .types
                                    .iter()
                                    .find(|sort| opaque_sorts.contains(*sort))
                                    .cloned(),
                            },
                        )
                        .is_some()
                    {
                        return unsupported(
                            span,
                            format!("duplicate constructor declaration `{}`", variant.name),
                        );
                    }
                }
            }
            Command::Datatypes { span, datatypes } => {
                for (datatype_span, name, definition) in datatypes {
                    match definition {
                        Subdatatypes::Variants(variants) => {
                            for variant in variants {
                                for sort in &variant.types {
                                    if !supported_sort(sort) {
                                        return unsupported(
                                            &variant.span,
                                            format!(
                                                "datatype* constructor `{}` with unsupported input sort `{sort}`",
                                                variant.name
                                            ),
                                        );
                                    }
                                }
                                if constructors
                                    .insert(
                                        variant.name.clone(),
                                        ConstructorDecl {
                                            inputs: variant.types.clone(),
                                            output: name.clone(),
                                            opaque_sort: variant
                                                .types
                                                .iter()
                                                .find(|sort| opaque_sorts.contains(*sort))
                                                .cloned(),
                                        },
                                    )
                                    .is_some()
                                {
                                    return unsupported(
                                        datatype_span,
                                        format!(
                                            "duplicate constructor declaration `{}`",
                                            variant.name
                                        ),
                                    );
                                }
                            }
                        }
                        Subdatatypes::NewSort(presort, _)
                            if schema_only_registered_presort(presort, registered_presorts) => {}
                        Subdatatypes::NewSort(presort, _) => {
                            return unsupported(
                                span,
                                format!(
                                    "datatype* sort `{name}` with unsupported presort `{presort}`"
                                ),
                            );
                        }
                    }
                }
            }
            Command::Relation { span, name, inputs } => {
                for sort in inputs {
                    if !supported_sort(sort) {
                        return unsupported(
                            span,
                            format!("relation `{name}` with unsupported sort `{sort}`"),
                        );
                    }
                }
                if relations
                    .insert(
                        name.clone(),
                        RelationDecl {
                            sorts: inputs.clone(),
                            opaque_sort: inputs
                                .iter()
                                .find(|sort| opaque_sorts.contains(*sort))
                                .cloned(),
                        },
                    )
                    .is_some()
                {
                    return Err(CausalSliceError::Unsupported {
                        location: format!("{source_name}: top-level command {index}"),
                        reason: format!("duplicate relation declaration `{name}`"),
                    });
                }
            }
            Command::Constructor {
                span,
                name,
                schema,
                hidden,
                let_binding,
                term_constructor,
                ..
            } => {
                if *hidden || *let_binding || term_constructor.is_some() {
                    return unsupported(
                        span,
                        format!(
                            "standalone constructor `{name}` with hidden, global, or encoded-view annotations"
                        ),
                    );
                }
                let [output] = schema.outputs.as_slice() else {
                    return unsupported(
                        span,
                        format!("tuple-output standalone constructor `{name}`"),
                    );
                };
                for sort in schema.input.iter().chain(std::iter::once(output)) {
                    if !supported_sort(sort) {
                        return unsupported(
                            span,
                            format!(
                                "standalone constructor `{name}` with unsupported sort `{sort}`"
                            ),
                        );
                    }
                }
                if constructors
                    .insert(
                        name.clone(),
                        ConstructorDecl {
                            inputs: schema.input.clone(),
                            output: output.clone(),
                            opaque_sort: schema
                                .input
                                .iter()
                                .chain(std::iter::once(output))
                                .find(|sort| opaque_sorts.contains(*sort))
                                .cloned(),
                        },
                    )
                    .is_some()
                {
                    return unsupported(
                        span,
                        format!("duplicate constructor declaration `{name}`"),
                    );
                }
            }
            Command::Function {
                span,
                name,
                schema,
                merge,
                hidden,
                let_binding,
                term_constructor,
                identity_vals,
                ..
            } if !hidden
                && !let_binding
                && term_constructor.is_none()
                && identity_vals.is_none() =>
            {
                let [output] = schema.outputs.as_slice() else {
                    continue;
                };
                let merge_kind = match merge {
                    None => MutableMergeKind::AssertEq,
                    Some(merge) if merge.actions.0.is_empty() => match &merge.result {
                        GenericExpr::Var(_, variable) if variable == "new" => {
                            MutableMergeKind::ExactNew
                        }
                        GenericExpr::Call(_, function, args)
                            if output == "BigRat"
                                && matches!(function.as_str(), "min" | "max")
                                && matches!(
                                    args.as_slice(),
                                    [GenericExpr::Var(_, old), GenericExpr::Var(_, new)]
                                        if old == "old" && new == "new"
                                ) =>
                        {
                            if function == "min" {
                                MutableMergeKind::BigRatMin
                            } else {
                                MutableMergeKind::BigRatMax
                            }
                        }
                        _ => continue,
                    },
                    Some(_) => continue,
                };
                for sort in schema.input.iter().chain(std::iter::once(output)) {
                    if !supported_sort(sort) {
                        return unsupported(
                            span,
                            format!(
                                "causally modeled mutable function `{name}` with unsupported sort `{sort}`"
                            ),
                        );
                    }
                }
                if mutable_functions
                    .insert(
                        name.clone(),
                        MutableFunctionDecl {
                            inputs: schema.input.clone(),
                            output: output.clone(),
                            opaque_sort: schema
                                .input
                                .iter()
                                .chain(std::iter::once(output))
                                .find(|sort| opaque_sorts.contains(*sort))
                                .cloned(),
                            merge: merge_kind,
                        },
                    )
                    .is_some()
                {
                    return unsupported(
                        span,
                        format!("duplicate mutable function declaration `{name}`"),
                    );
                }
            }
            _ => {}
        }
    }
    Ok((relations, constructors, mutable_functions))
}

fn name_and_prepare_rules(
    commands: &mut [Command],
    source_name: &str,
    source_rule_origins: &IndexMap<usize, SourceRuleOrigin>,
) -> Result<Vec<SourceRuleMapping>, CausalSliceError> {
    let mut used_names = HashSet::default();
    for command in commands.iter() {
        if let Command::Rule { rule } = command {
            if !rule.name.is_empty() && !source_string_is_stable(&rule.name) {
                return unsupported(
                    &rule.span,
                    "an explicit rule name containing a quote, backslash, or control character",
                );
            }
            if !rule.name.is_empty() && !used_names.insert(rule.name.clone()) {
                return unsupported(
                    &rule.span,
                    format!("duplicate explicit rule name `{}`", rule.name),
                );
            }
        }
    }

    let mut mapping = Vec::new();
    for (command_index, command) in commands.iter_mut().enumerate() {
        let Command::Rule { rule } = command else {
            continue;
        };
        let original_name = (!rule.name.is_empty()).then(|| rule.name.clone());
        if rule.name.is_empty() {
            let (start, end) = match &rule.span {
                Span::Egglog(span) => (span.i, span.j),
                _ => {
                    return Err(CausalSliceError::Unsupported {
                        location: format!("{source_name}: top-level command {command_index}"),
                        reason: "a rule without an egglog source span".to_owned(),
                    });
                }
            };
            let base = format!("__causal_slice_v0_b{start}_e{end}_c{command_index}");
            let mut candidate = base.clone();
            let mut collision = 0usize;
            while used_names.contains(&candidate) {
                candidate = format!("{base}_n{collision}");
                collision += 1;
            }
            used_names.insert(candidate.clone());
            rule.name = candidate;
        }

        let origin = source_rule_origins.get(&command_index);
        mapping.push(SourceRuleMapping {
            source_command_index: origin
                .map(|origin| origin.source_command_index)
                .unwrap_or(command_index),
            source_location: origin
                .map(|origin| origin.source_location.clone())
                .unwrap_or_else(|| rule.span.to_string()),
            original_name: origin
                .map(|origin| origin.original_name.clone())
                .unwrap_or(original_name),
            registered_name: rule.name.clone(),
            semantic_definition: semantic_rule_definition(rule),
        });
    }
    Ok(mapping)
}

fn lower_rewrites(
    commands: Vec<Command>,
    source_name: &str,
) -> Result<(Vec<Command>, IndexMap<usize, SourceRuleOrigin>), CausalSliceError> {
    let mut used_rule_names = commands
        .iter()
        .filter_map(|command| match command {
            Command::Rule { rule } if !rule.name.is_empty() => Some(rule.name.clone()),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let mut lowered = Vec::with_capacity(commands.len());
    let mut origins = IndexMap::default();

    for (source_command_index, command) in commands.into_iter().enumerate() {
        match command {
            Command::Rewrite(ruleset, rewrite, subsume) => {
                if subsume {
                    return unsupported(
                        &rewrite.span,
                        "a subsuming rewrite; causal prefix replay requires explicit visibility provenance"
                            .to_owned(),
                    );
                }
                let original_name = (!rewrite.name.is_empty()).then(|| rewrite.name.clone());
                let source_location = rewrite.span.to_string();
                let (rule, derived_replay_var) = lower_one_rewrite(
                    ruleset,
                    rewrite,
                    source_command_index,
                    0,
                    &mut used_rule_names,
                    source_name,
                )?;
                let lowered_index = lowered.len();
                lowered.push(Command::Rule { rule });
                origins.insert(
                    lowered_index,
                    SourceRuleOrigin {
                        source_command_index,
                        source_location,
                        original_name,
                        derived_replay_vars: vec![derived_replay_var],
                    },
                );
            }
            Command::BiRewrite(ruleset, rewrite) => {
                let original_name = (!rewrite.name.is_empty()).then(|| rewrite.name.clone());
                let source_location = rewrite.span.to_string();
                let reverse = Rewrite {
                    span: rewrite.span.clone(),
                    lhs: rewrite.rhs.clone(),
                    rhs: rewrite.lhs.clone(),
                    conditions: rewrite.conditions.clone(),
                    name: rewrite.name.clone(),
                };
                for (expansion_index, rewrite) in [rewrite, reverse].into_iter().enumerate() {
                    let (rule, derived_replay_var) = lower_one_rewrite(
                        ruleset.clone(),
                        rewrite,
                        source_command_index,
                        expansion_index,
                        &mut used_rule_names,
                        source_name,
                    )?;
                    let lowered_index = lowered.len();
                    lowered.push(Command::Rule { rule });
                    origins.insert(
                        lowered_index,
                        SourceRuleOrigin {
                            source_command_index,
                            source_location: source_location.clone(),
                            original_name: original_name.clone(),
                            derived_replay_vars: vec![derived_replay_var],
                        },
                    );
                }
            }
            command => lowered.push(command),
        }
    }
    Ok((lowered, origins))
}

fn lower_one_rewrite(
    ruleset: String,
    rewrite: Rewrite,
    source_command_index: usize,
    expansion_index: usize,
    used_rule_names: &mut HashSet<String>,
    source_name: &str,
) -> Result<(Rule, String), CausalSliceError> {
    let (start, end) = match &rewrite.span {
        Span::Egglog(span) => (span.i, span.j),
        _ => {
            return Err(CausalSliceError::Unsupported {
                location: format!("{source_name}: top-level command {source_command_index}"),
                reason: "a rewrite without an egglog source span".to_owned(),
            });
        }
    };
    let base =
        format!("__causal_slice_v0_rw_b{start}_e{end}_c{source_command_index}_r{expansion_index}");
    let mut name = base.clone();
    let mut collision = 0usize;
    while !used_rule_names.insert(name.clone()) {
        name = format!("{base}_n{collision}");
        collision += 1;
    }

    let mut used_vars = HashSet::default();
    collect_expr_vars(&rewrite.lhs, &mut used_vars);
    collect_expr_vars(&rewrite.rhs, &mut used_vars);
    for condition in &rewrite.conditions {
        collect_fact_vars(condition, &mut used_vars);
    }
    let root_base = format!(
        "__causal_slice_v0_root_b{start}_e{end}_c{source_command_index}_r{expansion_index}"
    );
    let mut root = root_base.clone();
    let mut collision = 0usize;
    while used_vars.contains(&root) {
        root = format!("{root_base}_n{collision}");
        collision += 1;
    }

    let span = rewrite.span;
    let body = std::iter::once(Fact::Eq(
        span.clone(),
        Expr::Var(span.clone(), root.clone()),
        rewrite.lhs,
    ))
    .chain(rewrite.conditions)
    .collect();
    let head = Actions::singleton(Action::Union(
        span.clone(),
        Expr::Var(span.clone(), root.clone()),
        rewrite.rhs,
    ));
    Ok((
        Rule {
            span,
            body,
            head,
            ruleset,
            name,
            eval_mode: RuleEvalMode::Seminaive,
            no_decomp: false,
            include_subsumed: false,
        },
        root,
    ))
}

fn collect_expr_vars(expr: &Expr, vars: &mut HashSet<String>) {
    match expr {
        GenericExpr::Var(_, var) => {
            vars.insert(var.clone());
        }
        GenericExpr::Call(_, _, args) => {
            for arg in args {
                collect_expr_vars(arg, vars);
            }
        }
        GenericExpr::Lit(..) => {}
    }
}

fn collect_fact_vars(fact: &Fact, vars: &mut HashSet<String>) {
    match fact {
        GenericFact::Fact(expr) => collect_expr_vars(expr, vars),
        GenericFact::Eq(_, left, right) => {
            collect_expr_vars(left, vars);
            collect_expr_vars(right, vars);
        }
    }
}

fn validate_and_model(
    commands: &[Command],
    resolved_source: &ResolvedSourceModel,
    declarations: ModelDeclarations<'_>,
    source_rule_origins: &IndexMap<usize, SourceRuleOrigin>,
    registered_presorts: &HashSet<String>,
    source_name: &str,
    fact_directory: Option<&Path>,
) -> Result<ProgramModel, CausalSliceError> {
    let ModelDeclarations {
        relations,
        constructors,
        mutable_functions,
    } = declarations;
    let mut rules = IndexMap::default();
    let mut checks = Vec::new();
    let mut source_facts = Vec::new();
    let mut source_expansions = SourceCommandExpansions::default();
    let mut source_globals = IndexMap::default();
    let mut schedule_indices = Vec::new();
    let scoped_program = commands
        .iter()
        .any(|command| matches!(command, Command::Push(..) | Command::Pop(..)));
    let mut regions = Vec::new();
    let mut active_region: Option<ProgramRegion> = None;
    let mut active_source_globals: Option<IndexMap<String, String>> = None;
    let mut persistent_source_commands = IndexSet::default();
    let mut scopes_started = false;
    let mut observations_started = false;
    let mut print_size_observations = 0usize;
    let mut resolved_action_index = 0usize;
    let mut resolved_check_index = 0usize;

    for (index, command) in commands.iter().enumerate() {
        match command {
            Command::Relation { .. }
            | Command::Datatype { .. }
            | Command::Datatypes { .. }
            | Command::Constructor { .. }
            | Command::Function { .. }
            | Command::AddRuleset(..)
            | Command::UnstableCombinedRuleset(..) => {
                if !schedule_indices.is_empty() || scopes_started {
                    return unsupported_command(
                        command,
                        index,
                        source_name,
                        "declaration after the computation schedule",
                    );
                }
            }
            Command::Sort {
                presort_and_args,
                uf: None,
                proof_func: None,
                container_rebuild: None,
                proof_constructors: None,
                unionable: true,
                ..
            } if presort_and_args.as_ref().is_none_or(|(presort, _)| {
                schema_only_registered_presort(presort, registered_presorts)
            }) =>
            {
                if !schedule_indices.is_empty() || scopes_started {
                    return unsupported_command(
                        command,
                        index,
                        source_name,
                        "sort declaration after the computation schedule",
                    );
                }
            }
            Command::Rule { rule } => {
                if !schedule_indices.is_empty() || scopes_started {
                    return unsupported(
                        &rule.span,
                        "rule declaration after the computation schedule".to_owned(),
                    );
                }
                let derived_replay_vars = source_rule_origins
                    .get(&index)
                    .map(|origin| origin.derived_replay_vars.as_slice())
                    .unwrap_or_default();
                let resolved_rule = resolved_source.rules.get(&rule.name).ok_or_else(|| {
                    CausalSliceError::Invariant(format!(
                        "typed source model lost rule `{}`",
                        rule.name
                    ))
                })?;
                let model = match model_rule(
                    rule,
                    resolved_rule,
                    relations,
                    constructors,
                    mutable_functions,
                    &source_globals,
                    derived_replay_vars,
                ) {
                    Ok(model) => model,
                    Err(CausalSliceError::Unsupported { location, reason }) => {
                        log::debug!(
                            "causal source model deferred rule `{}` at {location}: {reason}",
                            rule.name
                        );
                        opaque_rule_model(
                            rule,
                            relations,
                            constructors,
                            &source_globals,
                            DeferredUnsupported { location, reason },
                        )
                    }
                    Err(error) => return Err(error),
                };
                if rules.insert(rule.name.clone(), model).is_some() {
                    return unsupported(
                        &rule.span,
                        format!("duplicate registered rule `{}`", rule.name),
                    );
                }
            }
            Command::Action(action) => {
                if !scoped_program && !schedule_indices.is_empty() {
                    return unsupported_action(
                        action,
                        "ordinary action after the computation schedule",
                    );
                }
                if scoped_program
                    && active_region
                        .as_ref()
                        .is_some_and(|region| !region.schedule_indices.is_empty())
                {
                    return unsupported_action(
                        action,
                        "an ordinary action after the scoped computation schedule",
                    );
                }
                let visible_globals = active_source_globals.as_ref().unwrap_or(&source_globals);
                let resolved_action = resolved_source.actions.get(resolved_action_index);
                resolved_action_index += 1;
                let fact = model_source_fact(
                    SourceFactId(u32::try_from(source_facts.len()).map_err(|_| {
                        CausalSliceError::Invariant(
                            "source fact count exceeded u32 capacity".to_owned(),
                        )
                    })?),
                    index,
                    action,
                    resolved_action,
                    relations,
                    constructors,
                    mutable_functions,
                    visible_globals,
                )?;
                if let SourceFactKind::GlobalConstructor { name, sort, .. } = &fact.kind {
                    if rules.values().any(|rule| rule.var_sorts.contains_key(name)) {
                        return unsupported_action(
                            action,
                            format!(
                                "source global `{name}` shadowing an earlier local rule variable; the strict proof checker resolves the replayed name as the global"
                            ),
                        );
                    }
                    let globals = active_source_globals
                        .as_mut()
                        .unwrap_or(&mut source_globals);
                    if globals.insert(name.clone(), sort.clone()).is_some() {
                        return unsupported_action(
                            action,
                            format!("a duplicate source global `{name}`"),
                        );
                    }
                }
                source_facts.push(fact);
                if let Some(region) = active_region.as_mut() {
                    region.source_command_indices.insert(index);
                } else {
                    persistent_source_commands.insert(index);
                }
            }
            Command::Input { span, name, file } => {
                if !scoped_program && !schedule_indices.is_empty() {
                    return unsupported(
                        span,
                        "an input command after the computation schedule".to_owned(),
                    );
                }
                if scoped_program
                    && active_region
                        .as_ref()
                        .is_some_and(|region| !region.schedule_indices.is_empty())
                {
                    return unsupported(
                        span,
                        "an input command after the scoped computation schedule".to_owned(),
                    );
                }
                let relation = relations.get(name).ok_or_else(|| {
                    CausalSliceError::Unsupported {
                        location: span.to_string(),
                        reason: format!(
                            "input into `{name}`; causal slice input support is limited to declared relations"
                        ),
                    }
                })?;
                for sort in &relation.sorts {
                    if !matches!(sort.as_str(), "i64" | "f64" | "String") {
                        return unsupported(
                            span,
                            format!("input relation `{name}` with unsupported TSV sort `{sort}`"),
                        );
                    }
                }
                let rows = EGraph::read_input_rows(fact_directory, &relation.sorts, span, file)?;
                let mut expansion = Vec::with_capacity(rows.len());
                for (expansion_index, args) in rows.into_iter().enumerate() {
                    for literal in &args {
                        validate_printable_literal(span, literal)?;
                    }
                    let fact = SourceFact {
                        id: SourceFactId(u32::try_from(source_facts.len()).map_err(|_| {
                            CausalSliceError::Invariant(
                                "source fact count exceeded u32 capacity".to_owned(),
                            )
                        })?),
                        command_index: index,
                        expansion_index: Some(expansion_index),
                        kind: SourceFactKind::Relation(AtomTemplate {
                            relation: name.clone(),
                            args: args.iter().cloned().map(AtomArg::Lit).collect(),
                        }),
                    };
                    expansion.push(source_fact_command(span, &fact));
                    source_facts.push(fact);
                }
                source_expansions.insert(index, expansion);
                if let Some(region) = active_region.as_mut() {
                    region.source_command_indices.insert(index);
                } else {
                    persistent_source_commands.insert(index);
                }
            }
            Command::RunSchedule(schedule) => {
                validate_input_schedule(schedule)?;
                if scoped_program {
                    let Some(region) = active_region.as_mut() else {
                        return unsupported_command(
                            command,
                            index,
                            source_name,
                            "a computation schedule outside a pushed transaction",
                        );
                    };
                    if !region.check_indices.is_empty() {
                        return unsupported_command(
                            command,
                            index,
                            source_name,
                            "a computation schedule after an observation in one pushed transaction",
                        );
                    }
                    region.schedule_indices.push(index);
                } else if observations_started {
                    return unsupported_command(
                        command,
                        index,
                        source_name,
                        "a computation schedule after an observation",
                    );
                }
                schedule_indices.push(index);
            }
            Command::Check(span, facts) => {
                let has_schedule = if scoped_program {
                    active_region
                        .as_ref()
                        .is_some_and(|region| !region.schedule_indices.is_empty())
                } else {
                    !schedule_indices.is_empty()
                };
                if !has_schedule {
                    return unsupported(span, "a positive check before the schedule".to_owned());
                }
                observations_started = true;
                let visible_globals = active_source_globals.as_ref().unwrap_or(&source_globals);
                let resolved_facts = resolved_source
                    .checks
                    .get(resolved_check_index)
                    .map(Vec::as_slice);
                resolved_check_index += 1;
                let check = model_check(
                    span,
                    facts,
                    resolved_facts,
                    relations,
                    constructors,
                    visible_globals,
                )?;
                let check_index = checks.len();
                checks.push(check);
                if scoped_program {
                    let region = active_region.as_mut().ok_or_else(|| {
                        CausalSliceError::Invariant(
                            "scoped positive check lost its active transaction".to_owned(),
                        )
                    })?;
                    region.check_indices.push(check_index);
                    region.check_command_indices.push(index);
                }
            }
            Command::Push(count) if scoped_program => {
                if *count != 1 {
                    return unsupported_command(
                        command,
                        index,
                        source_name,
                        "a push count other than one",
                    );
                }
                if active_region.is_some() {
                    return unsupported_command(
                        command,
                        index,
                        source_name,
                        "nested push/pop transactions",
                    );
                }
                scopes_started = true;
                active_source_globals = Some(source_globals.clone());
                active_region = Some(ProgramRegion {
                    schedule_indices: Vec::new(),
                    check_indices: Vec::new(),
                    check_command_indices: Vec::new(),
                    source_command_indices: persistent_source_commands.clone(),
                    pop_command_index: None,
                });
            }
            Command::Pop(_, count) if scoped_program => {
                if *count != 1 {
                    return unsupported_command(
                        command,
                        index,
                        source_name,
                        "a pop count other than one",
                    );
                }
                let mut region =
                    active_region
                        .take()
                        .ok_or_else(|| CausalSliceError::Unsupported {
                            location: format!("{source_name}: top-level command {index}"),
                            reason: "a pop without one active pushed transaction".to_owned(),
                        })?;
                if region.schedule_indices.is_empty() || region.check_indices.is_empty() {
                    return unsupported_command(
                        command,
                        index,
                        source_name,
                        "a pushed transaction without both a computation schedule and a positive check",
                    );
                }
                region.pop_command_index = Some(index);
                regions.push(region);
                active_source_globals = None;
            }
            Command::Fail(span, command) if matches!(command.as_ref(), Command::Check(..)) => {
                return unsupported(span, "negative checks / proof of absence".to_owned());
            }
            Command::Rewrite(..) | Command::BiRewrite(..) => {
                return unsupported_command(
                    command,
                    index,
                    source_name,
                    "rewrites, unions, or congruence",
                );
            }
            Command::Sort { .. } => {
                return unsupported_command(
                    command,
                    index,
                    source_name,
                    "functions, constructors, datatypes, or custom sorts",
                );
            }
            Command::Include(..) => {
                return unsupported_command(
                    command,
                    index,
                    source_name,
                    "include commands (they can hide schedules)",
                );
            }
            Command::Extract(..) => {
                return unsupported_command(
                    command,
                    index,
                    source_name,
                    "extract observations in Bronze",
                );
            }
            Command::PrintSize(..) => {
                // Preserve read-only diagnostics at their original boundary.
                // In a print-only program they conservatively retain the
                // complete effective execution prefix.
                if schedule_indices.is_empty() {
                    return unsupported_command(
                        command,
                        index,
                        source_name,
                        "a print-size observation before the schedule",
                    );
                }
                observations_started = true;
                print_size_observations += 1;
            }
            Command::PrintOverallStatistics(span, file) => {
                if file.is_some() {
                    return unsupported(
                        span,
                        "print-stats file output; causal replay does not reproduce output side effects"
                            .to_owned(),
                    );
                }
                if schedule_indices.is_empty() {
                    return unsupported(span, "print-stats before the schedule".to_owned());
                }
                // Preserved as an operational diagnostic, not as a semantic
                // observation: manual replay necessarily changes run reports.
                observations_started = true;
            }
            _ => {
                return unsupported_command(
                    command,
                    index,
                    source_name,
                    "this top-level command in the Bronze fragment",
                );
            }
        }
    }

    if active_region.is_some() {
        return Err(CausalSliceError::Unsupported {
            location: source_name.to_owned(),
            reason: "an unterminated pushed transaction".to_owned(),
        });
    }
    if schedule_indices.is_empty() {
        return Err(CausalSliceError::Unsupported {
            location: source_name.to_owned(),
            reason: "a program without a computation schedule".to_owned(),
        });
    }
    if !scoped_program {
        regions.push(ProgramRegion {
            schedule_indices: schedule_indices.clone(),
            check_indices: (0..checks.len()).collect(),
            check_command_indices: commands
                .iter()
                .enumerate()
                .filter_map(|(index, command)| {
                    matches!(command, Command::Check(..)).then_some(index)
                })
                .collect(),
            source_command_indices: source_facts.iter().map(|fact| fact.command_index).collect(),
            pop_command_index: None,
        });
    } else if regions.is_empty() {
        return Err(CausalSliceError::Unsupported {
            location: source_name.to_owned(),
            reason: "a scoped program without a complete pushed transaction".to_owned(),
        });
    }
    let prefix_fallbacks = if checks.is_empty() {
        print_size_observations
    } else {
        0
    };
    if scoped_program && prefix_fallbacks > 0 {
        return Err(CausalSliceError::Unsupported {
            location: source_name.to_owned(),
            reason: "print-only Prefix observations across push/pop transactions".to_owned(),
        });
    }
    if checks.is_empty() && prefix_fallbacks == 0 {
        return Err(CausalSliceError::Unsupported {
            location: source_name.to_owned(),
            reason: "a program without a positive check or print-size prefix root".to_owned(),
        });
    }
    Ok(ProgramModel {
        rules,
        checks,
        source_facts,
        constructors: constructors.clone(),
        mutable_functions: mutable_functions.clone(),
        source_expansions,
        schedule_indices,
        regions,
        prefix_fallbacks,
    })
}

fn opaque_rule_model(
    rule: &crate::ast::Rule,
    relations: &IndexMap<String, RelationDecl>,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
    error: DeferredUnsupported,
) -> RuleModel {
    let opaque = if matches!(rule.head.0.as_slice(), [GenericAction::Panic(..)]) {
        OpaqueRulePolicy::UnreachedPanicHead
    } else if empty_body_initializer_is_replayable(rule, relations, constructors, source_globals) {
        OpaqueRulePolicy::EmptyBodyInitializer
    } else {
        OpaqueRulePolicy::Reject(error)
    };
    RuleModel {
        span: rule.span.clone(),
        body: Vec::new(),
        body_equalities: Vec::new(),
        body_lookups: Vec::new(),
        body_functions: Vec::new(),
        body_primitives: Vec::new(),
        head_lets: Vec::new(),
        head: Vec::new(),
        head_constructors: Vec::new(),
        head_sets: Vec::new(),
        head_subsumes: Vec::new(),
        head_primitives: Vec::new(),
        head_unions: Vec::new(),
        var_order: Vec::new(),
        replay_var_order: Vec::new(),
        derived_replay_aliases: IndexMap::default(),
        var_sorts: IndexMap::default(),
        global_uses: IndexMap::default(),
        opaque: Some(opaque),
    }
}

fn empty_body_initializer_is_replayable(
    rule: &crate::ast::Rule,
    relations: &IndexMap<String, RelationDecl>,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
) -> bool {
    if !rule.body.is_empty() || rule.eval_mode != RuleEvalMode::Seminaive {
        return false;
    }
    let mut locals = HashSet::default();
    for action in &rule.head.0 {
        match action {
            GenericAction::Let(_, name, expression) => {
                if !initializer_expr_is_replayable(
                    expression,
                    false,
                    &locals,
                    relations,
                    constructors,
                    source_globals,
                ) {
                    return false;
                }
                locals.insert(name.clone());
            }
            GenericAction::Expr(_, expression) => {
                if !initializer_expr_is_replayable(
                    expression,
                    true,
                    &locals,
                    relations,
                    constructors,
                    source_globals,
                ) {
                    return false;
                }
            }
            GenericAction::Set(..)
            | GenericAction::Change(..)
            | GenericAction::Union(..)
            | GenericAction::Panic(..) => return false,
        }
    }
    true
}

fn initializer_expr_is_replayable(
    expression: &Expr,
    allow_relation: bool,
    locals: &HashSet<String>,
    relations: &IndexMap<String, RelationDecl>,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
) -> bool {
    match expression {
        GenericExpr::Lit(..) => true,
        GenericExpr::Var(_, variable) => {
            locals.contains(variable) || source_globals.contains_key(variable)
        }
        GenericExpr::Call(_, function, args) => {
            let known_call = constructors.contains_key(function)
                || (allow_relation && relations.contains_key(function));
            known_call
                && args.iter().all(|arg| {
                    initializer_expr_is_replayable(
                        arg,
                        false,
                        locals,
                        relations,
                        constructors,
                        source_globals,
                    )
                })
        }
    }
}

fn model_rule(
    rule: &crate::ast::Rule,
    resolved_rule: &ResolvedRule,
    relations: &IndexMap<String, RelationDecl>,
    constructors: &IndexMap<String, ConstructorDecl>,
    mutable_functions: &IndexMap<String, MutableFunctionDecl>,
    source_globals: &IndexMap<String, String>,
    derived_replay_vars: &[String],
) -> Result<RuleModel, CausalSliceError> {
    if resolved_rule.name != rule.name
        || resolved_rule.body.len() != rule.body.len()
        || resolved_rule.head.len() != rule.head.len()
        || resolved_rule.ruleset != rule.ruleset
        || resolved_rule.eval_mode != rule.eval_mode
        || resolved_rule.no_decomp != rule.no_decomp
        || resolved_rule.include_subsumed != rule.include_subsumed
    {
        return Err(CausalSliceError::Invariant(format!(
            "typed source model diverged from rule `{}`",
            rule.name
        )));
    }
    if rule.eval_mode != RuleEvalMode::Seminaive {
        return unsupported(
            &rule.span,
            format!("non-default evaluation mode on rule `{}`", rule.name),
        );
    }
    if rule.include_subsumed {
        return unsupported(
            &rule.span,
            format!("subsumed-row matching on rule `{}`", rule.name),
        );
    }
    if rule.head.0.is_empty() {
        return unsupported(&rule.span, format!("an empty head on rule `{}`", rule.name));
    }
    let mut var_order = Vec::new();
    let mut var_sorts = IndexMap::default();
    let mut body = Vec::new();
    let mut body_lookups = Vec::new();
    let mut body_primitive_occurrences = vec![Vec::new(); rule.body.len()];
    for (fact_index, fact) in rule.body.iter().enumerate() {
        let resolved_fact = &resolved_rule.body[fact_index];
        match fact {
            GenericFact::Fact(expr) => {
                if let Some(primitive) = model_query_predicate(
                    expr,
                    resolved_fact,
                    constructors,
                    source_globals,
                    &format!("rule `{}` body", rule.name),
                )? {
                    collect_nested_query_primitives(
                        &primitive.application,
                        &primitive.span,
                        &mut body_primitive_occurrences[fact_index],
                    );
                    register_arg_vars(
                        &primitive.application,
                        &primitive.sort,
                        &mut var_order,
                        &mut var_sorts,
                    )?;
                    body_primitive_occurrences[fact_index].push(primitive);
                    continue;
                }
                let ResolvedFact::Fact(resolved_expr) = resolved_fact else {
                    return Err(CausalSliceError::Invariant(format!(
                        "typed source model changed a relation fact in rule `{}`",
                        rule.name
                    )));
                };
                if let GenericExpr::Call(span, function, _) = expr
                    && let Some(constructor) = constructors.get(function)
                {
                    let application = model_typed_atom_arg(
                        expr,
                        resolved_expr,
                        &constructor.output,
                        constructors,
                        source_globals,
                        &format!("rule `{}` bare constructor body fact", rule.name),
                    )?;
                    collect_intermediate_query_primitives(
                        span,
                        &application,
                        &mut body_primitive_occurrences[fact_index],
                    );
                    register_arg_vars(
                        &application,
                        &constructor.output,
                        &mut var_order,
                        &mut var_sorts,
                    )?;
                    body_lookups.push(ConstructorLookupTemplate {
                        span: span.clone(),
                        application: application.clone(),
                        output: application,
                        sort: constructor.output.clone(),
                    });
                    continue;
                }
                let atom = model_typed_atom(
                    expr,
                    resolved_expr,
                    relations,
                    constructors,
                    source_globals,
                    "rule body",
                )?;
                for arg in &atom.args {
                    collect_intermediate_query_primitives(
                        &expr.span(),
                        arg,
                        &mut body_primitive_occurrences[fact_index],
                    );
                }
                register_atom_vars(&atom, relations, &mut var_order, &mut var_sorts)?;
                body.push(atom);
            }
            GenericFact::Eq(..) => {}
        }
    }
    let mut body_equalities = Vec::new();
    let mut body_functions = Vec::new();
    for (fact_index, fact) in rule.body.iter().enumerate() {
        let resolved_fact = &resolved_rule.body[fact_index];
        let GenericFact::Eq(span, left, right) = fact else {
            continue;
        };
        if let Some(primitive) = model_query_primitive(
            span,
            left,
            right,
            resolved_fact,
            &var_sorts,
            constructors,
            source_globals,
            &format!("rule `{}` body", rule.name),
        )? {
            collect_nested_query_primitives(
                &primitive.application,
                &primitive.span,
                &mut body_primitive_occurrences[fact_index],
            );
            register_arg_vars(
                &primitive.application,
                &primitive.sort,
                &mut var_order,
                &mut var_sorts,
            )?;
            if let Some(output) = &primitive.output {
                register_arg_vars(output, &primitive.sort, &mut var_order, &mut var_sorts)?;
            }
            body_primitive_occurrences[fact_index].push(primitive);
            continue;
        }
        if let Some(lookup) = model_function_lookup(
            span,
            left,
            right,
            mutable_functions,
            constructors,
            source_globals,
            &format!("rule `{}` body", rule.name),
        )? {
            for (key, sort) in lookup.keys.iter().zip(&lookup.input_sorts) {
                register_arg_vars(key, sort, &mut var_order, &mut var_sorts)?;
            }
            register_arg_vars(
                &lookup.output,
                &lookup.output_sort,
                &mut var_order,
                &mut var_sorts,
            )?;
            body_functions.push(lookup);
            continue;
        }
        if let Some(lookup) = model_constructor_lookup(
            span,
            left,
            right,
            resolved_fact,
            constructors,
            source_globals,
            &format!("rule `{}` body", rule.name),
        )? {
            collect_intermediate_query_primitives(
                span,
                &lookup.application,
                &mut body_primitive_occurrences[fact_index],
            );
            register_arg_vars(
                &lookup.application,
                &lookup.sort,
                &mut var_order,
                &mut var_sorts,
            )?;
            register_arg_vars(&lookup.output, &lookup.sort, &mut var_order, &mut var_sorts)?;
            body_lookups.push(lookup);
            continue;
        }
        let ResolvedFact::Eq(_, resolved_left, resolved_right) = resolved_fact else {
            return Err(CausalSliceError::Invariant(format!(
                "typed source model changed an equality in rule `{}`",
                rule.name
            )));
        };
        let equality = model_resolved_equality(
            span,
            left,
            right,
            resolved_left,
            resolved_right,
            constructors,
            source_globals,
            &format!("rule `{}` body", rule.name),
        )?;
        collect_intermediate_query_primitives(
            span,
            &equality.left,
            &mut body_primitive_occurrences[fact_index],
        );
        collect_intermediate_query_primitives(
            span,
            &equality.right,
            &mut body_primitive_occurrences[fact_index],
        );
        register_arg_vars(
            &equality.left,
            &equality.sort,
            &mut var_order,
            &mut var_sorts,
        )?;
        register_arg_vars(
            &equality.right,
            &equality.sort,
            &mut var_order,
            &mut var_sorts,
        )?;
        body_equalities.push(equality);
    }
    let body_primitives = body_primitive_occurrences
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    let mut head = Vec::new();
    let mut head_lets = Vec::new();
    let mut head_constructors = Vec::new();
    let mut head_sets = Vec::new();
    let mut head_subsumes = Vec::new();
    let mut head_unions = Vec::new();
    let mut head_var_sorts = var_sorts.clone();
    let mut saw_non_let_head_action = false;
    for (action, resolved_action) in rule.head.0.iter().zip(&resolved_rule.head.0) {
        if !source_and_resolved_action_shapes_match(action, resolved_action) {
            return Err(CausalSliceError::Invariant(format!(
                "typed source model changed a head action in rule `{}`",
                rule.name
            )));
        }
        let args = match action {
            GenericAction::Let(span, name, expression) => {
                if saw_non_let_head_action {
                    return unsupported(
                        span,
                        format!(
                            "a head-local binding after an effect action in rule `{}`",
                            rule.name
                        ),
                    );
                }
                let ResolvedAction::Let(_, resolved_var, resolved_expression) = resolved_action
                else {
                    unreachable!("head action shapes were checked above")
                };
                if resolved_var.name != *name {
                    return Err(CausalSliceError::Invariant(format!(
                        "typed source model renamed head local `{name}` in rule `{}`",
                        rule.name
                    )));
                }
                if head_var_sorts.contains_key(name) || source_globals.contains_key(name) {
                    return unsupported(
                        span,
                        format!(
                            "head-local binding `{name}` shadows an existing binding in rule `{}`",
                            rule.name
                        ),
                    );
                }
                let sort = resolved_var.sort.name().to_owned();
                let value = model_typed_atom_arg(
                    expression,
                    resolved_expression,
                    &sort,
                    constructors,
                    source_globals,
                    &format!("rule `{}` head local `{name}`", rule.name),
                )?;
                for (var_span, var) in atom_arg_vars(&value) {
                    if !head_var_sorts.contains_key(var) {
                        return unsupported(
                            var_span,
                            format!(
                                "head-local `{name}` reads unbound variable `{var}` in rule `{}`",
                                rule.name
                            ),
                        );
                    }
                }
                head_lets.push(HeadLetTemplate {
                    name: name.clone(),
                    sort: sort.clone(),
                    value,
                });
                head_var_sorts.insert(name.clone(), sort);
                Vec::new()
            }
            GenericAction::Expr(_, expr) => {
                saw_non_let_head_action = true;
                let ResolvedAction::Expr(_, resolved_expr) = resolved_action else {
                    unreachable!("head action shapes were checked above")
                };
                let GenericExpr::Call(span, function, _) = expr else {
                    return unsupported_action(
                        action,
                        format!("a non-call head action in rule `{}`", rule.name),
                    );
                };
                if relations.contains_key(function) {
                    let atom = model_typed_atom(
                        expr,
                        resolved_expr,
                        relations,
                        constructors,
                        source_globals,
                        "rule head",
                    )?;
                    let args = atom.args.clone();
                    head.push(atom);
                    args
                } else if let Some(constructor) = constructors.get(function) {
                    let constructor = model_typed_atom_arg(
                        expr,
                        resolved_expr,
                        &constructor.output,
                        constructors,
                        source_globals,
                        "rule head",
                    )?;
                    let args = vec![constructor.clone()];
                    head_constructors.push(constructor);
                    args
                } else {
                    return unsupported(
                        span,
                        format!(
                            "primitive or function call `{function}` in rule `{}` head",
                            rule.name
                        ),
                    );
                }
            }
            GenericAction::Union(span, left, right) => {
                saw_non_let_head_action = true;
                let ResolvedAction::Union(_, resolved_left, resolved_right) = resolved_action
                else {
                    unreachable!("head action shapes were checked above")
                };
                let equality = model_resolved_equality(
                    span,
                    left,
                    right,
                    resolved_left,
                    resolved_right,
                    constructors,
                    source_globals,
                    &format!("rule `{}` union head", rule.name),
                )?;
                let args = vec![equality.left.clone(), equality.right.clone()];
                head_unions.push(equality);
                args
            }
            GenericAction::Set(span, function, keys, value) => {
                saw_non_let_head_action = true;
                let Some(declaration) = mutable_functions.get(function) else {
                    return unsupported_action(
                        action,
                        format!(
                            "a non-insert/union head action in rule `{}`: set of function `{function}` without a causally modeled single-output merge",
                            rule.name,
                        ),
                    );
                };
                if let Some(sort) = &declaration.opaque_sort {
                    return unsupported(
                        span,
                        format!(
                            "set of function `{function}` with opaque container sort `{sort}` in rule `{}`",
                            rule.name
                        ),
                    );
                }
                if !matches!(
                    declaration.merge,
                    MutableMergeKind::AssertEq | MutableMergeKind::ExactNew
                ) {
                    return unsupported(
                        span,
                        format!(
                            "set of function `{function}` with a custom merge in rule `{}`; only assert-equal and exact `:merge new` rule writes are currently causal",
                            rule.name
                        ),
                    );
                }
                if keys.len() != declaration.inputs.len() {
                    return unsupported(
                        span,
                        format!(
                            "set of function `{function}` with {} keys instead of {} in rule `{}`",
                            keys.len(),
                            declaration.inputs.len(),
                            rule.name
                        ),
                    );
                }
                let modeled_keys = keys
                    .iter()
                    .zip(&declaration.inputs)
                    .map(|(key, sort)| {
                        model_atom_arg(key, sort, constructors, source_globals, "rule head set")
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let modeled_value = model_atom_arg(
                    value,
                    &declaration.output,
                    constructors,
                    source_globals,
                    "rule head set",
                )?;
                let mut args = modeled_keys.clone();
                args.push(modeled_value.clone());
                head_sets.push(FunctionSetTemplate {
                    span: span.clone(),
                    function: function.clone(),
                    keys: modeled_keys,
                    value: modeled_value,
                    input_sorts: declaration.inputs.clone(),
                    output_sort: declaration.output.clone(),
                });
                args
            }
            GenericAction::Change(span, crate::ast::Change::Subsume, function, args) => {
                saw_non_let_head_action = true;
                let Some(constructor) = constructors.get(function) else {
                    return unsupported(
                        span,
                        format!(
                            "subsume target `{function}` in rule `{}` is not a constructor",
                            rule.name
                        ),
                    );
                };
                let target = model_atom_arg(
                    &Expr::Call(span.clone(), function.clone(), args.clone()),
                    &constructor.output,
                    constructors,
                    source_globals,
                    "rule head subsume",
                )?;
                if !body_lookups
                    .iter()
                    .any(|lookup| same_atom_arg_shape(&lookup.application, &target))
                {
                    return unsupported(
                        span,
                        format!(
                            "subsume target in rule `{}` that does not exactly alias a live body constructor lookup",
                            rule.name
                        ),
                    );
                }
                head_subsumes.push(target.clone());
                vec![target]
            }
            _ => {
                return unsupported_action(
                    action,
                    format!("a non-insert/union head action in rule `{}`", rule.name),
                );
            }
        };
        for arg in &args {
            for (span, var) in atom_arg_vars(arg) {
                if !head_var_sorts.contains_key(var) {
                    return unsupported(
                        span,
                        format!("head-only variable `{var}` in rule `{}`", rule.name),
                    );
                }
            }
        }
    }
    if rule.body.is_empty() && !head_lets.is_empty() {
        return unsupported(
            &rule.span,
            format!(
                "empty-body head locals in rule `{}` use the closed-initializer replay path",
                rule.name
            ),
        );
    }
    let mut head_primitives = Vec::new();
    for arg in head_lets.iter().map(|local| &local.value).chain(
        head.iter()
            .flat_map(|atom| atom.args.iter())
            .chain(head_constructors.iter())
            .chain(
                head_sets
                    .iter()
                    .flat_map(|set| set.keys.iter().chain(std::iter::once(&set.value))),
            )
            .chain(head_subsumes.iter())
            .chain(
                head_unions
                    .iter()
                    .flat_map(|equality| [&equality.left, &equality.right]),
            ),
    ) {
        collect_replay_primitives(arg, &mut head_primitives);
    }
    let semantic_head_actions = rule
        .head
        .0
        .iter()
        .filter(|action| !matches!(action, GenericAction::Let(..)))
        .count();
    if !head_subsumes.is_empty()
        && (head_unions.len() != 1 || semantic_head_actions != 1 + head_subsumes.len())
    {
        return unsupported(
            &rule.span,
            format!(
                "subsume side effects in rule `{}` without exactly one independent union head",
                rule.name
            ),
        );
    }
    if !head_unions.is_empty() && head_subsumes.is_empty() && head_unions.len() != 1 {
        return unsupported(
            &rule.span,
            format!("more than one union action in rule `{}`", rule.name),
        );
    }

    let derived_replay_vars = derived_replay_vars
        .iter()
        .map(String::as_str)
        .collect::<HashSet<_>>();
    let mut derived_replay_aliases = IndexMap::default();
    for derived in &derived_replay_vars {
        let derivable = body_lookups.iter().any(|lookup| {
            matches!(&lookup.output, AtomArg::Var(_, output) if output.as_str() == *derived)
                && atom_arg_vars(&lookup.application)
                    .iter()
                    .all(|(_, input)| !derived_replay_vars.contains(input.as_str()))
        });
        if !derivable {
            let direct_alias = body_equalities.iter().find_map(|equality| {
                match (&equality.left, &equality.right) {
                    (AtomArg::Var(_, left), AtomArg::Var(_, right))
                        if left == derived && !derived_replay_vars.contains(right.as_str()) =>
                    {
                        Some(right.clone())
                    }
                    _ => None,
                }
            });
            let Some(direct_alias) = direct_alias else {
                return Err(CausalSliceError::Invariant(format!(
                    "internal replay variable `{derived}` on rule `{}` is neither functionally determined by a constructor lookup nor a typed direct alias",
                    rule.name
                )));
            };
            derived_replay_aliases.insert((*derived).to_owned(), direct_alias);
        }
    }
    let replay_var_order = var_order
        .iter()
        .filter(|var| !derived_replay_vars.contains(var.as_str()))
        .cloned()
        .collect();

    let mut model = RuleModel {
        span: rule.span.clone(),
        body,
        body_equalities,
        body_lookups,
        body_functions,
        body_primitives,
        head_lets,
        head,
        head_constructors,
        head_sets,
        head_subsumes,
        head_primitives,
        head_unions,
        var_order,
        replay_var_order,
        derived_replay_aliases,
        var_sorts,
        global_uses: IndexMap::default(),
        opaque: None,
    };
    model.global_uses = rule_global_uses(&model)
        .into_iter()
        .map(|(name, sort)| (name.to_owned(), sort.to_owned()))
        .collect();
    Ok(model)
}

fn source_and_resolved_action_shapes_match(source: &Action, resolved: &ResolvedAction) -> bool {
    matches!(
        (source, resolved),
        (GenericAction::Let(..), GenericAction::Let(..))
            | (GenericAction::Set(..), GenericAction::Set(..))
            | (GenericAction::Change(..), GenericAction::Change(..))
            | (GenericAction::Union(..), GenericAction::Union(..))
            | (GenericAction::Panic(..), GenericAction::Panic(..))
            | (GenericAction::Expr(..), GenericAction::Expr(..))
    )
}

fn model_check(
    span: &Span,
    facts: &[Fact],
    resolved_facts: Option<&[ResolvedFact]>,
    relations: &IndexMap<String, RelationDecl>,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
) -> Result<CheckModel, CausalSliceError> {
    if facts.is_empty() {
        return unsupported(span, "an empty positive check".to_owned());
    }
    if facts.len() > 2 {
        return unsupported(
            span,
            "a potentially tree-decomposed positive check; causal slice v0 has no provenance for materialized intermediate rows"
                .to_owned(),
        );
    }
    let mut atoms = Vec::new();
    let mut equalities = Vec::new();
    let mut var_order = Vec::new();
    let mut var_sorts = IndexMap::default();
    if let Some(resolved) = resolved_facts
        && resolved.len() != facts.len()
    {
        return Err(CausalSliceError::Invariant(
            "typed positive-check model changed its fact count".to_owned(),
        ));
    }
    for (fact_index, fact) in facts.iter().enumerate() {
        let resolved_fact = resolved_facts.map(|facts| &facts[fact_index]);
        match fact {
            GenericFact::Fact(expr) => {
                let atom = if let Some(ResolvedFact::Fact(resolved_expr)) = resolved_fact {
                    model_typed_atom(
                        expr,
                        resolved_expr,
                        relations,
                        constructors,
                        source_globals,
                        "positive check",
                    )?
                } else if resolved_fact.is_some() {
                    return Err(CausalSliceError::Invariant(
                        "typed positive-check model changed a relation fact".to_owned(),
                    ));
                } else {
                    model_atom(
                        expr,
                        relations,
                        constructors,
                        source_globals,
                        "positive check",
                    )?
                };
                register_atom_vars(&atom, relations, &mut var_order, &mut var_sorts)?;
                atoms.push(atom);
            }
            GenericFact::Eq(fact_span, left, right) => {
                let equality = if let Some(ResolvedFact::Eq(_, resolved_left, resolved_right)) =
                    resolved_fact
                {
                    model_typed_equality(
                        fact_span,
                        left,
                        right,
                        resolved_left,
                        resolved_right,
                        &var_sorts,
                        constructors,
                        source_globals,
                        "positive check",
                    )?
                } else if resolved_fact.is_some() {
                    return Err(CausalSliceError::Invariant(
                        "typed positive-check model changed an equality fact".to_owned(),
                    ));
                } else {
                    model_equality(
                        fact_span,
                        left,
                        right,
                        &var_sorts,
                        constructors,
                        source_globals,
                        "positive check",
                    )?
                };
                register_equality_vars(&equality, &mut var_order, &mut var_sorts)?;
                equalities.push(equality);
            }
        }
    }
    if facts.len() > 1 {
        let occurrences = variable_check_fact_occurrences(&atoms, &equalities);
        if let Some(var) = var_order
            .iter()
            .find(|var| occurrences.get(var.as_str()).copied() == Some(1))
        {
            return unsupported(
                span,
                format!(
                    "multi-atom check variable `{var}` that Generic Join may project; exact observation capture requires a projection-preserving match witness"
                ),
            );
        }
    }
    let mut model = CheckModel {
        atoms,
        equalities,
        var_sorts,
        global_uses: IndexMap::default(),
    };
    model.global_uses = check_global_uses(&model)
        .into_iter()
        .map(|(name, sort)| (name.to_owned(), sort.to_owned()))
        .collect();
    Ok(model)
}

fn model_equality(
    span: &Span,
    left: &Expr,
    right: &Expr,
    known_var_sorts: &IndexMap<String, String>,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
    context: &str,
) -> Result<EqualityTemplate, CausalSliceError> {
    let left_sort =
        infer_equality_expr_sort(left, known_var_sorts, constructors, source_globals, context)?;
    let right_sort = infer_equality_expr_sort(
        right,
        known_var_sorts,
        constructors,
        source_globals,
        context,
    )?;
    let sort = match (left_sort, right_sort) {
        (Some(left), Some(right)) if left == right => left,
        (Some(left), Some(right)) => {
            return unsupported(
                span,
                format!("an equality between `{left}` and `{right}` in {context}"),
            );
        }
        (Some(sort), None) | (None, Some(sort)) => sort,
        (None, None) => {
            return unsupported(
                span,
                format!("an equality whose variable sort cannot be inferred in {context}"),
            );
        }
    };
    if !constructors
        .values()
        .any(|constructor| constructor.output == sort)
    {
        return unsupported(
            span,
            format!("equality or primitive filters over non-equality sort `{sort}` in {context}"),
        );
    }
    Ok(EqualityTemplate {
        span: span.clone(),
        left: model_atom_arg(left, &sort, constructors, source_globals, context)?,
        right: model_atom_arg(right, &sort, constructors, source_globals, context)?,
        sort,
    })
}

#[allow(clippy::too_many_arguments)]
fn model_typed_equality(
    span: &Span,
    left: &Expr,
    right: &Expr,
    resolved_left: &ResolvedExpr,
    resolved_right: &ResolvedExpr,
    known_var_sorts: &IndexMap<String, String>,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
    context: &str,
) -> Result<EqualityTemplate, CausalSliceError> {
    let left_sort =
        infer_equality_expr_sort(left, known_var_sorts, constructors, source_globals, context)?;
    let right_sort = infer_equality_expr_sort(
        right,
        known_var_sorts,
        constructors,
        source_globals,
        context,
    )?;
    let sort = match (left_sort, right_sort) {
        (Some(left), Some(right)) if left == right => left,
        (Some(left), Some(right)) => {
            return unsupported(
                span,
                format!("an equality between `{left}` and `{right}` in {context}"),
            );
        }
        (Some(sort), None) | (None, Some(sort)) => sort,
        (None, None) => {
            return unsupported(
                span,
                format!("an equality whose variable sort cannot be inferred in {context}"),
            );
        }
    };
    if !constructors
        .values()
        .any(|constructor| constructor.output == sort)
    {
        return unsupported(
            span,
            format!("equality or primitive filters over non-equality sort `{sort}` in {context}"),
        );
    }
    Ok(EqualityTemplate {
        span: span.clone(),
        left: model_typed_atom_arg(
            left,
            resolved_left,
            &sort,
            constructors,
            source_globals,
            context,
        )?,
        right: model_typed_atom_arg(
            right,
            resolved_right,
            &sort,
            constructors,
            source_globals,
            context,
        )?,
        sort,
    })
}

#[allow(clippy::too_many_arguments)]
fn model_resolved_equality(
    span: &Span,
    left: &Expr,
    right: &Expr,
    resolved_left: &ResolvedExpr,
    resolved_right: &ResolvedExpr,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
    context: &str,
) -> Result<EqualityTemplate, CausalSliceError> {
    let left_sort = resolved_left.output_type();
    let right_sort = resolved_right.output_type();
    if left_sort.name() != right_sort.name() {
        return unsupported(
            span,
            format!(
                "an equality between `{}` and `{}` in {context}",
                left_sort.name(),
                right_sort.name()
            ),
        );
    }
    let sort = left_sort.name().to_owned();
    Ok(EqualityTemplate {
        span: span.clone(),
        left: model_typed_atom_arg(
            left,
            resolved_left,
            &sort,
            constructors,
            source_globals,
            context,
        )?,
        right: model_typed_atom_arg(
            right,
            resolved_right,
            &sort,
            constructors,
            source_globals,
            context,
        )?,
        sort,
    })
}

fn model_typed_atom_arg(
    expr: &Expr,
    resolved: &ResolvedExpr,
    expected_sort: &str,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
    context: &str,
) -> Result<AtomArg, CausalSliceError> {
    match (expr, resolved) {
        (GenericExpr::Var(_, source), ResolvedExpr::Var(_, typed)) => {
            if typed.name != *source || typed.sort.name() != expected_sort {
                return Err(CausalSliceError::Invariant(format!(
                    "typed source variable `{source}` diverged in {context}"
                )));
            }
            model_atom_arg(expr, expected_sort, constructors, source_globals, context)
        }
        (GenericExpr::Lit(_, source), ResolvedExpr::Lit(_, typed)) if source == typed => {
            model_atom_arg(expr, expected_sort, constructors, source_globals, context)
        }
        (
            GenericExpr::Call(span, function, args),
            ResolvedExpr::Call(_, resolved_call, resolved_args),
        ) => {
            if resolved_call.name() != function {
                return unsupported(
                    span,
                    format!(
                        "source call `{function}` rewritten to `{}` by a command macro in {context}",
                        resolved_call.name()
                    ),
                );
            }
            if resolved_call.output().name() != expected_sort || resolved_args.len() != args.len() {
                return Err(CausalSliceError::Invariant(format!(
                    "typed source call `{function}` diverged in {context}"
                )));
            }
            let (input_sorts, primitive) = match resolved_call {
                ResolvedCall::Primitive(primitive) => {
                    let capability =
                        PrimitiveReplayCapability::for_query(span, primitive, context)?;
                    (
                        primitive
                            .input()
                            .iter()
                            .map(|sort| sort.name().to_owned())
                            .collect::<Vec<_>>(),
                        Some(capability),
                    )
                }
                ResolvedCall::Func(function_type) => {
                    let declaration = constructors.get(function).ok_or_else(|| {
                        CausalSliceError::Unsupported {
                            location: span.to_string(),
                            reason: format!(
                                "nested non-constructor call `{function}` in {context}"
                            ),
                        }
                    })?;
                    if declaration.output != expected_sort
                        || function_type.input.len() != declaration.inputs.len()
                        || function_type
                            .input
                            .iter()
                            .zip(&declaration.inputs)
                            .any(|(typed, declared)| typed.name() != declared)
                    {
                        return Err(CausalSliceError::Invariant(format!(
                            "typed constructor `{function}` diverged from its declaration"
                        )));
                    }
                    (declaration.inputs.clone(), None)
                }
                ResolvedCall::Values(..) => {
                    return unsupported(
                        span,
                        format!("a tuple-values expression nested in {context}"),
                    );
                }
            };
            if input_sorts.len() != args.len() {
                return Err(CausalSliceError::Invariant(format!(
                    "typed source call `{function}` changed arity in {context}"
                )));
            }
            let modeled_args = args
                .iter()
                .zip(resolved_args)
                .zip(&input_sorts)
                .map(|((arg, resolved), sort)| {
                    model_typed_atom_arg(arg, resolved, sort, constructors, source_globals, context)
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(AtomArg::App {
                function: function.clone(),
                args: modeled_args,
                input_sorts,
                output_sort: expected_sort.to_owned(),
                primitive,
            })
        }
        _ => Err(CausalSliceError::Invariant(format!(
            "typed source expression changed shape in {context}"
        ))),
    }
}

#[allow(clippy::too_many_arguments)]
fn model_query_primitive(
    span: &Span,
    left: &Expr,
    right: &Expr,
    resolved_fact: &ResolvedFact,
    _known_var_sorts: &IndexMap<String, String>,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
    context: &str,
) -> Result<Option<QueryPrimitiveTemplate>, CausalSliceError> {
    let ResolvedFact::Eq(_, resolved_left, resolved_right) = resolved_fact else {
        return Err(CausalSliceError::Invariant(format!(
            "typed source model changed an equality in {context}"
        )));
    };
    let left_is_primitive = matches!(
        resolved_left,
        ResolvedExpr::Call(_, ResolvedCall::Primitive(_), _)
    );
    let right_is_primitive = matches!(
        resolved_right,
        ResolvedExpr::Call(_, ResolvedCall::Primitive(_), _)
    );
    let (application_expr, output_expr, resolved_application, resolved_output) =
        match (left_is_primitive, right_is_primitive) {
            (true, false) => (left, right, resolved_left, resolved_right),
            (false, true) => (right, left, resolved_right, resolved_left),
            (false, false) => return Ok(None),
            (true, true) => {
                return unsupported(
                    span,
                    format!("an equality between two primitive calls in {context}"),
                );
            }
        };
    let output_sort = resolved_application.output_type().name().to_owned();
    if resolved_output.output_type().name() != output_sort {
        return Err(CausalSliceError::Invariant(format!(
            "typed source primitive equality changed output sort in {context}"
        )));
    }
    if let GenericExpr::Var(output_span, output_name) = output_expr
        && (output_name == "_" || output_name.starts_with('@'))
    {
        return unsupported(
            output_span,
            "wildcard or parser-generated query primitive output variables",
        );
    }
    let application = model_typed_atom_arg(
        application_expr,
        resolved_application,
        &output_sort,
        constructors,
        source_globals,
        context,
    )?;
    let AtomArg::App {
        primitive: Some(capability),
        ..
    } = &application
    else {
        return Err(CausalSliceError::Invariant(format!(
            "typed source primitive equality lost its primitive capability in {context}"
        )));
    };
    let capability = capability.clone();
    let output = model_typed_atom_arg(
        output_expr,
        resolved_output,
        &output_sort,
        constructors,
        source_globals,
        context,
    )?;
    Ok(Some(QueryPrimitiveTemplate {
        span: span.clone(),
        application,
        output: Some(output),
        sort: output_sort,
        capability,
    }))
}

impl PrimitiveReplayCapability {
    fn for_query(
        span: &Span,
        primitive: &SpecializedPrimitive,
        context: &str,
    ) -> Result<Self, CausalSliceError> {
        if primitive.effect() != crate::PrimitiveEffect::Pure {
            return unsupported(
                span,
                format!(
                    "non-Pure primitive `{}` with effect {:?} in {context}",
                    primitive.name(),
                    primitive.effect()
                ),
            );
        }
        if primitive.validator().is_none() {
            return unsupported(
                span,
                format!(
                    "Pure primitive `{}` without a proof validator in {context}",
                    primitive.name()
                ),
            );
        }
        if !primitive.is_replay_safe() {
            return unsupported(
                span,
                format!(
                    "Pure proof-validating primitive `{}` without an explicit deterministic replay capability in {context}",
                    primitive.name()
                ),
            );
        }
        Ok(Self {
            specialization: primitive.clone(),
        })
    }

    fn matches(&self, actual: &SpecializedPrimitive) -> bool {
        self.specialization == *actual
    }
}

fn model_query_predicate(
    expr: &Expr,
    resolved_fact: &ResolvedFact,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
    context: &str,
) -> Result<Option<QueryPrimitiveTemplate>, CausalSliceError> {
    let GenericExpr::Call(span, function, args) = expr else {
        return Ok(None);
    };
    let ResolvedFact::Fact(ResolvedExpr::Call(
        _,
        ResolvedCall::Primitive(primitive),
        resolved_args,
    )) = resolved_fact
    else {
        return Ok(None);
    };
    if primitive.output().name() != "Unit" {
        return Ok(None);
    }
    if primitive.name() != function
        || primitive.input().len() != args.len()
        || resolved_args.len() != args.len()
    {
        return Err(CausalSliceError::Invariant(format!(
            "typed source model changed predicate occurrence `{function}` in {context}"
        )));
    }
    let input_sorts = primitive
        .input()
        .iter()
        .map(|sort| sort.name().to_owned())
        .collect::<Vec<_>>();
    let capability = PrimitiveReplayCapability::for_query(span, primitive, context)?;
    Ok(Some(QueryPrimitiveTemplate {
        span: span.clone(),
        application: AtomArg::App {
            function: function.clone(),
            args: args
                .iter()
                .zip(resolved_args)
                .zip(&input_sorts)
                .map(|((arg, resolved), sort)| {
                    model_typed_atom_arg(arg, resolved, sort, constructors, source_globals, context)
                })
                .collect::<Result<Vec<_>, _>>()?,
            input_sorts,
            output_sort: "Unit".to_owned(),
            primitive: Some(capability.clone()),
        },
        output: Some(AtomArg::Lit(Literal::Unit)),
        sort: "Unit".to_owned(),
        capability,
    }))
}

fn model_constructor_lookup(
    span: &Span,
    left: &Expr,
    right: &Expr,
    resolved_fact: &ResolvedFact,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
    context: &str,
) -> Result<Option<ConstructorLookupTemplate>, CausalSliceError> {
    let ResolvedFact::Eq(_, resolved_left, resolved_right) = resolved_fact else {
        return Err(CausalSliceError::Invariant(format!(
            "typed source model changed an equality in {context}"
        )));
    };
    let (application_expr, output_expr, resolved_application, resolved_output) = match (left, right)
    {
        (GenericExpr::Call(..), GenericExpr::Var(..)) => {
            (left, right, resolved_left, resolved_right)
        }
        (GenericExpr::Var(..), GenericExpr::Call(..)) => {
            (right, left, resolved_right, resolved_left)
        }
        _ => return Ok(None),
    };
    let GenericExpr::Call(call_span, function, args) = application_expr else {
        unreachable!("constructor application orientation was checked above")
    };
    let constructor = constructors
        .get(function)
        .ok_or_else(|| CausalSliceError::Unsupported {
            location: call_span.to_string(),
            reason: format!("function/primitive lookup `{function}` in {context}"),
        })?;
    let GenericExpr::Var(output_span, output_name) = output_expr else {
        unreachable!("constructor output orientation was checked above")
    };
    if output_name == "_" || output_name.starts_with('@') {
        return unsupported(
            output_span,
            "wildcard or parser-generated constructor lookup output variables",
        );
    };
    let application = model_typed_atom_arg(
        application_expr,
        resolved_application,
        &constructor.output,
        constructors,
        source_globals,
        context,
    )?;
    let AtomArg::App {
        args: modeled_args, ..
    } = &application
    else {
        return Err(CausalSliceError::Invariant(
            "modeled constructor lookup lost its application".to_owned(),
        ));
    };
    if args.len() != modeled_args.len() {
        return Err(CausalSliceError::Invariant(
            "constructor lookup source/model arity diverged".to_owned(),
        ));
    }
    let output = model_typed_atom_arg(
        output_expr,
        resolved_output,
        &constructor.output,
        constructors,
        source_globals,
        context,
    )?;
    Ok(Some(ConstructorLookupTemplate {
        span: span.clone(),
        application,
        output,
        sort: constructor.output.clone(),
    }))
}

fn model_function_lookup(
    span: &Span,
    left: &Expr,
    right: &Expr,
    mutable_functions: &IndexMap<String, MutableFunctionDecl>,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
    context: &str,
) -> Result<Option<FunctionLookupTemplate>, CausalSliceError> {
    let left_function = match left {
        GenericExpr::Call(_, function, args) if mutable_functions.contains_key(function) => {
            Some((function, args))
        }
        _ => None,
    };
    let right_function = match right {
        GenericExpr::Call(_, function, args) if mutable_functions.contains_key(function) => {
            Some((function, args))
        }
        _ => None,
    };
    let ((function, keys), output) = match (left_function, right_function) {
        (Some(call), None) => (call, right),
        (None, Some(call)) => (call, left),
        (None, None) => return Ok(None),
        (Some(_), Some(_)) => {
            return unsupported(
                span,
                format!("two mutable function calls in one equality in {context}"),
            );
        }
    };
    let declaration = &mutable_functions[function];
    if let Some(sort) = &declaration.opaque_sort {
        return unsupported(
            span,
            format!(
                "lookup of function `{function}` with opaque container sort `{sort}` in {context}"
            ),
        );
    }
    if keys.len() != declaration.inputs.len() {
        return unsupported(
            span,
            format!(
                "lookup of function `{function}` with {} keys instead of {} in {context}",
                keys.len(),
                declaration.inputs.len()
            ),
        );
    }
    Ok(Some(FunctionLookupTemplate {
        span: span.clone(),
        function: function.clone(),
        keys: keys
            .iter()
            .zip(&declaration.inputs)
            .map(|(key, sort)| model_atom_arg(key, sort, constructors, source_globals, context))
            .collect::<Result<Vec<_>, _>>()?,
        output: model_atom_arg(
            output,
            &declaration.output,
            constructors,
            source_globals,
            context,
        )?,
        input_sorts: declaration.inputs.clone(),
        output_sort: declaration.output.clone(),
    }))
}

fn infer_equality_expr_sort(
    expr: &Expr,
    known_var_sorts: &IndexMap<String, String>,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
    context: &str,
) -> Result<Option<String>, CausalSliceError> {
    match expr {
        GenericExpr::Var(_, var) => Ok(source_globals
            .get(var)
            .or_else(|| known_var_sorts.get(var))
            .cloned()),
        GenericExpr::Lit(_, literal) => Ok(Some(
            match literal {
                Literal::Int(_) => "i64",
                Literal::Float(_) => "f64",
                Literal::String(_) => "String",
                Literal::Bool(_) => "bool",
                Literal::Unit => "Unit",
            }
            .to_owned(),
        )),
        GenericExpr::Call(span, function, _) => constructors
            .get(function)
            .map(|constructor| Some(constructor.output.clone()))
            .ok_or_else(|| CausalSliceError::Unsupported {
                location: span.to_string(),
                reason: format!("equality or primitive function lookup `{function}` in {context}"),
            }),
    }
}

fn register_equality_vars(
    equality: &EqualityTemplate,
    order: &mut Vec<String>,
    sorts: &mut IndexMap<String, String>,
) -> Result<(), CausalSliceError> {
    register_arg_vars(&equality.left, &equality.sort, order, sorts)?;
    register_arg_vars(&equality.right, &equality.sort, order, sorts)
}

fn variable_check_fact_occurrences<'a>(
    atoms: &'a [AtomTemplate],
    equalities: &'a [EqualityTemplate],
) -> HashMap<&'a str, usize> {
    let mut occurrences = variable_atom_occurrences(atoms);
    for equality in equalities {
        let mut vars = HashSet::default();
        for (_, var) in atom_arg_vars(&equality.left)
            .into_iter()
            .chain(atom_arg_vars(&equality.right))
        {
            vars.insert(var.as_str());
        }
        for var in vars {
            *occurrences.entry(var).or_default() += 1;
        }
    }
    occurrences
}

fn variable_atom_occurrences(atoms: &[AtomTemplate]) -> HashMap<&str, usize> {
    let mut occurrences = HashMap::default();
    for atom in atoms {
        let mut vars_in_atom = HashSet::default();
        for arg in &atom.args {
            for (_, var) in atom_arg_vars(arg) {
                vars_in_atom.insert(var.as_str());
            }
        }
        for var in vars_in_atom {
            *occurrences.entry(var).or_default() += 1;
        }
    }
    occurrences
}

#[allow(clippy::too_many_arguments)]
fn model_source_fact(
    id: SourceFactId,
    command_index: usize,
    action: &Action,
    resolved_action: Option<&ResolvedAction>,
    relations: &IndexMap<String, RelationDecl>,
    constructors: &IndexMap<String, ConstructorDecl>,
    mutable_functions: &IndexMap<String, MutableFunctionDecl>,
    source_globals: &IndexMap<String, String>,
) -> Result<SourceFact, CausalSliceError> {
    if let GenericAction::Let(_, name, expr) = action {
        let GenericExpr::Call(_, function, _) = expr else {
            return unsupported(
                &expr.span(),
                "a source global not rooted in an immutable constructor".to_owned(),
            );
        };
        if !constructors.contains_key(function) {
            return unsupported(
                &expr.span(),
                format!("source global `{name}` rooted in primitive or function `{function}`"),
            );
        }
        let sort = validate_closed_source_expr(expr, constructors, source_globals)?;
        let _application =
            if let Some(GenericAction::Let(_, resolved_name, resolved_expr)) = resolved_action {
                if resolved_name.name != *name || resolved_expr.output_type().name() != sort {
                    return Err(CausalSliceError::Invariant(format!(
                        "typed source global `{name}` diverged from its source action"
                    )));
                }
                model_typed_atom_arg(
                    expr,
                    resolved_expr,
                    &sort,
                    constructors,
                    source_globals,
                    "source global",
                )?
            } else if resolved_action.is_some() {
                return Err(CausalSliceError::Invariant(format!(
                    "typed source action changed global `{name}`"
                )));
            } else {
                model_atom_arg(expr, &sort, constructors, source_globals, "source global")?
            };
        return Ok(SourceFact {
            id,
            command_index,
            expansion_index: None,
            kind: SourceFactKind::GlobalConstructor {
                name: name.clone(),
                sort,
            },
        });
    }

    if let GenericAction::Set(span, function, keys, value) = action {
        let declaration =
            mutable_functions
                .get(function)
                .ok_or_else(|| CausalSliceError::Unsupported {
                    location: span.to_string(),
                    reason: format!(
                        "a source set of function `{function}` without a causally modeled merge"
                    ),
                })?;
        if let Some(sort) = &declaration.opaque_sort {
            return unsupported(
                span,
                format!("a source set of function `{function}` with opaque sort `{sort}`"),
            );
        }
        if keys.len() != declaration.inputs.len() {
            return unsupported(
                span,
                format!(
                    "a source set of function `{function}` with {} keys instead of {}",
                    keys.len(),
                    declaration.inputs.len()
                ),
            );
        }
        let modeled_keys = keys
            .iter()
            .zip(&declaration.inputs)
            .map(|(key, sort)| {
                model_atom_arg(
                    key,
                    sort,
                    constructors,
                    source_globals,
                    "source function set",
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let modeled_value = model_atom_arg(
            value,
            &declaration.output,
            constructors,
            source_globals,
            "source function set",
        )?;
        for arg in modeled_keys.iter().chain(std::iter::once(&modeled_value)) {
            if let Some((span, variable)) = atom_arg_vars(arg).into_iter().next() {
                return unsupported(
                    span,
                    format!("non-ground source function-set variable `{variable}`"),
                );
            }
        }
        return Ok(SourceFact {
            id,
            command_index,
            expansion_index: None,
            kind: SourceFactKind::FunctionSet(FunctionSetTemplate {
                span: span.clone(),
                function: function.clone(),
                keys: modeled_keys,
                value: modeled_value,
                input_sorts: declaration.inputs.clone(),
                output_sort: declaration.output.clone(),
            }),
        });
    }

    let GenericAction::Expr(_, expr) = action else {
        return unsupported_action(action, "a non-insert initialization action");
    };
    let GenericExpr::Call(span, function, _) = expr else {
        return unsupported(&expr.span(), "a non-call source initialization".to_owned());
    };
    let kind = if relations.contains_key(function) {
        SourceFactKind::Relation(model_atom(
            expr,
            relations,
            constructors,
            source_globals,
            "source initialization",
        )?)
    } else if let Some(constructor) = constructors.get(function) {
        SourceFactKind::Constructor(model_atom_arg(
            expr,
            &constructor.output,
            constructors,
            source_globals,
            "source initialization",
        )?)
    } else {
        return unsupported(
            span,
            format!("primitive or function call `{function}` in source initialization"),
        );
    };
    let args = match &kind {
        SourceFactKind::Relation(atom) => atom.args.as_slice(),
        SourceFactKind::Constructor(application) => std::slice::from_ref(application),
        SourceFactKind::GlobalConstructor { .. } => {
            unreachable!("source globals return before ordinary source-fact validation")
        }
        SourceFactKind::FunctionSet(..) => {
            unreachable!("source function sets return before ordinary source-fact validation")
        }
    };
    for arg in args {
        if let Some((span, var)) = atom_arg_vars(arg).into_iter().next() {
            return unsupported(
                span,
                format!("non-ground source initialization variable `{var}`"),
            );
        }
    }
    Ok(SourceFact {
        id,
        command_index,
        expansion_index: None,
        kind,
    })
}

fn validate_closed_source_expr(
    expr: &Expr,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
) -> Result<String, CausalSliceError> {
    match expr {
        GenericExpr::Lit(_, literal) => Ok(match literal {
            Literal::Int(_) => "i64",
            Literal::Float(_) => "f64",
            Literal::String(_) => "String",
            Literal::Bool(_) => "bool",
            Literal::Unit => "Unit",
        }
        .to_owned()),
        GenericExpr::Var(span, name) => {
            source_globals
                .get(name)
                .cloned()
                .ok_or_else(|| CausalSliceError::Unsupported {
                    location: span.to_string(),
                    reason: format!("an unknown or non-global source binding `{name}`"),
                })
        }
        GenericExpr::Call(span, function, args) => {
            let (input_sorts, output_sort): (&[&str], &str) = if let Some(constructor) =
                constructors.get(function)
            {
                let input_sorts = constructor
                    .inputs
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>();
                return validate_closed_source_call(
                    span,
                    function,
                    args,
                    &input_sorts,
                    &constructor.output,
                    constructors,
                    source_globals,
                );
            } else {
                match function.as_str() {
                    "bigint" => (&["i64"], "BigInt"),
                    "from-string" => (&["String"], "BigInt"),
                    "bigrat" => (&["BigInt", "BigInt"], "BigRat"),
                    _ => {
                        return unsupported(
                            span,
                            format!(
                                "primitive or function `{function}` in a source global expression"
                            ),
                        );
                    }
                }
            };
            validate_closed_source_call(
                span,
                function,
                args,
                input_sorts,
                output_sort,
                constructors,
                source_globals,
            )
        }
    }
}

fn validate_closed_source_call(
    span: &Span,
    function: &str,
    args: &[Expr],
    input_sorts: &[&str],
    output_sort: &str,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
) -> Result<String, CausalSliceError> {
    if args.len() != input_sorts.len() {
        return unsupported(
            span,
            format!(
                "source global call `{function}` with arity {} instead of {}",
                args.len(),
                input_sorts.len()
            ),
        );
    }
    for (arg, expected) in args.iter().zip(input_sorts) {
        let actual = validate_closed_source_expr(arg, constructors, source_globals)?;
        if actual != *expected {
            return unsupported(
                &arg.span(),
                format!(
                    "source global call `{function}` expecting `{expected}` but receiving `{actual}`"
                ),
            );
        }
    }
    Ok(output_sort.to_owned())
}

fn source_fact_command(span: &Span, fact: &SourceFact) -> Command {
    let SourceFactKind::Relation(atom) = &fact.kind else {
        panic!("only expanded input relation rows are rendered as source fact commands")
    };
    let args = atom
        .args
        .iter()
        .map(|arg| source_atom_arg_expr(span, arg))
        .collect();
    Command::Action(GenericAction::Expr(
        span.clone(),
        Expr::Call(span.clone(), atom.relation.clone(), args),
    ))
}

fn source_atom_arg_expr(span: &Span, arg: &AtomArg) -> Expr {
    match arg {
        AtomArg::Lit(literal) => Expr::Lit(span.clone(), literal.clone()),
        AtomArg::Global { name, .. } => Expr::Var(span.clone(), name.clone()),
        AtomArg::App { function, args, .. } => Expr::Call(
            span.clone(),
            function.clone(),
            args.iter()
                .map(|arg| source_atom_arg_expr(span, arg))
                .collect(),
        ),
        AtomArg::Var(_, var) => panic!("validated source fact retained variable `{var}`"),
    }
}

fn model_atom(
    expr: &Expr,
    relations: &IndexMap<String, RelationDecl>,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
    context: &str,
) -> Result<AtomTemplate, CausalSliceError> {
    let GenericExpr::Call(span, relation, args) = expr else {
        return unsupported(&expr.span(), format!("a non-relation fact in {context}"));
    };
    let declaration = relations
        .get(relation)
        .ok_or_else(|| CausalSliceError::Unsupported {
            location: span.to_string(),
            reason: format!("primitive or function call `{relation}` in {context}"),
        })?;
    if let Some(sort) = &declaration.opaque_sort {
        return unsupported(
            span,
            format!("relation `{relation}` with opaque container sort `{sort}` in {context}"),
        );
    }
    if args.len() != declaration.sorts.len() {
        return unsupported(
            span,
            format!(
                "relation `{relation}` with arity {} instead of {} in {context}",
                args.len(),
                declaration.sorts.len()
            ),
        );
    }
    let args = args
        .iter()
        .zip(&declaration.sorts)
        .map(|(arg, sort)| model_atom_arg(arg, sort, constructors, source_globals, context))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(AtomTemplate {
        relation: relation.clone(),
        args,
    })
}

fn model_typed_atom(
    expr: &Expr,
    resolved: &ResolvedExpr,
    relations: &IndexMap<String, RelationDecl>,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
    context: &str,
) -> Result<AtomTemplate, CausalSliceError> {
    let GenericExpr::Call(span, relation, args) = expr else {
        return unsupported(&expr.span(), format!("a non-relation fact in {context}"));
    };
    let declaration = relations
        .get(relation)
        .ok_or_else(|| CausalSliceError::Unsupported {
            location: span.to_string(),
            reason: format!("primitive or function call `{relation}` in {context}"),
        })?;
    let ResolvedExpr::Call(_, ResolvedCall::Func(function), resolved_args) = resolved else {
        return Err(CausalSliceError::Invariant(format!(
            "typed source relation `{relation}` changed call kind in {context}"
        )));
    };
    if function.name != *relation
        || function.input.len() != declaration.sorts.len()
        || function
            .input
            .iter()
            .zip(&declaration.sorts)
            .any(|(typed, declared)| typed.name() != declared)
        || resolved_args.len() != args.len()
    {
        return Err(CausalSliceError::Invariant(format!(
            "typed source relation `{relation}` diverged from its declaration in {context}"
        )));
    }
    if let Some(sort) = &declaration.opaque_sort {
        return unsupported(
            span,
            format!("relation `{relation}` with opaque container sort `{sort}` in {context}"),
        );
    }
    let args = args
        .iter()
        .zip(resolved_args)
        .zip(&declaration.sorts)
        .map(|((arg, resolved), sort)| {
            model_typed_atom_arg(arg, resolved, sort, constructors, source_globals, context)
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(AtomTemplate {
        relation: relation.clone(),
        args,
    })
}

fn model_atom_arg(
    expr: &Expr,
    expected_sort: &str,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
    context: &str,
) -> Result<AtomArg, CausalSliceError> {
    match expr {
        GenericExpr::Var(span, var) => {
            if var == "_" || var.starts_with('@') {
                unsupported(
                    span,
                    "wildcard or parser-generated variables (they have no stable source binding)",
                )
            } else if let Some(actual_sort) = source_globals.get(var) {
                if actual_sort != expected_sort {
                    return unsupported(
                        span,
                        format!(
                            "source global `{var}` has sort `{actual_sort}` instead of `{expected_sort}` in {context}"
                        ),
                    );
                }
                Ok(AtomArg::Global {
                    name: var.clone(),
                    sort: expected_sort.to_owned(),
                })
            } else {
                Ok(AtomArg::Var(span.clone(), var.clone()))
            }
        }
        GenericExpr::Lit(span, literal) => {
            validate_printable_literal(span, literal)?;
            Ok(AtomArg::Lit(literal.clone()))
        }
        GenericExpr::Call(span, function, args) => {
            let Some(constructor) = constructors.get(function) else {
                let scalar_constructor_inputs: Option<&[&str]> =
                    match (expected_sort, function.as_str()) {
                        ("BigInt", "bigint") => Some(&["i64"]),
                        ("BigRat", "bigrat") => Some(&["BigInt", "BigInt"]),
                        _ => None,
                    };
                if let Some(input_sorts) = scalar_constructor_inputs {
                    if args.len() != input_sorts.len() {
                        return unsupported(
                            span,
                            format!(
                                "scalar constructor `{function}` with arity {} instead of {} in {context}",
                                args.len(),
                                input_sorts.len()
                            ),
                        );
                    }
                    return Ok(AtomArg::App {
                        function: function.clone(),
                        args: args
                            .iter()
                            .zip(input_sorts)
                            .map(|(arg, sort)| {
                                model_atom_arg(arg, sort, constructors, source_globals, context)
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                        input_sorts: input_sorts.iter().map(|sort| (*sort).to_owned()).collect(),
                        output_sort: expected_sort.to_owned(),
                        primitive: None,
                    });
                }
                if replay_primitive_head_context(context)
                    && expected_sort == "BigRat"
                    && let Some(arity) = replay_safe_bigrat_primitive_arity(function)
                {
                    if args.len() != arity {
                        return unsupported(
                            span,
                            format!(
                                "BigRat `{function}` with arity {} instead of {arity} in {context}",
                                args.len(),
                            ),
                        );
                    }
                    return Ok(AtomArg::App {
                        function: function.clone(),
                        args: args
                            .iter()
                            .map(|arg| {
                                model_atom_arg(arg, "BigRat", constructors, source_globals, context)
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                        input_sorts: vec!["BigRat".to_owned(); arity],
                        output_sort: "BigRat".to_owned(),
                        primitive: None,
                    });
                }
                return Err(CausalSliceError::Unsupported {
                    location: span.to_string(),
                    reason: format!("nested non-constructor call `{function}` in {context}"),
                });
            };
            if let Some(sort) = &constructor.opaque_sort {
                return unsupported(
                    span,
                    format!(
                        "constructor `{function}` with opaque container sort `{sort}` in {context}"
                    ),
                );
            }
            if constructor.output != expected_sort {
                return unsupported(
                    span,
                    format!(
                        "constructor `{function}` returning `{}` where `{expected_sort}` is required in {context}",
                        constructor.output
                    ),
                );
            }
            if args.len() != constructor.inputs.len() {
                return unsupported(
                    span,
                    format!(
                        "constructor `{function}` with arity {} instead of {} in {context}",
                        args.len(),
                        constructor.inputs.len()
                    ),
                );
            }
            Ok(AtomArg::App {
                function: function.clone(),
                args: args
                    .iter()
                    .zip(&constructor.inputs)
                    .map(|(arg, sort)| {
                        model_atom_arg(arg, sort, constructors, source_globals, context)
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                input_sorts: constructor.inputs.clone(),
                output_sort: constructor.output.clone(),
                primitive: None,
            })
        }
    }
}

fn replay_primitive_head_context(context: &str) -> bool {
    context == "rule head" || (context.starts_with("rule `") && context.ends_with("` union head"))
}

fn replay_safe_bigrat_primitive_arity(function: &str) -> Option<usize> {
    match function {
        "+" | "-" | "*" | "/" => Some(2),
        "neg" | "abs" | "floor" | "ceil" | "round" => Some(1),
        _ => None,
    }
}

fn collect_nested_query_primitives(
    application: &AtomArg,
    span: &Span,
    primitives: &mut Vec<QueryPrimitiveTemplate>,
) {
    let AtomArg::App { args, .. } = application else {
        return;
    };
    for arg in args {
        collect_intermediate_query_primitives(span, arg, primitives);
    }
}

fn collect_intermediate_query_primitives(
    span: &Span,
    arg: &AtomArg,
    primitives: &mut Vec<QueryPrimitiveTemplate>,
) {
    let AtomArg::App {
        args,
        output_sort,
        primitive,
        ..
    } = arg
    else {
        return;
    };
    for child in args {
        collect_intermediate_query_primitives(span, child, primitives);
    }
    if let Some(capability) = primitive
        && resolved_auxiliary_scalar_primitive(&capability.specialization).is_none()
    {
        primitives.push(QueryPrimitiveTemplate {
            span: span.clone(),
            application: arg.clone(),
            output: None,
            sort: output_sort.clone(),
            capability: capability.clone(),
        });
    }
}

/// Compare source-level applications while deliberately ignoring spans. This
/// is stricter than equality modulo the e-graph: a replay-safe subsume target
/// must be the same logical constructor application that made the body match,
/// not merely another term in its eventual e-class.
fn same_atom_arg_shape(left: &AtomArg, right: &AtomArg) -> bool {
    match (left, right) {
        (AtomArg::Var(_, left), AtomArg::Var(_, right)) => left == right,
        (
            AtomArg::Global {
                name: left_name,
                sort: left_sort,
            },
            AtomArg::Global {
                name: right_name,
                sort: right_sort,
            },
        ) => left_name == right_name && left_sort == right_sort,
        (AtomArg::Lit(left), AtomArg::Lit(right)) => left == right,
        (
            AtomArg::App {
                function: left_function,
                args: left_args,
                input_sorts: left_inputs,
                output_sort: left_output,
                ..
            },
            AtomArg::App {
                function: right_function,
                args: right_args,
                input_sorts: right_inputs,
                output_sort: right_output,
                ..
            },
        ) => {
            left_function == right_function
                && left_inputs == right_inputs
                && left_output == right_output
                && left_args.len() == right_args.len()
                && left_args
                    .iter()
                    .zip(right_args)
                    .all(|(left, right)| same_atom_arg_shape(left, right))
        }
        _ => false,
    }
}

fn collect_replay_primitives(arg: &AtomArg, primitives: &mut Vec<AtomArg>) {
    let AtomArg::App {
        function,
        args,
        input_sorts,
        output_sort,
        primitive,
    } = arg
    else {
        return;
    };
    for arg in args {
        collect_replay_primitives(arg, primitives);
    }
    if primitive.is_some()
        || (replay_safe_bigrat_primitive_arity(function) == Some(input_sorts.len())
            && input_sorts.iter().all(|sort| sort == "BigRat")
            && output_sort == "BigRat")
    {
        primitives.push(arg.clone());
    }
}

fn atom_arg_vars(arg: &AtomArg) -> Vec<(&Span, &String)> {
    match arg {
        AtomArg::Var(span, var) => vec![(span, var)],
        AtomArg::Global { .. } | AtomArg::Lit(_) => Vec::new(),
        AtomArg::App { args, .. } => args.iter().flat_map(atom_arg_vars).collect(),
    }
}

fn collect_atom_arg_globals<'a>(arg: &'a AtomArg, globals: &mut IndexMap<&'a str, &'a str>) {
    match arg {
        AtomArg::Global { name, sort } => {
            if let Some(previous) = globals.insert(name, sort) {
                debug_assert_eq!(previous, sort);
            }
        }
        AtomArg::App { args, .. } => {
            for arg in args {
                collect_atom_arg_globals(arg, globals);
            }
        }
        AtomArg::Var(..) | AtomArg::Lit(..) => {}
    }
}

fn rule_global_uses(rule: &RuleModel) -> IndexMap<&str, &str> {
    let mut globals = IndexMap::default();
    for atom in rule.body.iter().chain(&rule.head) {
        for arg in &atom.args {
            collect_atom_arg_globals(arg, &mut globals);
        }
    }
    for lookup in &rule.body_lookups {
        collect_atom_arg_globals(&lookup.application, &mut globals);
        collect_atom_arg_globals(&lookup.output, &mut globals);
    }
    for equality in &rule.body_equalities {
        collect_atom_arg_globals(&equality.left, &mut globals);
        collect_atom_arg_globals(&equality.right, &mut globals);
    }
    for lookup in &rule.body_functions {
        for key in &lookup.keys {
            collect_atom_arg_globals(key, &mut globals);
        }
        collect_atom_arg_globals(&lookup.output, &mut globals);
    }
    for primitive in &rule.body_primitives {
        collect_atom_arg_globals(&primitive.application, &mut globals);
        if let Some(output) = &primitive.output {
            collect_atom_arg_globals(output, &mut globals);
        }
    }
    for local in &rule.head_lets {
        collect_atom_arg_globals(&local.value, &mut globals);
    }
    for constructor in &rule.head_constructors {
        collect_atom_arg_globals(constructor, &mut globals);
    }
    for set in &rule.head_sets {
        for key in &set.keys {
            collect_atom_arg_globals(key, &mut globals);
        }
        collect_atom_arg_globals(&set.value, &mut globals);
    }
    for subsume in &rule.head_subsumes {
        collect_atom_arg_globals(subsume, &mut globals);
    }
    for equality in &rule.head_unions {
        collect_atom_arg_globals(&equality.left, &mut globals);
        collect_atom_arg_globals(&equality.right, &mut globals);
    }
    globals
}

fn check_global_uses(check: &CheckModel) -> IndexMap<&str, &str> {
    let mut globals = IndexMap::default();
    for atom in &check.atoms {
        for arg in &atom.args {
            collect_atom_arg_globals(arg, &mut globals);
        }
    }
    for equality in &check.equalities {
        collect_atom_arg_globals(&equality.left, &mut globals);
        collect_atom_arg_globals(&equality.right, &mut globals);
    }
    globals
}

fn register_atom_vars(
    atom: &AtomTemplate,
    relations: &IndexMap<String, RelationDecl>,
    order: &mut Vec<String>,
    sorts: &mut IndexMap<String, String>,
) -> Result<(), CausalSliceError> {
    let declaration = &relations[&atom.relation];
    for (arg, sort) in atom.args.iter().zip(&declaration.sorts) {
        register_arg_vars(arg, sort, order, sorts)?;
    }
    Ok(())
}

fn register_arg_vars(
    arg: &AtomArg,
    sort: &str,
    order: &mut Vec<String>,
    sorts: &mut IndexMap<String, String>,
) -> Result<(), CausalSliceError> {
    match arg {
        AtomArg::Var(span, var) => match sorts.get(var) {
            Some(previous) if previous != sort => unsupported(
                span,
                format!("variable `{var}` used at both sort `{previous}` and `{sort}`"),
            ),
            Some(_) => Ok(()),
            None => {
                sorts.insert(var.clone(), sort.to_owned());
                order.push(var.clone());
                Ok(())
            }
        },
        AtomArg::Global { .. } | AtomArg::Lit(_) => Ok(()),
        AtomArg::App {
            args, input_sorts, ..
        } => {
            for (arg, sort) in args.iter().zip(input_sorts) {
                register_arg_vars(arg, sort, order, sorts)?;
            }
            Ok(())
        }
    }
}

fn validate_input_schedule(schedule: &Schedule) -> Result<(), CausalSliceError> {
    match schedule {
        Schedule::Run(span, config) => {
            if config.until.is_some() {
                unsupported(span, "`:until` observations inside a schedule".to_owned())
            } else {
                Ok(())
            }
        }
        Schedule::RunRule(span, _)
        | Schedule::RunRuleBatch(span, _)
        | Schedule::RunRuleBatchPacked(span, _) => unsupported(
            span,
            "manual `run-rule` or `run-rule-batch` in the input program".to_owned(),
        ),
        Schedule::Saturate(_, inner) | Schedule::Repeat(_, _, inner) => {
            validate_input_schedule(inner)
        }
        Schedule::Sequence(_, schedules) => {
            for schedule in schedules {
                validate_input_schedule(schedule)?;
            }
            Ok(())
        }
    }
}

fn elaborate_source_fact(
    egraph: &EGraph,
    fact: &SourceFact,
    source_traces: &IndexMap<usize, SourceExecutionTrace>,
    trace_functions: &IndexMap<TableId, TraceFunctionMeta>,
    relations: &IndexMap<String, RelationDecl>,
    witnesses: &mut WitnessArena,
    prefix_fallback: bool,
) -> Result<Vec<RowKey>, CausalSliceError> {
    if matches!(fact.kind, SourceFactKind::FunctionSet(..)) {
        return Err(CausalSliceError::Invariant(
            "source function set reached relation/constructor elaboration".to_owned(),
        ));
    }
    if let Some(trace) = source_traces.get(&fact.command_index) {
        let mut observed = Vec::new();
        let mut new_rows = Vec::new();
        for batch in &trace.batches {
            witnesses.load_current_globals(&batch.globals)?;
            if !batch.unions.is_empty() {
                return Err(CausalSliceError::Unsupported {
                    location: format!("source command {}", fact.command_index),
                    reason: "a source constructor/merge that committed a union".to_owned(),
                });
            }
            for application in &batch.applications {
                if application.origin.index() >= batch.matches.len() {
                    return Err(CausalSliceError::Invariant(format!(
                        "source application origin {} exceeded {} matches",
                        application.origin.index(),
                        batch.matches.len()
                    )));
                }
            }
            for application in &batch.primitives {
                if application.origin.index() >= batch.matches.len() {
                    return Err(CausalSliceError::Invariant(format!(
                        "source primitive origin {} exceeded {} matches",
                        application.origin.index(),
                        batch.matches.len()
                    )));
                }
            }
            let effects = elaborate_fire_applications(
                egraph,
                batch.applications.iter(),
                trace_functions,
                witnesses,
                prefix_fallback,
                None,
            )?;
            observed.extend(effects.observed_rows);
            new_rows.extend(effects.new_rows);
            // Source commands are preserved in full, so their constructor
            // syntax is available before every replay leaf without a retained
            // dynamic firing dependency.
        }
        match &fact.kind {
            SourceFactKind::Relation(atom) => {
                if trace.global_endpoint.is_some() {
                    return Err(CausalSliceError::Invariant(format!(
                        "source relation command {} captured a global endpoint",
                        fact.command_index
                    )));
                }
                let expected = ground_atoms(
                    egraph,
                    std::slice::from_ref(atom),
                    &IndexMap::default(),
                    witnesses,
                    relations,
                )?;
                if !same_row_multiset(&expected, &observed) {
                    return Err(CausalSliceError::Invariant(format!(
                        "native source applications for command {} do not match its source relation fact",
                        fact.command_index
                    )));
                }
            }
            SourceFactKind::Constructor(application) => {
                if trace.global_endpoint.is_some() || !observed.is_empty() || !new_rows.is_empty() {
                    return Err(CausalSliceError::Invariant(format!(
                        "source constructor command {} unexpectedly produced relation rows",
                        fact.command_index
                    )));
                }
                let AtomArg::App { output_sort, .. } = application else {
                    return Err(CausalSliceError::Invariant(
                        "source constructor initialization stopped being an application".to_owned(),
                    ));
                };
                let _endpoint = ground_arg(
                    egraph,
                    application,
                    output_sort,
                    &IndexMap::default(),
                    witnesses,
                )?;
            }
            SourceFactKind::GlobalConstructor { name, sort, .. } => {
                if !observed.is_empty() || !new_rows.is_empty() {
                    return Err(CausalSliceError::Invariant(format!(
                        "source global command {} unexpectedly produced relation rows",
                        fact.command_index
                    )));
                }
                let endpoint = trace.global_endpoint.ok_or_else(|| {
                    CausalSliceError::Invariant(format!(
                        "source global `{name}` did not capture its definition-time endpoint"
                    ))
                })?;
                let Some(witness) = witnesses.by_endpoint(sort, endpoint) else {
                    return Err(CausalSliceError::Unsupported {
                        location: format!("source global `{name}`"),
                        reason: "a constructor result without an immutable replay witness"
                            .to_owned(),
                    });
                };
                witnesses.bind_global(name, sort, endpoint, witness)?;
            }
            SourceFactKind::FunctionSet(..) => unreachable!("checked before source tracing"),
        }
        Ok(new_rows)
    } else {
        match &fact.kind {
            SourceFactKind::Relation(..) => {
                Ok(vec![source_row(egraph, relations, fact, witnesses)?])
            }
            SourceFactKind::Constructor(..) => Err(CausalSliceError::Invariant(format!(
                "source constructor command {} had no native trace",
                fact.command_index
            ))),
            SourceFactKind::GlobalConstructor { .. } => Err(CausalSliceError::Invariant(format!(
                "source global command {} had no native trace",
                fact.command_index
            ))),
            SourceFactKind::FunctionSet(..) => unreachable!("checked before source tracing"),
        }
    }
}

fn elaborate_source_scalar_arg(
    egraph: &EGraph,
    arg: &AtomArg,
    sort: &str,
    applications: &[&PrimitiveApplication],
    cursor: &mut usize,
    witnesses: &mut WitnessArena,
) -> Result<(TypedEndpoint, WitnessId), CausalSliceError> {
    match arg {
        AtomArg::Lit(literal) => {
            let value = literal_to_value(egraph.backend.base_values(), literal);
            let witness = scalar_witness(
                egraph,
                sort,
                value,
                witnesses,
                "source function-set literal",
            )?;
            Ok((
                TypedEndpoint {
                    sort: sort.to_owned(),
                    value,
                },
                witness,
            ))
        }
        AtomArg::Global {
            name,
            sort: modeled_sort,
        } => {
            if modeled_sort != sort {
                return Err(CausalSliceError::Invariant(format!(
                    "source function-set global `{name}` changed sort"
                )));
            }
            let value = witnesses.global(name, sort)?;
            Ok((
                TypedEndpoint {
                    sort: sort.to_owned(),
                    value,
                },
                witnesses.global_witness(name, sort)?,
            ))
        }
        AtomArg::Var(_, variable) => Err(CausalSliceError::Invariant(format!(
            "validated source function set retained variable `{variable}`"
        ))),
        AtomArg::App {
            function,
            args,
            input_sorts,
            output_sort,
            ..
        } if matches!(function.as_str(), "bigint" | "bigrat") => {
            if output_sort != sort {
                return Err(CausalSliceError::Invariant(format!(
                    "source scalar constructor `{function}` changed output sort"
                )));
            }
            let children = args
                .iter()
                .zip(input_sorts)
                .map(|(child, child_sort)| {
                    elaborate_source_scalar_arg(
                        egraph,
                        child,
                        child_sort,
                        applications,
                        cursor,
                        witnesses,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            let application = applications.get(*cursor).copied().ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "source scalar constructor `{function}` had no native primitive receipt"
                ))
            })?;
            *cursor += 1;
            let (_, expected_function) =
                resolve_auxiliary_scalar_function(egraph, function, crate::Context::Full)?;
            if application.function != expected_function {
                return Err(CausalSliceError::Invariant(format!(
                    "source scalar constructor `{function}` used an unexpected runtime specialization"
                )));
            }
            let child_values = children
                .iter()
                .map(|(endpoint, _)| endpoint.value)
                .collect::<Vec<_>>();
            if application.args != child_values {
                return Err(CausalSliceError::Invariant(format!(
                    "source scalar constructor `{function}` arguments diverged from its syntax"
                )));
            }
            let witness = witnesses.intern_app(
                sort,
                function,
                children.into_iter().map(|(_, witness)| witness).collect(),
                application.result,
                DepArena::EMPTY,
                true,
            )?;
            Ok((
                TypedEndpoint {
                    sort: sort.to_owned(),
                    value: application.result,
                },
                witness,
            ))
        }
        AtomArg::App { function, .. } => Err(CausalSliceError::Unsupported {
            location: format!("source function-set argument `{function}`"),
            reason: "an inline equality constructor in a mutable source set; bind it to a source global first"
                .to_owned(),
        }),
    }
}

fn elaborate_source_function_set(
    egraph: &EGraph,
    fact: &SourceFact,
    source_traces: &IndexMap<usize, SourceExecutionTrace>,
    trace_functions: &IndexMap<TableId, TraceFunctionMeta>,
    witnesses: &mut WitnessArena,
) -> Result<(FunctionRowKey, TypedEndpoint), CausalSliceError> {
    let SourceFactKind::FunctionSet(set) = &fact.kind else {
        return Err(CausalSliceError::Invariant(
            "non-function source fact reached function-set elaboration".to_owned(),
        ));
    };
    let trace = source_traces.get(&fact.command_index).ok_or_else(|| {
        CausalSliceError::Invariant(format!(
            "source function set command {} had no native trace",
            fact.command_index
        ))
    })?;
    if trace.global_endpoint.is_some() {
        return Err(CausalSliceError::Invariant(format!(
            "source function set command {} captured a global endpoint",
            fact.command_index
        )));
    }
    let table_applications = trace
        .batches
        .iter()
        .map(|batch| batch.applications.len())
        .sum::<usize>();
    let unions = trace
        .batches
        .iter()
        .map(|batch| batch.unions.len())
        .sum::<usize>();
    if table_applications != 0 || unions != 0 {
        return Err(CausalSliceError::Unsupported {
            location: set.span.to_string(),
            reason: format!(
                "a source set of `{}` with {table_applications} constructor/table applications and {unions} unions",
                set.function
            ),
        });
    }
    let applications = trace
        .batches
        .iter()
        .flat_map(|batch| &batch.primitives)
        .collect::<Vec<_>>();
    let receipts = trace
        .batches
        .iter()
        .flat_map(|batch| &batch.mutations)
        .collect::<Vec<_>>();
    let [receipt] = receipts.as_slice() else {
        return Err(CausalSliceError::Unsupported {
            location: set.span.to_string(),
            reason: format!(
                "a source set of `{}` producing {} mutable commit receipts instead of one",
                set.function,
                receipts.len()
            ),
        });
    };
    if receipt.outcome != TableMutationOutcome::Inserted || receipt.previous.is_some() {
        return Err(CausalSliceError::Unsupported {
            location: set.span.to_string(),
            reason: format!(
                "a source set of `{}` that invokes or collides with its merge; v0 admits only a fresh insertion",
                set.function
            ),
        });
    }
    let location = format!("source function set command {}", fact.command_index);
    let (committed_key, committed_output) = logical_function_row(
        receipt.table,
        &receipt.committed,
        trace_functions,
        &location,
    )?;
    if committed_key.function != set.function || receipt.incoming != receipt.committed {
        return Err(CausalSliceError::Invariant(format!(
            "{location} committed a row different from its fresh source proposal"
        )));
    }
    let mut cursor = 0usize;
    let keys = set
        .keys
        .iter()
        .zip(&set.input_sorts)
        .map(|(key, sort)| {
            elaborate_source_scalar_arg(egraph, key, sort, &applications, &mut cursor, witnesses)
                .map(|(endpoint, _)| endpoint)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let (value, _) = elaborate_source_scalar_arg(
        egraph,
        &set.value,
        &set.output_sort,
        &applications,
        &mut cursor,
        witnesses,
    )?;
    if cursor != applications.len() {
        return Err(CausalSliceError::Unsupported {
            location: set.span.to_string(),
            reason: format!(
                "a source set of `{}` with additional primitive or merge-callback effects",
                set.function
            ),
        });
    }
    let expected_key = FunctionRowKey {
        function: set.function.clone(),
        keys,
    };
    if expected_key != committed_key || value != committed_output {
        return Err(CausalSliceError::Invariant(format!(
            "{location} runtime row diverged from its source syntax"
        )));
    }
    Ok((committed_key, committed_output))
}

fn snapshot_primitive_result_witnesses(
    batch: &RuleExecutionTrace,
    witnesses: &WitnessArena,
) -> IndexMap<TypedEndpoint, WitnessId> {
    batch
        .primitives
        .iter()
        .filter_map(|application| {
            witnesses
                .by_endpoint("BigRat", application.result)
                .map(|witness| {
                    (
                        TypedEndpoint {
                            sort: "BigRat".to_owned(),
                            value: application.result,
                        },
                        witness,
                    )
                })
        })
        .collect()
}

fn elaborate_prefix_replay(
    input: PrefixElaborationInput<'_>,
    witnesses: &mut WitnessArena,
) -> Result<PrefixElaboration, CausalSliceError> {
    let PrefixElaborationInput {
        egraph,
        rules,
        rule_primitives,
        relations,
        source_facts,
        source_traces,
        batches,
        trace_functions,
    } = input;
    let mut source_rows = IndexSet::default();
    for fact in source_facts {
        source_rows.extend(elaborate_source_fact(
            egraph,
            fact,
            source_traces,
            trace_functions,
            relations,
            witnesses,
            true,
        )?);
    }

    let mut replay_fires = Vec::new();
    let mut pending_firings = 0usize;
    let mut captured_bindings = 0usize;
    let mut effective_applications = 0usize;
    let mut effective_output_rows = 0usize;
    let mut equality_edges = 0usize;

    for (wave, batch) in batches.into_iter().enumerate() {
        witnesses.load_current_globals(&batch.globals)?;
        if !batch.mutations.is_empty() {
            return Err(CausalSliceError::Unsupported {
                location: format!("traced Prefix wave {wave}"),
                reason: "mutable-state commit receipts in conservative Prefix replay".to_owned(),
            });
        }
        let prestate_witness_snapshot = witnesses.snapshot();
        let prestate_witnesses = snapshot_primitive_result_witnesses(&batch, witnesses);
        let applications_by_origin = OriginIndex::build(
            batch.matches.len(),
            &batch.applications,
            |application| Some(application.origin.index()),
            "application",
        )?;
        let primitives_by_origin = OriginIndex::build(
            batch.matches.len(),
            &batch.primitives,
            |application| Some(application.origin.index()),
            "primitive",
        )?;
        let unions_by_origin = OriginIndex::build(
            batch.matches.len(),
            &batch.unions,
            |receipt| receipt.origin.map(|origin| origin.index()),
            "union",
        )?;

        for (ordinal, captured) in batch.matches.iter().enumerate() {
            pending_firings += 1;
            let rule_name = captured.rule.as_ref();
            let model = rules.get(rule_name).ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "native trace referenced unmodeled rule `{rule_name}`"
                ))
            })?;
            if let Some(policy) = &model.opaque {
                match policy {
                    OpaqueRulePolicy::Reject(error)
                    | OpaqueRulePolicy::ProjectedGrounding(error)
                    | OpaqueRulePolicy::UnreplayableGrounding(error) => {
                        return Err(error.clone().into_error());
                    }
                    OpaqueRulePolicy::UnreachedPanicHead => {
                        if !applications_by_origin.for_origin(ordinal).is_empty()
                            || !unions_by_origin.for_origin(ordinal).is_empty()
                        {
                            return Err(CausalSliceError::Invariant(format!(
                                "single-panic rule `{rule_name}` reported a successful head effect"
                            )));
                        }
                        continue;
                    }
                    OpaqueRulePolicy::EmptyBodyInitializer => {
                        let application_indices = applications_by_origin.for_origin(ordinal);
                        if !primitives_by_origin.for_origin(ordinal).is_empty()
                            || !unions_by_origin.for_origin(ordinal).is_empty()
                            || application_indices.iter().any(|index| {
                                !trace_functions
                                    .contains_key(&batch.applications[*index as usize].table)
                            })
                        {
                            return Err(CausalSliceError::Invariant(format!(
                                "validated empty-body initializer `{rule_name}` executed an opaque table, primitive, or union effect"
                            )));
                        }
                        let effects = elaborate_fire_applications(
                            egraph,
                            application_indices
                                .iter()
                                .map(|index| &batch.applications[*index as usize]),
                            trace_functions,
                            witnesses,
                            true,
                            None,
                        )?;
                        effective_output_rows += effects.new_rows.len();
                        if effects.new_rows.is_empty() && effects.new_witnesses.is_empty() {
                            continue;
                        }
                        let rule_index = rules.get_index_of(rule_name).ok_or_else(|| {
                            CausalSliceError::Invariant(format!(
                                "native trace referenced unindexed rule `{rule_name}`"
                            ))
                        })?;
                        replay_fires.push(CompactReplayFire {
                            rule_index: u32::try_from(rule_index).map_err(|_| {
                                CausalSliceError::Invariant(
                                    "rule index exceeded u32 capacity".to_owned(),
                                )
                            })?,
                            wave: u32::try_from(wave).map_err(|_| {
                                CausalSliceError::Invariant(
                                    "wave index exceeded u32 capacity".to_owned(),
                                )
                            })?,
                            ordinal: u32::try_from(ordinal).map_err(|_| {
                                CausalSliceError::Invariant(
                                    "wave ordinal exceeded u32 capacity".to_owned(),
                                )
                            })?,
                            bindings: Box::new([]),
                            selector_variables: None,
                        });
                        effective_applications += 1;
                        continue;
                    }
                }
            }
            // Capture bindings before the head applications below extend the
            // witness arena. Every emitted expression was therefore available
            // at the original match boundary.
            let mut bindings = reconstruct_rule_bindings(
                egraph,
                rule_name,
                &captured.bindings,
                model,
                witnesses,
                Some(&prestate_witness_snapshot),
            )
            .map_err(BindingReconstructionError::into_error)?;

            let primitive_indices = primitives_by_origin.for_origin(ordinal);
            let primitive_result = elaborate_fire_primitive_sequence(
                FirePrimitiveSequenceInput {
                    egraph,
                    rule_name,
                    model,
                    metadata: rule_primitives.get(rule_name).ok_or_else(|| {
                        CausalSliceError::Invariant(format!(
                            "rule `{rule_name}` has no resolved primitive metadata"
                        ))
                    })?,
                    applications: primitive_indices
                        .iter()
                        .map(|index| &batch.primitives[*index as usize])
                        .collect(),
                    bindings: &mut bindings,
                    prestate_witnesses: &prestate_witnesses,
                },
                witnesses,
            )?;
            let Some((_, primitive_error)) = primitive_result else {
                if !applications_by_origin.for_origin(ordinal).is_empty()
                    || !unions_by_origin.for_origin(ordinal).is_empty()
                {
                    return Err(CausalSliceError::Invariant(format!(
                        "query-filtered rule `{rule_name}` still produced head effects"
                    )));
                }
                continue;
            };
            if let Some(error) = primitive_error {
                return Err(error.into_error());
            }
            captured_bindings += bindings.len();

            let application_indices = applications_by_origin.for_origin(ordinal);
            let effects = elaborate_fire_applications(
                egraph,
                application_indices
                    .iter()
                    .map(|index| &batch.applications[*index as usize]),
                trace_functions,
                witnesses,
                true,
                None,
            )?;
            for constructor in model.head_constructors.iter().chain(&model.head_subsumes) {
                let AtomArg::App { output_sort, .. } = constructor else {
                    return Err(CausalSliceError::Invariant(
                        "modeled constructor action lost its application node".to_owned(),
                    ));
                };
                ground_arg(egraph, constructor, output_sort, &bindings, witnesses)?;
            }
            let expected_head = ground_atoms(egraph, &model.head, &bindings, witnesses, relations)?;
            if !same_row_multiset(&expected_head, &effects.observed_rows) {
                return Err(CausalSliceError::Invariant(format!(
                    "native applications for rule `{rule_name}` do not match its complete source head"
                )));
            }

            let union_indices = unions_by_origin.for_origin(ordinal);
            let applied_unions = count_prefix_applied_unions(
                rule_name,
                &model.head_unions,
                union_indices
                    .iter()
                    .map(|index| &batch.unions[*index as usize]),
            )?;
            effective_output_rows += effects.new_rows.len();
            equality_edges += applied_unions;
            if effects.new_rows.is_empty()
                && effects.new_witnesses.is_empty()
                && applied_unions == 0
            {
                continue;
            }

            let rule_index = rules.get_index_of(rule_name).ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "native trace referenced unindexed rule `{rule_name}`"
                ))
            })?;
            let replay_bindings = model
                .replay_var_order
                .iter()
                .map(|variable| {
                    let binding = bindings.get(variable).ok_or_else(|| {
                        CausalSliceError::Invariant(format!(
                            "captured rule `{rule_name}` omitted replay variable `{variable}`"
                        ))
                    })?;
                    Ok(binding.syntax)
                })
                .collect::<Result<Vec<_>, CausalSliceError>>()?;
            replay_fires.push(CompactReplayFire {
                rule_index: u32::try_from(rule_index).map_err(|_| {
                    CausalSliceError::Invariant("rule index exceeded u32 capacity".to_owned())
                })?,
                wave: u32::try_from(wave).map_err(|_| {
                    CausalSliceError::Invariant("wave index exceeded u32 capacity".to_owned())
                })?,
                ordinal: u32::try_from(ordinal).map_err(|_| {
                    CausalSliceError::Invariant("wave ordinal exceeded u32 capacity".to_owned())
                })?,
                bindings: replay_bindings.into_boxed_slice(),
                selector_variables: None,
            });
            effective_applications += 1;
        }
    }

    Ok(PrefixElaboration {
        replay_fires,
        pending_firings,
        captured_bindings,
        effective_applications,
        effective_output_rows,
        source_events: source_rows.len(),
        witness_nodes: witnesses.nodes.len(),
        equality_edges,
    })
}

fn type_unoriginated_equality(
    egraph: &EGraph,
    witnesses: &WitnessArena,
    ordered_receipt: OrderedUnionReceipt<'_>,
    wave: usize,
) -> Result<AppliedEquality, DeferredUnsupported> {
    let receipt = ordered_receipt.receipt;
    let UnionOutcome::Applied { parent, child } = receipt.outcome else {
        return Err(DeferredUnsupported {
            location: format!("traced wave {wave}"),
            reason: "a redundant unoriginated union reached successful-union typing".to_owned(),
        });
    };
    let rhs_sorts = witnesses.endpoint_sorts.get(&receipt.rhs);
    let mut sorts = witnesses
        .endpoint_sorts
        .get(&receipt.lhs)
        .into_iter()
        .flatten()
        .filter(|sort| {
            rhs_sorts
                .is_some_and(|candidates| candidates.iter().any(|candidate| candidate == *sort))
        })
        .filter(|&sort| {
            egraph
                .get_sort_by_name(sort)
                .is_some_and(|runtime_sort| runtime_sort.is_eq_sort())
        })
        .cloned()
        .collect::<Vec<_>>();
    sorts.sort();
    sorts.dedup();
    let [sort] = sorts.as_slice() else {
        return Err(DeferredUnsupported {
            location: format!("traced wave {wave}"),
            reason: format!(
                "a congruence, merge, or rebuild union without an originating rule match had {} candidate equality sorts at its commit boundary",
                sorts.len()
            ),
        });
    };
    Ok(AppliedEquality {
        left: TypedEndpoint {
            sort: sort.clone(),
            value: receipt.lhs,
        },
        right: TypedEndpoint {
            sort: sort.clone(),
            value: receipt.rhs,
        },
        parent,
        child,
        commit_ordinal: ordered_receipt.commit_ordinal,
    })
}

fn source_witness_prerequisites<'a>(
    witnesses: &WitnessArena,
    witness_start: usize,
    endpoints: impl IntoIterator<Item = &'a TypedEndpoint>,
    dependencies: &mut DepArena,
) -> Result<DepId, CausalSliceError> {
    let mut prerequisites = IndexSet::default();
    for endpoint in endpoints {
        if let Some(witness) = witnesses.by_endpoint(&endpoint.sort, endpoint.value)
            && witness.index() < witness_start
        {
            prerequisites.insert(witnesses.availability(witness));
        }
    }
    for record in &witnesses.nodes[witness_start..] {
        if let WitnessNode::App { children, .. } = &record.node {
            for child in children {
                if child.index() < witness_start {
                    prerequisites.insert(witnesses.availability(*child));
                }
            }
        }
    }
    let mut result = DepArena::EMPTY;
    for prerequisite in prerequisites {
        result = dependencies.and(result, prerequisite)?;
    }
    Ok(result)
}

fn mark_new_source_witnesses(
    witnesses: &mut WitnessArena,
    witness_start: usize,
    dependency: DepId,
) {
    for index in witness_start..witnesses.nodes.len() {
        if matches!(witnesses.nodes[index].node, WitnessNode::App { .. }) {
            witnesses.set_availability(WitnessId(index as u32), dependency);
        }
    }
}

fn supports_pre_wave_prefix_fallback(reason: &str) -> bool {
    reason == "syntax that was unavailable at the captured firing"
        || (reason.starts_with("an equality-canonicalized premise of rule `")
            && reason.ends_with("without commit-time relation-row rekey provenance"))
}

fn supports_pre_wave_constructor_hit_fallback(error: &DeferredUnsupported) -> bool {
    matches!(
        error.reason.as_str(),
        "a table hit without a previously captured constructor witness"
            | "a congruence-created table hit without exact constructor-row provenance"
    )
}

fn binding_is_replay_selector_stable(
    egraph: &EGraph,
    sort_name: &str,
    binding: BindingWitness,
    witnesses: &WitnessArena,
    prestate_witness_count: usize,
    current_binding_witnesses: &HashSet<WitnessId>,
) -> Result<bool, CausalSliceError> {
    let sort = egraph.get_sort_by_name(sort_name).ok_or_else(|| {
        CausalSliceError::Invariant(format!(
            "replay-key planning lost runtime sort `{sort_name}`"
        ))
    })?;
    if !sort.is_eq_sort() && !sort.is_container_sort() {
        return Ok(true);
    }

    // Point evaluation is sound only when this syntax had one raw denotation
    // at the match boundary. Include the pre-wave arena plus witnesses copied
    // from this shared-prestate match set; exclude witnesses first produced by
    // current-wave heads. Hardboiled's `(Int 32 1)` has both 51 and 271 here
    // and is therefore omitted from its packed selector.
    let syntax = witnesses.nodes[binding.syntax.index()].syntax;
    let mut endpoints = HashSet::default();
    for witness in witnesses
        .syntax_instances
        .get(&syntax)
        .map(Vec::as_slice)
        .unwrap_or_default()
    {
        if witness.index() >= prestate_witness_count && !current_binding_witnesses.contains(witness)
        {
            continue;
        }
        if let Some(endpoint) = witnesses.endpoint(*witness) {
            endpoints.insert(endpoint);
        }
    }
    Ok(endpoints.len() == 1 && endpoints.contains(&binding.endpoint))
}

fn replay_grounding_key(
    variables: &[String],
    index: usize,
    pending_fires: &[PendingFire],
    model: &RuleModel,
    egraph: &EGraph,
    equality_forest: &EqualityForest,
) -> Result<Box<[Value]>, CausalSliceError> {
    let fire = &pending_fires[index].grounding;
    let mut key = Vec::with_capacity(variables.len());
    for variable in variables {
        let binding = fire.bindings.get(variable).ok_or_else(|| {
            CausalSliceError::Invariant(format!(
                "grounded firing of `{}` omitted replay-key variable `{variable}`",
                fire.rule
            ))
        })?;
        let sort_name = model.var_sorts.get(variable).ok_or_else(|| {
            CausalSliceError::Invariant(format!(
                "rule `{}` omitted the type of replay-key variable `{variable}`",
                fire.rule
            ))
        })?;
        let sort = egraph.get_sort_by_name(sort_name).ok_or_else(|| {
            CausalSliceError::Invariant(format!(
                "replay-key planning lost runtime sort `{sort_name}`"
            ))
        })?;
        key.push(if sort.is_eq_sort() {
            equality_forest.typed_canonical_value(sort_name, binding.endpoint)
        } else {
            binding.endpoint
        });
    }
    Ok(key.into_boxed_slice())
}

fn replay_selector_identifies_targets(
    variables: &[String],
    target_indices: &[usize],
    candidate_indices: &[usize],
    pending_fires: &[PendingFire],
    model: &RuleModel,
    egraph: &EGraph,
    equality_forest: &EqualityForest,
) -> Result<bool, CausalSliceError> {
    let mut projected_groundings = HashMap::<Box<[Value]>, HashSet<Box<[Value]>>>::default();
    for index in candidate_indices {
        let projected = replay_grounding_key(
            variables,
            *index,
            pending_fires,
            model,
            egraph,
            equality_forest,
        )?;
        let complete = replay_grounding_key(
            &model.replay_var_order,
            *index,
            pending_fires,
            model,
            egraph,
            equality_forest,
        )?;
        projected_groundings
            .entry(projected)
            .or_default()
            .insert(complete);
    }
    let mut target_keys = HashSet::default();
    for index in target_indices {
        let key = replay_grounding_key(
            variables,
            *index,
            pending_fires,
            model,
            egraph,
            equality_forest,
        )?;
        if !target_keys.insert(key.clone())
            || projected_groundings.get(&key).map(HashSet::len) != Some(1)
        {
            return Ok(false);
        }
    }
    Ok(true)
}

struct ReplaySelectorPlanningInput<'a> {
    egraph: &'a EGraph,
    rules: &'a IndexMap<String, RuleModel>,
    witnesses: &'a WitnessArena,
    prestate_witness_count: usize,
    equality_forest: &'a EqualityForest,
    wave: usize,
    pending_fires: &'a mut [PendingFire],
    current_start: usize,
    events: &'a mut [ReplayEvent],
}

fn assign_wave_replay_selectors(
    input: ReplaySelectorPlanningInput<'_>,
) -> Result<(), CausalSliceError> {
    let ReplaySelectorPlanningInput {
        egraph,
        rules,
        witnesses,
        prestate_witness_count,
        equality_forest,
        wave,
        pending_fires,
        current_start,
        events,
    } = input;
    let current_binding_witnesses = pending_fires[current_start..]
        .iter()
        .flat_map(|pending| pending.grounding.bindings.values())
        .map(|binding| binding.syntax)
        .collect::<HashSet<_>>();
    let mut groups = IndexMap::<String, Vec<usize>>::default();
    for (index, pending) in pending_fires.iter().enumerate().skip(current_start) {
        groups
            .entry(pending.grounding.rule.clone())
            .or_default()
            .push(index);
    }

    let mut plans = IndexMap::<String, ReplaySelector>::default();
    for (rule_name, target_indices) in groups {
        let model = rules.get(&rule_name).ok_or_else(|| {
            CausalSliceError::Invariant(format!(
                "replay-key planning referenced unknown rule `{rule_name}`"
            ))
        })?;
        // Packed replay freshly queries the complete current database. In the
        // supported monotone fragment, successful matches from earlier waves
        // remain candidates even though seminaive execution need not report
        // them again. Plan this wave's key against that cumulative prefix.
        let candidate_indices = pending_fires
            .iter()
            .enumerate()
            .filter_map(|(index, pending)| (pending.grounding.rule == rule_name).then_some(index))
            .collect::<Vec<_>>();
        let mut stable_variables = Vec::new();
        for variable in &model.replay_var_order {
            let sort_name = model.var_sorts.get(variable).ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "rule `{rule_name}` omitted the type of replay variable `{variable}`"
                ))
            })?;
            let stable = target_indices.iter().try_fold(true, |stable, index| {
                let binding = pending_fires[*index]
                    .grounding
                    .bindings
                    .get(variable)
                    .copied()
                    .ok_or_else(|| {
                        CausalSliceError::Invariant(format!(
                            "grounded firing of `{rule_name}` omitted replay variable `{variable}`"
                        ))
                    })?;
                Ok::<_, CausalSliceError>(
                    stable
                        && binding_is_replay_selector_stable(
                            egraph,
                            sort_name,
                            binding,
                            witnesses,
                            prestate_witness_count,
                            &current_binding_witnesses,
                        )?,
                )
            })?;
            if stable {
                stable_variables.push(variable.clone());
            }
        }
        let plan = if replay_selector_identifies_targets(
            &stable_variables,
            &target_indices,
            &candidate_indices,
            pending_fires,
            model,
            egraph,
            equality_forest,
        )? {
            // Keep the maximal stable key. If it is not unique, no subset can
            // become unique; minimizing it would only churn source and tests
            // without improving the soundness boundary.
            ReplaySelector::Key(Arc::from(stable_variables))
        } else {
            ReplaySelector::Unsupported(Arc::new(DeferredUnsupported {
                location: model.span.to_string(),
                reason: format!(
                    "{} successful groundings of rule `{rule_name}` in traced wave {wave} cannot be uniquely identified by replay-stable source bindings {stable_variables:?}; packed logical selectors or a stable match-time endpoint handle are required",
                    target_indices.len(),
                ),
            }))
        };

        for index in target_indices {
            pending_fires[index].grounding.selector = plan.clone();
        }
        plans.insert(rule_name, plan);
    }

    for event in events {
        let EventKind::Fire(fire) = &mut event.kind else {
            continue;
        };
        let plan = plans.get(&fire.rule).ok_or_else(|| {
            CausalSliceError::Invariant(format!(
                "promoted firing of `{}` in wave {wave} had no pending replay-key group",
                fire.rule
            ))
        })?;
        fire.selector = plan.clone();
    }
    Ok(())
}

fn elaborate_events(
    input: ElaborationInput<'_>,
    witnesses: &mut WitnessArena,
) -> Result<Elaboration, CausalSliceError> {
    let ElaborationInput {
        egraph,
        rules,
        rule_primitives,
        relations,
        source_facts,
        source_traces,
        batches,
        trace_functions,
        prefix_fallback,
    } = input;
    let mut dependencies = DepArena::default();
    let mut events = EventArena::default();
    let mut producers = IndexMap::default();
    let mut function_rows = IndexMap::default();
    let mut equality_forest = EqualityForest::default();
    let mut opaque_equality_error = None;
    let mut source_events = 0;
    for fact in source_facts {
        let witness_start = witnesses.nodes.len();
        if matches!(fact.kind, SourceFactKind::FunctionSet(..)) {
            let (row, output) = elaborate_source_function_set(
                egraph,
                fact,
                source_traces,
                trace_functions,
                witnesses,
            )?;
            if function_rows.contains_key(&row) {
                return Err(CausalSliceError::Unsupported {
                    location: format!("source function set command {}", fact.command_index),
                    reason: "two source mutable insertions of the same logical key".to_owned(),
                });
            }
            let prerequisites = source_witness_prerequisites(
                witnesses,
                witness_start,
                row.keys.iter().chain(std::iter::once(&output)),
                &mut dependencies,
            )?;
            let event = events.push(ReplayEvent {
                kind: EventKind::Source { fact: fact.id },
                prerequisites,
                deferred_prerequisite_error: None,
                effective_outputs: Vec::new(),
            })?;
            let dependency = dependencies.event(event)?;
            mark_new_source_witnesses(witnesses, witness_start, dependency);
            function_rows.insert(
                row,
                FunctionRowState {
                    output,
                    dependency,
                    deferred_error: None,
                },
            );
            source_events += 1;
            continue;
        }
        let rows = elaborate_source_fact(
            egraph,
            fact,
            source_traces,
            trace_functions,
            relations,
            witnesses,
            prefix_fallback,
        )?;
        let rows = rows
            .into_iter()
            .filter(|row| !producers.contains_key(row))
            .collect::<Vec<_>>();
        let created_replay_witness = witnesses.nodes[witness_start..]
            .iter()
            .any(|record| matches!(record.node, WitnessNode::App { .. }));
        if rows.is_empty() && !created_replay_witness {
            continue;
        }
        let prerequisites = source_witness_prerequisites(
            witnesses,
            witness_start,
            rows.iter().flat_map(|row| row.args.iter()),
            &mut dependencies,
        )?;
        let event = events.push(ReplayEvent {
            kind: EventKind::Source { fact: fact.id },
            prerequisites,
            deferred_prerequisite_error: None,
            effective_outputs: rows.clone(),
        })?;
        let dependency = dependencies.event(event)?;
        mark_new_source_witnesses(witnesses, witness_start, dependency);
        for row in rows {
            producers.insert(row, dependency);
        }
        source_events += 1;
    }

    let mut pending_fires = Vec::new();
    let mut opaque_pending_firings = 0usize;
    let mut opaque_promoted_events = 0usize;
    let mut causal_prefix_fallbacks = 0usize;
    for (wave, batch) in batches.iter().enumerate() {
        // Native matches in this batch were all selected from the shared
        // pre-wave database. A conservative premise fallback must therefore
        // stop here, before any event from this wave is added.
        let pre_wave_last_event = events
            .events
            .len()
            .checked_sub(1)
            .map(|index| EventId(index as u32));
        let wave_event_start = events.events.len();
        let wave_pending_start = pending_fires.len();
        for application in &batch.applications {
            let rule = batch
                .matches
                .get(application.origin.index())
                .map(|matched| matched.rule.as_ref())
                .unwrap_or("<invalid-origin>");
            let function = trace_functions
                .get(&application.table)
                .map(|meta| meta.name.as_str())
                .unwrap_or("<unmodeled-table>");
            log::trace!(
                "causal raw table receipt wave={wave} origin={} rule={rule} instruction={} function={function} table={:?} args={:?} result={:?}",
                application.origin.index(),
                application.instruction,
                application.table,
                application.args,
                application.result
            );
        }
        for application in &batch.primitives {
            log::trace!(
                "causal raw primitive receipt wave={wave} origin={} instruction={} function={:?} args={:?} result={:?}",
                application.origin.index(),
                application.instruction,
                application.function,
                application.args,
                application.result
            );
        }
        let mut wave_app_index = WaveAppIndex::default();
        witnesses.load_current_globals(&batch.globals)?;
        let prestate_witness_snapshot = witnesses.snapshot();
        let prestate_witnesses = snapshot_primitive_result_witnesses(batch, witnesses);
        let mut applications_by_origin = vec![Vec::new(); batch.matches.len()];
        for application in &batch.applications {
            let origin = application.origin.index();
            let Some(applications) = applications_by_origin.get_mut(origin) else {
                return Err(CausalSliceError::Invariant(format!(
                    "application origin {origin} exceeded {} matches",
                    batch.matches.len()
                )));
            };
            applications.push(application);
        }
        let primitives_by_origin = OriginIndex::build(
            batch.matches.len(),
            &batch.primitives,
            |application| Some(application.origin.index()),
            "primitive",
        )?;
        let mutations_by_origin = OriginIndex::build(
            batch.matches.len(),
            &batch.mutations,
            |receipt| match &receipt.cause {
                TableMutationCause::Rule { origin, .. } => Some(origin.index()),
                TableMutationCause::Rebuild { .. } | TableMutationCause::Unattributed => None,
            },
            "mutable mutation",
        )?;
        let mut unions_by_origin = vec![Vec::new(); batch.matches.len()];
        let mut unoriginated_unions = Vec::new();
        for (commit_ordinal, receipt) in batch.unions.iter().enumerate() {
            let ordered_receipt = OrderedUnionReceipt {
                commit_ordinal,
                receipt,
            };
            let Some(origin) = receipt.origin else {
                if !prefix_fallback && matches!(receipt.outcome, UnionOutcome::Applied { .. }) {
                    unoriginated_unions.push(ordered_receipt);
                }
                continue;
            };
            let Some(unions) = unions_by_origin.get_mut(origin.index()) else {
                return Err(CausalSliceError::Invariant(format!(
                    "union origin {} exceeded {} matches",
                    origin.index(),
                    batch.matches.len()
                )));
            };
            unions.push(ordered_receipt);
        }
        let force_wave_prefix = !unoriginated_unions.is_empty();

        let mut new_outputs = IndexMap::<RowKey, DepId>::default();
        let mut new_equality_edges = Vec::new();
        let mut origin_event_dependencies = vec![None; batch.matches.len()];
        for (ordinal, captured) in batch.matches.iter().enumerate() {
            let rule_name = captured.rule.as_ref();
            let model = rules.get(rule_name).ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "native trace referenced unmodeled rule `{rule_name}`"
                ))
            })?;
            let mut reconstructed_bindings = None;
            let dynamic_policy;
            let policy = if let Some(policy) = model.opaque.as_ref() {
                Some(policy)
            } else {
                match reconstruct_rule_bindings(
                    egraph,
                    rule_name,
                    &captured.bindings,
                    model,
                    witnesses,
                    Some(&prestate_witness_snapshot),
                ) {
                    Ok(bindings) => {
                        reconstructed_bindings = Some(bindings);
                        None
                    }
                    Err(BindingReconstructionError::Projected(error)) => {
                        dynamic_policy = OpaqueRulePolicy::ProjectedGrounding(error);
                        Some(&dynamic_policy)
                    }
                    Err(BindingReconstructionError::Other(CausalSliceError::Unsupported {
                        location,
                        reason,
                    })) => {
                        dynamic_policy =
                            OpaqueRulePolicy::UnreplayableGrounding(DeferredUnsupported {
                                location,
                                reason,
                            });
                        Some(&dynamic_policy)
                    }
                    Err(BindingReconstructionError::Other(error)) => return Err(error),
                }
            };
            if let Some(policy) = policy {
                log::debug!("causal elaboration deferred firing of rule `{rule_name}`: {policy:?}");
                let mutation_indices = mutations_by_origin.for_origin(ordinal);
                if matches!(policy, OpaqueRulePolicy::UnreachedPanicHead) {
                    if !applications_by_origin[ordinal].is_empty()
                        || !unions_by_origin[ordinal].is_empty()
                        || !mutation_indices.is_empty()
                    {
                        return Err(CausalSliceError::Invariant(format!(
                            "single-panic rule `{rule_name}` reported a successful head effect"
                        )));
                    }
                    continue;
                }
                let effective_mutation = mutation_indices.iter().any(|index| {
                    matches!(
                        batch.mutations[*index as usize].outcome,
                        TableMutationOutcome::Inserted | TableMutationOutcome::Replaced
                    )
                });
                let known_applications = applications_by_origin[ordinal]
                    .iter()
                    .copied()
                    .filter(|application| trace_functions.contains_key(&application.table))
                    .collect::<Vec<_>>();
                let deferred_grounding = matches!(
                    policy,
                    OpaqueRulePolicy::ProjectedGrounding(_)
                        | OpaqueRulePolicy::UnreplayableGrounding(_)
                );
                if matches!(policy, OpaqueRulePolicy::EmptyBodyInitializer)
                    && (known_applications.len() != applications_by_origin[ordinal].len()
                        || !primitives_by_origin.for_origin(ordinal).is_empty()
                        || !unions_by_origin[ordinal].is_empty()
                        || !mutation_indices.is_empty())
                {
                    return Err(CausalSliceError::Invariant(format!(
                        "validated empty-body initializer `{rule_name}` executed an opaque table, primitive, or union effect"
                    )));
                }
                // Rule primitive metadata was already restricted to Pure,
                // proof-validating, replay-safe specializations. If an
                // unreplayable grounding used one, the traced table/union
                // receipts below still determine whether it had a persistent
                // effect. Let complete no-ops be discarded there rather than
                // rejecting them solely because their primitive syntax cannot
                // be reconstructed.
                if deferred_grounding
                    && (known_applications.len() != applications_by_origin[ordinal].len()
                        || !model.head_subsumes.is_empty())
                {
                    let detail = match policy {
                        OpaqueRulePolicy::ProjectedGrounding(error)
                        | OpaqueRulePolicy::UnreplayableGrounding(error) => {
                            format!(" at {}: {}", error.location, error.reason)
                        }
                        _ => String::new(),
                    };
                    return Err(CausalSliceError::Invariant(format!(
                        "unreplayable grounding of modeled rule `{rule_name}` executed an untracked table or subsume effect{detail}"
                    )));
                }
                let effects = match elaborate_fire_applications(
                    egraph,
                    known_applications.iter().copied(),
                    trace_functions,
                    witnesses,
                    prefix_fallback,
                    Some(CausalApplicationInput {
                        equality_forest: &equality_forest,
                        dependencies: &mut dependencies,
                        app_index: &mut wave_app_index,
                    }),
                ) {
                    Ok(effects) => effects,
                    Err(CausalSliceError::Unsupported { .. })
                        if matches!(
                            policy,
                            OpaqueRulePolicy::Reject(_)
                                | OpaqueRulePolicy::ProjectedGrounding(_)
                                | OpaqueRulePolicy::UnreplayableGrounding(_)
                        ) =>
                    {
                        let relation_applications =
                            known_applications.iter().copied().filter(|application| {
                                trace_functions
                                    .get(&application.table)
                                    .is_some_and(|meta| meta.kind == TraceFunctionKind::Relation)
                            });
                        elaborate_fire_applications(
                            egraph,
                            relation_applications,
                            trace_functions,
                            witnesses,
                            prefix_fallback,
                            Some(CausalApplicationInput {
                                equality_forest: &equality_forest,
                                dependencies: &mut dependencies,
                                app_index: &mut wave_app_index,
                            }),
                        )?
                    }
                    Err(error) => return Err(error),
                };
                if matches!(policy, OpaqueRulePolicy::EmptyBodyInitializer)
                    && let Some(error) = effects.deferred_error.as_ref()
                {
                    return Err(CausalSliceError::Unsupported {
                        location: model.span.to_string(),
                        reason: format!(
                            "{} in validated empty-body initializer `{rule_name}`",
                            error.reason
                        ),
                    });
                }
                let effective_outputs = effects
                    .new_rows
                    .into_iter()
                    .filter(|row| !producers.contains_key(row) && !new_outputs.contains_key(row))
                    .collect::<Vec<_>>();
                // A native match is captured before action-lane query filters
                // finish. Reached union instructions always produce a receipt,
                // including redundant unions, so a deferred grounding with no
                // table, union, or mutation receipt never executed its stateful
                // head and has no equality edge to classify.
                let head_was_filtered = applications_by_origin[ordinal].is_empty()
                    && unions_by_origin[ordinal].is_empty()
                    && mutation_indices.is_empty();
                let deferred_grounding_equality_edges = if deferred_grounding {
                    if head_was_filtered {
                        Vec::new()
                    } else {
                        classify_prefix_union_receipts(
                            rule_name,
                            &model.head_unions,
                            &unions_by_origin[ordinal],
                        )?
                    }
                } else {
                    Vec::new()
                };
                let applied_union = if deferred_grounding {
                    !deferred_grounding_equality_edges.is_empty()
                } else {
                    unions_by_origin[ordinal].iter().any(|receipt| {
                        matches!(receipt.receipt.outcome, UnionOutcome::Applied { .. })
                    })
                };
                let has_effect = !effective_outputs.is_empty()
                    || !effects.new_witnesses.is_empty()
                    || applied_union
                    || effective_mutation;
                let mut effect_prerequisites = DepArena::EMPTY;
                for dependency in effects.read_dependencies.iter().copied() {
                    effect_prerequisites = dependencies.and(effect_prerequisites, dependency)?;
                }

                match policy {
                    OpaqueRulePolicy::EmptyBodyInitializer => {
                        let grounding = GroundedFire {
                            rule: rule_name.to_owned(),
                            wave: u32::try_from(wave).map_err(|_| {
                                CausalSliceError::Invariant(
                                    "wave index exceeded u32 capacity".to_owned(),
                                )
                            })?,
                            ordinal: u32::try_from(ordinal).map_err(|_| {
                                CausalSliceError::Invariant(
                                    "wave ordinal exceeded u32 capacity".to_owned(),
                                )
                            })?,
                            bindings: IndexMap::default(),
                            selector: ReplaySelector::Unplanned,
                        };
                        let _promoted = if has_effect || force_wave_prefix {
                            let event = events.push(ReplayEvent {
                                kind: EventKind::Fire(grounding.clone()),
                                prerequisites: effect_prerequisites,
                                deferred_prerequisite_error: None,
                                effective_outputs: effective_outputs.clone(),
                            })?;
                            let dependency = dependencies.event(event)?;
                            origin_event_dependencies[ordinal] = Some(dependency);
                            for row in effective_outputs {
                                new_outputs.insert(row, dependency);
                            }
                            for witness in effects.new_witnesses {
                                witnesses.set_availability(witness, dependency);
                            }
                            Some(event)
                        } else {
                            None
                        };
                        pending_fires.push(PendingFire {
                            grounding,
                            effective: has_effect,
                        });
                    }
                    OpaqueRulePolicy::UnreachedPanicHead => {
                        unreachable!("single-panic candidates were discarded above")
                    }
                    OpaqueRulePolicy::Reject(error)
                    | OpaqueRulePolicy::ProjectedGrounding(error)
                    | OpaqueRulePolicy::UnreplayableGrounding(error) => {
                        opaque_pending_firings += 1;
                        if applied_union && opaque_equality_error.is_none() {
                            opaque_equality_error = Some(error.clone());
                        }
                        if has_effect || force_wave_prefix {
                            let event = events.push(ReplayEvent {
                                kind: EventKind::OpaqueFire,
                                prerequisites: effect_prerequisites,
                                deferred_prerequisite_error: Some(error.clone()),
                                effective_outputs: effective_outputs.clone(),
                            })?;
                            let dependency = dependencies.event(event)?;
                            origin_event_dependencies[ordinal] = Some(dependency);
                            for row in effective_outputs {
                                new_outputs.insert(row, dependency);
                            }
                            for witness in effects.new_witnesses {
                                witnesses.set_availability(witness, dependency);
                            }
                            for equality in deferred_grounding_equality_edges {
                                new_equality_edges.push((equality, dependency));
                            }
                            opaque_promoted_events += usize::from(has_effect);
                        }
                    }
                }
                continue;
            }
            let mut bindings = reconstructed_bindings.ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "traceable rule `{rule_name}` lost its reconstructed bindings"
                ))
            })?;
            let primitive_indices = primitives_by_origin.for_origin(ordinal);
            let primitive_applications = primitive_indices
                .iter()
                .map(|index| &batch.primitives[*index as usize])
                .collect::<Vec<_>>();
            let resolved_rule = rule_primitives.get(rule_name).ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "rule `{rule_name}` has no resolved primitive metadata"
                ))
            })?;
            let ordered_head = !model.head_lets.is_empty() || !resolved_rule.head.is_empty();
            let primitive_result = if ordered_head {
                elaborate_fire_query_sequence(
                    FirePrimitiveSequenceInput {
                        egraph,
                        rule_name,
                        model,
                        metadata: resolved_rule,
                        applications: primitive_applications.clone(),
                        bindings: &mut bindings,
                        prestate_witnesses: &prestate_witnesses,
                    },
                    witnesses,
                )?
                .map(|result| {
                    (
                        result.availability,
                        result.deferred,
                        primitive_applications[result.head_application_start..].to_vec(),
                    )
                })
            } else {
                elaborate_fire_primitive_sequence(
                    FirePrimitiveSequenceInput {
                        egraph,
                        rule_name,
                        model,
                        metadata: resolved_rule,
                        applications: primitive_applications.clone(),
                        bindings: &mut bindings,
                        prestate_witnesses: &prestate_witnesses,
                    },
                    witnesses,
                )?
                .map(|(availability, deferred)| (availability, deferred, Vec::new()))
            };
            let Some(primitive_result) = primitive_result else {
                if !applications_by_origin[ordinal].is_empty()
                    || !unions_by_origin[ordinal].is_empty()
                    || !mutations_by_origin.for_origin(ordinal).is_empty()
                {
                    return Err(CausalSliceError::Invariant(format!(
                        "query-filtered rule `{rule_name}` still produced head effects"
                    )));
                }
                continue;
            };
            let (primitive_availability, primitive_error, head_applications) = primitive_result;
            if ordered_head {
                seed_core_head_bindings(
                    rule_name,
                    &resolved_rule.core_head,
                    &resolved_rule.substitutions,
                    captured,
                    &mut bindings,
                    witnesses,
                    &prestate_witness_snapshot,
                )?;
            }
            let prerequisite_result = (|| {
                let body = ground_atoms_at(
                    egraph,
                    &model.body,
                    &bindings,
                    witnesses,
                    relations,
                    Some(&prestate_witness_snapshot),
                )?;

                let mut premise_dependencies = IndexSet::default();
                premise_dependencies.insert(primitive_availability);
                premise_dependencies.extend(global_use_dependencies(
                    &model.global_uses,
                    witnesses,
                    &equality_forest,
                    &model.span.to_string(),
                )?);
                for row in &body {
                    match producers.get(row) {
                        Some(dependency) => {
                            premise_dependencies.insert(*dependency);
                        }
                        None if new_outputs.contains_key(row) => {
                            return Err(CausalSliceError::Invariant(format!(
                                "rule `{rule_name}` matched a tuple produced only in the same wave: {}",
                                display_row(row)
                            )));
                        }
                        None => {
                            let reason = if equality_forest.edge_count() > 0 {
                                format!(
                                    "an equality-canonicalized premise of rule `{rule_name}` without commit-time relation-row rekey provenance"
                                )
                            } else {
                                format!(
                                    "a premise row of rule `{rule_name}` without source or producer provenance: {}",
                                    display_row(row)
                                )
                            };
                            return Err(CausalSliceError::Unsupported {
                                location: model.span.to_string(),
                                reason,
                            });
                        }
                    }
                }
                let mut non_reflexive_equality_variables = HashSet::default();
                for equality in &model.body_equalities {
                    let left = ground_arg_at(
                        egraph,
                        &equality.left,
                        &equality.sort,
                        &bindings,
                        witnesses,
                        Some(&prestate_witness_snapshot),
                    )?;
                    let right = ground_arg_at(
                        egraph,
                        &equality.right,
                        &equality.sort,
                        &bindings,
                        witnesses,
                        Some(&prestate_witness_snapshot),
                    )?;
                    let sort = egraph.get_sort_by_name(&equality.sort).ok_or_else(|| {
                        CausalSliceError::Invariant(format!(
                            "runtime sort `{}` disappeared",
                            equality.sort
                        ))
                    })?;
                    if sort.is_eq_sort() {
                        if left.value != right.value {
                            non_reflexive_equality_variables.extend(
                                atom_arg_vars(&equality.left)
                                    .into_iter()
                                    .chain(atom_arg_vars(&equality.right))
                                    .map(|(_, variable)| variable.clone()),
                            );
                        }
                        premise_dependencies.insert(dependencies.equality(left, right)?);
                    } else if left.value != right.value {
                        return Err(CausalSliceError::Invariant(format!(
                            "rule `{rule_name}` captured a false scalar body equality at {}",
                            equality.span
                        )));
                    }
                }
                for atom in &model.body {
                    let declaration = &relations[&atom.relation];
                    for (application, sort) in atom.args.iter().zip(&declaration.sorts) {
                        if !matches!(application, AtomArg::App { .. }) {
                            continue;
                        }
                        let output = ground_arg_at(
                            egraph,
                            application,
                            sort,
                            &bindings,
                            witnesses,
                            Some(&prestate_witness_snapshot),
                        )?;
                        premise_dependencies.insert(ground_application_availability(
                            GroundApplicationInput {
                                egraph,
                                application,
                                sort,
                                bindings: &bindings,
                                witnesses,
                                output: &output,
                                equality_forest: &equality_forest,
                                snapshot: Some(&prestate_witness_snapshot),
                                app_index: &mut wave_app_index,
                            },
                            &mut dependencies,
                        )?);
                    }
                }
                for lookup in &model.body_lookups {
                    let output =
                        ground_arg(egraph, &lookup.output, &lookup.sort, &bindings, witnesses)?;
                    let application_output = ground_arg_at(
                        egraph,
                        &lookup.application,
                        &lookup.sort,
                        &bindings,
                        witnesses,
                        Some(&prestate_witness_snapshot),
                    )?;
                    if application_output.value != output.value
                        && egraph
                            .get_sort_by_name(&lookup.sort)
                            .is_some_and(|sort| sort.is_eq_sort())
                    {
                        non_reflexive_equality_variables.extend(
                            atom_arg_vars(&lookup.output)
                                .into_iter()
                                .map(|(_, variable)| variable.clone()),
                        );
                    }
                    let application_availability = ground_application_availability(
                        GroundApplicationInput {
                            egraph,
                            application: &lookup.application,
                            sort: &lookup.sort,
                            bindings: &bindings,
                            witnesses,
                            output: &output,
                            equality_forest: &equality_forest,
                            snapshot: Some(&prestate_witness_snapshot),
                            app_index: &mut wave_app_index,
                        },
                        &mut dependencies,
                    )?;
                    premise_dependencies.insert(application_availability);
                    premise_dependencies.insert(endpoint_availability_at(
                        &output,
                        witnesses,
                        &lookup.span,
                        Some(&prestate_witness_snapshot),
                    )?);
                }
                for lookup in &model.body_functions {
                    if lookup.keys.iter().any(|key| {
                        atom_arg_vars(key).iter().any(|(_, variable)| {
                            non_reflexive_equality_variables.contains(variable.as_str())
                        })
                    }) {
                        return Err(CausalSliceError::Unsupported {
                            location: lookup.span.to_string(),
                            reason: format!(
                                "a mutable function key constrained through a non-reflexive equality in rule `{rule_name}`; the unchanged strict proof extractor rejects the corresponding function fact"
                            ),
                        });
                    }
                    let (_row_dependency, lookup_dependencies) = function_lookup_dependencies(
                        egraph,
                        lookup,
                        &bindings,
                        witnesses,
                        &prestate_witness_snapshot,
                        &function_rows,
                        &equality_forest,
                    )?;
                    premise_dependencies.extend(lookup_dependencies);
                }
                let mut prerequisites = DepArena::EMPTY;
                for dependency in premise_dependencies {
                    prerequisites = dependencies.and(prerequisites, dependency)?;
                }
                for binding in bindings.values() {
                    prerequisites =
                        dependencies.and(prerequisites, witnesses.availability(binding.syntax))?;
                }
                Ok(prerequisites)
            })();
            let (mut prerequisites, prerequisite_error) = match prerequisite_result {
                Ok(prerequisites) => (prerequisites, None),
                Err(CausalSliceError::Unsupported { reason, .. })
                    if supports_pre_wave_prefix_fallback(&reason) =>
                {
                    causal_prefix_fallbacks += 1;
                    (dependencies.prefix(pre_wave_last_event)?, None)
                }
                Err(CausalSliceError::Unsupported { location, reason }) => (
                    DepArena::EMPTY,
                    Some(DeferredUnsupported {
                        location: model.span.to_string(),
                        reason: format!(
                            "{reason} while grounding {location} in rule `{rule_name}`"
                        ),
                    }),
                ),
                Err(error) => return Err(error),
            };
            let deferred_prerequisite_error = primitive_error.or(prerequisite_error);

            let mut ordered_head_error = None;
            let mut effects = if ordered_head {
                match preflight_resolved_head_receipts(
                    rule_name,
                    model,
                    &resolved_rule.core_head,
                    &applications_by_origin[ordinal],
                    &head_applications,
                    trace_functions,
                ) {
                    Ok(receipts) => elaborate_resolved_head(
                        ResolvedHeadInput {
                            egraph,
                            rule_name,
                            model,
                            core_head: &resolved_rule.core_head,
                            receipts,
                            bindings: &mut bindings,
                            trace_functions,
                            prefix_fallback,
                            equality_forest: &equality_forest,
                        },
                        witnesses,
                        &mut dependencies,
                        &mut wave_app_index,
                    )?,
                    Err(CausalSliceError::Unsupported { location, reason }) => {
                        ordered_head_error = Some(DeferredUnsupported {
                            location: model.span.to_string(),
                            reason: format!(
                                "{reason} while grounding {location} in the registered head of rule `{rule_name}`"
                            ),
                        });
                        elaborate_fire_applications(
                            egraph,
                            applications_by_origin[ordinal].iter().copied(),
                            trace_functions,
                            witnesses,
                            prefix_fallback,
                            Some(CausalApplicationInput {
                                equality_forest: &equality_forest,
                                dependencies: &mut dependencies,
                                app_index: &mut wave_app_index,
                            }),
                        )?
                    }
                    Err(error) => return Err(error),
                }
            } else {
                let mut effects = elaborate_fire_applications(
                    egraph,
                    applications_by_origin[ordinal].iter().copied(),
                    trace_functions,
                    witnesses,
                    prefix_fallback,
                    Some(CausalApplicationInput {
                        equality_forest: &equality_forest,
                        dependencies: &mut dependencies,
                        app_index: &mut wave_app_index,
                    }),
                )?;
                alias_captured_head_syntaxes(
                    AliasCapturedHeadInput {
                        egraph,
                        model,
                        bindings: &bindings,
                        applications: &applications_by_origin[ordinal],
                        trace_functions,
                        equality_forest: &equality_forest,
                    },
                    witnesses,
                    &mut dependencies,
                    &mut effects,
                    &mut wave_app_index,
                )?;
                effects
            };
            if effects
                .deferred_error
                .as_ref()
                .is_some_and(supports_pre_wave_constructor_hit_fallback)
            {
                let prefix = dependencies.prefix(pre_wave_last_event)?;
                prerequisites = dependencies.and(prerequisites, prefix)?;
                effects.deferred_error = None;
                causal_prefix_fallbacks += 1;
            }
            let mut opaque_error = ordered_head_error.or_else(|| {
                effects
                    .deferred_error
                    .as_ref()
                    .map(|error| DeferredUnsupported {
                        location: model.span.to_string(),
                        reason: format!("{} in rule `{rule_name}`", error.reason),
                    })
            });
            let mutation_indices = mutations_by_origin.for_origin(ordinal);
            let mutation_receipts = mutation_indices
                .iter()
                .map(|index| &batch.mutations[*index as usize])
                .collect::<Vec<_>>();
            let raw_effective_mutation = mutation_receipts.iter().any(|receipt| {
                matches!(
                    receipt.outcome,
                    TableMutationOutcome::Inserted | TableMutationOutcome::Replaced
                )
            });
            let effective_mutation = if opaque_error.is_some() {
                raw_effective_mutation
            } else {
                match validate_rule_mutation_receipts(
                    egraph,
                    rule_name,
                    model,
                    &bindings,
                    &mutation_receipts,
                    trace_functions,
                    witnesses,
                ) {
                    Ok(effective) => effective,
                    Err(CausalSliceError::Unsupported { location, reason }) => {
                        opaque_error = Some(DeferredUnsupported {
                            location: model.span.to_string(),
                            reason: format!(
                                "{reason} while grounding {location} in the complete head of rule `{rule_name}`"
                            ),
                        });
                        raw_effective_mutation
                    }
                    Err(error) => return Err(error),
                }
            };
            for dependency in effects.read_dependencies.iter().copied() {
                prerequisites = dependencies.and(prerequisites, dependency)?;
            }
            let applied_unions = if opaque_error.is_some() {
                classify_prefix_union_receipts(
                    rule_name,
                    &model.head_unions,
                    &unions_by_origin[ordinal],
                )?
            } else {
                let validation = (|| {
                    for constructor in model.head_constructors.iter().chain(&model.head_subsumes) {
                        let AtomArg::App { output_sort, .. } = constructor else {
                            return Err(CausalSliceError::Invariant(
                                "modeled constructor action lost its application node".to_owned(),
                            ));
                        };
                        ground_arg(egraph, constructor, output_sort, &bindings, witnesses)?;
                    }
                    let expected_head =
                        ground_atoms(egraph, &model.head, &bindings, witnesses, relations)?;
                    if !same_row_multiset(&expected_head, &effects.observed_rows) {
                        return Err(CausalSliceError::Invariant(format!(
                            "native applications for rule `{rule_name}` do not match its complete source head"
                        )));
                    }
                    if prefix_fallback {
                        classify_prefix_union_receipts(
                            rule_name,
                            &model.head_unions,
                            &unions_by_origin[ordinal],
                        )
                    } else {
                        let expected_unions = model
                            .head_unions
                            .iter()
                            .map(|equality| ground_equality(egraph, equality, &bindings, witnesses))
                            .collect::<Result<Vec<_>, _>>()?;
                        match_union_receipts(
                            rule_name,
                            &expected_unions,
                            &unions_by_origin[ordinal],
                        )
                    }
                })();
                match validation {
                    Ok(applied_unions) => applied_unions,
                    Err(CausalSliceError::Unsupported { location, reason }) => {
                        opaque_error = Some(DeferredUnsupported {
                            location: model.span.to_string(),
                            reason: format!(
                                "{reason} while grounding {location} in the complete head of rule `{rule_name}`"
                            ),
                        });
                        classify_prefix_union_receipts(
                            rule_name,
                            &model.head_unions,
                            &unions_by_origin[ordinal],
                        )?
                    }
                    Err(error) => return Err(error),
                }
            };

            let effective_outputs = effects
                .new_rows
                .into_iter()
                .filter(|row| !producers.contains_key(row) && !new_outputs.contains_key(row))
                .collect::<Vec<_>>();
            if let Some(error) = opaque_error {
                opaque_pending_firings += 1;
                let has_effect = !applied_unions.is_empty()
                    || !effective_outputs.is_empty()
                    || !effects.new_witnesses.is_empty()
                    || effective_mutation;
                if !has_effect
                    && !force_wave_prefix
                    && applied_unions.is_empty()
                    && effective_outputs.is_empty()
                    && effects.new_witnesses.is_empty()
                    && !effective_mutation
                {
                    continue;
                }
                let event = events.push(ReplayEvent {
                    kind: EventKind::OpaqueFire,
                    prerequisites,
                    deferred_prerequisite_error: Some(error.clone()),
                    effective_outputs: effective_outputs.clone(),
                })?;
                let dependency = dependencies.event(event)?;
                origin_event_dependencies[ordinal] = Some(dependency);
                for row in effective_outputs {
                    new_outputs.insert(row, dependency);
                }
                for witness in effects.new_witnesses {
                    witnesses.set_availability(witness, dependency);
                }
                for equality in applied_unions {
                    new_equality_edges.push((equality, dependency));
                    if opaque_equality_error.is_none() {
                        opaque_equality_error = Some(error.clone());
                    }
                }
                opaque_promoted_events += usize::from(has_effect);
                continue;
            }
            let replay_bindings = model
                .replay_var_order
                .iter()
                .map(|variable| {
                    bindings
                        .get(variable)
                        .cloned()
                        .map(|binding| (variable.clone(), binding))
                        .ok_or_else(|| {
                            CausalSliceError::Invariant(format!(
                                "completed grounding for rule `{rule_name}` omitted replay variable `{variable}`"
                            ))
                        })
                })
                .collect::<Result<IndexMap<_, _>, _>>()?;
            let grounding = GroundedFire {
                rule: rule_name.to_owned(),
                wave: u32::try_from(wave).map_err(|_| {
                    CausalSliceError::Invariant("wave index exceeded u32 capacity".to_owned())
                })?,
                ordinal: u32::try_from(ordinal).map_err(|_| {
                    CausalSliceError::Invariant("wave ordinal exceeded u32 capacity".to_owned())
                })?,
                bindings: replay_bindings,
                selector: ReplaySelector::Unplanned,
            };
            let has_effect = !effective_outputs.is_empty()
                || !effects.new_witnesses.is_empty()
                || !applied_unions.is_empty()
                || effective_mutation;
            let _promoted = if !has_effect && !force_wave_prefix {
                None
            } else {
                let event = events.push(ReplayEvent {
                    kind: EventKind::Fire(grounding.clone()),
                    prerequisites,
                    deferred_prerequisite_error,
                    effective_outputs: effective_outputs.clone(),
                })?;
                let dependency = dependencies.event(event)?;
                origin_event_dependencies[ordinal] = Some(dependency);
                for row in effective_outputs {
                    new_outputs.insert(row, dependency);
                }
                for witness in effects.new_witnesses {
                    witnesses.set_availability(witness, dependency);
                }
                for equality in applied_unions {
                    new_equality_edges.push((equality, dependency));
                }
                Some(event)
            };
            pending_fires.push(PendingFire {
                grounding,
                effective: has_effect,
            });
        }

        assign_wave_replay_selectors(ReplaySelectorPlanningInput {
            egraph,
            rules,
            witnesses,
            prestate_witness_count: prestate_witness_snapshot.node_count,
            equality_forest: &equality_forest,
            wave,
            pending_fires: &mut pending_fires,
            current_start: wave_pending_start,
            events: &mut events.events[wave_event_start..],
        })?;

        // A bounded ruleset iteration searches against one pre-state. Every
        // captured match must be elaborated before publishing its successful
        // unions, but the equality forest must still observe the native UF
        // commit order across rule-origin and rebuild receipts.
        if !unoriginated_unions.is_empty() {
            let last_event = events
                .events
                .len()
                .checked_sub(1)
                .map(|index| EventId(index as u32));
            let prefix = dependencies.prefix(last_event)?;
            for receipt in unoriginated_unions {
                match type_unoriginated_equality(egraph, witnesses, receipt, wave) {
                    Ok(equality) => {
                        new_equality_edges.push((equality, prefix));
                        causal_prefix_fallbacks += 1;
                    }
                    Err(error) => {
                        opaque_equality_error.get_or_insert(error);
                    }
                }
            }
        }
        new_equality_edges.sort_by_key(|(equality, _)| equality.commit_ordinal);
        let mut typed_edges = new_equality_edges.into_iter().peekable();
        for (commit_ordinal, receipt) in batch.unions.iter().enumerate() {
            equality_forest.observe_receipt(receipt)?;
            if typed_edges
                .peek()
                .is_some_and(|(equality, _)| equality.commit_ordinal == commit_ordinal)
            {
                let (equality, dependency) = typed_edges
                    .next()
                    .expect("peeked typed equality edge disappeared");
                equality_forest.add_explanation(equality, dependency)?;
            }
        }
        if let Some((equality, _)) = typed_edges.next() {
            return Err(CausalSliceError::Invariant(format!(
                "typed equality edge retained unknown commit ordinal {} in traced wave {wave}",
                equality.commit_ordinal
            )));
        }
        apply_wave_mutation_receipts(
            wave,
            &batch.mutations,
            trace_functions,
            &origin_event_dependencies,
            &mut function_rows,
            &equality_forest,
            &mut dependencies,
        )?;
        for (row, dependency) in new_outputs {
            producers.insert(row, dependency);
        }
        causal_prefix_fallbacks += refresh_rebuilt_container_witnesses(
            egraph,
            witnesses,
            wave,
            &batch.rebuilt_containers,
            events
                .events
                .len()
                .checked_sub(1)
                .map(|index| EventId(index as u32)),
            &mut dependencies,
        )?;
    }
    Ok(Elaboration {
        pending_fires,
        opaque_pending_firings,
        opaque_promoted_events,
        events,
        dependencies,
        producers,
        source_events,
        equality_forest,
        opaque_equality_error,
        causal_prefix_fallbacks,
    })
}

fn refresh_rebuilt_container_witnesses(
    egraph: &EGraph,
    witnesses: &mut WitnessArena,
    wave: usize,
    rebuilt_containers: &[Value],
    last_replayable_event: Option<EventId>,
    dependencies: &mut DepArena,
) -> Result<usize, CausalSliceError> {
    if rebuilt_containers.is_empty() {
        return Ok(0);
    }
    let rebuilt = rebuilt_containers.iter().copied().collect::<HashSet<_>>();
    let changed = witnesses
        .endpoint_instances
        .keys()
        .filter(|endpoint| {
            rebuilt.contains(&endpoint.value)
                && egraph
                    .get_sort_by_name(&endpoint.sort)
                    .is_some_and(|sort| sort.is_container_sort())
        })
        .cloned()
        .collect::<Vec<_>>();
    if changed.is_empty() {
        return Ok(0);
    }

    let prefix = dependencies.prefix(last_replayable_event)?;
    for endpoint in &changed {
        let runtime_sort = egraph.get_sort_by_name(&endpoint.sort).ok_or_else(|| {
            CausalSliceError::Invariant(format!(
                "runtime container sort `{}` disappeared",
                endpoint.sort
            ))
        })?;
        let runtime_type = runtime_sort.value_type();
        let replayable_stable_transition =
            runtime_type == Some(std::any::TypeId::of::<crate::sort::VecContainer>());
        let poison = if replayable_stable_transition {
            None
        } else {
            Some(dependencies.unsupported(
                format!("traced wave {wave}"),
                format!(
                    "container witness of sort `{}` whose semantic contents changed during rebuild; only deterministic stable-ID Vec transitions currently have replay support",
                    endpoint.sort
                ),
            )?)
        };
        let previous = witnesses
            .current_container_support(endpoint)
            .or_else(|| {
                witnesses
                    .by_endpoint(&endpoint.sort, endpoint.value)
                    .map(|witness| witnesses.availability(witness))
            })
            .ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "rebuilt container endpoint {endpoint:?} lost every replay witness"
                ))
            })?;
        let mut support = dependencies.and(previous, prefix)?;
        if let Some(poison) = poison {
            support = dependencies.and(support, poison)?;
        }
        // Earlier firings already copied `previous`. Replacing one typed
        // current-support pointer gives every later alias the new temporal
        // support without an O(aliases) rewrite or a version-history arena.
        witnesses.replace_current_container_support(endpoint.clone(), support);
    }
    Ok(changed.len())
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ObservationConstructorRow {
    inputs: Box<[Value]>,
    output: Value,
}

fn captured_observation_constructor_rows(
    egraph: &EGraph,
    batch: &RuleExecutionTrace,
    match_index: usize,
    constructors: &IndexMap<String, ConstructorDecl>,
) -> Result<IndexMap<String, Vec<ObservationConstructorRow>>, CausalSliceError> {
    let applications = batch
        .primitives
        .iter()
        .filter(|application| application.origin.index() == match_index)
        .collect::<Vec<_>>();
    let marker_function = applications
        .iter()
        .filter(|application| application.args.is_empty())
        .max_by_key(|application| application.instruction)
        .map(|application| application.function)
        .ok_or_else(|| {
            CausalSliceError::Invariant(
                "a positive-check match omitted its trace marker application".to_owned(),
            )
        })?;
    let marker = literal_to_value(
        egraph.backend.base_values(),
        &Literal::String(crate::CAUSAL_CHECK_CONSTRUCTOR_MARKER.to_owned()),
    );
    let mut result = IndexMap::<String, Vec<ObservationConstructorRow>>::default();
    for application in applications {
        if application.function != marker_function || application.args.first() != Some(&marker) {
            continue;
        }
        let Some(function_value) = application.args.get(1) else {
            return Err(CausalSliceError::Invariant(
                "a positive-check constructor marker omitted its function name".to_owned(),
            ));
        };
        let function = egraph
            .backend
            .base_values()
            .unwrap::<crate::sort::S>(*function_value)
            .0;
        let Some(constructor) = constructors.get(&function) else {
            continue;
        };
        if application.args.len() != constructor.inputs.len() + 3 {
            return Err(CausalSliceError::Invariant(format!(
                "positive-check constructor marker `{function}` had the wrong arity"
            )));
        }
        let row = ObservationConstructorRow {
            inputs: application.args[2..application.args.len() - 1]
                .to_vec()
                .into_boxed_slice(),
            output: application.args[application.args.len() - 1],
        };
        let rows = result.entry(function).or_default();
        if !rows.contains(&row) {
            rows.push(row);
        }
    }
    Ok(result)
}

#[allow(clippy::too_many_arguments)]
fn prepare_observation_arg(
    egraph: &EGraph,
    arg: &AtomArg,
    sort: &str,
    bindings: &IndexMap<String, BindingWitness>,
    constructor_rows: &IndexMap<String, Vec<ObservationConstructorRow>>,
    primitive_applications: &[&PrimitiveApplication],
    witnesses: &mut WitnessArena,
    dependencies: &mut DepArena,
    equality_forest: &EqualityForest,
    opaque_equality_error: Option<&DeferredUnsupported>,
    app_index: &mut WaveAppIndex,
    selected_dependencies: &mut IndexSet<DepId>,
) -> Result<(TypedEndpoint, WitnessId), CausalSliceError> {
    let (value, witness) = match arg {
        AtomArg::Lit(literal) => {
            let value = literal_to_value(egraph.backend.base_values(), literal);
            let witness = witnesses.intern_literal(sort, literal.clone())?;
            match witnesses.endpoint(witness) {
                Some(endpoint) if endpoint == value => {}
                Some(_) => {
                    return Err(CausalSliceError::Invariant(format!(
                        "observation literal of sort `{sort}` changed runtime endpoint"
                    )));
                }
                None => witnesses.bind_endpoint_alias(sort, value, witness)?,
            }
            (value, witness)
        }
        AtomArg::Global {
            name,
            sort: modeled_sort,
        } => {
            if modeled_sort != sort {
                return Err(CausalSliceError::Invariant(format!(
                    "observation global `{name}` was modeled as `{modeled_sort}` but used as `{sort}`"
                )));
            }
            let value = witnesses.global(name, sort)?;
            let witness = witnesses.by_endpoint(sort, value).ok_or_else(|| {
                CausalSliceError::Unsupported {
                    location: "positive check".to_owned(),
                    reason: format!("source global `{name}` without an exact match-time witness"),
                }
            })?;
            (value, witness)
        }
        AtomArg::Var(_, variable) => {
            let binding = bindings.get(variable).ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "observation grounding omitted source variable `{variable}`"
                ))
            })?;
            (binding.endpoint, binding.syntax)
        }
        AtomArg::App {
            function,
            args,
            input_sorts,
            output_sort,
            primitive,
        } => {
            if output_sort != sort {
                return Err(CausalSliceError::Invariant(format!(
                    "observation constructor `{function}` was modeled as `{output_sort}` but used as `{sort}`"
                )));
            }
            let children = args
                .iter()
                .zip(input_sorts)
                .map(|(child, child_sort)| {
                    prepare_observation_arg(
                        egraph,
                        child,
                        child_sort,
                        bindings,
                        constructor_rows,
                        primitive_applications,
                        witnesses,
                        dependencies,
                        equality_forest,
                        opaque_equality_error,
                        app_index,
                        selected_dependencies,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            let child_witnesses = children
                .iter()
                .map(|(_, witness)| *witness)
                .collect::<Vec<_>>();
            if let Some(capability) = primitive {
                let expected_function = capability.specialization.external_id(crate::Context::Read);
                let child_values = children
                    .iter()
                    .map(|(endpoint, _)| endpoint.value)
                    .collect::<Vec<_>>();
                let mut outputs = primitive_applications
                    .iter()
                    .filter(|application| {
                        application.function == expected_function
                            && application.args == child_values
                    })
                    .map(|application| application.result)
                    .collect::<Vec<_>>();
                outputs.sort_unstable();
                outputs.dedup();
                if outputs.len() != 1 {
                    return Err(CausalSliceError::Unsupported {
                        location: format!("positive check primitive `{function}`"),
                        reason: format!(
                            "{} exact match-time primitive results for the grounded source occurrence",
                            outputs.len()
                        ),
                    });
                }
                let mut availability = DepArena::EMPTY;
                for child in &child_witnesses {
                    availability =
                        dependencies.and(availability, witnesses.availability(*child))?;
                }
                let value = outputs[0];
                let witness = witnesses.intern_app(
                    sort,
                    function,
                    child_witnesses,
                    value,
                    availability,
                    true,
                )?;
                witnesses.prefer_endpoint_witness(sort, value, witness)?;
                selected_dependencies.insert(witnesses.availability(witness));
                return Ok((
                    TypedEndpoint {
                        sort: sort.to_owned(),
                        value,
                    },
                    witness,
                ));
            }
            if matches!(function.as_str(), "bigint" | "bigrat") {
                let (_, expected_function) =
                    resolve_auxiliary_scalar_function(egraph, function, crate::Context::Read)?;
                let child_values = children
                    .iter()
                    .map(|(endpoint, _)| endpoint.value)
                    .collect::<Vec<_>>();
                let mut outputs = primitive_applications
                    .iter()
                    .filter(|application| {
                        application.function == expected_function
                            && application.args == child_values
                    })
                    .map(|application| application.result)
                    .collect::<Vec<_>>();
                outputs.sort_unstable();
                outputs.dedup();
                if outputs.len() != 1 {
                    return Err(CausalSliceError::Unsupported {
                        location: format!("positive check constructor `{function}`"),
                        reason: format!(
                            "{} exact match-time primitive applications for the grounded inputs",
                            outputs.len()
                        ),
                    });
                }
                let value = outputs[0];
                let witness = witnesses.intern_app(
                    sort,
                    function,
                    child_witnesses,
                    value,
                    DepArena::EMPTY,
                    true,
                )?;
                witnesses.prefer_endpoint_witness(sort, value, witness)?;
                selected_dependencies.insert(witnesses.availability(witness));
                return Ok((
                    TypedEndpoint {
                        sort: sort.to_owned(),
                        value,
                    },
                    witness,
                ));
            }
            let node = WitnessNode::App {
                sort: sort.to_owned(),
                function: function.clone(),
                children: child_witnesses,
            };
            let candidates =
                constructor_rows
                    .get(function)
                    .ok_or_else(|| CausalSliceError::Unsupported {
                        location: format!("positive check constructor `{function}`"),
                        reason: "syntax without an exact match-time constructor row".to_owned(),
                    })?;
            let mut outputs = candidates
                .iter()
                .filter(|row| {
                    row.inputs
                        .iter()
                        .zip(&children)
                        .all(|(value, (endpoint, _))| *value == endpoint.value)
                })
                .map(|row| row.output)
                .collect::<Vec<_>>();
            outputs.sort_unstable();
            outputs.dedup();
            if outputs.len() != 1 {
                return Err(CausalSliceError::Unsupported {
                    location: format!("positive check constructor `{function}`"),
                    reason: format!(
                        "{} exact match-time constructor rows for the grounded inputs",
                        outputs.len()
                    ),
                });
            }
            let value = outputs[0];
            let witness = if let Some(witness) =
                witnesses.instance_by_node_endpoint(sort, value, &node)
            {
                witness
            } else {
                let availability = match congruent_app_availability_explained(
                    witnesses,
                    &node,
                    value,
                    equality_forest,
                    dependencies,
                    None,
                    app_index,
                )? {
                    Some(availability) => availability,
                    None if opaque_equality_error.is_some() => {
                        let error = opaque_equality_error.expect("checked as present");
                        return Err(CausalSliceError::Unsupported {
                            location: error.location.clone(),
                            reason: error.reason.clone(),
                        });
                    }
                    None => {
                        return Err(CausalSliceError::Unsupported {
                            location: format!("positive check constructor `{function}`"),
                            reason: "a match-time constructor rekey without complete child equality provenance"
                                .to_owned(),
                        });
                    }
                };
                witnesses.alias_app_endpoint(node.clone(), value, availability)?
            };
            witnesses.ids.insert(node, witness);
            witnesses.prefer_endpoint_witness(sort, value, witness)?;
            (value, witness)
        }
    };
    selected_dependencies.insert(witnesses.availability(witness));
    Ok((
        TypedEndpoint {
            sort: sort.to_owned(),
            value,
        },
        witness,
    ))
}

fn observation_roots(
    input: ObservationInput<'_>,
    dependencies: &mut DepArena,
    witnesses: &mut WitnessArena,
) -> Result<DepId, CausalSliceError> {
    let ObservationInput {
        egraph,
        checks,
        relations,
        constructors,
        traces,
        producers,
        equality_forest,
        opaque_equality_error,
    } = input;
    if checks.len() != traces.len() {
        return Err(CausalSliceError::Invariant(format!(
            "captured {} check traces for {} observations",
            traces.len(),
            checks.len()
        )));
    }

    let mut root = DepArena::EMPTY;
    let mut app_index = WaveAppIndex::default();
    for (check, batches) in checks.iter().zip(traces) {
        if batches
            .iter()
            .any(|batch| !batch.applications.is_empty() || !batch.unions.is_empty())
        {
            return Err(CausalSliceError::Unsupported {
                location: "positive check trace".to_owned(),
                reason: "an observation that stages constructor or relation applications"
                    .to_owned(),
            });
        }
        let (batch, match_index, captured) = batches
            .iter()
            .find_map(|batch| {
                batch
                    .matches
                    .first()
                    .map(|captured| (batch, 0usize, captured))
            })
            .ok_or_else(|| {
                CausalSliceError::Invariant(
                    "a successful positive check had no captured satisfying match".to_owned(),
                )
            })?;
        witnesses.load_current_globals(&batch.globals)?;
        for dependency in global_use_dependencies(
            &check.global_uses,
            witnesses,
            equality_forest,
            "positive check",
        )? {
            root = dependencies.and(root, dependency)?;
        }
        let var_order = check.var_sorts.keys().cloned().collect::<Vec<_>>();
        let bindings = reconstruct_bindings(
            egraph,
            &captured.bindings,
            &var_order,
            &check.var_sorts,
            witnesses,
        )?;
        let constructor_rows =
            captured_observation_constructor_rows(egraph, batch, match_index, constructors)?;
        let primitive_applications = batch
            .primitives
            .iter()
            .filter(|application| application.origin.index() == match_index)
            .collect::<Vec<_>>();
        let mut observation_witness_dependencies = IndexSet::default();
        for atom in &check.atoms {
            let declaration = &relations[&atom.relation];
            for (arg, sort) in atom.args.iter().zip(&declaration.sorts) {
                prepare_observation_arg(
                    egraph,
                    arg,
                    sort,
                    &bindings,
                    &constructor_rows,
                    &primitive_applications,
                    witnesses,
                    dependencies,
                    equality_forest,
                    opaque_equality_error,
                    &mut app_index,
                    &mut observation_witness_dependencies,
                )?;
            }
        }
        for equality in &check.equalities {
            for arg in [&equality.left, &equality.right] {
                prepare_observation_arg(
                    egraph,
                    arg,
                    &equality.sort,
                    &bindings,
                    &constructor_rows,
                    &primitive_applications,
                    witnesses,
                    dependencies,
                    equality_forest,
                    opaque_equality_error,
                    &mut app_index,
                    &mut observation_witness_dependencies,
                )?;
            }
        }
        for dependency in observation_witness_dependencies {
            root = dependencies.and(root, dependency)?;
        }
        for binding in bindings.values() {
            root = dependencies.and(root, witnesses.availability(binding.syntax))?;
        }
        for row in ground_atoms(egraph, &check.atoms, &bindings, witnesses, relations)? {
            match producers.get(&row) {
                Some(dependency) => {
                    root = dependencies.and(root, *dependency)?;
                }
                None => {
                    return Err(CausalSliceError::Invariant(format!(
                        "positive check selected a tuple with no source or rule producer: {}",
                        display_row(&row)
                    )));
                }
            }
        }
        for equality in &check.equalities {
            let (left, right) = ground_equality(egraph, equality, &bindings, witnesses)?;
            root = dependencies.and(
                root,
                endpoint_availability(&left, witnesses, &equality.span)?,
            )?;
            root = dependencies.and(
                root,
                endpoint_availability(&right, witnesses, &equality.span)?,
            )?;
            let explanation = match equality_forest.explain(&left, &right) {
                Some(explanation) => explanation,
                None if opaque_equality_error.is_some() => {
                    return Err(opaque_equality_error
                        .expect("checked as present")
                        .clone()
                        .into_error());
                }
                None => {
                    return Err(CausalSliceError::Invariant(format!(
                        "positive check matched equality `{}` without a recorded cause",
                        equality.span
                    )));
                }
            };
            for dependency in explanation {
                root = dependencies.and(root, dependency)?;
            }
        }
    }
    Ok(root)
}

fn reconstruct_bindings(
    egraph: &EGraph,
    captured: &[(std::sync::Arc<str>, Value)],
    var_order: &[String],
    var_sorts: &IndexMap<String, String>,
    witnesses: &mut WitnessArena,
) -> Result<IndexMap<String, BindingWitness>, CausalSliceError> {
    let captured_by_name = captured
        .iter()
        .map(|(name, value)| (name.as_ref(), *value))
        .collect::<HashMap<_, _>>();
    let mut result = IndexMap::default();
    for var in var_order {
        let value = captured_by_name.get(var.as_str()).copied().ok_or_else(|| {
            let available = captured_by_name
                .keys()
                .copied()
                .collect::<Vec<_>>()
                .join(", ");
            CausalSliceError::Invariant(format!(
                "match-time binding for `{var}` was projected away; available names: [{available}]"
            ))
        })?;
        let sort_name = &var_sorts[var];
        let sort = egraph.get_sort_by_name(sort_name).ok_or_else(|| {
            CausalSliceError::Invariant(format!("runtime sort `{sort_name}` disappeared"))
        })?;
        let syntax = if sort.is_eq_sort() || sort.is_container_sort() {
            witnesses.by_endpoint(sort_name, value).ok_or_else(|| {
                CausalSliceError::Unsupported {
                    location: format!("captured binding `{var}`"),
                    reason: format!("a `{sort_name}` endpoint without a match-time replay witness"),
                }
            })?
        } else {
            scalar_witness(
                egraph,
                sort_name,
                value,
                witnesses,
                &format!("binding `{var}`"),
            )?
        };
        let binding = BindingWitness {
            syntax,
            endpoint: value,
        };
        debug_assert_eq!(binding.endpoint, value);
        result.insert(var.clone(), binding);
    }
    Ok(result)
}

fn reconstruct_rule_bindings(
    egraph: &EGraph,
    rule_name: &str,
    captured: &[(std::sync::Arc<str>, Value)],
    model: &RuleModel,
    witnesses: &mut WitnessArena,
    snapshot: Option<&WitnessSnapshot>,
) -> Result<IndexMap<String, BindingWitness>, BindingReconstructionError> {
    let captured_by_name = captured
        .iter()
        .map(|(name, value)| (name.as_ref(), *value))
        .collect::<HashMap<_, _>>();
    let mut result = IndexMap::default();
    for var in &model.var_order {
        let Some(value) = captured_by_name.get(var.as_str()).copied() else {
            continue;
        };
        let sort_name = &model.var_sorts[var];
        let sort = egraph.get_sort_by_name(sort_name).ok_or_else(|| {
            CausalSliceError::Invariant(format!("runtime sort `{sort_name}` disappeared"))
        })?;
        let syntax = if sort.is_eq_sort() || sort.is_container_sort() {
            witnesses
                .by_endpoint_at(sort_name, value, snapshot)
                .ok_or_else(|| CausalSliceError::Unsupported {
                    location: format!("captured binding `{var}` in rule `{rule_name}`"),
                    reason: format!("a `{sort_name}` endpoint without a match-time replay witness"),
                })?
        } else {
            scalar_witness(
                egraph,
                sort_name,
                value,
                witnesses,
                &format!("binding `{var}`"),
            )?
        };
        result.insert(
            var.clone(),
            BindingWitness {
                syntax,
                endpoint: value,
            },
        );
    }

    let mut changed = true;
    while changed {
        changed = false;
        for lookup in &model.body_lookups {
            let AtomArg::Var(_, output_var) = &lookup.output else {
                continue;
            };
            if result.contains_key(output_var)
                || atom_arg_vars(&lookup.application)
                    .iter()
                    .any(|(_, var)| !result.contains_key(*var))
            {
                continue;
            }
            let endpoint = ground_arg_at(
                egraph,
                &lookup.application,
                &lookup.sort,
                &result,
                witnesses,
                snapshot,
            )?;
            let syntax = witnesses
                .by_endpoint_at(&lookup.sort, endpoint.value, snapshot)
                .ok_or_else(|| CausalSliceError::Unsupported {
                    location: lookup.span.to_string(),
                    reason: format!(
                        "a derived constructor output `{output_var}` without replay syntax"
                    ),
                })?;
            result.insert(
                output_var.clone(),
                BindingWitness {
                    syntax,
                    endpoint: endpoint.value,
                },
            );
            changed = true;
        }
    }

    let query_outputs = model
        .body_primitives
        .iter()
        .filter_map(|primitive| match primitive.output.as_ref() {
            Some(AtomArg::Var(_, output)) => Some(output.as_str()),
            _ => None,
        })
        .collect::<HashSet<_>>();
    if let Some(var) = model
        .var_order
        .iter()
        .find(|var| !result.contains_key(var.as_str()) && !query_outputs.contains(var.as_str()))
    {
        let available = captured_by_name
            .keys()
            .copied()
            .collect::<Vec<_>>()
            .join(", ");
        return Err(BindingReconstructionError::Projected(DeferredUnsupported {
            location: model.span.to_string(),
            reason: format!(
                "match-time binding for `{var}` in rule `{rule_name}` was projected away and could not be derived from constructor inputs; available names: [{available}]"
            ),
        }));
    }
    Ok(result)
}

fn ensure_rule_bindings_complete(
    rule_name: &str,
    model: &RuleModel,
    bindings: &IndexMap<String, BindingWitness>,
) -> Result<(), CausalSliceError> {
    if let Some(variable) = model
        .var_order
        .iter()
        .find(|variable| !bindings.contains_key(variable.as_str()))
    {
        return Err(CausalSliceError::Invariant(format!(
            "completed grounding for rule `{rule_name}` omitted replay variable `{variable}`"
        )));
    }
    Ok(())
}

fn ground_atoms(
    egraph: &EGraph,
    atoms: &[AtomTemplate],
    bindings: &IndexMap<String, BindingWitness>,
    witnesses: &WitnessArena,
    relations: &IndexMap<String, RelationDecl>,
) -> Result<Vec<RowKey>, CausalSliceError> {
    ground_atoms_at(egraph, atoms, bindings, witnesses, relations, None)
}

fn ground_atoms_at(
    egraph: &EGraph,
    atoms: &[AtomTemplate],
    bindings: &IndexMap<String, BindingWitness>,
    witnesses: &WitnessArena,
    relations: &IndexMap<String, RelationDecl>,
    snapshot: Option<&WitnessSnapshot>,
) -> Result<Vec<RowKey>, CausalSliceError> {
    atoms
        .iter()
        .map(|atom| {
            let declaration = &relations[&atom.relation];
            let args = atom
                .args
                .iter()
                .zip(&declaration.sorts)
                .map(|(arg, sort)| ground_arg_at(egraph, arg, sort, bindings, witnesses, snapshot))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(RowKey {
                relation: atom.relation.clone(),
                args,
            })
        })
        .collect()
}

fn ground_equality(
    egraph: &EGraph,
    equality: &EqualityTemplate,
    bindings: &IndexMap<String, BindingWitness>,
    witnesses: &WitnessArena,
) -> Result<(TypedEndpoint, TypedEndpoint), CausalSliceError> {
    let left = ground_arg(egraph, &equality.left, &equality.sort, bindings, witnesses)?;
    let right = ground_arg(egraph, &equality.right, &equality.sort, bindings, witnesses)?;
    if left.sort != right.sort {
        return Err(CausalSliceError::Invariant(format!(
            "modeled equality `{}` grounded at two runtime sorts",
            equality.span
        )));
    }
    Ok((left, right))
}

struct GroundApplicationInput<'a> {
    egraph: &'a EGraph,
    application: &'a AtomArg,
    sort: &'a str,
    bindings: &'a IndexMap<String, BindingWitness>,
    witnesses: &'a WitnessArena,
    output: &'a TypedEndpoint,
    equality_forest: &'a EqualityForest,
    snapshot: Option<&'a WitnessSnapshot>,
    app_index: &'a mut WaveAppIndex,
}

fn ground_application_availability(
    input: GroundApplicationInput<'_>,
    dependencies: &mut DepArena,
) -> Result<DepId, CausalSliceError> {
    let GroundApplicationInput {
        egraph,
        application,
        sort,
        bindings,
        witnesses,
        output,
        equality_forest,
        snapshot,
        app_index,
    } = input;
    let AtomArg::App {
        function,
        args,
        input_sorts,
        ..
    } = application
    else {
        return Err(CausalSliceError::Invariant(
            "constructor lookup grounding lost its application".to_owned(),
        ));
    };
    if output.sort != sort {
        return Err(CausalSliceError::Invariant(format!(
            "constructor lookup `{function}` produced `{}` after being modeled as `{sort}`",
            output.sort
        )));
    }
    let children = args
        .iter()
        .zip(input_sorts)
        .map(|(child, child_sort)| {
            ground_arg_with_witness_at(egraph, child, child_sort, bindings, witnesses, snapshot)
                .map(|(_, witness)| witness)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let expected = WitnessNode::App {
        sort: sort.to_owned(),
        function: function.clone(),
        children,
    };
    congruent_app_availability(
        witnesses,
        &expected,
        output.value,
        equality_forest,
        dependencies,
        snapshot,
        app_index,
    )?
    .ok_or_else(|| CausalSliceError::Unsupported {
        location: format!("grounded constructor `{function}`"),
        reason: "exact match-time row without prior constructor-row provenance".to_owned(),
    })
}

fn endpoint_availability(
    endpoint: &TypedEndpoint,
    witnesses: &WitnessArena,
    span: &Span,
) -> Result<DepId, CausalSliceError> {
    endpoint_availability_at(endpoint, witnesses, span, None)
}

fn endpoint_availability_at(
    endpoint: &TypedEndpoint,
    witnesses: &WitnessArena,
    span: &Span,
    snapshot: Option<&WitnessSnapshot>,
) -> Result<DepId, CausalSliceError> {
    let witness = witnesses
        .by_endpoint_at(&endpoint.sort, endpoint.value, snapshot)
        .ok_or_else(|| CausalSliceError::Unsupported {
            location: span.to_string(),
            reason: format!(
                "an equality endpoint of sort `{}` without match-time replay syntax",
                endpoint.sort
            ),
        })?;
    Ok(witnesses.availability(witness))
}

fn global_use_dependencies(
    uses: &IndexMap<String, String>,
    witnesses: &WitnessArena,
    equality_forest: &EqualityForest,
    location: &str,
) -> Result<IndexSet<DepId>, CausalSliceError> {
    let mut dependencies = IndexSet::default();
    for (name, sort) in uses {
        let (definition, current) = witnesses.global_endpoints(name, sort)?;
        for endpoint in [definition, current] {
            let witness = witnesses
                .by_endpoint(&endpoint.sort, endpoint.value)
                .ok_or_else(|| CausalSliceError::Unsupported {
                    location: location.to_owned(),
                    reason: format!(
                        "source global `{name}` endpoint without match-time replay syntax"
                    ),
                })?;
            dependencies.insert(witnesses.availability(witness));
        }
        let explanation = equality_forest
            .explain(definition, current)
            .ok_or_else(|| CausalSliceError::Unsupported {
                location: location.to_owned(),
                reason: format!(
                    "source global `{name}` changed runtime endpoint without a captured successful-union path"
                ),
            })?;
        dependencies.extend(explanation);
    }
    Ok(dependencies)
}

fn logical_function_row(
    table: TableId,
    row: &[Value],
    trace_functions: &IndexMap<TableId, TraceFunctionMeta>,
    location: &str,
) -> Result<(FunctionRowKey, TypedEndpoint), CausalSliceError> {
    let meta = trace_functions.get(&table).ok_or_else(|| {
        CausalSliceError::Invariant(format!(
            "{location} referenced unmodeled mutation table {table:?}"
        ))
    })?;
    if meta.kind != TraceFunctionKind::Mutable {
        return Err(CausalSliceError::Invariant(format!(
            "{location} reported a mutation for non-mutable traced function `{}`",
            meta.name
        )));
    }
    let logical_arity = meta.input_sorts.len() + 1;
    if row.len() < logical_arity {
        return Err(CausalSliceError::Invariant(format!(
            "{location} captured {} columns for mutable function `{}` with logical arity {logical_arity}",
            row.len(),
            meta.name
        )));
    }
    let keys = meta
        .input_sorts
        .iter()
        .zip(&row[..meta.input_sorts.len()])
        .map(|(sort, value)| TypedEndpoint {
            sort: sort.clone(),
            value: *value,
        })
        .collect();
    let output = TypedEndpoint {
        sort: meta.output_sort.clone(),
        value: row[meta.input_sorts.len()],
    };
    Ok((
        FunctionRowKey {
            function: meta.name.clone(),
            keys,
        },
        output,
    ))
}

fn ground_function_set(
    egraph: &EGraph,
    set: &FunctionSetTemplate,
    bindings: &IndexMap<String, BindingWitness>,
    witnesses: &WitnessArena,
) -> Result<(FunctionRowKey, TypedEndpoint), CausalSliceError> {
    let keys = set
        .keys
        .iter()
        .zip(&set.input_sorts)
        .map(|(key, sort)| ground_arg(egraph, key, sort, bindings, witnesses))
        .collect::<Result<Vec<_>, _>>()?;
    let output = ground_arg(egraph, &set.value, &set.output_sort, bindings, witnesses)?;
    Ok((
        FunctionRowKey {
            function: set.function.clone(),
            keys,
        },
        output,
    ))
}

fn validate_rule_mutation_receipts(
    egraph: &EGraph,
    rule_name: &str,
    model: &RuleModel,
    bindings: &IndexMap<String, BindingWitness>,
    receipts: &[&TableMutationReceipt],
    trace_functions: &IndexMap<TableId, TraceFunctionMeta>,
    witnesses: &WitnessArena,
) -> Result<bool, CausalSliceError> {
    if model.head_sets.len() != receipts.len() {
        return Err(CausalSliceError::Invariant(format!(
            "rule `{rule_name}` modeled {} causal set action(s) but native commit reported {} rule-attributed mutation receipt(s)",
            model.head_sets.len(),
            receipts.len()
        )));
    }
    let expected = model
        .head_sets
        .iter()
        .map(|set| ground_function_set(egraph, set, bindings, witnesses))
        .collect::<Result<Vec<_>, _>>()?;
    let mut used = vec![false; expected.len()];
    let mut instructions = HashSet::default();
    let mut effective = false;
    for receipt in receipts {
        let TableMutationCause::Rule { instruction, .. } = receipt.cause else {
            return Err(CausalSliceError::Invariant(format!(
                "rule `{rule_name}` was grouped with a non-rule mutation receipt"
            )));
        };
        if !instructions.insert(instruction) {
            return Err(CausalSliceError::Invariant(format!(
                "rule `{rule_name}` reported more than one mutation for traced head instruction {instruction}"
            )));
        }
        let location = format!("mutation from rule `{rule_name}` instruction {instruction}");
        let merge = trace_functions
            .get(&receipt.table)
            .and_then(|meta| meta.mutable_merge)
            .ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "{location} referenced a mutation table without a modeled merge"
                ))
            })?;
        if !matches!(
            merge,
            MutableMergeKind::AssertEq | MutableMergeKind::ExactNew
        ) {
            return Err(CausalSliceError::Invariant(format!(
                "{location} reached causal set validation with an unsupported custom merge"
            )));
        }
        let incoming =
            logical_function_row(receipt.table, &receipt.incoming, trace_functions, &location)?;
        let Some(expected_index) = expected
            .iter()
            .enumerate()
            .position(|(index, row)| !used[index] && row == &incoming)
        else {
            let expected_locations = model
                .head_sets
                .iter()
                .map(|set| set.span.to_string())
                .collect::<Vec<_>>();
            return Err(CausalSliceError::Invariant(format!(
                "{location} committed logical row {incoming:?}, which does not match any remaining complete-head set {expected:?} at {expected_locations:?}"
            )));
        };
        used[expected_index] = true;

        let committed = logical_function_row(
            receipt.table,
            &receipt.committed,
            trace_functions,
            &location,
        )?;
        if committed != incoming {
            return Err(CausalSliceError::Invariant(format!(
                "{location} selected {committed:?} instead of its incoming row {incoming:?} for an incoming-preserving causal merge"
            )));
        }
        let previous = receipt
            .previous
            .as_deref()
            .map(|row| logical_function_row(receipt.table, row, trace_functions, &location))
            .transpose()?;
        match receipt.outcome {
            TableMutationOutcome::Inserted => {
                if previous.is_some() {
                    return Err(CausalSliceError::Invariant(format!(
                        "{location} reported Inserted with a previous row"
                    )));
                }
                effective = true;
            }
            TableMutationOutcome::Replaced => {
                let Some((previous_key, previous_output)) = previous else {
                    return Err(CausalSliceError::Invariant(format!(
                        "{location} reported Replaced without a previous row"
                    )));
                };
                if previous_key != incoming.0 {
                    return Err(CausalSliceError::Invariant(format!(
                        "{location} replaced a row at a different logical key"
                    )));
                }
                if merge == MutableMergeKind::AssertEq && previous_output != incoming.1 {
                    return Err(CausalSliceError::Unsupported {
                        location,
                        reason: "an assert-equal function write that selected between distinct runtime outputs"
                            .to_owned(),
                    });
                }
                effective = true;
            }
            TableMutationOutcome::NoOp => {
                let Some(previous) = previous else {
                    return Err(CausalSliceError::Invariant(format!(
                        "{location} reported NoOp without a previous row"
                    )));
                };
                if previous != committed {
                    return Err(CausalSliceError::Invariant(format!(
                        "{location} reported a causal set no-op whose selected row differs from the previous row"
                    )));
                }
            }
        }
    }
    debug_assert!(used.into_iter().all(|matched| matched));
    Ok(effective)
}

fn function_lookup_dependencies(
    egraph: &EGraph,
    lookup: &FunctionLookupTemplate,
    bindings: &IndexMap<String, BindingWitness>,
    witnesses: &WitnessArena,
    snapshot: &WitnessSnapshot,
    function_rows: &IndexMap<FunctionRowKey, FunctionRowState>,
    equality_forest: &EqualityForest,
) -> Result<(DepId, Vec<DepId>), CausalSliceError> {
    let mut syntax_dependencies = Vec::new();
    let mut keys = lookup
        .keys
        .iter()
        .zip(&lookup.input_sorts)
        .map(|(key, sort)| {
            let endpoint = ground_arg_at(egraph, key, sort, bindings, witnesses, Some(snapshot))?;
            match key {
                AtomArg::Lit(_) => {}
                AtomArg::Var(_, variable) => {
                    let binding = bindings.get(variable).ok_or_else(|| {
                        CausalSliceError::Invariant(format!(
                            "mutable lookup grounding omitted source variable `{variable}`"
                        ))
                    })?;
                    syntax_dependencies.push(witnesses.availability(binding.syntax));
                }
                AtomArg::Global { name, sort } => {
                    syntax_dependencies
                        .push(witnesses.availability(witnesses.global_witness(name, sort)?));
                }
                AtomArg::App { .. } => {
                    syntax_dependencies.push(endpoint_availability_at(
                        &endpoint,
                        witnesses,
                        &lookup.span,
                        Some(snapshot),
                    )?);
                }
            }
            Ok(endpoint)
        })
        .collect::<Result<Vec<_>, CausalSliceError>>()?;
    for endpoint in &mut keys {
        let canonical = equality_forest.canonical_endpoint(endpoint);
        if canonical != *endpoint {
            return Err(CausalSliceError::Unsupported {
                location: lookup.span.to_string(),
                reason: format!(
                    "an equality-rekeyed key lookup of mutable function `{}`; the unchanged strict proof extractor rejects the corresponding non-reflexive function fact",
                    lookup.function
                ),
            });
        }
    }
    let expected_output = ground_arg_at(
        egraph,
        &lookup.output,
        &lookup.output_sort,
        bindings,
        witnesses,
        Some(snapshot),
    )?;
    match &lookup.output {
        AtomArg::Lit(_) => {}
        AtomArg::Var(_, variable) => {
            let binding = bindings.get(variable).ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "mutable lookup grounding omitted source variable `{variable}`"
                ))
            })?;
            syntax_dependencies.push(witnesses.availability(binding.syntax));
        }
        AtomArg::Global { name, sort } => {
            syntax_dependencies.push(witnesses.availability(witnesses.global_witness(name, sort)?));
        }
        AtomArg::App { .. } => {
            syntax_dependencies.push(endpoint_availability_at(
                &expected_output,
                witnesses,
                &lookup.span,
                Some(snapshot),
            )?);
        }
    }
    let canonical_output = equality_forest.canonical_endpoint(&expected_output);
    if canonical_output != expected_output {
        return Err(CausalSliceError::Unsupported {
            location: lookup.span.to_string(),
            reason: format!(
                "an equality-rekeyed output lookup of mutable function `{}`; the unchanged strict proof extractor rejects the corresponding non-reflexive function fact",
                lookup.function
            ),
        });
    }
    let key = FunctionRowKey {
        function: lookup.function.clone(),
        keys,
    };
    let state = function_rows.get(&key).ok_or_else(|| {
        CausalSliceError::Unsupported {
            location: lookup.span.to_string(),
            reason: format!(
                "mutable function row `{}` used by a native match without source or commit-time provenance",
                lookup.function
            ),
        }
    })?;
    if let Some(error) = &state.deferred_error {
        return Err(error.clone().into_error());
    }
    syntax_dependencies.push(state.dependency);
    if state.output != expected_output {
        if state.output.sort != expected_output.sort {
            return Err(CausalSliceError::Invariant(format!(
                "mutable function `{}` row output changed runtime sort",
                lookup.function
            )));
        }
        let explanation = equality_forest
            .explain(&state.output, &expected_output)
            .ok_or_else(|| CausalSliceError::Invariant(format!(
                "native lookup of mutable function `{}` captured output {expected_output:?}, but the current causal sidecar contains {:?}",
                lookup.function, state.output
            )))?;
        syntax_dependencies.extend(explanation);
    }
    Ok((state.dependency, syntax_dependencies))
}

fn poisoned_function_row(
    output: TypedEndpoint,
    location: String,
    reason: String,
) -> FunctionRowState {
    FunctionRowState {
        output,
        dependency: DepArena::EMPTY,
        deferred_error: Some(DeferredUnsupported { location, reason }),
    }
}

struct RekeyFunctionRowInput<'a> {
    previous_key: &'a FunctionRowKey,
    previous_output: &'a TypedEndpoint,
    incoming_key: &'a FunctionRowKey,
    incoming_output: &'a TypedEndpoint,
    equality_forest: &'a EqualityForest,
    location: &'a str,
}

fn rekey_function_row_dependency(
    input: RekeyFunctionRowInput<'_>,
    previous_dependency: DepId,
    dependencies: &mut DepArena,
) -> Result<DepId, DeferredUnsupported> {
    let RekeyFunctionRowInput {
        previous_key,
        previous_output,
        incoming_key,
        incoming_output,
        equality_forest,
        location,
    } = input;
    if previous_key.function != incoming_key.function
        || previous_key.keys.len() != incoming_key.keys.len()
        || previous_output.sort != incoming_output.sort
    {
        return Err(DeferredUnsupported {
            location: location.to_owned(),
            reason: "a mutable function rebuild changed its logical schema".to_owned(),
        });
    }
    let mut support = previous_dependency;
    for (previous, incoming) in previous_key
        .keys
        .iter()
        .zip(&incoming_key.keys)
        .chain(std::iter::once((previous_output, incoming_output)))
    {
        if previous == incoming {
            continue;
        }
        if previous.sort != incoming.sort {
            return Err(DeferredUnsupported {
                location: location.to_owned(),
                reason: "a mutable function rebuild changed a cell's runtime sort".to_owned(),
            });
        }
        let Some(explanation) = equality_forest.explain(previous, incoming) else {
            return Err(DeferredUnsupported {
                location: location.to_owned(),
                reason: format!(
                    "mutable function `{}` rekeyed a `{}` cell without a captured successful-union path",
                    previous_key.function, previous.sort
                ),
            });
        };
        for dependency in explanation {
            support =
                dependencies
                    .and(support, dependency)
                    .map_err(|error| DeferredUnsupported {
                        location: location.to_owned(),
                        reason: error.to_string(),
                    })?;
        }
    }
    Ok(support)
}

fn apply_wave_mutation_receipts(
    wave: usize,
    receipts: &[TableMutationReceipt],
    trace_functions: &IndexMap<TableId, TraceFunctionMeta>,
    origin_dependencies: &[Option<DepId>],
    function_rows: &mut IndexMap<FunctionRowKey, FunctionRowState>,
    equality_forest: &EqualityForest,
    dependencies: &mut DepArena,
) -> Result<(), CausalSliceError> {
    for receipt in receipts {
        match &receipt.cause {
            TableMutationCause::Rule {
                origin,
                instruction,
            } => {
                let location =
                    format!("traced wave {wave} rule mutation instruction {instruction}");
                let merge = trace_functions
                    .get(&receipt.table)
                    .and_then(|meta| meta.mutable_merge)
                    .ok_or_else(|| {
                        CausalSliceError::Invariant(format!(
                            "{location} referenced a mutation table without a modeled merge"
                        ))
                    })?;
                let (incoming_key, incoming_output) = logical_function_row(
                    receipt.table,
                    &receipt.incoming,
                    trace_functions,
                    &location,
                )?;
                let (committed_key, committed_output) = logical_function_row(
                    receipt.table,
                    &receipt.committed,
                    trace_functions,
                    &location,
                )?;
                if committed_key != incoming_key {
                    return Err(CausalSliceError::Invariant(format!(
                        "{location} changed the logical key while applying its merge"
                    )));
                }
                if matches!(
                    merge,
                    MutableMergeKind::BigRatMin | MutableMergeKind::BigRatMax
                ) {
                    match receipt.outcome {
                        TableMutationOutcome::Inserted => {
                            if receipt.previous.is_some() || committed_output != incoming_output {
                                return Err(CausalSliceError::Invariant(format!(
                                    "{location} reported a fresh custom-merge insertion that did not commit its incoming row"
                                )));
                            }
                            let dependency = origin_dependencies
                                .get(origin.index())
                                .copied()
                                .flatten()
                                .ok_or_else(|| {
                                    CausalSliceError::Invariant(format!(
                                        "{location} inserted custom-merge state without a promoted originating event"
                                    ))
                                })?;
                            function_rows.insert(
                                incoming_key,
                                FunctionRowState {
                                    output: incoming_output,
                                    dependency,
                                    deferred_error: None,
                                },
                            );
                        }
                        TableMutationOutcome::NoOp => {
                            let previous = receipt
                                .previous
                                .as_deref()
                                .map(|row| {
                                    logical_function_row(
                                        receipt.table,
                                        row,
                                        trace_functions,
                                        &location,
                                    )
                                })
                                .transpose()?
                                .ok_or_else(|| {
                                    CausalSliceError::Invariant(format!(
                                        "{location} reported a custom-merge no-op without a previous row"
                                    ))
                                })?;
                            if previous != (committed_key.clone(), committed_output.clone()) {
                                return Err(CausalSliceError::Invariant(format!(
                                    "{location} reported a custom-merge no-op that did not preserve the previous row"
                                )));
                            }
                            if let Some(state) = function_rows.get(&committed_key) {
                                if state.output != committed_output {
                                    return Err(CausalSliceError::Invariant(format!(
                                        "{location} selected a no-op output different from the causal sidecar"
                                    )));
                                }
                            } else {
                                function_rows.insert(
                                    committed_key,
                                    poisoned_function_row(
                                        committed_output,
                                        location,
                                        "a custom-merge no-op selected a prior row without source or commit-time provenance"
                                            .to_owned(),
                                    ),
                                );
                            }
                        }
                        TableMutationOutcome::Replaced => {
                            let previous = receipt
                                .previous
                                .as_deref()
                                .map(|row| {
                                    logical_function_row(
                                        receipt.table,
                                        row,
                                        trace_functions,
                                        &location,
                                    )
                                })
                                .transpose()?
                                .ok_or_else(|| {
                                    CausalSliceError::Invariant(format!(
                                        "{location} reported a custom-merge replacement without a previous row"
                                    ))
                                })?;
                            if previous.0 != committed_key {
                                return Err(CausalSliceError::Invariant(format!(
                                    "{location} replaced custom-merge state at a different logical key"
                                )));
                            }
                            function_rows.insert(
                                committed_key,
                                poisoned_function_row(
                                    committed_output,
                                    location,
                                    "a custom BigRat min/max merge selected between an existing row and an incoming proposal; selector provenance is not yet modeled"
                                        .to_owned(),
                                ),
                            );
                        }
                    }
                    continue;
                }
                if committed_output != incoming_output {
                    return Err(CausalSliceError::Invariant(format!(
                        "{location} did not select its incoming logical row under an incoming-preserving causal merge"
                    )));
                }
                match receipt.outcome {
                    TableMutationOutcome::Inserted | TableMutationOutcome::Replaced => {
                        let dependency = origin_dependencies
                            .get(origin.index())
                            .copied()
                            .flatten()
                            .ok_or_else(|| {
                                CausalSliceError::Invariant(format!(
                                    "{location} changed mutable state without a promoted originating event"
                                ))
                            })?;
                        function_rows.insert(
                            incoming_key,
                            FunctionRowState {
                                output: incoming_output,
                                dependency,
                                deferred_error: None,
                            },
                        );
                    }
                    TableMutationOutcome::NoOp => {
                        if let Some(state) = function_rows.get(&incoming_key) {
                            if state.output != committed_output {
                                return Err(CausalSliceError::Invariant(format!(
                                    "{location} selected a no-op output different from the causal sidecar"
                                )));
                            }
                        } else {
                            function_rows.insert(
                                incoming_key,
                                poisoned_function_row(
                                    committed_output,
                                    location,
                                    "a causal set no-op selected a prior row without source or commit-time provenance"
                                        .to_owned(),
                                ),
                            );
                        }
                    }
                }
            }
            TableMutationCause::Rebuild { previous } => {
                let location = format!("traced wave {wave} mutable function rebuild");
                let merge = trace_functions
                    .get(&receipt.table)
                    .and_then(|meta| meta.mutable_merge)
                    .ok_or_else(|| {
                        CausalSliceError::Invariant(format!(
                            "{location} referenced a mutation table without a modeled merge"
                        ))
                    })?;
                let (previous_key, previous_output) =
                    logical_function_row(receipt.table, previous, trace_functions, &location)?;
                let (incoming_key, incoming_output) = logical_function_row(
                    receipt.table,
                    &receipt.incoming,
                    trace_functions,
                    &location,
                )?;
                let (committed_key, committed_output) = logical_function_row(
                    receipt.table,
                    &receipt.committed,
                    trace_functions,
                    &location,
                )?;
                if matches!(
                    merge,
                    MutableMergeKind::BigRatMin | MutableMergeKind::BigRatMax
                ) {
                    if committed_key != incoming_key {
                        return Err(CausalSliceError::Invariant(format!(
                            "{location} changed the logical key while rebuilding custom-merge state"
                        )));
                    }
                    function_rows.shift_remove(&previous_key);
                    if incoming_key != previous_key {
                        function_rows.shift_remove(&incoming_key);
                    }
                    function_rows.insert(
                        committed_key,
                        poisoned_function_row(
                            committed_output,
                            location,
                            "a custom BigRat min/max row passed through equality rebuild; selector and rekey provenance are not yet modeled"
                                .to_owned(),
                        ),
                    );
                    continue;
                }
                let source_state = function_rows.shift_remove(&previous_key);
                let target_state = if incoming_key == previous_key {
                    None
                } else {
                    function_rows.get(&incoming_key).cloned()
                };
                let previous_at_target = receipt
                    .previous
                    .as_deref()
                    .map(|row| logical_function_row(receipt.table, row, trace_functions, &location))
                    .transpose()?;

                match receipt.outcome {
                    TableMutationOutcome::NoOp => {
                        let Some((target_key, target_output)) = previous_at_target else {
                            return Err(CausalSliceError::Invariant(format!(
                                "{location} reported NoOp without a previous target row"
                            )));
                        };
                        if (committed_key.clone(), committed_output.clone())
                            != (target_key, target_output)
                        {
                            return Err(CausalSliceError::Invariant(format!(
                                "{location} no-op did not preserve its previous target row"
                            )));
                        }
                        if let Some(target) = target_state {
                            if target.output != committed_output {
                                return Err(CausalSliceError::Invariant(format!(
                                    "{location} target output differs from the causal sidecar"
                                )));
                            }
                        } else {
                            function_rows.insert(
                                committed_key,
                                poisoned_function_row(
                                    committed_output,
                                    location,
                                    "a mutable function rekey collision selected an untracked prior target row"
                                        .to_owned(),
                                ),
                            );
                        }
                    }
                    TableMutationOutcome::Inserted => {
                        if previous_at_target.is_some() {
                            return Err(CausalSliceError::Invariant(format!(
                                "{location} reported Inserted with a previous target row"
                            )));
                        }
                        if committed_key != incoming_key || committed_output != incoming_output {
                            return Err(CausalSliceError::Invariant(format!(
                                "{location} inserted a logical row different from the rebuilt proposal"
                            )));
                        }
                        let state = match source_state {
                            Some(source) if source.output == previous_output => {
                                match rekey_function_row_dependency(
                                    RekeyFunctionRowInput {
                                        previous_key: &previous_key,
                                        previous_output: &previous_output,
                                        incoming_key: &incoming_key,
                                        incoming_output: &incoming_output,
                                        equality_forest,
                                        location: &location,
                                    },
                                    source.dependency,
                                    dependencies,
                                ) {
                                    Ok(dependency) => {
                                        let deferred_error = source.deferred_error.or_else(|| {
                                            (previous_key != incoming_key
                                                || previous_output != incoming_output)
                                                .then(|| DeferredUnsupported {
                                                    location: location.clone(),
                                                    reason: "a mutable function row was rekeyed or its output was canonicalized; the unchanged strict proof extractor rejects the resulting replay fact"
                                                        .to_owned(),
                                                })
                                        });
                                        FunctionRowState {
                                            output: incoming_output,
                                            dependency,
                                            deferred_error,
                                        }
                                    }
                                    Err(error) => poisoned_function_row(
                                        incoming_output,
                                        error.location,
                                        error.reason,
                                    ),
                                }
                            }
                            Some(source) => poisoned_function_row(
                                incoming_output,
                                location,
                                format!(
                                    "mutable function rebuild source output {:?} differs from its recorded previous row {previous_output:?}",
                                    source.output
                                ),
                            ),
                            None => poisoned_function_row(
                                incoming_output,
                                location,
                                "a mutable function rebuild source row lacked causal provenance"
                                    .to_owned(),
                            ),
                        };
                        function_rows.insert(incoming_key, state);
                    }
                    TableMutationOutcome::Replaced => {
                        let differing_output = previous_at_target
                            .as_ref()
                            .is_none_or(|(_, output)| output != &incoming_output);
                        let reason = if differing_output {
                            "a mutable function rekey collision selected between differing outputs; sequential replay does not preserve rebuild proposal ordering"
                        } else {
                            "a mutable function rebuild replacement did not match incoming-preserving no-op semantics"
                        };
                        function_rows.insert(
                            committed_key,
                            poisoned_function_row(committed_output, location, reason.to_owned()),
                        );
                    }
                }
            }
            TableMutationCause::Unattributed => {
                let location = format!("traced wave {wave} unattributed mutable mutation");
                let (committed_key, committed_output) = logical_function_row(
                    receipt.table,
                    &receipt.committed,
                    trace_functions,
                    &location,
                )?;
                if receipt.outcome != TableMutationOutcome::NoOp
                    || !function_rows.contains_key(&committed_key)
                {
                    function_rows.insert(
                        committed_key,
                        poisoned_function_row(
                            committed_output,
                            location,
                            "an unattributed mutable-state change (for example container refresh)"
                                .to_owned(),
                        ),
                    );
                }
            }
        }
    }
    Ok(())
}

fn match_union_receipts(
    rule_name: &str,
    expected: &[(TypedEndpoint, TypedEndpoint)],
    receipts: &[OrderedUnionReceipt<'_>],
) -> Result<Vec<AppliedEquality>, CausalSliceError> {
    if expected.len() != receipts.len() {
        return Err(CausalSliceError::Invariant(format!(
            "rule `{rule_name}` modeled {} union action(s) but native commit reported {} receipt(s)",
            expected.len(),
            receipts.len()
        )));
    }
    let mut unmatched = receipts.to_vec();
    let mut applied = Vec::new();
    for (left, right) in expected {
        let Some(index) = unmatched.iter().position(|receipt| {
            receipt.receipt.lhs == left.value && receipt.receipt.rhs == right.value
        }) else {
            return Err(CausalSliceError::Invariant(format!(
                "rule `{rule_name}` expected union endpoints ({left:?}, {right:?}) but native commit reported {unmatched:?}"
            )));
        };
        let ordered_receipt = unmatched.swap_remove(index);
        let receipt = ordered_receipt.receipt;
        match receipt.outcome {
            UnionOutcome::Applied { parent, child } => {
                if parent == child {
                    return Err(CausalSliceError::Invariant(format!(
                        "rule `{rule_name}` reported a successful union with identical committed endpoints"
                    )));
                }
                applied.push(AppliedEquality {
                    left: left.clone(),
                    right: right.clone(),
                    parent,
                    child,
                    commit_ordinal: ordered_receipt.commit_ordinal,
                });
            }
            UnionOutcome::Redundant { .. } => {}
        }
    }
    debug_assert!(unmatched.is_empty());
    Ok(applied)
}

fn classify_prefix_union_receipts(
    rule_name: &str,
    expected: &[EqualityTemplate],
    receipts: &[OrderedUnionReceipt<'_>],
) -> Result<Vec<AppliedEquality>, CausalSliceError> {
    if expected.len() != receipts.len() {
        return Err(CausalSliceError::Invariant(format!(
            "rule `{rule_name}` modeled {} union action(s) but native commit reported {} receipt(s)",
            expected.len(),
            receipts.len()
        )));
    }
    let mut applied = Vec::new();
    for (equality, ordered_receipt) in expected.iter().zip(receipts) {
        let receipt = ordered_receipt.receipt;
        if let UnionOutcome::Applied { parent, child } = receipt.outcome {
            if parent == child {
                return Err(CausalSliceError::Invariant(format!(
                    "rule `{rule_name}` reported a successful union with identical committed endpoints"
                )));
            }
            applied.push(AppliedEquality {
                left: TypedEndpoint {
                    sort: equality.sort.clone(),
                    value: receipt.lhs,
                },
                right: TypedEndpoint {
                    sort: equality.sort.clone(),
                    value: receipt.rhs,
                },
                parent,
                child,
                commit_ordinal: ordered_receipt.commit_ordinal,
            });
        }
    }
    Ok(applied)
}

fn count_prefix_applied_unions<'a>(
    rule_name: &str,
    expected: &[EqualityTemplate],
    receipts: impl ExactSizeIterator<Item = &'a UnionReceipt>,
) -> Result<usize, CausalSliceError> {
    if expected.len() != receipts.len() {
        return Err(CausalSliceError::Invariant(format!(
            "rule `{rule_name}` modeled {} union action(s) but native commit reported {} receipt(s)",
            expected.len(),
            receipts.len()
        )));
    }
    let mut applied = 0usize;
    for (_equality, receipt) in expected.iter().zip(receipts) {
        if let UnionOutcome::Applied { parent, child } = receipt.outcome {
            if parent == child {
                return Err(CausalSliceError::Invariant(format!(
                    "rule `{rule_name}` reported a successful union with identical committed endpoints"
                )));
            }
            applied += 1;
        }
    }
    Ok(applied)
}

#[derive(Default)]
struct FireApplicationEffects {
    observed_rows: Vec<RowKey>,
    new_rows: Vec<RowKey>,
    new_witnesses: Vec<WitnessId>,
    read_dependencies: Vec<DepId>,
    deferred_error: Option<DeferredUnsupported>,
}

impl FireApplicationEffects {
    fn absorb(&mut self, mut other: Self) {
        self.observed_rows.append(&mut other.observed_rows);
        self.new_rows.append(&mut other.new_rows);
        self.new_witnesses.append(&mut other.new_witnesses);
        self.read_dependencies.append(&mut other.read_dependencies);
        if self.deferred_error.is_none() {
            self.deferred_error = other.deferred_error;
        }
    }

    fn normalize(&mut self) {
        self.new_rows.sort_by_key(|row| {
            self.observed_rows
                .iter()
                .position(|observed| observed == row)
                .unwrap_or(usize::MAX)
        });
        self.new_rows.dedup();
        self.new_witnesses.sort_unstable_by_key(|id| id.index());
        self.new_witnesses.dedup();
    }
}

enum QueryPrimitiveOutcome {
    Filtered,
    Matched {
        availability: DepId,
        deferred: Option<DeferredUnsupported>,
    },
}

fn elaborate_auxiliary_scalar_application(
    egraph: &EGraph,
    rule_name: &str,
    phase: &str,
    kind: QueryAuxiliaryPrimitive,
    application: &PrimitiveApplication,
    witnesses: &mut WitnessArena,
) -> Result<(), CausalSliceError> {
    match kind {
        QueryAuxiliaryPrimitive::BigInt => {
            let [value] = application.args.as_slice() else {
                return Err(CausalSliceError::Invariant(format!(
                    "rule `{rule_name}` traced a malformed `bigint` {phase} constructor"
                )));
            };
            let child = scalar_witness(
                egraph,
                "i64",
                *value,
                witnesses,
                &format!("{phase} `bigint` argument"),
            )?;
            witnesses.intern_app(
                "BigInt",
                "bigint",
                vec![child],
                application.result,
                DepArena::EMPTY,
                true,
            )?;
        }
        QueryAuxiliaryPrimitive::BigRat => {
            let [numerator, denominator] = application.args.as_slice() else {
                return Err(CausalSliceError::Invariant(format!(
                    "rule `{rule_name}` traced a malformed `bigrat` {phase} constructor"
                )));
            };
            let children = [numerator, denominator]
                .into_iter()
                .map(|value| {
                    witnesses.by_endpoint("BigInt", *value).ok_or_else(|| {
                        CausalSliceError::Invariant(format!(
                            "rule `{rule_name}` {phase} `bigrat` argument lacked syntax"
                        ))
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            witnesses.intern_app(
                "BigRat",
                "bigrat",
                children,
                application.result,
                DepArena::EMPTY,
                true,
            )?;
        }
    }
    Ok(())
}

struct QueryPrimitiveInput<'a> {
    egraph: &'a EGraph,
    rule_name: &'a str,
    model: &'a RuleModel,
    metadata: &'a [RulePrimitiveMeta],
    applications: Vec<&'a PrimitiveApplication>,
    bindings: &'a mut IndexMap<String, BindingWitness>,
    prestate_witnesses: &'a IndexMap<TypedEndpoint, WitnessId>,
}

fn elaborate_query_primitive(
    input: QueryPrimitiveInput<'_>,
    witnesses: &mut WitnessArena,
) -> Result<QueryPrimitiveOutcome, CausalSliceError> {
    let QueryPrimitiveInput {
        egraph,
        rule_name,
        model,
        metadata,
        applications,
        bindings,
        prestate_witnesses,
    } = input;
    if applications.len() > metadata.len() {
        return Err(CausalSliceError::Invariant(format!(
            "rule `{rule_name}` query primitive tape has an invalid logical boundary"
        )));
    }
    let mut expected_logical = model.body_primitives.iter();
    let mut availability = DepArena::EMPTY;
    let mut deferred = None;
    for (index, primitive) in metadata.iter().enumerate() {
        let Some(application) = applications.get(index).copied() else {
            return Ok(QueryPrimitiveOutcome::Filtered);
        };
        if application.function != primitive.function {
            return Err(CausalSliceError::Invariant(format!(
                "rule `{rule_name}` query primitive trace diverged from its resolved specialization"
            )));
        }
        if let Some(kind) = primitive.query_auxiliary {
            elaborate_auxiliary_scalar_application(
                egraph,
                rule_name,
                "query",
                kind,
                application,
                witnesses,
            )?;
            continue;
        }
        if !primitive.logical_query {
            return Err(CausalSliceError::Invariant(format!(
                "rule `{rule_name}` query primitive tape contains an unclassified primitive"
            )));
        }
        let expected = expected_logical.next().ok_or_else(|| {
            CausalSliceError::Invariant(format!(
                "rule `{rule_name}` traced an unmodeled logical query primitive"
            ))
        })?;
        let Some((next_availability, next_deferred)) = elaborate_logical_query_application(
            egraph,
            rule_name,
            expected,
            application,
            bindings,
            prestate_witnesses,
            witnesses,
        )?
        else {
            return Ok(QueryPrimitiveOutcome::Filtered);
        };
        if availability == DepArena::EMPTY {
            availability = next_availability;
        } else if next_availability != DepArena::EMPTY && next_availability != availability {
            return Err(CausalSliceError::Unsupported {
                location: model.span.to_string(),
                reason: format!(
                    "rule `{rule_name}` has multiple query-result availability causes that require dependency conjunction"
                ),
            });
        }
        if deferred.is_none() {
            deferred = next_deferred;
        }
    }
    if expected_logical.next().is_some() {
        return Err(CausalSliceError::Invariant(format!(
            "rule `{rule_name}` lost modeled logical query metadata"
        )));
    }
    Ok(QueryPrimitiveOutcome::Matched {
        availability,
        deferred,
    })
}

fn elaborate_logical_query_application(
    egraph: &EGraph,
    rule_name: &str,
    expected: &QueryPrimitiveTemplate,
    application: &PrimitiveApplication,
    bindings: &mut IndexMap<String, BindingWitness>,
    prestate_witnesses: &IndexMap<TypedEndpoint, WitnessId>,
    witnesses: &mut WitnessArena,
) -> Result<Option<(DepId, Option<DeferredUnsupported>)>, CausalSliceError> {
    let AtomArg::App {
        function,
        args,
        input_sorts,
        output_sort,
        ..
    } = &expected.application
    else {
        return Err(CausalSliceError::Invariant(format!(
            "rule `{rule_name}` query primitive model stopped being an application"
        )));
    };
    if application.function
        != expected
            .capability
            .specialization
            .external_id(crate::Context::Pure)
        || application.args.len() != args.len()
    {
        return Err(CausalSliceError::Invariant(format!(
            "rule `{rule_name}` query primitive model diverged from admitted `{function}`"
        )));
    }
    let mut children = Vec::with_capacity(args.len());
    for ((arg, sort), captured) in args.iter().zip(input_sorts).zip(&application.args) {
        intern_atom_arg_literals(egraph, arg, sort, witnesses)?;
        let (endpoint, syntax) =
            ground_arg_with_witness_at(egraph, arg, sort, bindings, witnesses, None)?;
        if endpoint.value != *captured {
            return Err(CausalSliceError::Invariant(format!(
                "rule `{rule_name}` query primitive instruction {} captured arguments that diverge from its grounding",
                application.instruction
            )));
        }
        children.push(syntax);
    }

    let Some(expected_output) = expected.output.as_ref() else {
        let syntax = witnesses.intern_app(
            output_sort,
            function,
            children,
            application.result,
            DepArena::EMPTY,
            true,
        )?;
        witnesses.prefer_endpoint_witness(output_sort, application.result, syntax)?;
        return Ok(Some((DepArena::EMPTY, None)));
    };

    if let AtomArg::Var(_, output_variable) = expected_output
        && !bindings.contains_key(output_variable)
    {
        let result_endpoint = TypedEndpoint {
            sort: output_sort.clone(),
            value: application.result,
        };
        let runtime_sort = egraph.get_sort_by_name(output_sort).ok_or_else(|| {
            CausalSliceError::Invariant(format!("runtime sort `{output_sort}` disappeared"))
        })?;
        let (syntax, availability, deferred) = if runtime_sort.is_container_sort() {
            let availability = prestate_witnesses
                .get(&result_endpoint)
                .map(|witness| witnesses.availability(*witness))
                .unwrap_or(DepArena::EMPTY);
            let syntax = witnesses.intern_app(
                output_sort,
                function,
                children,
                application.result,
                availability,
                true,
            )?;
            (
                syntax,
                availability,
                Some(DeferredUnsupported {
                    location: expected.span.to_string(),
                    reason: format!(
                        "container-valued primitive `{function}` result without a match-time replay witness and temporal support in rule `{rule_name}`"
                    ),
                }),
            )
        } else if runtime_sort.is_eq_sort() {
            let availability = prestate_witnesses
                .get(&result_endpoint)
                .map(|witness| witnesses.availability(*witness))
                .unwrap_or(DepArena::EMPTY);
            let syntax = witnesses.intern_app(
                output_sort,
                function,
                children,
                application.result,
                availability,
                true,
            )?;
            let deferred = (!prestate_witnesses.contains_key(&result_endpoint)).then(|| {
                DeferredUnsupported {
                    location: expected.span.to_string(),
                    reason: format!(
                        "equality-sort primitive `{function}` result without a preexisting replay witness in rule `{rule_name}`"
                    ),
                }
            });
            (syntax, availability, deferred)
        } else {
            (
                scalar_witness(
                    egraph,
                    output_sort,
                    application.result,
                    witnesses,
                    &format!("query primitive `{function}` result"),
                )?,
                DepArena::EMPTY,
                None,
            )
        };
        bindings.insert(
            output_variable.clone(),
            BindingWitness {
                syntax,
                endpoint: application.result,
            },
        );
        return Ok(Some((availability, deferred)));
    }

    let output = ground_arg(egraph, expected_output, output_sort, bindings, witnesses)?;
    if output.value != application.result {
        return Ok(None);
    }
    let runtime_sort = egraph.get_sort_by_name(output_sort).ok_or_else(|| {
        CausalSliceError::Invariant(format!("runtime sort `{output_sort}` disappeared"))
    })?;
    let availability = if runtime_sort.is_eq_sort() || runtime_sort.is_container_sort() {
        let output_witness = witnesses
            .by_endpoint(output_sort, output.value)
            .ok_or_else(|| CausalSliceError::Unsupported {
                location: expected.span.to_string(),
                reason: format!(
                    "query filter output of sort `{output_sort}` lacked a pre-state replay witness in rule `{rule_name}`"
                ),
            })?;
        witnesses.availability(output_witness)
    } else {
        DepArena::EMPTY
    };
    Ok(Some((availability, None)))
}

struct FirePrimitiveSequenceInput<'a> {
    egraph: &'a EGraph,
    rule_name: &'a str,
    model: &'a RuleModel,
    metadata: &'a ResolvedRulePrimitives,
    applications: Vec<&'a PrimitiveApplication>,
    bindings: &'a mut IndexMap<String, BindingWitness>,
    prestate_witnesses: &'a IndexMap<TypedEndpoint, WitnessId>,
}

struct FireQuerySequenceResult {
    availability: DepId,
    deferred: Option<DeferredUnsupported>,
    head_application_start: usize,
}

fn elaborate_fire_query_sequence(
    input: FirePrimitiveSequenceInput<'_>,
    witnesses: &mut WitnessArena,
) -> Result<Option<FireQuerySequenceResult>, CausalSliceError> {
    let FirePrimitiveSequenceInput {
        egraph,
        rule_name,
        model,
        metadata,
        applications,
        bindings,
        prestate_witnesses,
    } = input;
    let query_count = applications.len().min(metadata.body.len());
    let (query_applications, head_applications) = applications.split_at(query_count);
    let query = elaborate_query_primitive(
        QueryPrimitiveInput {
            egraph,
            rule_name,
            model,
            metadata: &metadata.body,
            applications: query_applications.to_vec(),
            bindings,
            prestate_witnesses,
        },
        witnesses,
    )?;
    let QueryPrimitiveOutcome::Matched {
        availability,
        deferred,
    } = query
    else {
        return Ok(None);
    };
    // A compiler assertion or fallible call can remove a lane before its
    // first source-head primitive. The caller still checks that no earlier
    // table/union/mutation effect escaped before treating it as filtered.
    if !metadata.head.is_empty() && head_applications.is_empty() {
        return Ok(None);
    }
    ensure_rule_bindings_complete(rule_name, model, bindings)?;
    Ok(Some(FireQuerySequenceResult {
        availability,
        deferred,
        head_application_start: query_count,
    }))
}

fn elaborate_fire_primitive_sequence(
    input: FirePrimitiveSequenceInput<'_>,
    witnesses: &mut WitnessArena,
) -> Result<Option<(DepId, Option<DeferredUnsupported>)>, CausalSliceError> {
    let FirePrimitiveSequenceInput {
        egraph,
        rule_name,
        model,
        metadata,
        applications,
        bindings,
        prestate_witnesses,
    } = input;
    // Native action instructions execute query validators before the source
    // head. A filtered lane therefore records a strict prefix of the body
    // tape and no head calls; a successful lane records the complete body
    // tape followed by the head tape.
    let query_count = applications.len().min(metadata.body.len());
    let (query_applications, head_applications) = applications.split_at(query_count);
    let query = elaborate_query_primitive(
        QueryPrimitiveInput {
            egraph,
            rule_name,
            model,
            metadata: &metadata.body,
            applications: query_applications.to_vec(),
            bindings,
            prestate_witnesses,
        },
        witnesses,
    )?;
    let QueryPrimitiveOutcome::Matched {
        availability: query_availability,
        deferred: query_error,
    } = query
    else {
        return Ok(None);
    };
    // A compiler-emitted assertion can reject a lane after every query
    // primitive succeeds but before the first head primitive runs. The
    // caller verifies that such a lane produced no table, union, or mutable
    // effects before accepting it as filtered. A nonempty strict prefix of
    // the head tape remains an invariant violation below.
    if !metadata.head.is_empty() && head_applications.is_empty() {
        return Ok(None);
    }
    ensure_rule_bindings_complete(rule_name, model, bindings)?;
    let (head_availability, head_error) = elaborate_fire_primitives(
        FirePrimitiveInput {
            egraph,
            rule_name,
            model,
            metadata: &metadata.head,
            applications: head_applications.to_vec(),
            bindings,
            prestate_witnesses,
        },
        witnesses,
    )?;
    let availability = if query_availability == DepArena::EMPTY {
        head_availability
    } else {
        debug_assert_eq!(head_availability, DepArena::EMPTY);
        query_availability
    };
    Ok(Some((availability, query_error.or(head_error))))
}

struct FirePrimitiveInput<'a> {
    egraph: &'a EGraph,
    rule_name: &'a str,
    model: &'a RuleModel,
    metadata: &'a [RulePrimitiveMeta],
    applications: Vec<&'a PrimitiveApplication>,
    bindings: &'a IndexMap<String, BindingWitness>,
    prestate_witnesses: &'a IndexMap<TypedEndpoint, WitnessId>,
}

fn elaborate_fire_primitives(
    input: FirePrimitiveInput<'_>,
    witnesses: &mut WitnessArena,
) -> Result<(DepId, Option<DeferredUnsupported>), CausalSliceError> {
    let FirePrimitiveInput {
        egraph,
        rule_name,
        model,
        metadata,
        applications,
        bindings,
        prestate_witnesses,
    } = input;
    if metadata.len() != applications.len() {
        return Err(CausalSliceError::Invariant(format!(
            "rule `{rule_name}` captured {} head primitive applications for {} resolved calls",
            applications.len(),
            metadata.len()
        )));
    }
    let mut availability = DepArena::EMPTY;
    let mut deferred = None;
    let mut expected_head = model.head_primitives.iter();
    for (application, primitive) in applications.into_iter().zip(metadata) {
        if application.function != primitive.function {
            return Err(CausalSliceError::Invariant(format!(
                "rule `{rule_name}` primitive instruction {} used an unexpected runtime specialization",
                application.instruction
            )));
        }
        if let Some(kind) = primitive.query_auxiliary {
            elaborate_auxiliary_scalar_application(
                egraph,
                rule_name,
                "head",
                kind,
                application,
                witnesses,
            )?;
            continue;
        }
        let expected = expected_head.next().ok_or_else(|| {
            CausalSliceError::Invariant(format!(
                "rule `{rule_name}` traced an unmodeled non-auxiliary head primitive"
            ))
        })?;
        let AtomArg::App {
            function,
            args,
            input_sorts,
            output_sort,
            ..
        } = expected
        else {
            return Err(CausalSliceError::Invariant(format!(
                "rule `{rule_name}` primitive model stopped being an application"
            )));
        };
        if replay_safe_bigrat_primitive_arity(function) != Some(input_sorts.len())
            || input_sorts.iter().any(|sort| sort != "BigRat")
            || output_sort != "BigRat"
            || application.args.len() != args.len()
        {
            return Err(CausalSliceError::Invariant(format!(
                "rule `{rule_name}` primitive model diverged from admitted BigRat `{function}`"
            )));
        }
        let mut children = Vec::with_capacity(args.len());
        for ((arg, sort), captured) in args.iter().zip(input_sorts).zip(&application.args) {
            let endpoint = ground_arg(egraph, arg, sort, bindings, witnesses)?;
            if endpoint.value != *captured {
                return Err(CausalSliceError::Invariant(format!(
                    "rule `{rule_name}` primitive instruction {} captured arguments that diverge from its grounding",
                    application.instruction
                )));
            }
            children.push(witnesses.by_endpoint(sort, endpoint.value).ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "rule `{rule_name}` primitive argument lacked replay syntax"
                ))
            })?);
        }
        let result_endpoint = TypedEndpoint {
            sort: output_sort.clone(),
            value: application.result,
        };
        let result_availability = if let Some(preexisting) =
            prestate_witnesses.get(&result_endpoint)
        {
            witnesses.availability(*preexisting)
        } else {
            deferred.get_or_insert_with(|| DeferredUnsupported {
                location: model.span.to_string(),
                reason: format!(
                    "BigRat `{function}` result without a preexisting replay witness in rule `{rule_name}`"
                ),
            });
            DepArena::EMPTY
        };
        let witness = witnesses.intern_app(
            output_sort,
            function,
            children,
            application.result,
            result_availability,
            true,
        )?;
        // Subsequent constructor applications in this complete source head
        // must retain the primitive syntax rather than an equivalent literal
        // witness for the same scalar endpoint.
        witnesses.prefer_endpoint_witness(output_sort, application.result, witness)?;
        availability = result_availability;
    }
    if expected_head.next().is_some() {
        return Err(CausalSliceError::Invariant(format!(
            "rule `{rule_name}` did not execute every modeled head primitive"
        )));
    }
    Ok((availability, deferred))
}

#[derive(Clone, Copy)]
enum HeadCallReceipt<'a> {
    Table(&'a TableApplication),
    Primitive(&'a PrimitiveApplication),
}

impl HeadCallReceipt<'_> {
    fn instruction(&self) -> u32 {
        match self {
            Self::Table(application) => application.instruction,
            Self::Primitive(application) => application.instruction,
        }
    }
}

fn ordered_head_call_receipts<'a>(
    rule_name: &str,
    table_applications: &[&'a TableApplication],
    primitive_applications: &[&'a PrimitiveApplication],
) -> Result<Vec<HeadCallReceipt<'a>>, CausalSliceError> {
    let mut receipts = table_applications
        .iter()
        .copied()
        .map(HeadCallReceipt::Table)
        .chain(
            primitive_applications
                .iter()
                .copied()
                .map(HeadCallReceipt::Primitive),
        )
        .collect::<Vec<_>>();
    receipts.sort_by_key(HeadCallReceipt::instruction);
    if let Some(duplicate) = receipts
        .windows(2)
        .find(|pair| pair[0].instruction() == pair[1].instruction())
    {
        return Err(CausalSliceError::Invariant(format!(
            "rule `{rule_name}` captured both table/primitive results for native instruction {}",
            duplicate[0].instruction()
        )));
    }
    Ok(receipts)
}

fn preflight_resolved_head_receipts<'a>(
    rule_name: &str,
    model: &RuleModel,
    core_head: &ResolvedCoreActions,
    table_applications: &[&'a TableApplication],
    primitive_applications: &[&'a PrimitiveApplication],
    trace_functions: &IndexMap<TableId, TraceFunctionMeta>,
) -> Result<Vec<HeadCallReceipt<'a>>, CausalSliceError> {
    let receipts =
        ordered_head_call_receipts(rule_name, table_applications, primitive_applications)?;
    // This must remain a pure preflight: the caller may choose opaque generic
    // elaboration on `Unsupported`, so no abandoned structured-head state may
    // leak into that fallback.
    let mut pending = receipts.iter().copied();
    for action in &core_head.0 {
        let GenericCoreAction::Let(span, output, call, arguments) = action else {
            continue;
        };
        let receipt = pending
            .next()
            .ok_or_else(|| CausalSliceError::Unsupported {
                location: span.to_string(),
                reason: format!(
                    "rule `{rule_name}` stopped before registered head call `{}` completed",
                    call.name()
                ),
            })?;
        match (call, receipt) {
            (ResolvedCall::Func(function), HeadCallReceipt::Table(application)) => {
                if function.is_tuple_output() {
                    return unsupported(
                        span,
                        format!(
                            "tuple-output function `{}` in rule `{rule_name}` head",
                            function.name
                        ),
                    );
                }
                let meta = trace_functions.get(&application.table).ok_or_else(|| {
                    CausalSliceError::Unsupported {
                        location: span.to_string(),
                        reason: format!(
                            "rule `{rule_name}` called unmodeled table {:?}",
                            application.table
                        ),
                    }
                })?;
                if meta.name != function.name
                    || meta.output_sort != function.output().name()
                    || meta.input_sorts.len() != function.input.len()
                    || meta
                        .input_sorts
                        .iter()
                        .zip(&function.input)
                        .any(|(captured, expected)| captured != expected.name())
                    || arguments.len() != function.input.len()
                    || application.args.len() != arguments.len()
                    || output.sort.name() != meta.output_sort
                {
                    return unsupported(
                        span,
                        format!(
                            "rule `{rule_name}` registered head call `{}` ({:?} -> {}) has no exact receipt before native instruction {} for `{}` ({:?} -> {}) with {} arguments",
                            function.name,
                            function
                                .input
                                .iter()
                                .map(|sort| sort.name())
                                .collect::<Vec<_>>(),
                            function.output().name(),
                            application.instruction,
                            meta.name,
                            meta.input_sorts,
                            meta.output_sort,
                            application.args.len(),
                        ),
                    );
                }
            }
            (ResolvedCall::Primitive(primitive), HeadCallReceipt::Primitive(application)) => {
                if primitive.effect() != crate::PrimitiveEffect::Pure
                    || primitive.validator().is_none()
                    || !primitive.is_replay_safe()
                {
                    return unsupported(
                        span,
                        format!(
                            "head primitive `{}` without a Pure proof-validating specialization in rule `{rule_name}`",
                            primitive.name()
                        ),
                    );
                }
                if primitive.external_id(crate::Context::Write) != application.function
                    || primitive.input().len() != arguments.len()
                    || application.args.len() != arguments.len()
                    || output.sort.name() != primitive.output().name()
                {
                    return unsupported(
                        span,
                        format!(
                            "rule `{rule_name}` registered head primitive `{}` has no exact receipt before native instruction {}",
                            primitive.name(),
                            application.instruction
                        ),
                    );
                }
            }
            (ResolvedCall::Values(_), _) => {
                return unsupported(
                    span,
                    format!("tuple-values call in rule `{rule_name}` head"),
                );
            }
            (ResolvedCall::Func(function), HeadCallReceipt::Primitive(application)) => {
                return unsupported(
                    span,
                    format!(
                        "rule `{rule_name}` function `{}` has no exact table receipt before primitive instruction {}",
                        function.name, application.instruction
                    ),
                );
            }
            (ResolvedCall::Primitive(primitive), HeadCallReceipt::Table(application)) => {
                return unsupported(
                    span,
                    format!(
                        "rule `{rule_name}` primitive `{}` has no exact primitive receipt before table instruction {}",
                        primitive.name(),
                        application.instruction
                    ),
                );
            }
        }
    }
    if let Some(receipt) = pending.next() {
        return unsupported(
            &model.span,
            format!(
                "rule `{rule_name}` captured unconsumed native head instruction {}",
                receipt.instruction()
            ),
        );
    }
    Ok(receipts)
}

struct ResolvedHeadInput<'a> {
    egraph: &'a EGraph,
    rule_name: &'a str,
    model: &'a RuleModel,
    core_head: &'a ResolvedCoreActions,
    receipts: Vec<HeadCallReceipt<'a>>,
    bindings: &'a mut IndexMap<String, BindingWitness>,
    trace_functions: &'a IndexMap<TableId, TraceFunctionMeta>,
    prefix_fallback: bool,
    equality_forest: &'a EqualityForest,
}

fn elaborate_resolved_head(
    input: ResolvedHeadInput<'_>,
    witnesses: &mut WitnessArena,
    dependencies: &mut DepArena,
    app_index: &mut WaveAppIndex,
) -> Result<FireApplicationEffects, CausalSliceError> {
    let ResolvedHeadInput {
        egraph,
        rule_name,
        model,
        core_head,
        receipts,
        bindings,
        trace_functions,
        prefix_fallback,
        equality_forest,
    } = input;
    let mut receipts = receipts.into_iter();
    let mut effects = FireApplicationEffects::default();

    for action in &core_head.0 {
        match action {
            GenericCoreAction::Let(span, output, call, arguments) => {
                let receipt = receipts
                    .next()
                    .ok_or_else(|| CausalSliceError::Unsupported {
                        location: span.to_string(),
                        reason: format!(
                            "rule `{rule_name}` stopped before registered head call `{}` completed",
                            call.name()
                        ),
                    })?;
                let binding = match (call, receipt) {
                    (ResolvedCall::Func(function), HeadCallReceipt::Table(application)) => {
                        if function.is_tuple_output() {
                            return unsupported(
                                span,
                                format!(
                                    "tuple-output function `{}` in rule `{rule_name}` head",
                                    function.name
                                ),
                            );
                        }
                        let meta = trace_functions.get(&application.table).ok_or_else(|| {
                            CausalSliceError::Unsupported {
                                location: span.to_string(),
                                reason: format!(
                                    "rule `{rule_name}` called unmodeled table {:?}",
                                    application.table
                                ),
                            }
                        })?;
                        if meta.name != function.name
                            || meta.output_sort != function.output().name()
                            || meta.input_sorts.len() != function.input.len()
                            || meta
                                .input_sorts
                                .iter()
                                .zip(&function.input)
                                .any(|(captured, expected)| captured != expected.name())
                            || arguments.len() != function.input.len()
                            || application.args.len() != arguments.len()
                            || output.sort.name() != meta.output_sort
                        {
                            return unsupported(
                                span,
                                format!(
                                    "rule `{rule_name}` registered head call `{}` ({:?} -> {}) has no exact receipt before native instruction {} for `{}` ({:?} -> {}) with {} arguments",
                                    function.name,
                                    function
                                        .input
                                        .iter()
                                        .map(|sort| sort.name())
                                        .collect::<Vec<_>>(),
                                    function.output().name(),
                                    application.instruction,
                                    meta.name,
                                    meta.input_sorts,
                                    meta.output_sort,
                                    application.args.len(),
                                ),
                            );
                        }
                        let children = arguments
                            .iter()
                            .zip(&function.input)
                            .map(|(argument, sort)| {
                                resolve_core_term_binding(
                                    egraph,
                                    argument,
                                    sort.name(),
                                    bindings,
                                    witnesses,
                                )
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        if children
                            .iter()
                            .zip(&application.args)
                            .any(|(binding, captured)| binding.endpoint != *captured)
                        {
                            return Err(CausalSliceError::Invariant(format!(
                                "rule `{rule_name}` table instruction {} captured arguments that diverge from its registered core grounding",
                                application.instruction
                            )));
                        }
                        let mut call_effects = elaborate_fire_applications(
                            egraph,
                            std::iter::once(application),
                            trace_functions,
                            witnesses,
                            prefix_fallback,
                            Some(CausalApplicationInput {
                                equality_forest,
                                dependencies,
                                app_index,
                            }),
                        )?;
                        let syntax = match meta.kind {
                            // Relation calls return an internal token with no
                            // source syntax. Its compiler temporary is left
                            // unbound; any later attempt to read it fails
                            // closed in `resolve_core_term_binding`.
                            TraceFunctionKind::Relation => None,
                            TraceFunctionKind::Constructor => {
                                let node = WitnessNode::App {
                                    sort: meta.output_sort.clone(),
                                    function: meta.name.clone(),
                                    children: children
                                        .iter()
                                        .map(|binding| binding.syntax)
                                        .collect(),
                                };
                                call_effects.read_dependencies.extend(
                                    children
                                        .iter()
                                        .map(|child| witnesses.availability(child.syntax)),
                                );
                                let witness = if let Some(witness) = witnesses
                                    .instance_by_node_endpoint(
                                        &meta.output_sort,
                                        application.result,
                                        &node,
                                    ) {
                                    witness
                                } else if application.newly_staged {
                                    let witness = witnesses.alias_app_endpoint(
                                        node,
                                        application.result,
                                        DepArena::EMPTY,
                                    )?;
                                    call_effects.new_witnesses.push(witness);
                                    witness
                                } else if let Some(availability) = congruent_app_availability(
                                    witnesses,
                                    &node,
                                    application.result,
                                    equality_forest,
                                    dependencies,
                                    None,
                                    app_index,
                                )? {
                                    let witness = witnesses.alias_app_endpoint(
                                        node,
                                        application.result,
                                        availability,
                                    )?;
                                    call_effects.read_dependencies.push(availability);
                                    witness
                                } else {
                                    return Err(CausalSliceError::Unsupported {
                                        location: span.to_string(),
                                        reason: format!(
                                            "registered constructor `{}` completed without exact constructor-row and equality provenance for its core syntax",
                                            meta.name
                                        ),
                                    });
                                };
                                witnesses.prefer_endpoint_witness(
                                    &meta.output_sort,
                                    application.result,
                                    witness,
                                )?;
                                Some(witness)
                            }
                            TraceFunctionKind::Mutable => {
                                return unsupported(
                                    span,
                                    format!(
                                        "action-time mutable lookup `{}` in rule `{rule_name}`",
                                        meta.name
                                    ),
                                );
                            }
                        };
                        effects.absorb(call_effects);
                        syntax.map(|syntax| BindingWitness {
                            syntax,
                            endpoint: application.result,
                        })
                    }
                    (
                        ResolvedCall::Primitive(primitive),
                        HeadCallReceipt::Primitive(application),
                    ) => {
                        if primitive.effect() != crate::PrimitiveEffect::Pure
                            || primitive.validator().is_none()
                            || !primitive.is_replay_safe()
                        {
                            return unsupported(
                                span,
                                format!(
                                    "head primitive `{}` without a Pure proof-validating specialization in rule `{rule_name}`",
                                    primitive.name()
                                ),
                            );
                        }
                        if primitive.external_id(crate::Context::Write) != application.function
                            || primitive.input().len() != arguments.len()
                            || application.args.len() != arguments.len()
                            || output.sort.name() != primitive.output().name()
                        {
                            return Err(CausalSliceError::Invariant(format!(
                                "rule `{rule_name}` primitive instruction {} diverged from its registered specialization",
                                application.instruction
                            )));
                        }
                        let children = arguments
                            .iter()
                            .zip(primitive.input())
                            .map(|(argument, sort)| {
                                resolve_core_term_binding(
                                    egraph,
                                    argument,
                                    sort.name(),
                                    bindings,
                                    witnesses,
                                )
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        if children
                            .iter()
                            .zip(&application.args)
                            .any(|(binding, captured)| binding.endpoint != *captured)
                        {
                            return Err(CausalSliceError::Invariant(format!(
                                "rule `{rule_name}` primitive instruction {} captured arguments that diverge from its registered core grounding",
                                application.instruction
                            )));
                        }
                        let mut availability = DepArena::EMPTY;
                        for child in &children {
                            let dependency = witnesses.availability(child.syntax);
                            effects.read_dependencies.push(dependency);
                            availability = dependencies.and(availability, dependency)?;
                        }
                        let syntax = witnesses.intern_app(
                            primitive.output().name(),
                            primitive.name(),
                            children.iter().map(|binding| binding.syntax).collect(),
                            application.result,
                            availability,
                            true,
                        )?;
                        witnesses.prefer_endpoint_witness(
                            primitive.output().name(),
                            application.result,
                            syntax,
                        )?;
                        Some(BindingWitness {
                            syntax,
                            endpoint: application.result,
                        })
                    }
                    (ResolvedCall::Values(_), _) => {
                        return unsupported(
                            span,
                            format!("tuple-values call in rule `{rule_name}` head"),
                        );
                    }
                    (ResolvedCall::Func(function), HeadCallReceipt::Primitive(application)) => {
                        return Err(CausalSliceError::Invariant(format!(
                            "rule `{rule_name}` function `{}` was traced as primitive instruction {}",
                            function.name, application.instruction
                        )));
                    }
                    (ResolvedCall::Primitive(primitive), HeadCallReceipt::Table(application)) => {
                        return Err(CausalSliceError::Invariant(format!(
                            "rule `{rule_name}` primitive `{}` was traced as table instruction {}",
                            primitive.name(),
                            application.instruction
                        )));
                    }
                };
                if let Some(binding) = binding {
                    bind_core_variable(rule_name, output, binding, bindings)?;
                }
            }
            GenericCoreAction::LetAtomTerm(_, output, term) => {
                let binding = resolve_core_term_binding(
                    egraph,
                    term,
                    output.sort.name(),
                    bindings,
                    witnesses,
                )?;
                bind_core_variable(rule_name, output, binding, bindings)?;
            }
            GenericCoreAction::Set(span, call, keys, values) => {
                let ResolvedCall::Func(function) = call else {
                    return unsupported(
                        span,
                        format!("non-function set action in rule `{rule_name}`"),
                    );
                };
                if keys.len() != function.input.len() || values.len() != function.outputs.len() {
                    return Err(CausalSliceError::Invariant(format!(
                        "rule `{rule_name}` registered malformed set action for `{}`",
                        function.name
                    )));
                }
                for (term, sort) in keys.iter().zip(&function.input) {
                    let _ =
                        resolve_core_term_binding(egraph, term, sort.name(), bindings, witnesses)?;
                }
                for (term, sort) in values.iter().zip(&function.outputs) {
                    let _ =
                        resolve_core_term_binding(egraph, term, sort.name(), bindings, witnesses)?;
                }
            }
            GenericCoreAction::Change(span, _, call, arguments) => {
                let ResolvedCall::Func(function) = call else {
                    return unsupported(
                        span,
                        format!("non-function change action in rule `{rule_name}`"),
                    );
                };
                if arguments.len() != function.input.len() {
                    return Err(CausalSliceError::Invariant(format!(
                        "rule `{rule_name}` registered malformed change action for `{}`",
                        function.name
                    )));
                }
                for (term, sort) in arguments.iter().zip(&function.input) {
                    let _ =
                        resolve_core_term_binding(egraph, term, sort.name(), bindings, witnesses)?;
                }
            }
            GenericCoreAction::Union(_, left, right) => {
                let sort = core_term_sort(left);
                let right_sort = core_term_sort(right);
                if right_sort != sort {
                    return Err(CausalSliceError::Invariant(format!(
                        "rule `{rule_name}` registered a union between `{sort}` and `{right_sort}`"
                    )));
                }
                let _ = resolve_core_term_binding(egraph, left, &sort, bindings, witnesses)?;
                let _ = resolve_core_term_binding(egraph, right, &sort, bindings, witnesses)?;
            }
            GenericCoreAction::Panic(span, _) => {
                return unsupported(span, format!("panic action in rule `{rule_name}`"));
            }
        }
    }
    if let Some(receipt) = receipts.next() {
        return Err(CausalSliceError::Invariant(format!(
            "rule `{rule_name}` captured unconsumed native head instruction {}",
            receipt.instruction()
        )));
    }
    for local in &model.head_lets {
        let actual = bindings.get(&local.name).ok_or_else(|| {
            CausalSliceError::Invariant(format!(
                "registered head of rule `{rule_name}` omitted source local `{}`",
                local.name
            ))
        })?;
        let (expected, syntax) = ground_arg_with_witness_at(
            egraph,
            &local.value,
            &local.sort,
            bindings,
            witnesses,
            None,
        )
        .map_err(|error| match error {
            CausalSliceError::Unsupported { location, reason } => {
                CausalSliceError::Unsupported {
                    location: model.span.to_string(),
                    reason: format!(
                        "{reason} while validating source local `{}` from {location} in rule `{rule_name}`",
                        local.name
                    ),
                }
            }
            error => error,
        })?;
        if actual.endpoint != expected.value
            || witnesses.nodes[actual.syntax.index()].syntax
                != witnesses.nodes[syntax.index()].syntax
        {
            return Err(CausalSliceError::Invariant(format!(
                "registered head of rule `{rule_name}` diverged from source local `{}`",
                local.name
            )));
        }
    }
    effects.normalize();
    Ok(effects)
}

fn core_term_sort(term: &GenericAtomTerm<ResolvedVar>) -> String {
    match term {
        GenericAtomTerm::Var(_, variable) | GenericAtomTerm::Global(_, variable) => {
            variable.sort.name().to_owned()
        }
        GenericAtomTerm::Literal(_, literal) => {
            crate::sort::literal_sort(literal).name().to_owned()
        }
    }
}

fn resolve_core_term_binding(
    egraph: &EGraph,
    term: &GenericAtomTerm<ResolvedVar>,
    expected_sort: &str,
    bindings: &IndexMap<String, BindingWitness>,
    witnesses: &mut WitnessArena,
) -> Result<BindingWitness, CausalSliceError> {
    match term {
        GenericAtomTerm::Var(_, variable) => {
            if variable.sort.name() != expected_sort {
                return Err(CausalSliceError::Invariant(format!(
                    "registered variable `{}` changed sort from `{}` to `{expected_sort}`",
                    variable.name,
                    variable.sort.name()
                )));
            }
            bindings.get(&variable.name).cloned().ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "registered head reads unbound variable `{}`",
                    variable.name
                ))
            })
        }
        GenericAtomTerm::Global(_, variable) => {
            if variable.sort.name() != expected_sort {
                return Err(CausalSliceError::Invariant(format!(
                    "registered global `{}` changed sort from `{}` to `{expected_sort}`",
                    variable.name,
                    variable.sort.name()
                )));
            }
            Ok(BindingWitness {
                syntax: witnesses.global_witness(&variable.name, expected_sort)?,
                endpoint: witnesses.global(&variable.name, expected_sort)?,
            })
        }
        GenericAtomTerm::Literal(_, literal) => {
            let actual_sort = crate::sort::literal_sort(literal);
            if actual_sort.name() != expected_sort {
                return Err(CausalSliceError::Invariant(format!(
                    "registered literal of sort `{}` used as `{expected_sort}`",
                    actual_sort.name()
                )));
            }
            let endpoint = literal_to_value(egraph.backend.base_values(), literal);
            let syntax = witnesses.intern_literal(expected_sort, literal.clone())?;
            bind_witness_endpoint(witnesses, expected_sort, endpoint, syntax)?;
            Ok(BindingWitness { syntax, endpoint })
        }
    }
}

fn bind_witness_endpoint(
    witnesses: &mut WitnessArena,
    sort: &str,
    endpoint: Value,
    syntax: WitnessId,
) -> Result<(), CausalSliceError> {
    match witnesses.endpoint(syntax) {
        Some(previous) if previous != endpoint => Err(CausalSliceError::Invariant(format!(
            "replay syntax of sort `{sort}` changed runtime endpoints"
        ))),
        Some(_) => Ok(()),
        None => witnesses.bind_endpoint_alias(sort, endpoint, syntax),
    }
}

fn bind_core_variable(
    rule_name: &str,
    variable: &ResolvedVar,
    binding: BindingWitness,
    bindings: &mut IndexMap<String, BindingWitness>,
) -> Result<(), CausalSliceError> {
    if let Some(previous) = bindings.get(&variable.name)
        && previous.endpoint != binding.endpoint
    {
        return Err(CausalSliceError::Invariant(format!(
            "registered head of rule `{rule_name}` rebound `{}` to a different endpoint",
            variable.name
        )));
    }
    bindings.entry(variable.name.clone()).or_insert(binding);
    Ok(())
}

fn seed_core_head_bindings(
    rule_name: &str,
    core_head: &ResolvedCoreActions,
    substitutions: &[(ResolvedVar, crate::core::ResolvedAtomTerm)],
    captured: &RuleMatch,
    bindings: &mut IndexMap<String, BindingWitness>,
    witnesses: &WitnessArena,
    snapshot: &WitnessSnapshot,
) -> Result<(), CausalSliceError> {
    let mut changed = true;
    while changed {
        changed = false;
        for (source, target) in substitutions {
            let GenericAtomTerm::Var(_, target) = target else {
                continue;
            };
            if bindings.contains_key(&target.name) {
                continue;
            }
            let Some(binding) = bindings.get(&source.name).cloned() else {
                continue;
            };
            if source.sort.name() != target.sort.name() {
                return Err(CausalSliceError::Invariant(format!(
                    "registered substitution in rule `{rule_name}` changed sort from `{}` to `{}`",
                    source.sort.name(),
                    target.sort.name()
                )));
            }
            bindings.insert(target.name.clone(), binding);
            changed = true;
        }
    }
    let captured = captured
        .bindings
        .iter()
        .map(|(name, value)| (name.as_ref(), *value))
        .collect::<IndexMap<_, _>>();
    for variable in core_head.free_vars() {
        if bindings.contains_key(&variable.name) {
            continue;
        }
        let endpoint = captured
            .get(variable.name.as_str())
            .copied()
            .ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "registered head of rule `{rule_name}` reads uncaptured core variable `{}`",
                    variable.name
                ))
            })?;
        let sort = variable.sort.name();
        let syntax = witnesses
            .by_endpoint_at(sort, endpoint, Some(snapshot))
            .ok_or_else(|| CausalSliceError::Unsupported {
                location: format!("captured core binding `{}`", variable.name),
                reason: format!("a `{sort}` endpoint without syntax in the exact wave pre-state"),
            })?;
        bindings.insert(variable.name, BindingWitness { syntax, endpoint });
    }
    Ok(())
}

struct CausalApplicationInput<'a> {
    equality_forest: &'a EqualityForest,
    dependencies: &'a mut DepArena,
    app_index: &'a mut WaveAppIndex,
}

fn elaborate_fire_applications<'a>(
    egraph: &EGraph,
    applications: impl IntoIterator<Item = &'a TableApplication>,
    trace_functions: &IndexMap<TableId, TraceFunctionMeta>,
    witnesses: &mut WitnessArena,
    prefix_fallback: bool,
    causal: Option<CausalApplicationInput<'_>>,
) -> Result<FireApplicationEffects, CausalSliceError> {
    let (equality_forest, mut dependencies, mut app_index) = match causal {
        Some(CausalApplicationInput {
            equality_forest,
            dependencies,
            app_index,
        }) => (Some(equality_forest), Some(dependencies), Some(app_index)),
        None => (None, None, None),
    };
    let mut observed_rows = Vec::new();
    let mut new_rows = Vec::new();
    let mut new_witnesses = Vec::new();
    let mut read_dependencies = Vec::new();
    let mut deferred_error = None;
    for application in applications {
        let meta = trace_functions.get(&application.table).ok_or_else(|| {
            CausalSliceError::Unsupported {
                location: format!("native action instruction {}", application.instruction),
                reason: format!("an application of unmodeled table {:?}", application.table),
            }
        })?;
        if application.args.len() != meta.input_sorts.len() {
            return Err(CausalSliceError::Invariant(format!(
                "application of `{}` captured {} arguments for runtime arity {}",
                meta.name,
                application.args.len(),
                meta.input_sorts.len()
            )));
        }
        match meta.kind {
            TraceFunctionKind::Relation => {
                let row = RowKey {
                    relation: meta.name.clone(),
                    args: meta
                        .input_sorts
                        .iter()
                        .zip(&application.args)
                        .map(|(sort, value)| TypedEndpoint {
                            sort: sort.clone(),
                            value: *value,
                        })
                        .collect(),
                };
                observed_rows.push(row.clone());
                if application.newly_staged {
                    new_rows.push(row);
                }
            }
            TraceFunctionKind::Constructor => {
                log::debug!(
                    "causal constructor receipt origin={} instruction={} function={} args={:?} result={:?}",
                    application.origin.index(),
                    application.instruction,
                    meta.name,
                    application.args,
                    application.result
                );
                let children = meta
                    .input_sorts
                    .iter()
                    .zip(&application.args)
                    .map(|(sort, value)| {
                        endpoint_witness(egraph, sort, *value, witnesses, &meta.name)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                read_dependencies
                    .extend(children.iter().map(|child| witnesses.availability(*child)));
                let expected = WitnessNode::App {
                    sort: meta.output_sort.clone(),
                    function: meta.name.clone(),
                    children: children.clone(),
                };
                if application.newly_staged {
                    let was_known = witnesses
                        .instance_by_node_endpoint(&meta.output_sort, application.result, &expected)
                        .is_some();
                    let witness = witnesses.intern_app(
                        &meta.output_sort,
                        &meta.name,
                        children,
                        application.result,
                        DepArena::EMPTY,
                        true,
                    )?;
                    if !was_known {
                        new_witnesses.push(witness);
                    }
                } else {
                    match witnesses.by_endpoint(&meta.output_sort, application.result) {
                        Some(witness)
                            if witnesses.nodes[witness.index()].node != expected
                                && !prefix_fallback
                                && children.iter().any(|child| {
                                    witness_contains_bigrat_primitive(witnesses, *child)
                                }) =>
                        {
                            let availability = witnesses.availability(witness);
                            let alias = witnesses.intern_app(
                                &meta.output_sort,
                                &meta.name,
                                children,
                                application.result,
                                availability,
                                true,
                            )?;
                            witnesses.prefer_endpoint_witness(
                                &meta.output_sort,
                                application.result,
                                alias,
                            )?;
                            read_dependencies.push(witnesses.availability(alias));
                        }
                        Some(witness)
                            if witnesses.nodes[witness.index()].node != expected
                                && !prefix_fallback =>
                        {
                            if let (Some(equality_forest), Some(dependencies)) =
                                (equality_forest, dependencies.as_deref_mut())
                                && let Some(availability) = congruent_app_availability(
                                    witnesses,
                                    &expected,
                                    application.result,
                                    equality_forest,
                                    dependencies,
                                    None,
                                    app_index.as_deref_mut().ok_or_else(|| {
                                        CausalSliceError::Invariant(
                                            "causal constructor lookup has no wave application index"
                                                .to_owned(),
                                        )
                                    })?,
                                )?
                            {
                                witnesses.alias_app_endpoint(
                                    expected,
                                    application.result,
                                    availability,
                                )?;
                                read_dependencies.push(availability);
                                continue;
                            }
                            if dependencies.is_some() {
                                let alias = witnesses.alias_app_endpoint(
                                    expected,
                                    application.result,
                                    DepArena::EMPTY,
                                )?;
                                new_witnesses.push(alias);
                                deferred_error.get_or_insert_with(|| DeferredUnsupported {
                                    location: format!("constructor application `{}`", meta.name),
                                    reason: "a congruence-created table hit without exact constructor-row provenance"
                                        .to_owned(),
                                });
                                continue;
                            }
                            return Err(CausalSliceError::Unsupported {
                                location: format!("constructor application `{}`", meta.name),
                                reason: "a table hit whose match-time syntax conflicts with its captured witness"
                                    .to_owned(),
                            });
                        }
                        Some(witness) => {
                            read_dependencies.push(witnesses.availability(witness));
                        }
                        None if prefix_fallback => {
                            // A congruence-created row may have no earlier
                            // syntax witness. This exact table hit proves the
                            // source application denotes its endpoint in the
                            // fully retained prestate, but is not a producer.
                            witnesses.intern_app(
                                &meta.output_sort,
                                &meta.name,
                                children,
                                application.result,
                                DepArena::EMPTY,
                                true,
                            )?;
                        }
                        None if dependencies.is_some() => {
                            // The table hit proves that this syntax denoted the
                            // endpoint in the native prestate, but without a
                            // prior witness we cannot yet identify its causal
                            // producer. Carry a poisoned witness forward so an
                            // irrelevant firing can still be sliced away and a
                            // later retained use reaches this exact boundary.
                            let alias = witnesses.intern_app(
                                &meta.output_sort,
                                &meta.name,
                                children,
                                application.result,
                                DepArena::EMPTY,
                                true,
                            )?;
                            new_witnesses.push(alias);
                            deferred_error.get_or_insert_with(|| DeferredUnsupported {
                                location: format!("constructor application `{}`", meta.name),
                                reason:
                                    "a table hit without a previously captured constructor witness"
                                        .to_owned(),
                            });
                        }
                        None => {
                            return Err(CausalSliceError::Unsupported {
                                location: format!("constructor application `{}`", meta.name),
                                reason:
                                    "a table hit without a previously captured constructor witness"
                                        .to_owned(),
                            });
                        }
                    }
                }
            }
            TraceFunctionKind::Mutable => {
                return Err(CausalSliceError::Unsupported {
                    location: format!("mutable function application `{}`", meta.name),
                    reason: "an action-time lookup-or-insert on mutable state; exact `:merge new` sets are traced at commit instead"
                        .to_owned(),
                });
            }
        }
    }
    new_rows.sort_by_key(|row| {
        observed_rows
            .iter()
            .position(|observed| observed == row)
            .unwrap_or(usize::MAX)
    });
    new_rows.dedup();
    new_witnesses.sort_unstable_by_key(|id| id.index());
    new_witnesses.dedup();
    Ok(FireApplicationEffects {
        observed_rows,
        new_rows,
        new_witnesses,
        read_dependencies,
        deferred_error,
    })
}

struct AliasCapturedHeadInput<'a> {
    egraph: &'a EGraph,
    model: &'a RuleModel,
    bindings: &'a IndexMap<String, BindingWitness>,
    applications: &'a [&'a TableApplication],
    trace_functions: &'a IndexMap<TableId, TraceFunctionMeta>,
    equality_forest: &'a EqualityForest,
}

fn alias_captured_head_syntaxes(
    input: AliasCapturedHeadInput<'_>,
    witnesses: &mut WitnessArena,
    dependencies: &mut DepArena,
    effects: &mut FireApplicationEffects,
    app_index: &mut WaveAppIndex,
) -> Result<(), CausalSliceError> {
    let AliasCapturedHeadInput {
        egraph,
        model,
        bindings,
        applications,
        trace_functions,
        equality_forest,
    } = input;
    let mut modeled_applications = Vec::new();
    for atom in &model.head {
        for arg in &atom.args {
            collect_postorder_applications(arg, &mut modeled_applications);
        }
    }
    for application in model.head_constructors.iter().chain(&model.head_subsumes) {
        collect_postorder_applications(application, &mut modeled_applications);
    }
    for equality in &model.head_unions {
        collect_postorder_applications(&equality.left, &mut modeled_applications);
        collect_postorder_applications(&equality.right, &mut modeled_applications);
    }
    for set in &model.head_sets {
        for key in &set.keys {
            collect_postorder_applications(key, &mut modeled_applications);
        }
        collect_postorder_applications(&set.value, &mut modeled_applications);
    }

    let mut used = vec![false; applications.len()];
    for modeled in modeled_applications {
        let AtomArg::App {
            function,
            args,
            input_sorts,
            output_sort,
            ..
        } = modeled
        else {
            continue;
        };
        let grounded_children = args
            .iter()
            .zip(input_sorts)
            .map(|(arg, sort)| {
                ground_arg_with_witness_at(egraph, arg, sort, bindings, witnesses, None)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let captured_args = grounded_children
            .iter()
            .map(|(endpoint, _)| endpoint.value)
            .collect::<Vec<_>>();
        let Some((index, captured)) = applications.iter().enumerate().find(|(index, captured)| {
            if used[*index] || captured.args != captured_args {
                return false;
            }
            trace_functions.get(&captured.table).is_some_and(|meta| {
                meta.kind == TraceFunctionKind::Constructor
                    && meta.name == *function
                    && meta.output_sort == *output_sort
            })
        }) else {
            continue;
        };
        used[index] = true;
        effects.read_dependencies.extend(
            grounded_children
                .iter()
                .map(|(_, witness)| witnesses.availability(*witness)),
        );
        let expected = WitnessNode::App {
            sort: output_sort.clone(),
            function: function.clone(),
            children: grounded_children
                .iter()
                .map(|(_, witness)| *witness)
                .collect(),
        };
        if captured.newly_staged {
            let alias = witnesses.alias_app_endpoint(expected, captured.result, DepArena::EMPTY)?;
            effects.new_witnesses.push(alias);
        } else if let Some(availability) = congruent_app_availability(
            witnesses,
            &expected,
            captured.result,
            equality_forest,
            dependencies,
            None,
            app_index,
        )? {
            witnesses.alias_app_endpoint(expected, captured.result, availability)?;
            effects.read_dependencies.push(availability);
        }
    }
    effects.new_witnesses.sort_unstable_by_key(|id| id.index());
    effects.new_witnesses.dedup();
    Ok(())
}

fn collect_postorder_applications<'a>(arg: &'a AtomArg, applications: &mut Vec<&'a AtomArg>) {
    if let AtomArg::App { args, .. } = arg {
        for child in args {
            collect_postorder_applications(child, applications);
        }
        applications.push(arg);
    }
}

fn congruent_app_availability(
    witnesses: &WitnessArena,
    expected: &WitnessNode,
    output: Value,
    equality_forest: &EqualityForest,
    dependencies: &mut DepArena,
    snapshot: Option<&WitnessSnapshot>,
    app_index: &mut WaveAppIndex,
) -> Result<Option<DepId>, CausalSliceError> {
    congruent_app_availability_with_mode(
        witnesses,
        expected,
        output,
        equality_forest,
        dependencies,
        snapshot,
        app_index,
        CongruenceEqualityMode::Deferred,
    )
}

fn congruent_app_availability_explained(
    witnesses: &WitnessArena,
    expected: &WitnessNode,
    output: Value,
    equality_forest: &EqualityForest,
    dependencies: &mut DepArena,
    snapshot: Option<&WitnessSnapshot>,
    app_index: &mut WaveAppIndex,
) -> Result<Option<DepId>, CausalSliceError> {
    congruent_app_availability_with_mode(
        witnesses,
        expected,
        output,
        equality_forest,
        dependencies,
        snapshot,
        app_index,
        CongruenceEqualityMode::Explained,
    )
}

#[derive(Clone, Copy)]
enum CongruenceEqualityMode {
    Deferred,
    Explained,
}

#[allow(clippy::too_many_arguments)]
fn congruent_app_availability_with_mode(
    witnesses: &WitnessArena,
    expected: &WitnessNode,
    output: Value,
    equality_forest: &EqualityForest,
    dependencies: &mut DepArena,
    snapshot: Option<&WitnessSnapshot>,
    app_index: &mut WaveAppIndex,
    equality_mode: CongruenceEqualityMode,
) -> Result<Option<DepId>, CausalSliceError> {
    let WitnessNode::App {
        sort,
        function,
        children: _,
    } = expected
    else {
        return Err(CausalSliceError::Invariant(
            "congruence lookup received a literal witness".to_owned(),
        ));
    };
    let key = (sort.clone(), function.clone());
    app_index.synchronize_group(&key, witnesses, equality_forest)?;
    let Some(candidates) = witnesses.app_instances.get(&key) else {
        return Ok(None);
    };
    let Some(signature) =
        canonical_app_signature(witnesses, expected, Some(output), equality_forest)
    else {
        return Ok(None);
    };
    let Some(positions) = app_index
        .groups
        .get(&key)
        .and_then(|group| group.buckets.get(&signature))
    else {
        return Ok(None);
    };
    let visible = snapshot
        .map(|snapshot| {
            snapshot
                .app_instance_lengths
                .get(&key)
                .copied()
                .unwrap_or(0)
        })
        .unwrap_or(candidates.len())
        .min(candidates.len());
    congruent_app_availability_from_positions(
        witnesses,
        expected,
        output,
        equality_forest,
        dependencies,
        candidates,
        positions
            .iter()
            .rev()
            .copied()
            .filter(|position| *position < visible),
        equality_mode,
    )
}

fn canonical_app_signature(
    witnesses: &WitnessArena,
    application: &WitnessNode,
    output: Option<Value>,
    equality_forest: &EqualityForest,
) -> Option<CanonicalAppSignature> {
    let WitnessNode::App { sort, children, .. } = application else {
        return None;
    };
    let children = children
        .iter()
        .map(|child| {
            let value = witnesses.endpoint(*child)?;
            let sort = match &witnesses.nodes[child.index()].node {
                WitnessNode::Literal { sort, .. } | WitnessNode::App { sort, .. } => sort,
            };
            Some(equality_forest.canonical_endpoint(&TypedEndpoint {
                sort: sort.clone(),
                value,
            }))
        })
        .collect::<Option<Vec<_>>>()?;
    Some(CanonicalAppSignature {
        children: children.into_boxed_slice(),
        output: equality_forest.canonical_endpoint(&TypedEndpoint {
            sort: sort.clone(),
            value: output?,
        }),
    })
}

#[allow(clippy::too_many_arguments)]
fn congruent_app_availability_from_positions(
    witnesses: &WitnessArena,
    expected: &WitnessNode,
    output: Value,
    equality_forest: &EqualityForest,
    dependencies: &mut DepArena,
    candidates: &[WitnessId],
    positions: impl IntoIterator<Item = usize>,
    equality_mode: CongruenceEqualityMode,
) -> Result<Option<DepId>, CausalSliceError> {
    let WitnessNode::App { sort, children, .. } = expected else {
        return Err(CausalSliceError::Invariant(
            "congruence lookup received a literal witness".to_owned(),
        ));
    };
    for position in positions {
        let candidate = candidates[position];
        let Some(candidate_output) = witnesses.endpoint(candidate) else {
            continue;
        };
        let WitnessNode::App {
            children: candidate_children,
            ..
        } = &witnesses.nodes[candidate.index()].node
        else {
            continue;
        };
        if candidate_children.len() != children.len() {
            continue;
        }
        let mut support = vec![witnesses.availability(candidate)];
        let mut complete = true;
        for (candidate_child, current_child) in candidate_children.iter().zip(children) {
            support.push(witnesses.availability(*current_child));
            let Some(candidate_endpoint) = witnesses.endpoint(*candidate_child) else {
                complete = false;
                break;
            };
            let Some(current_endpoint) = witnesses.endpoint(*current_child) else {
                complete = false;
                break;
            };
            if candidate_endpoint == current_endpoint {
                continue;
            }
            let candidate_sort = match &witnesses.nodes[candidate_child.index()].node {
                WitnessNode::Literal { sort, .. } | WitnessNode::App { sort, .. } => sort,
            };
            let current_sort = match &witnesses.nodes[current_child.index()].node {
                WitnessNode::Literal { sort, .. } | WitnessNode::App { sort, .. } => sort,
            };
            if candidate_sort != current_sort {
                complete = false;
                break;
            }
            let left = TypedEndpoint {
                sort: candidate_sort.clone(),
                value: candidate_endpoint,
            };
            let right = TypedEndpoint {
                sort: current_sort.clone(),
                value: current_endpoint,
            };
            match equality_mode {
                CongruenceEqualityMode::Deferred => {
                    if !equality_forest.are_equal(&left, &right) {
                        complete = false;
                        break;
                    }
                    support.push(dependencies.equality(left, right)?);
                }
                CongruenceEqualityMode::Explained => {
                    let Some(explanation) = equality_forest.explain(&left, &right) else {
                        complete = false;
                        break;
                    };
                    support.extend(explanation);
                }
            }
        }
        if !complete {
            continue;
        }
        if candidate_output != output {
            let left = TypedEndpoint {
                sort: sort.clone(),
                value: candidate_output,
            };
            let right = TypedEndpoint {
                sort: sort.clone(),
                value: output,
            };
            match equality_mode {
                CongruenceEqualityMode::Deferred => {
                    if !equality_forest.are_equal(&left, &right) {
                        continue;
                    }
                    support.push(dependencies.equality(left, right)?);
                }
                CongruenceEqualityMode::Explained => {
                    let Some(explanation) = equality_forest.explain(&left, &right) else {
                        continue;
                    };
                    support.extend(explanation);
                }
            }
        }
        let mut availability = DepArena::EMPTY;
        for dependency in support {
            availability = dependencies.and(availability, dependency)?;
        }
        return Ok(Some(availability));
    }
    Ok(None)
}

#[cfg(test)]
fn congruent_app_availability_linear(
    witnesses: &WitnessArena,
    expected: &WitnessNode,
    output: Value,
    equality_forest: &EqualityForest,
    dependencies: &mut DepArena,
    snapshot: Option<&WitnessSnapshot>,
) -> Result<Option<DepId>, CausalSliceError> {
    let WitnessNode::App { sort, function, .. } = expected else {
        return Err(CausalSliceError::Invariant(
            "congruence lookup received a literal witness".to_owned(),
        ));
    };
    let key = (sort.clone(), function.clone());
    let Some(candidates) = witnesses.app_instances.get(&key) else {
        return Ok(None);
    };
    let visible = snapshot
        .map(|snapshot| {
            snapshot
                .app_instance_lengths
                .get(&key)
                .copied()
                .unwrap_or(0)
        })
        .unwrap_or(candidates.len())
        .min(candidates.len());
    congruent_app_availability_from_positions(
        witnesses,
        expected,
        output,
        equality_forest,
        dependencies,
        candidates,
        (0..visible).rev(),
        CongruenceEqualityMode::Deferred,
    )
}

fn witness_contains_bigrat_primitive(witnesses: &WitnessArena, witness: WitnessId) -> bool {
    witnesses.nodes[witness.index()].contains_bigrat_primitive
}

fn endpoint_witness(
    egraph: &EGraph,
    sort: &str,
    value: Value,
    witnesses: &mut WitnessArena,
    function: &str,
) -> Result<WitnessId, CausalSliceError> {
    if let Some(witness) = witnesses.by_endpoint(sort, value) {
        return Ok(witness);
    }
    let runtime_sort = egraph
        .get_sort_by_name(sort)
        .ok_or_else(|| CausalSliceError::Invariant(format!("runtime sort `{sort}` disappeared")))?;
    if runtime_sort.is_container_sort() {
        return Err(CausalSliceError::Unsupported {
            location: format!("constructor application `{function}`"),
            reason: format!(
                "a `{sort}` container endpoint without an exact earlier primitive witness"
            ),
        });
    }
    if runtime_sort.is_eq_sort() {
        return Err(CausalSliceError::Unsupported {
            location: format!("constructor application `{function}`"),
            reason: format!("a `{sort}` child endpoint without an earlier immutable witness"),
        });
    }
    scalar_witness(
        egraph,
        sort,
        value,
        witnesses,
        &format!("constructor `{function}` argument"),
    )
}

fn scalar_witness(
    egraph: &EGraph,
    sort_name: &str,
    value: Value,
    witnesses: &mut WitnessArena,
    location: &str,
) -> Result<WitnessId, CausalSliceError> {
    if let Some(witness) = witnesses.by_endpoint(sort_name, value) {
        return Ok(witness);
    }
    let sort = egraph.get_sort_by_name(sort_name).ok_or_else(|| {
        CausalSliceError::Invariant(format!("runtime sort `{sort_name}` disappeared"))
    })?;
    let mut termdag = TermDag::default();
    let term = sort.reconstruct_termdag_base(egraph.backend.base_values(), value, &mut termdag);
    let expr = termdag.term_to_expr(&term, Span::Panic);
    let witness = intern_reconstructed_base_witness(&expr, sort_name, witnesses, location)?;
    witnesses.bind_endpoint(sort_name, value, witness)?;
    Ok(witness)
}

fn intern_reconstructed_base_witness(
    expr: &Expr,
    sort: &str,
    witnesses: &mut WitnessArena,
    location: &str,
) -> Result<WitnessId, CausalSliceError> {
    match expr {
        GenericExpr::Lit(_, literal) => {
            let actual = match literal {
                Literal::Int(_) => "i64",
                Literal::Float(_) => "f64",
                Literal::String(_) => "String",
                Literal::Bool(_) => "bool",
                Literal::Unit => "Unit",
            };
            if actual != sort || !literal_is_source_stable(literal) {
                return Err(CausalSliceError::Unsupported {
                    location: location.to_owned(),
                    reason: format!(
                        "a `{sort}` witness that egglog's source printer cannot round-trip"
                    ),
                });
            }
            witnesses.intern_literal(sort, literal.clone())
        }
        GenericExpr::Call(span, function, args) => {
            if sort == "BigInt" && function == "from-string" {
                let [GenericExpr::Lit(_, Literal::String(value))] = args.as_slice() else {
                    return Err(CausalSliceError::Invariant(format!(
                        "reconstructed BigInt at {span} is not one canonical string"
                    )));
                };
                let value = value
                    .parse::<i64>()
                    .map_err(|_| CausalSliceError::Unsupported {
                        location: location.to_owned(),
                        reason: format!(
                            "a BigInt witness outside the replayable i64 range: `{value}`"
                        ),
                    })?;
                let child = witnesses.intern_literal("i64", Literal::Int(value))?;
                return witnesses.intern_syntax_app("BigInt", "bigint", vec![child]);
            }
            let input_sorts: &[&str] = match (sort, function.as_str()) {
                ("BigInt", "bigint") => &["i64"],
                ("BigRat", "bigrat") => &["BigInt", "BigInt"],
                _ => {
                    return Err(CausalSliceError::Unsupported {
                        location: location.to_owned(),
                        reason: format!(
                            "a non-scalar `{sort}` value reconstructed through unsupported primitive `{function}`"
                        ),
                    });
                }
            };
            if args.len() != input_sorts.len() {
                return Err(CausalSliceError::Invariant(format!(
                    "reconstructed `{function}` at {span} has arity {} instead of {}",
                    args.len(),
                    input_sorts.len()
                )));
            }
            let children = args
                .iter()
                .zip(input_sorts)
                .map(|(arg, input_sort)| {
                    intern_reconstructed_base_witness(arg, input_sort, witnesses, location)
                })
                .collect::<Result<Vec<_>, _>>()?;
            witnesses.intern_syntax_app(sort, function, children)
        }
        GenericExpr::Var(span, variable) => Err(CausalSliceError::Invariant(format!(
            "reconstructed base witness at {span} contains variable `{variable}`"
        ))),
    }
}

fn source_row(
    egraph: &EGraph,
    relations: &IndexMap<String, RelationDecl>,
    fact: &SourceFact,
    witnesses: &mut WitnessArena,
) -> Result<RowKey, CausalSliceError> {
    let SourceFactKind::Relation(atom) = &fact.kind else {
        return Err(CausalSliceError::Invariant(
            "source_row received a constructor-only or global initialization".to_owned(),
        ));
    };
    let declaration = &relations[&atom.relation];
    for (arg, sort) in atom.args.iter().zip(&declaration.sorts) {
        let AtomArg::Lit(literal) = arg else {
            return Err(CausalSliceError::Unsupported {
                location: format!("source command {}", fact.command_index),
                reason: "a constructed source value without native application evidence".to_owned(),
            });
        };
        let value = literal_to_value(egraph.backend.base_values(), literal);
        let witness = witnesses.intern_literal(sort, literal.clone())?;
        witnesses.bind_endpoint(sort, value, witness)?;
    }
    ground_atoms(
        egraph,
        std::slice::from_ref(atom),
        &IndexMap::default(),
        witnesses,
        relations,
    )?
    .pop()
    .ok_or_else(|| CausalSliceError::Invariant("source grounding produced no row".to_owned()))
}

fn ground_arg(
    egraph: &EGraph,
    arg: &AtomArg,
    sort: &str,
    bindings: &IndexMap<String, BindingWitness>,
    witnesses: &WitnessArena,
) -> Result<TypedEndpoint, CausalSliceError> {
    ground_arg_at(egraph, arg, sort, bindings, witnesses, None)
}

fn ground_arg_at(
    egraph: &EGraph,
    arg: &AtomArg,
    sort: &str,
    bindings: &IndexMap<String, BindingWitness>,
    witnesses: &WitnessArena,
    snapshot: Option<&WitnessSnapshot>,
) -> Result<TypedEndpoint, CausalSliceError> {
    let value = match arg {
        AtomArg::Lit(literal) => literal_to_value(egraph.backend.base_values(), literal),
        AtomArg::Global {
            name,
            sort: modeled_sort,
        } => {
            if modeled_sort != sort {
                return Err(CausalSliceError::Invariant(format!(
                    "source global `{name}` was grounded as `{sort}` after being modeled as `{modeled_sort}`"
                )));
            }
            witnesses.global(name, sort)?
        }
        AtomArg::Var(_, variable) => bindings
            .get(variable)
            .map(|binding| binding.endpoint)
            .ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "grounding omitted source variable `{variable}`"
                ))
            })?,
        AtomArg::App { .. } => {
            return ground_arg_with_witness_at(egraph, arg, sort, bindings, witnesses, snapshot)
                .map(|(endpoint, _)| endpoint);
        }
    };
    Ok(TypedEndpoint {
        sort: sort.to_owned(),
        value,
    })
}

fn ground_arg_with_witness_at(
    egraph: &EGraph,
    arg: &AtomArg,
    sort: &str,
    bindings: &IndexMap<String, BindingWitness>,
    witnesses: &WitnessArena,
    snapshot: Option<&WitnessSnapshot>,
) -> Result<(TypedEndpoint, WitnessId), CausalSliceError> {
    let (value, witness) = match arg {
        AtomArg::Lit(literal) => {
            let value = literal_to_value(egraph.backend.base_values(), literal);
            // Literal syntax is immutable and available independently of the
            // e-graph state. Select it by syntax identity: the same scalar
            // endpoint may currently prefer a computed primitive witness.
            let node = WitnessNode::Literal {
                sort: sort.to_owned(),
                value: literal.clone(),
            };
            let witness = witnesses.ids.get(&node).copied().ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "grounded `{sort}` literal lacked its exact syntax witness"
                ))
            })?;
            if witnesses.endpoint(witness) != Some(value) {
                return Err(CausalSliceError::Invariant(format!(
                    "grounded `{sort}` literal syntax changed endpoints"
                )));
            }
            (value, witness)
        }
        AtomArg::Global {
            name,
            sort: modeled_sort,
        } => {
            if modeled_sort != sort {
                return Err(CausalSliceError::Invariant(format!(
                    "source global `{name}` was grounded as `{sort}` after being modeled as `{modeled_sort}`"
                )));
            }
            (
                witnesses.global(name, sort)?,
                witnesses.global_witness(name, sort)?,
            )
        }
        AtomArg::Var(_, variable) => {
            let binding = bindings.get(variable).ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "grounding omitted source variable `{variable}`"
                ))
            })?;
            (binding.endpoint, binding.syntax)
        }
        AtomArg::App {
            function,
            args,
            input_sorts,
            primitive,
            ..
        } => {
            let grounded_children = args
                .iter()
                .zip(input_sorts)
                .map(|(child, child_sort)| {
                    ground_arg_with_witness_at(
                        egraph, child, child_sort, bindings, witnesses, snapshot,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            let node = WitnessNode::App {
                sort: sort.to_owned(),
                function: function.clone(),
                children: grounded_children
                    .iter()
                    .map(|(_, witness)| *witness)
                    .collect(),
            };
            let matches_inputs = |witness: WitnessId| {
                let WitnessNode::App { children, .. } = &witnesses.nodes[witness.index()].node
                else {
                    return false;
                };
                children.len() == grounded_children.len()
                    && children
                        .iter()
                        .zip(&grounded_children)
                        .all(|(captured, (current, _))| {
                            witnesses.endpoint(*captured) == Some(current.value)
                        })
            };
            let witness = if primitive.is_some() {
                // Typed replay-safe primitives are not e-graph table rows.
                // A query or ordered head may materialize their exact syntax
                // during this firing, so constructor pre-wave visibility does
                // not apply.
                witnesses
                    .ids
                    .get(&node)
                    .copied()
                    .filter(|witness| matches_inputs(*witness))
            } else if let Some(snapshot) = snapshot {
                let key = (sort.to_owned(), function.clone());
                let instances = witnesses.app_instances.get(&key);
                let visible = instances
                    .and_then(|_| snapshot.app_instance_lengths.get(&key).copied())
                    .unwrap_or(0);
                instances.and_then(|instances| {
                    instances[..visible.min(instances.len())]
                        .iter()
                        .rev()
                        .copied()
                        .find(|witness| {
                            witnesses.nodes[witness.index()].node == node
                                && matches_inputs(*witness)
                        })
                })
            } else {
                witnesses
                    .ids
                    .get(&node)
                    .copied()
                    .filter(|witness| matches_inputs(*witness))
            }
            .ok_or_else(|| CausalSliceError::Unsupported {
                location: format!("grounded constructor `{function}`"),
                reason: "syntax that was unavailable at the captured firing".to_owned(),
            })?;
            let endpoint = witnesses.endpoint(witness).ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "constructor witness `{function}` has no runtime endpoint"
                ))
            })?;
            (endpoint, witness)
        }
    };
    Ok((
        TypedEndpoint {
            sort: sort.to_owned(),
            value,
        },
        witness,
    ))
}

fn intern_atom_arg_literals(
    egraph: &EGraph,
    arg: &AtomArg,
    sort: &str,
    witnesses: &mut WitnessArena,
) -> Result<(), CausalSliceError> {
    match arg {
        AtomArg::Lit(literal) => {
            let witness = witnesses.intern_literal(sort, literal.clone())?;
            let endpoint = literal_to_value(egraph.backend.base_values(), literal);
            witnesses.bind_endpoint_alias(sort, endpoint, witness)?;
        }
        AtomArg::App {
            args, input_sorts, ..
        } => {
            for (child, child_sort) in args.iter().zip(input_sorts) {
                intern_atom_arg_literals(egraph, child, child_sort, witnesses)?;
            }
        }
        AtomArg::Var(..) | AtomArg::Global { .. } => {}
    }
    Ok(())
}

fn same_row_multiset(left: &[RowKey], right: &[RowKey]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut unmatched = right.to_vec();
    for row in left {
        let Some(index) = unmatched.iter().position(|candidate| candidate == row) else {
            return false;
        };
        unmatched.swap_remove(index);
    }
    unmatched.is_empty()
}

fn backward_slice(
    events: &EventArena,
    dependencies: &DepArena,
    equality_forest: &EqualityForest,
    root: DepId,
) -> Result<(IndexSet<EventId>, usize), CausalSliceError> {
    let mut retained = IndexSet::default();
    let mut visited_dependencies = HashSet::default();
    let mut retained_prefix_fallbacks = 0usize;
    let mut work = vec![root];
    while let Some(dependency) = work.pop() {
        if !visited_dependencies.insert(dependency) {
            continue;
        }
        match &dependencies.nodes[dependency.index()] {
            DepNode::Empty => {}
            DepNode::And(left, right) => {
                work.push(*right);
                work.push(*left);
            }
            DepNode::Eq { left, right } => {
                let explanation = equality_forest.explain(left, right).ok_or_else(|| {
                    CausalSliceError::Unsupported {
                        location: format!("retained equality {left:?} = {right:?}"),
                        reason: "a successful-union path containing an untyped or opaque edge"
                            .to_owned(),
                    }
                })?;
                work.extend(explanation);
            }
            DepNode::Event(event) => {
                if retained.insert(*event) {
                    let replay_event = &events.events[event.index()];
                    work.push(replay_event.prerequisites);
                }
            }
            DepNode::Prefix(last_event) => {
                retained_prefix_fallbacks += 1;
                for index in 0..=last_event.index() {
                    let event = EventId(index as u32);
                    if retained.insert(event) {
                        work.push(events.events[index].prerequisites);
                    }
                }
            }
            DepNode::Unsupported { location, reason } => {
                return Err(CausalSliceError::Unsupported {
                    location: location.clone(),
                    reason: reason.clone(),
                });
            }
        }
    }
    retained.sort_unstable();
    Ok((retained, retained_prefix_fallbacks))
}

const SHARED_REPLAY_WITNESS_PREFIX: &str = "$__csw";

fn emit_prefix_replay_commands(
    _commands: &[Command],
    schedule_span: &Span,
    rules: &IndexMap<String, RuleModel>,
    fires: &[CompactReplayFire],
    witnesses: &WitnessArena,
) -> Result<(String, usize), CausalSliceError> {
    let mut previous_position = None;
    let mut rendered = String::new();
    let mut shared_witnesses = 0usize;
    let mut global_names = IndexMap::default();
    for (name, witness) in &witnesses.global_witnesses {
        global_names.entry(*witness).or_insert(name.as_str());
    }

    let mut start = 0usize;
    while start < fires.len() {
        let wave = fires[start].wave;
        let mut end = start + 1;
        while end < fires.len() && fires[end].wave == wave {
            end += 1;
        }
        let wave_fires = &fires[start..end];
        let mut root_witnesses = IndexSet::<WitnessId>::default();
        let mut witness_uses = HashMap::<WitnessId, usize>::default();
        let mut group_indices = IndexMap::<u32, u32>::default();
        let mut group_variables = IndexMap::<u32, Arc<[String]>>::default();
        for fire in wave_fires {
            let position = (fire.wave, fire.ordinal);
            if let Some(previous) = previous_position {
                debug_assert!(previous < position);
            }
            previous_position = Some(position);
            let next_group = u32::try_from(group_indices.len())
                .expect("packed replay group count exceeded u32 capacity");
            group_indices.entry(fire.rule_index).or_insert(next_group);
            let (_, model) = rules.get_index(fire.rule_index as usize).ok_or_else(|| {
                CausalSliceError::Invariant(
                    "captured compact replay referenced an unknown rule index".to_owned(),
                )
            })?;
            let actual_variables = fire
                .selector_variables
                .as_deref()
                .unwrap_or(&model.replay_var_order);
            if let Some(expected) = group_variables.get(&fire.rule_index) {
                if expected.as_ref() != actual_variables {
                    return Err(CausalSliceError::Invariant(format!(
                        "one packed replay group for rule index {} had inconsistent selector columns",
                        fire.rule_index
                    )));
                }
            } else {
                group_variables.insert(
                    fire.rule_index,
                    fire.selector_variables
                        .clone()
                        .unwrap_or_else(|| Arc::from(model.replay_var_order.clone())),
                );
            }
            if fire.bindings.len() != actual_variables.len() {
                return Err(CausalSliceError::Invariant(format!(
                    "packed replay firing for rule index {} has {} witnesses for {} selector columns",
                    fire.rule_index,
                    fire.bindings.len(),
                    actual_variables.len()
                )));
            }
            for witness in &fire.bindings {
                root_witnesses.insert(*witness);
                *witness_uses.entry(*witness).or_default() += 1;
            }
        }

        let mut witness_indices = IndexMap::<WitnessId, u32>::default();
        for witness in root_witnesses {
            collect_packed_witness_dag(witness, witnesses, &global_names, &mut witness_indices);
        }
        let packed_witnesses = witness_indices
            .keys()
            .map(|witness| {
                if let Some(name) = global_names.get(witness) {
                    let record = &witnesses.nodes[witness.index()];
                    let sort = match &record.node {
                        WitnessNode::Literal { sort, .. } | WitnessNode::App { sort, .. } => sort,
                    };
                    return GenericPackedWitnessNode::Call {
                        span: schedule_span.clone(),
                        sort: sort.clone(),
                        function: (*name).to_owned(),
                        children: Box::new([]),
                    };
                }
                match &witnesses.nodes[witness.index()].node {
                    WitnessNode::Literal { sort, value } => GenericPackedWitnessNode::Literal {
                        span: schedule_span.clone(),
                        sort: sort.clone(),
                        value: value.clone(),
                    },
                    WitnessNode::App {
                        sort,
                        function,
                        children,
                    } => GenericPackedWitnessNode::Call {
                        span: schedule_span.clone(),
                        sort: sort.clone(),
                        function: function.clone(),
                        children: children
                            .iter()
                            .map(|child| witness_indices[child])
                            .collect::<Vec<_>>()
                            .into_boxed_slice(),
                    },
                }
            })
            .collect();
        shared_witnesses += witness_uses.values().filter(|uses| **uses > 1).count();
        let groups = group_indices
            .keys()
            .map(|rule_index| {
                let (rule_name, _) = rules
                    .get_index(*rule_index as usize)
                    .expect("captured compact replay rule index must remain valid");
                GenericPackedRuleGroup {
                    span: schedule_span.clone(),
                    rule: rule_name.clone(),
                    variables: group_variables[rule_index]
                        .iter()
                        .cloned()
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                }
            })
            .collect();
        let packed_fires = wave_fires
            .iter()
            .map(|fire| PackedRuleFire {
                span: schedule_span.clone(),
                group: group_indices[&fire.rule_index],
                witnesses: fire
                    .bindings
                    .iter()
                    .map(|witness| witness_indices[witness])
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
            })
            .collect();
        let replay = Command::RunSchedule(Schedule::RunRuleBatchPacked(
            schedule_span.clone(),
            GenericPackedRunRuleBatch {
                witnesses: GenericPackedWitnesses::Dag(packed_witnesses),
                groups,
                fires: packed_fires,
            },
        ));
        rendered.push_str(&replay.to_string());
        rendered.push('\n');
        start = end;
    }

    Ok((rendered, shared_witnesses))
}

fn collect_packed_witness_dag(
    witness: WitnessId,
    witnesses: &WitnessArena,
    global_names: &IndexMap<WitnessId, &str>,
    indices: &mut IndexMap<WitnessId, u32>,
) {
    if indices.contains_key(&witness) {
        return;
    }
    if !global_names.contains_key(&witness)
        && let WitnessNode::App { children, .. } = &witnesses.nodes[witness.index()].node
    {
        for child in children {
            collect_packed_witness_dag(*child, witnesses, global_names, indices);
        }
    }
    let index = u32::try_from(indices.len()).expect("packed witness DAG exceeded u32 capacity");
    indices.insert(witness, index);
}

fn emit_program<'a>(
    commands: &[Command],
    schedule_indices: &[usize],
    schedule_span: &Span,
    rules: &IndexMap<String, RuleModel>,
    fires: impl IntoIterator<Item = &'a GroundedFire>,
    witnesses: &WitnessArena,
    source_expansions: &SourceCommandExpansions,
) -> Result<(String, usize), CausalSliceError> {
    let (replay_commands, shared_replay_witnesses) =
        render_replay_commands(commands, schedule_span, rules, fires, witnesses)?;
    Ok((
        emit_program_with_replay_commands(
            commands,
            schedule_indices,
            &replay_commands,
            source_expansions,
        ),
        shared_replay_witnesses,
    ))
}

fn render_replay_commands<'a>(
    commands: &[Command],
    schedule_span: &Span,
    rules: &IndexMap<String, RuleModel>,
    fires: impl IntoIterator<Item = &'a GroundedFire>,
    witnesses: &WitnessArena,
) -> Result<(String, usize), CausalSliceError> {
    let compact = fires
        .into_iter()
        .map(|fire| {
            let rule_index = rules
                .get_index_of(&fire.rule)
                .expect("grounded replay rule was validated during modeling");
            let selector_variables = fire.selector_variables()?;
            let bindings = selector_variables
                .iter()
                .map(|variable| fire.bindings[variable].syntax)
                .collect::<Vec<_>>()
                .into_boxed_slice();
            Ok(CompactReplayFire {
                rule_index: u32::try_from(rule_index)
                    .expect("packed replay rule index exceeded u32 capacity"),
                wave: fire.wave,
                ordinal: fire.ordinal,
                bindings,
                selector_variables: Some(Arc::clone(selector_variables)),
            })
        })
        .collect::<Result<Vec<_>, CausalSliceError>>()?;
    emit_prefix_replay_commands(commands, schedule_span, rules, &compact, witnesses)
}

fn replay_witness_callables<'a>(
    fires: impl IntoIterator<Item = &'a GroundedFire>,
    witnesses: &WitnessArena,
) -> Result<IndexSet<String>, CausalSliceError> {
    let mut work = Vec::new();
    for fire in fires {
        work.extend(
            fire.selector_variables()?
                .iter()
                .map(|variable| fire.bindings[variable].syntax),
        );
    }

    let mut visited = HashSet::default();
    let mut callables = IndexSet::default();
    while let Some(witness) = work.pop() {
        if !visited.insert(witness) {
            continue;
        }
        if let WitnessNode::App {
            function, children, ..
        } = &witnesses.nodes[witness.index()].node
        {
            callables.insert(function.clone());
            work.extend(children.iter().copied());
        }
    }
    Ok(callables)
}

fn emit_program_with_replay_commands(
    commands: &[Command],
    schedule_indices: &[usize],
    replay_commands: &str,
    source_expansions: &SourceCommandExpansions,
) -> String {
    let mut replay_by_schedule = IndexMap::default();
    if let Some(first) = schedule_indices.first() {
        replay_by_schedule.insert(*first, replay_commands.to_owned());
    }
    emit_program_with_replay_regions(
        commands,
        schedule_indices,
        &replay_by_schedule,
        source_expansions,
    )
}

fn emit_program_with_replay_regions(
    commands: &[Command],
    schedule_indices: &[usize],
    replay_by_schedule: &IndexMap<usize, String>,
    source_expansions: &SourceCommandExpansions,
) -> String {
    let mut rendered = String::new();
    for (index, command) in commands.iter().enumerate() {
        if let Some(replay_commands) = replay_by_schedule.get(&index) {
            rendered.push_str(replay_commands);
        } else if schedule_indices.contains(&index) {
            // All automatic computation boundaries are removed. Unscoped
            // programs insert every traced wave at their first consecutive
            // boundary; scoped programs insert each transaction-local replay
            // at that transaction's own first boundary.
        } else if let Some(expansion) = source_expansions.get(&index) {
            for command in expansion {
                rendered.push_str(&command.to_string());
                rendered.push('\n');
            }
        } else {
            rendered.push_str(&command.to_string());
            rendered.push('\n');
        }
    }
    rendered
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum DefinitionRef {
    Sort(String),
    Callable(String),
    Ruleset(String),
    Rule(String),
    Global(String),
}

struct SourceDefinitionIndex {
    definitions: IndexMap<DefinitionRef, usize>,
    dependencies: Vec<IndexSet<DefinitionRef>>,
}

fn define_source_symbol(
    definitions: &mut IndexMap<DefinitionRef, usize>,
    symbol: DefinitionRef,
    command_index: usize,
) -> Result<(), CausalSliceError> {
    if let Some(previous) = definitions.insert(symbol.clone(), command_index)
        && previous != command_index
    {
        return Err(CausalSliceError::Invariant(format!(
            "source symbol {symbol:?} was defined by commands {previous} and {command_index}"
        )));
    }
    Ok(())
}

fn command_definitions(
    command: &Command,
    command_index: usize,
    definitions: &mut IndexMap<DefinitionRef, usize>,
) -> Result<(), CausalSliceError> {
    match command {
        Command::Sort { name, .. } => define_source_symbol(
            definitions,
            DefinitionRef::Sort(name.clone()),
            command_index,
        )?,
        Command::Datatype { name, variants, .. } => {
            define_source_symbol(
                definitions,
                DefinitionRef::Sort(name.clone()),
                command_index,
            )?;
            for variant in variants {
                define_source_symbol(
                    definitions,
                    DefinitionRef::Callable(variant.name.clone()),
                    command_index,
                )?;
            }
        }
        Command::Datatypes { datatypes, .. } => {
            for (_, name, subdatatype) in datatypes {
                define_source_symbol(
                    definitions,
                    DefinitionRef::Sort(name.clone()),
                    command_index,
                )?;
                if let Subdatatypes::Variants(variants) = subdatatype {
                    for variant in variants {
                        define_source_symbol(
                            definitions,
                            DefinitionRef::Callable(variant.name.clone()),
                            command_index,
                        )?;
                    }
                }
            }
        }
        Command::Constructor { name, .. }
        | Command::Relation { name, .. }
        | Command::Function { name, .. } => define_source_symbol(
            definitions,
            DefinitionRef::Callable(name.clone()),
            command_index,
        )?,
        Command::AddRuleset(_, name) | Command::UnstableCombinedRuleset(_, name, _) => {
            define_source_symbol(
                definitions,
                DefinitionRef::Ruleset(name.clone()),
                command_index,
            )?;
        }
        Command::Rule { rule } => define_source_symbol(
            definitions,
            DefinitionRef::Rule(rule.name.clone()),
            command_index,
        )?,
        Command::Action(Action::Let(_, name, _)) => define_source_symbol(
            definitions,
            DefinitionRef::Global(name.clone()),
            command_index,
        )?,
        Command::Rewrite(..)
        | Command::BiRewrite(..)
        | Command::Action(..)
        | Command::Extract(..)
        | Command::RunSchedule(..)
        | Command::PrintOverallStatistics(..)
        | Command::Check(..)
        | Command::Prove(..)
        | Command::ProveExists(..)
        | Command::PrintFunction(..)
        | Command::PrintSize(..)
        | Command::Input { .. }
        | Command::Output { .. }
        | Command::Push(..)
        | Command::Pop(..)
        | Command::Fail(..)
        | Command::Include(..)
        | Command::UserDefined(..) => {}
    }
    Ok(())
}

fn collect_expr_dependencies(
    expr: &Expr,
    known_globals: &HashSet<String>,
    dependencies: &mut IndexSet<DefinitionRef>,
) {
    match expr {
        Expr::Var(_, name) => {
            if known_globals.contains(name) {
                dependencies.insert(DefinitionRef::Global(name.clone()));
            }
        }
        Expr::Call(_, function, children) => {
            dependencies.insert(DefinitionRef::Callable(function.clone()));
            for child in children {
                collect_expr_dependencies(child, known_globals, dependencies);
            }
        }
        Expr::Lit(..) => {}
    }
}

fn collect_sort_expr_dependencies(expr: &Expr, dependencies: &mut IndexSet<DefinitionRef>) {
    match expr {
        Expr::Var(_, sort) => {
            dependencies.insert(DefinitionRef::Sort(sort.clone()));
        }
        Expr::Call(_, sort, children) => {
            dependencies.insert(DefinitionRef::Sort(sort.clone()));
            for child in children {
                collect_sort_expr_dependencies(child, dependencies);
            }
        }
        Expr::Lit(..) => {}
    }
}

fn collect_fact_dependencies(
    fact: &Fact,
    known_globals: &HashSet<String>,
    dependencies: &mut IndexSet<DefinitionRef>,
) {
    match fact {
        Fact::Fact(expr) => collect_expr_dependencies(expr, known_globals, dependencies),
        Fact::Eq(_, left, right) => {
            collect_expr_dependencies(left, known_globals, dependencies);
            collect_expr_dependencies(right, known_globals, dependencies);
        }
    }
}

fn collect_action_dependencies(
    action: &Action,
    known_globals: &HashSet<String>,
    dependencies: &mut IndexSet<DefinitionRef>,
) {
    match action {
        Action::Let(_, _, expression) | Action::Expr(_, expression) => {
            collect_expr_dependencies(expression, known_globals, dependencies);
        }
        Action::Set(_, function, keys, value) => {
            dependencies.insert(DefinitionRef::Callable(function.clone()));
            for key in keys {
                collect_expr_dependencies(key, known_globals, dependencies);
            }
            collect_expr_dependencies(value, known_globals, dependencies);
        }
        Action::Change(_, _, function, keys) => {
            dependencies.insert(DefinitionRef::Callable(function.clone()));
            for key in keys {
                collect_expr_dependencies(key, known_globals, dependencies);
            }
        }
        Action::Union(_, left, right) => {
            collect_expr_dependencies(left, known_globals, dependencies);
            collect_expr_dependencies(right, known_globals, dependencies);
        }
        Action::Panic(..) => {}
    }
}

fn collect_schema_dependencies(
    schema: &crate::ast::Schema,
    dependencies: &mut IndexSet<DefinitionRef>,
) {
    dependencies.extend(
        schema
            .input
            .iter()
            .chain(&schema.outputs)
            .cloned()
            .map(DefinitionRef::Sort),
    );
}

fn command_dependencies(
    command: &Command,
    known_globals: &HashSet<String>,
) -> IndexSet<DefinitionRef> {
    let mut dependencies = IndexSet::default();
    match command {
        Command::Sort {
            presort_and_args, ..
        } => {
            if let Some((presort, args)) = presort_and_args {
                dependencies.insert(DefinitionRef::Sort(presort.clone()));
                for arg in args {
                    collect_sort_expr_dependencies(arg, &mut dependencies);
                }
            }
        }
        Command::Datatype { variants, .. } => {
            dependencies.extend(
                variants
                    .iter()
                    .flat_map(|variant| &variant.types)
                    .cloned()
                    .map(DefinitionRef::Sort),
            );
        }
        Command::Datatypes { datatypes, .. } => {
            for (_, _, subdatatype) in datatypes {
                match subdatatype {
                    Subdatatypes::Variants(variants) => dependencies.extend(
                        variants
                            .iter()
                            .flat_map(|variant| &variant.types)
                            .cloned()
                            .map(DefinitionRef::Sort),
                    ),
                    Subdatatypes::NewSort(presort, args) => {
                        dependencies.insert(DefinitionRef::Sort(presort.clone()));
                        for arg in args {
                            collect_sort_expr_dependencies(arg, &mut dependencies);
                        }
                    }
                }
            }
        }
        Command::Constructor {
            schema,
            term_constructor,
            ..
        }
        | Command::Function {
            schema,
            term_constructor,
            ..
        } => {
            collect_schema_dependencies(schema, &mut dependencies);
            if let Some(constructor) = term_constructor {
                dependencies.insert(DefinitionRef::Callable(constructor.clone()));
            }
            if let Command::Function {
                merge: Some(merge), ..
            } = command
            {
                for action in &merge.actions.0 {
                    collect_action_dependencies(action, known_globals, &mut dependencies);
                }
                collect_expr_dependencies(&merge.result, known_globals, &mut dependencies);
            }
        }
        Command::Relation { inputs, .. } => {
            dependencies.extend(inputs.iter().cloned().map(DefinitionRef::Sort))
        }
        Command::UnstableCombinedRuleset(_, _, members) => {
            dependencies.extend(members.iter().cloned().map(DefinitionRef::Ruleset))
        }
        Command::Rule { rule } => {
            if !rule.ruleset.is_empty() {
                dependencies.insert(DefinitionRef::Ruleset(rule.ruleset.clone()));
            }
            for fact in &rule.body {
                collect_fact_dependencies(fact, known_globals, &mut dependencies);
            }
            for action in &rule.head.0 {
                collect_action_dependencies(action, known_globals, &mut dependencies);
            }
        }
        Command::Rewrite(_, rewrite, _) | Command::BiRewrite(_, rewrite) => {
            collect_expr_dependencies(&rewrite.lhs, known_globals, &mut dependencies);
            collect_expr_dependencies(&rewrite.rhs, known_globals, &mut dependencies);
            for fact in &rewrite.conditions {
                collect_fact_dependencies(fact, known_globals, &mut dependencies);
            }
        }
        Command::Action(action) => {
            collect_action_dependencies(action, known_globals, &mut dependencies)
        }
        Command::Extract(_, expression, variants) => {
            collect_expr_dependencies(expression, known_globals, &mut dependencies);
            collect_expr_dependencies(variants, known_globals, &mut dependencies);
        }
        Command::Check(_, facts) | Command::Prove(_, facts) => {
            for fact in facts {
                collect_fact_dependencies(fact, known_globals, &mut dependencies);
            }
        }
        Command::PrintFunction(_, function, ..) => {
            dependencies.insert(DefinitionRef::Callable(function.clone()));
        }
        Command::Input { name, .. } => {
            dependencies.insert(DefinitionRef::Callable(name.clone()));
        }
        Command::Output { exprs, .. } | Command::UserDefined(_, _, exprs) => {
            for expr in exprs {
                collect_expr_dependencies(expr, known_globals, &mut dependencies);
            }
        }
        Command::Fail(_, inner) => dependencies.extend(command_dependencies(inner, known_globals)),
        Command::AddRuleset(..)
        | Command::RunSchedule(..)
        | Command::PrintOverallStatistics(..)
        | Command::ProveExists(..)
        | Command::PrintSize(..)
        | Command::Push(..)
        | Command::Pop(..)
        | Command::Include(..) => {}
    }
    dependencies
}

fn build_source_definition_index(
    commands: &[Command],
) -> Result<SourceDefinitionIndex, CausalSliceError> {
    let mut definitions = IndexMap::default();
    for (command_index, command) in commands.iter().enumerate() {
        command_definitions(command, command_index, &mut definitions)?;
    }
    let known_globals = definitions
        .keys()
        .filter_map(|definition| match definition {
            DefinitionRef::Global(name) => Some(name.clone()),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let dependencies = commands
        .iter()
        .map(|command| command_dependencies(command, &known_globals))
        .collect();
    Ok(SourceDefinitionIndex {
        definitions,
        dependencies,
    })
}

fn close_source_dependencies(
    index: &SourceDefinitionIndex,
    mut retained_commands: IndexSet<usize>,
    seed_refs: impl IntoIterator<Item = DefinitionRef>,
) -> IndexSet<usize> {
    let mut work = retained_commands.iter().copied().collect::<Vec<_>>();
    let mut pending_refs = seed_refs.into_iter().collect::<Vec<_>>();
    loop {
        while let Some(reference) = pending_refs.pop() {
            if let Some(command_index) = index.definitions.get(&reference)
                && retained_commands.insert(*command_index)
            {
                work.push(*command_index);
            }
        }
        let Some(command_index) = work.pop() else {
            break;
        };
        pending_refs.extend(index.dependencies[command_index].iter().cloned());
    }
    retained_commands.sort_unstable();
    retained_commands
}

struct RetainedProofSource<'a> {
    facts: &'a [SourceFact],
    fact_ids: &'a IndexSet<SourceFactId>,
    rule_names: &'a IndexSet<String>,
    witness_callables: &'a IndexSet<String>,
}

fn emit_proof_program_with_replay_regions(
    commands: &[Command],
    schedule_indices: &[usize],
    replay_by_schedule: &IndexMap<usize, String>,
    source_expansions: &SourceCommandExpansions,
    retained: RetainedProofSource<'_>,
) -> Result<String, CausalSliceError> {
    let index = build_source_definition_index(commands)?;
    let mut retained_commands = IndexSet::default();
    let mut seed_refs = retained
        .rule_names
        .iter()
        .cloned()
        .map(DefinitionRef::Rule)
        .collect::<IndexSet<_>>();
    seed_refs.extend(
        retained
            .witness_callables
            .iter()
            .cloned()
            .map(DefinitionRef::Callable),
    );
    for (command_index, command) in commands.iter().enumerate() {
        if matches!(
            command,
            Command::Check(..) | Command::Push(..) | Command::Pop(..)
        ) {
            retained_commands.insert(command_index);
        }
    }
    for fact in retained.facts {
        if !retained.fact_ids.contains(&fact.id) {
            continue;
        }
        if fact.expansion_index.is_none() {
            retained_commands.insert(fact.command_index);
        } else if let SourceFactKind::Relation(atom) = &fact.kind {
            seed_refs.insert(DefinitionRef::Callable(atom.relation.clone()));
        }
    }
    let retained_commands = close_source_dependencies(&index, retained_commands, seed_refs);

    let mut rendered = String::new();
    for (command_index, command) in commands.iter().enumerate() {
        if let Some(replay_commands) = replay_by_schedule.get(&command_index) {
            rendered.push_str(replay_commands);
            continue;
        }
        if schedule_indices.contains(&command_index) {
            continue;
        }
        if let Some(expansion) = source_expansions.get(&command_index) {
            for fact in retained.facts.iter().filter(|fact| {
                fact.command_index == command_index && retained.fact_ids.contains(&fact.id)
            }) {
                let expansion_index = fact.expansion_index.ok_or_else(|| {
                    CausalSliceError::Invariant(format!(
                        "input source fact {:?} lost its expansion index",
                        fact.id
                    ))
                })?;
                let selected = expansion.get(expansion_index).ok_or_else(|| {
                    CausalSliceError::Invariant(format!(
                        "input source fact {:?} referenced missing expansion {expansion_index}",
                        fact.id
                    ))
                })?;
                rendered.push_str(&selected.to_string());
                rendered.push('\n');
            }
            continue;
        }
        if !retained_commands.contains(&command_index) {
            continue;
        }
        if matches!(
            command,
            Command::PrintSize(..) | Command::PrintOverallStatistics(..)
        ) {
            continue;
        }
        rendered.push_str(&command.to_string());
        rendered.push('\n');
    }
    Ok(rendered)
}

fn filter_rule_mapping(
    mapping: &[SourceRuleMapping],
    source_projection: ReplaySourceProjection,
    retained_rule_names: &IndexSet<String>,
) -> Vec<SourceRuleMapping> {
    mapping
        .iter()
        .filter(|entry| {
            source_projection == ReplaySourceProjection::Legacy
                || retained_rule_names.contains(&entry.registered_name)
        })
        .cloned()
        .collect()
}

fn validate_emitted_program(
    template: &EGraph,
    filename: Option<String>,
    source: &str,
    rules: &IndexMap<String, RuleModel>,
    mapping: &[SourceRuleMapping],
    typecheck: bool,
) -> Result<(), CausalSliceError> {
    let mut parser = template.clone();
    let parsed = parser.parse_program(filename.clone(), source)?;
    let mut emitted_rules = HashMap::default();
    let mut replay_globals = HashSet::default();
    for command in &parsed {
        match command {
            Command::RunSchedule(schedule) => {
                validate_replay_schedule(schedule, rules, &replay_globals)?
            }
            Command::Rule { rule } => {
                emitted_rules.insert(rule.name.as_str(), semantic_rule_definition(rule));
            }
            Command::Action(Action::Let(span, name, expression)) => {
                if name.starts_with(SHARED_REPLAY_WITNESS_PREFIX) {
                    validate_closed_replay_witness(expression, span, &replay_globals)?;
                }
                replay_globals.insert(name.clone());
            }
            Command::Include(span, _) => {
                return unsupported(span, "an include in emitted source".to_owned());
            }
            _ => {}
        }
    }
    for entry in mapping {
        let actual = emitted_rules
            .get(entry.registered_name.as_str())
            .ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "emitted source omitted rule `{}`",
                    entry.registered_name
                ))
            })?;
        if *actual != entry.semantic_definition {
            return Err(CausalSliceError::Invariant(format!(
                "emitted definition for `{}` differs from its source mapping",
                entry.registered_name
            )));
        }
    }
    if typecheck {
        let mut resolver = template.clone();
        resolver.resolve_program(filename, source)?;
    }
    // Proof-oriented projection additionally resolves and typechecks every
    // retained declaration and replay witness. The egglog pretty printer is
    // not generally a fixed point, so requiring a second rendering to be
    // byte-identical would reject valid emitted programs. Determinism is
    // instead tested across independent slicer executions, while unstable
    // scalar literal spellings are rejected before emission.
    Ok(())
}

fn validate_replay_schedule(
    schedule: &Schedule,
    rules: &IndexMap<String, RuleModel>,
    replay_globals: &HashSet<String>,
) -> Result<(), CausalSliceError> {
    match schedule {
        Schedule::RunRule(span, config) => {
            validate_replay_run_rule(span, config, rules, replay_globals)
        }
        Schedule::RunRuleBatch(span, configs) => {
            for config in configs {
                validate_replay_run_rule(span, config, rules, replay_globals)?;
            }
            Ok(())
        }
        Schedule::RunRuleBatchPacked(span, batch) => {
            validate_replay_packed_batch(span, batch, rules, replay_globals)
        }
        Schedule::Sequence(_, schedules) => {
            for schedule in schedules {
                validate_replay_schedule(schedule, rules, replay_globals)?;
            }
            Ok(())
        }
        Schedule::Run(span, _) | Schedule::Repeat(span, _, _) | Schedule::Saturate(span, _) => {
            unsupported(
                span,
                "an automatic run, repeat, or saturate node in emitted source".to_owned(),
            )
        }
    }
}

fn validate_replay_run_rule(
    span: &Span,
    config: &RunRuleConfig,
    rules: &IndexMap<String, RuleModel>,
    replay_globals: &HashSet<String>,
) -> Result<(), CausalSliceError> {
    if config.expect != Some(1) {
        return unsupported(span, "a replay leaf without `:expect 1`".to_owned());
    }
    if !config.selectors.is_empty() {
        return unsupported(span, "internal replay selectors".to_owned());
    }
    let model = rules.get(&config.rule).ok_or_else(|| {
        CausalSliceError::Invariant(format!("replay references unknown rule `{}`", config.rule))
    })?;
    let names = config
        .bindings
        .iter()
        .map(|(name, _)| name.as_str())
        .collect::<Vec<_>>();
    let expected = model
        .replay_var_order
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>();
    if !is_ordered_subsequence(&names, &expected) {
        return Err(CausalSliceError::Invariant(format!(
            "replay binding list for `{}` was {names:?}, which is not an ordered subset of {expected:?}",
            config.rule,
        )));
    }
    for (_, expr) in &config.bindings {
        validate_closed_replay_witness(expr, span, replay_globals)?;
    }
    Ok(())
}

fn validate_replay_packed_batch(
    span: &Span,
    batch: &crate::ast::PackedRunRuleBatch,
    rules: &IndexMap<String, RuleModel>,
    replay_globals: &HashSet<String>,
) -> Result<(), CausalSliceError> {
    let witness_count = match &batch.witnesses {
        GenericPackedWitnesses::Expressions(witnesses) => {
            for witness in witnesses {
                validate_closed_replay_witness(witness, span, replay_globals)?;
            }
            witnesses.len()
        }
        GenericPackedWitnesses::Dag(witnesses) => {
            let mut uses = vec![0usize; witnesses.len()];
            for (index, witness) in witnesses.iter().enumerate() {
                if let GenericPackedWitnessNode::Call { children, .. } = witness {
                    for child in children {
                        let child = *child as usize;
                        if child >= index {
                            return Err(CausalSliceError::Invariant(format!(
                                "packed replay witness {index} references non-prior child {child}"
                            )));
                        }
                        uses[child] += 1;
                    }
                }
            }
            for fire in batch.fires.iter() {
                for witness in &fire.witnesses {
                    let Some(uses) = uses.get_mut(*witness as usize) else {
                        return Err(CausalSliceError::Invariant(
                            "packed replay fire has invalid witness indices".to_owned(),
                        ));
                    };
                    *uses += 1;
                }
            }
            if let Some(unreachable) = uses.iter().position(|uses| *uses == 0) {
                return Err(CausalSliceError::Invariant(format!(
                    "packed replay witness {unreachable} is unreachable from every fire"
                )));
            }
            witnesses.len()
        }
    };
    for group in &batch.groups {
        let model = rules.get(&group.rule).ok_or_else(|| {
            CausalSliceError::Invariant(format!(
                "packed replay references unknown rule `{}`",
                group.rule
            ))
        })?;
        let actual = group
            .variables
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>();
        let expected = model
            .replay_var_order
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>();
        if !is_ordered_subsequence(&actual, &expected) {
            return Err(CausalSliceError::Invariant(format!(
                "packed replay variables for `{}` were {actual:?}, expected an ordered subset of {expected:?}",
                group.rule
            )));
        }
    }
    for fire in batch.fires.iter() {
        let Some(group) = batch.groups.get(fire.group as usize) else {
            return Err(CausalSliceError::Invariant(format!(
                "packed replay references unknown group {}",
                fire.group
            )));
        };
        if fire.witnesses.len() != group.variables.len()
            || fire
                .witnesses
                .iter()
                .any(|witness| *witness as usize >= witness_count)
        {
            return Err(CausalSliceError::Invariant(
                "packed replay fire has invalid witness indices".to_owned(),
            ));
        }
    }
    Ok(())
}

fn is_ordered_subsequence(actual: &[&str], expected: &[&str]) -> bool {
    let mut expected = expected.iter();
    actual
        .iter()
        .all(|actual| expected.by_ref().any(|expected| expected == actual))
}

fn validate_closed_replay_witness(
    expr: &Expr,
    span: &Span,
    replay_globals: &HashSet<String>,
) -> Result<(), CausalSliceError> {
    match expr {
        GenericExpr::Lit(..) => Ok(()),
        GenericExpr::Call(_, _, args) => {
            for arg in args {
                validate_closed_replay_witness(arg, span, replay_globals)?;
            }
            Ok(())
        }
        GenericExpr::Var(_, var) if replay_globals.contains(var) => Ok(()),
        GenericExpr::Var(_, var) => unsupported(
            span,
            format!("a replay witness containing free variable `{var}`"),
        ),
    }
}

fn semantic_rule_definition(rule: &crate::ast::Rule) -> String {
    let body = rule
        .body
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(" ");
    let head = rule
        .head
        .0
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(" ");
    format!(
        "ruleset={};eval={:?};include_subsumed={};no_decomp={};body=({body});head={}",
        rule.ruleset, rule.eval_mode, rule.include_subsumed, rule.no_decomp, head
    )
}

fn command_schedule_span(command: &Command) -> Option<Span> {
    let Command::RunSchedule(schedule) = command else {
        return None;
    };
    Some(match schedule {
        Schedule::Run(span, _)
        | Schedule::RunRule(span, _)
        | Schedule::RunRuleBatch(span, _)
        | Schedule::RunRuleBatchPacked(span, _)
        | Schedule::Repeat(span, _, _)
        | Schedule::Saturate(span, _)
        | Schedule::Sequence(span, _) => span.clone(),
    })
}

fn display_row(row: &RowKey) -> String {
    if row.args.is_empty() {
        format!("({})", row.relation)
    } else {
        let args = row
            .args
            .iter()
            .map(|endpoint| format!("<{}>", endpoint.sort))
            .collect::<Vec<_>>()
            .join(" ");
        format!("({} {args})", row.relation)
    }
}

fn validate_printable_literal(span: &Span, literal: &Literal) -> Result<(), CausalSliceError> {
    if literal_is_source_stable(literal) {
        Ok(())
    } else {
        unsupported(
            span,
            "a String literal containing a quote, backslash, or control character (the current source printer cannot round-trip it)",
        )
    }
}

fn literal_is_source_stable(literal: &Literal) -> bool {
    match literal {
        Literal::String(value) => source_string_is_stable(value),
        _ => true,
    }
}

fn source_string_is_stable(value: &str) -> bool {
    !value
        .chars()
        .any(|character| character == '"' || character == '\\' || character.is_control())
}

fn unsupported<T>(span: &Span, reason: impl Into<String>) -> Result<T, CausalSliceError> {
    Err(CausalSliceError::Unsupported {
        location: span.to_string(),
        reason: reason.into(),
    })
}

fn unsupported_action<T>(
    action: &Action,
    reason: impl Into<String>,
) -> Result<T, CausalSliceError> {
    let span = match action {
        GenericAction::Let(span, ..)
        | GenericAction::Set(span, ..)
        | GenericAction::Change(span, ..)
        | GenericAction::Union(span, ..)
        | GenericAction::Panic(span, ..)
        | GenericAction::Expr(span, ..) => span,
    };
    unsupported(span, reason)
}

fn unsupported_command<T>(
    command: &Command,
    index: usize,
    source_name: &str,
    reason: impl Into<String>,
) -> Result<T, CausalSliceError> {
    let location = match command {
        Command::Relation { span, .. }
        | Command::Function { span, .. }
        | Command::Constructor { span, .. }
        | Command::Datatype { span, .. }
        | Command::Datatypes { span, .. }
        | Command::Sort { span, .. }
        | Command::Input { span, .. }
        | Command::Output { span, .. } => span.to_string(),
        Command::AddRuleset(span, _)
        | Command::UnstableCombinedRuleset(span, ..)
        | Command::Extract(span, ..)
        | Command::Check(span, ..)
        | Command::Prove(span, ..)
        | Command::ProveExists(span, ..)
        | Command::PrintOverallStatistics(span, ..)
        | Command::PrintFunction(span, ..)
        | Command::PrintSize(span, ..)
        | Command::Pop(span, ..)
        | Command::Fail(span, ..)
        | Command::Include(span, ..)
        | Command::UserDefined(span, ..) => span.to_string(),
        Command::Rule { rule } => rule.span.to_string(),
        Command::Rewrite(_, rewrite, _) | Command::BiRewrite(_, rewrite) => {
            rewrite.span.to_string()
        }
        Command::Action(action) => match action {
            GenericAction::Let(span, ..)
            | GenericAction::Set(span, ..)
            | GenericAction::Change(span, ..)
            | GenericAction::Union(span, ..)
            | GenericAction::Panic(span, ..)
            | GenericAction::Expr(span, ..) => span.to_string(),
        },
        Command::RunSchedule(schedule) => {
            command_schedule_span(&Command::RunSchedule(schedule.clone()))
                .map(|span| span.to_string())
                .unwrap_or_else(|| format!("{source_name}: top-level command {index}"))
        }
        Command::Push(_) => format!("{source_name}: top-level command {index}"),
    };
    Err(CausalSliceError::Unsupported {
        location,
        reason: reason.into(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_index_matches_linear(
        witnesses: &WitnessArena,
        expected: &WitnessNode,
        output: Value,
        equality_forest: &EqualityForest,
        snapshot: Option<&WitnessSnapshot>,
        app_index: &mut WaveAppIndex,
        initial_dependencies: &DepArena,
    ) -> Option<DepId> {
        let mut indexed_dependencies = initial_dependencies.clone();
        let indexed = congruent_app_availability(
            witnesses,
            expected,
            output,
            equality_forest,
            &mut indexed_dependencies,
            snapshot,
            app_index,
        )
        .unwrap();
        let mut linear_dependencies = initial_dependencies.clone();
        let linear = congruent_app_availability_linear(
            witnesses,
            expected,
            output,
            equality_forest,
            &mut linear_dependencies,
            snapshot,
        )
        .unwrap();
        assert_eq!(indexed, linear);
        assert_eq!(indexed_dependencies, linear_dependencies);
        indexed
    }

    #[test]
    fn replay_witness_callables_include_nested_applications() {
        let mut witnesses = WitnessArena::default();
        let inner = witnesses
            .intern_syntax_app("InnerSort", "Inner", Vec::new())
            .unwrap();
        let outer = witnesses
            .intern_syntax_app("OuterSort", "Outer", vec![inner])
            .unwrap();
        let mut bindings = IndexMap::default();
        bindings.insert(
            "x".to_owned(),
            BindingWitness {
                syntax: outer,
                endpoint: EGraph::default().base_to_value(1_i64),
            },
        );
        let fire = GroundedFire {
            rule: "nested".to_owned(),
            wave: 0,
            ordinal: 0,
            bindings,
            selector: ReplaySelector::Key(Arc::from(["x".to_owned()])),
        };
        let mut rules = IndexMap::default();
        rules.insert(
            "nested".to_owned(),
            RuleModel {
                span: Span::Panic,
                body: Vec::new(),
                body_equalities: Vec::new(),
                body_lookups: Vec::new(),
                body_functions: Vec::new(),
                body_primitives: Vec::new(),
                head_lets: Vec::new(),
                head: Vec::new(),
                head_constructors: Vec::new(),
                head_sets: Vec::new(),
                head_subsumes: Vec::new(),
                head_primitives: Vec::new(),
                head_unions: Vec::new(),
                var_order: vec!["x".to_owned()],
                replay_var_order: vec!["x".to_owned()],
                derived_replay_aliases: IndexMap::default(),
                var_sorts: IndexMap::default(),
                global_uses: IndexMap::default(),
                opaque: None,
            },
        );

        assert_eq!(
            replay_witness_callables([&fire], &witnesses)
                .unwrap()
                .into_iter()
                .collect::<Vec<_>>(),
            ["Outer", "Inner"]
        );
    }

    #[test]
    fn replay_key_planning_projects_ambiguous_syntax_and_counts_no_ops_and_prefix_rows() {
        let mut egraph = EGraph::default();
        egraph.parse_and_run_program(None, "(sort Expr)").unwrap();
        let mut witnesses = WitnessArena::default();
        let one = witnesses.intern_literal("i64", Literal::Int(1)).unwrap();
        let two = witnesses.intern_literal("i64", Literal::Int(2)).unwrap();
        let first_endpoint = egraph.base_to_value(101_i64);
        let second_endpoint = egraph.base_to_value(102_i64);
        let first_expr = witnesses
            .intern_app(
                "Expr",
                "A",
                vec![one],
                first_endpoint,
                DepArena::EMPTY,
                true,
            )
            .unwrap();
        let second_expr = witnesses
            .intern_app(
                "Expr",
                "A",
                vec![one],
                second_endpoint,
                DepArena::EMPTY,
                true,
            )
            .unwrap();
        assert_eq!(
            witnesses.nodes[first_expr.index()].syntax,
            witnesses.nodes[second_expr.index()].syntax
        );

        let mut var_sorts = IndexMap::default();
        var_sorts.insert("x".to_owned(), "i64".to_owned());
        var_sorts.insert("e".to_owned(), "Expr".to_owned());
        let mut rules = IndexMap::default();
        rules.insert(
            "copy".to_owned(),
            RuleModel {
                span: crate::span!(),
                body: Vec::new(),
                body_equalities: Vec::new(),
                body_lookups: Vec::new(),
                body_functions: Vec::new(),
                body_primitives: Vec::new(),
                head_lets: Vec::new(),
                head: Vec::new(),
                head_constructors: Vec::new(),
                head_sets: Vec::new(),
                head_subsumes: Vec::new(),
                head_primitives: Vec::new(),
                head_unions: Vec::new(),
                var_order: vec!["x".to_owned(), "e".to_owned()],
                replay_var_order: vec!["x".to_owned(), "e".to_owned()],
                derived_replay_aliases: IndexMap::default(),
                var_sorts,
                global_uses: IndexMap::default(),
                opaque: None,
            },
        );

        let grounding = |x: i64, syntax: WitnessId, endpoint: Value| {
            let mut bindings = IndexMap::default();
            bindings.insert(
                "x".to_owned(),
                BindingWitness {
                    syntax: if x == 1 { one } else { two },
                    endpoint: egraph.base_to_value(x),
                },
            );
            bindings.insert("e".to_owned(), BindingWitness { syntax, endpoint });
            GroundedFire {
                rule: "copy".to_owned(),
                wave: 0,
                ordinal: 0,
                bindings,
                selector: ReplaySelector::Unplanned,
            }
        };
        let prestate_witness_count = witnesses.nodes.len();

        let mut distinct = vec![
            PendingFire {
                grounding: grounding(1, first_expr, first_endpoint),
                effective: true,
            },
            PendingFire {
                grounding: grounding(2, second_expr, second_endpoint),
                effective: true,
            },
        ];
        assign_wave_replay_selectors(ReplaySelectorPlanningInput {
            egraph: &egraph,
            rules: &rules,
            witnesses: &witnesses,
            prestate_witness_count,
            equality_forest: &EqualityForest::default(),
            wave: 0,
            pending_fires: &mut distinct,
            current_start: 0,
            events: &mut [],
        })
        .unwrap();
        for pending in &distinct {
            let ReplaySelector::Key(variables) = &pending.grounding.selector else {
                panic!("distinct scalar bindings should form a packed replay key")
            };
            assert_eq!(variables.as_ref(), ["x"]);
        }

        let mut colliding_no_op = vec![
            PendingFire {
                grounding: grounding(1, first_expr, first_endpoint),
                effective: true,
            },
            PendingFire {
                grounding: grounding(1, second_expr, second_endpoint),
                effective: false,
            },
        ];
        assign_wave_replay_selectors(ReplaySelectorPlanningInput {
            egraph: &egraph,
            rules: &rules,
            witnesses: &witnesses,
            prestate_witness_count,
            equality_forest: &EqualityForest::default(),
            wave: 0,
            pending_fires: &mut colliding_no_op,
            current_start: 0,
            events: &mut [],
        })
        .unwrap();
        assert!(
            colliding_no_op.iter().all(|pending| matches!(
                pending.grounding.selector,
                ReplaySelector::Unsupported(_)
            ))
        );

        let repeated = grounding(1, first_expr, first_endpoint);
        let mut repeated_prefix = vec![
            PendingFire {
                grounding: GroundedFire {
                    selector: ReplaySelector::Key(Arc::from(["x".to_owned()])),
                    ..repeated.clone()
                },
                effective: true,
            },
            PendingFire {
                grounding: GroundedFire {
                    wave: 1,
                    selector: ReplaySelector::Unplanned,
                    ..repeated
                },
                effective: false,
            },
        ];
        assign_wave_replay_selectors(ReplaySelectorPlanningInput {
            egraph: &egraph,
            rules: &rules,
            witnesses: &witnesses,
            prestate_witness_count,
            equality_forest: &EqualityForest::default(),
            wave: 1,
            pending_fires: &mut repeated_prefix,
            current_start: 1,
            events: &mut [],
        })
        .unwrap();
        assert!(matches!(
            &repeated_prefix[1].grounding.selector,
            ReplaySelector::Key(variables) if variables.as_ref() == ["x"]
        ));
    }

    #[test]
    fn proof_projection_validation_rejects_unknown_closed_calls() {
        let source = "(relation Goal ())\n(Missing 1)\n";
        let rules = IndexMap::default();
        assert!(
            validate_emitted_program(&EGraph::default(), None, source, &rules, &[], false).is_ok()
        );
        assert!(
            validate_emitted_program(&EGraph::default(), None, source, &rules, &[], true).is_err()
        );
    }

    #[test]
    fn untyped_committed_union_still_advances_raw_canonical_state() {
        let egraph = EGraph::default();
        let parent = egraph.base_to_value(101_i64);
        let skipped_child = egraph.base_to_value(102_i64);
        let typed_child = egraph.base_to_value(103_i64);
        let skipped = UnionReceipt {
            origin: None,
            lhs: parent,
            rhs: skipped_child,
            outcome: UnionOutcome::Applied {
                parent,
                child: skipped_child,
            },
        };
        let typed = UnionReceipt {
            origin: None,
            lhs: typed_child,
            rhs: skipped_child,
            outcome: UnionOutcome::Applied {
                parent,
                child: typed_child,
            },
        };

        let mut forest = EqualityForest::default();
        // The first receipt deliberately has no typed explanation edge. It
        // must nevertheless update the commit-order union-find state.
        forest.observe_receipt(&skipped).unwrap();
        forest.observe_receipt(&typed).unwrap();
        forest
            .add_explanation(
                AppliedEquality {
                    left: TypedEndpoint {
                        sort: "Expr".to_owned(),
                        value: typed_child,
                    },
                    right: TypedEndpoint {
                        sort: "Expr".to_owned(),
                        value: skipped_child,
                    },
                    parent,
                    child: typed_child,
                    commit_ordinal: 1,
                },
                DepArena::EMPTY,
            )
            .unwrap();

        assert_eq!(forest.canonical_value(skipped_child), parent);
        assert_eq!(forest.canonical_value(typed_child), parent);
        assert_eq!(forest.raw_parent_count(), 2);
        assert_eq!(forest.edge_count(), 1);
        assert_eq!(
            forest.explain(
                &TypedEndpoint {
                    sort: "Expr".to_owned(),
                    value: typed_child,
                },
                &TypedEndpoint {
                    sort: "Expr".to_owned(),
                    value: parent,
                },
            ),
            Some(vec![DepArena::EMPTY])
        );
        assert_eq!(
            forest.explain(
                &TypedEndpoint {
                    sort: "Expr".to_owned(),
                    value: typed_child,
                },
                &TypedEndpoint {
                    sort: "Expr".to_owned(),
                    value: skipped_child,
                },
            ),
            None,
            "the untyped edge must remain an explicit fail-closed boundary"
        );
    }

    #[test]
    fn witness_snapshot_excludes_an_old_syntax_bound_after_wave_start() {
        let mut witnesses = WitnessArena::default();
        let syntax = witnesses
            .intern_syntax_app("Expr", "A", Vec::new())
            .unwrap();
        let snapshot = witnesses.snapshot();
        let endpoint = EGraph::default().base_to_value(7_i64);

        witnesses.bind_endpoint("Expr", endpoint, syntax).unwrap();
        assert_eq!(witnesses.by_endpoint("Expr", endpoint), Some(syntax));
        assert_eq!(
            witnesses.by_endpoint_at("Expr", endpoint, Some(&snapshot)),
            None
        );

        let expected = witnesses.nodes[syntax.index()].node.clone();
        let equality_forest = EqualityForest::default();
        let mut app_index = WaveAppIndex::default();
        assert_eq!(
            assert_index_matches_linear(
                &witnesses,
                &expected,
                endpoint,
                &equality_forest,
                Some(&snapshot),
                &mut app_index,
                &DepArena::default(),
            ),
            None
        );
        assert_eq!(
            assert_index_matches_linear(
                &witnesses,
                &expected,
                endpoint,
                &equality_forest,
                None,
                &mut app_index,
                &DepArena::default(),
            ),
            Some(DepArena::EMPTY)
        );
    }

    #[test]
    fn wave_app_index_preserves_snapshot_and_reverse_candidate_choice() {
        let egraph = EGraph::default();
        let first_child_endpoint = egraph.base_to_value(21_i64);
        let second_child_endpoint = egraph.base_to_value(22_i64);
        let output = egraph.base_to_value(23_i64);
        let mut dependencies = DepArena::default();
        let first_dependency = dependencies.event(EventId(0)).unwrap();
        let second_dependency = dependencies.event(EventId(1)).unwrap();
        let equality_dependency = dependencies.event(EventId(2)).unwrap();
        let mut witnesses = WitnessArena::default();
        let first_child = witnesses
            .intern_app(
                "Expr",
                "Leaf",
                Vec::new(),
                first_child_endpoint,
                DepArena::EMPTY,
                true,
            )
            .unwrap();
        witnesses
            .intern_app(
                "Expr",
                "A",
                vec![first_child],
                output,
                first_dependency,
                true,
            )
            .unwrap();
        let snapshot = witnesses.snapshot();
        let second_child = witnesses
            .intern_app(
                "Expr",
                "Leaf",
                Vec::new(),
                second_child_endpoint,
                DepArena::EMPTY,
                true,
            )
            .unwrap();
        let mut equality_forest = EqualityForest::default();
        let receipt = UnionReceipt {
            origin: None,
            lhs: first_child_endpoint,
            rhs: second_child_endpoint,
            outcome: UnionOutcome::Applied {
                parent: first_child_endpoint,
                child: second_child_endpoint,
            },
        };
        equality_forest.observe_receipt(&receipt).unwrap();
        equality_forest
            .add_explanation(
                AppliedEquality {
                    left: TypedEndpoint {
                        sort: "Expr".to_owned(),
                        value: first_child_endpoint,
                    },
                    right: TypedEndpoint {
                        sort: "Expr".to_owned(),
                        value: second_child_endpoint,
                    },
                    parent: first_child_endpoint,
                    child: second_child_endpoint,
                    commit_ordinal: 0,
                },
                equality_dependency,
            )
            .unwrap();
        let expected = WitnessNode::App {
            sort: "Expr".to_owned(),
            function: "A".to_owned(),
            children: vec![second_child],
        };
        let mut app_index = WaveAppIndex::default();

        let first_result = assert_index_matches_linear(
            &witnesses,
            &expected,
            output,
            &equality_forest,
            Some(&snapshot),
            &mut app_index,
            &dependencies,
        );
        assert!(first_result.is_some());
        witnesses
            .intern_app(
                "Expr",
                "A",
                vec![second_child],
                output,
                second_dependency,
                true,
            )
            .unwrap();

        let snapshot_result = assert_index_matches_linear(
            &witnesses,
            &expected,
            output,
            &equality_forest,
            Some(&snapshot),
            &mut app_index,
            &dependencies,
        );
        let current_result = assert_index_matches_linear(
            &witnesses,
            &expected,
            output,
            &equality_forest,
            None,
            &mut app_index,
            &dependencies,
        );
        assert_eq!(snapshot_result, first_result);
        assert_eq!(current_result, Some(second_dependency));
    }

    #[test]
    fn wave_app_index_retries_candidates_with_late_child_endpoints() {
        let egraph = EGraph::default();
        let child_endpoint = egraph.base_to_value(31_i64);
        let output = egraph.base_to_value(32_i64);
        let mut witnesses = WitnessArena::default();
        let child = witnesses
            .intern_syntax_app("Expr", "Leaf", Vec::new())
            .unwrap();
        let application = witnesses
            .intern_syntax_app("Expr", "A", vec![child])
            .unwrap();
        witnesses
            .bind_endpoint("Expr", output, application)
            .unwrap();
        let expected = witnesses.nodes[application.index()].node.clone();
        let equality_forest = EqualityForest::default();
        let mut app_index = WaveAppIndex::default();

        assert_eq!(
            assert_index_matches_linear(
                &witnesses,
                &expected,
                output,
                &equality_forest,
                None,
                &mut app_index,
                &DepArena::default(),
            ),
            None
        );
        witnesses
            .bind_endpoint("Expr", child_endpoint, child)
            .unwrap();
        assert_eq!(
            assert_index_matches_linear(
                &witnesses,
                &expected,
                output,
                &equality_forest,
                None,
                &mut app_index,
                &DepArena::default(),
            ),
            Some(DepArena::EMPTY)
        );
    }

    #[test]
    fn witness_snapshot_preserves_the_prestate_preferred_endpoint_syntax() {
        let mut witnesses = WitnessArena::default();
        let endpoint = EGraph::default().base_to_value(11_i64);
        let first = witnesses
            .intern_app("Expr", "A", Vec::new(), endpoint, DepArena::EMPTY, true)
            .unwrap();
        let second = witnesses
            .intern_app("Expr", "B", Vec::new(), endpoint, DepArena::EMPTY, true)
            .unwrap();
        assert_ne!(first, second);
        witnesses
            .prefer_endpoint_witness("Expr", endpoint, first)
            .unwrap();

        let snapshot = witnesses.snapshot();
        assert_eq!(
            witnesses.by_endpoint_at("Expr", endpoint, Some(&snapshot)),
            Some(first)
        );
    }
}
