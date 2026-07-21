//! A deliberately narrow dynamic causal slicer for positive relation programs.
//!
//! This module is a feasibility spike, not a general egglog provenance API. It
//! records match-time bindings from one ordinary reference-backend execution,
//! reconstructs exact relation tuples for a monotone fragment, and emits a
//! source program whose only schedule leaves are guarded manual rule batches.

use std::{
    path::Path,
    time::{Duration, Instant},
};

use thiserror::Error;

use crate::{
    EGraph, Error as EgglogError, TermDag,
    ast::{
        Action, Actions, Command, Expr, Fact, GenericAction, GenericExpr, GenericFact,
        GenericPackedRuleGroup, GenericPackedRunRuleBatch, Literal, PackedRuleFire, Rewrite, Rule,
        RuleEvalMode, Ruleset, RunRuleConfig, Schedule, Span,
    },
    core_relations::{
        RuleExecutionTrace, RuleMatch, TableApplication, TableId, UnionOutcome, UnionReceipt, Value,
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

#[derive(Clone, Debug)]
pub struct CausalSliceStats {
    pub original_bytes: usize,
    pub source_facts: usize,
    pub observation_count: usize,
    pub waves: usize,
    /// Groundings materialized by the native join before head-effect
    /// classification. The current debug API retains every raw trace batch
    /// through the run, then constructs these pending firings post-run; a
    /// production tracer should elaborate and discard them wave by wave.
    pub pending_firings: usize,
    pub matched_applications: usize,
    /// Applications selected as the first logical producer of at least one
    /// previously absent tuple in a traced wave. This is not native commit
    /// attribution when multiple matches produce the same tuple.
    pub effective_applications: usize,
    pub effective_output_rows: usize,
    /// Matched applications that were not selected as a logical producer.
    pub no_op_applications: usize,
    /// Persistent fire events promoted because at least one complete head
    /// action inserted a previously absent relation row.
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
    },
}

#[derive(Clone, Debug)]
struct RuleModel {
    span: Span,
    body: Vec<AtomTemplate>,
    body_lookups: Vec<ConstructorLookupTemplate>,
    head: Vec<AtomTemplate>,
    head_constructors: Vec<AtomArg>,
    head_unions: Vec<EqualityTemplate>,
    var_order: Vec<String>,
    replay_var_order: Vec<String>,
    var_sorts: IndexMap<String, String>,
    global_uses: IndexMap<String, String>,
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
struct SourceFact {
    command_index: usize,
    kind: SourceFactKind,
}

#[derive(Clone, Debug)]
enum SourceFactKind {
    Relation(AtomTemplate),
    Constructor(AtomArg),
    GlobalConstructor { name: String, sort: String },
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

#[derive(Clone, Debug)]
enum DepNode {
    Empty,
    Event(EventId),
    And(DepId, DepId),
}

#[derive(Clone, Debug)]
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

    fn and(&mut self, left: DepId, right: DepId) -> Result<DepId, CausalSliceError> {
        if left == Self::EMPTY {
            Ok(right)
        } else if right == Self::EMPTY || left == right {
            Ok(left)
        } else {
            self.push(DepNode::And(left, right))
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

#[derive(Clone, Debug)]
struct WitnessRecord {
    node: WitnessNode,
    original_value: Option<Value>,
    availability: DepId,
}

#[derive(Clone, Debug, Default)]
struct WitnessArena {
    nodes: Vec<WitnessRecord>,
    ids: IndexMap<WitnessNode, WitnessId>,
    endpoints: IndexMap<TypedEndpoint, WitnessId>,
    /// Definition-time endpoints retained to explain later canonicalized uses.
    globals: IndexMap<String, TypedEndpoint>,
    /// Exact values read from the native pre-state for the batch currently
    /// being elaborated.
    current_globals: IndexMap<String, TypedEndpoint>,
}

impl WitnessArena {
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
        self.nodes.push(WitnessRecord {
            node: node.clone(),
            original_value: None,
            availability: DepArena::EMPTY,
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
            id
        } else {
            let id = WitnessId(u32::try_from(self.nodes.len()).map_err(|_| {
                CausalSliceError::Invariant("witness arena exceeded u32 capacity".to_owned())
            })?);
            self.nodes.push(WitnessRecord {
                node: node.clone(),
                original_value: Some(endpoint),
                availability,
            });
            self.ids.insert(node, id);
            id
        };
        self.bind_endpoint_with_alias(sort, endpoint, id, allow_endpoint_alias)?;
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
        self.nodes.push(WitnessRecord {
            node: node.clone(),
            original_value: None,
            availability: DepArena::EMPTY,
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
        self.bind_endpoint_with_alias(sort, endpoint, id, false)
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

    fn bind_global(
        &mut self,
        name: &str,
        sort: &str,
        endpoint: Value,
    ) -> Result<(), CausalSliceError> {
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
        }
        self.current_globals.insert(name.to_owned(), value);
        Ok(())
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

    fn availability(&self, id: WitnessId) -> DepId {
        self.nodes[id.index()].availability
    }

    fn expr(&self, id: WitnessId, span: &Span) -> Expr {
        match &self.nodes[id.index()].node {
            WitnessNode::Literal { value, .. } => Expr::Lit(span.clone(), value.clone()),
            WitnessNode::App {
                function, children, ..
            } => Expr::Call(
                span.clone(),
                function.clone(),
                children
                    .iter()
                    .map(|child| self.expr(*child, span))
                    .collect(),
            ),
        }
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
}

#[derive(Clone, Debug)]
struct PendingFire {
    grounding: GroundedFire,
    promoted: Option<EventId>,
}

#[derive(Clone, Debug)]
enum EventKind {
    Source { row: RowKey },
    Fire(GroundedFire),
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
    events: EventArena,
    dependencies: DepArena,
    producers: IndexMap<RowKey, DepId>,
    source_events: usize,
    equality_forest: EqualityForest,
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
    left: TypedEndpoint,
    right: TypedEndpoint,
    dependency: DepId,
}

#[derive(Clone, Debug, Default)]
struct EqualityForest {
    edges: Vec<EqualityEdge>,
    adjacency: IndexMap<TypedEndpoint, Vec<(TypedEndpoint, DepId)>>,
}

impl EqualityForest {
    fn add(
        &mut self,
        left: TypedEndpoint,
        right: TypedEndpoint,
        dependency: DepId,
    ) -> Result<(), CausalSliceError> {
        if left.sort != right.sort {
            return Err(CausalSliceError::Invariant(format!(
                "successful union crossed runtime sorts `{}` and `{}`",
                left.sort, right.sort
            )));
        }
        if self.explain(&left, &right).is_some() {
            return Err(CausalSliceError::Invariant(
                "a successful native union would create a cycle in the explanation forest"
                    .to_owned(),
            ));
        }
        self.adjacency
            .entry(left.clone())
            .or_default()
            .push((right.clone(), dependency));
        self.adjacency
            .entry(right.clone())
            .or_default()
            .push((left.clone(), dependency));
        self.edges.push(EqualityEdge {
            left,
            right,
            dependency,
        });
        Ok(())
    }

    fn explain(&self, left: &TypedEndpoint, right: &TypedEndpoint) -> Option<Vec<DepId>> {
        if left == right {
            return Some(Vec::new());
        }
        let mut visited = HashSet::default();
        let mut work = vec![(left.clone(), Vec::new())];
        while let Some((current, path)) = work.pop() {
            if !visited.insert(current.clone()) {
                continue;
            }
            for (next, dependency) in self.adjacency.get(&current).into_iter().flatten() {
                let mut next_path = path.clone();
                next_path.push(*dependency);
                if next == right {
                    return Some(next_path);
                }
                work.push((next.clone(), next_path));
            }
        }
        None
    }

    fn edge_count(&self) -> usize {
        debug_assert!(self.edges.iter().all(|edge| {
            edge.left.sort == edge.right.sort
                && self.adjacency.get(&edge.left).is_some_and(|neighbors| {
                    neighbors.contains(&(edge.right.clone(), edge.dependency))
                })
        }));
        self.edges.len()
    }
}

struct ProgramModel {
    rules: IndexMap<String, RuleModel>,
    checks: Vec<CheckModel>,
    source_facts: Vec<SourceFact>,
    constructors: IndexMap<String, ConstructorDecl>,
    source_expansions: SourceCommandExpansions,
    schedule_index: usize,
    prefix_fallbacks: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TraceFunctionKind {
    Relation,
    Constructor,
}

#[derive(Clone, Debug)]
struct TraceFunctionMeta {
    name: String,
    input_sorts: Vec<String>,
    output_sort: String,
    kind: TraceFunctionKind,
}

struct ElaborationInput<'a> {
    egraph: &'a EGraph,
    rules: &'a IndexMap<String, RuleModel>,
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
    traces: &'a [Vec<RuleExecutionTrace>],
    producers: &'a IndexMap<RowKey, DepId>,
    equality_forest: &'a EqualityForest,
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
    causal_slice_program_with_fact_directory(filename, input, None)
}

/// Trace and slice a program while constructing only the retained replay
/// projection used by ordinary or proof-mode execution.
pub fn causal_slice_replay_program(
    filename: Option<String>,
    input: &str,
) -> Result<CausalReplay, CausalSliceError> {
    causal_slice_replay_program_with_fact_directory(filename, input, None)
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
    let generated = generate_causal_slice(filename, input, fact_directory, true)?;
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
    let generated = generate_causal_slice(filename, input, fact_directory, false)?;
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

fn generate_causal_slice(
    filename: Option<String>,
    input: &str,
    fact_directory: Option<&Path>,
    include_full_transcript: bool,
) -> Result<GeneratedCausalSlice, CausalSliceError> {
    let total_start = Instant::now();
    let preparation_start = Instant::now();
    let mut parser = EGraph::default();
    let commands = parser.parse_program(filename.clone(), input)?;
    let source_name = filename.as_deref().unwrap_or("<input>");
    let (mut commands, source_rule_origins) = lower_rewrites(commands, source_name)?;

    let (relations, constructors) = collect_declarations(&commands, source_name)?;
    let rule_mapping = name_and_prepare_rules(&mut commands, source_name, &source_rule_origins)?;
    let ProgramModel {
        rules,
        checks,
        source_facts,
        constructors,
        source_expansions,
        schedule_index,
        prefix_fallbacks,
    } = validate_and_model(
        &commands,
        &relations,
        &constructors,
        &source_rule_origins,
        source_name,
        fact_directory,
    )?;
    let preparation_time = preparation_start.elapsed();

    let mut egraph = EGraph::default().with_union_to_set_optimization(false);
    let trace_start = Instant::now();
    let mut schedule_batches = None;
    let mut check_batches = Vec::new();
    let mut source_traces = IndexMap::default();

    for (command_index, command) in commands.iter().cloned().enumerate() {
        if command_index == schedule_index {
            let batches = run_one_traced_command(&mut egraph, command)?;
            schedule_batches = Some(batches);
        } else if matches!(command, Command::Check(..)) {
            check_batches.push(run_one_traced_command(&mut egraph, command)?);
        } else if let Some(expansion) = source_expansions.get(&command_index) {
            egraph.run_program(expansion.clone())?;
        } else if matches!(command, Command::Action(..)) {
            let global_name = match &command {
                Command::Action(Action::Let(_, name, _)) => Some(name.clone()),
                _ => None,
            };
            let batches = run_one_traced_command(&mut egraph, command)?;
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
    let schedule_batches = schedule_batches.ok_or_else(|| {
        CausalSliceError::Invariant("validated schedule was not executed".to_owned())
    })?;
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

    let trace_functions = trace_function_metadata(&egraph, &relations, &constructors)?;
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
        );
        let source = emit_program_with_replay_commands(
            &commands,
            schedule_index,
            &replay_commands,
            &source_expansions,
        );
        let emission_time = emission_start.elapsed();

        let emitted_validation_start = Instant::now();
        validate_emitted_program(filename, &source, &rules, &rule_mapping)?;
        let emitted_validation_time = emitted_validation_start.elapsed();
        let total_time = total_start.elapsed();
        let stats = CausalSliceStats {
            original_bytes: input.len(),
            source_facts: source_facts.len(),
            observation_count: 0,
            waves,
            pending_firings,
            matched_applications: pending_firings,
            effective_applications,
            effective_output_rows,
            no_op_applications: pending_firings - effective_applications,
            promoted_events: effective_applications,
            retained_applications: effective_applications,
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
        events,
        mut dependencies,
        producers: final_producers,
        source_events,
        equality_forest,
    } = elaborate_events(
        ElaborationInput {
            egraph: &egraph,
            rules: &rules,
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
            traces: &check_batches,
            producers: &final_producers,
            equality_forest: &equality_forest,
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
    let retained = if prefix_fallbacks > 0 {
        let mut retained = IndexSet::default();
        for index in 0..events.events.len() {
            retained.insert(EventId(u32::try_from(index).map_err(|_| {
                CausalSliceError::Invariant("event index exceeded u32 capacity".to_owned())
            })?));
        }
        retained
    } else {
        backward_slice(&events, &dependencies, roots)
    };
    if prefix_fallbacks == 0
        && let Some(error) = retained.iter().find_map(|event| {
            events.events[event.index()]
                .deferred_prerequisite_error
                .clone()
        })
    {
        return Err(error.into_error());
    }
    drop(schedule_batches);
    drop(check_batches);
    let slicing_time = slicing_start.elapsed();

    let emission_start = Instant::now();
    let full_transcript_source = include_full_transcript.then(|| {
        emit_program(
            &commands,
            schedule_index,
            &schedule_span,
            &rules,
            pending_fires.iter().map(|fire| &fire.grounding),
            &witnesses,
            &source_expansions,
        )
        .0
    });
    let (source, shared_replay_witnesses) = emit_program(
        &commands,
        schedule_index,
        &schedule_span,
        &rules,
        retained
            .iter()
            .filter_map(|event| match &events.events[event.index()].kind {
                EventKind::Source { .. } => None,
                EventKind::Fire(fire) => Some(fire),
            }),
        &witnesses,
        &source_expansions,
    );
    let emission_time = emission_start.elapsed();

    let emitted_validation_start = Instant::now();
    if let Some(full_transcript_source) = &full_transcript_source {
        validate_emitted_program(
            filename.clone(),
            full_transcript_source,
            &rules,
            &rule_mapping,
        )?;
    }
    validate_emitted_program(filename, &source, &rules, &rule_mapping)?;
    let emitted_validation_time = emitted_validation_start.elapsed();

    let effective_applications = pending_fires
        .iter()
        .filter(|fire| fire.promoted.is_some())
        .count();
    let retained_applications = retained
        .iter()
        .filter(|event| matches!(events.events[event.index()].kind, EventKind::Fire(_)))
        .count();
    let effective_output_rows = events
        .events
        .iter()
        .filter(|event| matches!(event.kind, EventKind::Fire(_)))
        .map(|event| event.effective_outputs.len())
        .sum::<usize>();
    let total_time = total_start.elapsed();
    let stats = CausalSliceStats {
        original_bytes: input.len(),
        source_facts: source_facts.len(),
        observation_count: checks.len(),
        waves,
        pending_firings: pending_fires.len(),
        matched_applications: pending_fires.len(),
        effective_applications,
        effective_output_rows,
        no_op_applications: pending_fires.len() - effective_applications,
        promoted_events: effective_applications,
        retained_applications,
        source_events,
        dependency_nodes: dependencies.nodes.len(),
        witness_nodes: witnesses.nodes.len(),
        shared_replay_witnesses,
        equality_edges: equality_forest.edge_count(),
        prefix_fallbacks,
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
        rule_mapping,
    })
}

fn run_one_traced_command(
    egraph: &mut EGraph,
    command: Command,
) -> Result<Vec<RuleExecutionTrace>, CausalSliceError> {
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
        .begin_rule_match_trace_with_globals(globals)
        .map_err(|error| CausalSliceError::Invariant(error.to_string()))?;

    let result = egraph.run_program(vec![command]);
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

fn schema_only_container_presort(presort: &str) -> bool {
    matches!(presort, "Pair" | "Vec")
}

fn collect_declarations(
    commands: &[Command],
    source_name: &str,
) -> Result<
    (
        IndexMap<String, RelationDecl>,
        IndexMap<String, ConstructorDecl>,
    ),
    CausalSliceError,
> {
    let mut relations = IndexMap::default();
    let mut constructors = IndexMap::default();
    let datatype_sorts = commands
        .iter()
        .filter_map(|command| match command {
            Command::Datatype { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect::<HashSet<_>>();
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
    let opaque_sorts = commands
        .iter()
        .filter_map(|command| match command {
            Command::Sort {
                name,
                presort_and_args: Some((presort, _)),
                ..
            } if schema_only_container_presort(presort) => Some(name.clone()),
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
            _ => {}
        }
    }
    Ok((relations, constructors))
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
    relations: &IndexMap<String, RelationDecl>,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_rule_origins: &IndexMap<usize, SourceRuleOrigin>,
    source_name: &str,
    fact_directory: Option<&Path>,
) -> Result<ProgramModel, CausalSliceError> {
    let mut rules = IndexMap::default();
    let mut checks = Vec::new();
    let mut source_facts = Vec::new();
    let mut source_expansions = SourceCommandExpansions::default();
    let mut source_globals = IndexMap::default();
    let mut schedule_index = None;
    let mut observations_started = false;
    let mut print_size_observations = 0usize;

    for (index, command) in commands.iter().enumerate() {
        match command {
            Command::Relation { .. }
            | Command::Datatype { .. }
            | Command::Constructor { .. }
            | Command::Function { .. }
            | Command::AddRuleset(..) => {
                if schedule_index.is_some() {
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
            } if presort_and_args
                .as_ref()
                .is_none_or(|(presort, _)| schema_only_container_presort(presort)) =>
            {
                if schedule_index.is_some() {
                    return unsupported_command(
                        command,
                        index,
                        source_name,
                        "sort declaration after the computation schedule",
                    );
                }
            }
            Command::Rule { rule } => {
                if schedule_index.is_some() {
                    return unsupported(
                        &rule.span,
                        "rule declaration after the computation schedule".to_owned(),
                    );
                }
                let derived_replay_vars = source_rule_origins
                    .get(&index)
                    .map(|origin| origin.derived_replay_vars.as_slice())
                    .unwrap_or_default();
                let model = model_rule(
                    rule,
                    relations,
                    constructors,
                    &source_globals,
                    derived_replay_vars,
                )?;
                if rules.insert(rule.name.clone(), model).is_some() {
                    return unsupported(
                        &rule.span,
                        format!("duplicate registered rule `{}`", rule.name),
                    );
                }
            }
            Command::Action(action) => {
                if schedule_index.is_some() {
                    return unsupported_action(
                        action,
                        "ordinary action after the computation schedule",
                    );
                }
                let fact =
                    model_source_fact(index, action, relations, constructors, &source_globals)?;
                if let SourceFactKind::GlobalConstructor { name, sort } = &fact.kind {
                    if rules.values().any(|rule| rule.var_sorts.contains_key(name)) {
                        return unsupported_action(
                            action,
                            format!(
                                "source global `{name}` shadowing an earlier local rule variable; the strict proof checker resolves the replayed name as the global"
                            ),
                        );
                    }
                    if source_globals.insert(name.clone(), sort.clone()).is_some() {
                        return unsupported_action(
                            action,
                            format!("a duplicate source global `{name}`"),
                        );
                    }
                }
                source_facts.push(fact);
            }
            Command::Input { span, name, file } => {
                if schedule_index.is_some() {
                    return unsupported(
                        span,
                        "an input command after the computation schedule".to_owned(),
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
                for args in rows {
                    for literal in &args {
                        validate_printable_literal(span, literal)?;
                    }
                    let fact = SourceFact {
                        command_index: index,
                        kind: SourceFactKind::Relation(AtomTemplate {
                            relation: name.clone(),
                            args: args.iter().cloned().map(AtomArg::Lit).collect(),
                        }),
                    };
                    expansion.push(source_fact_command(span, &fact));
                    source_facts.push(fact);
                }
                source_expansions.insert(index, expansion);
            }
            Command::RunSchedule(schedule) => {
                if schedule_index.replace(index).is_some() {
                    return unsupported_command(
                        command,
                        index,
                        source_name,
                        "more than one top-level computation schedule",
                    );
                }
                if observations_started {
                    return unsupported_command(
                        command,
                        index,
                        source_name,
                        "a computation schedule after an observation",
                    );
                }
                validate_input_schedule(schedule)?;
            }
            Command::Check(span, facts) => {
                if schedule_index.is_none() {
                    return unsupported(span, "a positive check before the schedule".to_owned());
                }
                observations_started = true;
                checks.push(model_check(
                    span,
                    facts,
                    relations,
                    constructors,
                    &source_globals,
                )?);
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
            Command::Datatypes { .. } | Command::Sort { .. } => {
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
                if schedule_index.is_none() {
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
                if schedule_index.is_none() {
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

    let schedule_index = schedule_index.ok_or_else(|| CausalSliceError::Unsupported {
        location: source_name.to_owned(),
        reason: "a program without exactly one computation schedule".to_owned(),
    })?;
    let prefix_fallbacks = if checks.is_empty() {
        print_size_observations
    } else {
        0
    };
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
        source_expansions,
        schedule_index,
        prefix_fallbacks,
    })
}

fn model_rule(
    rule: &crate::ast::Rule,
    relations: &IndexMap<String, RelationDecl>,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
    derived_replay_vars: &[String],
) -> Result<RuleModel, CausalSliceError> {
    if rule.body.is_empty() {
        return unsupported(&rule.span, format!("an empty body on rule `{}`", rule.name));
    }
    if rule.head.0.is_empty() {
        return unsupported(&rule.span, format!("an empty head on rule `{}`", rule.name));
    }
    let mut var_order = Vec::new();
    let mut var_sorts = IndexMap::default();
    let mut body = Vec::new();
    for fact in &rule.body {
        match fact {
            GenericFact::Fact(expr) => {
                let atom = model_atom(expr, relations, constructors, source_globals, "rule body")?;
                if atom.args.iter().any(atom_arg_contains_app) {
                    return unsupported(
                        &rule.span,
                        format!(
                            "nested constructor matching in rule `{}`; v0 only binds constructed values through variables",
                            rule.name
                        ),
                    );
                }
                register_atom_vars(&atom, relations, &mut var_order, &mut var_sorts)?;
                body.push(atom);
            }
            GenericFact::Eq(..) => {}
        }
    }
    let mut body_lookups = Vec::new();
    for fact in &rule.body {
        let GenericFact::Eq(span, left, right) = fact else {
            continue;
        };
        let lookup = model_constructor_lookup(
            span,
            left,
            right,
            &var_sorts,
            constructors,
            source_globals,
            &format!("rule `{}` body", rule.name),
        )?;
        register_arg_vars(
            &lookup.application,
            &lookup.sort,
            &mut var_order,
            &mut var_sorts,
        )?;
        register_arg_vars(&lookup.output, &lookup.sort, &mut var_order, &mut var_sorts)?;
        body_lookups.push(lookup);
    }
    let mut head = Vec::new();
    let mut head_constructors = Vec::new();
    let mut head_unions = Vec::new();
    for action in &rule.head.0 {
        let args = match action {
            GenericAction::Expr(_, expr) => {
                let GenericExpr::Call(span, function, _) = expr else {
                    return unsupported_action(
                        action,
                        format!("a non-call head action in rule `{}`", rule.name),
                    );
                };
                if relations.contains_key(function) {
                    let atom =
                        model_atom(expr, relations, constructors, source_globals, "rule head")?;
                    let args = atom.args.clone();
                    head.push(atom);
                    args
                } else if let Some(constructor) = constructors.get(function) {
                    let constructor = model_atom_arg(
                        expr,
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
                let equality = model_equality(
                    span,
                    left,
                    right,
                    &var_sorts,
                    constructors,
                    source_globals,
                    &format!("rule `{}` union head", rule.name),
                )?;
                let args = vec![equality.left.clone(), equality.right.clone()];
                head_unions.push(equality);
                args
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
                if !var_sorts.contains_key(var) {
                    return unsupported(
                        span,
                        format!("head-only variable `{var}` in rule `{}`", rule.name),
                    );
                }
            }
        }
    }
    if !head_unions.is_empty() && (rule.head.0.len() != 1 || head_unions.len() != 1) {
        return unsupported(
            &rule.span,
            format!(
                "a union mixed with other head actions in rule `{}`; replaying a retained complete head requires redundant-union support",
                rule.name
            ),
        );
    }

    // Generic Join deliberately projects a variable that occurs in only one
    // body atom when the head does not use it. A later `run-rule :bind` query
    // specializes the plan and can enumerate several extensions of that
    // projected firing, so PR #23 cannot replay the ordinary physical match
    // with an exact guard. One-atom rules use MinCover and retain every column.
    if rule.body.len() > 1 {
        let body_occurrences = variable_rule_fact_occurrences(&body, &body_lookups);
        let mut head_vars = atom_variables(&head);
        for constructor in &head_constructors {
            for (_, var) in atom_arg_vars(constructor) {
                head_vars.insert(var.as_str());
            }
        }
        for equality in &head_unions {
            for (_, var) in atom_arg_vars(&equality.left)
                .into_iter()
                .chain(atom_arg_vars(&equality.right))
            {
                head_vars.insert(var.as_str());
            }
        }
        if let Some(var) = var_order.iter().find(|var| {
            body_occurrences.get(var.as_str()).copied() == Some(1)
                && !head_vars.contains(var.as_str())
        }) {
            return unsupported(
                &rule.span,
                format!(
                    "multi-atom rule variable `{var}` that Generic Join may project; exact replay requires a projection-preserving match selector and a representative premise-row witness"
                ),
            );
        }
    }

    let derived_replay_vars = derived_replay_vars
        .iter()
        .map(String::as_str)
        .collect::<HashSet<_>>();
    for derived in &derived_replay_vars {
        let derivable = body_lookups.iter().any(|lookup| {
            matches!(&lookup.output, AtomArg::Var(_, output) if output.as_str() == *derived)
                && atom_arg_vars(&lookup.application)
                    .iter()
                    .all(|(_, input)| !derived_replay_vars.contains(input.as_str()))
        });
        if !derivable {
            return Err(CausalSliceError::Invariant(format!(
                "internal replay variable `{derived}` on rule `{}` is not functionally determined by a constructor lookup",
                rule.name
            )));
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
        body_lookups,
        head,
        head_constructors,
        head_unions,
        var_order,
        replay_var_order,
        var_sorts,
        global_uses: IndexMap::default(),
    };
    model.global_uses = rule_global_uses(&model)
        .into_iter()
        .map(|(name, sort)| (name.to_owned(), sort.to_owned()))
        .collect();
    Ok(model)
}

fn model_check(
    span: &Span,
    facts: &[Fact],
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
    for fact in facts {
        match fact {
            GenericFact::Fact(expr) => {
                let atom = model_atom(
                    expr,
                    relations,
                    constructors,
                    source_globals,
                    "positive check",
                )?;
                register_atom_vars(&atom, relations, &mut var_order, &mut var_sorts)?;
                atoms.push(atom);
            }
            GenericFact::Eq(fact_span, left, right) => {
                let equality = model_equality(
                    fact_span,
                    left,
                    right,
                    &var_sorts,
                    constructors,
                    source_globals,
                    "positive check",
                )?;
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

fn model_constructor_lookup(
    span: &Span,
    left: &Expr,
    right: &Expr,
    known_var_sorts: &IndexMap<String, String>,
    constructors: &IndexMap<String, ConstructorDecl>,
    source_globals: &IndexMap<String, String>,
    context: &str,
) -> Result<ConstructorLookupTemplate, CausalSliceError> {
    let (application_expr, output_expr) = match (left, right) {
        (GenericExpr::Call(..), GenericExpr::Var(..)) => (left, right),
        (GenericExpr::Var(..), GenericExpr::Call(..)) => (right, left),
        _ => {
            return unsupported(
                span,
                format!(
                    "equality or primitive filters in {context}; only a constructor application equated with an output variable is supported"
                ),
            );
        }
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
    let application = model_atom_arg(
        application_expr,
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
    let output = model_atom_arg(
        output_expr,
        &constructor.output,
        constructors,
        source_globals,
        context,
    )?;
    if let AtomArg::Var(_, output_var) = &output
        && let Some(previous) = known_var_sorts.get(output_var)
        && previous != &constructor.output
    {
        return unsupported(
            output_span,
            format!(
                "constructor lookup output `{output_var}` has sort `{previous}` instead of `{}` in {context}",
                constructor.output
            ),
        );
    }
    Ok(ConstructorLookupTemplate {
        span: span.clone(),
        application,
        output,
        sort: constructor.output.clone(),
    })
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

fn variable_rule_fact_occurrences<'a>(
    atoms: &'a [AtomTemplate],
    lookups: &'a [ConstructorLookupTemplate],
) -> HashMap<&'a str, usize> {
    let mut occurrences = variable_atom_occurrences(atoms);
    for lookup in lookups {
        let mut vars = HashSet::default();
        for (_, var) in atom_arg_vars(&lookup.application)
            .into_iter()
            .chain(atom_arg_vars(&lookup.output))
        {
            vars.insert(var.as_str());
        }
        for var in vars {
            *occurrences.entry(var).or_default() += 1;
        }
    }
    occurrences
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

fn atom_variables(atoms: &[AtomTemplate]) -> HashSet<&str> {
    atoms
        .iter()
        .flat_map(|atom| &atom.args)
        .flat_map(atom_arg_vars)
        .map(|(_, var)| var.as_str())
        .collect()
}

fn model_source_fact(
    command_index: usize,
    action: &Action,
    relations: &IndexMap<String, RelationDecl>,
    constructors: &IndexMap<String, ConstructorDecl>,
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
        return Ok(SourceFact {
            command_index,
            kind: SourceFactKind::GlobalConstructor {
                name: name.clone(),
                sort,
            },
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
        command_index,
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
            let constructor =
                constructors
                    .get(function)
                    .ok_or_else(|| CausalSliceError::Unsupported {
                        location: span.to_string(),
                        reason: format!("nested non-constructor call `{function}` in {context}"),
                    })?;
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
            })
        }
    }
}

fn atom_arg_contains_app(arg: &AtomArg) -> bool {
    match arg {
        AtomArg::App { .. } => true,
        AtomArg::Var(..) | AtomArg::Global { .. } | AtomArg::Lit(..) => false,
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
    for constructor in &rule.head_constructors {
        collect_atom_arg_globals(constructor, &mut globals);
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
            let effects = elaborate_fire_applications(
                egraph,
                batch.applications.iter(),
                trace_functions,
                witnesses,
                prefix_fallback,
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
            SourceFactKind::GlobalConstructor { name, sort } => {
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
                if witnesses.by_endpoint(sort, endpoint).is_none() {
                    return Err(CausalSliceError::Unsupported {
                        location: format!("source global `{name}`"),
                        reason: "a constructor result without an immutable replay witness"
                            .to_owned(),
                    });
                }
                witnesses.bind_global(name, sort, endpoint)?;
            }
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
        }
    }
}

fn elaborate_prefix_replay(
    input: PrefixElaborationInput<'_>,
    witnesses: &mut WitnessArena,
) -> Result<PrefixElaboration, CausalSliceError> {
    let PrefixElaborationInput {
        egraph,
        rules,
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
        let applications_by_origin = OriginIndex::build(
            batch.matches.len(),
            &batch.applications,
            |application| Some(application.origin.index()),
            "application",
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
            // Capture bindings before the head applications below extend the
            // witness arena. Every emitted expression was therefore available
            // at the original match boundary.
            let bindings = reconstruct_rule_bindings(egraph, &captured.bindings, model, witnesses)?;
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
            )?;
            for constructor in &model.head_constructors {
                let AtomArg::App { output_sort, .. } = constructor else {
                    return Err(CausalSliceError::Invariant(
                        "modeled constructor head lost its application node".to_owned(),
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

fn elaborate_events(
    input: ElaborationInput<'_>,
    witnesses: &mut WitnessArena,
) -> Result<Elaboration, CausalSliceError> {
    let ElaborationInput {
        egraph,
        rules,
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
    let mut equality_forest = EqualityForest::default();
    let mut source_events = 0;
    for fact in source_facts {
        let rows = elaborate_source_fact(
            egraph,
            fact,
            source_traces,
            trace_functions,
            relations,
            witnesses,
            prefix_fallback,
        )?;
        for row in rows {
            if producers.contains_key(&row) {
                continue;
            }
            let event = events.push(ReplayEvent {
                kind: EventKind::Source { row: row.clone() },
                prerequisites: DepArena::EMPTY,
                deferred_prerequisite_error: None,
                effective_outputs: vec![row.clone()],
            })?;
            let dependency = dependencies.event(event)?;
            producers.insert(row, dependency);
            source_events += 1;
        }
    }

    let mut pending_fires = Vec::new();
    for (wave, batch) in batches.iter().enumerate() {
        witnesses.load_current_globals(&batch.globals)?;
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
        let mut unions_by_origin = vec![Vec::new(); batch.matches.len()];
        for receipt in &batch.unions {
            let Some(origin) = receipt.origin else {
                if prefix_fallback {
                    continue;
                }
                return Err(CausalSliceError::Unsupported {
                    location: format!("traced wave {wave}"),
                    reason:
                        "a congruence, merge, or rebuild union without an originating rule match"
                            .to_owned(),
                });
            };
            let Some(unions) = unions_by_origin.get_mut(origin.index()) else {
                return Err(CausalSliceError::Invariant(format!(
                    "union origin {} exceeded {} matches",
                    origin.index(),
                    batch.matches.len()
                )));
            };
            unions.push(receipt);
        }

        let mut new_outputs = IndexMap::<RowKey, DepId>::default();
        let mut new_equality_edges = Vec::new();
        for (ordinal, captured) in batch.matches.iter().enumerate() {
            let rule_name = captured.rule.as_ref();
            let model = rules.get(rule_name).ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "native trace referenced unmodeled rule `{rule_name}`"
                ))
            })?;
            let bindings = reconstruct_rule_bindings(egraph, &captured.bindings, model, witnesses)?;
            let prerequisite_result = (|| {
                let body = ground_atoms(egraph, &model.body, &bindings, witnesses, relations)?;

                let mut premise_dependencies = IndexSet::default();
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
                            if equality_forest.edge_count() > 0 {
                                return Err(CausalSliceError::Unsupported {
                                    location: model.span.to_string(),
                                    reason: format!(
                                        "an equality-canonicalized premise of rule `{rule_name}` without commit-time relation-row rekey provenance"
                                    ),
                                });
                            }
                            return Err(CausalSliceError::Invariant(format!(
                                "rule `{rule_name}` matched without a known source row: {}",
                                display_row(row)
                            )));
                        }
                    }
                }
                for lookup in &model.body_lookups {
                    let (application, application_witness) = ground_application_witness(
                        egraph,
                        &lookup.application,
                        &lookup.sort,
                        &bindings,
                        witnesses,
                    )?;
                    let output =
                        ground_arg(egraph, &lookup.output, &lookup.sort, &bindings, witnesses)?;
                    premise_dependencies.insert(witnesses.availability(application_witness));
                    premise_dependencies.insert(endpoint_availability(
                        &output,
                        witnesses,
                        &lookup.span,
                    )?);
                    let explanation = equality_forest.explain(&application, &output).ok_or_else(
                        || CausalSliceError::Unsupported {
                            location: lookup.span.to_string(),
                            reason: format!(
                                "constructor lookup in rule `{rule_name}` whose canonical output lacks a captured successful-union path"
                            ),
                        },
                    )?;
                    premise_dependencies.extend(explanation);
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
            let (prerequisites, deferred_prerequisite_error) = match prerequisite_result {
                Ok(prerequisites) => (prerequisites, None),
                Err(CausalSliceError::Unsupported { location, reason }) => (
                    DepArena::EMPTY,
                    Some(DeferredUnsupported { location, reason }),
                ),
                Err(error) => return Err(error),
            };

            let effects = elaborate_fire_applications(
                egraph,
                applications_by_origin[ordinal].iter().copied(),
                trace_functions,
                witnesses,
                prefix_fallback,
            )?;
            for constructor in &model.head_constructors {
                let AtomArg::App { output_sort, .. } = constructor else {
                    return Err(CausalSliceError::Invariant(
                        "modeled constructor head lost its application node".to_owned(),
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
            let applied_unions = if prefix_fallback {
                classify_prefix_union_receipts(
                    rule_name,
                    &model.head_unions,
                    &unions_by_origin[ordinal],
                )?
            } else {
                let expected_unions = model
                    .head_unions
                    .iter()
                    .map(|equality| ground_equality(egraph, equality, &bindings, witnesses))
                    .collect::<Result<Vec<_>, _>>()?;
                match_union_receipts(rule_name, &expected_unions, &unions_by_origin[ordinal])?
            };

            let effective_outputs = effects
                .new_rows
                .into_iter()
                .filter(|row| !producers.contains_key(row) && !new_outputs.contains_key(row))
                .collect::<Vec<_>>();
            let grounding = GroundedFire {
                rule: rule_name.to_owned(),
                wave: u32::try_from(wave).map_err(|_| {
                    CausalSliceError::Invariant("wave index exceeded u32 capacity".to_owned())
                })?,
                ordinal: u32::try_from(ordinal).map_err(|_| {
                    CausalSliceError::Invariant("wave ordinal exceeded u32 capacity".to_owned())
                })?,
                bindings,
            };
            let promoted = if effective_outputs.is_empty()
                && effects.new_witnesses.is_empty()
                && applied_unions.is_empty()
            {
                None
            } else {
                let event = events.push(ReplayEvent {
                    kind: EventKind::Fire(grounding.clone()),
                    prerequisites,
                    deferred_prerequisite_error,
                    effective_outputs: effective_outputs.clone(),
                })?;
                let dependency = dependencies.event(event)?;
                for row in effective_outputs {
                    new_outputs.insert(row, dependency);
                }
                for witness in effects.new_witnesses {
                    witnesses.set_availability(witness, dependency);
                }
                for (left, right) in applied_unions {
                    new_equality_edges.push((left, right, dependency));
                }
                Some(event)
            };
            pending_fires.push(PendingFire {
                grounding,
                promoted,
            });
        }

        // A bounded ruleset iteration searches against one pre-state. Publish
        // all newly produced rows only after every captured match is elaborated.
        for (row, dependency) in new_outputs {
            producers.insert(row, dependency);
        }
        for (left, right, dependency) in new_equality_edges {
            equality_forest.add(left, right, dependency)?;
        }
    }
    Ok(Elaboration {
        pending_fires,
        events,
        dependencies,
        producers,
        source_events,
        equality_forest,
    })
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
        traces,
        producers,
        equality_forest,
    } = input;
    if checks.len() != traces.len() {
        return Err(CausalSliceError::Invariant(format!(
            "captured {} check traces for {} observations",
            traces.len(),
            checks.len()
        )));
    }

    let mut root = DepArena::EMPTY;
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
        let (batch, captured) = batches
            .iter()
            .find_map(|batch| batch.matches.first().map(|captured| (batch, captured)))
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
            let explanation = equality_forest.explain(&left, &right).ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "positive check matched equality `{}` without a recorded cause",
                    equality.span
                ))
            })?;
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
        let syntax = if sort.is_eq_sort() {
            witnesses.by_endpoint(sort_name, value).ok_or_else(|| {
                CausalSliceError::Unsupported {
                    location: format!("captured binding `{var}`"),
                    reason: format!(
                        "a `{sort_name}` endpoint without a match-time constructor witness"
                    ),
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
    captured: &[(std::sync::Arc<str>, Value)],
    model: &RuleModel,
    witnesses: &mut WitnessArena,
) -> Result<IndexMap<String, BindingWitness>, CausalSliceError> {
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
        let syntax = if sort.is_eq_sort() {
            witnesses.by_endpoint(sort_name, value).ok_or_else(|| {
                CausalSliceError::Unsupported {
                    location: format!("captured binding `{var}`"),
                    reason: format!(
                        "a `{sort_name}` endpoint without a match-time constructor witness"
                    ),
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
            let endpoint = ground_arg(
                egraph,
                &lookup.application,
                &lookup.sort,
                &result,
                witnesses,
            )?;
            let syntax = witnesses
                .by_endpoint(&lookup.sort, endpoint.value)
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

    if let Some(var) = model
        .var_order
        .iter()
        .find(|var| !result.contains_key(var.as_str()))
    {
        let available = captured_by_name
            .keys()
            .copied()
            .collect::<Vec<_>>()
            .join(", ");
        return Err(CausalSliceError::Invariant(format!(
            "match-time binding for `{var}` was projected away and could not be derived from constructor inputs; available names: [{available}]"
        )));
    }
    Ok(result)
}

fn ground_atoms(
    egraph: &EGraph,
    atoms: &[AtomTemplate],
    bindings: &IndexMap<String, BindingWitness>,
    witnesses: &WitnessArena,
    relations: &IndexMap<String, RelationDecl>,
) -> Result<Vec<RowKey>, CausalSliceError> {
    atoms
        .iter()
        .map(|atom| {
            let declaration = &relations[&atom.relation];
            let args = atom
                .args
                .iter()
                .zip(&declaration.sorts)
                .map(|(arg, sort)| ground_arg(egraph, arg, sort, bindings, witnesses))
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

fn ground_application_witness(
    egraph: &EGraph,
    application: &AtomArg,
    sort: &str,
    bindings: &IndexMap<String, BindingWitness>,
    witnesses: &WitnessArena,
) -> Result<(TypedEndpoint, WitnessId), CausalSliceError> {
    let endpoint = ground_arg(egraph, application, sort, bindings, witnesses)?;
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
    let children = args
        .iter()
        .zip(input_sorts)
        .map(|(arg, input_sort)| {
            let child = ground_arg(egraph, arg, input_sort, bindings, witnesses)?;
            witnesses
                .by_endpoint(input_sort, child.value)
                .ok_or_else(|| {
                    CausalSliceError::Invariant(format!(
                        "constructor lookup `{function}` child lacked captured syntax"
                    ))
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let node = WitnessNode::App {
        sort: sort.to_owned(),
        function: function.clone(),
        children,
    };
    let witness =
        witnesses
            .ids
            .get(&node)
            .copied()
            .ok_or_else(|| CausalSliceError::Unsupported {
                location: format!("constructor lookup `{function}`"),
                reason: "syntax that was unavailable at the captured match".to_owned(),
            })?;
    if witnesses.endpoint(witness) != Some(endpoint.value) {
        return Err(CausalSliceError::Invariant(format!(
            "constructor lookup `{function}` witness endpoint diverged while grounding"
        )));
    }
    Ok((endpoint, witness))
}

fn endpoint_availability(
    endpoint: &TypedEndpoint,
    witnesses: &WitnessArena,
    span: &Span,
) -> Result<DepId, CausalSliceError> {
    let witness = witnesses
        .by_endpoint(&endpoint.sort, endpoint.value)
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

fn match_union_receipts(
    rule_name: &str,
    expected: &[(TypedEndpoint, TypedEndpoint)],
    receipts: &[&UnionReceipt],
) -> Result<Vec<(TypedEndpoint, TypedEndpoint)>, CausalSliceError> {
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
        let Some(index) = unmatched
            .iter()
            .position(|receipt| receipt.lhs == left.value && receipt.rhs == right.value)
        else {
            return Err(CausalSliceError::Invariant(format!(
                "rule `{rule_name}` expected union endpoints ({left:?}, {right:?}) but native commit reported {unmatched:?}"
            )));
        };
        let receipt = unmatched.swap_remove(index);
        match receipt.outcome {
            UnionOutcome::Applied { parent, child } => {
                if parent == child {
                    return Err(CausalSliceError::Invariant(format!(
                        "rule `{rule_name}` reported a successful union with identical committed endpoints"
                    )));
                }
                applied.push((left.clone(), right.clone()));
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
    receipts: &[&UnionReceipt],
) -> Result<Vec<(TypedEndpoint, TypedEndpoint)>, CausalSliceError> {
    if expected.len() != receipts.len() {
        return Err(CausalSliceError::Invariant(format!(
            "rule `{rule_name}` modeled {} union action(s) but native commit reported {} receipt(s)",
            expected.len(),
            receipts.len()
        )));
    }
    let mut applied = Vec::new();
    for (equality, receipt) in expected.iter().zip(receipts) {
        if let UnionOutcome::Applied { parent, child } = receipt.outcome {
            if parent == child {
                return Err(CausalSliceError::Invariant(format!(
                    "rule `{rule_name}` reported a successful union with identical committed endpoints"
                )));
            }
            applied.push((
                TypedEndpoint {
                    sort: equality.sort.clone(),
                    value: receipt.lhs,
                },
                TypedEndpoint {
                    sort: equality.sort.clone(),
                    value: receipt.rhs,
                },
            ));
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

struct FireApplicationEffects {
    observed_rows: Vec<RowKey>,
    new_rows: Vec<RowKey>,
    new_witnesses: Vec<WitnessId>,
}

fn elaborate_fire_applications<'a>(
    egraph: &EGraph,
    applications: impl IntoIterator<Item = &'a TableApplication>,
    trace_functions: &IndexMap<TableId, TraceFunctionMeta>,
    witnesses: &mut WitnessArena,
    prefix_fallback: bool,
) -> Result<FireApplicationEffects, CausalSliceError> {
    let mut observed_rows = Vec::new();
    let mut new_rows = Vec::new();
    let mut new_witnesses = Vec::new();
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
                let children = meta
                    .input_sorts
                    .iter()
                    .zip(&application.args)
                    .map(|(sort, value)| {
                        endpoint_witness(egraph, sort, *value, witnesses, &meta.name)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let expected = WitnessNode::App {
                    sort: meta.output_sort.clone(),
                    function: meta.name.clone(),
                    children: children.clone(),
                };
                if application.newly_staged {
                    let was_known = witnesses
                        .by_endpoint(&meta.output_sort, application.result)
                        .is_some();
                    let witness = witnesses.intern_app(
                        &meta.output_sort,
                        &meta.name,
                        children,
                        application.result,
                        DepArena::EMPTY,
                        prefix_fallback,
                    )?;
                    if !was_known {
                        new_witnesses.push(witness);
                    }
                } else {
                    match witnesses.by_endpoint(&meta.output_sort, application.result) {
                        Some(witness)
                            if witnesses.nodes[witness.index()].node != expected
                                && !prefix_fallback =>
                        {
                            return Err(CausalSliceError::Unsupported {
                                location: format!("constructor application `{}`", meta.name),
                                reason: "a table hit whose match-time syntax conflicts with its captured witness"
                                    .to_owned(),
                            });
                        }
                        Some(_) => {}
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
    })
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
        AtomArg::Var(_, var) => bindings
            .get(var)
            .map(|binding| binding.endpoint)
            .ok_or_else(|| {
                CausalSliceError::Invariant(format!("grounding omitted source variable `{var}`"))
            })?,
        AtomArg::App {
            function,
            args,
            input_sorts,
            ..
        } => {
            let children = args
                .iter()
                .zip(input_sorts)
                .map(|(arg, sort)| {
                    let endpoint = ground_arg(egraph, arg, sort, bindings, witnesses)?;
                    witnesses.by_endpoint(sort, endpoint.value).ok_or_else(|| {
                        CausalSliceError::Invariant(format!(
                            "grounded constructor `{function}` child lacked its captured witness"
                        ))
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            let node = WitnessNode::App {
                sort: sort.to_owned(),
                function: function.clone(),
                children,
            };
            let witness =
                witnesses
                    .ids
                    .get(&node)
                    .ok_or_else(|| CausalSliceError::Unsupported {
                        location: format!("grounded constructor `{function}`"),
                        reason: "syntax that was unavailable at the captured firing".to_owned(),
                    })?;
            witnesses.endpoint(*witness).ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "constructor witness `{function}` has no runtime endpoint"
                ))
            })?
        }
    };
    Ok(TypedEndpoint {
        sort: sort.to_owned(),
        value,
    })
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

fn backward_slice(events: &EventArena, dependencies: &DepArena, root: DepId) -> IndexSet<EventId> {
    let mut retained = IndexSet::default();
    let mut visited_dependencies = HashSet::default();
    let mut work = vec![root];
    while let Some(dependency) = work.pop() {
        if !visited_dependencies.insert(dependency) {
            continue;
        }
        match dependencies.nodes[dependency.index()] {
            DepNode::Empty => {}
            DepNode::And(left, right) => {
                work.push(right);
                work.push(left);
            }
            DepNode::Event(event) => {
                if retained.insert(event) {
                    let replay_event = &events.events[event.index()];
                    if let EventKind::Source { row } = &replay_event.kind {
                        let _retained_source_row = row;
                    }
                    work.push(replay_event.prerequisites);
                }
            }
        }
    }
    retained.sort_unstable();
    retained
}

const SHARED_REPLAY_WITNESS_PREFIX: &str = "$__csw";

fn emit_prefix_replay_commands(
    _commands: &[Command],
    schedule_span: &Span,
    rules: &IndexMap<String, RuleModel>,
    fires: &[CompactReplayFire],
    witnesses: &WitnessArena,
) -> (String, usize) {
    let mut previous_position = None;
    let mut rendered = String::new();
    let mut shared_witnesses = 0usize;

    let mut start = 0usize;
    while start < fires.len() {
        let wave = fires[start].wave;
        let mut end = start + 1;
        while end < fires.len() && fires[end].wave == wave {
            end += 1;
        }
        let wave_fires = &fires[start..end];
        let mut witness_indices = IndexMap::<WitnessId, u32>::default();
        let mut witness_uses = HashMap::<WitnessId, usize>::default();
        let mut group_indices = IndexMap::<u32, u32>::default();
        for fire in wave_fires {
            let position = (fire.wave, fire.ordinal);
            if let Some(previous) = previous_position {
                debug_assert!(previous < position);
            }
            previous_position = Some(position);
            let next_group = u32::try_from(group_indices.len())
                .expect("packed replay group count exceeded u32 capacity");
            group_indices.entry(fire.rule_index).or_insert(next_group);
            for witness in &fire.bindings {
                let next_witness = u32::try_from(witness_indices.len())
                    .expect("packed replay witness count exceeded u32 capacity");
                witness_indices.entry(*witness).or_insert(next_witness);
                *witness_uses.entry(*witness).or_default() += 1;
            }
        }

        let packed_witnesses = witness_indices
            .keys()
            .map(|witness| witnesses.expr(*witness, schedule_span))
            .collect();
        shared_witnesses += witness_uses.values().filter(|uses| **uses > 1).count();
        let groups = group_indices
            .keys()
            .map(|rule_index| {
                let (rule_name, model) = rules
                    .get_index(*rule_index as usize)
                    .expect("captured compact replay rule index must remain valid");
                GenericPackedRuleGroup {
                    span: schedule_span.clone(),
                    rule: rule_name.clone(),
                    variables: model.replay_var_order.clone().into_boxed_slice(),
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
                witnesses: packed_witnesses,
                groups,
                fires: packed_fires,
            },
        ));
        rendered.push_str(&replay.to_string());
        rendered.push('\n');
        start = end;
    }

    (rendered, shared_witnesses)
}

fn emit_program<'a>(
    commands: &[Command],
    schedule_index: usize,
    schedule_span: &Span,
    rules: &IndexMap<String, RuleModel>,
    fires: impl IntoIterator<Item = &'a GroundedFire>,
    witnesses: &WitnessArena,
    source_expansions: &SourceCommandExpansions,
) -> (String, usize) {
    let compact = fires
        .into_iter()
        .map(|fire| {
            let rule_index = rules
                .get_index_of(&fire.rule)
                .expect("grounded replay rule was validated during modeling");
            let model = &rules[&fire.rule];
            let bindings = model
                .replay_var_order
                .iter()
                .map(|variable| fire.bindings[variable].syntax)
                .collect::<Vec<_>>()
                .into_boxed_slice();
            CompactReplayFire {
                rule_index: u32::try_from(rule_index)
                    .expect("packed replay rule index exceeded u32 capacity"),
                wave: fire.wave,
                ordinal: fire.ordinal,
                bindings,
            }
        })
        .collect::<Vec<_>>();
    let (replay_commands, shared_replay_witnesses) =
        emit_prefix_replay_commands(commands, schedule_span, rules, &compact, witnesses);
    (
        emit_program_with_replay_commands(
            commands,
            schedule_index,
            &replay_commands,
            source_expansions,
        ),
        shared_replay_witnesses,
    )
}

fn emit_program_with_replay_commands(
    commands: &[Command],
    schedule_index: usize,
    replay_commands: &str,
    source_expansions: &SourceCommandExpansions,
) -> String {
    let mut rendered = String::new();
    for (index, command) in commands.iter().enumerate() {
        if index == schedule_index {
            rendered.push_str(replay_commands);
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

fn validate_emitted_program(
    filename: Option<String>,
    source: &str,
    rules: &IndexMap<String, RuleModel>,
    mapping: &[SourceRuleMapping],
) -> Result<(), CausalSliceError> {
    let mut parser = EGraph::default();
    let parsed = parser.parse_program(filename, source)?;
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
            Command::Action(Action::Let(span, name, expression))
                if name.starts_with(SHARED_REPLAY_WITNESS_PREFIX) =>
            {
                validate_closed_replay_witness(expression, span, &replay_globals)?;
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
    // Parsing is the source-of-truth validation here. The egglog pretty
    // printer is not generally a fixed point, so requiring a second rendering
    // to be byte-identical would reject valid emitted programs. Determinism is
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
    if names != expected {
        return Err(CausalSliceError::Invariant(format!(
            "replay binding list for `{}` is incomplete or out of order",
            config.rule
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
    for witness in &batch.witnesses {
        validate_closed_replay_witness(witness, span, replay_globals)?;
    }
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
        if actual != expected {
            return Err(CausalSliceError::Invariant(format!(
                "packed replay variables for `{}` were {actual:?}, expected {expected:?}",
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
                .any(|witness| *witness as usize >= batch.witnesses.len())
        {
            return Err(CausalSliceError::Invariant(
                "packed replay fire has invalid witness indices".to_owned(),
            ));
        }
    }
    Ok(())
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
