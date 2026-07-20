//! A deliberately narrow dynamic causal slicer for positive relation programs.
//!
//! This module is a feasibility spike, not a general egglog provenance API. It
//! records match-time bindings from one ordinary reference-backend execution,
//! reconstructs exact relation tuples for a monotone fragment, and emits a
//! source program whose only schedule leaves are guarded `run-rule` calls.

use std::{
    path::Path,
    time::{Duration, Instant},
};

use thiserror::Error;

use crate::{
    EGraph, Error as EgglogError, TermDag,
    ast::{
        Action, Command, Expr, Fact, GenericAction, GenericExpr, GenericFact, Literal,
        RuleEvalMode, RunRuleConfig, Schedule, Span,
    },
    core_relations::{RuleMatch, Value},
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
    pub traced_run_time: Duration,
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
}

#[derive(Clone, Debug)]
struct AtomTemplate {
    relation: String,
    args: Vec<AtomArg>,
}

#[derive(Clone, Debug)]
enum AtomArg {
    Var(Span, String),
    Lit(Literal),
}

#[derive(Clone, Debug)]
struct RuleModel {
    body: Vec<AtomTemplate>,
    head: Vec<AtomTemplate>,
    var_order: Vec<String>,
    var_sorts: IndexMap<String, String>,
}

#[derive(Clone, Debug)]
struct CheckModel {
    atoms: Vec<AtomTemplate>,
    var_sorts: IndexMap<String, String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct FactKey {
    relation: String,
    args: Vec<Literal>,
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
    Literal { sort: String, value: Literal },
}

#[derive(Clone, Debug, Default)]
struct WitnessArena {
    nodes: Vec<WitnessNode>,
    ids: IndexMap<WitnessNode, WitnessId>,
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
        self.nodes.push(node.clone());
        self.ids.insert(node, id);
        Ok(id)
    }

    fn literal(&self, id: WitnessId) -> &Literal {
        match &self.nodes[id.index()] {
            WitnessNode::Literal { value, .. } => value,
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct BindingWitness {
    syntax: WitnessId,
    endpoint: Value,
}

impl BindingWitness {
    fn literal(self, witnesses: &WitnessArena) -> &Literal {
        // The endpoint is intentionally retained with the immutable syntax.
        // V0 does not print it or resolve it through the final database.
        let _captured_endpoint = self.endpoint;
        witnesses.literal(self.syntax)
    }
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
    Source { fact: FactKey },
    Fire(GroundedFire),
}

#[derive(Clone, Debug)]
struct ReplayEvent {
    kind: EventKind,
    prerequisites: DepId,
    effective_outputs: Vec<FactKey>,
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
    producers: IndexMap<FactKey, DepId>,
    source_events: usize,
}

struct ProgramModel {
    rules: IndexMap<String, RuleModel>,
    checks: Vec<CheckModel>,
    source_facts: Vec<FactKey>,
    source_expansions: SourceCommandExpansions,
    schedule_index: usize,
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

/// Trace and slice a program while resolving supported scalar relation inputs
/// relative to `fact_directory`. Input rows are embedded as ordinary source
/// facts in both replay projections, so the emitted programs are independent
/// of the external files.
pub fn causal_slice_program_with_fact_directory(
    filename: Option<String>,
    input: &str,
    fact_directory: Option<&Path>,
) -> Result<CausalSlice, CausalSliceError> {
    let mut parser = EGraph::default();
    let mut commands = parser.parse_program(filename.clone(), input)?;
    let source_name = filename.as_deref().unwrap_or("<input>");

    let relations = collect_relations(&commands, source_name)?;
    let rule_mapping = name_and_prepare_rules(&mut commands, source_name)?;
    let ProgramModel {
        rules,
        checks,
        source_facts,
        source_expansions,
        schedule_index,
    } = validate_and_model(&commands, &relations, source_name, fact_directory)?;

    let mut egraph = EGraph::default();
    let trace_start = Instant::now();
    let mut schedule_batches = None;
    let mut check_batches = Vec::new();

    for (command_index, command) in commands.iter().cloned().enumerate() {
        if command_index == schedule_index {
            let batches = run_one_traced_command(&mut egraph, command)?;
            schedule_batches = Some(batches);
        } else if matches!(command, Command::Check(..)) {
            check_batches.push(run_one_traced_command(&mut egraph, command)?);
        } else if let Some(expansion) = source_expansions.get(&command_index) {
            egraph.run_program(expansion.clone())?;
        } else {
            egraph.run_program(vec![command])?;
        }
    }
    let traced_run_time = trace_start.elapsed();
    let schedule_batches = schedule_batches.ok_or_else(|| {
        CausalSliceError::Invariant("validated schedule was not executed".to_owned())
    })?;
    let waves = schedule_batches.len();
    let observation_matches = check_batches
        .iter()
        .flat_map(|batches| batches.iter())
        .map(Vec::len)
        .sum::<usize>();
    let observation_trace_bindings = check_batches
        .iter()
        .flat_map(|batches| batches.iter())
        .flatten()
        .map(|event| event.bindings.len())
        .sum::<usize>();
    let schedule_trace_bindings = schedule_batches
        .iter()
        .flatten()
        .map(|event| event.bindings.len())
        .sum::<usize>();
    let max_batch_matches = schedule_batches
        .iter()
        .chain(check_batches.iter().flat_map(|batches| batches.iter()))
        .map(Vec::len)
        .max()
        .unwrap_or(0);
    let total_raw_matches =
        schedule_batches.iter().map(Vec::len).sum::<usize>() + observation_matches;
    let raw_trace_bindings = schedule_trace_bindings + observation_trace_bindings;
    let raw_trace_lower_bound_bytes = total_raw_matches * std::mem::size_of::<RuleMatch>()
        + raw_trace_bindings * std::mem::size_of::<(std::sync::Arc<str>, Value)>();

    let mut witnesses = WitnessArena::default();
    let Elaboration {
        pending_fires,
        events,
        mut dependencies,
        producers: final_producers,
        source_events,
    } = elaborate_events(
        &egraph,
        &rules,
        &source_facts,
        &schedule_batches,
        &mut witnesses,
    )?;
    let roots = observation_roots(
        &egraph,
        &checks,
        &check_batches,
        &final_producers,
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
        .map(|(batches, check)| batches.iter().map(Vec::len).sum::<usize>() * check.var_sorts.len())
        .sum();
    let retained = backward_slice(&events, &dependencies, roots);
    drop(schedule_batches);
    drop(check_batches);

    let schedule_span = command_schedule_span(&commands[schedule_index])
        .ok_or_else(|| CausalSliceError::Invariant("schedule command lost its span".to_owned()))?;
    let full_transcript_source = emit_program(
        &commands,
        schedule_index,
        &schedule_span,
        &rules,
        pending_fires.iter().map(|fire| &fire.grounding),
        &witnesses,
        &source_expansions,
    );
    let source = emit_program(
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

    validate_emitted_program(
        filename.clone(),
        &full_transcript_source,
        &rules,
        &rule_mapping,
    )?;
    validate_emitted_program(filename, &source, &rules, &rule_mapping)?;

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
        equality_edges: 0,
        prefix_fallbacks: 0,
        captured_bindings,
        observation_matches,
        observation_bindings,
        max_batch_matches,
        raw_trace_bindings,
        raw_trace_lower_bound_bytes,
        traced_run_time,
        full_transcript_bytes: full_transcript_source.len(),
        sliced_bytes: source.len(),
    };

    Ok(CausalSlice {
        source,
        full_transcript_source,
        stats,
        rule_mapping,
    })
}

fn run_one_traced_command(
    egraph: &mut EGraph,
    command: Command,
) -> Result<Vec<Vec<RuleMatch>>, CausalSliceError> {
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
        .begin_rule_match_trace()
        .map_err(|error| CausalSliceError::Invariant(error.to_string()))?;

    let result = egraph.run_program(vec![command]);
    let batches = egraph
        .backend
        .as_any_mut()
        .downcast_mut::<egglog_bridge::EGraph>()
        .expect("the backend type cannot change during one command")
        .take_rule_match_trace()
        .expect("the trace was started immediately above");
    result?;
    Ok(batches)
}

fn collect_relations(
    commands: &[Command],
    source_name: &str,
) -> Result<IndexMap<String, RelationDecl>, CausalSliceError> {
    let mut relations = IndexMap::default();
    for (index, command) in commands.iter().enumerate() {
        if let Command::Relation { span, name, inputs } = command {
            for sort in inputs {
                if !matches!(sort.as_str(), "i64" | "String" | "bool" | "f64" | "Unit") {
                    return unsupported(
                        span,
                        format!("relation `{name}` with non-scalar sort `{sort}`"),
                    );
                }
            }
            if relations
                .insert(
                    name.clone(),
                    RelationDecl {
                        sorts: inputs.clone(),
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
    }
    Ok(relations)
}

fn name_and_prepare_rules(
    commands: &mut [Command],
    source_name: &str,
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

        mapping.push(SourceRuleMapping {
            source_command_index: command_index,
            source_location: rule.span.to_string(),
            original_name,
            registered_name: rule.name.clone(),
            semantic_definition: semantic_rule_definition(rule),
        });
    }
    Ok(mapping)
}

fn validate_and_model(
    commands: &[Command],
    relations: &IndexMap<String, RelationDecl>,
    source_name: &str,
    fact_directory: Option<&Path>,
) -> Result<ProgramModel, CausalSliceError> {
    let mut rules = IndexMap::default();
    let mut checks = Vec::new();
    let mut source_facts = Vec::new();
    let mut source_expansions = SourceCommandExpansions::default();
    let mut schedule_index = None;
    let mut observations_started = false;

    for (index, command) in commands.iter().enumerate() {
        match command {
            Command::Relation { .. } | Command::AddRuleset(..) => {
                if schedule_index.is_some() {
                    return unsupported_command(
                        command,
                        index,
                        source_name,
                        "declaration after the computation schedule",
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
                let model = model_rule(rule, relations)?;
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
                source_facts.push(model_source_fact(action, relations)?);
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
                    let fact = FactKey {
                        relation: name.clone(),
                        args,
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
                checks.push(model_check(span, facts, relations)?);
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
            Command::Function { .. }
            | Command::Constructor { .. }
            | Command::Datatype { .. }
            | Command::Datatypes { .. }
            | Command::Sort { .. } => {
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
    if checks.is_empty() {
        return Err(CausalSliceError::Unsupported {
            location: source_name.to_owned(),
            reason: "a program without at least one positive check root".to_owned(),
        });
    }
    Ok(ProgramModel {
        rules,
        checks,
        source_facts,
        source_expansions,
        schedule_index,
    })
}

fn model_rule(
    rule: &crate::ast::Rule,
    relations: &IndexMap<String, RelationDecl>,
) -> Result<RuleModel, CausalSliceError> {
    if rule.body.is_empty() {
        return unsupported(&rule.span, format!("an empty body on rule `{}`", rule.name));
    }
    if rule.head.0.is_empty() {
        return unsupported(&rule.span, format!("an empty head on rule `{}`", rule.name));
    }
    if rule.body.len() > 2 && !rule.no_decomp {
        return unsupported(
            &rule.span,
            format!(
                "potentially tree-decomposed rule `{}`; causal slice v0 has no provenance for materialized intermediate rows",
                rule.name
            ),
        );
    }

    let mut var_order = Vec::new();
    let mut var_sorts = IndexMap::default();
    let mut body = Vec::new();
    for fact in &rule.body {
        let GenericFact::Fact(expr) = fact else {
            return unsupported(
                &rule.span,
                format!("equality or primitive filters in rule `{}`", rule.name),
            );
        };
        let atom = model_atom(expr, relations, "rule body")?;
        register_atom_vars(&atom, relations, &mut var_order, &mut var_sorts)?;
        body.push(atom);
    }

    let mut head = Vec::new();
    for action in &rule.head.0 {
        let GenericAction::Expr(_, expr) = action else {
            return unsupported_action(
                action,
                format!("a non-insert head action in rule `{}`", rule.name),
            );
        };
        let atom = model_atom(expr, relations, "rule head")?;
        for arg in &atom.args {
            if let AtomArg::Var(span, var) = arg
                && !var_sorts.contains_key(var)
            {
                return unsupported(
                    span,
                    format!("head-only variable `{var}` in rule `{}`", rule.name),
                );
            }
        }
        head.push(atom);
    }

    // Generic Join deliberately projects a variable that occurs in only one
    // body atom when the head does not use it. A later `run-rule :bind` query
    // specializes the plan and can enumerate several extensions of that
    // projected firing, so PR #23 cannot replay the ordinary physical match
    // with an exact guard. One-atom rules use MinCover and retain every column.
    if body.len() > 1 {
        let body_occurrences = variable_atom_occurrences(&body);
        let head_vars = atom_variables(&head);
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

    Ok(RuleModel {
        body,
        head,
        var_order,
        var_sorts,
    })
}

fn model_check(
    span: &Span,
    facts: &[Fact],
    relations: &IndexMap<String, RelationDecl>,
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
    let mut var_order = Vec::new();
    let mut var_sorts = IndexMap::default();
    for fact in facts {
        let GenericFact::Fact(expr) = fact else {
            return unsupported(span, "equality or primitive facts in a check".to_owned());
        };
        let atom = model_atom(expr, relations, "positive check")?;
        register_atom_vars(&atom, relations, &mut var_order, &mut var_sorts)?;
        atoms.push(atom);
    }
    if atoms.len() > 1 {
        let occurrences = variable_atom_occurrences(&atoms);
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
    Ok(CheckModel { atoms, var_sorts })
}

fn variable_atom_occurrences(atoms: &[AtomTemplate]) -> HashMap<&str, usize> {
    let mut occurrences = HashMap::default();
    for atom in atoms {
        let mut vars_in_atom = HashSet::default();
        for arg in &atom.args {
            if let AtomArg::Var(_, var) = arg {
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
        .filter_map(|arg| match arg {
            AtomArg::Var(_, var) => Some(var.as_str()),
            AtomArg::Lit(_) => None,
        })
        .collect()
}

fn model_source_fact(
    action: &Action,
    relations: &IndexMap<String, RelationDecl>,
) -> Result<FactKey, CausalSliceError> {
    let GenericAction::Expr(_, expr) = action else {
        return unsupported_action(action, "a non-relation initialization action");
    };
    let atom = model_atom(expr, relations, "source initialization")?;
    let mut args = Vec::new();
    for arg in atom.args {
        match arg {
            AtomArg::Lit(literal) => args.push(literal),
            AtomArg::Var(span, var) => {
                return unsupported(
                    &span,
                    format!("non-ground source initialization variable `{var}`"),
                );
            }
        }
    }
    Ok(FactKey {
        relation: atom.relation,
        args,
    })
}

fn source_fact_command(span: &Span, fact: &FactKey) -> Command {
    let args = fact
        .args
        .iter()
        .cloned()
        .map(|literal| Expr::Lit(span.clone(), literal))
        .collect();
    Command::Action(GenericAction::Expr(
        span.clone(),
        Expr::Call(span.clone(), fact.relation.clone(), args),
    ))
}

fn model_atom(
    expr: &Expr,
    relations: &IndexMap<String, RelationDecl>,
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
        .map(|arg| match arg {
            GenericExpr::Var(span, var) => {
                if var == "_" || var.starts_with('@') {
                    unsupported(
                        span,
                        "wildcard or parser-generated variables (they have no stable source binding)",
                    )
                } else {
                    Ok(AtomArg::Var(span.clone(), var.clone()))
                }
            }
            GenericExpr::Lit(span, literal) => {
                validate_printable_literal(span, literal)?;
                Ok(AtomArg::Lit(literal.clone()))
            }
            GenericExpr::Call(span, head, _) => unsupported(
                span,
                format!("nested call `{head}` in a relation tuple in {context}"),
            ),
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(AtomTemplate {
        relation: relation.clone(),
        args,
    })
}

fn register_atom_vars(
    atom: &AtomTemplate,
    relations: &IndexMap<String, RelationDecl>,
    order: &mut Vec<String>,
    sorts: &mut IndexMap<String, String>,
) -> Result<(), CausalSliceError> {
    let declaration = &relations[&atom.relation];
    for (arg, sort) in atom.args.iter().zip(&declaration.sorts) {
        let AtomArg::Var(span, var) = arg else {
            continue;
        };
        match sorts.get(var) {
            Some(previous) if previous != sort => {
                return unsupported(
                    span,
                    format!("variable `{var}` used at both sort `{previous}` and `{sort}`"),
                );
            }
            Some(_) => {}
            None => {
                sorts.insert(var.clone(), sort.clone());
                order.push(var.clone());
            }
        }
    }
    Ok(())
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
        Schedule::RunRule(span, _) => {
            unsupported(span, "manual `run-rule` in the input program".to_owned())
        }
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

fn elaborate_events(
    egraph: &EGraph,
    rules: &IndexMap<String, RuleModel>,
    source_facts: &[FactKey],
    batches: &[Vec<RuleMatch>],
    witnesses: &mut WitnessArena,
) -> Result<Elaboration, CausalSliceError> {
    let mut dependencies = DepArena::default();
    let mut events = EventArena::default();
    let mut producers = IndexMap::default();
    let mut source_events = 0;
    for fact in source_facts {
        if producers.contains_key(fact) {
            continue;
        }
        let event = events.push(ReplayEvent {
            kind: EventKind::Source { fact: fact.clone() },
            prerequisites: DepArena::EMPTY,
            effective_outputs: vec![fact.clone()],
        })?;
        let dependency = dependencies.event(event)?;
        producers.insert(fact.clone(), dependency);
        source_events += 1;
    }

    let mut pending_fires = Vec::new();
    for (wave, batch) in batches.iter().enumerate() {
        let mut new_outputs = IndexMap::<FactKey, DepId>::default();
        for (ordinal, captured) in batch.iter().enumerate() {
            let rule_name = captured.rule.as_ref();
            let model = rules.get(rule_name).ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "native trace referenced unmodeled rule `{rule_name}`"
                ))
            })?;
            let bindings = reconstruct_bindings(
                egraph,
                &captured.bindings,
                &model.var_order,
                &model.var_sorts,
                witnesses,
            )?;
            let body = ground_atoms(&model.body, &bindings, witnesses)?;
            let head = ground_atoms(&model.head, &bindings, witnesses)?;

            let mut premise_dependencies = IndexSet::default();
            for fact in &body {
                match producers.get(fact) {
                    Some(dependency) => {
                        premise_dependencies.insert(*dependency);
                    }
                    None if new_outputs.contains_key(fact) => {
                        return Err(CausalSliceError::Invariant(format!(
                            "rule `{rule_name}` matched a tuple produced only in the same wave: {}",
                            display_fact(fact)
                        )));
                    }
                    None => {
                        return Err(CausalSliceError::Invariant(format!(
                            "rule `{rule_name}` matched without a known structural premise: {}",
                            display_fact(fact)
                        )));
                    }
                }
            }
            let mut prerequisites = DepArena::EMPTY;
            for dependency in premise_dependencies {
                prerequisites = dependencies.and(prerequisites, dependency)?;
            }

            let mut effective_outputs = IndexSet::default();
            for fact in head {
                if !producers.contains_key(&fact) && !new_outputs.contains_key(&fact) {
                    effective_outputs.insert(fact);
                }
            }
            let effective_outputs = effective_outputs.into_iter().collect::<Vec<_>>();
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
            let promoted = if effective_outputs.is_empty() {
                None
            } else {
                let event = events.push(ReplayEvent {
                    kind: EventKind::Fire(grounding.clone()),
                    prerequisites,
                    effective_outputs: effective_outputs.clone(),
                })?;
                let dependency = dependencies.event(event)?;
                for fact in effective_outputs {
                    new_outputs.insert(fact, dependency);
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
        for (fact, dependency) in new_outputs {
            producers.insert(fact, dependency);
        }
    }
    Ok(Elaboration {
        pending_fires,
        events,
        dependencies,
        producers,
        source_events,
    })
}

fn observation_roots(
    egraph: &EGraph,
    checks: &[CheckModel],
    traces: &[Vec<Vec<RuleMatch>>],
    producers: &IndexMap<FactKey, DepId>,
    dependencies: &mut DepArena,
    witnesses: &mut WitnessArena,
) -> Result<DepId, CausalSliceError> {
    if checks.len() != traces.len() {
        return Err(CausalSliceError::Invariant(format!(
            "captured {} check traces for {} observations",
            traces.len(),
            checks.len()
        )));
    }

    let mut root = DepArena::EMPTY;
    for (check, batches) in checks.iter().zip(traces) {
        let captured = batches
            .iter()
            .flat_map(|batch| batch.iter())
            .next()
            .ok_or_else(|| {
                CausalSliceError::Invariant(
                    "a successful positive check had no captured satisfying match".to_owned(),
                )
            })?;
        let var_order = check.var_sorts.keys().cloned().collect::<Vec<_>>();
        let bindings = reconstruct_bindings(
            egraph,
            &captured.bindings,
            &var_order,
            &check.var_sorts,
            witnesses,
        )?;
        for fact in ground_atoms(&check.atoms, &bindings, witnesses)? {
            match producers.get(&fact) {
                Some(dependency) => {
                    root = dependencies.and(root, *dependency)?;
                }
                None => {
                    return Err(CausalSliceError::Invariant(format!(
                        "positive check selected a tuple with no source or rule producer: {}",
                        display_fact(&fact)
                    )));
                }
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
        let mut termdag = TermDag::default();
        let term = sort.reconstruct_termdag_base(egraph.backend.base_values(), value, &mut termdag);
        let expr = termdag.term_to_expr(&term, Span::Panic);
        let GenericExpr::Lit(_, literal) = expr else {
            return Err(CausalSliceError::Invariant(format!(
                "scalar binding `{var}` of sort `{sort_name}` was not printable as a literal"
            )));
        };
        if !literal_is_source_stable(&literal) {
            return Err(CausalSliceError::Unsupported {
                location: format!("captured binding `{var}`"),
                reason: format!(
                    "a `{sort_name}` witness that egglog's source printer cannot round-trip"
                ),
            });
        }
        let syntax = witnesses.intern_literal(sort_name, literal)?;
        let binding = BindingWitness {
            syntax,
            endpoint: value,
        };
        debug_assert_eq!(binding.endpoint, value);
        result.insert(var.clone(), binding);
    }
    Ok(result)
}

fn ground_atoms(
    atoms: &[AtomTemplate],
    bindings: &IndexMap<String, BindingWitness>,
    witnesses: &WitnessArena,
) -> Result<Vec<FactKey>, CausalSliceError> {
    atoms
        .iter()
        .map(|atom| {
            let args = atom
                .args
                .iter()
                .map(|arg| match arg {
                    AtomArg::Lit(literal) => Ok(literal.clone()),
                    AtomArg::Var(_, var) => bindings
                        .get(var)
                        .map(|binding| binding.literal(witnesses).clone())
                        .ok_or_else(|| {
                            CausalSliceError::Invariant(format!(
                                "grounding omitted source variable `{var}`"
                            ))
                        }),
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(FactKey {
                relation: atom.relation.clone(),
                args,
            })
        })
        .collect()
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
                    if let EventKind::Source { fact } = &replay_event.kind {
                        let _retained_source_fact = fact;
                    }
                    work.push(replay_event.prerequisites);
                }
            }
        }
    }
    retained.sort_unstable();
    retained
}

fn emit_program<'a>(
    commands: &[Command],
    schedule_index: usize,
    schedule_span: &Span,
    rules: &IndexMap<String, RuleModel>,
    fires: impl IntoIterator<Item = &'a GroundedFire>,
    witnesses: &WitnessArena,
    source_expansions: &SourceCommandExpansions,
) -> String {
    let mut previous_position = None;
    let leaves = fires
        .into_iter()
        .map(|fire| {
            let position = (fire.wave, fire.ordinal);
            if let Some(previous) = previous_position {
                debug_assert!(previous < position);
            }
            previous_position = Some(position);
            let model = &rules[&fire.rule];
            let bindings = model
                .var_order
                .iter()
                .map(|var| {
                    let literal = fire.bindings[var].literal(witnesses).clone();
                    (var.clone(), Expr::Lit(schedule_span.clone(), literal))
                })
                .collect();
            Schedule::RunRule(
                schedule_span.clone(),
                RunRuleConfig {
                    rule: fire.rule.clone(),
                    bindings,
                    selectors: Vec::new(),
                    expect: Some(1),
                },
            )
        })
        .collect::<Vec<_>>();

    let mut rendered = String::new();
    for (index, command) in commands.iter().enumerate() {
        if index == schedule_index {
            if !leaves.is_empty() {
                let replay_schedule = if leaves.len() == 1 {
                    leaves[0].clone()
                } else {
                    Schedule::Sequence(schedule_span.clone(), leaves.clone())
                };
                let replay = Command::RunSchedule(replay_schedule);
                rendered.push_str(&replay.to_string());
                rendered.push('\n');
            }
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
    for command in &parsed {
        match command {
            Command::RunSchedule(schedule) => validate_replay_schedule(schedule, rules)?,
            Command::Rule { rule } => {
                emitted_rules.insert(rule.name.as_str(), semantic_rule_definition(rule));
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
) -> Result<(), CausalSliceError> {
    match schedule {
        Schedule::RunRule(span, config) => {
            if config.expect != Some(1) {
                return unsupported(span, "a replay leaf without `:expect 1`".to_owned());
            }
            if !config.selectors.is_empty() {
                return unsupported(span, "internal replay selectors".to_owned());
            }
            let model = rules.get(&config.rule).ok_or_else(|| {
                CausalSliceError::Invariant(format!(
                    "replay references unknown rule `{}`",
                    config.rule
                ))
            })?;
            let names = config
                .bindings
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>();
            let expected = model
                .var_order
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>();
            if names != expected {
                return Err(CausalSliceError::Invariant(format!(
                    "replay binding list for `{}` is incomplete or out of order",
                    config.rule
                )));
            }
            if config
                .bindings
                .iter()
                .any(|(_, expr)| !matches!(expr, GenericExpr::Lit(..)))
            {
                return unsupported(span, "a non-literal replay witness".to_owned());
            }
            Ok(())
        }
        Schedule::Sequence(_, schedules) => {
            for schedule in schedules {
                validate_replay_schedule(schedule, rules)?;
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
        | Schedule::Repeat(span, _, _)
        | Schedule::Saturate(span, _)
        | Schedule::Sequence(span, _) => span.clone(),
    })
}

fn display_fact(fact: &FactKey) -> String {
    if fact.args.is_empty() {
        format!("({})", fact.relation)
    } else {
        let args = fact
            .args
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(" ");
        format!("({} {args})", fact.relation)
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
