//! Graph-neutral replay-program construction for a selected slice.
//!
//! # Lowering laws
//!
//! Lowering copies the selected trace projection into an owned intermediate
//! representation. The result contains source names, source literals, catalog
//! ordinals, and structural term recipes, but no backend ids, runtime values,
//! trace handles, or borrows from the recording graph. [`ReplayProgram::to_commands`]
//! turns that representation into the ordinary owned [`Command`] values used
//! for fresh-graph execution, including under proof mode. Source rendering is
//! an export and parser-round-trip helper, not the in-process replay boundary.
//!
//! The capture catalog is the source of truth for surface declarations,
//! selected source commands, normalized rule identities, and exact input-row
//! literals. Candidate static setup is interleaved by catalog ordinal, then
//! pruned to the transitive `Sort`/`Function`/`Ruleset` closure of the replay
//! roots. Source rows, grounded firing waves, and checks are ordered by their
//! recorded chronology. Only selected input rows are materialized, so lowering
//! never rereads their source files. A selected rewrite is reconstructed as a
//! rewrite, and a selected direction of a birewrite preserves the original
//! birewrite form and orientation.
//!
//! Structural-call-valued bindings cross into the fresh graph only through checked
//! aliases. Each alias is scheduled at a retained pre-wave boundary after its
//! children and historical key support are available and before its producer is
//! removed. Structural reuse is confined to an occurrence lifetime: removals
//! split alias epochs so identical syntax cannot conflate deleted and recreated
//! native values.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use thiserror::Error;

use crate::ast::{
    Action, Command, Expr, RunRuleConfig, RustSpan, Schedule, Schema, Span, Subdatatypes,
};
use crate::core_relations::{
    FactId, ReplayLiteral, ReplayOpId, ReplaySortId, ReplayTerm, ReplayTermId, SourceRef,
    TraceView, TraceViewError,
};
use crate::slicing::backward::Slice;
use crate::util::{HashMap, HashSet};
use crate::{
    CaptureCatalog, CatalogRuleSurface, EGraph, Literal, ReplayOpKey, RewriteDirection,
    RuleBindingRole, RuleCatalogEntry,
};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
/// Arena-local reference to an owned replay term.
///
/// Unlike the trace's replay-term ids, this reference is meaningful only in a
/// [`ReplayProgram`] and carries no recording-graph identity.
struct ReplayTermRef(u32);

impl ReplayTermRef {
    fn from_index(index: usize) -> Result<Self, ReplayError> {
        Ok(Self(index.try_into().map_err(|_| {
            ReplayError::Invalid("owned replay term arena exceeds u32".into())
        })?))
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
/// A typed, graph-neutral recipe for a literal or structural call.
enum OwnedReplayTerm {
    Literal {
        sort: String,
        literal: Literal,
    },
    Call {
        sort: String,
        op: String,
        children: Box<[ReplayTermRef]>,
    },
}

impl OwnedReplayTerm {
    fn sort(&self) -> &str {
        match self {
            Self::Literal { sort, .. } | Self::Call { sort, .. } => sort,
        }
    }
}

/// A retained declaration or rule, positioned by its surface catalog ordinal.
struct ReplaySetup {
    catalog_ordinal: usize,
    command: Command,
}

/// The source-level action used to reconstruct selected initial state.
///
/// Synthetic sources retain their ordinary surface command. Selected input
/// rows are materialized from the exact literals retained at capture time.
enum ReplaySourceKind {
    Command(Box<Command>),
    InputRow {
        /// One-based physical line, used only to preserve order within one input command.
        line: u64,
        function: String,
        literals: Box<[Literal]>,
    },
}

/// A selected source action together with its catalog chronology.
struct ReplaySource {
    /// Last completed trace wave before the source executed on the recorder.
    after_wave: u64,
    catalog_ordinal: usize,
    kind: ReplaySourceKind,
}

/// A checked source-level name established for a structural call before a wave.
struct ReplayAlias {
    name: String,
    term: ReplayTermRef,
}

/// One grounded rule variable and its owned literal-or-alias term.
struct ReplayBinding {
    variable: String,
    term: ReplayTermRef,
}

/// A selected rule firing lowered to its stable replay name and bindings.
struct ReplayFiring {
    replay_name: String,
    bindings: Box<[ReplayBinding]>,
}

/// All checked aliases and grounded firings executed at one retained wave.
///
/// Aliases run first against the immutable pre-wave database; the grouped
/// firings then execute through one ordinary `run-rule` schedule.
struct ReplayWave {
    wave: u64,
    /// Largest catalog ordinal among selected firings in this wave.
    setup_bound: usize,
    aliases: Box<[ReplayAlias]>,
    firings: Box<[ReplayFiring]>,
}

/// A retained surface check placed after the wave that originally satisfied it.
struct ReplayCheck {
    after_wave: u64,
    catalog_ordinal: usize,
    command: Command,
}

/// One chronological unit in the owned replay program.
enum ReplayEvent {
    Source(ReplaySource),
    Wave(ReplayWave),
    Check(Box<ReplayCheck>),
}

impl ReplayEvent {
    /// Order sources, waves, and checks without borrowing the captured trace.
    ///
    /// Pre-run sources and checks share catalog order. Later checks sort after
    /// the wave they observe; input rows retain line order within their command.
    fn chronology_key(&self) -> (u64, u8, usize, u64) {
        match self {
            Self::Source(source) => {
                let line = match &source.kind {
                    ReplaySourceKind::Command(_) => 0,
                    ReplaySourceKind::InputRow { line, .. } => *line,
                };
                (source.after_wave, 1, source.catalog_ordinal, line)
            }
            Self::Wave(wave) => (wave.wave, 0, 0, 0),
            Self::Check(check) => (check.after_wave, 1, check.catalog_ordinal, u64::MAX),
        }
    }
}

/// An owned, graph-neutral replay intermediate representation.
///
/// `setup` holds candidate catalog declarations plus retained rules. Lowering
/// keeps only the transitive declaration closure needed by the emitted roots.
/// `terms` owns structural binding recipes, and `events` preserves
/// source/wave/check chronology. No field is a handle into the recording graph.
pub(super) struct ReplayProgram {
    setup: Vec<ReplaySetup>,
    terms: Vec<OwnedReplayTerm>,
    events: Vec<ReplayEvent>,
}

impl ReplayProgram {
    /// Lower the owned IR into ordinary commands for a fresh graph.
    ///
    /// Setup commands are emitted no later than the first chronological event
    /// that needs them. Structural call values are re-established by `let-check`,
    /// grounded firings use ordinary `run-rule` schedules, and literals remain
    /// source literals. The final hygiene pass alpha-renames retained internal
    /// symbols consistently across declarations, rules, bindings, and sorts.
    pub(super) fn to_commands(&self) -> Result<Vec<Command>, ReplayError> {
        let mut commands = Vec::new();
        let mut setup = self.setup.iter().peekable();

        let mut aliases = HashMap::<ReplayTermRef, String>::default();
        for event in &self.events {
            let setup_bound = match event {
                ReplayEvent::Source(source) => source.catalog_ordinal,
                ReplayEvent::Wave(wave) => wave.setup_bound,
                ReplayEvent::Check(check) => check.catalog_ordinal,
            };
            while setup
                .peek()
                .is_some_and(|entry| entry.catalog_ordinal <= setup_bound)
            {
                let entry = setup.next().expect("peeked replay setup disappeared");
                commands.push(entry.command.clone());
            }
            match event {
                ReplayEvent::Source(source) => match &source.kind {
                    ReplaySourceKind::Command(command) => commands.push(command.as_ref().clone()),
                    ReplaySourceKind::InputRow {
                        function, literals, ..
                    } => {
                        let span = replay_span(commands.len());
                        let args = literals
                            .iter()
                            .cloned()
                            .map(|literal| Expr::Lit(span.clone(), literal))
                            .collect();
                        let expr = Expr::Call(span.clone(), function.clone(), args);
                        commands.push(Command::Action(Action::Expr(span, expr)));
                    }
                },
                ReplayEvent::Wave(wave) => {
                    for alias in &wave.aliases {
                        if aliases.contains_key(&alias.term) {
                            return Err(ReplayError::Invalid(format!(
                                "replay term {} receives more than one checked alias",
                                alias.term.index()
                            )));
                        }
                        let node = self.term(alias.term)?;
                        let OwnedReplayTerm::Call { sort, op, children } = node else {
                            return Err(ReplayError::Invalid(format!(
                                "checked alias `{}` targets a literal",
                                alias.name
                            )));
                        };
                        let span = replay_span(commands.len());
                        let args = children
                            .iter()
                            .copied()
                            .map(|child| self.term_reference_expr(child, &aliases, &span))
                            .collect::<Result<Vec<_>, _>>()?;
                        commands.push(Command::LetCheck {
                            span: span.clone(),
                            name: alias.name.clone(),
                            expr: Expr::Call(span, op.clone(), args),
                            expected_sort: Some(sort.clone()),
                        });
                        aliases.insert(alias.term, alias.name.clone());
                    }

                    if wave.firings.is_empty() {
                        return Err(ReplayError::Invalid(format!(
                            "replay wave {} contains no firings",
                            wave.wave
                        )));
                    }
                    let span = replay_span(commands.len());
                    let configs = wave
                        .firings
                        .iter()
                        .map(|firing| {
                            let bindings = firing
                                .bindings
                                .iter()
                                .map(|binding| {
                                    Ok((
                                        binding.variable.clone(),
                                        self.term_reference_expr(binding.term, &aliases, &span)?,
                                    ))
                                })
                                .collect::<Result<Vec<_>, ReplayError>>()?;
                            Ok(RunRuleConfig {
                                rule: firing.replay_name.clone(),
                                bindings,
                            })
                        })
                        .collect::<Result<Vec<_>, ReplayError>>()?;
                    commands.push(Command::RunSchedule(Schedule::RunRule(span, configs)));
                }
                ReplayEvent::Check(check) => commands.push(check.command.clone()),
            }
        }
        commands.extend(setup.map(|entry| entry.command.clone()));
        let observed = observed_source_symbols(&commands);
        let commands = retain_required_declarations(commands);
        Ok(hygienic_source_commands(commands, observed))
    }

    fn term(&self, term: ReplayTermRef) -> Result<&OwnedReplayTerm, ReplayError> {
        self.terms.get(term.index()).ok_or_else(|| {
            ReplayError::Invalid(format!(
                "replay term reference {} is out of range",
                term.index()
            ))
        })
    }

    fn term_reference_expr(
        &self,
        term: ReplayTermRef,
        aliases: &HashMap<ReplayTermRef, String>,
        span: &Span,
    ) -> Result<Expr, ReplayError> {
        match self.term(term)? {
            OwnedReplayTerm::Literal { literal, .. } => {
                Ok(Expr::Lit(span.clone(), literal.clone()))
            }
            OwnedReplayTerm::Call { .. } => aliases
                .get(&term)
                .cloned()
                .map(|name| Expr::Var(span.clone(), name))
                .ok_or_else(|| {
                    ReplayError::Invalid(format!(
                        "replay term {} is used before its checked alias",
                        term.index()
                    ))
                }),
        }
    }
}

/// Render ordinary commands as a standalone source program.
#[cfg(any(feature = "bin", test))]
pub(super) fn render_commands_as_source(commands: &[Command]) -> String {
    use std::fmt::Write as _;

    let mut rendered = String::new();
    for command in commands {
        writeln!(&mut rendered, "{command}").expect("writing to a String cannot fail");
    }
    rendered
}

fn split_replay_direction(symbol: &str) -> (&str, &str) {
    symbol
        .strip_suffix("=>")
        .map(|base| (base, "=>"))
        .or_else(|| symbol.strip_suffix("<=").map(|base| (base, "<=")))
        .unwrap_or((symbol, ""))
}

fn split_global_symbol(symbol: &str) -> (&str, &str) {
    symbol
        .strip_prefix(crate::GLOBAL_NAME_PREFIX)
        .map(|symbol| (crate::GLOBAL_NAME_PREFIX, symbol))
        .unwrap_or(("", symbol))
}

fn observed_source_symbols(commands: &[Command]) -> Vec<String> {
    let mut observed = Vec::new();
    for command in commands {
        let mut heads = Vec::new();
        let mut leaves = Vec::new();
        let mut record_head = |head: String| {
            heads.push(head.clone());
            head
        };
        let mut record_leaf = |leaf: String| {
            leaves.push(leaf.clone());
            leaf
        };
        let command = command
            .clone()
            .map_symbols(&mut record_head, &mut record_leaf);
        observed.extend(heads);
        observed.extend(leaves);
        if let Command::Rewrite(_, rewrite, _) | Command::BiRewrite(_, rewrite) = &command {
            observed.push(rewrite.name.clone());
        }
        let mut strings = Vec::new();
        let _ = command.map_string_symbols(&mut |symbol: String| {
            strings.push(symbol.clone());
            symbol
        });
        observed.extend(strings);
    }
    observed
}

/// Alpha-renames replay-owned and parser-reserved internal symbols across the
/// complete candidate program. This is deliberately cold: capture keeps exact
/// provenance-marked names, then one occupied-name-aware map makes aliases,
/// declarations, rule references, grounded binding keys, and direction suffixes
/// agree without conflating user symbols. Observation precedes declaration
/// pruning so an unused declaration cannot change a generated replay name.
fn hygienic_source_commands(commands: Vec<Command>, observed: Vec<String>) -> Vec<Command> {
    let mut occupied = HashSet::default();
    let mut internal_bases = Vec::new();
    let mut seen_internal = HashSet::default();
    for symbol in observed {
        let (_, canonical) = split_global_symbol(&symbol);
        if let Some(internal) = canonical.strip_prefix(crate::util::INTERNAL_SYMBOL_PREFIX) {
            let (base, _) = split_replay_direction(internal);
            if seen_internal.insert(base.to_owned()) {
                internal_bases.push(base.to_owned());
            }
        } else {
            occupied.insert(canonical.to_owned());
        }
    }

    let mut renames = HashMap::default();
    for base in internal_bases {
        let mut suffix = 0usize;
        let replacement = loop {
            let candidate = if suffix == 0 {
                base.clone()
            } else {
                format!("{base}_{suffix}")
            };
            let spellings = [
                candidate.clone(),
                format!("{candidate}=>"),
                format!("{candidate}<="),
            ];
            if spellings.iter().all(|name| !occupied.contains(name)) {
                occupied.extend(spellings);
                break candidate;
            }
            suffix += 1;
        };
        renames.insert(base, replacement);
    }

    let rename = |symbol: String| {
        let (global, canonical) = split_global_symbol(&symbol);
        let Some(internal) = canonical.strip_prefix(crate::util::INTERNAL_SYMBOL_PREFIX) else {
            return symbol;
        };
        let (base, direction) = split_replay_direction(internal);
        let replacement = renames
            .get(base)
            .expect("observed internal symbol lost its allocated base");
        format!("{global}{replacement}{direction}")
    };

    commands
        .into_iter()
        .map(|command| {
            let mut rename_head = |head: String| rename(head);
            let mut rename_leaf = |leaf: String| rename(leaf);
            let mut command = command
                .map_symbols(&mut rename_head, &mut rename_leaf)
                .map_string_symbols(&mut |symbol: String| rename(symbol));
            if let Command::Rewrite(_, rewrite, _) | Command::BiRewrite(_, rewrite) = &mut command {
                rewrite.name = rename(std::mem::take(&mut rewrite.name));
            }
            command
        })
        .collect()
}

fn replay_span(command: usize) -> Span {
    Span::Rust(Arc::new(RustSpan {
        file: "generated slice replay",
        line: command.saturating_add(1).try_into().unwrap_or(u32::MAX),
        column: 1,
    }))
}

#[derive(Debug, Error)]
/// Failures while validating or lowering a selected replay.
///
/// This internal type distinguishes capture, catalog, and unsupported source-
/// representation failures. The public facade reports them through the crate's
/// existing `crate::Error` type.
pub(super) enum ReplayError {
    #[error("slice replay is unavailable without exact trace capture")]
    Disabled,
    #[error("slice replay requires the main native backend")]
    UnsupportedBackend,
    #[error("slice replay trace error: {0}")]
    Trace(#[from] TraceViewError),
    #[error("invalid slice replay: {0}")]
    Invalid(String),
    #[error("unsupported slice replay: {0}")]
    Unsupported(String),
}

/// Copies typed term recipes out of the trace into the owned term arena.
///
/// Sort and operation ids are resolved through the capture catalog, every call
/// is type-checked against its registered signature, and cycles or missing ids
/// fail closed. Newly interned calls are reported in occurrence order so alias
/// scheduling can pair them with the captured per-occurrence plan.
struct OwnedTermBuilder<'a, 'view> {
    view: &'a mut TraceView<'view>,
    sorts: HashMap<ReplaySortId, String>,
    ops: HashMap<ReplayOpId, ReplayOpKey>,
    literal_memo: HashMap<ReplayTermId, ReplayTermRef>,
    visiting: HashSet<ReplayTermId>,
    nodes: Vec<OwnedReplayTerm>,
    newly_interned_calls: Vec<(ReplayTermId, ReplayTermRef)>,
}

impl<'a, 'view> OwnedTermBuilder<'a, 'view> {
    fn new(view: &'a mut TraceView<'view>, catalog: &CaptureCatalog) -> Result<Self, ReplayError> {
        let mut sorts = HashMap::default();
        for (name, id) in &catalog.sort_ids {
            if sorts.insert(*id, name.clone()).is_some() {
                return Err(ReplayError::Invalid(format!(
                    "replay sort id {} has multiple names",
                    id.get()
                )));
            }
        }
        let mut ops = HashMap::default();
        for (key, id) in &catalog.op_ids {
            if ops.insert(*id, key.clone()).is_some() {
                return Err(ReplayError::Invalid(format!(
                    "replay operation id {} has multiple signatures",
                    id.get()
                )));
            }
        }
        Ok(Self {
            view,
            sorts,
            ops,
            literal_memo: HashMap::default(),
            visiting: HashSet::default(),
            nodes: Vec::new(),
            newly_interned_calls: Vec::new(),
        })
    }

    fn intern(&mut self, source: ReplayTermId) -> Result<ReplayTermRef, ReplayError> {
        if source.is_missing() {
            return Err(ReplayError::Invalid(
                "selected binding owns a missing replay term".into(),
            ));
        }
        if !self.visiting.insert(source) {
            return Err(ReplayError::Invalid(format!(
                "replay term {} is cyclic",
                source.get()
            )));
        }
        let node = self.view.replay_term(source)?;
        if matches!(node, ReplayTerm::Literal { .. })
            && let Some(term) = self.literal_memo.get(&source)
        {
            self.visiting.remove(&source);
            return Ok(*term);
        }
        let owned = match node {
            ReplayTerm::Literal { sort, literal } => OwnedReplayTerm::Literal {
                sort: self.sort_name(sort)?.to_owned(),
                literal: replay_literal(literal),
            },
            ReplayTerm::Call { sort, op, children } => {
                let sort_name = self.sort_name(sort)?.to_owned();
                let op = self.ops.get(&op).cloned().ok_or_else(|| {
                    ReplayError::Invalid("replay term uses an unknown operation id".into())
                })?;
                if op.output != sort_name {
                    return Err(ReplayError::Invalid(format!(
                        "replay operation `{}` returns `{}` but term is typed `{sort_name}`",
                        op.name, op.output
                    )));
                }
                if op.inputs.len() != children.len() {
                    return Err(ReplayError::Invalid(format!(
                        "replay operation `{}` expects {} children but term has {}",
                        op.name,
                        op.inputs.len(),
                        children.len()
                    )));
                }
                let mut owned_children = Vec::with_capacity(children.len());
                for (index, child) in children.iter().copied().enumerate() {
                    let child = self.intern(child)?;
                    let actual = self.nodes[child.index()].sort();
                    if actual != op.inputs[index] {
                        return Err(ReplayError::Invalid(format!(
                            "replay operation `{}` child {index} expects `{}` but owns `{actual}`",
                            op.name, op.inputs[index]
                        )));
                    }
                    owned_children.push(child);
                }
                OwnedReplayTerm::Call {
                    sort: sort_name,
                    op: op.name,
                    children: owned_children.into_boxed_slice(),
                }
            }
        };
        self.visiting.remove(&source);
        let is_call = matches!(owned, OwnedReplayTerm::Call { .. });
        let term = ReplayTermRef::from_index(self.nodes.len())?;
        self.nodes.push(owned);
        if is_call {
            self.newly_interned_calls.push((source, term));
        } else {
            self.literal_memo.insert(source, term);
        }
        Ok(term)
    }

    fn sort_name(&self, sort: ReplaySortId) -> Result<&str, ReplayError> {
        self.sorts
            .get(&sort)
            .map(String::as_str)
            .ok_or_else(|| ReplayError::Invalid(format!("unknown replay sort id {}", sort.get())))
    }

    fn take_new_calls(&mut self) -> Vec<(ReplayTermId, ReplayTermRef)> {
        std::mem::take(&mut self.newly_interned_calls)
    }
}

fn replay_literal(literal: ReplayLiteral) -> Literal {
    match literal {
        ReplayLiteral::Unit => Literal::Unit,
        ReplayLiteral::Bool(value) => Literal::Bool(value),
        ReplayLiteral::I64(value) => Literal::Int(value),
        ReplayLiteral::F64(bits) => {
            Literal::Float(ordered_float::OrderedFloat(f64::from_bits(bits)))
        }
        ReplayLiteral::String(value) => Literal::String(value.to_string()),
    }
}

fn is_static_declaration(command: &Command) -> bool {
    matches!(
        command,
        Command::Sort { .. }
            | Command::Datatype { .. }
            | Command::Datatypes { .. }
            | Command::Constructor { .. }
            | Command::Relation { .. }
            | Command::Function { .. }
            | Command::AddRuleset(..)
            | Command::UnstableCombinedRuleset(..)
    )
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum DefinitionKey {
    Sort(String),
    Function(String),
    Ruleset(String),
}

#[derive(Default)]
struct CommandFootprint {
    provides: HashSet<DefinitionKey>,
    requires: HashSet<DefinitionKey>,
    opaque: bool,
}

impl CommandFootprint {
    fn require_sort(&mut self, name: &str) {
        self.requires.insert(DefinitionKey::Sort(name.to_owned()));
    }

    fn require_function(&mut self, name: &str) {
        self.requires
            .insert(DefinitionKey::Function(name.to_owned()));
    }

    fn require_ruleset(&mut self, name: &str) {
        if !name.is_empty() {
            self.requires
                .insert(DefinitionKey::Ruleset(name.to_owned()));
        }
    }

    fn require_schema(&mut self, schema: &Schema) {
        for sort in schema.input.iter().chain(&schema.outputs) {
            self.require_sort(sort);
        }
    }

    fn require_sort_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Var(_, name) => self.require_sort(name),
            Expr::Call(_, name, children) => {
                self.require_sort(name);
                for child in children {
                    self.require_sort_expr(child);
                }
            }
            Expr::Lit(..) => {}
        }
    }
}

fn command_footprint(command: &Command) -> CommandFootprint {
    let mut footprint = CommandFootprint::default();
    {
        let mut record_head = |head: String| {
            footprint.require_function(&head);
            head
        };
        let mut keep_leaf = |leaf: String| leaf;
        let _ = command
            .clone()
            .map_symbols(&mut record_head, &mut keep_leaf);
    }

    match command {
        Command::Sort {
            name,
            presort_and_args,
            uf,
            proof_func,
            container_rebuild,
            proof_constructors,
            ..
        } => {
            footprint.provides.insert(DefinitionKey::Sort(name.clone()));
            if let Some((presort, args)) = presort_and_args {
                footprint.require_sort(presort);
                for arg in args {
                    footprint.require_sort_expr(arg);
                }
            }
            if let Some((constructor, index)) = uf {
                footprint.require_function(constructor);
                if let Some(index) = index {
                    footprint.require_function(index);
                }
            }
            if let Some(proof_func) = proof_func {
                footprint.require_function(proof_func);
            }
            if let Some(spec) = container_rebuild {
                footprint.require_function(&spec.internal_rebuild_prim);
                if let Some(proof_prim) = &spec.internal_rebuild_proof_prim {
                    footprint.require_function(proof_prim);
                }
            }
            if let Some(names) = proof_constructors {
                for name in [
                    &names.congr,
                    &names.congr_all,
                    &names.trans,
                    &names.sym,
                    &names.normalize,
                    &names.fiat,
                ] {
                    footprint.require_function(name);
                }
            }
        }
        Command::Datatype { name, variants, .. } => {
            footprint.provides.insert(DefinitionKey::Sort(name.clone()));
            for variant in variants {
                footprint
                    .provides
                    .insert(DefinitionKey::Function(variant.name.clone()));
                for sort in &variant.types {
                    footprint.require_sort(sort);
                }
            }
        }
        Command::Datatypes { datatypes, .. } => {
            for (_, name, body) in datatypes {
                footprint.provides.insert(DefinitionKey::Sort(name.clone()));
                match body {
                    Subdatatypes::Variants(variants) => {
                        for variant in variants {
                            footprint
                                .provides
                                .insert(DefinitionKey::Function(variant.name.clone()));
                            for sort in &variant.types {
                                footprint.require_sort(sort);
                            }
                        }
                    }
                    Subdatatypes::NewSort(presort, args) => {
                        footprint.require_sort(presort);
                        for arg in args {
                            footprint.require_sort_expr(arg);
                        }
                    }
                }
            }
        }
        Command::Constructor {
            name,
            schema,
            term_constructor,
            ..
        }
        | Command::Function {
            name,
            schema,
            term_constructor,
            ..
        } => {
            footprint
                .provides
                .insert(DefinitionKey::Function(name.clone()));
            footprint.require_schema(schema);
            if let Some(constructor) = term_constructor {
                footprint.require_function(constructor);
            }
        }
        Command::Relation { name, inputs, .. } => {
            footprint
                .provides
                .insert(DefinitionKey::Function(name.clone()));
            for sort in inputs {
                footprint.require_sort(sort);
            }
        }
        Command::AddRuleset(_, name) => {
            footprint
                .provides
                .insert(DefinitionKey::Ruleset(name.clone()));
        }
        Command::UnstableCombinedRuleset(_, name, members) => {
            footprint
                .provides
                .insert(DefinitionKey::Ruleset(name.clone()));
            for member in members {
                footprint.require_ruleset(member);
            }
        }
        Command::Rule { rule } => footprint.require_ruleset(&rule.ruleset),
        Command::Rewrite(ruleset, ..) | Command::BiRewrite(ruleset, ..) => {
            footprint.require_ruleset(ruleset)
        }
        Command::LetCheck {
            expected_sort: Some(sort),
            ..
        } => footprint.require_sort(sort),
        Command::Action(..)
        | Command::Actions(..)
        | Command::LetBegin(..)
        | Command::LetCheck {
            expected_sort: None,
            ..
        }
        | Command::Check(..)
        | Command::RunSchedule(Schedule::RunRule(..)) => {}
        _ => footprint.opaque = true,
    }
    footprint
}

/// Retain the transitive static-definition closure of the actual replay roots.
///
/// Source dependencies are already closed exactly in [`selected_source_closure`].
/// This second, graph-neutral pass handles only declaration dependencies. An
/// opaque retained command conservatively keeps every declaration, while a
/// missing provider denotes a builtin or a declaration supplied by the replay
/// factory before trace capture.
fn retain_required_declarations(commands: Vec<Command>) -> Vec<Command> {
    let footprints = commands.iter().map(command_footprint).collect::<Vec<_>>();
    if footprints.iter().any(|footprint| footprint.opaque) {
        return commands;
    }

    let mut providers = HashMap::<DefinitionKey, usize>::default();
    for (index, (command, footprint)) in commands.iter().zip(&footprints).enumerate() {
        if is_static_declaration(command) {
            for definition in &footprint.provides {
                providers.entry(definition.clone()).or_insert(index);
            }
        }
    }

    let mut pending = Vec::new();
    for (command, footprint) in commands.iter().zip(&footprints) {
        if !is_static_declaration(command) {
            pending.extend(footprint.requires.iter().cloned());
        }
    }
    let mut selected = HashSet::<usize>::default();
    while let Some(requirement) = pending.pop() {
        let Some(provider) = providers.get(&requirement).copied() else {
            continue;
        };
        if selected.insert(provider) {
            pending.extend(footprints[provider].requires.iter().cloned());
        }
    }

    commands
        .into_iter()
        .enumerate()
        .filter_map(|(index, command)| {
            (!is_static_declaration(&command) || selected.contains(&index)).then_some(command)
        })
        .collect()
}

/// Close selected source roots over catalog-recorded source dependencies.
///
/// Unsupported source commands fail only when this closure reaches them, so an
/// unrelated unsupported command does not prevent slicing a supported check.
fn selected_source_closure(
    catalog: &CaptureCatalog,
    roots: &HashSet<SourceRef>,
) -> Result<HashSet<SourceRef>, ReplayError> {
    let mut selected = HashSet::default();
    let mut pending = roots.iter().cloned().collect::<Vec<_>>();
    while let Some(source) = pending.pop() {
        if !selected.insert(source.clone()) {
            continue;
        }
        match &source {
            SourceRef::Synthetic(_) => {
                let entry = catalog.source_commands.get(&source).ok_or_else(|| {
                    ReplayError::Invalid(format!("selected source {source:?} has no catalog entry"))
                })?;
                if let Some(reason) = &entry.unsupported {
                    return Err(ReplayError::Unsupported(format!(
                        "selected source {source:?}: {reason}"
                    )));
                }
                pending.extend(entry.dependencies.iter().cloned());
            }
            SourceRef::InputRow { command, .. } => {
                let entry = catalog.input_commands.get(command).ok_or_else(|| {
                    ReplayError::Invalid(format!(
                        "selected input source {source:?} has no catalog entry"
                    ))
                })?;
                if let Some(reason) = &entry.unsupported {
                    return Err(ReplayError::Unsupported(format!(
                        "selected input source {source:?}: {reason}"
                    )));
                }
            }
        }
    }
    Ok(selected)
}

/// Re-materialize exactly the selected input rows as source literal actions.
///
/// Each cell is copied from the replay-term literal interned during capture, so
/// the artifact is independent of the original input file and still preserves
/// exact floating-point bits.
fn selected_input_rows(
    view: &mut TraceView<'_>,
    catalog: &CaptureCatalog,
    sources: &HashSet<SourceRef>,
) -> Result<Vec<ReplaySource>, ReplayError> {
    let mut selected = BTreeMap::<u64, BTreeSet<u64>>::new();
    for source in sources {
        if let SourceRef::InputRow { command, line } = source {
            selected.entry(*command).or_default().insert(*line);
        }
    }
    let mut rows = Vec::new();
    for (command, selected_lines) in selected {
        let entry = catalog.input_commands.get(&command).ok_or_else(|| {
            ReplayError::Invalid(format!("input command {command} is absent from catalog"))
        })?;
        for line in selected_lines {
            let row = entry
                .rows
                .binary_search_by_key(&line, |row| row.line)
                .ok()
                .and_then(|index| entry.rows.get(index))
                .ok_or_else(|| {
                    ReplayError::Invalid(format!(
                        "selected input row {command}:{line} is absent from captured history"
                    ))
                })?;
            let literals = row
                .terms
                .iter()
                .map(|term| match view.replay_term(*term)? {
                    ReplayTerm::Literal { literal, .. } => Ok(replay_literal(literal)),
                    ReplayTerm::Call { .. } => Err(ReplayError::Invalid(format!(
                        "selected input row {command}:{line} contains a structural call"
                    ))),
                })
                .collect::<Result<Box<[_]>, _>>()?;
            rows.push(ReplaySource {
                after_wave: entry.after_wave,
                catalog_ordinal: catalog.command_catalog[entry.command].surface_command,
                kind: ReplaySourceKind::InputRow {
                    line,
                    function: entry.function.clone(),
                    literals,
                },
            });
        }
    }
    Ok(rows)
}

/// Restore selected immutable globals at their surface variable occurrences.
///
/// Normalization lowers a global read to a private zero-argument lookup. Replay
/// emits the selected surface `let`, so retained rules must refer to that global
/// again and must reject any global whose source was not selected.
fn restore_selected_rule_globals(
    command: Command,
    catalog: &CaptureCatalog,
    sources: &HashSet<SourceRef>,
    rule: &str,
) -> Result<Command, ReplayError> {
    let mut missing = None;
    let command = command.visit_exprs(&mut |expr| match expr {
        Expr::Call(span, name, children) if children.is_empty() => {
            let Some(source) = catalog.immutable_globals.get(&name) else {
                return Expr::Call(span, name, children);
            };
            if sources.contains(source) {
                // Global removal lowers a source-level variable to a lookup
                // of its private zero-argument function. Replay emits the
                // selected source `let` instead, so restore only that leaf;
                // the rest of the retained rule stays normalized.
                Expr::Var(span, name)
            } else {
                missing.get_or_insert((name.clone(), source.clone()));
                Expr::Call(span, name, children)
            }
        }
        other => other,
    });
    if let Some((name, source)) = missing {
        return Err(ReplayError::Invalid(format!(
            "retained rule `{rule}` reads immutable global `{name}` from unselected source {source:?}"
        )));
    }
    Ok(command)
}

/// Ensure a retained surface rewrite reads only selected immutable globals.
fn validate_selected_surface_globals(
    command: &Command,
    catalog: &CaptureCatalog,
    sources: &HashSet<SourceRef>,
    rule: &str,
) -> Result<(), ReplayError> {
    let mut missing = None;
    let _ = command.clone().visit_exprs(&mut |expr| {
        if let Expr::Var(_, name) = &expr
            && let Some(source) = catalog.immutable_globals.get(name)
            && !sources.contains(source)
        {
            missing.get_or_insert((name.clone(), source.clone()));
        }
        expr
    });
    if let Some((name, source)) = missing {
        return Err(ReplayError::Invalid(format!(
            "retained rewrite `{rule}` reads immutable global `{name}` from unselected source {source:?}"
        )));
    }
    Ok(())
}

/// Recover and validate the normalized rule command for one catalog ordinal.
fn normalized_rule_command(
    catalog: &CaptureCatalog,
    sources: &HashSet<SourceRef>,
    ordinal: u32,
    entry: &RuleCatalogEntry,
) -> Result<Command, ReplayError> {
    let command = catalog
        .command_catalog
        .get(entry.command)
        .ok_or_else(|| {
            ReplayError::Invalid(format!(
                "rule ordinal {ordinal} cites missing command {}",
                entry.command
            ))
        })?
        .command
        .clone();
    let command = restore_selected_rule_globals(command, catalog, sources, &entry.replay_name)?;
    let Command::Rule { rule } = &command else {
        return Err(ReplayError::Invalid(format!(
            "rule ordinal {ordinal} does not map to a normalized rule command"
        )));
    };
    if rule.name != entry.replay_name || rule.ruleset != entry.ruleset {
        return Err(ReplayError::Invalid(format!(
            "rule ordinal {ordinal} catalog identity disagrees with its normalized command"
        )));
    }
    Ok(command)
}

/// Reconstruct a retained rewrite from its original surface command.
///
/// Selected normalized directions are validated against a single catalog
/// identity, then grouped by their surface command. A one-way rewrite remains
/// a `rewrite` with its stable replay name. A bidirectional source remains a
/// `birewrite` in its original orientation even when only one recorded
/// direction fired; lowering never exposes the private directional rules.
fn retained_rewrite_command(
    catalog: &CaptureCatalog,
    sources: &HashSet<SourceRef>,
    surface_command: usize,
    ordinals: &[u32],
) -> Result<Command, ReplayError> {
    let surface = catalog
        .surface_command_catalog
        .get(surface_command)
        .and_then(Option::as_ref)
        .ok_or_else(|| {
            ReplayError::Invalid(format!(
                "retained rewrite cites missing surface command {surface_command}"
            ))
        })?
        .clone();

    let mut forward = None;
    let mut reverse = None;
    let mut expected_bidirectional = None;
    let mut expected_base_name = None;
    let mut expected_ruleset = None;
    for &ordinal in ordinals {
        let entry = catalog.rule_catalog.get(ordinal as usize).ok_or_else(|| {
            ReplayError::Invalid(format!("selected rule ordinal {ordinal} is absent"))
        })?;
        let _ = normalized_rule_command(catalog, sources, ordinal, entry)?;
        let CatalogRuleSurface::Rewrite {
            surface_command: entry_surface,
            direction,
            bidirectional,
            base_name,
        } = &entry.surface
        else {
            return Err(ReplayError::Invalid(format!(
                "rule ordinal {ordinal} is not cataloged as a rewrite"
            )));
        };
        if *entry_surface != surface_command {
            return Err(ReplayError::Invalid(format!(
                "rule ordinal {ordinal} cites rewrite surface command {entry_surface}, expected {surface_command}"
            )));
        }
        if expected_bidirectional
            .replace(*bidirectional)
            .is_some_and(|expected| expected != *bidirectional)
            || expected_base_name
                .replace(base_name.clone())
                .is_some_and(|expected| expected != *base_name)
            || expected_ruleset
                .replace(entry.ruleset.clone())
                .is_some_and(|expected| expected != entry.ruleset)
        {
            return Err(ReplayError::Invalid(format!(
                "retained rewrite surface command {surface_command} has inconsistent catalog entries"
            )));
        }
        let slot = match direction {
            RewriteDirection::Forward => &mut forward,
            RewriteDirection::Reverse => &mut reverse,
        };
        if slot.replace(entry).is_some() {
            return Err(ReplayError::Invalid(format!(
                "retained rewrite surface command {surface_command} contains duplicate {direction:?} directions"
            )));
        }
    }

    let bidirectional = expected_bidirectional.ok_or_else(|| {
        ReplayError::Invalid(format!(
            "retained rewrite surface command {surface_command} has no rule directions"
        ))
    })?;
    let base_name = expected_base_name.expect("rewrite direction has no base name");
    let ruleset = expected_ruleset.expect("rewrite direction has no ruleset");
    validate_selected_surface_globals(&surface, catalog, sources, &base_name)?;

    match surface {
        Command::Rewrite(surface_ruleset, mut rewrite, subsume) if !bidirectional => {
            let entry = forward.ok_or_else(|| {
                ReplayError::Invalid(format!(
                    "one-way rewrite surface command {surface_command} retained no forward direction"
                ))
            })?;
            if reverse.is_some() || surface_ruleset != ruleset {
                return Err(ReplayError::Invalid(format!(
                    "one-way rewrite surface command {surface_command} disagrees with its catalog"
                )));
            }
            rewrite.name.clone_from(&entry.replay_name);
            Ok(Command::Rewrite(surface_ruleset, rewrite, subsume))
        }
        Command::BiRewrite(surface_ruleset, mut rewrite) if bidirectional => {
            if surface_ruleset != ruleset {
                return Err(ReplayError::Invalid(format!(
                    "bidirectional rewrite surface command {surface_command} disagrees with its ruleset"
                )));
            }
            rewrite.name = base_name;
            Ok(Command::BiRewrite(surface_ruleset, rewrite))
        }
        Command::Rewrite(..) | Command::BiRewrite(..) => Err(ReplayError::Invalid(format!(
            "rewrite surface command {surface_command} disagrees with its directionality"
        ))),
        _ => Err(ReplayError::Invalid(format!(
            "retained rewrite surface command {surface_command} is not a rewrite"
        ))),
    }
}

/// Lower a closed [`Slice`] and its capture catalog into owned replay IR.
///
/// The lowering proceeds in four coupled phases:
///
/// 1. close source dependencies and recover static declarations, source
///    actions, and retained rule surfaces from the catalog;
/// 2. copy structural binding terms, schedule their checked aliases within the
///    captured occurrence lifetimes, and group grounded firings by wave;
/// 3. recover every successful check and merge all source, wave, and check events in
///    recorded chronology; and
/// 4. return only owned names, literals, commands, and structural recipes.
///
/// Alias canonicalization is intentionally conservative. Dependencies can move
/// an alias earlier within its valid retained boundaries, but selected
/// removals split reuse epochs and a producer deletion is an exclusive upper
/// bound on capture.
fn lower_slice_to_owned_program(
    catalog: &CaptureCatalog,
    view: &mut TraceView<'_>,
    slice: &Slice,
) -> Result<ReplayProgram, ReplayError> {
    let sources = selected_source_closure(catalog, &slice.source_roots)?;
    let mut retained_rules = BTreeSet::new();
    let mut firings = Vec::with_capacity(slice.firing_bindings.len());
    let mut firing_ids = slice.firing_bindings.keys().copied().collect::<Vec<_>>();
    firing_ids.sort_unstable();
    for id in firing_ids {
        let firing = view.firing(id)?;
        retained_rules.insert(firing.rule);
        firings.push((
            id,
            firing.rule,
            firing.wave.get(),
            firing.history_cutoff.get(),
        ));
    }

    let mut setup = Vec::new();
    for (ordinal, command) in catalog.surface_command_catalog.iter().enumerate() {
        if command.as_ref().is_some_and(is_static_declaration) {
            setup.push(ReplaySetup {
                catalog_ordinal: ordinal,
                command: command
                    .clone()
                    .expect("static surface command disappeared from replay catalog"),
            });
        }
    }
    let mut source_events = BTreeMap::new();
    for source in &sources {
        let SourceRef::Synthetic(_) = source else {
            continue;
        };
        let entry = &catalog.source_commands[source];
        let normalized = catalog.command_catalog.get(entry.command).ok_or_else(|| {
            ReplayError::Invalid(format!(
                "source {source:?} cites missing command {}",
                entry.command
            ))
        })?;
        let surface_command = normalized.surface_command;
        let surface = catalog
            .surface_command_catalog
            .get(surface_command)
            .and_then(Option::as_ref)
            .ok_or_else(|| {
                ReplayError::Invalid(format!(
                    "source {source:?} cites missing surface command {surface_command}"
                ))
            })?;
        // Surface lets are replayed as lets. Emitting their normalized
        // internal function and set bypasses ordinary proof-global lowering
        // and can manufacture unbound tuple values on the fresh proof graph.
        let command = surface.clone();
        if !matches!(
            command,
            Command::Action(_) | Command::Actions(_) | Command::LetBegin(..)
        ) {
            return Err(ReplayError::Invalid(format!(
                "source {source:?} does not map to an atomic action command"
            )));
        }
        source_events
            .entry(surface_command)
            .or_insert(ReplaySource {
                after_wave: entry.after_wave,
                catalog_ordinal: surface_command,
                kind: ReplaySourceKind::Command(Box::new(command)),
            });
    }
    let mut source_events = source_events.into_values().collect::<Vec<_>>();
    source_events.extend(selected_input_rows(view, catalog, &sources)?);
    let mut rewrite_groups = BTreeMap::<usize, Vec<u32>>::new();
    for rule in &retained_rules {
        let entry = catalog.rule_catalog.get(*rule as usize).ok_or_else(|| {
            ReplayError::Invalid(format!("selected rule ordinal {rule} is absent"))
        })?;
        match entry.surface {
            CatalogRuleSurface::Normalized => {
                setup.push(ReplaySetup {
                    catalog_ordinal: catalog.command_catalog[entry.command].surface_command,
                    command: normalized_rule_command(catalog, &sources, *rule, entry)?,
                });
            }
            CatalogRuleSurface::Rewrite {
                surface_command, ..
            } => rewrite_groups
                .entry(surface_command)
                .or_default()
                .push(*rule),
        }
    }
    for (surface_command, rules) in rewrite_groups {
        setup.push(ReplaySetup {
            catalog_ordinal: surface_command,
            command: retained_rewrite_command(catalog, &sources, surface_command, &rules)?,
        });
    }
    setup.sort_by_key(|entry| entry.catalog_ordinal);

    // A checked alias remains a valid name for later monotone unions/rekeys,
    // but not across removal/recreation: identical syntax can then denote a
    // fresh native occurrence. Exact producer tombstones also end that call's
    // capture window. Use a conservative global removal epoch for structural
    // deduplication so unrelated deletions may inhibit reuse but can never
    // merge two occurrence lifetimes.
    let mut alias_reset_positions = Vec::new();
    let mut selected_removal_by_fact = HashMap::<FactId, u64>::default();
    for index in slice.replay_removals.iter().copied() {
        let removal = view.removal(index)?;
        let position = removal.position.get();
        alias_reset_positions.push(position);
        selected_removal_by_fact
            .entry(removal.removed_fact)
            .and_modify(|current| *current = (*current).min(position))
            .or_insert(position);
    }
    alias_reset_positions.sort_unstable();
    alias_reset_positions.dedup();

    let mut terms = OwnedTermBuilder::new(view, catalog)?;
    let mut waves = BTreeMap::<u64, Vec<ReplayFiring>>::new();
    let mut wave_setup_bounds = BTreeMap::<u64, usize>::new();
    let mut aliases_by_wave = BTreeMap::<u64, Vec<ReplayAlias>>::new();
    let mut alias_wave_by_term = HashMap::<ReplayTermRef, u64>::default();
    let mut alias_ordinal_by_term = HashMap::<ReplayTermRef, usize>::default();
    // A replay boundary observes one immutable pre-wave database. Repeated
    // structurally identical calls within one removal epoch must therefore
    // resolve to the same runtime value and need only one checked alias.
    let mut source_call_by_boundary =
        HashMap::<(u64, Option<u64>, ReplayTermId), ReplayTermRef>::default();
    let mut canonical_call_by_boundary =
        HashMap::<(usize, Option<u64>, OwnedReplayTerm), ReplayTermRef>::default();
    let mut canonical_term = HashMap::<ReplayTermRef, ReplayTermRef>::default();
    let mut wave_history_cutoffs = BTreeMap::<u64, u64>::new();
    for (_, _, wave, history_cutoff) in &firings {
        wave_history_cutoffs
            .entry(*wave)
            .and_modify(|current| *current = (*current).min(*history_cutoff))
            .or_insert(*history_cutoff);
    }
    let mut next_alias = 0usize;
    for (id, rule, wave, _) in firings {
        let rule_entry = &catalog.rule_catalog[rule as usize];
        let catalog_ordinal = catalog.command_catalog[rule_entry.command].surface_command;
        wave_setup_bounds
            .entry(wave)
            .and_modify(|bound| *bound = (*bound).max(catalog_ordinal))
            .or_insert(catalog_ordinal);
        let binding_plans = slice.firing_bindings.get(&id).ok_or_else(|| {
            ReplayError::Invalid(format!(
                "selected firing {} has no projected bindings",
                id.get()
            ))
        })?;
        if binding_plans.len() != rule_entry.variables.len() {
            return Err(ReplayError::Invalid(format!(
                "selected firing {} has {} bindings for {} rule variables",
                id.get(),
                binding_plans.len(),
                rule_entry.variables.len()
            )));
        }
        let mut bindings = Vec::with_capacity(binding_plans.len());
        for (variable, binding_plan) in rule_entry.variables.iter().zip(binding_plans.iter()) {
            let variable_name = &variable.name;
            let expected_sort = &variable.sort;
            match (&rule_entry.surface, &variable.role) {
                (CatalogRuleSurface::Normalized, RuleBindingRole::RewriteRoot) => {
                    return Err(ReplayError::Invalid(format!(
                        "normalized rule `{}` unexpectedly owns rewrite-root binding `{variable_name}`",
                        rule_entry.replay_name
                    )));
                }
                // The fresh graph lowers the selected source global again, and
                // may choose a different private normalized input name. Its
                // selected source reconstructs the value, so the private
                // recorded term and binding must not enter the artifact.
                (CatalogRuleSurface::Rewrite { .. }, RuleBindingRole::DerivedGlobal(global)) => {
                    let source = catalog.immutable_globals.get(global).ok_or_else(|| {
                        ReplayError::Invalid(format!(
                            "surface rewrite `{}` maps binding `{variable_name}` to unknown immutable global `{global}`",
                            rule_entry.replay_name
                        ))
                    })?;
                    if !sources.contains(source) {
                        return Err(ReplayError::Invalid(format!(
                            "surface rewrite `{}` requires immutable global `{global}` from unselected source {source:?}",
                            rule_entry.replay_name
                        )));
                    }
                    continue;
                }
                _ => {}
            }
            let term = terms.intern(binding_plan.term)?;
            let actual_sort = terms.nodes[term.index()].sort();
            if actual_sort != expected_sort {
                return Err(ReplayError::Invalid(format!(
                    "firing {} variable `{variable_name}` expects `{expected_sort}` but term owns `{actual_sort}`",
                    id.get()
                )));
            }
            let new_calls = terms.take_new_calls();
            if new_calls.len() != binding_plan.aliases.len() {
                return Err(ReplayError::Invalid(format!(
                    "firing {} binding `{variable_name}` owns {} structural call occurrences but has {} alias plans",
                    id.get(),
                    new_calls.len(),
                    binding_plan.aliases.len()
                )));
            }
            for ((source_call, call), plan) in
                new_calls.into_iter().zip(binding_plan.aliases.iter())
            {
                let plan = *plan;
                let canonical_children = match &terms.nodes[call.index()] {
                    OwnedReplayTerm::Literal { .. } => unreachable!("Call queue contained literal"),
                    OwnedReplayTerm::Call { children, .. } => children
                        .iter()
                        .map(|child| canonical_term.get(child).copied().unwrap_or(*child))
                        .collect::<Vec<_>>(),
                };
                let dependency_wave = canonical_children
                    .iter()
                    .filter_map(|child| alias_wave_by_term.get(child).copied())
                    .max()
                    .unwrap_or(0);
                let OwnedReplayTerm::Call { children, .. } = &mut terms.nodes[call.index()] else {
                    unreachable!("Call queue contained literal")
                };
                *children = canonical_children.into_boxed_slice();
                // Producer existence does not imply that the replayed child
                // spellings address its key yet; equality/rekey support may
                // become visible only at a later retained boundary. A selected
                // tombstone for this exact producer is the exclusive upper
                // bound: the alias must be checked before replay deletes it.
                let history_ready_after = plan.ready_after.get();
                let live_before = plan
                    .producer
                    .and_then(|producer| selected_removal_by_fact.get(&producer).copied());
                let alias_wave = wave_history_cutoffs
                    .iter()
                    .find_map(|(candidate_wave, candidate_cutoff)| {
                        (*candidate_wave >= dependency_wave
                            && *candidate_wave <= wave
                            && *candidate_cutoff >= history_ready_after
                            && live_before.is_none_or(|end| *candidate_cutoff < end))
                        .then_some(*candidate_wave)
                    })
                    .ok_or_else(|| {
                        ReplayError::Invalid(format!(
                            "firing {} binding `{variable_name}` call {} has no retained pre-wave point in its availability/readiness/liveness window",
                            id.get(),
                            source_call.get()
                        ))
                    })?;
                let fresh_after = plan.fresh_after.map(|position| position.get());
                if let Some(previous) = source_call_by_boundary
                    .get(&(alias_wave, fresh_after, source_call))
                    .copied()
                {
                    if terms.nodes[previous.index()] != terms.nodes[call.index()] {
                        return Err(ReplayError::Invalid(format!(
                            "replay term {} has inconsistent structure at wave {alias_wave}",
                            source_call.get()
                        )));
                    }
                } else {
                    source_call_by_boundary.insert((alias_wave, fresh_after, source_call), call);
                }
                let alias_history_cutoff = *wave_history_cutoffs
                    .get(&alias_wave)
                    .expect("selected alias wave has no history cutoff");
                let alias_epoch = alias_reset_positions
                    .partition_point(|position| *position <= alias_history_cutoff);
                let structural_key = (alias_epoch, fresh_after, terms.nodes[call.index()].clone());
                if let Some(canonical) = canonical_call_by_boundary.get(&structural_key).copied() {
                    let canonical_wave = alias_wave_by_term[&canonical];
                    let canonical_wave = if alias_wave < canonical_wave {
                        let aliases = aliases_by_wave
                            .get_mut(&canonical_wave)
                            .expect("canonical alias wave disappeared");
                        let index = aliases
                            .iter()
                            .position(|alias| alias.term == canonical)
                            .expect("canonical alias disappeared from its wave");
                        let alias = aliases.remove(index);
                        aliases_by_wave.entry(alias_wave).or_default().push(alias);
                        alias_wave_by_term.insert(canonical, alias_wave);
                        alias_wave
                    } else {
                        canonical_wave
                    };
                    canonical_term.insert(call, canonical);
                    alias_wave_by_term.insert(call, canonical_wave);
                    continue;
                }
                canonical_call_by_boundary.insert(structural_key, call);
                aliases_by_wave
                    .entry(alias_wave)
                    .or_default()
                    .push(ReplayAlias {
                        name: format!("$@__slice_replay_{next_alias}"),
                        term: call,
                    });
                alias_wave_by_term.insert(call, alias_wave);
                alias_ordinal_by_term.insert(call, next_alias);
                next_alias += 1;
            }
            bindings.push(ReplayBinding {
                variable: variable_name.clone(),
                term: canonical_term.get(&term).copied().unwrap_or(term),
            });
        }
        waves.entry(wave).or_default().push(ReplayFiring {
            replay_name: rule_entry.replay_name.clone(),
            bindings: bindings.into_boxed_slice(),
        });
    }
    let term_nodes = std::mem::take(&mut terms.nodes);
    drop(terms);
    for aliases in aliases_by_wave.values_mut() {
        aliases.sort_unstable_by_key(|alias| alias_ordinal_by_term[&alias.term]);
    }

    let mut events = source_events
        .into_iter()
        .map(ReplayEvent::Source)
        .collect::<Vec<_>>();
    for (wave, firings) in waves {
        events.push(ReplayEvent::Wave(ReplayWave {
            wave,
            setup_bound: wave_setup_bounds
                .remove(&wave)
                .expect("selected replay wave has no setup bound"),
            aliases: aliases_by_wave
                .remove(&wave)
                .unwrap_or_default()
                .into_boxed_slice(),
            firings: firings.into_boxed_slice(),
        }));
    }
    for root in view.check_roots() {
        let check = root.check;
        let command_index = catalog.check_commands.get(&check).ok_or_else(|| {
            ReplayError::Invalid(format!("selected check {check} has no catalog command"))
        })?;
        let normalized = catalog.command_catalog.get(*command_index).ok_or_else(|| {
            ReplayError::Invalid(format!(
                "selected check {check} cites missing command {command_index}"
            ))
        })?;
        let surface_command = normalized.surface_command;
        let command = catalog
            .surface_command_catalog
            .get(surface_command)
            .and_then(Option::as_ref)
            .ok_or_else(|| {
                ReplayError::Invalid(format!(
                    "selected check {check} cites missing surface command {surface_command}"
                ))
            })?
            .clone();
        if !matches!(command, Command::Check(..)) {
            return Err(ReplayError::Invalid(format!(
                "selected check {check} maps to a non-check command"
            )));
        }
        events.push(ReplayEvent::Check(Box::new(ReplayCheck {
            after_wave: root.wave.get(),
            catalog_ordinal: surface_command,
            command,
        })));
    }
    events.sort_by_key(ReplayEvent::chronology_key);

    Ok(ReplayProgram {
        setup,
        terms: term_nodes,
        events,
    })
}

/// Build graph-neutral replay IR from a healthy native capture and selection.
///
/// The concrete backend is borrowed only while trace records are copied into
/// owned data. Missing capture, poisoned catalog state, and unsupported backend
/// implementations fail before a partial replay program is returned.
pub(super) fn build_replay_program(
    egraph: &EGraph,
    slice: &Slice,
) -> Result<ReplayProgram, ReplayError> {
    let catalog = egraph
        .capture_catalog
        .as_ref()
        .ok_or(ReplayError::Disabled)?;
    catalog
        .ensure_healthy()
        .map_err(|error| ReplayError::Invalid(error.to_string()))?;
    let bridge = egraph
        .backend
        .as_any()
        .downcast_ref::<egglog_bridge::EGraph>()
        .ok_or(ReplayError::UnsupportedBackend)?;
    bridge.with_trace_view(|view| Ok(lower_slice_to_owned_program(catalog, view, slice)))?
}

#[cfg(test)]
#[path = "replay_tests.rs"]
mod tests;
