//! Owned, graph-neutral causal replay input.
//!
//! This module is deliberately a cold boundary. It may inspect selected raw
//! receipts while the recording graph is alive, but none of its output owns a
//! backend id, runtime value, receipt handle, or borrow into that graph.

use std::collections::{BTreeMap, BTreeSet, HashSet as StdHashSet};

use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::ast::{Command, FunctionSubtype};
use crate::causal_slice::CausalSlice;
use crate::core_relations::{
    CausalReceiptView, ReplayLiteral, ReplayOpId, ReplaySortId, ReplayTerm, ReplayTermId, SourceRef,
};
use crate::util::{HashMap, HashSet};
use crate::{CausalState, EGraph, Literal, ReplayOpKey};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ReplayTermRef(u32);

impl ReplayTermRef {
    fn from_index(index: usize) -> Result<Self, CausalReplayError> {
        Ok(Self(index.try_into().map_err(|_| {
            CausalReplayError::Invalid("owned replay term arena exceeds u32".into())
        })?))
    }

    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OwnedReplayOp {
    pub(crate) name: String,
    pub(crate) inputs: Box<[String]>,
    pub(crate) output: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum OwnedReplayTerm {
    Literal {
        sort: String,
        literal: Literal,
    },
    Call {
        sort: String,
        op: OwnedReplayOp,
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReplayTermArena {
    pub(crate) nodes: Vec<OwnedReplayTerm>,
}

#[derive(Clone, Debug)]
pub(crate) enum ReplaySetupKind {
    Command(Command),
}

#[derive(Clone, Debug)]
pub(crate) struct ReplaySetup {
    pub(crate) catalog_ordinal: usize,
    pub(crate) kind: ReplaySetupKind,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum OwnedSourceRef {
    Synthetic(u64),
    InputRow { command: u64, line: u64 },
}

impl From<&SourceRef> for OwnedSourceRef {
    fn from(source: &SourceRef) -> Self {
        match source {
            SourceRef::Synthetic(ordinal) => Self::Synthetic(*ordinal),
            SourceRef::InputRow { command, line } => Self::InputRow {
                command: *command,
                line: *line,
            },
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) enum ReplaySourceKind {
    Command(Command),
    InputRow {
        function: String,
        line: u64,
        literals: Box<[Literal]>,
    },
}

#[derive(Clone, Debug)]
pub(crate) struct ReplaySource {
    pub(crate) catalog_ordinal: usize,
    pub(crate) source: OwnedSourceRef,
    pub(crate) kind: ReplaySourceKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReplayAlias {
    pub(crate) name: String,
    pub(crate) term: ReplayTermRef,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReplayBinding {
    pub(crate) variable: String,
    pub(crate) sort: String,
    pub(crate) term: ReplayTermRef,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReplayFiring {
    pub(crate) receipt_match: u64,
    pub(crate) rule_ordinal: u32,
    pub(crate) replay_name: String,
    pub(crate) bindings: Box<[ReplayBinding]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReplayWave {
    pub(crate) wave: u64,
    pub(crate) position: u64,
    pub(crate) aliases: Box<[ReplayAlias]>,
    pub(crate) firings: Box<[ReplayFiring]>,
}

#[derive(Clone, Debug)]
pub(crate) struct ReplayCheck {
    pub(crate) check: u32,
    pub(crate) after_wave: u64,
    pub(crate) catalog_ordinal: usize,
    pub(crate) position: u64,
    pub(crate) command: Command,
}

#[derive(Clone, Debug)]
pub(crate) enum ReplayEvent {
    Source(ReplaySource),
    Wave(ReplayWave),
    Check(ReplayCheck),
}

impl ReplayEvent {
    fn chronology_key(&self) -> (u64, u8, usize, u64) {
        match self {
            Self::Source(source) => {
                let line = match source.source {
                    OwnedSourceRef::Synthetic(_) => 0,
                    OwnedSourceRef::InputRow { line, .. } => line,
                };
                (0, 0, source.catalog_ordinal, line)
            }
            Self::Wave(wave) => (wave.wave, 0, 0, 0),
            Self::Check(check) if check.after_wave == 0 => (0, 0, check.catalog_ordinal, u64::MAX),
            Self::Check(check) => (check.after_wave, 1, check.catalog_ordinal, 0),
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct ReplayIrStats {
    pub(crate) setup_commands: u64,
    pub(crate) logical_sources: u64,
    pub(crate) closed_sources: u64,
    pub(crate) source_events: u64,
    pub(crate) input_rows: u64,
    pub(crate) terms: u64,
    pub(crate) aliases: u64,
    pub(crate) firings: u64,
    pub(crate) waves: u64,
    pub(crate) checks: u64,
}

#[derive(Clone, Debug)]
pub(crate) struct CausalReplayIr {
    pub(crate) setup: Vec<ReplaySetup>,
    pub(crate) terms: ReplayTermArena,
    pub(crate) events: Vec<ReplayEvent>,
    pub(crate) stats: ReplayIrStats,
}

#[derive(Debug, Error)]
pub(crate) enum CausalReplayError {
    #[error("causal replay is unavailable without exact receipt capture")]
    Disabled,
    #[error("causal replay requires the main native backend")]
    UnsupportedBackend,
    #[error("causal replay receipt error: {0}")]
    Receipt(String),
    #[error("causal replay input error: {0}")]
    Input(String),
    #[error("invalid causal replay: {0}")]
    Invalid(String),
    #[error("unsupported causal replay: {0}")]
    Unsupported(String),
}

struct OwnedTermBuilder<'a, 'view> {
    view: &'a mut CausalReceiptView<'view>,
    sorts: HashMap<ReplaySortId, String>,
    ops: HashMap<ReplayOpId, OwnedReplayOp>,
    memo: HashMap<ReplayTermId, ReplayTermRef>,
    visiting: HashSet<ReplayTermId>,
    nodes: Vec<OwnedReplayTerm>,
    newly_interned_calls: Vec<ReplayTermRef>,
}

impl<'a, 'view> OwnedTermBuilder<'a, 'view> {
    fn new(
        view: &'a mut CausalReceiptView<'view>,
        causal: &CausalState,
    ) -> Result<Self, CausalReplayError> {
        let mut sorts = HashMap::default();
        for (name, id) in &causal.sort_ids {
            if sorts.insert(*id, name.clone()).is_some() {
                return Err(CausalReplayError::Invalid(format!(
                    "replay sort id {} has multiple names",
                    id.get()
                )));
            }
        }
        let mut ops = HashMap::default();
        for (key, id) in &causal.op_ids {
            let ReplayOpKey {
                name,
                inputs,
                output,
            } = key;
            let op = OwnedReplayOp {
                name: name.clone(),
                inputs: inputs.clone().into_boxed_slice(),
                output: output.clone(),
            };
            if ops.insert(*id, op).is_some() {
                return Err(CausalReplayError::Invalid(format!(
                    "replay operation id {} has multiple signatures",
                    id.get()
                )));
            }
        }
        Ok(Self {
            view,
            sorts,
            ops,
            memo: HashMap::default(),
            visiting: HashSet::default(),
            nodes: Vec::new(),
            newly_interned_calls: Vec::new(),
        })
    }

    fn intern(&mut self, source: ReplayTermId) -> Result<ReplayTermRef, CausalReplayError> {
        if source.is_missing() {
            return Err(CausalReplayError::Invalid(
                "selected binding owns a missing replay term".into(),
            ));
        }
        if let Some(term) = self.memo.get(&source) {
            return Ok(*term);
        }
        if !self.visiting.insert(source) {
            return Err(CausalReplayError::Invalid(format!(
                "replay term {} is cyclic",
                source.get()
            )));
        }
        let node = self
            .view
            .replay_term(source)
            .map_err(|error| CausalReplayError::Receipt(error.to_string()))?;
        let owned = match node {
            ReplayTerm::Literal { sort, literal } => OwnedReplayTerm::Literal {
                sort: self.sort_name(sort)?.to_owned(),
                literal: replay_literal(literal)?,
            },
            ReplayTerm::Call { sort, op, children } => {
                let sort_name = self.sort_name(sort)?.to_owned();
                let op = self.ops.get(&op).cloned().ok_or_else(|| {
                    CausalReplayError::Invalid("replay term uses an unknown operation id".into())
                })?;
                if op.output != sort_name {
                    return Err(CausalReplayError::Invalid(format!(
                        "replay operation `{}` returns `{}` but term is typed `{sort_name}`",
                        op.name, op.output
                    )));
                }
                if op.inputs.len() != children.len() {
                    return Err(CausalReplayError::Invalid(format!(
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
                        return Err(CausalReplayError::Invalid(format!(
                            "replay operation `{}` child {index} expects `{}` but owns `{actual}`",
                            op.name, op.inputs[index]
                        )));
                    }
                    owned_children.push(child);
                }
                OwnedReplayTerm::Call {
                    sort: sort_name,
                    op,
                    children: owned_children.into_boxed_slice(),
                }
            }
        };
        self.visiting.remove(&source);
        let is_call = matches!(owned, OwnedReplayTerm::Call { .. });
        let term = ReplayTermRef::from_index(self.nodes.len())?;
        self.nodes.push(owned);
        self.memo.insert(source, term);
        if is_call {
            self.newly_interned_calls.push(term);
        }
        Ok(term)
    }

    fn sort_name(&self, sort: ReplaySortId) -> Result<&str, CausalReplayError> {
        self.sorts.get(&sort).map(String::as_str).ok_or_else(|| {
            CausalReplayError::Invalid(format!("unknown replay sort id {}", sort.get()))
        })
    }

    fn take_new_calls(&mut self) -> Vec<ReplayTermRef> {
        std::mem::take(&mut self.newly_interned_calls)
    }
}

fn replay_literal(literal: ReplayLiteral) -> Result<Literal, CausalReplayError> {
    Ok(match literal {
        ReplayLiteral::Unit => Literal::Unit,
        ReplayLiteral::Bool(value) => Literal::Bool(value),
        ReplayLiteral::I64(value) => Literal::Int(value),
        ReplayLiteral::F64(bits) => {
            Literal::Float(ordered_float::OrderedFloat(f64::from_bits(bits)))
        }
        ReplayLiteral::String(value) => Literal::String(value.to_string()),
        ReplayLiteral::Internal(value) => {
            return Err(CausalReplayError::Unsupported(format!(
                "internal replay literal {value} has no source representation"
            )));
        }
    })
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

fn selected_source_closure(
    causal: &CausalState,
    roots: &HashSet<SourceRef>,
) -> Result<HashSet<SourceRef>, CausalReplayError> {
    let mut selected = HashSet::default();
    let mut pending = roots.iter().cloned().collect::<Vec<_>>();
    while let Some(source) = pending.pop() {
        if !selected.insert(source.clone()) {
            continue;
        }
        match &source {
            SourceRef::Synthetic(_) => {
                let entry = causal.source_commands.get(&source).ok_or_else(|| {
                    CausalReplayError::Invalid(format!(
                        "selected source {source:?} has no catalog entry"
                    ))
                })?;
                if let Some(reason) = &entry.unsupported {
                    return Err(CausalReplayError::Unsupported(format!(
                        "selected source {source:?}: {reason}"
                    )));
                }
                pending.extend(entry.dependencies.iter().cloned());
            }
            SourceRef::InputRow { command, .. } => {
                let entry = causal.input_commands.get(command).ok_or_else(|| {
                    CausalReplayError::Invalid(format!(
                        "selected input source {source:?} has no catalog entry"
                    ))
                })?;
                if let Some(reason) = &entry.unsupported {
                    return Err(CausalReplayError::Unsupported(format!(
                        "selected input source {source:?}: {reason}"
                    )));
                }
            }
        }
    }
    Ok(selected)
}

fn selected_input_rows(
    egraph: &EGraph,
    causal: &CausalState,
    sources: &HashSet<SourceRef>,
) -> Result<Vec<ReplaySource>, CausalReplayError> {
    let mut selected = BTreeMap::<u64, BTreeSet<u64>>::new();
    for source in sources {
        if let SourceRef::InputRow { command, line } = source {
            selected.entry(*command).or_default().insert(*line);
        }
    }
    let mut rows = Vec::new();
    for (command, lines) in selected {
        let entry = causal.input_commands.get(&command).ok_or_else(|| {
            CausalReplayError::Invalid(format!("input command {command} is absent from catalog"))
        })?;
        let function_type = egraph
            .type_info
            .get_func_type(&entry.function)
            .ok_or_else(|| {
                CausalReplayError::Invalid(format!(
                    "input function `{}` is absent from type information",
                    entry.function
                ))
            })?;
        if function_type.subtype == FunctionSubtype::Custom {
            return Err(CausalReplayError::Unsupported(format!(
                "selected input into value function `{}`",
                entry.function
            )));
        }
        let bytes = std::fs::read(&entry.resolved_path).map_err(|error| {
            CausalReplayError::Input(format!(
                "cannot reread `{}`: {error}",
                entry.resolved_path.display()
            ))
        })?;
        let digest: [u8; 32] = Sha256::digest(&bytes).into();
        if digest != entry.digest {
            return Err(CausalReplayError::Input(format!(
                "input `{}` changed after receipt capture",
                entry.resolved_path.display()
            )));
        }
        let contents = String::from_utf8(bytes).map_err(|error| {
            CausalReplayError::Input(format!(
                "input `{}` is no longer UTF-8: {error}",
                entry.resolved_path.display()
            ))
        })?;
        let schema = EGraph::input_row_schema(function_type);
        let mut remaining = lines.clone();
        for (index, text) in contents.lines().enumerate() {
            let line = u64::try_from(index + 1)
                .map_err(|_| CausalReplayError::Input("input has too many lines".into()))?;
            if !lines.contains(&line) {
                continue;
            }
            let parsed = EGraph::parse_input_line(&schema, &entry.file, line, text)
                .map_err(|error| CausalReplayError::Input(error.to_string()))?
                .ok_or_else(|| {
                    CausalReplayError::Invalid(format!(
                        "selected input row {}:{} parsed as empty",
                        entry.file, line
                    ))
                })?;
            remaining.remove(&line);
            rows.push(ReplaySource {
                catalog_ordinal: entry.command,
                source: OwnedSourceRef::InputRow { command, line },
                kind: ReplaySourceKind::InputRow {
                    function: entry.function.clone(),
                    line,
                    literals: parsed.literals.into_boxed_slice(),
                },
            });
        }
        if let Some(line) = remaining.first() {
            return Err(CausalReplayError::Invalid(format!(
                "selected input row {}:{line} no longer exists",
                entry.file
            )));
        }
    }
    Ok(rows)
}

fn canonical_symbol(name: &str) -> &str {
    name.strip_prefix(crate::GLOBAL_NAME_PREFIX).unwrap_or(name)
}

fn validate_alias_namespace(
    egraph: &EGraph,
    causal: &CausalState,
    max_aliases: usize,
) -> Result<(), CausalReplayError> {
    let mut occupied = StdHashSet::new();
    occupied.extend(
        causal
            .immutable_globals
            .keys()
            .map(|name| canonical_symbol(name).to_owned()),
    );
    for entry in &causal.rule_catalog {
        occupied.extend(
            entry
                .variables
                .iter()
                .map(|(name, _)| canonical_symbol(name).to_owned()),
        );
    }
    for index in 0..max_aliases {
        let canonical = format!("__causal_replay_{index}");
        if occupied.contains(&canonical) || egraph.names.contains_canonical(&canonical) {
            return Err(CausalReplayError::Invalid(format!(
                "generated checked alias `${canonical}` collides with a user symbol"
            )));
        }
    }
    Ok(())
}

fn build_owned(
    egraph: &EGraph,
    causal: &CausalState,
    view: &mut CausalReceiptView<'_>,
    slice: &CausalSlice,
) -> Result<CausalReplayIr, CausalReplayError> {
    causal
        .validate_replay_rule_names()
        .map_err(CausalReplayError::Invalid)?;

    let sources = selected_source_closure(causal, &slice.sources)?;
    let mut retained_rules = BTreeSet::new();
    let mut matches = Vec::with_capacity(slice.matches.len());
    let mut match_ids = slice.matches.iter().copied().collect::<Vec<_>>();
    match_ids.sort_unstable();
    for id in match_ids {
        let matched = view
            .matched(id)
            .map_err(|error| CausalReplayError::Receipt(error.to_string()))?;
        retained_rules.insert(matched.rule);
        matches.push((id, matched.rule, matched.wave.get(), matched.position.get()));
    }

    let mut setup = Vec::new();
    for (ordinal, entry) in causal.command_catalog.iter().enumerate() {
        if is_static_declaration(&entry.command) {
            setup.push(ReplaySetup {
                catalog_ordinal: ordinal,
                kind: ReplaySetupKind::Command(entry.command.clone()),
            });
        }
    }
    let mut source_events = Vec::new();
    for source in &sources {
        let SourceRef::Synthetic(_) = source else {
            continue;
        };
        let entry = &causal.source_commands[source];
        let command = causal
            .command_catalog
            .get(entry.command)
            .ok_or_else(|| {
                CausalReplayError::Invalid(format!(
                    "source {source:?} cites missing command {}",
                    entry.command
                ))
            })?
            .command
            .clone();
        if !matches!(command, Command::Action(_)) {
            return Err(CausalReplayError::Invalid(format!(
                "source {source:?} does not map to an action command"
            )));
        }
        source_events.push(ReplaySource {
            catalog_ordinal: entry.command,
            source: source.into(),
            kind: ReplaySourceKind::Command(command),
        });
    }
    source_events.extend(selected_input_rows(egraph, causal, &sources)?);
    for rule in &retained_rules {
        let entry = causal.rule_catalog.get(*rule as usize).ok_or_else(|| {
            CausalReplayError::Invalid(format!("selected rule ordinal {rule} is absent"))
        })?;
        let command = causal
            .command_catalog
            .get(entry.command)
            .ok_or_else(|| {
                CausalReplayError::Invalid(format!(
                    "rule ordinal {rule} cites missing command {}",
                    entry.command
                ))
            })?
            .command
            .clone();
        let Command::Rule { rule: command_rule } = &command else {
            return Err(CausalReplayError::Invalid(format!(
                "rule ordinal {rule} does not map to a rule command"
            )));
        };
        if command_rule.name != entry.replay_name || command_rule.ruleset != entry.ruleset {
            return Err(CausalReplayError::Invalid(format!(
                "rule ordinal {rule} catalog identity disagrees with its emitted command"
            )));
        }
        setup.push(ReplaySetup {
            catalog_ordinal: entry.command,
            kind: ReplaySetupKind::Command(command),
        });
    }
    setup.sort_by_key(|entry| entry.catalog_ordinal);

    let mut terms = OwnedTermBuilder::new(view, causal)?;
    let mut waves = BTreeMap::<u64, (u64, Vec<ReplayFiring>)>::new();
    let mut aliases_by_wave = BTreeMap::<u64, Vec<ReplayAlias>>::new();
    let mut next_alias = 0usize;
    for (id, rule, wave, position) in matches {
        let catalog = &causal.rule_catalog[rule as usize];
        let binding_terms = slice.match_terms.get(&id).ok_or_else(|| {
            CausalReplayError::Invalid(format!(
                "selected match {} has no projected bindings",
                id.get()
            ))
        })?;
        if binding_terms.len() != catalog.variables.len() {
            return Err(CausalReplayError::Invalid(format!(
                "selected match {} has {} terms for {} rule variables",
                id.get(),
                binding_terms.len(),
                catalog.variables.len()
            )));
        }
        let mut bindings = Vec::with_capacity(binding_terms.len());
        for ((variable, expected_sort), source_term) in
            catalog.variables.iter().zip(binding_terms.iter().copied())
        {
            let term = terms.intern(source_term)?;
            let actual_sort = terms.nodes[term.index()].sort();
            if actual_sort != expected_sort {
                return Err(CausalReplayError::Invalid(format!(
                    "match {} variable `{variable}` expects `{expected_sort}` but term owns `{actual_sort}`",
                    id.get()
                )));
            }
            bindings.push(ReplayBinding {
                variable: variable.clone(),
                sort: expected_sort.clone(),
                term,
            });
        }
        for term in terms.take_new_calls() {
            aliases_by_wave.entry(wave).or_default().push(ReplayAlias {
                name: format!("$__causal_replay_{next_alias}"),
                term,
            });
            next_alias += 1;
        }
        let wave_entry = waves.entry(wave).or_insert((position, Vec::new()));
        wave_entry.0 = wave_entry.0.min(position);
        wave_entry.1.push(ReplayFiring {
            receipt_match: id.get(),
            rule_ordinal: rule,
            replay_name: catalog.replay_name.clone(),
            bindings: bindings.into_boxed_slice(),
        });
    }
    validate_alias_namespace(egraph, causal, next_alias)?;
    let term_nodes = std::mem::take(&mut terms.nodes);
    drop(terms);

    let mut events = source_events
        .into_iter()
        .map(ReplayEvent::Source)
        .collect::<Vec<_>>();
    for (wave, (position, mut firings)) in waves {
        firings.sort_unstable_by_key(|firing| firing.receipt_match);
        events.push(ReplayEvent::Wave(ReplayWave {
            wave,
            position,
            aliases: aliases_by_wave
                .remove(&wave)
                .unwrap_or_default()
                .into_boxed_slice(),
            firings: firings.into_boxed_slice(),
        }));
    }
    let mut checks = slice.checks.iter().copied().collect::<Vec<_>>();
    checks.sort_unstable();
    for check in checks {
        let position = slice.check_positions.get(&check).ok_or_else(|| {
            CausalReplayError::Invalid(format!("selected check {check} has no history position"))
        })?;
        let root = view
            .check_root(check)
            .map_err(|error| CausalReplayError::Receipt(error.to_string()))?;
        let command_index = causal.check_commands.get(&check).ok_or_else(|| {
            CausalReplayError::Invalid(format!("selected check {check} has no catalog command"))
        })?;
        let command = causal
            .command_catalog
            .get(*command_index)
            .ok_or_else(|| {
                CausalReplayError::Invalid(format!(
                    "selected check {check} cites missing command {command_index}"
                ))
            })?
            .command
            .clone();
        if !matches!(command, Command::Check(..)) {
            return Err(CausalReplayError::Invalid(format!(
                "selected check {check} maps to a non-check command"
            )));
        }
        events.push(ReplayEvent::Check(ReplayCheck {
            check,
            after_wave: root.wave.get(),
            catalog_ordinal: *command_index,
            position: position.get(),
            command,
        }));
    }
    events.sort_by_key(ReplayEvent::chronology_key);

    let stats = ReplayIrStats {
        setup_commands: setup
            .iter()
            .filter(|entry| matches!(entry.kind, ReplaySetupKind::Command(_)))
            .count() as u64,
        logical_sources: slice.sources.len() as u64,
        closed_sources: sources.len() as u64,
        source_events: events
            .iter()
            .filter(|event| matches!(event, ReplayEvent::Source(_)))
            .count() as u64,
        input_rows: events
            .iter()
            .filter(|event| {
                matches!(
                    event,
                    ReplayEvent::Source(ReplaySource {
                        kind: ReplaySourceKind::InputRow { .. },
                        ..
                    })
                )
            })
            .count() as u64,
        terms: term_nodes.len() as u64,
        aliases: next_alias as u64,
        firings: events
            .iter()
            .map(|event| match event {
                ReplayEvent::Wave(wave) => wave.firings.len() as u64,
                ReplayEvent::Source(_) | ReplayEvent::Check(_) => 0,
            })
            .sum(),
        waves: events
            .iter()
            .filter(|event| matches!(event, ReplayEvent::Wave(_)))
            .count() as u64,
        checks: events
            .iter()
            .filter(|event| matches!(event, ReplayEvent::Check(_)))
            .count() as u64,
    };
    Ok(CausalReplayIr {
        setup,
        terms: ReplayTermArena { nodes: term_nodes },
        events,
        stats,
    })
}

pub(crate) fn build_causal_replay_ir(
    egraph: &EGraph,
    slice: &CausalSlice,
) -> Result<CausalReplayIr, CausalReplayError> {
    let causal = egraph
        .causal_state
        .as_ref()
        .ok_or(CausalReplayError::Disabled)?;
    causal
        .ensure_healthy()
        .map_err(|error| CausalReplayError::Invalid(error.to_string()))?;
    let bridge = egraph
        .backend
        .as_any()
        .downcast_ref::<egglog_bridge::EGraph>()
        .ok_or(CausalReplayError::UnsupportedBackend)?;
    bridge
        .with_causal_receipt_view(|view| Ok(build_owned(egraph, causal, view, slice)))
        .map_err(|error| CausalReplayError::Receipt(error.to_string()))?
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::PathBuf;
    use std::sync::OnceLock;
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::*;
    use crate::causal_slice::slice_all_checks;

    fn serial_pool() -> &'static rayon::ThreadPool {
        static SERIAL_POOL: OnceLock<rayon::ThreadPool> = OnceLock::new();
        SERIAL_POOL.get_or_init(|| {
            rayon::ThreadPoolBuilder::new()
                .num_threads(1)
                .build()
                .unwrap()
        })
    }

    fn temp_fact_dir() -> PathBuf {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "egglog-causal-replay-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&path).unwrap();
        path
    }

    #[test]
    fn owned_ir_keeps_complete_bindings_and_check_chronology() {
        let mut egraph = EGraph::default();
        serial_pool()
            .install(|| egraph.enable_causal_receipts())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(datatype E (A i64))
                 (relation Seed (E))
                 (relation Out (E))
                 (Seed (A 1))
                 (rule ((Seed x)) ((Out x)) :name \"step\")
                 (run 1)
                 (check (Out (A 1)))",
            )
            .unwrap();
        let bridge = egraph
            .backend
            .as_any()
            .downcast_ref::<egglog_bridge::EGraph>()
            .unwrap();
        let compatibility_reads = bridge.causal_compatibility_projection_reads().unwrap();
        let slice = slice_all_checks(&egraph).unwrap();
        let ir = build_causal_replay_ir(&egraph, &slice).unwrap();
        assert_eq!(
            compatibility_reads,
            bridge.causal_compatibility_projection_reads().unwrap(),
            "owned IR construction must not materialize a full receipt snapshot"
        );
        assert_eq!(ir.stats.firings, 1);
        assert_eq!(ir.stats.waves, 1);
        assert_eq!(ir.stats.checks, 1);
        let wave = ir
            .events
            .iter()
            .find_map(|event| match event {
                ReplayEvent::Wave(wave) => Some(wave),
                ReplayEvent::Source(_) | ReplayEvent::Check(_) => None,
            })
            .unwrap();
        let wave_index = ir
            .events
            .iter()
            .position(|event| matches!(event, ReplayEvent::Wave(_)))
            .unwrap();
        let check_index = ir
            .events
            .iter()
            .position(|event| matches!(event, ReplayEvent::Check(_)))
            .unwrap();
        assert!(wave_index < check_index);
        assert_eq!(wave.firings[0].replay_name, "step");
        assert_eq!(wave.firings[0].bindings.len(), 1);
        assert!(
            wave.aliases
                .iter()
                .all(|alias| alias.name.starts_with("$__causal_replay_"))
        );
    }

    #[test]
    fn owned_ir_preserves_pre_run_check_and_source_order() {
        let mut egraph = EGraph::default();
        serial_pool()
            .install(|| egraph.enable_causal_receipts())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(relation R (i64))
                 (R 1)
                 (check (R 1))
                 (R 2)
                 (check (R 2))",
            )
            .unwrap();
        let slice = slice_all_checks(&egraph).unwrap();
        let ir = build_causal_replay_ir(&egraph, &slice).unwrap();
        assert_eq!(ir.stats.source_events, 2);
        assert_eq!(ir.stats.checks, 2);
        assert!(matches!(ir.events[0], ReplayEvent::Source(_)));
        assert!(matches!(ir.events[1], ReplayEvent::Check(_)));
        assert!(matches!(ir.events[2], ReplayEvent::Source(_)));
        assert!(matches!(ir.events[3], ReplayEvent::Check(_)));
    }

    #[test]
    fn owned_ir_rereads_only_selected_input_rows_and_checks_digest() {
        static NEXT_RELATIVE: AtomicU64 = AtomicU64::new(0);
        let relative_dir = PathBuf::from("target").join(format!(
            "egglog-causal-replay-relative-{}-{}",
            std::process::id(),
            NEXT_RELATIVE.fetch_add(1, Ordering::Relaxed)
        ));
        let dir = std::env::current_dir().unwrap().join(&relative_dir);
        fs::create_dir_all(&dir).unwrap();
        let file = relative_dir.join("rows.tsv");
        fs::write(&file, "drop\nkeep\n").unwrap();

        let mut egraph = EGraph::default();
        egraph.fact_directory = Some(relative_dir);
        serial_pool()
            .install(|| egraph.enable_causal_receipts())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(relation R (String))
                 (input R \"rows.tsv\")
                 (check (R \"keep\"))",
            )
            .unwrap();
        assert!(
            egraph
                .causal_state
                .as_ref()
                .unwrap()
                .input_commands
                .values()
                .all(|entry| entry.resolved_path.is_absolute()),
            "capture must freeze the effective input path independently of later cwd changes"
        );
        let slice = slice_all_checks(&egraph).unwrap();
        let ir = build_causal_replay_ir(&egraph, &slice).unwrap();
        assert_eq!(ir.stats.input_rows, 1);
        let selected = ir.events.iter().find_map(|event| match event {
            ReplayEvent::Source(ReplaySource {
                kind: ReplaySourceKind::InputRow { line, literals, .. },
                ..
            }) => Some((*line, literals.as_ref())),
            _ => None,
        });
        assert_eq!(selected, Some((2, &[Literal::String("keep".into())][..])));

        fs::write(&file, "changed-but-unselected\nkeep\n").unwrap();
        let error = build_causal_replay_ir(&egraph, &slice).unwrap_err();
        assert!(
            matches!(error, CausalReplayError::Input(message) if message.contains("changed after receipt capture"))
        );
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn owned_ir_rejects_checked_alias_collisions_with_any_declaration() {
        let mut egraph = EGraph::default();
        serial_pool()
            .install(|| egraph.enable_causal_receipts())
            .unwrap();
        egraph
            .parse_and_run_program(
                None,
                "(function $__causal_replay_0 (i64) i64 :no-merge)
                 (datatype E (A i64))
                 (relation Seed (E))
                 (relation Out (E))
                 (Seed (A 1))
                 (rule ((Seed x)) ((Out x)) :name \"step\")
                 (run 1)
                 (check (Out (A 1)))",
            )
            .unwrap();
        let slice = slice_all_checks(&egraph).unwrap();
        let error = build_causal_replay_ir(&egraph, &slice).unwrap_err();
        assert!(
            matches!(error, CausalReplayError::Invalid(message) if message.contains("collides with a user symbol"))
        );
    }

    #[test]
    fn unsupported_input_fails_only_when_selected() {
        let dir = temp_fact_dir();
        fs::write(dir.join("value.tsv"), "1\t2\n").unwrap();

        let mut selected = EGraph::default();
        selected.fact_directory = Some(dir.clone());
        serial_pool()
            .install(|| selected.enable_causal_receipts())
            .unwrap();
        selected
            .parse_and_run_program(
                None,
                "(function f (i64) i64 :no-merge)
                 (relation Out (i64))
                 (input f \"value.tsv\")
                 (rule ((= value (f 1))) ((Out value)) :name \"read-f\")
                 (run 1)
                 (check (Out 2))",
            )
            .unwrap();
        let slice = slice_all_checks(&selected).unwrap();
        let error = build_causal_replay_ir(&selected, &slice).unwrap_err();
        assert!(
            matches!(error, CausalReplayError::Unsupported(message) if message.contains("value function `f`"))
        );

        let mut unreachable = EGraph::default();
        unreachable.fact_directory = Some(dir.clone());
        serial_pool()
            .install(|| unreachable.enable_causal_receipts())
            .unwrap();
        unreachable
            .parse_and_run_program(
                None,
                "(function f (i64) i64 :no-merge)
                 (relation R (Unit))
                 (input f \"value.tsv\")
                 (R ())
                 (check (R ()))",
            )
            .unwrap();
        let slice = slice_all_checks(&unreachable).unwrap();
        build_causal_replay_ir(&unreachable, &slice).unwrap();
        fs::remove_dir_all(dir).unwrap();
    }
}
