//! Graph-neutral replay-program construction for a selected slice.
//!
//! Output owns no backend ids, runtime values, trace handles, or borrows from
//! the recording graph. A fresh graph may execute it under ordinary proof mode.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::ast::{Action, Command, Expr, FunctionSubtype, RunRuleConfig, RustSpan, Schedule, Span};
use crate::core_relations::{
    ReplayLiteral, ReplayOpId, ReplaySortId, ReplayTerm, ReplayTermId, SourceRef, TraceView,
};
use crate::slicing::backward::Slice;
use crate::util::{HashMap, HashSet};
use crate::{
    CaptureCatalog, CatalogRuleSurface, EGraph, Literal, ReplayOpKey, RewriteDirection,
    RuleBindingRole, RuleCatalogEntry,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ReplayTermRef(u32);

impl ReplayTermRef {
    fn from_index(index: usize) -> Result<Self, ReplayError> {
        Ok(Self(index.try_into().map_err(|_| {
            ReplayError::Invalid("owned replay term arena exceeds u32".into())
        })?))
    }

    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct OwnedReplayOp {
    pub(crate) name: String,
    pub(crate) inputs: Box<[String]>,
    pub(crate) output: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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
    Command(Box<Command>),
    InputRow {
        function: String,
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
    pub(crate) firing_id: u64,
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
    pub(crate) after_wave: u64,
    pub(crate) catalog_ordinal: usize,
    pub(crate) command: Command,
}

#[derive(Clone, Debug)]
pub(crate) enum ReplayEvent {
    Source(ReplaySource),
    Wave(ReplayWave),
    Check(Box<ReplayCheck>),
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
pub(crate) struct ReplayProgram {
    pub(crate) setup: Vec<ReplaySetup>,
    pub(crate) terms: ReplayTermArena,
    pub(crate) events: Vec<ReplayEvent>,
    pub(crate) stats: ReplayIrStats,
}

impl ReplayProgram {
    /// Lower the graph-neutral slice into the ordinary command surface used by
    /// the fresh proof graph. Runtime values from the recording graph never
    /// cross this boundary: constructor values are re-established by
    /// `let-check`, and literals remain source literals.
    pub(crate) fn to_commands(&self) -> Result<Vec<Command>, ReplayError> {
        let mut commands = Vec::new();
        let mut setup = self.setup.iter().peekable();

        let mut aliases = HashMap::<ReplayTermRef, String>::default();
        for event in &self.events {
            let setup_bound = match event {
                ReplayEvent::Source(source) => Some(source.catalog_ordinal),
                ReplayEvent::Check(check) if check.after_wave == 0 => Some(check.catalog_ordinal),
                ReplayEvent::Wave(_) | ReplayEvent::Check(_) => None,
            };
            while setup
                .peek()
                .is_some_and(|entry| setup_bound.is_none_or(|bound| entry.catalog_ordinal <= bound))
            {
                let entry = setup.next().expect("peeked replay setup disappeared");
                match &entry.kind {
                    ReplaySetupKind::Command(command) => commands.push(command.clone()),
                }
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
                            expr: Expr::Call(span, op.name.clone(), args),
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
        commands.extend(setup.map(|entry| match &entry.kind {
            ReplaySetupKind::Command(command) => command.clone(),
        }));
        Ok(hygienic_source_commands(commands))
    }

    pub(crate) fn render_commands(commands: &[Command]) -> Result<String, ReplayError> {
        use std::fmt::Write as _;

        let mut rendered = String::new();
        for command in commands {
            writeln!(&mut rendered, "{command}").map_err(|error| {
                ReplayError::Invalid(format!("cannot render slice replay command: {error}"))
            })?;
        }
        Ok(rendered)
    }

    fn term(&self, term: ReplayTermRef) -> Result<&OwnedReplayTerm, ReplayError> {
        self.terms.nodes.get(term.index()).ok_or_else(|| {
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

/// Alpha-renames parser-reserved internal symbols across the complete retained
/// program. This is deliberately cold: capture keeps exact native names, then
/// one occupied-name-aware map makes declarations, rule references, grounded
/// binding keys, and expected sorts agree without conflating user symbols.
fn hygienic_source_commands(commands: Vec<Command>) -> Vec<Command> {
    let mut observed = Vec::new();
    for command in &commands {
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
        let mut strings = Vec::new();
        let _ = command.map_string_symbols(&mut |symbol: String| {
            strings.push(symbol.clone());
            symbol
        });
        observed.extend(strings);
    }

    let mut occupied = HashSet::default();
    let mut internal = Vec::new();
    let mut seen_internal = HashSet::default();
    for symbol in observed {
        if symbol.starts_with(crate::util::INTERNAL_SYMBOL_PREFIX) {
            if seen_internal.insert(symbol.clone()) {
                internal.push(symbol);
            }
        } else {
            occupied.insert(symbol);
        }
    }

    let mut renames = HashMap::default();
    for (slot, original) in internal.into_iter().enumerate() {
        let mut suffix = 0usize;
        let replacement = loop {
            let candidate = format!("__slice_replay_internal_{slot}_{suffix}");
            if occupied.insert(candidate.clone()) {
                break candidate;
            }
            suffix += 1;
        };
        renames.insert(original, replacement);
    }

    commands
        .into_iter()
        .map(|command| {
            let mut rename_head = |head: String| renames.get(&head).cloned().unwrap_or(head);
            let mut rename_leaf = |leaf: String| renames.get(&leaf).cloned().unwrap_or(leaf);
            command
                .map_symbols(&mut rename_head, &mut rename_leaf)
                .map_string_symbols(&mut |symbol: String| {
                    renames.get(&symbol).cloned().unwrap_or(symbol)
                })
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
pub(crate) enum ReplayError {
    #[error("slice replay is unavailable without exact trace capture")]
    Disabled,
    #[error("slice replay requires the main native backend")]
    UnsupportedBackend,
    #[error("slice replay trace error: {0}")]
    Trace(String),
    #[error("slice replay input error: {0}")]
    Input(String),
    #[error("invalid slice replay: {0}")]
    Invalid(String),
    #[error("unsupported slice replay: {0}")]
    Unsupported(String),
}

struct OwnedTermBuilder<'a, 'view> {
    view: &'a mut TraceView<'view>,
    sorts: HashMap<ReplaySortId, String>,
    ops: HashMap<ReplayOpId, OwnedReplayOp>,
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
        let node = self
            .view
            .replay_term(source)
            .map_err(|error| ReplayError::Trace(error.to_string()))?;
        if matches!(node, ReplayTerm::Literal { .. })
            && let Some(term) = self.literal_memo.get(&source)
        {
            self.visiting.remove(&source);
            return Ok(*term);
        }
        let owned = match node {
            ReplayTerm::Literal { sort, literal } => OwnedReplayTerm::Literal {
                sort: self.sort_name(sort)?.to_owned(),
                literal: replay_literal(literal)?,
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
                    op,
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

fn replay_literal(literal: ReplayLiteral) -> Result<Literal, ReplayError> {
    Ok(match literal {
        ReplayLiteral::Unit => Literal::Unit,
        ReplayLiteral::Bool(value) => Literal::Bool(value),
        ReplayLiteral::I64(value) => Literal::Int(value),
        ReplayLiteral::F64(bits) => {
            Literal::Float(ordered_float::OrderedFloat(f64::from_bits(bits)))
        }
        ReplayLiteral::String(value) => Literal::String(value.to_string()),
        ReplayLiteral::Internal(value) => {
            return Err(ReplayError::Unsupported(format!(
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

fn selected_input_rows(
    egraph: &EGraph,
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
    for (command, lines) in selected {
        let entry = catalog.input_commands.get(&command).ok_or_else(|| {
            ReplayError::Invalid(format!("input command {command} is absent from catalog"))
        })?;
        let function_type = egraph
            .type_info
            .get_func_type(&entry.function)
            .ok_or_else(|| {
                ReplayError::Invalid(format!(
                    "input function `{}` is absent from type information",
                    entry.function
                ))
            })?;
        if function_type.subtype == FunctionSubtype::Custom {
            return Err(ReplayError::Unsupported(format!(
                "selected input into value function `{}`",
                entry.function
            )));
        }
        let bytes = std::fs::read(&entry.resolved_path).map_err(|error| {
            ReplayError::Input(format!(
                "cannot reread `{}`: {error}",
                entry.resolved_path.display()
            ))
        })?;
        let digest: [u8; 32] = Sha256::digest(&bytes).into();
        if digest != entry.digest {
            return Err(ReplayError::Input(format!(
                "input `{}` changed after trace capture",
                entry.resolved_path.display()
            )));
        }
        let contents = String::from_utf8(bytes).map_err(|error| {
            ReplayError::Input(format!(
                "input `{}` is no longer UTF-8: {error}",
                entry.resolved_path.display()
            ))
        })?;
        let schema = EGraph::input_row_schema(function_type);
        let mut remaining = lines.clone();
        for (index, text) in contents.lines().enumerate() {
            let line = u64::try_from(index + 1)
                .map_err(|_| ReplayError::Input("input has too many lines".into()))?;
            if !lines.contains(&line) {
                continue;
            }
            let parsed = EGraph::parse_input_line(&schema, &entry.file, line, text)
                .map_err(|error| ReplayError::Input(error.to_string()))?
                .ok_or_else(|| {
                    ReplayError::Invalid(format!(
                        "selected input row {}:{} parsed as empty",
                        entry.file, line
                    ))
                })?;
            remaining.remove(&line);
            rows.push(ReplaySource {
                catalog_ordinal: catalog.command_catalog[entry.command].surface_command,
                source: OwnedSourceRef::InputRow { command, line },
                kind: ReplaySourceKind::InputRow {
                    function: entry.function.clone(),
                    literals: parsed.literals.into_boxed_slice(),
                },
            });
        }
        if let Some(line) = remaining.first() {
            return Err(ReplayError::Invalid(format!(
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
            match (forward, reverse) {
                (Some(_), Some(_)) => {
                    rewrite.name = base_name;
                    Ok(Command::BiRewrite(surface_ruleset, rewrite))
                }
                (Some(entry), None) => {
                    rewrite.name.clone_from(&entry.replay_name);
                    Ok(Command::Rewrite(surface_ruleset, rewrite, false))
                }
                (None, Some(entry)) => {
                    std::mem::swap(&mut rewrite.lhs, &mut rewrite.rhs);
                    rewrite.name.clone_from(&entry.replay_name);
                    Ok(Command::Rewrite(surface_ruleset, rewrite, false))
                }
                (None, None) => unreachable!("rewrite direction presence was checked above"),
            }
        }
        Command::Rewrite(..) | Command::BiRewrite(..) => Err(ReplayError::Invalid(format!(
            "rewrite surface command {surface_command} disagrees with its directionality"
        ))),
        _ => Err(ReplayError::Invalid(format!(
            "retained rewrite surface command {surface_command} is not a rewrite"
        ))),
    }
}

fn validate_alias_namespace(
    egraph: &EGraph,
    catalog: &CaptureCatalog,
    max_aliases: usize,
) -> Result<(), ReplayError> {
    let mut occupied = HashSet::default();
    occupied.extend(
        catalog
            .immutable_globals
            .keys()
            .map(|name| canonical_symbol(name).to_owned()),
    );
    for entry in &catalog.rule_catalog {
        occupied.extend(
            entry
                .variables
                .iter()
                .map(|variable| canonical_symbol(&variable.name).to_owned()),
        );
    }
    for index in 0..max_aliases {
        let canonical = format!("__slice_replay_{index}");
        if occupied.contains(&canonical) || egraph.names.contains_canonical(&canonical) {
            return Err(ReplayError::Invalid(format!(
                "generated checked alias `${canonical}` collides with a user symbol"
            )));
        }
    }
    Ok(())
}

fn build_owned(
    egraph: &EGraph,
    catalog: &CaptureCatalog,
    view: &mut TraceView<'_>,
    slice: &Slice,
) -> Result<ReplayProgram, ReplayError> {
    catalog
        .validate_replay_rule_names()
        .map_err(ReplayError::Invalid)?;

    let sources = selected_source_closure(catalog, &slice.sources)?;
    let mut retained_rules = BTreeSet::new();
    let mut firings = Vec::with_capacity(slice.firings.len());
    let mut firing_ids = slice.firings.iter().copied().collect::<Vec<_>>();
    firing_ids.sort_unstable();
    for id in firing_ids {
        let firing = view
            .firing(id)
            .map_err(|error| ReplayError::Trace(error.to_string()))?;
        retained_rules.insert(firing.rule);
        firings.push((id, firing.rule, firing.wave.get(), firing.position.get()));
    }

    let mut setup = Vec::new();
    for (ordinal, command) in catalog.surface_command_catalog.iter().enumerate() {
        if command.as_ref().is_some_and(is_static_declaration) {
            setup.push(ReplaySetup {
                catalog_ordinal: ordinal,
                kind: ReplaySetupKind::Command(
                    command
                        .clone()
                        .expect("static surface command disappeared from replay catalog"),
                ),
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
        if !matches!(command, Command::Action(_)) {
            return Err(ReplayError::Invalid(format!(
                "source {source:?} does not map to an action command"
            )));
        }
        source_events
            .entry(surface_command)
            .or_insert(ReplaySource {
                catalog_ordinal: surface_command,
                source: source.into(),
                kind: ReplaySourceKind::Command(Box::new(command)),
            });
    }
    let mut source_events = source_events.into_values().collect::<Vec<_>>();
    source_events.extend(selected_input_rows(egraph, catalog, &sources)?);
    let mut rewrite_groups = BTreeMap::<usize, Vec<u32>>::new();
    for rule in &retained_rules {
        let entry = catalog.rule_catalog.get(*rule as usize).ok_or_else(|| {
            ReplayError::Invalid(format!("selected rule ordinal {rule} is absent"))
        })?;
        match entry.surface {
            CatalogRuleSurface::Normalized => {
                setup.push(ReplaySetup {
                    catalog_ordinal: catalog.command_catalog[entry.command].surface_command,
                    kind: ReplaySetupKind::Command(normalized_rule_command(
                        catalog, &sources, *rule, entry,
                    )?),
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
            kind: ReplaySetupKind::Command(retained_rewrite_command(
                catalog,
                &sources,
                surface_command,
                &rules,
            )?),
        });
    }
    setup.sort_by_key(|entry| entry.catalog_ordinal);

    // A checked alias remains a valid name for later monotone unions/rekeys,
    // but not across removal/recreation: identical syntax can then denote a
    // fresh native occurrence. Use a conservative global removal epoch so
    // unrelated deletions may inhibit deduplication but can never merge two
    // occurrence lifetimes.
    let mut alias_reset_positions = slice
        .replay_removals
        .iter()
        .chain(&slice.interference_removals)
        .copied()
        .map(|index| {
            view.removal(index)
                .map(|removal| removal.position.get())
                .map_err(|error| ReplayError::Trace(error.to_string()))
        })
        .collect::<Result<Vec<_>, _>>()?;
    alias_reset_positions.sort_unstable();
    alias_reset_positions.dedup();

    let mut terms = OwnedTermBuilder::new(view, catalog)?;
    let mut waves = BTreeMap::<u64, (u64, Vec<ReplayFiring>)>::new();
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
    let mut wave_positions = BTreeMap::<u64, u64>::new();
    for (_, _, wave, position) in &firings {
        wave_positions
            .entry(*wave)
            .and_modify(|current| *current = (*current).min(*position))
            .or_insert(*position);
    }
    let mut next_alias = 0usize;
    for (id, rule, wave, position) in firings {
        let rule_entry = &catalog.rule_catalog[rule as usize];
        let binding_terms = slice.firing_terms.get(&id).ok_or_else(|| {
            ReplayError::Invalid(format!(
                "selected firing {} has no projected bindings",
                id.get()
            ))
        })?;
        if binding_terms.len() != rule_entry.variables.len() {
            return Err(ReplayError::Invalid(format!(
                "selected firing {} has {} terms for {} rule variables",
                id.get(),
                binding_terms.len(),
                rule_entry.variables.len()
            )));
        }
        let binding_windows = slice.firing_term_windows.get(&id).ok_or_else(|| {
            ReplayError::Invalid(format!(
                "selected firing {} has no checked-alias availability plan",
                id.get()
            ))
        })?;
        if binding_windows.len() != binding_terms.len() {
            return Err(ReplayError::Invalid(format!(
                "selected firing {} has {} alias windows for {} bindings",
                id.get(),
                binding_windows.len(),
                binding_terms.len()
            )));
        }
        let mut bindings = Vec::with_capacity(binding_terms.len());
        for ((variable, source_term), alias_windows) in rule_entry
            .variables
            .iter()
            .zip(binding_terms.iter().copied())
            .zip(binding_windows.iter())
        {
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
            let term = terms.intern(source_term)?;
            let actual_sort = terms.nodes[term.index()].sort();
            if actual_sort != expected_sort {
                return Err(ReplayError::Invalid(format!(
                    "firing {} variable `{variable_name}` expects `{expected_sort}` but term owns `{actual_sort}`",
                    id.get()
                )));
            }
            let new_calls = terms.take_new_calls();
            if new_calls.len() != alias_windows.len() {
                return Err(ReplayError::Invalid(format!(
                    "firing {} binding `{variable_name}` owns {} structural call occurrences but has {} availability windows",
                    id.get(),
                    new_calls.len(),
                    alias_windows.len()
                )));
            }
            for ((source_call, call), window) in new_calls.into_iter().zip(alias_windows.iter()) {
                if source_call != window.term {
                    return Err(ReplayError::Invalid(format!(
                        "firing {} binding `{variable_name}` availability order expected call {} but projected call {}",
                        id.get(),
                        source_call.get(),
                        window.term.get()
                    )));
                }
                let window = *window;
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
                let alias_wave = wave_positions
                    .iter()
                    .find_map(|(candidate_wave, candidate_position)| {
                        (*candidate_wave >= dependency_wave
                            && *candidate_wave <= wave
                            && *candidate_position >= window.available_after.get())
                        .then_some(*candidate_wave)
                    })
                    .ok_or_else(|| {
                        ReplayError::Invalid(format!(
                            "firing {} binding `{variable_name}` call {} has no retained pre-wave point in its availability window",
                            id.get(),
                            source_call.get()
                        ))
                    })?;
                let fresh_after = window.fresh_after.map(|position| position.get());
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
                let alias_position = *wave_positions
                    .get(&alias_wave)
                    .expect("selected alias wave has no history position");
                let alias_epoch =
                    alias_reset_positions.partition_point(|position| *position <= alias_position);
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
                        name: format!("$__slice_replay_{next_alias}"),
                        term: call,
                    });
                alias_wave_by_term.insert(call, alias_wave);
                alias_ordinal_by_term.insert(call, next_alias);
                next_alias += 1;
            }
            bindings.push(ReplayBinding {
                variable: variable_name.clone(),
                sort: expected_sort.clone(),
                term: canonical_term.get(&term).copied().unwrap_or(term),
            });
        }
        let wave_entry = waves.entry(wave).or_insert((position, Vec::new()));
        wave_entry.0 = wave_entry.0.min(position);
        wave_entry.1.push(ReplayFiring {
            firing_id: id.get(),
            rule_ordinal: rule,
            replay_name: rule_entry.replay_name.clone(),
            bindings: bindings.into_boxed_slice(),
        });
    }
    validate_alias_namespace(egraph, catalog, next_alias)?;
    let term_nodes = std::mem::take(&mut terms.nodes);
    drop(terms);
    for aliases in aliases_by_wave.values_mut() {
        aliases.sort_unstable_by_key(|alias| alias_ordinal_by_term[&alias.term]);
    }

    let mut events = source_events
        .into_iter()
        .map(ReplayEvent::Source)
        .collect::<Vec<_>>();
    for (wave, (position, mut firings)) in waves {
        firings.sort_unstable_by_key(|firing| firing.firing_id);
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
        if !slice.check_positions.contains_key(&check) {
            return Err(ReplayError::Invalid(format!(
                "selected check {check} has no history position"
            )));
        }
        let root = view
            .check_root(check)
            .map_err(|error| ReplayError::Trace(error.to_string()))?;
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
    Ok(ReplayProgram {
        setup,
        terms: ReplayTermArena { nodes: term_nodes },
        events,
        stats,
    })
}

pub(crate) fn build_replay_program(
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
    bridge
        .with_trace_view(|view| Ok(build_owned(egraph, catalog, view, slice)))
        .map_err(|error| ReplayError::Trace(error.to_string()))?
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::PathBuf;
    use std::sync::OnceLock;
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::*;
    use crate::slicing::backward::slice_all_checks;

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

    fn slice_commands(program: &str) -> (Vec<Command>, String) {
        let mut recorder = EGraph::default();
        serial_pool().install(|| recorder.enable_trace()).unwrap();
        recorder.parse_and_run_program(None, program).unwrap();
        let slice = slice_all_checks(&recorder).unwrap();
        let ir = build_replay_program(&recorder, &slice).unwrap();
        let commands = ir.to_commands().unwrap();
        let rendered = ReplayProgram::render_commands(&commands).unwrap();

        let mut proof = EGraph::default().with_proofs_enabled().with_proof_testing();
        serial_pool()
            .install(|| proof.parse_and_run_program(None, &rendered))
            .unwrap();
        (commands, rendered)
    }

    fn endpoint_normalization_program(order: [&str; 3]) -> String {
        let constructors = order
            .into_iter()
            .map(|name| format!("({name})"))
            .collect::<Vec<_>>()
            .join("\n");
        format!(
            "(datatype E (A) (B) (C))\n{constructors}\n(union (A) (B))\n(union (B) (C))\n(check (= (A) (C)))"
        )
    }

    #[test]
    fn applied_equality_distinguishes_proposal_from_native_edge() {
        let mut recorder = EGraph::default();
        serial_pool().install(|| recorder.enable_trace()).unwrap();
        recorder
            .parse_and_run_program(None, &endpoint_normalization_program(["A", "B", "C"]))
            .unwrap();

        recorder
            .with_trace_view(|view| {
                let first = view
                    .project_applied_equality(crate::core_relations::AppliedEqualityId::new(1))?;
                let second = view
                    .project_applied_equality(crate::core_relations::AppliedEqualityId::new(2))?;

                // The second source action spells its left endpoint as B, but
                // native execution has already canonicalized B to A. Its
                // recorded proposal and applied forest edge therefore carry
                // observably different identities.
                assert_eq!(second.left.term, first.right.term);
                assert_ne!(second.left.raw, first.right.raw);
                assert_eq!(second.left.raw, first.left.raw);
                assert_eq!(second.native_parent, first.native_parent);
                assert_eq!(second.native_parent, second.left.raw);
                assert_eq!(second.native_child, second.right.raw);
                let support = view.explain_equality_denotation_before(
                    crate::core_relations::AppliedEqualityId::new(2),
                )?;
                assert_eq!(
                    support.applied.as_ref(),
                    [crate::core_relations::AppliedEqualityId::new(1)]
                );
                assert!(
                    !support
                        .applied
                        .contains(&crate::core_relations::AppliedEqualityId::new(2))
                );
                Ok(())
            })
            .unwrap();
    }

    #[test]
    fn slice_replays_precanonicalized_union_endpoints_in_any_allocation_order() {
        for order in [
            ["A", "B", "C"],
            ["A", "C", "B"],
            ["B", "A", "C"],
            ["B", "C", "A"],
            ["C", "A", "B"],
            ["C", "B", "A"],
        ] {
            let mut recorder = EGraph::default();
            serial_pool().install(|| recorder.enable_trace()).unwrap();
            recorder
                .parse_and_run_program(None, &endpoint_normalization_program(order))
                .unwrap();
            let slice = slice_all_checks(&recorder).unwrap();
            let ir = build_replay_program(&recorder, &slice).unwrap();
            let rendered = ReplayProgram::render_commands(&ir.to_commands().unwrap()).unwrap();

            for (mode, mut replay) in [
                ("native", EGraph::default()),
                ("term", EGraph::default().with_term_encoding_enabled()),
            ] {
                replay
                    .parse_and_run_program(None, &rendered)
                    .unwrap_or_else(|error| {
                        panic!(
                            "{mode} replay failed for constructor order {order:?}: {error}\n{rendered}"
                        )
                    });
            }
        }
    }

    #[test]
    fn endpoint_denotation_does_not_retain_an_unrelated_prefix() {
        let mut recorder = EGraph::default();
        serial_pool().install(|| recorder.enable_trace()).unwrap();
        recorder
            .parse_and_run_program(
                None,
                "(datatype E (A) (B) (C) (NoiseL) (NoiseR))
                 (NoiseL) (NoiseR) (A) (B) (C)
                 (union (NoiseL) (NoiseR))
                 (union (A) (B))
                 (union (B) (C))
                 (check (= (A) (C)))",
            )
            .unwrap();
        let slice = slice_all_checks(&recorder).unwrap();
        let noise = crate::core_relations::AppliedEqualityId::new(1);
        assert!(!slice.equalities.contains(&noise));
        assert!(!slice.replay_equalities.contains(&noise));
        let ir = build_replay_program(&recorder, &slice).unwrap();
        let rendered = ReplayProgram::render_commands(&ir.to_commands().unwrap()).unwrap();
        for mut replay in [
            EGraph::default(),
            EGraph::default().with_term_encoding_enabled(),
        ] {
            replay.parse_and_run_program(None, &rendered).unwrap();
        }
    }

    #[test]
    fn rule_union_retains_precanonicalized_endpoint_denotation() {
        let mut recorder = EGraph::default();
        serial_pool().install(|| recorder.enable_trace()).unwrap();
        recorder
            .parse_and_run_program(
                None,
                "(datatype E (A) (B) (C))
                 (relation Trigger ())
                 (A) (B) (C)
                 (union (A) (B))
                 (Trigger)
                 (rule ((Trigger)) ((union (B) (C))) :name \"bridge\")
                 (run 1)
                 (check (= (A) (C)))",
            )
            .unwrap();
        let slice = slice_all_checks(&recorder).unwrap();
        assert!(
            slice
                .equalities
                .contains(&crate::core_relations::AppliedEqualityId::new(1)),
            "the rule union reads B through the earlier A=B denotation"
        );
        let ir = build_replay_program(&recorder, &slice).unwrap();
        let rendered = ReplayProgram::render_commands(&ir.to_commands().unwrap()).unwrap();
        for mut replay in [
            EGraph::default(),
            EGraph::default().with_term_encoding_enabled(),
        ] {
            replay.parse_and_run_program(None, &rendered).unwrap();
        }
    }

    #[test]
    fn carrier_container_denotation_retains_its_historical_anchor() {
        let program = "(sort E)
                       (constructor A () E)
                       (constructor Alias () E)
                       (constructor C () E)
                       (sort Es (Vec E))
                       (constructor Wrap (Es) E)
                       (relation Eq ())
                       (relation Finish ())
                       (ruleset equate)
                       (ruleset finish)
                       (A)
                       (Wrap (vec-of (A)))
                       (C)
                       (Eq)
                       (Finish)
                       (rule ((Eq)) ((union (A) (Alias)))
                         :ruleset equate :name \"equate\")
                       (rule ((Finish)) ((union (Wrap (vec-of (Alias))) (C)))
                         :ruleset finish :name \"finish\")
                       (run equate 1)
                       (run finish 1)
                       (check (= (Wrap (vec-of (A))) (C)))";
        let mut recorder = EGraph::default();
        serial_pool().install(|| recorder.enable_trace()).unwrap();
        serial_pool()
            .install(|| recorder.parse_and_run_program(None, program))
            .unwrap();
        recorder
            .with_trace_view(|view| {
                let mut rule_unions = Vec::new();
                for raw_id in 1..=view.totals().applied_equalities {
                    let id = crate::core_relations::AppliedEqualityId::new(raw_id);
                    let event = view.project_applied_equality(id)?;
                    if matches!(
                        event.reason,
                        crate::core_relations::EqualityReason::RuleUnion(_)
                    ) {
                        rule_unions.push(event);
                    }
                }
                assert_eq!(rule_unions.len(), 2, "expected equate and finish unions");
                let equate = &rule_unions[0];
                let finish = &rule_unions[1];
                let equate_terms = [equate.left.term, equate.right.term];
                let mut source_anchor = None;
                for raw_fact in 1..=view.totals().facts {
                    let fact = crate::core_relations::FactId::new(raw_fact);
                    let record = view.fact(fact)?;
                    let crate::core_relations::CauseRef::Cause(cause) = record.cause else {
                        continue;
                    };
                    if !matches!(
                        view.cause(cause)?,
                        crate::core_relations::RawCause::Source(_)
                    ) {
                        continue;
                    }
                    let schema = view.table_schema(record.table)?;
                    let Some(constructor) = schema.constructor else {
                        continue;
                    };
                    let terms = view.fact_terms(fact)?;
                    let output = constructor.child_sorts.len();
                    if terms
                        .get(output)
                        .is_some_and(|term| equate_terms.contains(term))
                    {
                        assert!(source_anchor.replace(fact).is_none());
                    }
                }
                let source_anchor = source_anchor.expect("missing source A producer");

                let support = view.explain_equality_denotation_before(finish.id)?;
                assert!(
                    support.facts.contains(&source_anchor),
                    "container denotation lost source anchor {source_anchor:?}: got {:?}",
                    support.facts
                );
                assert!(support.applied.contains(&equate.id));
                assert!(!support.applied.contains(&finish.id));
                Ok(())
            })
            .unwrap();
    }

    #[derive(Clone, Copy, Debug)]
    enum EndpointCarrier {
        SourceUnion,
        RuleUnion,
        SourceSet,
        RuleSet,
        DeleteRecreate,
    }

    #[derive(Clone, Copy, Debug)]
    struct EndpointCase {
        carrier: EndpointCarrier,
        order: [&'static str; 5],
        noise: bool,
        compact: bool,
    }

    fn next_endpoint_random(state: &mut u64) -> u64 {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        *state
    }

    fn shuffled_endpoint_order(state: &mut u64) -> [&'static str; 5] {
        let mut order = ["A", "B", "C", "NoiseL", "NoiseR"];
        for index in (1..order.len()).rev() {
            let other = (next_endpoint_random(state) as usize) % (index + 1);
            order.swap(index, other);
        }
        order
    }

    fn endpoint_case_program(case: EndpointCase) -> String {
        let mut lines = vec!["(datatype E (A) (B) (C) (F E) (NoiseL) (NoiseR))".to_owned()];
        match case.carrier {
            EndpointCarrier::SourceUnion => {}
            EndpointCarrier::RuleUnion => {
                lines.push("(relation Trigger ())".into());
                lines.push("(ruleset bridge)".into());
            }
            EndpointCarrier::SourceSet => {
                lines.push("(function f (E) i64 :no-merge)".into());
                lines.push("(relation Out (i64))".into());
                lines.push("(ruleset read)".into());
            }
            EndpointCarrier::RuleSet => {
                lines.push("(function f (E) i64 :no-merge)".into());
                lines.push("(relation Trigger ())".into());
                lines.push("(relation Out (i64))".into());
                lines.push("(ruleset write)".into());
                lines.push("(ruleset read)".into());
            }
            EndpointCarrier::DeleteRecreate => {
                lines.push("(relation Delete ())".into());
                lines.push("(relation Recreate ())".into());
                lines.push("(relation Before (E))".into());
                lines.push("(relation After (E))".into());
                lines.push("(relation Final ())".into());
                lines.push("(ruleset cleanup)".into());
                lines.push("(ruleset recreate)".into());
                lines.push("(ruleset reconcile)".into());
                lines.push("(ruleset finish)".into());
            }
        }

        let needs_c = matches!(
            case.carrier,
            EndpointCarrier::SourceUnion
                | EndpointCarrier::RuleUnion
                | EndpointCarrier::DeleteRecreate
        );
        for name in case.order {
            if matches!(name, "NoiseL" | "NoiseR") && !case.noise {
                continue;
            }
            if name == "C" && case.compact && !needs_c {
                continue;
            }
            lines.push(format!("({name})"));
        }
        if case.noise {
            lines.push("(union (NoiseL) (NoiseR))".into());
        }
        lines.push("(union (A) (B))".into());

        match case.carrier {
            EndpointCarrier::SourceUnion => {
                lines.push("(union (B) (C))".into());
                lines.push("(check (= (A) (C)))".into());
            }
            EndpointCarrier::RuleUnion => {
                lines.push("(Trigger)".into());
                lines.push(
                    "(rule ((Trigger)) ((union (B) (C))) :ruleset bridge :name \"bridge\")".into(),
                );
                lines.push("(run bridge 1)".into());
                lines.push("(check (= (A) (C)))".into());
            }
            EndpointCarrier::SourceSet => {
                lines.push("(set (f (B)) 7)".into());
                lines.push(
                    "(rule ((= value (f (A)))) ((Out value)) :ruleset read :name \"read\")".into(),
                );
                lines.push("(run read 1)".into());
                lines.push("(check (Out 7))".into());
            }
            EndpointCarrier::RuleSet => {
                lines.push("(Trigger)".into());
                lines.push(
                    "(rule ((Trigger)) ((set (f (B)) 7)) :ruleset write :name \"write\")".into(),
                );
                lines.push("(run write 1)".into());
                lines.push(
                    "(rule ((= value (f (A)))) ((Out value)) :ruleset read :name \"read\")".into(),
                );
                lines.push("(run read 1)".into());
                lines.push("(check (Out 7))".into());
            }
            EndpointCarrier::DeleteRecreate => {
                lines.push("(Before (F (B)))".into());
                lines.push("(Delete)".into());
                lines.push("(Recreate)".into());
                lines.push("(Final)".into());
                lines.push(
                    "(rule ((Delete)) ((delete (F (B)))) :ruleset cleanup :name \"delete-f\")"
                        .into(),
                );
                lines.push(
                    "(rule ((Recreate)) ((After (F (B)))) :ruleset recreate :name \"recreate-f\")"
                        .into(),
                );
                lines.push(
                    "(rule ((Before old) (After new)) ((union old new)) :ruleset reconcile :name \"reconcile\")"
                        .into(),
                );
                lines.push(
                    "(rule ((Final)) ((union (B) (C))) :ruleset finish :name \"finish\")".into(),
                );
                lines.push("(run cleanup 1)".into());
                lines.push("(run recreate 1)".into());
                lines.push("(run reconcile 1)".into());
                lines.push("(run finish 1)".into());
                lines.push("(check (= (A) (C)) (Before x) (After x))".into());
            }
        }
        lines.join("\n")
    }

    fn run_endpoint_case(case: EndpointCase) -> Result<(), String> {
        let program = endpoint_case_program(case);
        let mut recorder = EGraph::default();
        serial_pool()
            .install(|| recorder.enable_trace())
            .map_err(|error| format!("enable trace: {error}"))?;
        serial_pool()
            .install(|| recorder.parse_and_run_program(None, &program))
            .map_err(|error| format!("capture: {error}"))?;
        let slice = slice_all_checks(&recorder).map_err(|error| format!("slice: {error}"))?;
        let anchor = crate::core_relations::AppliedEqualityId::new(u64::from(case.noise) + 1);
        if !slice.equalities.contains(&anchor) || !slice.replay_equalities.contains(&anchor) {
            return Err(format!("missing denotation anchor {anchor:?}"));
        }
        if case.noise {
            let noise = crate::core_relations::AppliedEqualityId::new(1);
            if slice.equalities.contains(&noise) || slice.replay_equalities.contains(&noise) {
                return Err("disconnected noise equality was retained".into());
            }
        }
        if matches!(case.carrier, EndpointCarrier::DeleteRecreate)
            && slice.replay_removals.is_empty()
        {
            return Err("delete/recreate case lost its selected removal".into());
        }
        let replay = build_replay_program(&recorder, &slice)
            .map_err(|error| format!("build replay: {error}"))?;
        let rendered = ReplayProgram::render_commands(
            &replay
                .to_commands()
                .map_err(|error| format!("build commands: {error}"))?,
        )
        .map_err(|error| format!("render: {error}"))?;
        for (mode, mut graph) in [
            ("native", EGraph::default()),
            ("term", EGraph::default().with_term_encoding_enabled()),
        ] {
            graph
                .parse_and_run_program(None, &rendered)
                .map_err(|error| format!("{mode} replay: {error}\n{rendered}"))?;
        }
        Ok(())
    }

    fn retain_failing_endpoint_candidate(
        case: &mut EndpointCase,
        error: &mut String,
        probes: &mut usize,
        candidate: EndpointCase,
    ) {
        if *probes == 128 {
            return;
        }
        *probes += 1;
        if let Err(candidate_error) = run_endpoint_case(candidate) {
            *case = candidate;
            *error = candidate_error;
        }
    }

    fn shrink_endpoint_failure(
        mut case: EndpointCase,
        mut error: String,
    ) -> (EndpointCase, String) {
        let mut probes = 0usize;

        if case.noise {
            let candidate = EndpointCase {
                noise: false,
                ..case
            };
            retain_failing_endpoint_candidate(&mut case, &mut error, &mut probes, candidate);
        }
        if !case.compact {
            let candidate = EndpointCase {
                compact: true,
                ..case
            };
            retain_failing_endpoint_candidate(&mut case, &mut error, &mut probes, candidate);
        }
        let canonical = ["A", "B", "C", "NoiseL", "NoiseR"];
        for (target, canonical_name) in canonical.iter().enumerate() {
            let Some(current) = case.order.iter().position(|name| name == canonical_name) else {
                continue;
            };
            if current == target {
                continue;
            }
            let mut candidate = case;
            candidate.order.swap(target, current);
            retain_failing_endpoint_candidate(&mut case, &mut error, &mut probes, candidate);
        }
        (case, error)
    }

    #[test]
    fn endpoint_denotation_is_complete_across_carriers_and_allocation_orders() {
        let carriers = [
            EndpointCarrier::SourceUnion,
            EndpointCarrier::RuleUnion,
            EndpointCarrier::SourceSet,
            EndpointCarrier::RuleSet,
            EndpointCarrier::DeleteRecreate,
        ];
        let mut random = 0x6a09_e667_f3bc_c909;
        for index in 0..32 {
            let case = EndpointCase {
                carrier: carriers[index % carriers.len()],
                order: shuffled_endpoint_order(&mut random),
                noise: true,
                compact: false,
            };
            if let Err(error) = run_endpoint_case(case) {
                let (minimal, error) = shrink_endpoint_failure(case, error);
                panic!(
                    "endpoint denotation property failed for {minimal:?}: {error}\nminimal program:\n{}",
                    endpoint_case_program(minimal)
                );
            }
        }
    }

    #[test]
    fn owned_ir_preserves_pre_run_check_and_source_order() {
        let mut egraph = EGraph::default();
        serial_pool().install(|| egraph.enable_trace()).unwrap();
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
        let ir = build_replay_program(&egraph, &slice).unwrap();
        assert!(matches!(
            ir.events.as_slice(),
            [
                ReplayEvent::Source(_),
                ReplayEvent::Check(_),
                ReplayEvent::Source(_),
                ReplayEvent::Check(_),
            ]
        ));
    }

    #[test]
    fn rendered_artifact_round_trips_globals_and_grounded_rules_with_proofs() {
        let mut recorder = EGraph::default();
        serial_pool().install(|| recorder.enable_trace()).unwrap();
        recorder
            .parse_and_run_program(
                None,
                "(datatype E (A i64) (B E) (C E))
                 (relation Seed (E))
                 (Seed (A 1))
                 (let $dead (A 2))
                 (let $seed (A 1))
                 (rule ((Seed x))
                       ((union (B $seed) (C x)))
                       :name \"emit\")
                 (run 1)
                 (check (= (B $seed) (C (A 1))))",
            )
            .unwrap();
        let slice = slice_all_checks(&recorder).unwrap();
        let ir = build_replay_program(&recorder, &slice).unwrap();
        let commands = ir.to_commands().unwrap();
        assert!(commands.iter().any(|command| {
            matches!(command, Command::Action(Action::Let(_, name, _)) if name == "$seed")
        }));
        assert!(!commands.iter().any(|command| {
            matches!(command, Command::Action(Action::Let(_, name, _)) if name == "$dead")
        }));
        assert!(!commands.iter().any(|command| {
            matches!(
                command,
                Command::Function {
                    let_binding: true,
                    ..
                } | Command::Constructor {
                    let_binding: true,
                    ..
                }
            )
        }));
        let rendered = ReplayProgram::render_commands(&commands).unwrap();
        assert!(rendered.contains("(datatype E"));
        assert!(rendered.contains("(relation Seed"));
        assert!(rendered.contains("(let $seed (A 1))"));
        assert!(!rendered.contains(":internal-let"));
        assert!(rendered.contains("(let-check $__slice_replay_0 (A 1) :sort E)"));
        assert!(
            !rendered.contains('@'),
            "rendered replay leaked a parser-reserved internal symbol:\n{rendered}"
        );
        let global = rendered.find("(let $seed").unwrap();
        let rule = rendered.find(":name \"emit\"").unwrap();
        assert!(
            global < rule,
            "retained globals must precede dependent rules"
        );

        let mut direct_proof = EGraph::default().with_proofs_enabled().with_proof_testing();
        serial_pool()
            .install(|| direct_proof.run_program(commands))
            .unwrap();

        let mut proof = EGraph::default().with_proofs_enabled().with_proof_testing();
        serial_pool()
            .install(|| proof.parse_and_run_program(None, &rendered))
            .unwrap();
    }

    #[test]
    fn rendered_artifact_preserves_anonymous_rewrite_and_selected_global() {
        let (commands, rendered) = slice_commands(
            "(datatype E (A i64) (B i64))
             (let $left (A 1))
             (let $target (B 1))
             (rewrite (A x) $target)
             (run 1)
             (check (= $left $target))",
        );
        let rewrites = commands
            .iter()
            .filter_map(|command| match command {
                Command::Rewrite(_, rewrite, _) => Some(rewrite),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(rewrites.len(), 1, "unexpected artifact:\n{rendered}");
        assert!(rewrites[0].name.starts_with("__slice_replay_rule_s"));
        assert!(
            !commands
                .iter()
                .any(|command| matches!(command, Command::Rule { .. })),
            "surface rewrite was lowered back to a rule:\n{rendered}"
        );
        assert!(rendered.contains("(__rewrite_root "));
        assert!(!rendered.contains(crate::util::INTERNAL_SYMBOL_PREFIX));
    }

    #[test]
    fn rendered_artifact_preserves_birewrite_when_both_directions_are_retained() {
        let (commands, rendered) = slice_commands(
            "(datatype E (A i64) (B i64))
             (let $a (A 1))
             (let $b (B 2))
             (birewrite (A x) (B x))
             (run 1)
             (check (= $a (B 1)))
             (check (= (A 2) $b))",
        );
        let birewrites = commands
            .iter()
            .filter_map(|command| match command {
                Command::BiRewrite(_, rewrite) => Some(rewrite),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(birewrites.len(), 1, "unexpected artifact:\n{rendered}");
        assert!(birewrites[0].name.starts_with("__slice_replay_rule_s"));
        assert!(
            !commands
                .iter()
                .any(|command| matches!(command, Command::Rewrite(..) | Command::Rule { .. }))
        );
    }

    #[test]
    fn rendered_artifact_orients_single_retained_birewrite_direction() {
        let (commands, rendered) = slice_commands(
            "(datatype E (A i64) (B i64))
             (let $a (A 1))
             (birewrite (A x) (B x))
             (run 1)
             (check (= $a (B 1)))",
        );
        assert!(
            commands.iter().any(|command| matches!(
                command,
                Command::Rewrite(_, rewrite, false) if rewrite.name.ends_with("=>")
            )),
            "single selected direction was not emitted as an oriented rewrite:\n{rendered}"
        );
        assert!(
            !commands
                .iter()
                .any(|command| matches!(command, Command::BiRewrite(..)))
        );

        let (commands, rendered) = slice_commands(
            "(datatype E (A i64) (B i64))
             (let $b (B 2))
             (birewrite (A x) (B x))
             (run 1)
             (check (= (A 2) $b))",
        );
        assert!(
            commands.iter().any(|command| matches!(
                command,
                Command::Rewrite(_, rewrite, false)
                    if rewrite.name.ends_with("<=")
                        && rewrite.lhs.to_string() == "(B x)"
                        && rewrite.rhs.to_string() == "(A x)"
            )),
            "reverse selected direction was not swapped into an oriented rewrite:\n{rendered}"
        );
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

        let mut egraph = EGraph {
            fact_directory: Some(relative_dir),
            ..EGraph::default()
        };
        serial_pool().install(|| egraph.enable_trace()).unwrap();
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
                .capture_catalog
                .as_ref()
                .unwrap()
                .input_commands
                .values()
                .all(|entry| entry.resolved_path.is_absolute()),
            "capture must freeze the effective input path independently of later cwd changes"
        );
        let slice = slice_all_checks(&egraph).unwrap();
        let ir = build_replay_program(&egraph, &slice).unwrap();
        assert_eq!(ir.stats.input_rows, 1);
        let selected = ir.events.iter().find_map(|event| match event {
            ReplayEvent::Source(ReplaySource {
                source: OwnedSourceRef::InputRow { line, .. },
                kind: ReplaySourceKind::InputRow { literals, .. },
                ..
            }) => Some((*line, literals.as_ref())),
            _ => None,
        });
        assert_eq!(selected, Some((2, &[Literal::String("keep".into())][..])));

        fs::write(&file, "changed-but-unselected\nkeep\n").unwrap();
        let error = build_replay_program(&egraph, &slice).unwrap_err();
        assert!(
            matches!(error, ReplayError::Input(message) if message.contains("changed after trace capture"))
        );
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn unsupported_input_fails_only_when_selected() {
        let dir = temp_fact_dir();
        fs::write(dir.join("value.tsv"), "1\t2\n").unwrap();

        let mut selected = EGraph {
            fact_directory: Some(dir.clone()),
            ..EGraph::default()
        };
        serial_pool().install(|| selected.enable_trace()).unwrap();
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
        let error = build_replay_program(&selected, &slice).unwrap_err();
        assert!(
            matches!(error, ReplayError::Unsupported(message) if message.contains("value function `f`"))
        );

        let mut unreachable = EGraph {
            fact_directory: Some(dir.clone()),
            ..EGraph::default()
        };
        serial_pool()
            .install(|| unreachable.enable_trace())
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
        build_replay_program(&unreachable, &slice).unwrap();
        fs::remove_dir_all(dir).unwrap();
    }
}
