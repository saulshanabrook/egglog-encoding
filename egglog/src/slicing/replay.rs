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
    FactId, ReplayLiteral, ReplayOpId, ReplaySortId, ReplayTerm, ReplayTermId, SourceRef, TraceView,
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
pub(crate) enum OwnedReplayTerm {
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

#[derive(Clone, Debug)]
pub(crate) struct ReplaySetup {
    pub(crate) catalog_ordinal: usize,
    pub(crate) command: Command,
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
    pub(crate) term: ReplayTermRef,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReplayFiring {
    pub(crate) replay_name: String,
    pub(crate) bindings: Box<[ReplayBinding]>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReplayWave {
    pub(crate) wave: u64,
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

#[derive(Clone, Debug)]
pub(crate) struct ReplayProgram {
    pub(crate) setup: Vec<ReplaySetup>,
    pub(crate) terms: Vec<OwnedReplayTerm>,
    pub(crate) events: Vec<ReplayEvent>,
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

fn replay_literal(literal: ReplayLiteral) -> Result<Literal, ReplayError> {
    Ok(match literal {
        ReplayLiteral::Unit => Literal::Unit,
        ReplayLiteral::Bool(value) => Literal::Bool(value),
        ReplayLiteral::I64(value) => Literal::Int(value),
        ReplayLiteral::F64(bits) => {
            Literal::Float(ordered_float::OrderedFloat(f64::from_bits(bits)))
        }
        ReplayLiteral::String(value) => Literal::String(value.to_string()),
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
            debug_assert!(forward.is_some() || reverse.is_some());
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
        let removal = view
            .removal(index)
            .map_err(|error| ReplayError::Trace(error.to_string()))?;
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
    for (id, rule, wave, _) in firings {
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
            for ((source_call, call), plan) in new_calls.into_iter().zip(alias_windows.iter()) {
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
                let alias_wave = wave_positions
                    .iter()
                    .find_map(|(candidate_wave, candidate_position)| {
                        (*candidate_wave >= dependency_wave
                            && *candidate_wave <= wave
                            && *candidate_position >= history_ready_after
                            && live_before.is_none_or(|end| *candidate_position < end))
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
                term: canonical_term.get(&term).copied().unwrap_or(term),
            });
        }
        waves.entry(wave).or_default().push(ReplayFiring {
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
    for (wave, firings) in waves {
        events.push(ReplayEvent::Wave(ReplayWave {
            wave,
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

    Ok(ReplayProgram {
        setup,
        terms: term_nodes,
        events,
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
#[path = "replay_tests.rs"]
mod tests;
