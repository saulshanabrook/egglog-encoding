//! Exact producer-stamped command provenance through frontend desugaring.
//!
//! Desugaring records only a local disposition for each output node.  The
//! authoritative incoming origin is composed afterward, so no command name,
//! schema, span, or rendered form participates in provenance.

use std::fmt::Display;
use std::hash::Hash;

use thiserror::Error;

use crate::ast::{GenericCommand, GenericNCommand};
use crate::frontend_program::{CommandOrigin, GeneratedCommandRole};
use crate::schedule_origin::{ExactScheduleOrigins, ScheduleCommandNode, ScheduleOriginError};
use crate::typechecking::{FinalizedProgram, SortAuthorityAt};
use crate::util::{HashMap, HashSet};
use crate::{NCommand, ResolvedNCommand};

/// The only command shape provenance is allowed to inspect.
///
/// Both frontend command forests expose `Fail` nesting through this private
/// trait.  Producers never recover identity from names, schemas, spans, or
/// display text.
pub(crate) trait OriginCommandNode: Sized {
    fn fail_children(&self) -> Option<&[Self]>;
}

impl<Head, Leaf> OriginCommandNode for GenericNCommand<Head, Leaf>
where
    Head: Clone + Display,
    Leaf: Clone + PartialEq + Eq + Display + Hash,
{
    fn fail_children(&self) -> Option<&[Self]> {
        let GenericNCommand::Fail(_, children) = self else {
            return None;
        };
        Some(children)
    }
}

impl<Head, Leaf> OriginCommandNode for GenericCommand<Head, Leaf>
where
    Head: Clone + Display,
    Leaf: Clone + PartialEq + Eq + Display + Hash,
{
    fn fail_children(&self) -> Option<&[Self]> {
        let GenericCommand::Fail(_, children) = self else {
            return None;
        };
        Some(children)
    }
}

/// How one desugared command node relates to the producer's input command.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum CommandOriginDisposition {
    /// Preserve the complete incoming origin, including an existing generated
    /// role.
    Inherit,
    /// Retain only the incoming trigger and stamp this producer's role.
    Generated(GeneratedCommandRole),
}

/// One producer-local disposition at an exact recursive command path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CommandOriginDispositionAt {
    pub(crate) command_path: Vec<usize>,
    pub(crate) disposition: CommandOriginDisposition,
}

/// One authoritative origin at an exact recursive command path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CommandOriginAt {
    pub(crate) command_path: Vec<usize>,
    pub(crate) origin: CommandOrigin,
}

/// A total, deterministic recursive origin sidecar for one command forest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ExactCommandOrigins(Vec<CommandOriginAt>);

impl ExactCommandOrigins {
    pub(crate) fn try_new<C: OriginCommandNode>(
        commands: &[C],
        origins: Vec<CommandOriginAt>,
    ) -> Result<Self, CommandOriginError> {
        validate_paths(commands, &origins, |origin| &origin.command_path)?;
        validate_origins(&origins)?;
        Ok(Self(origins))
    }

    /// Stamp one producer-assigned origin across a freshly parsed command
    /// forest. Recursive paths remain exact even though every nested `Fail`
    /// command belongs to the same parsed subcommand.
    pub(crate) fn uniform<C: OriginCommandNode>(
        commands: &[C],
        origin: CommandOrigin,
    ) -> Result<Self, CommandOriginError> {
        let mut paths = Vec::new();
        collect_paths(commands, &mut Vec::new(), &mut paths);
        Self::try_new(
            commands,
            paths
                .into_iter()
                .map(|command_path| CommandOriginAt {
                    command_path,
                    origin: origin.clone(),
                })
                .collect(),
        )
    }

    /// Entries are in deterministic recursive command preorder.
    #[allow(dead_code)] // consumed by the pending compile-only mapper
    pub(crate) fn as_slice(&self) -> &[CommandOriginAt] {
        &self.0
    }
}

/// A command forest that cannot be detached from its exact producer origins.
///
/// Fields are deliberately private.  Transitions can inspect both components,
/// but no API returns a bare command vector.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OriginatedProgram<C> {
    commands: Vec<C>,
    origins: ExactCommandOrigins,
    schedule_origins: ExactScheduleOrigins,
}

impl<C: OriginCommandNode + ScheduleCommandNode> OriginatedProgram<C> {
    pub(crate) fn try_new(
        commands: Vec<C>,
        origins: ExactCommandOrigins,
        schedule_origins: ExactScheduleOrigins,
    ) -> Result<Self, CommandOriginError> {
        origins.validate(&commands)?;
        schedule_origins.validate(&commands, &origins)?;
        Ok(Self {
            commands,
            origins,
            schedule_origins,
        })
    }

    pub(crate) fn validate(&self) -> Result<(), CommandOriginError> {
        self.origins.validate(&self.commands).and_then(|()| {
            self.schedule_origins
                .validate(&self.commands, &self.origins)
                .map_err(CommandOriginError::from)
        })
    }

    pub(crate) fn commands(&self) -> &[C] {
        &self.commands
    }

    pub(crate) fn origins(&self) -> &ExactCommandOrigins {
        &self.origins
    }

    #[allow(dead_code)] // consumed by the pending standalone snapshot mapper
    pub(crate) fn schedule_origins(&self) -> &ExactScheduleOrigins {
        &self.schedule_origins
    }
}

/// A finalized command forest that cannot be detached from its exact producer
/// origins or its nominal sort authorities.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OriginatedFinalizedProgram {
    finalized: FinalizedProgram,
    origins: ExactCommandOrigins,
    schedule_origins: ExactScheduleOrigins,
}

impl OriginatedFinalizedProgram {
    pub(crate) fn try_new(
        finalized: FinalizedProgram,
        origins: ExactCommandOrigins,
        schedule_origins: ExactScheduleOrigins,
    ) -> Result<Self, CommandOriginError> {
        validate_sort_authorities(&finalized)?;
        origins.validate(&finalized.commands)?;
        schedule_origins.validate(&finalized.commands, &origins)?;
        Ok(Self {
            finalized,
            origins,
            schedule_origins,
        })
    }

    pub(crate) fn validate(&self) -> Result<(), CommandOriginError> {
        validate_sort_authorities(&self.finalized)?;
        self.origins.validate(&self.finalized.commands)?;
        self.schedule_origins
            .validate(&self.finalized.commands, &self.origins)?;
        Ok(())
    }

    pub(crate) fn commands(&self) -> &[ResolvedNCommand] {
        &self.finalized.commands
    }

    #[allow(dead_code)] // consumed by the pending standalone snapshot mapper
    pub(crate) fn sort_authorities(&self) -> &[SortAuthorityAt] {
        &self.finalized.sort_authorities
    }

    pub(crate) fn origins(&self) -> &ExactCommandOrigins {
        &self.origins
    }

    #[allow(dead_code)] // consumed by the pending standalone snapshot mapper
    pub(crate) fn schedule_origins(&self) -> &ExactScheduleOrigins {
        &self.schedule_origins
    }

    /// Apply one provenance-preserving transition.  The callback must return
    /// both authority carriers, and the result is revalidated before it can
    /// become another originated value.
    pub(crate) fn try_transform<E>(
        self,
        transform: impl FnOnce(
            FinalizedProgram,
            ExactCommandOrigins,
            ExactScheduleOrigins,
        ) -> Result<
            (FinalizedProgram, ExactCommandOrigins, ExactScheduleOrigins),
            E,
        >,
    ) -> Result<Self, E>
    where
        E: From<CommandOriginError>,
    {
        self.validate().map_err(E::from)?;
        let (finalized, origins, schedule_origins) =
            transform(self.finalized, self.origins, self.schedule_origins)?;
        Self::try_new(finalized, origins, schedule_origins).map_err(E::from)
    }

    /// Atomically append another originated forest.  One pre-append top-level
    /// offset rebases both exact-origin paths and sort-authority paths.
    #[allow(dead_code)] // used by the pending compile-only grouped transition
    pub(crate) fn appended(self, other: Self) -> Result<Self, CommandOriginError> {
        self.validate()?;
        other.validate()?;

        let offset = self.finalized.commands.len();
        let mut candidate_commands = self.finalized.commands;
        candidate_commands.extend(other.finalized.commands);

        let mut candidate_sort_authorities = self.finalized.sort_authorities;
        candidate_sort_authorities.extend(other.finalized.sort_authorities.into_iter().map(
            |mut authority| {
                let top = authority
                    .command_path
                    .first_mut()
                    .expect("validated sort-authority paths are never empty");
                *top += offset;
                authority
            },
        ));
        let candidate_finalized = FinalizedProgram {
            commands: candidate_commands,
            sort_authorities: candidate_sort_authorities,
        };

        let mut candidate_origin_entries = self.origins.0;
        candidate_origin_entries.extend(other.origins.0.into_iter().map(|mut entry| {
            let top = entry
                .command_path
                .first_mut()
                .expect("validated command-origin paths are never empty");
            *top += offset;
            entry
        }));
        let candidate_origins =
            ExactCommandOrigins::try_new(&candidate_finalized.commands, candidate_origin_entries)?;

        let mut candidate_schedule_entries = self.schedule_origins.into_entries();
        candidate_schedule_entries.extend(other.schedule_origins.into_entries().into_iter().map(
            |mut entry| {
                let top = entry
                    .address
                    .command_path
                    .first_mut()
                    .expect("validated schedule command paths are never empty");
                *top += offset;
                entry
            },
        ));
        let candidate_schedule_origins = ExactScheduleOrigins::try_new(
            &candidate_finalized.commands,
            &candidate_origins,
            candidate_schedule_entries,
        )?;
        Self::try_new(
            candidate_finalized,
            candidate_origins,
            candidate_schedule_origins,
        )
    }
}

impl ExactCommandOrigins {
    pub(crate) fn validate<C: OriginCommandNode>(
        &self,
        commands: &[C],
    ) -> Result<(), CommandOriginError> {
        validate_paths(commands, &self.0, |origin| &origin.command_path)?;
        validate_origins(&self.0)
    }
}

/// A validated, total producer-local sidecar.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LocalCommandOrigins {
    entries: Vec<CommandOriginDispositionAt>,
    contains_empty_producer: bool,
}

impl LocalCommandOrigins {
    /// Stamp a producer whose outputs contain no nested command nodes.
    pub(crate) fn from_top_level(
        commands: &[NCommand],
        dispositions: Vec<CommandOriginDisposition>,
    ) -> Result<Self, CommandOriginError> {
        let entries = dispositions
            .into_iter()
            .enumerate()
            .map(|(index, disposition)| CommandOriginDispositionAt {
                command_path: vec![index],
                disposition,
            })
            .collect();
        Self::try_new_with_empty_producer(commands, entries, commands.is_empty())
    }

    /// Validate a recursively assembled producer sidecar.
    #[cfg(test)]
    pub(crate) fn try_new(
        commands: &[NCommand],
        entries: Vec<CommandOriginDispositionAt>,
    ) -> Result<Self, CommandOriginError> {
        Self::try_new_with_empty_producer(commands, entries, false)
    }

    /// Validate a recursively assembled sidecar while retaining whether one of
    /// its producer invocations emitted no command to inherit the input.
    pub(crate) fn try_new_with_empty_producer(
        commands: &[NCommand],
        entries: Vec<CommandOriginDispositionAt>,
        contains_empty_producer: bool,
    ) -> Result<Self, CommandOriginError> {
        validate_paths(commands, &entries, |entry| &entry.command_path)?;
        if !commands.is_empty() {
            let inherited = entries
                .iter()
                .filter(|entry| {
                    entry.command_path.len() == 1
                        && entry.disposition == CommandOriginDisposition::Inherit
                })
                .count();
            if inherited != 1 {
                return Err(CommandOriginError::TopLevelInheritCount { actual: inherited });
            }
        }
        Ok(Self {
            entries,
            contains_empty_producer: contains_empty_producer || commands.is_empty(),
        })
    }

    pub(crate) fn into_parts(self) -> (Vec<CommandOriginDispositionAt>, bool) {
        (self.entries, self.contains_empty_producer)
    }

    /// Compose producer-local dispositions with one authoritative input.
    pub(crate) fn compose(
        self,
        commands: &[NCommand],
        incoming: &CommandOrigin,
    ) -> Result<ExactCommandOrigins, CommandOriginError> {
        if self.contains_empty_producer {
            return Err(CommandOriginError::UnanchoredEmptyProducer);
        }

        let incoming_trigger = match incoming {
            CommandOrigin::Source(source) => Some(*source),
            CommandOrigin::Generated { trigger, .. } => *trigger,
        };
        let origins = self
            .entries
            .into_iter()
            .map(|entry| {
                let origin = match entry.disposition {
                    CommandOriginDisposition::Inherit => incoming.clone(),
                    CommandOriginDisposition::Generated(role) => CommandOrigin::Generated {
                        trigger: Some(incoming_trigger.ok_or_else(|| {
                            CommandOriginError::GeneratedWithoutTrigger {
                                command_path: entry.command_path.clone(),
                                role: role.clone(),
                            }
                        })?),
                        role,
                    },
                };
                Ok(CommandOriginAt {
                    command_path: entry.command_path,
                    origin,
                })
            })
            .collect::<Result<Vec<_>, CommandOriginError>>()?;
        ExactCommandOrigins::try_new(commands, origins)
    }
}

/// Exact rejection reasons for malformed or unanchored command provenance.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub(crate) enum CommandOriginError {
    #[error(transparent)]
    Schedule(#[from] ScheduleOriginError),
    #[error("command-origin paths must not be empty")]
    EmptyPath,
    #[error("duplicate command-origin path {command_path:?}")]
    DuplicatePath { command_path: Vec<usize> },
    #[error("command-origin path {command_path:?} contains an out-of-range child")]
    OutOfRangePath { command_path: Vec<usize> },
    #[error("command-origin path {command_path:?} descends through a non-Fail command")]
    DescentThroughNonFail { command_path: Vec<usize> },
    #[error("command-origin sidecar is missing path {command_path:?}")]
    MissingPath { command_path: Vec<usize> },
    #[error(
        "command-origin sidecar is not in recursive preorder at entry {entry}: expected {expected:?}, found {actual:?}"
    )]
    NonPreorder {
        entry: usize,
        expected: Vec<usize>,
        actual: Vec<usize>,
    },
    #[error("desugar producer has {actual} top-level Inherit dispositions instead of one")]
    TopLevelInheritCount { actual: usize },
    #[error("an empty desugar producer cannot anchor its incoming command origin")]
    UnanchoredEmptyProducer,
    #[error(
        "generated command at path {command_path:?} with role {role:?} has no authoritative source trigger"
    )]
    GeneratedWithoutTrigger {
        command_path: Vec<usize>,
        role: GeneratedCommandRole,
    },
    #[error(
        "generated command at path {command_path:?} has unadmitted role Other({description:?})"
    )]
    UnadmittedGeneratedRole {
        command_path: Vec<usize>,
        description: String,
    },
    #[error(
        "generated command at path {command_path:?} with role {role:?} has the wrong source-trigger association"
    )]
    WrongGeneratedTriggerAssociation {
        command_path: Vec<usize>,
        role: GeneratedCommandRole,
    },
    #[error(
        "nested command at path {command_path:?} changed the effective trigger of enclosing Fail {enclosing_path:?}"
    )]
    NestedFailTriggerMismatch {
        command_path: Vec<usize>,
        enclosing_path: Vec<usize>,
    },
    #[error(
        "command at path {command_path:?} moved source trigger backwards from {previous:?} to {current:?}"
    )]
    SourceTriggerMovedBackward {
        command_path: Vec<usize>,
        previous: crate::frontend_program::SourceSubcommandRef,
        current: crate::frontend_program::SourceSubcommandRef,
    },
    #[error(
        "source-less generated command at path {command_path:?} appears after source-associated commands"
    )]
    SourceLessAfterSource { command_path: Vec<usize> },
    #[error("finalized sort path {command_path:?} has no nominal authority stamp")]
    MissingSortAuthority { command_path: Vec<usize> },
    #[error("sort authority targets missing or non-Sort command path {command_path:?}")]
    UnexpectedSortAuthority { command_path: Vec<usize> },
    #[error("sort command path {command_path:?} received duplicate nominal authority stamps")]
    DuplicateSortAuthority { command_path: Vec<usize> },
}

fn validate_sort_authorities(program: &FinalizedProgram) -> Result<(), CommandOriginError> {
    fn collect(commands: &[ResolvedNCommand], path: &mut Vec<usize>, paths: &mut Vec<Vec<usize>>) {
        for (index, command) in commands.iter().enumerate() {
            path.push(index);
            match command {
                ResolvedNCommand::Sort { .. } => paths.push(path.clone()),
                ResolvedNCommand::Fail(_, nested) => collect(nested, path, paths),
                _ => {}
            }
            path.pop();
        }
    }

    let mut expected = Vec::new();
    collect(&program.commands, &mut Vec::new(), &mut expected);
    let expected_set = expected.iter().cloned().collect::<HashSet<_>>();
    let mut actual = HashSet::default();
    for authority in &program.sort_authorities {
        if !actual.insert(authority.command_path.clone()) {
            return Err(CommandOriginError::DuplicateSortAuthority {
                command_path: authority.command_path.clone(),
            });
        }
    }
    if let Some(command_path) = expected.into_iter().find(|path| !actual.contains(path)) {
        return Err(CommandOriginError::MissingSortAuthority { command_path });
    }
    if let Some(command_path) = program
        .sort_authorities
        .iter()
        .map(|authority| &authority.command_path)
        .find(|path| !expected_set.contains(*path))
    {
        return Err(CommandOriginError::UnexpectedSortAuthority {
            command_path: command_path.clone(),
        });
    }
    Ok(())
}

fn validate_origins(origins: &[CommandOriginAt]) -> Result<(), CommandOriginError> {
    let mut triggers_by_path = HashMap::default();
    let mut previous_source = None;
    let mut saw_source_associated = false;
    for entry in origins {
        if let CommandOrigin::Generated { trigger, role } = &entry.origin {
            if let GeneratedCommandRole::Other(description) = role {
                return Err(CommandOriginError::UnadmittedGeneratedRole {
                    command_path: entry.command_path.clone(),
                    description: description.clone(),
                });
            }
            let source_less_role = matches!(
                role,
                GeneratedCommandRole::FrontendPrelude | GeneratedCommandRole::ProofHeader
            );
            if source_less_role != trigger.is_none() {
                return Err(CommandOriginError::WrongGeneratedTriggerAssociation {
                    command_path: entry.command_path.clone(),
                    role: role.clone(),
                });
            }
        }

        let trigger = match &entry.origin {
            CommandOrigin::Source(source) => Some(*source),
            CommandOrigin::Generated { trigger, .. } => *trigger,
        };
        if let Some(current) = trigger {
            if let Some(previous) = previous_source
                && current < previous
            {
                return Err(CommandOriginError::SourceTriggerMovedBackward {
                    command_path: entry.command_path.clone(),
                    previous,
                    current,
                });
            }
            previous_source = Some(current);
            saw_source_associated = true;
        } else if saw_source_associated {
            return Err(CommandOriginError::SourceLessAfterSource {
                command_path: entry.command_path.clone(),
            });
        }
        if entry.command_path.len() > 1 {
            let enclosing_path = entry.command_path[..entry.command_path.len() - 1].to_vec();
            let enclosing_trigger = triggers_by_path
                .get(&enclosing_path)
                .expect("validated preorder always visits an enclosing Fail before its child");
            if *enclosing_trigger != trigger {
                return Err(CommandOriginError::NestedFailTriggerMismatch {
                    command_path: entry.command_path.clone(),
                    enclosing_path,
                });
            }
        }
        triggers_by_path.insert(entry.command_path.clone(), trigger);
    }
    Ok(())
}

fn validate_paths<C: OriginCommandNode, T>(
    commands: &[C],
    entries: &[T],
    path: impl Fn(&T) -> &[usize],
) -> Result<(), CommandOriginError> {
    let mut seen = HashSet::default();
    for entry in entries {
        let command_path = path(entry);
        validate_path(commands, command_path)?;
        if !seen.insert(command_path.to_vec()) {
            return Err(CommandOriginError::DuplicatePath {
                command_path: command_path.to_vec(),
            });
        }
    }

    let mut expected = Vec::new();
    collect_paths(commands, &mut Vec::new(), &mut expected);
    for command_path in &expected {
        if !seen.contains(command_path) {
            return Err(CommandOriginError::MissingPath {
                command_path: command_path.clone(),
            });
        }
    }
    for (entry, (expected, actual)) in expected.iter().zip(entries.iter().map(&path)).enumerate() {
        if expected.as_slice() != actual {
            return Err(CommandOriginError::NonPreorder {
                entry,
                expected: expected.clone(),
                actual: actual.to_vec(),
            });
        }
    }
    Ok(())
}

fn validate_path<C: OriginCommandNode>(
    commands: &[C],
    path: &[usize],
) -> Result<(), CommandOriginError> {
    if path.is_empty() {
        return Err(CommandOriginError::EmptyPath);
    }

    let mut commands = commands;
    for (depth, index) in path.iter().copied().enumerate() {
        let Some(command) = commands.get(index) else {
            return Err(CommandOriginError::OutOfRangePath {
                command_path: path.to_vec(),
            });
        };
        if depth + 1 == path.len() {
            return Ok(());
        }
        let Some(nested) = command.fail_children() else {
            return Err(CommandOriginError::DescentThroughNonFail {
                command_path: path.to_vec(),
            });
        };
        commands = nested;
    }
    unreachable!("nonempty command path returned without visiting a command")
}

fn collect_paths<C: OriginCommandNode>(
    commands: &[C],
    path: &mut Vec<usize>,
    output: &mut Vec<Vec<usize>>,
) {
    for (index, command) in commands.iter().enumerate() {
        path.push(index);
        output.push(path.clone());
        if let Some(nested) = command.fail_children() {
            collect_paths(nested, path, output);
        }
        path.pop();
    }
}

#[cfg(test)]
mod tests {
    use egglog_ast::span::Span;

    use crate::ast::{GenericRunConfig, GenericSchedule};
    use crate::frontend_program::{SourceGroupId, SourceSubcommandId, SourceSubcommandRef};

    use super::*;

    fn leaf() -> NCommand {
        NCommand::PrintSize(Span::Panic, None)
    }

    fn resolved_leaf() -> ResolvedNCommand {
        ResolvedNCommand::PrintSize(Span::Panic, None)
    }

    fn resolved_run() -> ResolvedNCommand {
        ResolvedNCommand::RunSchedule(GenericSchedule::Run(
            Span::Panic,
            GenericRunConfig {
                ruleset: String::new(),
                until: None,
            },
        ))
    }

    fn resolved_sort(name: &str) -> ResolvedNCommand {
        ResolvedNCommand::Sort {
            span: Span::Panic,
            name: name.to_owned(),
            presort_and_args: None,
            uf: None,
            proof_func: None,
            container_rebuild: None,
            proof_constructors: None,
            unionable: true,
        }
    }

    fn no_resolved_schedules(
        commands: &[ResolvedNCommand],
        origins: &ExactCommandOrigins,
    ) -> ExactScheduleOrigins {
        ExactScheduleOrigins::try_new(commands, origins, Vec::new()).unwrap()
    }

    fn inherit(path: &[usize]) -> CommandOriginDispositionAt {
        CommandOriginDispositionAt {
            command_path: path.to_vec(),
            disposition: CommandOriginDisposition::Inherit,
        }
    }

    fn source(group: u32, subcommand: u32) -> SourceSubcommandRef {
        SourceSubcommandRef::new(
            SourceGroupId::new(group),
            SourceSubcommandId::new(subcommand),
        )
    }

    fn valid_recursive_entries() -> Vec<CommandOriginDispositionAt> {
        vec![
            inherit(&[0]),
            inherit(&[0, 0]),
            inherit(&[0, 1]),
            inherit(&[0, 1, 0]),
        ]
    }

    #[test]
    fn command_origin_rejects_corrupted_recursive_path_coverage() {
        let commands = vec![NCommand::Fail(
            Span::Panic,
            vec![leaf(), NCommand::Fail(Span::Panic, vec![leaf()])],
        )];

        let mut missing = valid_recursive_entries();
        missing.remove(2);
        assert!(matches!(
            LocalCommandOrigins::try_new(&commands, missing),
            Err(CommandOriginError::MissingPath { command_path })
                if command_path == [0, 1]
        ));

        let mut duplicate = valid_recursive_entries();
        duplicate.insert(1, inherit(&[0]));
        assert!(matches!(
            LocalCommandOrigins::try_new(&commands, duplicate),
            Err(CommandOriginError::DuplicatePath { command_path })
                if command_path == [0]
        ));

        let mut empty = valid_recursive_entries();
        empty[0].command_path.clear();
        assert!(matches!(
            LocalCommandOrigins::try_new(&commands, empty),
            Err(CommandOriginError::EmptyPath)
        ));

        let mut out_of_range = valid_recursive_entries();
        out_of_range[3].command_path = vec![0, 1, 9];
        assert!(matches!(
            LocalCommandOrigins::try_new(&commands, out_of_range),
            Err(CommandOriginError::OutOfRangePath { command_path })
                if command_path == [0, 1, 9]
        ));

        let mut through_leaf = valid_recursive_entries();
        through_leaf[3].command_path = vec![0, 0, 0];
        assert!(matches!(
            LocalCommandOrigins::try_new(&commands, through_leaf),
            Err(CommandOriginError::DescentThroughNonFail { command_path })
                if command_path == [0, 0, 0]
        ));

        let mut reordered = valid_recursive_entries();
        reordered.swap(1, 2);
        assert!(matches!(
            LocalCommandOrigins::try_new(&commands, reordered),
            Err(CommandOriginError::NonPreorder { entry: 1, .. })
        ));
    }

    #[test]
    fn command_origin_rejects_zero_or_multiple_top_level_inherits() {
        let commands = vec![leaf(), leaf()];
        let generated =
            CommandOriginDisposition::Generated(GeneratedCommandRole::FrontendDesugaring);
        assert!(matches!(
            LocalCommandOrigins::from_top_level(&commands, vec![generated.clone(), generated]),
            Err(CommandOriginError::TopLevelInheritCount { actual: 0 })
        ));
        assert!(matches!(
            LocalCommandOrigins::from_top_level(
                &commands,
                vec![
                    CommandOriginDisposition::Inherit,
                    CommandOriginDisposition::Inherit
                ]
            ),
            Err(CommandOriginError::TopLevelInheritCount { actual: 2 })
        ));
    }

    #[test]
    fn command_origin_exact_sidecar_rejects_invalid_generated_origin_shapes() {
        let commands = vec![leaf()];
        let at = |origin| CommandOriginAt {
            command_path: vec![0],
            origin,
        };

        assert!(matches!(
            ExactCommandOrigins::try_new(
                &commands,
                vec![at(CommandOrigin::Generated {
                    trigger: Some(source(0, 0)),
                    role: GeneratedCommandRole::Other("unvalidated".to_owned()),
                })]
            ),
            Err(CommandOriginError::UnadmittedGeneratedRole { .. })
        ));
        assert!(matches!(
            ExactCommandOrigins::try_new(
                &commands,
                vec![at(CommandOrigin::Generated {
                    trigger: Some(source(0, 0)),
                    role: GeneratedCommandRole::FrontendPrelude,
                })]
            ),
            Err(CommandOriginError::WrongGeneratedTriggerAssociation { .. })
        ));
        assert!(matches!(
            ExactCommandOrigins::try_new(
                &commands,
                vec![at(CommandOrigin::Generated {
                    trigger: None,
                    role: GeneratedCommandRole::FrontendDesugaring,
                })]
            ),
            Err(CommandOriginError::WrongGeneratedTriggerAssociation { .. })
        ));
    }

    #[test]
    fn command_origin_exact_sidecar_rejects_nested_fail_trigger_mutation() {
        let commands = vec![NCommand::Fail(Span::Panic, vec![leaf()])];
        let origins = vec![
            CommandOriginAt {
                command_path: vec![0],
                origin: CommandOrigin::Source(source(0, 0)),
            },
            CommandOriginAt {
                command_path: vec![0, 0],
                origin: CommandOrigin::Source(source(0, 1)),
            },
        ];
        assert!(matches!(
            ExactCommandOrigins::try_new(&commands, origins),
            Err(CommandOriginError::NestedFailTriggerMismatch {
                command_path,
                enclosing_path,
            }) if command_path == [0, 0] && enclosing_path == [0]
        ));
    }

    #[test]
    fn command_origin_exact_sidecar_validates_resolved_forests_without_inference() {
        let commands = vec![ResolvedNCommand::Fail(
            Span::Panic,
            vec![resolved_leaf(), resolved_leaf()],
        )];
        let trigger = source(2, 4);
        let origins = ExactCommandOrigins::try_new(
            &commands,
            vec![
                CommandOriginAt {
                    command_path: vec![0],
                    origin: CommandOrigin::Source(trigger),
                },
                CommandOriginAt {
                    command_path: vec![0, 0],
                    origin: CommandOrigin::Generated {
                        trigger: Some(trigger),
                        role: GeneratedCommandRole::TermEncoding,
                    },
                },
                CommandOriginAt {
                    command_path: vec![0, 1],
                    origin: CommandOrigin::Generated {
                        trigger: Some(trigger),
                        role: GeneratedCommandRole::ProofInstrumentation,
                    },
                },
            ],
        )
        .unwrap();
        assert!(origins.validate(&commands).is_ok());

        let mismatched = FinalizedProgram::new(vec![resolved_leaf(), resolved_leaf()], Vec::new());
        let schedules = no_resolved_schedules(&mismatched.commands, &origins);
        assert!(matches!(
            OriginatedFinalizedProgram::try_new(mismatched, origins, schedules),
            Err(CommandOriginError::DescentThroughNonFail { command_path })
                if command_path == [0, 0]
        ));
    }

    #[test]
    fn command_origin_rejects_backward_and_nonprefix_source_less_order() {
        let commands = vec![leaf(), leaf()];
        assert!(matches!(
            ExactCommandOrigins::try_new(
                &commands,
                vec![
                    CommandOriginAt {
                        command_path: vec![0],
                        origin: CommandOrigin::Source(source(1, 1)),
                    },
                    CommandOriginAt {
                        command_path: vec![1],
                        origin: CommandOrigin::Source(source(1, 0)),
                    },
                ],
            ),
            Err(CommandOriginError::SourceTriggerMovedBackward { command_path, .. })
                if command_path == [1]
        ));
        assert!(matches!(
            ExactCommandOrigins::try_new(
                &commands,
                vec![
                    CommandOriginAt {
                        command_path: vec![0],
                        origin: CommandOrigin::Source(source(0, 0)),
                    },
                    CommandOriginAt {
                        command_path: vec![1],
                        origin: CommandOrigin::Generated {
                            trigger: None,
                            role: GeneratedCommandRole::ProofHeader,
                        },
                    },
                ],
            ),
            Err(CommandOriginError::SourceLessAfterSource { command_path })
                if command_path == [1]
        ));
        ExactCommandOrigins::try_new(
            &commands,
            vec![
                CommandOriginAt {
                    command_path: vec![0],
                    origin: CommandOrigin::Generated {
                        trigger: None,
                        role: GeneratedCommandRole::FrontendPrelude,
                    },
                },
                CommandOriginAt {
                    command_path: vec![1],
                    origin: CommandOrigin::Source(source(0, 0)),
                },
            ],
        )
        .unwrap();
    }

    fn originated_resolved_leaf(origin: CommandOrigin) -> OriginatedFinalizedProgram {
        let commands = vec![resolved_leaf()];
        let origins = ExactCommandOrigins::try_new(
            &commands,
            vec![CommandOriginAt {
                command_path: vec![0],
                origin,
            }],
        )
        .unwrap();
        let schedules = no_resolved_schedules(&commands, &origins);
        OriginatedFinalizedProgram::try_new(
            FinalizedProgram::new(commands, Vec::new()),
            origins,
            schedules,
        )
        .unwrap()
    }

    #[test]
    fn originated_append_rebases_origins_and_sort_authority_with_one_offset() {
        use crate::typechecking::{SortAuthorityAt, SortRegistrationId};

        let left = originated_resolved_leaf(CommandOrigin::Source(source(0, 0)));
        let right_commands = vec![ResolvedNCommand::Fail(
            Span::Panic,
            vec![resolved_sort("S")],
        )];
        let right_origins = ExactCommandOrigins::try_new(
            &right_commands,
            vec![
                CommandOriginAt {
                    command_path: vec![0],
                    origin: CommandOrigin::Source(source(0, 1)),
                },
                CommandOriginAt {
                    command_path: vec![0, 0],
                    origin: CommandOrigin::Generated {
                        trigger: Some(source(0, 1)),
                        role: GeneratedCommandRole::FrontendDesugaring,
                    },
                },
            ],
        )
        .unwrap();
        let right_schedules = no_resolved_schedules(&right_commands, &right_origins);
        let sort_id = SortRegistrationId::new(9);
        let right = OriginatedFinalizedProgram::try_new(
            FinalizedProgram::new(
                right_commands,
                vec![SortAuthorityAt {
                    command_path: vec![0, 0],
                    local: sort_id,
                    source: None,
                }],
            ),
            right_origins,
            right_schedules,
        )
        .unwrap();

        let appended = left.appended(right).unwrap();
        assert_eq!(appended.commands().len(), 2);
        assert_eq!(
            appended
                .origins()
                .as_slice()
                .iter()
                .map(|entry| entry.command_path.clone())
                .collect::<Vec<_>>(),
            vec![vec![0], vec![1], vec![1, 0]]
        );
        assert_eq!(appended.sort_authorities()[0].command_path, [1, 0]);
        assert_eq!(appended.sort_authorities()[0].local, sort_id);
    }

    #[test]
    fn originated_append_rebases_only_current_schedule_address() {
        use crate::schedule_origin::ScheduleNodeOrigin;

        let left = originated_resolved_leaf(CommandOrigin::Source(source(0, 0)));
        let commands = vec![resolved_run()];
        let origins =
            ExactCommandOrigins::uniform(&commands, CommandOrigin::Source(source(0, 1))).unwrap();
        let schedules = ExactScheduleOrigins::source_input(&commands, &origins).unwrap();
        let right = OriginatedFinalizedProgram::try_new(
            FinalizedProgram::new(commands, Vec::new()),
            origins,
            schedules,
        )
        .unwrap();

        let appended = left.appended(right).unwrap();
        let [schedule] = appended.schedule_origins().as_slice() else {
            panic!("expected one appended schedule node")
        };
        assert_eq!(schedule.address.command_path, [1]);
        assert!(matches!(
            &schedule.origin,
            ScheduleNodeOrigin::Source { source_site, .. }
                if source_site.command_path == [0]
        ));
    }

    #[test]
    fn originated_constructor_rejects_schedule_topology_mutation_without_sidecar_update() {
        let commands = vec![resolved_run()];
        let trigger = CommandOrigin::Source(source(0, 0));
        let origins = ExactCommandOrigins::uniform(&commands, trigger.clone()).unwrap();
        let schedules = ExactScheduleOrigins::source_input(&commands, &origins).unwrap();

        let mutated = vec![ResolvedNCommand::RunSchedule(GenericSchedule::Repeat(
            Span::Panic,
            1,
            Box::new(GenericSchedule::Run(
                Span::Panic,
                GenericRunConfig {
                    ruleset: String::new(),
                    until: None,
                },
            )),
        ))];
        let mutated_origins = ExactCommandOrigins::uniform(&mutated, trigger).unwrap();
        assert!(matches!(
            OriginatedFinalizedProgram::try_new(
                FinalizedProgram::new(mutated, Vec::new()),
                mutated_origins,
                schedules,
            ),
            Err(CommandOriginError::Schedule(
                ScheduleOriginError::MissingAddress { address }
            )) if address.schedule_path == [0]
        ));
    }

    #[test]
    fn originated_finalized_rejects_malformed_sort_authority_without_panicking() {
        let commands = vec![resolved_sort("S")];
        let origins = ExactCommandOrigins::try_new(
            &commands,
            vec![CommandOriginAt {
                command_path: vec![0],
                origin: CommandOrigin::Source(source(0, 0)),
            }],
        )
        .unwrap();
        let schedules = no_resolved_schedules(&commands, &origins);
        assert!(matches!(
            OriginatedFinalizedProgram::try_new(
                FinalizedProgram {
                    commands,
                    sort_authorities: Vec::new(),
                },
                origins,
                schedules,
            ),
            Err(CommandOriginError::MissingSortAuthority { command_path })
                if command_path == [0]
        ));
    }

    #[test]
    fn originated_finalized_rejects_duplicate_and_unexpected_sort_authority() {
        use crate::typechecking::{SortAuthorityAt, SortRegistrationId};

        let trigger = source(0, 0);
        let sort_commands = vec![resolved_sort("S")];
        let sort_origins = ExactCommandOrigins::try_new(
            &sort_commands,
            vec![CommandOriginAt {
                command_path: vec![0],
                origin: CommandOrigin::Source(trigger),
            }],
        )
        .unwrap();
        let authority = SortAuthorityAt {
            command_path: vec![0],
            local: SortRegistrationId::new(9),
            source: None,
        };
        let sort_schedules = no_resolved_schedules(&sort_commands, &sort_origins);
        assert!(matches!(
            OriginatedFinalizedProgram::try_new(
                FinalizedProgram {
                    commands: sort_commands,
                    sort_authorities: vec![authority.clone(), authority],
                },
                sort_origins,
                sort_schedules,
            ),
            Err(CommandOriginError::DuplicateSortAuthority { command_path })
                if command_path == [0]
        ));

        let leaf_commands = vec![resolved_leaf()];
        let leaf_origins = ExactCommandOrigins::try_new(
            &leaf_commands,
            vec![CommandOriginAt {
                command_path: vec![0],
                origin: CommandOrigin::Source(trigger),
            }],
        )
        .unwrap();
        let leaf_schedules = no_resolved_schedules(&leaf_commands, &leaf_origins);
        assert!(matches!(
            OriginatedFinalizedProgram::try_new(
                FinalizedProgram {
                    commands: leaf_commands,
                    sort_authorities: vec![SortAuthorityAt {
                        command_path: vec![0],
                        local: SortRegistrationId::new(10),
                        source: None,
                    }],
                },
                leaf_origins,
                leaf_schedules,
            ),
            Err(CommandOriginError::UnexpectedSortAuthority { command_path })
                if command_path == [0]
        ));
    }

    #[test]
    fn originated_append_fails_closed_on_cross_boundary_origin_order() {
        let original = originated_resolved_leaf(CommandOrigin::Source(source(2, 0)));
        let snapshot = original.clone();
        let backward = originated_resolved_leaf(CommandOrigin::Source(source(1, 0)));
        assert!(matches!(
            original.clone().appended(backward),
            Err(CommandOriginError::SourceTriggerMovedBackward { command_path, .. })
                if command_path == [1]
        ));
        assert_eq!(original, snapshot);

        let source_less = originated_resolved_leaf(CommandOrigin::Generated {
            trigger: None,
            role: GeneratedCommandRole::ProofHeader,
        });
        assert!(matches!(
            original.clone().appended(source_less),
            Err(CommandOriginError::SourceLessAfterSource { command_path })
                if command_path == [1]
        ));

        let prefix = originated_resolved_leaf(CommandOrigin::Generated {
            trigger: None,
            role: GeneratedCommandRole::FrontendPrelude,
        });
        assert!(prefix.appended(original).is_ok());
    }
}
