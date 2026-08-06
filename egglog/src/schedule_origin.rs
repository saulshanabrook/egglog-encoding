//! Exact producer-stamped provenance for every structured schedule node.
//!
//! Schedule syntax is traversed only to validate total node addresses.  A
//! producer must state whether each output node inherits one exact input node
//! or was generated with a closed role and an exact command/node anchor.  No
//! schedule name, ruleset name, span, rendered form, or structural similarity
//! participates in that semantic decision.

use std::fmt::Display;
use std::hash::Hash;

use thiserror::Error;

use crate::ast::{GenericCommand, GenericNCommand, GenericSchedule};
use crate::command_origin::{ExactCommandOrigins, OriginCommandNode};
use crate::frontend_program::{CommandOrigin, SourceSubcommandRef};
use crate::util::{HashMap, HashSet};

/// The exact location of one schedule node inside a recursive command forest.
///
/// `command_path` descends only through `Fail`. `schedule_path` is empty for
/// the schedule root, selects a `Sequence` child by its index, and selects the
/// sole child of `Repeat` or `Saturate` with index zero.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct ScheduleNodeAddress {
    pub(crate) command_path: Vec<usize>,
    pub(crate) schedule_path: Vec<usize>,
}

/// Closed roles for schedule nodes introduced by frontend producers.
#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(dead_code)] // remaining roles are activated by proof/macro producer integration
pub(crate) enum GeneratedScheduleRole {
    FrontendDesugaring,
    MacroExpansion,
    ProofInstrumentation,
    ProofMaintenance(ProofMaintenanceSite),
}

/// Exact placement of proof-maintenance schedule nodes relative to their
/// triggering source operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)] // every site is part of the closed proof-producer vocabulary
pub(crate) enum ProofMaintenanceSite {
    AdjacentToRun,
    BeforeExtract,
    AfterCommand,
}

/// A stable exact anchor captured when a schedule node is generated.
///
/// The address names the producer's input, while the copied origin survives
/// later command-path rebasing.  This intentionally retains more information
/// than a source trigger alone: two identical generated Runs anchored at
/// different input nodes remain distinguishable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ExactScheduleAnchor {
    Command {
        input_command_path: Vec<usize>,
        origin: CommandOrigin,
    },
    Node {
        input: ScheduleNodeAddress,
        origin: Box<ScheduleNodeOrigin>,
    },
}

/// Authoritative provenance of one schedule node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ScheduleNodeOrigin {
    Source {
        source: SourceSubcommandRef,
        source_site: ScheduleNodeAddress,
    },
    Generated {
        trigger: SourceSubcommandRef,
        role: GeneratedScheduleRole,
        anchor: ExactScheduleAnchor,
        /// The output address at the producer that created the node.  Unlike
        /// the sidecar entry's current address, this is deliberately stable.
        producer_site: ScheduleNodeAddress,
    },
}

impl ScheduleNodeOrigin {
    fn trigger(&self) -> SourceSubcommandRef {
        match self {
            Self::Source { source, .. } => *source,
            Self::Generated { trigger, .. } => *trigger,
        }
    }
}

/// One authoritative origin at its current schedule-node address.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ScheduleNodeOriginAt {
    pub(crate) address: ScheduleNodeAddress,
    pub(crate) origin: ScheduleNodeOrigin,
}

/// A total recursive schedule-origin sidecar for one command forest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ExactScheduleOrigins(Vec<ScheduleNodeOriginAt>);

impl ExactScheduleOrigins {
    pub(crate) fn try_new<C: ScheduleCommandNode>(
        commands: &[C],
        command_origins: &ExactCommandOrigins,
        entries: Vec<ScheduleNodeOriginAt>,
    ) -> Result<Self, ScheduleOriginError> {
        validate_total_addresses(commands, &entries, |entry| &entry.address)?;
        validate_exact_origins(command_origins, &entries)?;
        Ok(Self(entries))
    }

    /// Stamp schedule nodes at the parser/source boundary.  A generated input
    /// carrying a schedule must already have an exact schedule sidecar from
    /// its producer; silently treating it as source would erase provenance.
    pub(crate) fn source_input<C: ScheduleCommandNode>(
        commands: &[C],
        command_origins: &ExactCommandOrigins,
    ) -> Result<Self, ScheduleOriginError> {
        let addresses = collect_schedule_addresses(commands);
        let origins_by_path = command_origins_by_path(command_origins);
        let entries = addresses
            .into_iter()
            .map(|address| {
                let command_origin =
                    origins_by_path.get(&address.command_path).ok_or_else(|| {
                        ScheduleOriginError::MissingEnclosingCommandOrigin {
                            command_path: address.command_path.clone(),
                        }
                    })?;
                let CommandOrigin::Source(source) = command_origin else {
                    return Err(ScheduleOriginError::UnstampedGeneratedInput {
                        address: address.clone(),
                    });
                };
                Ok(ScheduleNodeOriginAt {
                    origin: ScheduleNodeOrigin::Source {
                        source: *source,
                        source_site: address.clone(),
                    },
                    address,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Self::try_new(commands, command_origins, entries)
    }

    pub(crate) fn validate<C: ScheduleCommandNode>(
        &self,
        commands: &[C],
        command_origins: &ExactCommandOrigins,
    ) -> Result<(), ScheduleOriginError> {
        validate_total_addresses(commands, &self.0, |entry| &entry.address)?;
        validate_exact_origins(command_origins, &self.0)
    }

    /// Entries are in deterministic command/schedule recursive preorder.
    #[allow(dead_code)] // consumed by the pending compile-only mapper
    pub(crate) fn as_slice(&self) -> &[ScheduleNodeOriginAt] {
        &self.0
    }

    pub(crate) fn into_entries(self) -> Vec<ScheduleNodeOriginAt> {
        self.0
    }
}

/// A producer-local anchor resolved against the producer's exact input.
#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(dead_code)] // node anchors are activated by proof schedule wrapping
pub(crate) enum LocalScheduleAnchor {
    Command { input_command_path: Vec<usize> },
    Node { input: ScheduleNodeAddress },
}

/// How one output schedule node relates to the producer's input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ScheduleOriginDisposition {
    Inherit {
        input: ScheduleNodeAddress,
    },
    Generated {
        role: GeneratedScheduleRole,
        anchor: LocalScheduleAnchor,
    },
}

/// One producer-local schedule disposition at an exact output address.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ScheduleOriginDispositionAt {
    pub(crate) address: ScheduleNodeAddress,
    pub(crate) disposition: ScheduleOriginDisposition,
}

/// A validated, total producer-local schedule plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LocalScheduleOrigins(Vec<ScheduleOriginDispositionAt>);

impl LocalScheduleOrigins {
    pub(crate) fn try_new<C: ScheduleCommandNode>(
        commands: &[C],
        entries: Vec<ScheduleOriginDispositionAt>,
    ) -> Result<Self, ScheduleOriginError> {
        validate_total_addresses(commands, &entries, |entry| &entry.address)?;
        Ok(Self(entries))
    }

    /// Explicit identity plan for a topology-preserving producer.
    pub(crate) fn identity<C: ScheduleCommandNode>(
        commands: &[C],
    ) -> Result<Self, ScheduleOriginError> {
        let entries = collect_schedule_addresses(commands)
            .into_iter()
            .map(|address| ScheduleOriginDispositionAt {
                disposition: ScheduleOriginDisposition::Inherit {
                    input: address.clone(),
                },
                address,
            })
            .collect();
        Self::try_new(commands, entries)
    }

    /// Explicitly assert that a producer emitted no schedule nodes.
    pub(crate) fn empty<C: ScheduleCommandNode>(
        commands: &[C],
    ) -> Result<Self, ScheduleOriginError> {
        Self::try_new(commands, Vec::new())
    }

    pub(crate) fn into_entries(self) -> Vec<ScheduleOriginDispositionAt> {
        self.0
    }

    /// Compose local producer decisions with exact input authority.
    pub(crate) fn compose<C: ScheduleCommandNode>(
        self,
        input_command_origins: &ExactCommandOrigins,
        input_schedule_origins: &ExactScheduleOrigins,
        output_commands: &[C],
        output_command_origins: &ExactCommandOrigins,
    ) -> Result<ExactScheduleOrigins, ScheduleOriginError> {
        let input_commands = command_origins_by_path(input_command_origins);
        let input_schedules = input_schedule_origins
            .as_slice()
            .iter()
            .map(|entry| (entry.address.clone(), &entry.origin))
            .collect::<HashMap<_, _>>();
        let mut inherited = HashMap::<ScheduleNodeAddress, usize>::default();
        let mut output = Vec::with_capacity(self.0.len());

        for entry in self.0 {
            let origin = match entry.disposition {
                ScheduleOriginDisposition::Inherit { input } => {
                    let input_origin = input_schedules.get(&input).ok_or_else(|| {
                        ScheduleOriginError::UnknownInheritedInput {
                            output: entry.address.clone(),
                            input: input.clone(),
                        }
                    })?;
                    let count = inherited.entry(input.clone()).or_default();
                    *count += 1;
                    if *count > 1 {
                        return Err(ScheduleOriginError::MultiplyInheritedInput { input });
                    }
                    (*input_origin).clone()
                }
                ScheduleOriginDisposition::Generated { role, anchor } => {
                    let (trigger, anchor) = match anchor {
                        LocalScheduleAnchor::Command { input_command_path } => {
                            let command_origin = input_commands
                                .get(&input_command_path)
                                .ok_or_else(|| ScheduleOriginError::UnknownCommandAnchor {
                                    output: entry.address.clone(),
                                    input_command_path: input_command_path.clone(),
                                })?;
                            let trigger = command_trigger(command_origin).ok_or_else(|| {
                                ScheduleOriginError::GeneratedWithoutSourceTrigger {
                                    output: entry.address.clone(),
                                    role: role.clone(),
                                }
                            })?;
                            (
                                trigger,
                                ExactScheduleAnchor::Command {
                                    input_command_path,
                                    origin: (*command_origin).clone(),
                                },
                            )
                        }
                        LocalScheduleAnchor::Node { input } => {
                            let input_origin = input_schedules.get(&input).ok_or_else(|| {
                                ScheduleOriginError::UnknownNodeAnchor {
                                    output: entry.address.clone(),
                                    input: input.clone(),
                                }
                            })?;
                            (
                                input_origin.trigger(),
                                ExactScheduleAnchor::Node {
                                    input,
                                    origin: Box::new((*input_origin).clone()),
                                },
                            )
                        }
                    };
                    ScheduleNodeOrigin::Generated {
                        trigger,
                        role,
                        anchor,
                        producer_site: entry.address.clone(),
                    }
                }
            };
            output.push(ScheduleNodeOriginAt {
                address: entry.address,
                origin,
            });
        }

        if let Some(input) = input_schedules
            .keys()
            .find(|input| inherited.get(*input).copied().unwrap_or(0) == 0)
        {
            return Err(ScheduleOriginError::DroppedInput {
                input: (*input).clone(),
            });
        }

        ExactScheduleOrigins::try_new(output_commands, output_command_origins, output)
    }
}

/// Structural schedule access used solely for address/topology validation.
pub(crate) trait ScheduleCommandNode: OriginCommandNode {
    fn collect_owned_schedule_addresses(
        &self,
        command_path: &mut Vec<usize>,
        output: &mut Vec<ScheduleNodeAddress>,
    );
}

impl<Head, Leaf> ScheduleCommandNode for GenericNCommand<Head, Leaf>
where
    Head: Clone + Display,
    Leaf: Clone + PartialEq + Eq + Display + Hash,
{
    fn collect_owned_schedule_addresses(
        &self,
        command_path: &mut Vec<usize>,
        output: &mut Vec<ScheduleNodeAddress>,
    ) {
        match self {
            GenericNCommand::RunSchedule(schedule) => {
                collect_one_schedule(schedule, command_path, &mut Vec::new(), output)
            }
            GenericNCommand::Fail(_, nested) => {
                collect_schedule_addresses_into(nested, command_path, output)
            }
            _ => {}
        }
    }
}

impl<Head, Leaf> ScheduleCommandNode for GenericCommand<Head, Leaf>
where
    Head: Clone + Display,
    Leaf: Clone + PartialEq + Eq + Display + Hash,
{
    fn collect_owned_schedule_addresses(
        &self,
        command_path: &mut Vec<usize>,
        output: &mut Vec<ScheduleNodeAddress>,
    ) {
        match self {
            GenericCommand::RunSchedule(schedule) => {
                collect_one_schedule(schedule, command_path, &mut Vec::new(), output)
            }
            GenericCommand::Fail(_, nested) => {
                collect_schedule_addresses_into(nested, command_path, output)
            }
            _ => {}
        }
    }
}

pub(crate) fn collect_schedule_addresses<C: ScheduleCommandNode>(
    commands: &[C],
) -> Vec<ScheduleNodeAddress> {
    let mut output = Vec::new();
    collect_schedule_addresses_into(commands, &mut Vec::new(), &mut output);
    output
}

fn collect_schedule_addresses_into<C: ScheduleCommandNode>(
    commands: &[C],
    command_path: &mut Vec<usize>,
    output: &mut Vec<ScheduleNodeAddress>,
) {
    for (index, command) in commands.iter().enumerate() {
        command_path.push(index);
        command.collect_owned_schedule_addresses(command_path, output);
        command_path.pop();
    }
}

fn collect_one_schedule<Head, Leaf>(
    schedule: &GenericSchedule<Head, Leaf>,
    command_path: &[usize],
    schedule_path: &mut Vec<usize>,
    output: &mut Vec<ScheduleNodeAddress>,
) {
    output.push(ScheduleNodeAddress {
        command_path: command_path.to_vec(),
        schedule_path: schedule_path.clone(),
    });
    match schedule {
        GenericSchedule::Saturate(_, child) | GenericSchedule::Repeat(_, _, child) => {
            schedule_path.push(0);
            collect_one_schedule(child, command_path, schedule_path, output);
            schedule_path.pop();
        }
        GenericSchedule::Sequence(_, children) => {
            for (index, child) in children.iter().enumerate() {
                schedule_path.push(index);
                collect_one_schedule(child, command_path, schedule_path, output);
                schedule_path.pop();
            }
        }
        GenericSchedule::Run(..) => {}
    }
}

fn validate_total_addresses<C: ScheduleCommandNode, T>(
    commands: &[C],
    entries: &[T],
    address: impl Fn(&T) -> &ScheduleNodeAddress,
) -> Result<(), ScheduleOriginError> {
    let expected = collect_schedule_addresses(commands);
    let expected_set = expected.iter().cloned().collect::<HashSet<_>>();
    let mut seen = HashSet::default();
    for entry in entries {
        let actual = address(entry);
        if !expected_set.contains(actual) {
            return Err(ScheduleOriginError::UnexpectedAddress {
                address: actual.clone(),
            });
        }
        if !seen.insert(actual.clone()) {
            return Err(ScheduleOriginError::DuplicateAddress {
                address: actual.clone(),
            });
        }
    }
    if let Some(missing) = expected.iter().find(|address| !seen.contains(*address)) {
        return Err(ScheduleOriginError::MissingAddress {
            address: missing.clone(),
        });
    }
    for (entry, (expected, actual)) in expected.iter().zip(entries.iter().map(address)).enumerate()
    {
        if expected != actual {
            return Err(ScheduleOriginError::NonPreorder {
                entry,
                expected: expected.clone(),
                actual: actual.clone(),
            });
        }
    }
    Ok(())
}

fn validate_exact_origins(
    command_origins: &ExactCommandOrigins,
    entries: &[ScheduleNodeOriginAt],
) -> Result<(), ScheduleOriginError> {
    let command_origins = command_origins_by_path(command_origins);
    for entry in entries {
        let command_origin = command_origins
            .get(&entry.address.command_path)
            .ok_or_else(|| ScheduleOriginError::MissingEnclosingCommandOrigin {
                command_path: entry.address.command_path.clone(),
            })?;
        let enclosing_trigger = command_trigger(command_origin);
        if enclosing_trigger != Some(entry.origin.trigger()) {
            return Err(ScheduleOriginError::EnclosingTriggerMismatch {
                address: entry.address.clone(),
                command_trigger: enclosing_trigger,
                schedule_trigger: entry.origin.trigger(),
            });
        }
        if let ScheduleNodeOrigin::Generated {
            trigger, anchor, ..
        } = &entry.origin
        {
            let anchor_trigger = match anchor {
                ExactScheduleAnchor::Command { origin, .. } => command_trigger(origin),
                ExactScheduleAnchor::Node { origin, .. } => Some(origin.trigger()),
            };
            if anchor_trigger != Some(*trigger) {
                return Err(ScheduleOriginError::AnchorTriggerMismatch {
                    address: entry.address.clone(),
                    anchor_trigger,
                    schedule_trigger: *trigger,
                });
            }
        }
    }
    Ok(())
}

fn command_origins_by_path(origins: &ExactCommandOrigins) -> HashMap<Vec<usize>, &CommandOrigin> {
    origins
        .as_slice()
        .iter()
        .map(|entry| (entry.command_path.clone(), &entry.origin))
        .collect()
}

fn command_trigger(origin: &CommandOrigin) -> Option<SourceSubcommandRef> {
    match origin {
        CommandOrigin::Source(source) => Some(*source),
        CommandOrigin::Generated { trigger, .. } => *trigger,
    }
}

/// Exact rejection reasons for malformed or unanchored schedule provenance.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub(crate) enum ScheduleOriginError {
    #[error("unexpected schedule-origin address {address:?}")]
    UnexpectedAddress { address: ScheduleNodeAddress },
    #[error("duplicate schedule-origin address {address:?}")]
    DuplicateAddress { address: ScheduleNodeAddress },
    #[error("schedule-origin sidecar is missing address {address:?}")]
    MissingAddress { address: ScheduleNodeAddress },
    #[error(
        "schedule-origin sidecar is not in recursive preorder at entry {entry}: expected {expected:?}, found {actual:?}"
    )]
    NonPreorder {
        entry: usize,
        expected: ScheduleNodeAddress,
        actual: ScheduleNodeAddress,
    },
    #[error("schedule command path {command_path:?} has no exact enclosing command origin")]
    MissingEnclosingCommandOrigin { command_path: Vec<usize> },
    #[error("generated input schedule node {address:?} has no producer-stamped schedule origin")]
    UnstampedGeneratedInput { address: ScheduleNodeAddress },
    #[error("output schedule node {output:?} inherits unknown input node {input:?}")]
    UnknownInheritedInput {
        output: ScheduleNodeAddress,
        input: ScheduleNodeAddress,
    },
    #[error("input schedule node {input:?} was inherited more than once")]
    MultiplyInheritedInput { input: ScheduleNodeAddress },
    #[error("input schedule node {input:?} was not inherited")]
    DroppedInput { input: ScheduleNodeAddress },
    #[error(
        "generated output schedule node {output:?} anchors unknown input command {input_command_path:?}"
    )]
    UnknownCommandAnchor {
        output: ScheduleNodeAddress,
        input_command_path: Vec<usize>,
    },
    #[error("generated output schedule node {output:?} anchors unknown input node {input:?}")]
    UnknownNodeAnchor {
        output: ScheduleNodeAddress,
        input: ScheduleNodeAddress,
    },
    #[error("generated output schedule node {output:?} with role {role:?} has no source trigger")]
    GeneratedWithoutSourceTrigger {
        output: ScheduleNodeAddress,
        role: GeneratedScheduleRole,
    },
    #[error(
        "schedule node {address:?} has trigger {schedule_trigger:?}, but its enclosing command has {command_trigger:?}"
    )]
    EnclosingTriggerMismatch {
        address: ScheduleNodeAddress,
        command_trigger: Option<SourceSubcommandRef>,
        schedule_trigger: SourceSubcommandRef,
    },
    #[error(
        "generated schedule node {address:?} has trigger {schedule_trigger:?}, but its exact anchor has {anchor_trigger:?}"
    )]
    AnchorTriggerMismatch {
        address: ScheduleNodeAddress,
        anchor_trigger: Option<SourceSubcommandRef>,
        schedule_trigger: SourceSubcommandRef,
    },
    #[error("global elimination unexpectedly generated schedule-bearing command {command_path:?}")]
    GeneratedGlobalSchedule { command_path: Vec<usize> },
}

#[cfg(test)]
mod tests {
    use egglog_ast::span::Span;

    use crate::ast::GenericRunConfig;
    use crate::command_origin::{CommandOriginAt, ExactCommandOrigins};
    use crate::frontend_program::{
        GeneratedCommandRole as GeneratedCommandOriginRole, SourceGroupId, SourceSubcommandId,
    };
    use crate::{NCommand, Schedule};

    use super::*;

    fn source(group: u32, command: u32) -> SourceSubcommandRef {
        SourceSubcommandRef::new(SourceGroupId::new(group), SourceSubcommandId::new(command))
    }

    fn run() -> Schedule {
        GenericSchedule::Run(
            Span::Panic,
            GenericRunConfig {
                ruleset: String::new(),
                until: None,
            },
        )
    }

    fn run_command() -> NCommand {
        NCommand::RunSchedule(run())
    }

    fn nested_schedule(repeat: usize) -> Schedule {
        GenericSchedule::Sequence(
            Span::Panic,
            vec![
                GenericSchedule::Repeat(Span::Panic, repeat, Box::new(run())),
                GenericSchedule::Saturate(
                    Span::Panic,
                    Box::new(GenericSchedule::Sequence(Span::Panic, vec![run(), run()])),
                ),
            ],
        )
    }

    fn source_command_origins(
        commands: &[NCommand],
        trigger: SourceSubcommandRef,
    ) -> ExactCommandOrigins {
        ExactCommandOrigins::uniform(commands, CommandOrigin::Source(trigger)).unwrap()
    }

    #[test]
    fn schedule_addresses_are_total_recursive_preorder() {
        let commands = vec![NCommand::Fail(
            Span::Panic,
            vec![NCommand::RunSchedule(nested_schedule(7))],
        )];
        assert_eq!(
            collect_schedule_addresses(&commands),
            vec![
                ScheduleNodeAddress {
                    command_path: vec![0, 0],
                    schedule_path: vec![],
                },
                ScheduleNodeAddress {
                    command_path: vec![0, 0],
                    schedule_path: vec![0],
                },
                ScheduleNodeAddress {
                    command_path: vec![0, 0],
                    schedule_path: vec![0, 0],
                },
                ScheduleNodeAddress {
                    command_path: vec![0, 0],
                    schedule_path: vec![1],
                },
                ScheduleNodeAddress {
                    command_path: vec![0, 0],
                    schedule_path: vec![1, 0],
                },
                ScheduleNodeAddress {
                    command_path: vec![0, 0],
                    schedule_path: vec![1, 0, 0],
                },
                ScheduleNodeAddress {
                    command_path: vec![0, 0],
                    schedule_path: vec![1, 0, 1],
                },
            ]
        );
    }

    #[test]
    fn repeat_literal_never_changes_schedule_origin_shape() {
        let shapes = [0, 1, 100_000].map(|count| {
            collect_schedule_addresses(&[NCommand::RunSchedule(GenericSchedule::Repeat(
                Span::Panic,
                count,
                Box::new(run()),
            ))])
        });
        assert_eq!(shapes[0], shapes[1]);
        assert_eq!(shapes[1], shapes[2]);
        assert_eq!(shapes[0].len(), 2);
    }

    #[test]
    fn local_sidecar_rejects_missing_duplicate_unexpected_and_nonpreorder_addresses() {
        let commands = vec![NCommand::RunSchedule(GenericSchedule::Repeat(
            Span::Panic,
            1,
            Box::new(run()),
        ))];
        let mut identity = LocalScheduleOrigins::identity(&commands)
            .unwrap()
            .into_entries();

        let missing = vec![identity[0].clone()];
        assert!(matches!(
            LocalScheduleOrigins::try_new(&commands, missing),
            Err(ScheduleOriginError::MissingAddress { address })
                if address.schedule_path == [0]
        ));

        let duplicate = vec![identity[0].clone(), identity[0].clone()];
        assert!(matches!(
            LocalScheduleOrigins::try_new(&commands, duplicate),
            Err(ScheduleOriginError::DuplicateAddress { address })
                if address.schedule_path.is_empty()
        ));

        let mut unexpected = identity.clone();
        unexpected[1].address.schedule_path = vec![1];
        assert!(matches!(
            LocalScheduleOrigins::try_new(&commands, unexpected),
            Err(ScheduleOriginError::UnexpectedAddress { address })
                if address.schedule_path == [1]
        ));

        identity.reverse();
        assert!(matches!(
            LocalScheduleOrigins::try_new(&commands, identity),
            Err(ScheduleOriginError::NonPreorder { entry: 0, .. })
        ));
    }

    #[test]
    fn source_boundary_stamps_exact_sites_and_rejects_generated_schedule_inputs() {
        let commands = vec![run_command()];
        let trigger = source(3, 4);
        let source_origins = source_command_origins(&commands, trigger);
        let schedules = ExactScheduleOrigins::source_input(&commands, &source_origins).unwrap();
        assert_eq!(
            schedules.as_slice(),
            &[ScheduleNodeOriginAt {
                address: ScheduleNodeAddress {
                    command_path: vec![0],
                    schedule_path: vec![],
                },
                origin: ScheduleNodeOrigin::Source {
                    source: trigger,
                    source_site: ScheduleNodeAddress {
                        command_path: vec![0],
                        schedule_path: vec![],
                    },
                },
            }]
        );

        let generated_origins = ExactCommandOrigins::try_new(
            &commands,
            vec![CommandOriginAt {
                command_path: vec![0],
                origin: CommandOrigin::Generated {
                    trigger: Some(trigger),
                    role: GeneratedCommandOriginRole::MacroExpansion,
                },
            }],
        )
        .unwrap();
        assert!(matches!(
            ExactScheduleOrigins::source_input(&commands, &generated_origins),
            Err(ScheduleOriginError::UnstampedGeneratedInput { .. })
        ));
    }

    #[test]
    fn compose_preserves_one_exact_input_and_stamps_command_anchored_generation() {
        let trigger = source(1, 9);
        let input_commands = vec![NCommand::PrintSize(Span::Panic, None)];
        let input_command_origins = source_command_origins(&input_commands, trigger);
        let input_schedules =
            ExactScheduleOrigins::source_input(&input_commands, &input_command_origins).unwrap();

        let output_commands = vec![run_command()];
        let output_command_origins = ExactCommandOrigins::try_new(
            &output_commands,
            vec![CommandOriginAt {
                command_path: vec![0],
                origin: CommandOrigin::Generated {
                    trigger: Some(trigger),
                    role: GeneratedCommandOriginRole::FrontendDesugaring,
                },
            }],
        )
        .unwrap();
        let address = ScheduleNodeAddress {
            command_path: vec![0],
            schedule_path: vec![],
        };
        let local = LocalScheduleOrigins::try_new(
            &output_commands,
            vec![ScheduleOriginDispositionAt {
                address: address.clone(),
                disposition: ScheduleOriginDisposition::Generated {
                    role: GeneratedScheduleRole::FrontendDesugaring,
                    anchor: LocalScheduleAnchor::Command {
                        input_command_path: vec![0],
                    },
                },
            }],
        )
        .unwrap();
        let exact = local
            .compose(
                &input_command_origins,
                &input_schedules,
                &output_commands,
                &output_command_origins,
            )
            .unwrap();
        assert!(matches!(
            &exact.as_slice()[0].origin,
            ScheduleNodeOrigin::Generated {
                trigger: actual_trigger,
                role: GeneratedScheduleRole::FrontendDesugaring,
                anchor: ExactScheduleAnchor::Command {
                    input_command_path,
                    origin: CommandOrigin::Source(anchor_trigger),
                },
                producer_site,
            } if *actual_trigger == trigger
                && *anchor_trigger == trigger
                && input_command_path == &[0]
                && producer_site == &address
        ));
    }

    #[test]
    fn generated_wrapper_and_maintenance_anchor_exact_input_node() {
        let trigger = source(7, 2);
        let input_commands = vec![run_command()];
        let input_command_origins = source_command_origins(&input_commands, trigger);
        let input_schedules =
            ExactScheduleOrigins::source_input(&input_commands, &input_command_origins).unwrap();
        let input_root = ScheduleNodeAddress {
            command_path: vec![0],
            schedule_path: vec![],
        };

        let output_commands = vec![NCommand::RunSchedule(GenericSchedule::Sequence(
            Span::Panic,
            vec![run(), run()],
        ))];
        let output_command_origins = ExactCommandOrigins::try_new(
            &output_commands,
            vec![CommandOriginAt {
                command_path: vec![0],
                origin: CommandOrigin::Generated {
                    trigger: Some(trigger),
                    role: GeneratedCommandOriginRole::ProofInstrumentation,
                },
            }],
        )
        .unwrap();
        let address = |schedule_path| ScheduleNodeAddress {
            command_path: vec![0],
            schedule_path,
        };
        let local = LocalScheduleOrigins::try_new(
            &output_commands,
            vec![
                ScheduleOriginDispositionAt {
                    address: address(vec![]),
                    disposition: ScheduleOriginDisposition::Generated {
                        role: GeneratedScheduleRole::ProofInstrumentation,
                        anchor: LocalScheduleAnchor::Node {
                            input: input_root.clone(),
                        },
                    },
                },
                ScheduleOriginDispositionAt {
                    address: address(vec![0]),
                    disposition: ScheduleOriginDisposition::Inherit {
                        input: input_root.clone(),
                    },
                },
                ScheduleOriginDispositionAt {
                    address: address(vec![1]),
                    disposition: ScheduleOriginDisposition::Generated {
                        role: GeneratedScheduleRole::ProofMaintenance(
                            ProofMaintenanceSite::AdjacentToRun,
                        ),
                        anchor: LocalScheduleAnchor::Node {
                            input: input_root.clone(),
                        },
                    },
                },
            ],
        )
        .unwrap();
        let exact = local
            .compose(
                &input_command_origins,
                &input_schedules,
                &output_commands,
                &output_command_origins,
            )
            .unwrap();
        assert!(matches!(
            &exact.as_slice()[1].origin,
            ScheduleNodeOrigin::Source { source, source_site }
                if *source == trigger && source_site == &input_root
        ));
        assert!(matches!(
            &exact.as_slice()[2].origin,
            ScheduleNodeOrigin::Generated {
                role: GeneratedScheduleRole::ProofMaintenance(
                    ProofMaintenanceSite::AdjacentToRun
                ),
                anchor: ExactScheduleAnchor::Node { input, origin },
                ..
            } if input == &input_root
                && matches!(origin.as_ref(), ScheduleNodeOrigin::Source { source, .. } if *source == trigger)
        ));
    }

    #[test]
    fn compose_rejects_dropped_and_multiply_inherited_nodes() {
        let trigger = source(5, 0);
        let input_commands = vec![run_command()];
        let input_command_origins = source_command_origins(&input_commands, trigger);
        let input_schedules =
            ExactScheduleOrigins::source_input(&input_commands, &input_command_origins).unwrap();
        let output_commands = vec![NCommand::RunSchedule(GenericSchedule::Sequence(
            Span::Panic,
            vec![run(), run()],
        ))];
        let output_command_origins = source_command_origins(&output_commands, trigger);
        let output_addresses = collect_schedule_addresses(&output_commands);
        let input_root = ScheduleNodeAddress {
            command_path: vec![0],
            schedule_path: vec![],
        };

        let multiply = LocalScheduleOrigins::try_new(
            &output_commands,
            output_addresses
                .iter()
                .cloned()
                .map(|address| ScheduleOriginDispositionAt {
                    address,
                    disposition: ScheduleOriginDisposition::Inherit {
                        input: input_root.clone(),
                    },
                })
                .collect(),
        )
        .unwrap();
        assert!(matches!(
            multiply.compose(
                &input_command_origins,
                &input_schedules,
                &output_commands,
                &output_command_origins,
            ),
            Err(ScheduleOriginError::MultiplyInheritedInput { input }) if input == input_root
        ));

        let no_schedule_input_commands = vec![NCommand::PrintSize(Span::Panic, None)];
        let no_schedule_input_origins =
            source_command_origins(&no_schedule_input_commands, trigger);
        let generated = LocalScheduleOrigins::try_new(
            &output_commands,
            output_addresses
                .into_iter()
                .map(|address| ScheduleOriginDispositionAt {
                    address,
                    disposition: ScheduleOriginDisposition::Generated {
                        role: GeneratedScheduleRole::MacroExpansion,
                        anchor: LocalScheduleAnchor::Command {
                            input_command_path: vec![0],
                        },
                    },
                })
                .collect(),
        )
        .unwrap();
        assert!(matches!(
            generated.compose(
                &no_schedule_input_origins,
                &input_schedules,
                &output_commands,
                &output_command_origins,
            ),
            Err(ScheduleOriginError::DroppedInput { input }) if input == input_root
        ));
    }

    #[test]
    fn exact_sidecar_rejects_enclosing_and_anchor_trigger_mismatches() {
        let commands = vec![run_command()];
        let enclosing = source(0, 0);
        let other = source(0, 1);
        let command_origins = source_command_origins(&commands, enclosing);
        let address = ScheduleNodeAddress {
            command_path: vec![0],
            schedule_path: vec![],
        };
        assert!(matches!(
            ExactScheduleOrigins::try_new(
                &commands,
                &command_origins,
                vec![ScheduleNodeOriginAt {
                    address: address.clone(),
                    origin: ScheduleNodeOrigin::Source {
                        source: other,
                        source_site: address.clone(),
                    },
                }],
            ),
            Err(ScheduleOriginError::EnclosingTriggerMismatch { .. })
        ));

        assert!(matches!(
            ExactScheduleOrigins::try_new(
                &commands,
                &command_origins,
                vec![ScheduleNodeOriginAt {
                    address: address.clone(),
                    origin: ScheduleNodeOrigin::Generated {
                        trigger: enclosing,
                        role: GeneratedScheduleRole::ProofMaintenance(
                            ProofMaintenanceSite::AfterCommand,
                        ),
                        anchor: ExactScheduleAnchor::Command {
                            input_command_path: vec![0],
                            origin: CommandOrigin::Source(other),
                        },
                        producer_site: address,
                    },
                }],
            ),
            Err(ScheduleOriginError::AnchorTriggerMismatch { .. })
        ));
    }
}
