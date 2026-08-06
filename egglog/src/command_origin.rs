//! Exact producer-stamped command provenance through frontend desugaring.
//!
//! Desugaring records only a local disposition for each output node.  The
//! authoritative incoming origin is composed afterward, so no command name,
//! schema, span, or rendered form participates in provenance.

use thiserror::Error;

use crate::NCommand;
use crate::frontend_program::{CommandOrigin, GeneratedCommandRole};
use crate::util::{HashMap, HashSet};

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
    fn try_new(
        commands: &[NCommand],
        origins: Vec<CommandOriginAt>,
    ) -> Result<Self, CommandOriginError> {
        validate_paths(commands, &origins, |origin| &origin.command_path)?;
        validate_origins(&origins)?;
        Ok(Self(origins))
    }

    /// Entries are in deterministic recursive command preorder.
    #[allow(dead_code)] // consumed by the pending compile-only mapper
    pub(crate) fn as_slice(&self) -> &[CommandOriginAt] {
        &self.0
    }

    #[cfg(test)]
    pub(crate) fn into_vec(self) -> Vec<CommandOriginAt> {
        self.0
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
}

fn validate_origins(origins: &[CommandOriginAt]) -> Result<(), CommandOriginError> {
    let mut triggers_by_path = HashMap::default();
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

fn validate_paths<T>(
    commands: &[NCommand],
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

fn validate_path(commands: &[NCommand], path: &[usize]) -> Result<(), CommandOriginError> {
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
        let NCommand::Fail(_, nested) = command else {
            return Err(CommandOriginError::DescentThroughNonFail {
                command_path: path.to_vec(),
            });
        };
        commands = nested;
    }
    unreachable!("nonempty command path returned without visiting a command")
}

fn collect_paths(commands: &[NCommand], path: &mut Vec<usize>, output: &mut Vec<Vec<usize>>) {
    for (index, command) in commands.iter().enumerate() {
        path.push(index);
        output.push(path.clone());
        if let NCommand::Fail(_, nested) = command {
            collect_paths(nested, path, output);
        }
        path.pop();
    }
}

#[cfg(test)]
mod tests {
    use egglog_ast::span::Span;

    use crate::frontend_program::{SourceGroupId, SourceSubcommandId, SourceSubcommandRef};

    use super::*;

    fn leaf() -> NCommand {
        NCommand::PrintSize(Span::Panic, None)
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
}
