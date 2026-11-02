//! Source and AST iterator state for the common command executor.

use crate::*;

// Keep materialized commands inline; only one item is retained by dispatch.
#[allow(clippy::large_enum_variant)]
pub(super) enum ProgramItem<'a> {
    Command(Command),
    Expanded(Command),
    Source(Sexp<'a>),
}

pub(super) struct ProgramSource<'a> {
    pub(super) source: Option<SexpParser<'a>>,
    pub(super) commands: std::vec::IntoIter<Command>,
    pub(super) expanded: std::vec::IntoIter<Command>,
}

impl<'a> ProgramSource<'a> {
    pub(super) fn from_commands(commands: std::vec::IntoIter<Command>) -> Self {
        Self {
            source: None,
            commands,
            expanded: Vec::new().into_iter(),
        }
    }

    pub(super) fn from_text(filename: Option<String>, input: &'a str) -> Self {
        Self {
            source: Some(SexpParser::new(filename, input)),
            commands: Vec::new().into_iter(),
            expanded: Vec::new().into_iter(),
        }
    }
}

#[cfg(test)]
mod tests;
