//! Read AST commands and incrementally expanded source through one command loop.

use crate::*;

pub(super) enum ProgramSource<'a> {
    Commands(std::vec::IntoIter<Command>),
    Text {
        parser: SexpParser<'a>,
        expanded: std::vec::IntoIter<Command>,
    },
}

#[cfg(test)]
mod tests;
