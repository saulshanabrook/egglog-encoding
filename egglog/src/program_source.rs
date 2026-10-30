//! Read AST commands and incrementally expanded source through one command loop.

use crate::*;
use std::time::Duration;

pub(super) enum ProgramSource<'a> {
    Commands(std::vec::IntoIter<Command>),
    Text {
        parser: SexpParser<'a>,
        expanded: std::vec::IntoIter<Command>,
    },
}

impl ProgramSource<'_> {
    /// Reading and parser expansion may register macros or yield no commands.
    /// Drain each expansion before reading the next form; never execute here.
    pub(super) fn next_command(
        &mut self,
        parser: &mut Parser,
        parse_time: &mut Duration,
    ) -> Result<Option<Command>, ParseError> {
        match self {
            Self::Commands(commands) => Ok(commands.next()),
            Self::Text {
                parser: source,
                expanded,
            } => loop {
                if let Some(command) = expanded.next() {
                    return Ok(Some(command));
                }
                let timer = Instant::now();
                let parsed = parser.parse_next_command(source);
                *parse_time += timer.elapsed();
                match parsed? {
                    Some(commands) => *expanded = commands.into_iter(),
                    None => return Ok(None),
                }
            },
        }
    }
}

#[cfg(test)]
mod tests;
