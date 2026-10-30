//! Read, expand and prepare source/AST inputs for the common command executor.

use crate::*;
use action_execution::{GroundActionCache, GroundActions};

// One item is consumed by dispatch before reading another. Keep commands inline
// instead of adding an allocation on every ordinary or proof command.
#[allow(clippy::large_enum_variant)]
pub(super) enum ProgramItem {
    Command(Command),
    Prepared(GroundActions),
}

pub(super) struct ProgramSource<'a> {
    pub(super) source: Option<SexpParser<'a>>,
    commands: std::vec::IntoIter<Command>,
    expanded: std::vec::IntoIter<Command>,
}

impl<'a> ProgramSource<'a> {
    /// Materialized commands retain eager include parsing. Each command's macro
    /// expansion drains before another materialized command is read.
    pub(super) fn from_commands(commands: std::vec::IntoIter<Command>) -> Self {
        Self {
            source: None,
            commands,
            expanded: Vec::new().into_iter(),
        }
    }

    /// Streaming provenance is retained for nested includes; parser and command
    /// macro expansions must each drain before the next source form is read.
    pub(super) fn from_text(filename: Option<String>, input: &'a str) -> Self {
        Self {
            source: Some(SexpParser::new(filename, input)),
            commands: Vec::new().into_iter(),
            expanded: Vec::new().into_iter(),
        }
    }

    /// This stage may expand/register macros and prepare checked actions. It
    /// never executes actions or queues backend work, including on a cache hit.
    pub(super) fn next_item(
        &mut self,
        graph: &mut EGraph,
        calls: &mut GroundActionCache,
        run_commands: bool,
    ) -> Result<Option<ProgramItem>, Error> {
        loop {
            if let Some(command) = self.expanded.next() {
                let timer = Instant::now();
                let prepared = match &command {
                    Command::Action(action) if run_commands => graph.prepare_ground_action(
                        typechecking::ClosedAction::from_action(action),
                        calls,
                        |_| true,
                    ),
                    _ => None,
                };
                graph.overall_report.typecheck += timer.elapsed();
                return Ok(Some(match prepared {
                    Some(prepared) => ProgramItem::Prepared(prepared),
                    None => ProgramItem::Command(command),
                }));
            }
            if let Some(command) = self.commands.next() {
                let types = graph
                    .proof_state
                    .original_typechecking
                    .as_ref()
                    .map(|source| &source.type_info)
                    .unwrap_or(&graph.type_info);
                let timer = Instant::now();
                let expanded =
                    graph
                        .command_macros
                        .apply(command, &mut graph.parser.symbol_gen, types);
                graph.overall_report.frontend_other += timer.elapsed();
                self.expanded = expanded?.into_iter();
            } else if let Some(source) = &mut self.source {
                let commands = if run_commands && graph.proof_state.original_typechecking.is_none()
                {
                    let timer = Instant::now();
                    let form = source.next_sexp();
                    graph.overall_report.frontend_parse += timer.elapsed();
                    let Some(form) = form? else {
                        return Ok(None);
                    };
                    let timer = Instant::now();
                    let prepared = graph
                        .parser
                        .closed_action(&form)
                        .and_then(|(head, action)| {
                            if !graph
                                .command_macros
                                .preserves_closed_constructor_action(head)
                            {
                                return None;
                            }
                            graph.prepare_ground_action(Some(action), calls, |head| {
                                graph.parser.can_parse_constructor_call(head)
                            })
                        });
                    graph.overall_report.typecheck += timer.elapsed();
                    if let Some(prepared) = prepared {
                        return Ok(Some(ProgramItem::Prepared(prepared)));
                    }
                    // Reuse the same owned form for parser dispatch and diagnostics.
                    let timer = Instant::now();
                    let commands = graph.parser.parse_command(&form).map(Some);
                    graph.overall_report.frontend_parse += timer.elapsed();
                    commands
                } else {
                    // Proof and resolution paths need owned spans anyway.
                    let timer = Instant::now();
                    let commands = graph.parser.parse_next_command(source);
                    graph.overall_report.frontend_parse += timer.elapsed();
                    commands
                };
                match commands? {
                    Some(commands) => self.commands = commands.into_iter(),
                    None => return Ok(None),
                }
            } else {
                return Ok(None);
            }
        }
    }
}

#[cfg(test)]
mod tests;
