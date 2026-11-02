//! Read and expand program input within the action owner's commit boundaries.

use super::*;
use crate::program_source::ProgramItem;

impl ActionExecutor<'_> {
    /// Reading and lexing acquire no signatures or backend handles. Dispatch
    /// checks candidates before parsing or expanding them through callbacks.
    pub(super) fn next_item<'s>(
        &mut self,
        program: &mut ProgramSource<'s>,
    ) -> Result<Option<ProgramItem<'s>>, Error> {
        if let Some(command) = program.expanded.next() {
            return Ok(Some(ProgramItem::Expanded(command)));
        }
        if let Some(command) = program.commands.next() {
            return Ok(Some(ProgramItem::Command(command)));
        }
        if let Some(source) = &mut program.source {
            let timer = Instant::now();
            let form = source.next_sexp();
            self.graph.overall_report.frontend_parse += timer.elapsed();
            return Ok(form?.map(ProgramItem::Source));
        }
        Ok(None)
    }

    pub(crate) fn program(
        &mut self,
        mut program: ProgramSource<'_>,
        run_commands: bool,
    ) -> Result<ResolvedNCommandsWithOutput, Error> {
        let stream_includes = run_commands && program.source.is_some();
        let mut outputs = Vec::new();
        let mut desugared_before_proofs = Vec::new();
        let mut desugared = Vec::new();
        while let Some(item) = self.next_item(&mut program)? {
            let can_prepare =
                run_commands && self.graph.proof_state.original_typechecking.is_none();
            let (command, expanded) = match item {
                ProgramItem::Source(form) => {
                    // A source form enters ordinary parser/macro dispatch only
                    // if preparation declines it. Successful actions build no Expr tree.
                    if can_prepare
                        && let Some((head, action)) = self.graph.parser.closed_action(&form)
                        && self
                            .graph
                            .command_macros
                            .preserves_closed_constructor_action(head)
                        && self.prepare_action(action, true)?
                    {
                        continue;
                    }
                    let commands = self.callback(|graph| {
                        let timer = Instant::now();
                        let commands = graph.parser.parse_command(&form);
                        graph.overall_report.frontend_parse += timer.elapsed();
                        commands.map_err(Error::from)
                    })?;
                    program.commands = commands.into_iter();
                    continue;
                }
                ProgramItem::Command(command) => (command, false),
                ProgramItem::Expanded(command) => (command, true),
            };
            if can_prepare && let Command::Action(action) = &command {
                // A transparent macro cannot observe or change this action.
                // Already-expanded actions never invoke their macros again.
                let permitted = expanded
                    || match action {
                        Action::Expr(_, Expr::Call(_, head, _)) => self
                            .graph
                            .command_macros
                            .preserves_closed_constructor_action(Some(head)),
                        Action::Union(..) => self
                            .graph
                            .command_macros
                            .preserves_closed_constructor_action(None),
                        _ => false,
                    };
                if permitted
                    && let Some(action) = typechecking::ClosedAction::from_action(action)
                    && self.prepare_action(action, false)?
                {
                    continue;
                }
            }
            if !expanded {
                // All other callbacks see the already-committed prefix. Their
                // APIs cannot replace signatures or tables, so metadata stays valid.
                let expanded = self.callback(|graph| {
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
                    expanded
                })?;
                program.expanded = expanded.into_iter();
                continue;
            }
            if let Command::Include(span, file) = &command {
                let resolved = self.committed(|graph| {
                    let include_timer = Instant::now();
                    let s = std::fs::read_to_string(file)
                        .map_err(|e| Error::IoError(file.clone().into(), e, span.clone()));
                    graph.overall_report.frontend_other += include_timer.elapsed();
                    let s = s?;
                    let included_program = if stream_includes && !graph.are_proofs_enabled() {
                        ProgramSource::from_text(Some(file.clone()), &s)
                    } else {
                        ProgramSource::from_commands(
                            graph
                                .parse_program_timed(Some(file.clone()), &s)?
                                .into_iter(),
                        )
                    };
                    // run program internal on these include commands
                    graph.process_program_internal(included_program, run_commands)
                })?;
                outputs.extend(resolved.outputs);
                desugared.extend(resolved.resolved);
                desugared_before_proofs.extend(resolved.resolved_before_proofs);
            } else {
                let resolved = self.committed(|graph| graph.resolve_command(command))?;
                // Execution callers discard resolved trees; retaining them here
                // duplicates large proof programs. Keep only the checker's history.
                if run_commands {
                    if self.graph.are_proofs_enabled() {
                        self.graph
                            .proof_check_program
                            .extend(resolved.desugared_before_proofs);
                    }
                } else {
                    desugared_before_proofs.extend(resolved.desugared_before_proofs);
                    desugared.extend(resolved.desugared.clone());
                }
                for processed in resolved.desugared {
                    // even in desugar mode we still run push and pop
                    if run_commands
                        || matches!(
                            processed,
                            ResolvedNCommand::Push(_) | ResolvedNCommand::Pop(_, _)
                        )
                    {
                        let result = self.command(processed)?;
                        outputs.extend(result);
                    }
                }
            }
        }
        Ok(ResolvedNCommandsWithOutput {
            outputs,
            resolved_before_proofs: desugared_before_proofs,
            resolved: desugared,
        })
    }
}
