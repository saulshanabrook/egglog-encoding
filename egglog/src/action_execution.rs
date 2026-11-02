//! Prepare restricted constructor actions without effects; execute them through
//! the same command dispatch as resolved actions. Only insertion-only runs share
//! a commit. Unions retain an individual rebuild boundary.

use crate::*;

struct GroundActions {
    lookups: Vec<(egglog_bridge::TableAction, Vec<usize>)>,
    union: Option<(usize, usize)>,
}

#[derive(Default)]
struct GroundActionBatch {
    pending: Vec<GroundActions>,
    lookups: usize,
}

/// Own the mutable graph borrow while insertions may be pending. Ordinary work
/// receives that borrow only after the preceding actions have committed.
pub(super) struct ActionExecutor<'a> {
    graph: &'a mut EGraph,
    pending: GroundActionBatch,
}

impl<'a> ActionExecutor<'a> {
    /// Drain on every normal or error return. A failed drain takes precedence;
    /// effects are taken from the queue before execution and never replayed.
    pub(super) fn run<T>(
        graph: &'a mut EGraph,
        operation: impl FnOnce(&mut Self) -> Result<T, Error>,
    ) -> Result<T, Error> {
        let mut execution = Self {
            graph,
            pending: GroundActionBatch::default(),
        };
        let result = operation(&mut execution);
        execution
            .graph
            .flush_ground_actions(&mut execution.pending)?;
        result
    }

    fn committed<T>(
        &mut self,
        operation: impl FnOnce(&mut EGraph) -> Result<T, Error>,
    ) -> Result<T, Error> {
        self.graph.flush_ground_actions(&mut self.pending)?;
        operation(self.graph)
    }

    pub(super) fn command(
        &mut self,
        command: ResolvedNCommand,
    ) -> Result<Vec<CommandOutput>, Error> {
        enum CommandPhase {
            Install,
            Actions,
            Check,
            Other,
        }
        let phase = match &command {
            ResolvedNCommand::Sort { .. }
            | ResolvedNCommand::Function(_)
            | ResolvedNCommand::Index { .. }
            | ResolvedNCommand::AddRuleset(..)
            | ResolvedNCommand::UnstableCombinedRuleset(..)
            | ResolvedNCommand::NormRule { .. } => CommandPhase::Install,
            ResolvedNCommand::CoreAction(_)
            | ResolvedNCommand::CoreActions(_)
            | ResolvedNCommand::Input { .. } => CommandPhase::Actions,
            ResolvedNCommand::Check(..) => CommandPhase::Check,
            _ => CommandPhase::Other,
        };
        let command_timer = Instant::now();
        let process_before = self.graph.overall_report.process_time();
        let iteration_before = self.graph.overall_report.run.iterations.len();
        let prepared = match &command {
            ResolvedNCommand::CoreAction(action) => {
                self.graph.prepare_resolved_ground_action(action)
            }
            _ => None,
        };
        let result = if let Some(prepared) = prepared {
            self.graph
                .queue_ground_action(prepared, &mut self.pending)
                .map(|()| Vec::new())
        } else {
            self.committed(|graph| graph.run_command_inner(command))
        };
        let nested_process = self
            .graph
            .overall_report
            .process_time()
            .saturating_sub(process_before);
        let nested_rulesets = self.graph.overall_report.run.iterations[iteration_before..]
            .iter()
            .map(|iteration| iteration.report.total_time())
            .sum();
        let own_time = command_timer
            .elapsed()
            .saturating_sub(nested_process + nested_rulesets);
        match phase {
            CommandPhase::Install => self.graph.overall_report.frontend_install += own_time,
            CommandPhase::Actions => self.graph.overall_report.commands_actions += own_time,
            CommandPhase::Check => self.graph.overall_report.commands_check += own_time,
            CommandPhase::Other => self.graph.overall_report.commands_other += own_time,
        }
        result
    }

    pub(super) fn program(
        &mut self,
        program: Vec<Command>,
        run_commands: bool,
    ) -> Result<ResolvedNCommandsWithOutput, Error> {
        let mut outputs = Vec::new();
        let mut desugared_before_proofs = Vec::new();
        let mut desugared = Vec::new();
        for command in program {
            let callback_free = !self.graph.are_proofs_enabled()
                && self
                    .graph
                    .command_macros
                    .can_typecheck_without_callbacks(&command, &self.graph.type_info);
            let expanded = if callback_free {
                // The capability also certifies that no macros are registered.
                vec![command]
            } else {
                self.committed(|graph| {
                    let types = graph
                        .proof_state
                        .original_typechecking
                        .as_ref()
                        .map(|original| &original.type_info)
                        .unwrap_or(&graph.type_info);
                    let timer = Instant::now();
                    let result =
                        graph
                            .command_macros
                            .apply(command, &mut graph.parser.symbol_gen, types);
                    graph.overall_report.frontend_other += timer.elapsed();
                    result
                })?
            };
            for command in expanded {
                if let Command::Include(span, file) = &command {
                    let resolved = self.committed(|graph| {
                        let include_timer = Instant::now();
                        let s = std::fs::read_to_string(file)
                            .map_err(|e| Error::IoError(file.clone().into(), e, span.clone()));
                        graph.overall_report.frontend_other += include_timer.elapsed();
                        let included_program =
                            graph.parse_program_timed(Some(file.clone()), &s?)?;
                        // run program internal on these include commands
                        graph.process_program_internal(included_program, run_commands)
                    })?;
                    outputs.extend(resolved.outputs);
                    desugared.extend(resolved.resolved);
                    desugared_before_proofs.extend(resolved.resolved_before_proofs);
                } else {
                    let resolved = if callback_free
                        || (!self.graph.are_proofs_enabled()
                            && matches!(&command, Command::Action(action)
                                if self.graph.type_info.typecheck_closed_constructor_action(action).is_some()))
                    {
                        self.graph.resolve_command(command)?
                    } else {
                        self.committed(|graph| graph.resolve_command(command))?
                    };
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
        }
        Ok(ResolvedNCommandsWithOutput {
            outputs,
            resolved_before_proofs: desugared_before_proofs,
            resolved: desugared,
        })
    }
}

impl EGraph {
    /// Prepare one already-resolved constructor expression or union without
    /// allocating IDs or writing. Ordinary resolution has already checked types;
    /// this walk only admits closed calls supported by the physical native tables.
    /// Literals, variables, primitives, globals, views, indexes and custom sorts
    /// retain the ordinary compiler.
    fn prepare_resolved_ground_action(&self, action: &ResolvedAction) -> Option<GroundActions> {
        fn prepare_expr(
            graph: &EGraph,
            expr: &ResolvedExpr,
            prepared: &mut GroundActions,
        ) -> Option<usize> {
            let GenericExpr::Call(_, ResolvedCall::Func(func), args) = expr else {
                return None;
            };
            let function = graph.functions.get(&func.name)?;
            if func.subtype != FunctionSubtype::Constructor
                || function.subtype() != FunctionSubtype::Constructor
                || func.num_outputs() != 1
                || func.role.is_global()
                || function.is_view()
                || function.is_let_binding()
                || graph.type_info.indexes.contains_key(&func.name)
                || !(func.output().as_ref() as &dyn Any).is::<EqSort>()
            {
                return None;
            }
            let table = egglog_bridge::TableAction::for_constructor_insertions(
                &graph.backend,
                function.backend_id,
            )?;
            if table.input_arity() != args.len() {
                return None;
            }
            let args = args
                .iter()
                .map(|arg| prepare_expr(graph, arg, prepared))
                .collect::<Option<Vec<_>>>()?;
            let index = prepared.lookups.len();
            prepared.lookups.push((table, args));
            Some(index)
        }

        if self.proof_state.original_typechecking.is_some() {
            return None;
        }
        let mut prepared = GroundActions {
            lookups: Vec::new(),
            union: None,
        };
        match action {
            ResolvedAction::Expr(_, expr) => {
                prepare_expr(self, expr, &mut prepared)?;
            }
            ResolvedAction::Union(_, left, right) => {
                let left = prepare_expr(self, left, &mut prepared)?;
                let right = prepare_expr(self, right, &mut prepared)?;
                prepared.union = Some((left, right));
            }
            _ => return None,
        }
        Some(prepared)
    }

    fn eval_ground_actions(&mut self, prepared: Vec<GroundActions>) -> Result<(), Error> {
        #[cfg(test)]
        tests::GROUND_ACTIONS_EXECUTED.with(|count| count.set(count.get() + prepared.len()));
        let union = egglog_bridge::UnionAction::new(&self.backend);
        self.backend
            .run_actions(Some(&self.type_info), |state| {
                let mut values = Vec::new();
                for action in prepared {
                    values.clear();
                    for (table, args) in action.lookups {
                        let args: smallvec::SmallVec<[Value; 4]> =
                            args.iter().map(|index| values[*index]).collect();
                        values.push(table.lookup_or_insert(state, &args).unwrap());
                    }
                    if let Some((left, right)) = action.union {
                        union.union(state, values[left], values[right]);
                    }
                }
            })
            .map_err(|error| Error::BackendError(error.to_string()))
    }

    /// Constructor insertion runs share a bounded transaction. A union retains
    /// its original commit/rebuild boundary, including container callbacks.
    fn queue_ground_action(
        &mut self,
        prepared: GroundActions,
        pending: &mut GroundActionBatch,
    ) -> Result<(), Error> {
        if prepared.union.is_some() {
            self.flush_ground_actions(pending)?;
            self.eval_ground_actions(vec![prepared])
        } else {
            pending.lookups += prepared.lookups.len();
            pending.pending.push(prepared);
            if pending.pending.len() >= 256 || pending.lookups >= 16_384 {
                self.flush_ground_actions(pending)?;
            }
            Ok(())
        }
    }

    /// Drain exactly once; failed effects are never replayed.
    fn flush_ground_actions(&mut self, pending: &mut GroundActionBatch) -> Result<(), Error> {
        pending.lookups = 0;
        if !pending.pending.is_empty() {
            let timer = Instant::now();
            let result = self.eval_ground_actions(std::mem::take(&mut pending.pending));
            self.overall_report.commands_actions += timer.elapsed();
            result?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
