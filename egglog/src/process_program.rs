//! Source and AST input state and the shared program driver.

use crate::*;

// Keep materialized commands inline; only one item is retained by dispatch.
#[allow(clippy::large_enum_variant)]
pub(super) enum ProgramItem<'a> {
    /// Parsed command whose command macros have not run.
    Command(Command),
    /// Command produced by command macros; do not apply those macros again.
    Expanded(Command),
    /// Lexed source form awaiting command parsing and command macros.
    Source(Sexp<'a, std::ops::Range<usize>>),
}

pub(super) struct ProgramSource<'a> {
    pub(super) source: Option<SexpParser<'a>>,
    pub(super) commands: std::vec::IntoIter<Command>,
    pub(super) expanded: std::vec::IntoIter<Command>,
    /// User commands read by `include`, rather than an internal lowering query.
    included_source: bool,
}

impl<'a> ProgramSource<'a> {
    pub(super) fn from_commands(commands: std::vec::IntoIter<Command>) -> Self {
        Self {
            source: None,
            commands,
            expanded: Vec::new().into_iter(),
            included_source: false,
        }
    }

    pub(super) fn from_text(filename: Option<String>, input: &'a str) -> Self {
        Self {
            source: Some(SexpParser::new(filename, input)),
            commands: Vec::new().into_iter(),
            expanded: Vec::new().into_iter(),
            included_source: false,
        }
    }
}

impl EGraph {
    /// Reading and lexing acquire no signatures or backend handles. Dispatch
    /// checks candidates before parsing or expanding them through callbacks.
    pub(super) fn next_program_item<'s>(
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
            let form = source.next_sexp(|_, range| range);
            self.overall_report.frontend_parse += timer.elapsed();
            return Ok(form?.map(ProgramItem::Source));
        }
        Ok(None)
    }

    /// Run a program and return its outputs, or resolve it without execution.
    /// Only resolution retains the lowered commands in the returned value.
    pub(super) fn process_program_internal(
        &mut self,
        program: ProgramSource<'_>,
        run_commands: bool,
    ) -> Result<ResolvedNCommandsWithOutput, Error> {
        let mut pending = crate::action_execution::GroundActionBatch::default();
        let result = self.process_program_batched(program, run_commands, &mut pending);
        // Commit the completed prefix on success or error; a drain error wins.
        self.flush_ground_actions(&mut pending)?;
        result
    }

    pub(super) fn process_program_batched(
        &mut self,
        mut program: ProgramSource<'_>,
        run_commands: bool,
        pending: &mut crate::action_execution::GroundActionBatch,
    ) -> Result<ResolvedNCommandsWithOutput, Error> {
        let summary_scope = if run_commands {
            self.extension_state::<crate::proof_summary::ProofSummary>()
                .map(crate::proof_summary::ProofSummary::enter)
        } else {
            None
        };
        let stream_includes = run_commands && program.source.is_some();
        let mut outputs = Vec::new();
        let mut desugared_before_proofs = Vec::new();
        let mut desugared = Vec::new();
        while let Some(item) = self.next_program_item(&mut program)? {
            let can_prepare = run_commands && self.proof_state.original_typechecking.is_none();
            let expanded = matches!(&item, ProgramItem::Expanded(_));
            match item {
                ProgramItem::Source(form) => {
                    // A source form enters ordinary parser/macro dispatch only
                    // if preparation declines it. Successful actions build no Expr tree.
                    if can_prepare
                        && let Some((head, action)) = self.parser.closed_action(&form)
                        && self
                            .command_macros
                            .preserves_closed_constructor_action(head)
                        && let Some(prepared) = self.prepare_action(action, true, pending)
                    {
                        self.queue_ground_action(prepared, pending)?;
                    } else {
                        self.flush_ground_actions(pending)?;
                        let commands = {
                            let timer = Instant::now();
                            let commands = self
                                .parser
                                .parse_command(&form.with_spans(program.source.as_ref().unwrap()));
                            self.overall_report.frontend_parse += timer.elapsed();
                            commands.map_err(Error::from)
                        }?;
                        program.commands = commands.into_iter();
                    }
                }
                ProgramItem::Command(command) | ProgramItem::Expanded(command) => {
                    let prepared = if can_prepare && let Command::Action(action) = &command {
                        // A transparent macro cannot observe or change this action.
                        // Already-expanded actions never invoke their macros again.
                        let permitted = expanded
                            || match action {
                                Action::Expr(_, Expr::Call(_, head, _)) => self
                                    .command_macros
                                    .preserves_closed_constructor_action(Some(head)),
                                Action::Union(..) => self
                                    .command_macros
                                    .preserves_closed_constructor_action(None),
                                _ => false,
                            };
                        let action = match action {
                            Action::Expr(_, expr) => Some(typechecking::ClosedAction::Expr(expr)),
                            Action::Union(_, left, right) => {
                                Some(typechecking::ClosedAction::Union(left, right))
                            }
                            _ => None,
                        };
                        if permitted && let Some(action) = action {
                            self.prepare_action(action, false, pending)
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    if let Some(prepared) = prepared {
                        self.queue_ground_action(prepared, pending)?;
                    } else if !expanded {
                        // All other callbacks see the already-committed prefix. Their
                        // APIs cannot replace signatures or tables, so metadata stays valid.
                        self.flush_ground_actions(pending)?;
                        let expanded = {
                            let types = self
                                .proof_state
                                .original_typechecking
                                .as_ref()
                                .map(|source| &source.type_info)
                                .unwrap_or(&self.type_info);
                            let timer = Instant::now();
                            let expanded = self.command_macros.apply(
                                command,
                                &mut self.parser.symbol_gen,
                                types,
                            );
                            self.overall_report.frontend_other += timer.elapsed();
                            expanded
                        }?;
                        program.expanded = expanded.into_iter();
                    } else if let Command::Include(span, file) = &command {
                        self.commit_ground_actions(pending)?;
                        let resolved = {
                            let include_timer = Instant::now();
                            let s = std::fs::read_to_string(file)
                                .map_err(|e| Error::IoError(file.clone().into(), e, span.clone()));
                            self.overall_report.frontend_other += include_timer.elapsed();
                            let s = s?;
                            let mut included_program =
                                if stream_includes && !self.are_proofs_enabled() {
                                    ProgramSource::from_text(Some(file.clone()), &s)
                                } else {
                                    ProgramSource::from_commands(
                                        self.parse_program_timed(Some(file.clone()), &s)?
                                            .into_iter(),
                                    )
                                };
                            included_program.included_source = true;
                            // run program internal on these include commands
                            self.process_program_internal(included_program, run_commands)
                        }?;
                        outputs.extend(resolved.outputs);
                        desugared.extend(resolved.resolved);
                        desugared_before_proofs.extend(resolved.resolved_before_proofs);
                    } else {
                        self.commit_ground_actions(pending)?;
                        if summary_scope
                            .as_ref()
                            .is_some_and(|scope| scope.source || program.included_source)
                        {
                            match &command {
                                Command::Check(..) | Command::ProveExists(..) => self
                                    .extension_state::<crate::proof_summary::ProofSummary>()
                                    .unwrap()
                                    .request(false),
                                Command::Extract(..) | Command::ProveExtract(..) => self
                                    .extension_state::<crate::proof_summary::ProofSummary>()
                                    .unwrap()
                                    .request(true),
                                _ => {}
                            }
                        }
                        let resolved = self.resolve_command(command)?;
                        // Execution callers discard resolved trees; retaining them here
                        // duplicates large proof programs. Keep only the checker's history.
                        if run_commands {
                            if self.are_proofs_enabled() {
                                self.proof_check_program
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
                                let result = self.run_command(processed, Some(pending))?;
                                outputs.extend(result);
                            }
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

    pub(super) fn run_command(
        &mut self,
        command: ResolvedNCommand,
        mut pending: Option<&mut action_execution::GroundActionBatch>,
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
        let process_before = self.overall_report.process_time();
        let iteration_before = self.overall_report.run.iterations.len();
        let action = match &command {
            ResolvedNCommand::CoreAction(ResolvedAction::Expr(_, expr)) => {
                Some(typechecking::ClosedAction::Expr(expr))
            }
            ResolvedNCommand::CoreAction(ResolvedAction::Union(_, left, right)) => {
                Some(typechecking::ClosedAction::Union(left, right))
            }
            _ => None,
        };
        let mut calls = HashMap::default();
        let calls = pending
            .as_deref_mut()
            .map_or(&mut calls, |pending| &mut pending.calls);
        let prepared =
            action.and_then(|action| self.prepare_ground_action(action, calls, |_| true));
        let result = if let Some(prepared) = prepared {
            match pending {
                Some(pending) => self.queue_ground_action(prepared, pending),
                None => self.eval_ground_actions(vec![prepared]),
            }
            .map(|()| Vec::new())
        } else {
            match pending {
                Some(pending) => self.commit_ground_actions(pending),
                None => Ok(()),
            }
            .and_then(|()| self.run_command_inner(command))
        };
        let nested_process = self
            .overall_report
            .process_time()
            .saturating_sub(process_before);
        let nested_rulesets = self.overall_report.run.iterations[iteration_before..]
            .iter()
            .map(|iteration| iteration.report.total_time())
            .sum();
        let own_time = command_timer
            .elapsed()
            .saturating_sub(nested_process + nested_rulesets);
        match phase {
            CommandPhase::Install => self.overall_report.frontend_install += own_time,
            CommandPhase::Actions => self.overall_report.commands_actions += own_time,
            CommandPhase::Check => self.overall_report.commands_check += own_time,
            CommandPhase::Other => self.overall_report.commands_other += own_time,
        }
        result
    }

    fn run_command_inner(
        &mut self,
        command: ResolvedNCommand,
    ) -> Result<Vec<CommandOutput>, Error> {
        match command {
            // Sorts are already declared during typechecking
            ResolvedNCommand::Sort {
                name,
                uf,
                proof_constructors,
                ..
            } => {
                // Restore the sort's UF metadata into proof_state.
                if let Some((uf_ctor, _uf_index)) = uf {
                    self.proof_state
                        .uf_parent
                        .insert(name.clone(), uf_ctor.clone());
                }
                // The Proof sort's :internal-proof-names records the global proof
                // constructors; restore them so container rebuild can recover them.
                if let Some(pc) = proof_constructors {
                    let names = &mut self.proof_state.proof_names;
                    names.proof_datatype = name.clone();
                    names.congr_constructor = pc.congr;
                    names.congr_all_constructor = pc.congr_all;
                    names.eq_trans_constructor = pc.trans;
                    names.eq_sym_constructor = pc.sym;
                    names.container_normalize_constructor = pc.normalize;
                    // Recovered so `native_input` can build `(input …)` base-fact
                    // proofs when replaying an encoded program in a fresh e-graph.
                    names.fiat_prefix = pc.fiat;
                    names.proj_constructor = pc.proj;
                    names.proj_prim_prefix = pc.proj_prim;
                }
                log::info!("Declared sort {name}.")
            }
            ResolvedNCommand::Function(fdecl) => {
                self.declare_function(&fdecl)?;
                log::info!("Declared {} {}.", fdecl.subtype, fdecl.name)
            }
            ResolvedNCommand::Index { name, function, .. } => {
                // Nothing to build: storage creates the occurrence index the
                // first time a rule probes it. Typechecking already registered
                // the relation the atoms resolve against.
                log::info!("Declared index {name} over {function}.");
            }
            ResolvedNCommand::AddRuleset(_span, name) => {
                self.add_ruleset(name.clone());
                log::info!("Declared ruleset {name}.");
            }
            ResolvedNCommand::UnstableCombinedRuleset(span, name, others) => {
                self.add_combined_ruleset(&span, name.clone(), others)?;
                log::info!("Declared ruleset {name}.");
            }
            ResolvedNCommand::NormRule { rule } => {
                let name = rule.name.clone();
                self.add_rule(rule)?;
                log::info!("Declared rule {name}.")
            }
            ResolvedNCommand::RunSchedule(sched) => {
                let report = self.run_schedule(&sched)?;
                log::info!("Ran schedule {sched}.");
                log::info!("Report: {report}");
                // Already recorded by `step_rules`, per iteration.
                return Ok(vec![CommandOutput::RunSchedule(report)]);
            }
            ResolvedNCommand::PrintOverallStatistics(span, file) => match file {
                None => {
                    log::info!("Printed overall statistics");
                    return Ok(vec![CommandOutput::OverallStatistics(
                        self.overall_report.run.clone(),
                    )]);
                }
                Some(path) => {
                    let mut file = std::fs::File::create(&path)
                        .map_err(|e| Error::IoError(path.clone().into(), e, span.clone()))?;
                    log::info!("Printed overall statistics to json file {path}");

                    serde_json::to_writer(&mut file, &self.overall_report.run).map_err(|e| {
                        Error::BackendError(format!("failed writing statistics: {e}"))
                    })?;
                }
            },
            ResolvedNCommand::Check(span, facts) => {
                self.check_facts(&span, &facts)?;
                log::info!("Checked fact {facts:?}.");
            }
            ResolvedNCommand::CoreAction(action) => match &action {
                ResolvedAction::Let(_, name, contents) => {
                    panic!("Globals should have been desugared away: {name} = {contents}")
                }
                _ => {
                    self.eval_actions(&ResolvedActions::new(vec![action.clone()]))?;
                }
            },
            // One `eval_actions` call, so the block's `let`s stay local.
            ResolvedNCommand::CoreActions(actions) => {
                self.eval_actions(&actions)?;
            }
            ResolvedNCommand::LetBegin(..) => {
                unreachable!("LetBegin is removed by remove_globals")
            }
            ResolvedNCommand::ProveExtract(_, expr, variants) => {
                let outputs = self.run_prove_extract(&expr, &variants)?;
                if let Some(summary) = self.extension_state::<crate::proof_summary::ProofSummary>()
                {
                    let count = outputs
                        .iter()
                        .map(|output| match output {
                            CommandOutput::ProveExtract { proof_ids, .. } => proof_ids.len(),
                            _ => 0,
                        })
                        .sum();
                    summary.certificates(count, self.proof_state.verify_proofs);
                }
                return Ok(outputs);
            }
            ResolvedNCommand::Extract(span, expr, variants) => {
                let sort = expr.output_type();

                let x = self.eval_resolved_expr(span.clone(), &expr)?;
                let n = self.eval_resolved_expr(span, &variants)?;
                let n: i64 = self.backend.base_values().unwrap(n);

                if n < 0 {
                    return Err(Error::ExtractError(
                        "cannot extract a negative number of variants".to_string(),
                    ));
                }
                let output = self.extract_command(sort, x, n as usize)?;
                // Avoid rendering terms when messages are disabled.
                if log_enabled!(Level::Info) {
                    match &output {
                        CommandOutput::ExtractBest(termdag, cost, term) => {
                            log::info!("extracted with cost {cost}: {}", termdag.to_string(*term));
                        }
                        CommandOutput::ExtractVariants(_, terms) => {
                            let expr_str = expr.to_string();
                            log::info!("extracted {} variants for {expr_str}", terms.len());
                        }
                        _ => unreachable!(),
                    }
                }
                return Ok(vec![output]);
            }
            ResolvedNCommand::Push(n) => {
                (0..n).for_each(|_| self.push());
                log::info!("Pushed {n} levels.")
            }
            ResolvedNCommand::Pop(span, n) => {
                for _ in 0..n {
                    self.pop().map_err(|err| {
                        if let Error::Pop(_) = err {
                            Error::Pop(span.clone())
                        } else {
                            err
                        }
                    })?;
                }
                log::info!("Popped {n} levels.")
            }
            ResolvedNCommand::PrintFunction(span, f, n, file, mode) => {
                let file = file
                    .map(|file| {
                        let path: PathBuf = file.into();
                        match std::fs::File::create(&path) {
                            Ok(f) => Ok((f, path)),
                            Err(e) => Err(Error::IoError(path, e, span.clone())),
                        }
                    })
                    .transpose()?;
                return self
                    .print_function(&f, n, file, span.clone(), mode)
                    .map_err(|e| match e {
                        Error::TypeError(TypeError::UnboundFunction(f, _)) => {
                            Error::TypeError(TypeError::UnboundFunction(f, span.clone()))
                        }
                        // This case is currently impossible
                        _ => e,
                    })
                    .map(|opt| opt.into_iter().collect());
            }
            ResolvedNCommand::PrintSize(span, f) => {
                let res = self.print_size(f.as_deref()).map_err(|e| match e {
                    Error::TypeError(TypeError::UnboundFunction(f, _)) => {
                        Error::TypeError(TypeError::UnboundFunction(f, span.clone()))
                    }
                    // This case is currently impossible
                    _ => e,
                })?;
                return Ok(vec![res]);
            }
            ResolvedNCommand::Fail(span, cmds) => {
                // A single check is read-only, so avoid cloning the e-graph for
                // the overwhelmingly common negative-assertion form.
                if matches!(cmds.as_slice(), [ResolvedNCommand::Check(..)]) {
                    let check = cmds.into_iter().next().unwrap();
                    return match self.run_command(check, None) {
                        Err(error) => {
                            log::info!("Command failed as expected: {error}");
                            Ok(vec![])
                        }
                        Ok(_) => Err(Error::ExpectFail(span)),
                    };
                }

                self.push();
                let failure = cmds
                    .into_iter()
                    .find_map(|command| self.run_command(command, None).err());
                self.pop()
                    .expect("the snapshot pushed for `fail` must still be present");
                return match failure {
                    Some(error) => {
                        log::info!("Command failed as expected: {error}");
                        Ok(vec![])
                    }
                    None => Err(Error::ExpectFail(span)),
                };
            }
            ResolvedNCommand::Input {
                span,
                name,
                file,
                proof_base,
            } => {
                // An encoded program (term/proof mode, or a replayed desugared
                // program) declares nothing under the function's own name, so the
                // name resolving to a view is what says the rows go into the
                // encoded tables; a plain program targets a user
                // relation/constructor loaded by the relation loader.
                if self.functions.get(&name).is_some_and(|f| f.is_fd_view()) {
                    self.native_input(span, &name, file, proof_base)?;
                } else {
                    self.input_file(span, &name, file)?;
                }
            }
            ResolvedNCommand::Output { span, file, exprs } => {
                let mut filename = self.fact_directory.clone().unwrap_or_default();
                filename.push(file.as_str());

                // Preserve the command's file-error ordering: reject an invalid
                // output path before evaluating expressions.
                use std::io::Write;
                let mut f = File::options()
                    .append(true)
                    .create(true)
                    .open(&filename)
                    .map_err(|e| Error::IoError(filename.clone(), e, span.clone()))?;

                // Evaluation may mutate the e-graph, so finish it before
                // extraction takes a shared borrow for its prepared costs.
                let roots = exprs
                    .iter()
                    .map(|expr| {
                        let value = self.eval_resolved_expr(span.clone(), expr)?;
                        Ok((expr.output_type(), value))
                    })
                    .collect::<Result<Vec<_>, Error>>()?;
                let extracted = self.extract_best(roots)?;
                for root in extracted.terms {
                    let root = root.ok_or_else(|| {
                        Error::ExtractError(
                            "Unable to find any valid extraction (likely due to subsume or delete)"
                                .to_string(),
                        )
                    })?;
                    writeln!(f, "{}", extracted.termdag.to_string(root.term))
                        .map_err(|e| Error::IoError(filename.clone(), e, span.clone()))?;
                }

                log::info!("Output to '{filename:?}'.")
            }
            ResolvedNCommand::UserDefined(_span, name, exprs) => {
                let command = self
                    .commands
                    .get(&name)
                    .ok_or_else(|| {
                        NotFoundError(format!("Unrecognized user-defined command: {name}"))
                    })?
                    .clone();
                return command.update(self, &exprs);
            }

            ResolvedNCommand::ProveExists(span, resolved_call) => {
                let mut instrument = ProofInstrumentor::new(self);
                let (proof_store, proof_id) =
                    instrument
                        .prove_exists(&resolved_call)
                        .map_err(|error| Error::ProofError {
                            span: span.clone(),
                            error,
                        })?;
                if let Some(summary) = self.extension_state::<crate::proof_summary::ProofSummary>()
                {
                    summary.certificates(1, self.proof_state.verify_proofs);
                }
                return Ok(vec![CommandOutput::ProveExists {
                    proof_store,
                    proof_id,
                }]);
            }
        };

        Ok(vec![])
    }
}

#[cfg(test)]
mod tests;
