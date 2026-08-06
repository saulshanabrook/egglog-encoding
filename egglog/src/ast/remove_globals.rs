//! Remove global variables from the program by translating
//! them into functions with no arguments.
//! This requires type information, so it is done after type checking.
//! Primitives are translated into functions with a primitive output.
//! When a globally-bound primitive value is used in the actions of a rule,
//! we add a new variable to the query bound to the primitive value.

use crate::*;
use crate::{
    command_origin::{
        CommandOriginAt, CommandOriginDisposition, CommandOriginError, ExactCommandOrigins,
        OriginatedFinalizedProgram,
    },
    core::ResolvedCall,
    frontend_program::{CommandOrigin, GeneratedCommandRole},
    schedule_origin::{
        ExactScheduleOrigins, LocalScheduleOrigins, ScheduleNodeAddress, ScheduleOriginDisposition,
        ScheduleOriginDispositionAt, collect_schedule_addresses,
    },
    typechecking::{CallableIdentity, FinalizedProgram, FuncType, SortAuthorityAt},
    util::{HashMap, HashSet},
};
use egglog_ast::generic_ast::{GenericAction, GenericExpr, GenericFact, GenericRule};

struct GlobalRemover<'a> {
    fresh: &'a mut SymbolGen,
}

/// One command and its producer-authenticated relationship to the exact input
/// node being transformed.  Keeping these fields paired prevents later code
/// from reordering commands independently of their dispositions.
struct ProducedCommand {
    command: ResolvedNCommand,
    disposition: CommandOriginDisposition,
}

impl ProducedCommand {
    fn inherited(command: ResolvedNCommand) -> Self {
        Self {
            command,
            disposition: CommandOriginDisposition::Inherit,
        }
    }

    fn generated(command: ResolvedNCommand) -> Self {
        Self {
            command,
            disposition: CommandOriginDisposition::Generated(
                GeneratedCommandRole::GlobalElimination,
            ),
        }
    }
}

/// One producer-stamped output node, relative to a single input command.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ProducedOriginAt {
    command_path: Vec<usize>,
    input_command_path: Vec<usize>,
    disposition: CommandOriginDisposition,
}

/// Commands and provenance are inseparable throughout global elimination.
struct RemovedCommand {
    commands: Vec<ResolvedNCommand>,
    origins: Vec<ProducedOriginAt>,
    input_paths: Vec<Vec<usize>>,
}

impl RemovedCommand {
    fn leaf(outputs: Vec<ProducedCommand>) -> Self {
        assert!(
            !outputs.is_empty(),
            "global elimination cannot erase an input command"
        );
        let mut commands = Vec::with_capacity(outputs.len());
        let mut origins = Vec::with_capacity(outputs.len());
        for (index, output) in outputs.into_iter().enumerate() {
            commands.push(output.command);
            origins.push(ProducedOriginAt {
                command_path: vec![index],
                input_command_path: Vec::new(),
                disposition: output.disposition,
            });
        }
        let removed = Self {
            commands,
            origins,
            input_paths: vec![Vec::new()],
        };
        removed.validate();
        removed
    }

    fn inherited(command: ResolvedNCommand) -> Self {
        Self::leaf(vec![ProducedCommand::inherited(command)])
    }

    fn fail(span: Span, children: Vec<Self>) -> Self {
        let mut nested = Vec::new();
        let mut origins = vec![ProducedOriginAt {
            command_path: vec![0],
            input_command_path: Vec::new(),
            disposition: CommandOriginDisposition::Inherit,
        }];
        let mut input_paths = vec![Vec::new()];
        for (child_index, child) in children.into_iter().enumerate() {
            let offset = nested.len();
            for mut origin in child.origins {
                let output_child = origin
                    .command_path
                    .first_mut()
                    .expect("validated produced-origin paths are never empty");
                *output_child += offset;
                origin.command_path.insert(0, 0);
                origin.input_command_path.insert(0, child_index);
                origins.push(origin);
            }
            for mut input_path in child.input_paths {
                input_path.insert(0, child_index);
                input_paths.push(input_path);
            }
            nested.extend(child.commands);
        }
        let removed = Self {
            commands: vec![GenericNCommand::Fail(span, nested)],
            origins,
            input_paths,
        };
        removed.validate();
        removed
    }

    fn validate(&self) {
        fn collect_output_paths(
            commands: &[ResolvedNCommand],
            path: &mut Vec<usize>,
            output: &mut Vec<Vec<usize>>,
        ) {
            for (index, command) in commands.iter().enumerate() {
                path.push(index);
                output.push(path.clone());
                if let GenericNCommand::Fail(_, nested) = command {
                    collect_output_paths(nested, path, output);
                }
                path.pop();
            }
        }

        let mut expected_outputs = Vec::new();
        collect_output_paths(&self.commands, &mut Vec::new(), &mut expected_outputs);
        assert_eq!(
            self.origins
                .iter()
                .map(|origin| origin.command_path.clone())
                .collect::<Vec<_>>(),
            expected_outputs,
            "global-elimination origins must cover output commands in recursive preorder"
        );

        let input_paths = self.input_paths.iter().cloned().collect::<HashSet<_>>();
        assert_eq!(
            input_paths.len(),
            self.input_paths.len(),
            "global-elimination input paths must be unique"
        );
        for origin in &self.origins {
            assert!(
                input_paths.contains(&origin.input_command_path),
                "produced command refers to an unknown input command path"
            );
            if let CommandOriginDisposition::Generated(role) = &origin.disposition {
                assert_eq!(
                    role,
                    &GeneratedCommandRole::GlobalElimination,
                    "global elimination emitted an unrelated generated role"
                );
            }
        }
        for input_path in &self.input_paths {
            assert_eq!(
                self.origins
                    .iter()
                    .filter(|origin| {
                        origin.input_command_path == *input_path
                            && origin.disposition == CommandOriginDisposition::Inherit
                    })
                    .count(),
                1,
                "every global-elimination input node must have exactly one inherited output"
            );
        }
    }
}

struct RemovedProgram {
    finalized: FinalizedProgram,
    origins: Vec<ProducedOriginAt>,
}

/// Removes all globals from a program.
/// No top level lets are allowed after this pass,
/// nor any variable that references a global.
/// Adds new functions for global variables
/// and replaces references to globals with
/// references to the new functions.
/// e.g.
/// ```ignore
/// (let x 3)
/// (Add x x)
/// ```
/// becomes
/// ```ignore
/// (function x () i64)
/// (set (x) 3)
/// (Add (x) (x))
/// ```
///
/// If later, this global is referenced in a rule:
/// ```ignore
/// (rule ((Neg y))
///       ((Add x x)))
/// ```
/// We instrument the query to make the value available:
/// ```ignore
/// (rule ((Neg y)
///        (= fresh_var_for_x (x)))
///       ((Add fresh_var_for_x fresh_var_for_x)))
/// ```
// Kept as the source-compatible entry point for callers that do not carry the
// private finalized-program authority sidecar.
#[allow(dead_code)]
pub(crate) fn remove_globals(
    prog: Vec<ResolvedNCommand>,
    fresh: &mut SymbolGen,
) -> Vec<ResolvedNCommand> {
    let mut remover = GlobalRemover { fresh };
    prog.into_iter()
        .flat_map(|cmd| remover.remove_globals_cmd(cmd))
        .collect()
}

/// Remove globals while explicitly remapping the private sort-authority
/// sidecar through every command expansion and nested `Fail` flattening.
pub(crate) fn remove_globals_with_sort_authority(
    program: FinalizedProgram,
    fresh: &mut SymbolGen,
) -> FinalizedProgram {
    remove_globals_with_productions(program, fresh).finalized
}

fn remove_globals_with_productions(
    program: FinalizedProgram,
    fresh: &mut SymbolGen,
) -> RemovedProgram {
    program.validate_sort_authority_shape();
    let mut authorities_by_command = (0..program.commands.len())
        .map(|_| Vec::new())
        .collect::<Vec<Vec<SortAuthorityAt>>>();
    for mut authority in program.sort_authorities {
        let top = authority
            .command_path
            .first()
            .copied()
            .expect("sort authority paths are never empty");
        authority.command_path.remove(0);
        authorities_by_command
            .get_mut(top)
            .expect("validated sort authority had an out-of-range top-level path")
            .push(authority);
    }

    let mut remover = GlobalRemover { fresh };
    let mut commands = Vec::new();
    let mut sort_authorities = Vec::new();
    let mut origins = Vec::new();
    for (input_index, (command, authorities)) in program
        .commands
        .into_iter()
        .zip(authorities_by_command)
        .enumerate()
    {
        let offset = commands.len();
        let mut produced = remover.remove_globals_cmd_produced(command);
        for mut authority in authorities {
            let inherited = produced
                .origins
                .iter()
                .find(|origin| {
                    origin.input_command_path == authority.command_path
                        && origin.disposition == CommandOriginDisposition::Inherit
                })
                .expect("every input Sort has exactly one inherited produced command");
            authority.command_path = inherited.command_path.clone();
            let top = authority
                .command_path
                .first_mut()
                .expect("remapped sort authority paths are never empty");
            *top += offset;
            sort_authorities.push(authority);
        }
        for origin in &mut produced.origins {
            let top = origin
                .command_path
                .first_mut()
                .expect("produced command-origin paths are never empty");
            *top += offset;
            origin.input_command_path.insert(0, input_index);
        }
        commands.extend(produced.commands);
        origins.extend(produced.origins);
    }
    RemovedProgram {
        finalized: FinalizedProgram::new(commands, sort_authorities),
        origins,
    }
}

/// Remove globals without ever detaching the finalized commands from either
/// exact frontend authority sidecar.
///
/// The entire forest is preflighted before a `GlobalRemover` exists.  Fresh
/// allocation then runs against a staged generator and commits only after the
/// output commands, origins, and sort authorities validate together.
#[allow(dead_code)] // integrated by the pending compile-only source pipeline
pub(crate) fn remove_globals_originated(
    program: OriginatedFinalizedProgram,
    fresh: &mut SymbolGen,
) -> Result<OriginatedFinalizedProgram, RemoveGlobalsOriginError> {
    program.validate()?;
    preflight_global_elimination_origins(program.commands(), program.origins())?;

    let mut staged_fresh = fresh.clone();
    let transformed = program.try_transform(
        |finalized,
         incoming_origins,
         incoming_schedule_origins|
         -> Result<_, RemoveGlobalsOriginError> {
            let removed = remove_globals_with_productions(finalized, &mut staged_fresh);
            let origins = materialize_global_elimination_origins(
                &removed.finalized.commands,
                &removed.origins,
                &incoming_origins,
            )?;
            let schedule_origins = materialize_global_elimination_schedule_origins(
                &removed.finalized.commands,
                &removed.origins,
                &incoming_origins,
                &incoming_schedule_origins,
                &origins,
            )?;
            Ok((removed.finalized, origins, schedule_origins))
        },
    )?;
    *fresh = staged_fresh;
    Ok(transformed)
}

#[derive(Debug, thiserror::Error)]
pub(crate) enum RemoveGlobalsOriginError {
    #[error(transparent)]
    Origin(#[from] CommandOriginError),
}

fn source_trigger(origin: &CommandOrigin) -> Option<crate::frontend_program::SourceSubcommandRef> {
    match origin {
        CommandOrigin::Source(source) => Some(*source),
        CommandOrigin::Generated { trigger, .. } => *trigger,
    }
}

fn is_global_elimination_fanout(command: &ResolvedNCommand) -> bool {
    matches!(
        command,
        GenericNCommand::CoreAction(GenericAction::Let(..)) | GenericNCommand::LetBegin(..)
    )
}

fn preflight_global_elimination_origins(
    commands: &[ResolvedNCommand],
    origins: &ExactCommandOrigins,
) -> Result<(), CommandOriginError> {
    fn visit_level<'a>(
        commands: &[ResolvedNCommand],
        origins: &mut std::slice::Iter<'a, CommandOriginAt>,
        input_path: &mut Vec<usize>,
    ) -> Result<(), CommandOriginError> {
        for (index, command) in commands.iter().enumerate() {
            input_path.push(index);
            let incoming = origins
                .next()
                .ok_or_else(|| CommandOriginError::MissingPath {
                    command_path: input_path.clone(),
                })?;
            if is_global_elimination_fanout(command) {
                source_trigger(&incoming.origin).ok_or_else(|| {
                    CommandOriginError::GeneratedWithoutTrigger {
                        command_path: input_path.clone(),
                        role: GeneratedCommandRole::GlobalElimination,
                    }
                })?;
            }
            if let GenericNCommand::Fail(_, nested) = command {
                visit_level(nested, origins, input_path)?;
            }
            input_path.pop();
        }
        Ok(())
    }

    origins.validate(commands)?;
    let mut incoming = origins.as_slice().iter();
    visit_level(commands, &mut incoming, &mut Vec::new())?;
    debug_assert!(incoming.next().is_none(), "validated origins are total");
    Ok(())
}

fn materialize_global_elimination_origins(
    commands: &[ResolvedNCommand],
    produced: &[ProducedOriginAt],
    incoming: &ExactCommandOrigins,
) -> Result<ExactCommandOrigins, CommandOriginError> {
    let incoming = incoming
        .as_slice()
        .iter()
        .map(|origin| (origin.command_path.clone(), origin.origin.clone()))
        .collect::<HashMap<_, _>>();
    let origins = produced
        .iter()
        .map(|produced| {
            let incoming = incoming.get(&produced.input_command_path).ok_or_else(|| {
                CommandOriginError::MissingPath {
                    command_path: produced.input_command_path.clone(),
                }
            })?;
            let origin = match &produced.disposition {
                CommandOriginDisposition::Inherit => incoming.clone(),
                CommandOriginDisposition::Generated(role) => CommandOrigin::Generated {
                    trigger: Some(source_trigger(incoming).ok_or_else(|| {
                        CommandOriginError::GeneratedWithoutTrigger {
                            command_path: produced.command_path.clone(),
                            role: role.clone(),
                        }
                    })?),
                    role: role.clone(),
                },
            };
            Ok(CommandOriginAt {
                command_path: produced.command_path.clone(),
                origin,
            })
        })
        .collect::<Result<Vec<_>, CommandOriginError>>()?;
    ExactCommandOrigins::try_new(commands, origins)
}

fn materialize_global_elimination_schedule_origins(
    commands: &[ResolvedNCommand],
    produced: &[ProducedOriginAt],
    incoming_command_origins: &ExactCommandOrigins,
    incoming_schedule_origins: &ExactScheduleOrigins,
    output_command_origins: &ExactCommandOrigins,
) -> Result<ExactScheduleOrigins, CommandOriginError> {
    let produced_by_output = produced
        .iter()
        .map(|origin| (origin.command_path.clone(), origin))
        .collect::<HashMap<_, _>>();
    let entries = collect_schedule_addresses(commands)
        .into_iter()
        .map(|address| {
            let produced = produced_by_output
                .get(&address.command_path)
                .ok_or_else(|| CommandOriginError::MissingPath {
                    command_path: address.command_path.clone(),
                })?;
            if !matches!(produced.disposition, CommandOriginDisposition::Inherit) {
                return Err(
                    crate::schedule_origin::ScheduleOriginError::GeneratedGlobalSchedule {
                        command_path: address.command_path.clone(),
                    }
                    .into(),
                );
            }
            Ok(ScheduleOriginDispositionAt {
                disposition: ScheduleOriginDisposition::Inherit {
                    input: ScheduleNodeAddress {
                        command_path: produced.input_command_path.clone(),
                        schedule_path: address.schedule_path.clone(),
                    },
                },
                address,
            })
        })
        .collect::<Result<Vec<_>, CommandOriginError>>()?;
    let local = LocalScheduleOrigins::try_new(commands, entries)?;
    local
        .compose(
            incoming_command_origins,
            incoming_schedule_origins,
            commands,
            output_command_origins,
        )
        .map_err(CommandOriginError::from)
}

fn resolved_var_to_call(var: &ResolvedVar) -> ResolvedCall {
    let ResolvedVarBinding::Global { function } = var.binding else {
        panic!("global variable has no nominal function authority: {var:?}");
    };
    ResolvedCall::Func(FuncType {
        identity: CallableIdentity::Function(function),
        name: var.name.clone(),
        subtype: FunctionSubtype::Custom,
        input: vec![],
        outputs: vec![var.sort.clone()],
    })
}

/// TODO (yz) it would be better to implement replace_global_var
/// as a function from ResolvedVar to ResolvedExpr
/// and use it as an argument to `subst` instead of `visit_expr`,
/// but we have not implemented `subst` for command.
fn replace_global_vars(expr: ResolvedExpr) -> ResolvedExpr {
    match expr.get_global_var() {
        Some(resolved_var) => {
            GenericExpr::Call(expr.span(), resolved_var_to_call(&resolved_var), vec![])
        }
        None => expr,
    }
}

pub(crate) fn remove_globals_expr(expr: ResolvedExpr) -> ResolvedExpr {
    expr.visit_exprs(&mut replace_global_vars)
}

fn remove_globals_action(action: ResolvedAction) -> ResolvedAction {
    action.visit_exprs(&mut replace_global_vars)
}

impl GlobalRemover<'_> {
    fn remove_globals_cmd(&mut self, cmd: ResolvedNCommand) -> Vec<ResolvedNCommand> {
        self.remove_globals_cmd_produced(cmd).commands
    }

    fn remove_globals_cmd_produced(&mut self, cmd: ResolvedNCommand) -> RemovedCommand {
        match cmd {
            GenericNCommand::CoreAction(action) => match action {
                GenericAction::Let(span, name, expr) => {
                    let ty = expr.output_type();

                    let ResolvedVarBinding::Global { function } = name.binding else {
                        panic!("global let has no nominal function authority: {name:?}");
                    };

                    let resolved_call = ResolvedCall::Func(FuncType {
                        identity: CallableIdentity::Function(function),
                        name: name.name.clone(),
                        subtype: FunctionSubtype::Custom,
                        input: vec![],
                        outputs: vec![ty.clone()],
                    });
                    let func_decl = ResolvedFunctionDecl {
                        name: name.name,
                        subtype: FunctionSubtype::Custom,
                        schema: Schema {
                            input: vec![],
                            outputs: vec![ty.name().to_owned()],
                        },
                        resolved_schema: resolved_call.clone(),
                        merge: None,
                        cost: None,
                        unextractable: true,
                        internal_hidden: false,
                        internal_let: true,
                        span: span.clone(),
                        term_constructor: None,
                        identity_vals: None,
                        internal_term_node: false,
                    };
                    RemovedCommand::leaf(vec![
                        ProducedCommand::generated(GenericNCommand::Function(func_decl)),
                        ProducedCommand::inherited(GenericNCommand::CoreAction(
                            GenericAction::Set(
                                span,
                                resolved_call,
                                vec![],
                                remove_globals_expr(expr),
                            ),
                        )),
                    ])
                }
                _ => RemovedCommand::inherited(GenericNCommand::CoreAction(remove_globals_action(
                    action,
                ))),
            },
            // Rewrite global references but leave the block's own `let`s local.
            GenericNCommand::CoreActions(actions) => RemovedCommand::inherited(
                GenericNCommand::CoreActions(actions.visit_actions(&mut remove_globals_action)),
            ),
            // Declare `a` as a global function, then run the block, ending by
            // setting the function to the block's trailing value.
            GenericNCommand::LetBegin(span, name, actions) => {
                let mut acts = actions.0;
                let value = match acts.pop() {
                    Some(GenericAction::Expr(_, e)) => e,
                    _ => panic!("`(let _ (begin ...))` must end with an expression"),
                };
                let ty = value.output_type();
                let ResolvedVarBinding::Global { function } = name.binding else {
                    panic!("global begin-let has no nominal function authority: {name:?}");
                };
                let resolved_call = ResolvedCall::Func(FuncType {
                    identity: CallableIdentity::Function(function),
                    name: name.name.clone(),
                    subtype: FunctionSubtype::Custom,
                    input: vec![],
                    outputs: vec![ty.clone()],
                });
                let func_decl = ResolvedFunctionDecl {
                    name: name.name,
                    subtype: FunctionSubtype::Custom,
                    schema: Schema {
                        input: vec![],
                        outputs: vec![ty.name().to_owned()],
                    },
                    resolved_schema: resolved_call.clone(),
                    merge: None,
                    cost: None,
                    unextractable: true,
                    internal_hidden: false,
                    internal_let: true,
                    span: span.clone(),
                    term_constructor: None,
                    identity_vals: None,
                    internal_term_node: false,
                };
                let mut new_acts: Vec<_> = acts.into_iter().map(remove_globals_action).collect();
                new_acts.push(GenericAction::Set(
                    span,
                    resolved_call,
                    vec![],
                    remove_globals_expr(value),
                ));
                RemovedCommand::leaf(vec![
                    ProducedCommand::generated(GenericNCommand::Function(func_decl)),
                    ProducedCommand::inherited(GenericNCommand::CoreActions(GenericActions(
                        new_acts,
                    ))),
                ])
            }
            GenericNCommand::NormRule { rule } => {
                // A map from the global variables in actions to their new names
                // in the query.
                let mut globals = IndexMap::default();
                rule.head.clone().visit_exprs(&mut |expr| {
                    if let Some(resolved_var) = expr.get_global_var()
                        && !globals.contains_key(&resolved_var)
                    {
                        let new_name = self.fresh.fresh(&resolved_var.name);
                        globals.insert(
                            resolved_var.clone(),
                            GenericExpr::Var(
                                expr.span(),
                                ResolvedVar {
                                    name: new_name,
                                    sort: resolved_var.sort.clone(),
                                    binding: ResolvedVarBinding::Lexical {
                                        id: self.fresh.fresh_resolved_binding_id(),
                                    },
                                    is_global_ref: false,
                                },
                            ),
                        );
                    }
                    expr
                });
                let new_facts: Vec<ResolvedFact> = globals
                    .iter()
                    .map(|(old, new)| {
                        GenericFact::Eq(
                            new.span(),
                            GenericExpr::Call(new.span(), resolved_var_to_call(old), vec![]),
                            new.clone(),
                        )
                    })
                    .collect();

                let new_rule = GenericRule {
                    span: rule.span,
                    // instrument the old facts and add the new facts to the end
                    body: rule
                        .body
                        .iter()
                        .map(|fact| fact.clone().visit_exprs(&mut replace_global_vars))
                        .chain(new_facts)
                        .collect(),
                    // replace references to globals with the newly bound names
                    head: rule.head.clone().visit_exprs(&mut |expr| {
                        if let Some(resolved_var) = expr.get_global_var() {
                            globals.get(&resolved_var).unwrap().clone()
                        } else {
                            expr
                        }
                    }),
                    name: rule.name.clone(),
                    ruleset: rule.ruleset.clone(),
                    eval_mode: rule.eval_mode,
                    no_decomp: rule.no_decomp,
                    include_subsumed: rule.include_subsumed,
                };
                RemovedCommand::inherited(GenericNCommand::NormRule { rule: new_rule })
            }
            // Handle the corner case where a global command is wrapped in (fail).
            // Remove globals from every wrapped command and keep the whole flattened
            // result inside the `fail`.
            GenericNCommand::Fail(span, cmds) => {
                let removed = cmds
                    .into_iter()
                    .map(|cmd| self.remove_globals_cmd_produced(cmd))
                    .collect();
                RemovedCommand::fail(span, removed)
            }
            _ => RemovedCommand::inherited(cmd.visit_exprs(&mut replace_global_vars)),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::desugar::{desugar_command, desugar_command_with_origin};
    use crate::command_origin::{CommandOriginAt, ExactCommandOrigins, OriginatedProgram};
    use crate::frontend_program::{SourceGroupId, SourceSubcommandId, SourceSubcommandRef};
    use crate::schedule_origin::ExactScheduleOrigins;
    use crate::typechecking::SourceSortAuthorityAt;

    use super::*;

    fn source(group: u32, subcommand: u32) -> SourceSubcommandRef {
        SourceSubcommandRef::new(
            SourceGroupId::new(group),
            SourceSubcommandId::new(subcommand),
        )
    }

    fn resolve_one_originated(
        source_text: &str,
        incoming: CommandOrigin,
    ) -> (EGraph, OriginatedFinalizedProgram) {
        let mut egraph = EGraph::new_compile_only(false);
        let parsed = egraph.parse_program(None, source_text).unwrap();
        let [command] = parsed.as_slice() else {
            panic!("expected one parsed command: {parsed:?}")
        };
        let originated =
            desugar_command_with_origin(command.clone(), &mut egraph.parser, false, &incoming)
                .unwrap();
        let finalized = egraph
            .typecheck_originated_program_with_sort_authority(originated, Vec::new())
            .unwrap();
        (egraph, finalized)
    }

    fn resolve_one_detached(egraph: &mut EGraph, source_text: &str) -> FinalizedProgram {
        let parsed = egraph.parse_program(None, source_text).unwrap();
        let [command] = parsed.as_slice() else {
            panic!("expected one parsed command: {parsed:?}")
        };
        let commands = desugar_command(command.clone(), &mut egraph.parser, false).unwrap();
        egraph
            .typecheck_program_with_sort_authority(&commands, Vec::new())
            .unwrap()
    }

    fn resolve_program_originated(
        egraph: &mut EGraph,
        source_text: &str,
    ) -> OriginatedFinalizedProgram {
        let parsed = egraph.parse_program(None, source_text).unwrap();
        let mut commands = Vec::new();
        let mut origin_entries = Vec::new();
        let mut schedule_origin_entries = Vec::new();
        for (source_index, command) in parsed.into_iter().enumerate() {
            let originated = desugar_command_with_origin(
                command,
                &mut egraph.parser,
                false,
                &CommandOrigin::Source(source(0, source_index as u32)),
            )
            .unwrap();
            let offset = commands.len();
            commands.extend_from_slice(originated.commands());
            origin_entries.extend(originated.origins().as_slice().iter().cloned().map(
                |mut entry| {
                    *entry
                        .command_path
                        .first_mut()
                        .expect("desugared origin paths are never empty") += offset;
                    entry
                },
            ));
            schedule_origin_entries.extend(
                originated
                    .schedule_origins()
                    .as_slice()
                    .iter()
                    .cloned()
                    .map(|mut entry| {
                        *entry
                            .address
                            .command_path
                            .first_mut()
                            .expect("desugared schedule-origin paths are never empty") += offset;
                        entry
                    }),
            );
        }
        let origins = ExactCommandOrigins::try_new(&commands, origin_entries).unwrap();
        let schedule_origins =
            ExactScheduleOrigins::try_new(&commands, &origins, schedule_origin_entries).unwrap();
        let originated = OriginatedProgram::try_new(commands, origins, schedule_origins).unwrap();
        egraph
            .typecheck_originated_program_with_sort_authority(originated, Vec::new())
            .unwrap()
    }

    fn resolve_program_detached(egraph: &mut EGraph, source_text: &str) -> FinalizedProgram {
        let parsed = egraph.parse_program(None, source_text).unwrap();
        let mut commands = Vec::new();
        for command in parsed {
            commands.extend(desugar_command(command, &mut egraph.parser, false).unwrap());
        }
        egraph
            .typecheck_program_with_sort_authority(&commands, Vec::new())
            .unwrap()
    }

    fn origin_pattern(program: &OriginatedFinalizedProgram) -> Vec<(Vec<usize>, CommandOrigin)> {
        program
            .origins()
            .as_slice()
            .iter()
            .map(|entry| (entry.command_path.clone(), entry.origin.clone()))
            .collect()
    }

    #[test]
    fn global_elimination_maps_let_and_let_begin_exactly() {
        let trigger = source(4, 2);
        let (mut egraph, let_program) =
            resolve_one_originated("(let x 1)", CommandOrigin::Source(trigger));
        let removed =
            remove_globals_originated(let_program, &mut egraph.parser.symbol_gen).unwrap();
        assert!(matches!(
            removed.commands(),
            [
                GenericNCommand::Function(_),
                GenericNCommand::CoreAction(GenericAction::Set(..))
            ]
        ));
        assert_eq!(
            origin_pattern(&removed),
            vec![
                (
                    vec![0],
                    CommandOrigin::Generated {
                        trigger: Some(trigger),
                        role: GeneratedCommandRole::GlobalElimination,
                    },
                ),
                (vec![1], CommandOrigin::Source(trigger)),
            ]
        );

        let (mut egraph, begin_program) = resolve_one_originated(
            "(let doubled (begin (let y 2) (+ y y)))",
            CommandOrigin::Source(trigger),
        );
        let removed =
            remove_globals_originated(begin_program, &mut egraph.parser.symbol_gen).unwrap();
        assert!(matches!(
            removed.commands(),
            [
                GenericNCommand::Function(_),
                GenericNCommand::CoreActions(_)
            ]
        ));
        assert_eq!(
            origin_pattern(&removed),
            vec![
                (
                    vec![0],
                    CommandOrigin::Generated {
                        trigger: Some(trigger),
                        role: GeneratedCommandRole::GlobalElimination,
                    },
                ),
                (vec![1], CommandOrigin::Source(trigger)),
            ]
        );
    }

    #[test]
    fn global_elimination_production_pairs_each_command_with_its_disposition() {
        let mut egraph = EGraph::new_compile_only(false);
        let finalized = resolve_one_detached(&mut egraph, "(let x 1)");
        let [command] = finalized.commands.as_slice() else {
            panic!("expected one resolved let: {:?}", finalized.commands)
        };
        let mut fresh = egraph.parser.symbol_gen.clone();
        let produced =
            GlobalRemover { fresh: &mut fresh }.remove_globals_cmd_produced(command.clone());
        assert_eq!(produced.commands.len(), produced.origins.len());
        assert!(matches!(
            (&produced.commands[0], &produced.origins[0].disposition),
            (
                GenericNCommand::Function(_),
                CommandOriginDisposition::Generated(GeneratedCommandRole::GlobalElimination)
            )
        ));
        assert!(matches!(
            (&produced.commands[1], &produced.origins[1].disposition),
            (
                GenericNCommand::CoreAction(GenericAction::Set(..)),
                CommandOriginDisposition::Inherit
            )
        ));
    }

    #[test]
    fn global_elimination_inherit_preserves_generated_role_and_internal_let_is_not_inferred() {
        let trigger = source(2, 8);
        let incoming = CommandOrigin::Generated {
            trigger: Some(trigger),
            role: GeneratedCommandRole::TermEncoding,
        };
        let (mut egraph, program) = resolve_one_originated("(let x 1)", incoming.clone());
        let once = remove_globals_originated(program, &mut egraph.parser.symbol_gen).unwrap();
        assert_eq!(
            origin_pattern(&once),
            vec![
                (
                    vec![0],
                    CommandOrigin::Generated {
                        trigger: Some(trigger),
                        role: GeneratedCommandRole::GlobalElimination,
                    },
                ),
                (vec![1], incoming),
            ]
        );
        let [GenericNCommand::Function(function), _] = once.commands() else {
            panic!("expected generated function and set: {:?}", once.commands())
        };
        assert!(function.internal_let);

        let commands_before = once.commands().to_vec();
        let origins_before = origin_pattern(&once);
        let twice = remove_globals_originated(once, &mut egraph.parser.symbol_gen).unwrap();
        assert_eq!(twice.commands(), commands_before);
        assert_eq!(origin_pattern(&twice), origins_before);
        assert_eq!(twice.commands().len(), 2);
    }

    #[test]
    fn global_elimination_nested_fail_uses_each_exact_child_origin_and_offset() {
        let trigger = source(6, 1);
        let mut egraph = EGraph::new_compile_only(false);
        let parsed = egraph
            .parse_program(
                None,
                "(fail (let x 1) (sort S) (fail (let y (begin (let z 2) (+ z z))) (check (= 1 1))))",
            )
            .unwrap();
        let [command] = parsed.as_slice() else {
            panic!("expected one Fail command: {parsed:?}")
        };
        let commands = desugar_command(command.clone(), &mut egraph.parser, false).unwrap();
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
                CommandOriginAt {
                    command_path: vec![0, 2],
                    origin: CommandOrigin::Generated {
                        trigger: Some(trigger),
                        role: GeneratedCommandRole::MacroExpansion,
                    },
                },
                CommandOriginAt {
                    command_path: vec![0, 2, 0],
                    origin: CommandOrigin::Generated {
                        trigger: Some(trigger),
                        role: GeneratedCommandRole::ProofMaintenance,
                    },
                },
                CommandOriginAt {
                    command_path: vec![0, 2, 1],
                    origin: CommandOrigin::Source(trigger),
                },
            ],
        )
        .unwrap();
        let schedule_origins =
            ExactScheduleOrigins::try_new(&commands, &origins, Vec::new()).unwrap();
        let program = OriginatedProgram::try_new(commands, origins, schedule_origins).unwrap();
        let finalized = egraph
            .typecheck_originated_program_with_sort_authority(program, Vec::new())
            .unwrap();
        let sort_before = finalized.sort_authorities()[0].clone();
        assert_eq!(sort_before.command_path, [0, 1]);

        let removed = remove_globals_originated(finalized, &mut egraph.parser.symbol_gen).unwrap();
        let expected = vec![
            (vec![0], CommandOrigin::Source(trigger)),
            (
                vec![0, 0],
                CommandOrigin::Generated {
                    trigger: Some(trigger),
                    role: GeneratedCommandRole::GlobalElimination,
                },
            ),
            (
                vec![0, 1],
                CommandOrigin::Generated {
                    trigger: Some(trigger),
                    role: GeneratedCommandRole::TermEncoding,
                },
            ),
            (
                vec![0, 2],
                CommandOrigin::Generated {
                    trigger: Some(trigger),
                    role: GeneratedCommandRole::ProofInstrumentation,
                },
            ),
            (
                vec![0, 3],
                CommandOrigin::Generated {
                    trigger: Some(trigger),
                    role: GeneratedCommandRole::MacroExpansion,
                },
            ),
            (
                vec![0, 3, 0],
                CommandOrigin::Generated {
                    trigger: Some(trigger),
                    role: GeneratedCommandRole::GlobalElimination,
                },
            ),
            (
                vec![0, 3, 1],
                CommandOrigin::Generated {
                    trigger: Some(trigger),
                    role: GeneratedCommandRole::ProofMaintenance,
                },
            ),
            (vec![0, 3, 2], CommandOrigin::Source(trigger)),
        ];
        assert_eq!(origin_pattern(&removed), expected);
        assert_eq!(removed.sort_authorities().len(), 1);
        assert_eq!(removed.sort_authorities()[0].command_path, [0, 2]);
        assert_eq!(removed.sort_authorities()[0].local, sort_before.local);
        assert_eq!(removed.sort_authorities()[0].source, sort_before.source);
    }

    #[test]
    fn global_elimination_preserves_cross_view_source_sort_authority_when_rebasing() {
        let trigger = source(7, 3);
        let mut egraph = EGraph::new_compile_only(true);
        let source_registration = {
            let original = egraph
                .proof_state
                .original_typechecking
                .as_deref_mut()
                .unwrap();
            let parsed = original.parse_program(None, "(sort Source)").unwrap();
            let [command] = parsed.as_slice() else {
                panic!("expected one source Sort: {parsed:?}")
            };
            let commands = desugar_command(command.clone(), &mut original.parser, false).unwrap();
            original
                .typecheck_program_with_sort_authority(&commands, Vec::new())
                .unwrap()
                .sort_authorities[0]
                .local
        };

        let parsed = egraph
            .parse_program(None, "(fail (let x 1) (sort Local))")
            .unwrap();
        let [command] = parsed.as_slice() else {
            panic!("expected one execution Fail: {parsed:?}")
        };
        let originated = desugar_command_with_origin(
            command.clone(),
            &mut egraph.parser,
            false,
            &CommandOrigin::Source(trigger),
        )
        .unwrap();
        let finalized = egraph
            .typecheck_originated_program_with_sort_authority(
                originated,
                vec![SourceSortAuthorityAt {
                    command_path: vec![0, 1],
                    source: source_registration,
                }],
            )
            .unwrap();
        let sort_before = finalized.sort_authorities()[0].clone();
        assert_eq!(sort_before.command_path, [0, 1]);
        assert_eq!(sort_before.source, Some(source_registration));
        let execution_links_before = egraph.type_info.linked_sort_arc_count();
        let proof_links_before = egraph
            .proof_state
            .original_typechecking
            .as_deref()
            .unwrap()
            .type_info
            .linked_sort_arc_count();

        let removed = remove_globals_originated(finalized, &mut egraph.parser.symbol_gen).unwrap();
        assert_eq!(removed.sort_authorities().len(), 1);
        assert_eq!(removed.sort_authorities()[0].command_path, [0, 2]);
        assert_eq!(removed.sort_authorities()[0].local, sort_before.local);
        assert_eq!(
            removed.sort_authorities()[0].source,
            Some(source_registration)
        );
        assert_eq!(
            egraph.type_info.linked_sort_arc_count(),
            execution_links_before
        );
        assert_eq!(
            egraph
                .proof_state
                .original_typechecking
                .as_deref()
                .unwrap()
                .type_info
                .linked_sort_arc_count(),
            proof_links_before
        );
    }

    #[test]
    fn source_less_global_fanout_fails_before_fresh_but_one_to_one_succeeds() {
        let source_less = CommandOrigin::Generated {
            trigger: None,
            role: GeneratedCommandRole::ProofHeader,
        };
        let (mut egraph, program) = resolve_one_originated("(let x 1)", source_less.clone());
        let fresh_before = egraph.parser.symbol_gen.clone();
        assert!(matches!(
            remove_globals_originated(program, &mut egraph.parser.symbol_gen),
            Err(RemoveGlobalsOriginError::Origin(
                CommandOriginError::GeneratedWithoutTrigger {
                    command_path,
                    role: GeneratedCommandRole::GlobalElimination,
                }
            )) if command_path == [0]
        ));
        assert_eq!(egraph.parser.symbol_gen, fresh_before);

        let (mut egraph, program) = resolve_one_originated("(sort S)", source_less.clone());
        let removed = remove_globals_originated(program, &mut egraph.parser.symbol_gen).unwrap();
        assert_eq!(origin_pattern(&removed), vec![(vec![0], source_less)]);
    }

    #[test]
    fn originated_global_elimination_matches_legacy_output_and_fresh_state() {
        let source_text = "(let doubled (begin (let y 2) (+ y y)))";
        let trigger = source(1, 0);
        let (mut originated_egraph, originated) =
            resolve_one_originated(source_text, CommandOrigin::Source(trigger));
        let mut detached_egraph = EGraph::new_compile_only(false);
        let detached = resolve_one_detached(&mut detached_egraph, source_text);
        assert_eq!(
            originated_egraph.parser.symbol_gen,
            detached_egraph.parser.symbol_gen
        );

        let originated =
            remove_globals_originated(originated, &mut originated_egraph.parser.symbol_gen)
                .unwrap();
        let detached =
            remove_globals_with_sort_authority(detached, &mut detached_egraph.parser.symbol_gen);
        assert_eq!(originated.commands(), detached.commands);
        assert_eq!(originated.sort_authorities(), detached.sort_authorities);
        assert_eq!(
            originated_egraph.parser.symbol_gen,
            detached_egraph.parser.symbol_gen
        );
    }

    #[test]
    fn originated_rule_head_global_matches_legacy_and_advances_fresh_identically() {
        let source_text = r#"
            (relation Seen (i64))
            (let g 7)
            (rule ((Seen x)) ((Seen g)) :name "with_global")
        "#;
        let mut originated_egraph = EGraph::new_compile_only(false);
        let originated = resolve_program_originated(&mut originated_egraph, source_text);
        let mut detached_egraph = EGraph::new_compile_only(false);
        let detached = resolve_program_detached(&mut detached_egraph, source_text);
        assert_eq!(
            originated_egraph.parser.symbol_gen,
            detached_egraph.parser.symbol_gen
        );
        let fresh_before = originated_egraph.parser.symbol_gen.clone();

        let originated =
            remove_globals_originated(originated, &mut originated_egraph.parser.symbol_gen)
                .unwrap();
        let detached =
            remove_globals_with_sort_authority(detached, &mut detached_egraph.parser.symbol_gen);
        assert_eq!(originated.commands(), detached.commands);
        assert_eq!(originated.sort_authorities(), detached.sort_authorities);
        assert_ne!(originated_egraph.parser.symbol_gen, fresh_before);
        assert_eq!(
            originated_egraph.parser.symbol_gen,
            detached_egraph.parser.symbol_gen
        );
    }

    #[test]
    fn global_elimination_rejects_nested_source_less_fanout_before_fresh() {
        let source_less = CommandOrigin::Generated {
            trigger: None,
            role: GeneratedCommandRole::FrontendPrelude,
        };
        let (mut egraph, program) = resolve_one_originated("(fail (let x 1))", source_less);
        let fresh_before = egraph.parser.symbol_gen.clone();
        assert!(matches!(
            remove_globals_originated(program, &mut egraph.parser.symbol_gen),
            Err(RemoveGlobalsOriginError::Origin(
                CommandOriginError::GeneratedWithoutTrigger {
                    command_path,
                    role: GeneratedCommandRole::GlobalElimination,
                }
            )) if command_path == [0, 0]
        ));
        assert_eq!(egraph.parser.symbol_gen, fresh_before);
    }

    #[test]
    fn global_elimination_rebases_only_current_schedule_command_paths() {
        let mut egraph = EGraph::new_compile_only(false);
        let program = resolve_program_originated(&mut egraph, "(let x 1)\n(run 0)");
        let before = program.schedule_origins().as_slice();
        assert!(!before.is_empty());
        assert!(before.iter().all(|entry| entry.address.command_path == [1]));
        assert!(before.iter().all(|entry| matches!(
            &entry.origin,
            crate::schedule_origin::ScheduleNodeOrigin::Source { source_site, .. }
                if source_site.command_path == [0]
        )));
        let before_len = before.len();

        let removed = remove_globals_originated(program, &mut egraph.parser.symbol_gen).unwrap();
        let after = removed.schedule_origins().as_slice();
        assert_eq!(after.len(), before_len);
        assert!(after.iter().all(|entry| entry.address.command_path == [2]));
        assert!(after.iter().all(|entry| matches!(
            &entry.origin,
            crate::schedule_origin::ScheduleNodeOrigin::Source { source_site, .. }
                if source_site.command_path == [0]
        )));
    }
}
