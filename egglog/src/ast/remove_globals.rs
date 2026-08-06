//! Remove global variables from the program by translating
//! them into functions with no arguments.
//! This requires type information, so it is done after type checking.
//! Primitives are translated into functions with a primitive output.
//! When a globally-bound primitive value is used in the actions of a rule,
//! we add a new variable to the query bound to the primitive value.

use crate::*;
use crate::{
    core::ResolvedCall,
    typechecking::{CallableIdentity, FinalizedProgram, FuncType, SortAuthorityAt},
};
use egglog_ast::generic_ast::{GenericAction, GenericExpr, GenericFact, GenericRule};

struct GlobalRemover<'a> {
    fresh: &'a mut SymbolGen,
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
    for (command, authorities) in program.commands.into_iter().zip(authorities_by_command) {
        let offset = commands.len();
        let (produced, mut produced_authorities) =
            remover.remove_globals_cmd_with_sort_authority(command, authorities);
        for authority in &mut produced_authorities {
            let top = authority
                .command_path
                .first_mut()
                .expect("remapped sort authority paths are never empty");
            *top += offset;
        }
        commands.extend(produced);
        sort_authorities.extend(produced_authorities);
    }
    FinalizedProgram::new(commands, sort_authorities)
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
    fn remove_globals_cmd_with_sort_authority(
        &mut self,
        cmd: ResolvedNCommand,
        authorities: Vec<SortAuthorityAt>,
    ) -> (Vec<ResolvedNCommand>, Vec<SortAuthorityAt>) {
        if let GenericNCommand::Fail(span, commands) = cmd {
            let mut authorities_by_child = (0..commands.len())
                .map(|_| Vec::new())
                .collect::<Vec<Vec<SortAuthorityAt>>>();
            for mut authority in authorities {
                let child = authority
                    .command_path
                    .first()
                    .copied()
                    .expect("a Fail descendant sort authority omitted its child path");
                authority.command_path.remove(0);
                authorities_by_child
                    .get_mut(child)
                    .expect("validated Fail sort authority had an out-of-range child path")
                    .push(authority);
            }

            let mut nested = Vec::new();
            let mut remapped = Vec::new();
            for (command, child_authorities) in commands.into_iter().zip(authorities_by_child) {
                let offset = nested.len();
                let (produced, mut produced_authorities) =
                    self.remove_globals_cmd_with_sort_authority(command, child_authorities);
                for authority in &mut produced_authorities {
                    let child = authority
                        .command_path
                        .first_mut()
                        .expect("remapped Fail sort authority paths are never empty");
                    *child += offset;
                    authority.command_path.insert(0, 0);
                }
                nested.extend(produced);
                remapped.extend(produced_authorities);
            }
            return (vec![GenericNCommand::Fail(span, nested)], remapped);
        }

        if matches!(cmd, GenericNCommand::Sort { .. }) {
            let [mut authority] = <[SortAuthorityAt; 1]>::try_from(authorities)
                .expect("every finalized Sort must carry exactly one authority stamp");
            assert!(
                authority.command_path.is_empty(),
                "a non-Fail Sort authority carried a descendant path"
            );
            let produced = self.remove_globals_cmd(cmd);
            assert!(
                matches!(produced.as_slice(), [GenericNCommand::Sort { .. }]),
                "global removal changed a Sort into a different command shape"
            );
            authority.command_path.push(0);
            return (produced, vec![authority]);
        }

        assert!(
            authorities.is_empty(),
            "a non-Sort command received sort authority metadata"
        );
        let produced = self.remove_globals_cmd(cmd);
        assert!(
            !produced
                .iter()
                .any(|command| matches!(command, GenericNCommand::Sort { .. })),
            "global removal generated an unstamped Sort"
        );
        (produced, Vec::new())
    }

    fn remove_globals_cmd(&mut self, cmd: ResolvedNCommand) -> Vec<ResolvedNCommand> {
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
                    vec![
                        GenericNCommand::Function(func_decl),
                        GenericNCommand::CoreAction(GenericAction::Set(
                            span,
                            resolved_call,
                            vec![],
                            remove_globals_expr(expr),
                        )),
                    ]
                }
                _ => vec![GenericNCommand::CoreAction(remove_globals_action(action))],
            },
            // Rewrite global references but leave the block's own `let`s local.
            GenericNCommand::CoreActions(actions) => {
                vec![GenericNCommand::CoreActions(
                    actions.visit_actions(&mut remove_globals_action),
                )]
            }
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
                vec![
                    GenericNCommand::Function(func_decl),
                    GenericNCommand::CoreActions(GenericActions(new_acts)),
                ]
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
                vec![GenericNCommand::NormRule { rule: new_rule }]
            }
            // Handle the corner case where a global command is wrapped in (fail).
            // Remove globals from every wrapped command and keep the whole flattened
            // result inside the `fail`.
            GenericNCommand::Fail(span, cmds) => {
                let mut removed = vec![];
                for cmd in cmds {
                    removed.extend(self.remove_globals_cmd(cmd));
                }
                vec![GenericNCommand::Fail(span, removed)]
            }
            _ => vec![cmd.visit_exprs(&mut replace_global_vars)],
        }
    }
}
