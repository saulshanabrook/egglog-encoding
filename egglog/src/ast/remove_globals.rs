//! Replace global bindings and references with writes and reads of a shared
//! table for each sort, keyed by the binding name.
//! This requires type information, so it is done after type checking.
//! Primitives are translated into functions with a primitive output.
//! When a globally-bound primitive value is used in the actions of a rule,
//! we add a new variable to the query bound to the primitive value.

use crate::*;
use crate::{core::ResolvedCall, typechecking::FuncType};
use egglog_ast::generic_ast::{GenericAction, GenericExpr, GenericFact, GenericRule};

/// Storage assigned by global desugaring. `push`/`pop` clone and restore this
/// with the rest of the type information.
#[derive(Clone, Debug, Default)]
pub(crate) struct GlobalTables {
    tables: HashMap<String, Arc<FuncType>>,
    pub(crate) bindings: HashMap<String, Arc<FuncType>>,
}

impl GlobalTables {
    fn read(&self, span: Span, var: &ResolvedVar) -> ResolvedExpr {
        GenericExpr::Call(
            span.clone(),
            ResolvedCall::Func(self.bindings[&var.name].clone()),
            vec![GenericExpr::Lit(span, Literal::String(var.name.clone()))],
        )
    }

    fn replace_global_vars(&self, expr: ResolvedExpr) -> ResolvedExpr {
        match expr.get_global_var() {
            Some(var) => self.read(expr.span(), &var),
            None => expr,
        }
    }

    pub(crate) fn expr(&self, expr: ResolvedExpr) -> ResolvedExpr {
        expr.visit_exprs(&mut |expr| self.replace_global_vars(expr))
    }

    fn action(&self, action: ResolvedAction) -> ResolvedAction {
        action.visit_exprs(&mut |expr| self.replace_global_vars(expr))
    }
}

struct GlobalRemover<'a> {
    fresh: &'a mut SymbolGen,
    globals: &'a mut GlobalTables,
    declarations: Vec<ResolvedNCommand>,
}

/// Lower globals directly to one table per sort, keyed by the binding's name:
///
/// ```ignore
/// (let $x 3)
/// (let $y (+ $x 1))
/// ```
/// becomes
/// ```ignore
/// (function @Globals_i64 (String) i64 :no-merge :internal-let)
/// (set (@Globals_i64 "$x") 3)
/// (set (@Globals_i64 "$y") (+ (@Globals_i64 "$x") 1))
/// ```
/// Globals used in a rule head are bound in its query, so its actions do not
/// need to look up mutable tables. Names must be checked before this pass.
pub(crate) fn remove_globals(
    prog: Vec<ResolvedNCommand>,
    fresh: &mut SymbolGen,
    globals: &mut GlobalTables,
) -> Vec<ResolvedNCommand> {
    let mut remover = GlobalRemover {
        fresh,
        globals,
        declarations: vec![],
    };
    let commands = prog
        .into_iter()
        .flat_map(|cmd| remover.remove_globals_cmd(cmd))
        .collect::<Vec<_>>();
    remover.declarations.extend(commands);
    remover.declarations
}

impl GlobalRemover<'_> {
    fn bind(&mut self, span: &Span, name: &ResolvedVar) -> (ResolvedCall, Vec<ResolvedExpr>) {
        let sort = name.sort.name().to_owned();
        let table = self.globals.tables.entry(sort.clone()).or_insert_with(|| {
            let table_name = self.fresh.fresh(&format!("Globals_{sort}"));
            self.declarations
                .push(GenericNCommand::Function(ResolvedFunctionDecl {
                    name: table_name.clone(),
                    subtype: FunctionSubtype::Custom,
                    schema: Schema {
                        input: vec!["String".to_owned()],
                        outputs: vec![sort],
                    },
                    merge: None,
                    cost: None,
                    unextractable: true,
                    internal_hidden: false,
                    internal_let: true,
                    span: span.clone(),
                    internal_view: None,
                    identity_vals: None,
                    internal_term_node: false,
                }));
            Arc::new(FuncType {
                name: table_name,
                subtype: FunctionSubtype::Custom,
                is_global: true,
                input: vec![StringSort.to_arcsort()],
                outputs: vec![name.sort.clone()],
            })
        });
        self.globals
            .bindings
            .insert(name.name.clone(), table.clone());
        (
            ResolvedCall::Func(table.clone()),
            vec![GenericExpr::Lit(
                span.clone(),
                Literal::String(name.name.clone()),
            )],
        )
    }

    fn remove_globals_cmd(&mut self, cmd: ResolvedNCommand) -> Vec<ResolvedNCommand> {
        match cmd {
            GenericNCommand::CoreAction(action) => match action {
                GenericAction::Let(span, name, expr) => {
                    let expr = self.globals.expr(expr);
                    let (table, key) = self.bind(&span, &name);
                    vec![GenericNCommand::CoreAction(GenericAction::Set(
                        span, table, key, expr,
                    ))]
                }
                _ => vec![GenericNCommand::CoreAction(self.globals.action(action))],
            },
            // Rewrite global references but leave the block's own `let`s local.
            GenericNCommand::CoreActions(actions) => {
                vec![GenericNCommand::CoreActions(
                    actions.visit_actions(&mut |action| self.globals.action(action)),
                )]
            }
            // Run the block with local bindings, then store its trailing value
            // in the global's row.
            GenericNCommand::LetBegin(span, name, actions) => {
                let mut acts = actions.0;
                let value = match acts.pop() {
                    Some(GenericAction::Expr(_, e)) => e,
                    _ => panic!("`(let _ (begin ...))` must end with an expression"),
                };
                let value = self.globals.expr(value);
                let mut new_acts: Vec<_> = acts
                    .into_iter()
                    .map(|action| self.globals.action(action))
                    .collect();
                let (table, key) = self.bind(&span, &name);
                new_acts.push(GenericAction::Set(span, table, key, value));
                vec![GenericNCommand::CoreActions(GenericActions(new_acts))]
            }
            GenericNCommand::NormRule { rule } => {
                // A map from the global variables in actions to their new names
                // in the query.
                let mut globals = HashMap::default();
                rule.head.clone().visit_exprs(&mut |expr| {
                    if let Some(resolved_var) = expr.get_global_var() {
                        let new_name = self.fresh.fresh(&resolved_var.name);
                        globals.insert(
                            resolved_var.clone(),
                            GenericExpr::Var(
                                expr.span(),
                                ResolvedVar {
                                    name: new_name,
                                    sort: resolved_var.sort.clone(),
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
                        GenericFact::Eq(new.span(), self.globals.read(new.span(), old), new.clone())
                    })
                    .collect();

                let new_rule = GenericRule {
                    span: rule.span,
                    // instrument the old facts and add the new facts to the end
                    body: rule
                        .body
                        .iter()
                        .map(|fact| {
                            fact.clone()
                                .visit_exprs(&mut |expr| self.globals.replace_global_vars(expr))
                        })
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
            // Handle commands inside fail that reference existing globals.
            GenericNCommand::Fail(span, cmds) => {
                let mut removed = vec![];
                for cmd in cmds {
                    removed.extend(self.remove_globals_cmd(cmd));
                }
                vec![GenericNCommand::Fail(span, removed)]
            }
            _ => vec![cmd.visit_exprs(&mut |expr| self.globals.replace_global_vars(expr))],
        }
    }
}
