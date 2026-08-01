//! Remove global variables from the program by translating
//! them into functions with no arguments.
//! This requires type information, so it is done after type checking.
//! Primitives are translated into functions with a primitive output.
//! When a globally-bound primitive value is used in the actions of a rule,
//! we add a new variable to the query bound to the primitive value.

use crate::*;
use crate::{core::ResolvedCall, typechecking::FuncType};
use egglog_ast::generic_ast::{GenericAction, GenericExpr, GenericFact, GenericRule};

/// Name of the one table holding every eq-sort global of `sort`.
pub(crate) fn global_table_name(sort: &str) -> String {
    format!("@Globals_{sort}")
}

/// Where each eq-sort global lives: a row of its sort's shared table.
#[derive(Clone, Debug, Default)]
pub(crate) struct GlobalSlots {
    /// Global name -> (table, slot id).
    slots: HashMap<String, (String, i64)>,
    /// Table -> next unused slot id, which is also its declared-yet marker.
    next_id: HashMap<String, i64>,
    /// Globals slotted since the last [`Self::take_new`]. A slotted global has no
    /// function declaration of its own, so name checking reads them from here.
    newly_slotted: Vec<(String, Span)>,
}

impl GlobalSlots {
    fn slot(&self, global: &str) -> Option<&(String, i64)> {
        self.slots.get(global)
    }

    /// The globals slotted since the last call, which the caller must name-check.
    pub(crate) fn take_new(&mut self) -> Vec<(String, Span)> {
        std::mem::take(&mut self.newly_slotted)
    }

    /// Reserve `global` a row of its sort's table, returning the row and whether
    /// the table still needs declaring.
    fn assign(&mut self, global: &str, sort: &str, span: &Span) -> (String, i64, bool) {
        self.newly_slotted.push((global.to_owned(), span.clone()));
        let table = global_table_name(sort);
        let first = !self.next_id.contains_key(&table);
        let id = self.next_id.entry(table.clone()).or_default();
        let assigned = *id;
        *id += 1;
        self.slots
            .insert(global.to_owned(), (table.clone(), assigned));
        (table, assigned, first)
    }
}

struct GlobalRemover<'a> {
    fresh: &'a mut SymbolGen,
    slots: &'a mut GlobalSlots,
    /// The `i64` sort, for the shared tables' key column.
    key_sort: ArcSort,
    /// Whether eq-sort globals may share one table per sort. False when the
    /// program has already been encoded, where a new shared table would never be
    /// given a term relation or a view.
    share_tables: bool,
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
pub(crate) fn remove_globals(
    prog: Vec<ResolvedNCommand>,
    fresh: &mut SymbolGen,
    slots: &mut GlobalSlots,
    key_sort: ArcSort,
    share_tables: bool,
) -> Vec<ResolvedNCommand> {
    let mut remover = GlobalRemover {
        fresh,
        slots,
        key_sort,
        share_tables,
    };
    prog.into_iter()
        .flat_map(|cmd| remover.remove_globals_cmd(cmd))
        .collect()
}

/// The call a nullary-function global is read through.
fn nullary_call(var: &ResolvedVar) -> ResolvedCall {
    ResolvedCall::Func(FuncType {
        name: var.name.clone(),
        subtype: FunctionSubtype::Custom,
        input: vec![],
        outputs: vec![var.sort.clone()],
    })
}

/// The call a shared-table global is read through, keyed by its slot id.
fn table_call(table: &str, key_sort: &ArcSort, output: &ArcSort) -> ResolvedCall {
    ResolvedCall::Func(FuncType {
        name: table.to_owned(),
        subtype: FunctionSubtype::Custom,
        input: vec![key_sort.clone()],
        outputs: vec![output.clone()],
    })
}

/// The expression a reference to `var` reads its value from: a row of the sort's
/// shared table when `var` has a slot, and the global's own nullary function
/// otherwise (base-sort globals, which need no shared table).
///
/// TODO (yz) it would be better to implement replace_global_var
/// as a function from ResolvedVar to ResolvedExpr
/// and use it as an argument to `subst` instead of `visit_expr`,
/// but we have not implemented `subst` for command.
fn read_global(
    var: &ResolvedVar,
    slots: &GlobalSlots,
    key_sort: &ArcSort,
    span: Span,
) -> ResolvedExpr {
    match slots.slot(&var.name) {
        Some((table, id)) => GenericExpr::Call(
            span.clone(),
            table_call(table, key_sort, &var.sort),
            vec![GenericExpr::Lit(span, Literal::Int(*id))],
        ),
        None => GenericExpr::Call(span, nullary_call(var), vec![]),
    }
}

fn replace_global_vars(
    expr: ResolvedExpr,
    slots: &GlobalSlots,
    key_sort: &ArcSort,
) -> ResolvedExpr {
    match expr.get_global_var() {
        Some(resolved_var) => read_global(&resolved_var, slots, key_sort, expr.span()),
        None => expr,
    }
}

pub(crate) fn remove_globals_expr(
    expr: ResolvedExpr,
    slots: &GlobalSlots,
    key_sort: &ArcSort,
) -> ResolvedExpr {
    expr.visit_exprs(&mut |e| replace_global_vars(e, slots, key_sort))
}

fn remove_globals_action(
    action: ResolvedAction,
    slots: &GlobalSlots,
    key_sort: &ArcSort,
) -> ResolvedAction {
    action.visit_exprs(&mut |e| replace_global_vars(e, slots, key_sort))
}

impl GlobalRemover<'_> {
    fn expr(&self, expr: ResolvedExpr) -> ResolvedExpr {
        remove_globals_expr(expr, self.slots, &self.key_sort)
    }

    fn action(&self, action: ResolvedAction) -> ResolvedAction {
        remove_globals_action(action, self.slots, &self.key_sort)
    }

    /// The commands defining global `name` as `value`, ending with the `set` that
    /// writes it. Eq-sort globals share one table per sort, declared on first use;
    /// a base-sort global keeps its own nullary function, since it never goes
    /// stale and so is given no view or rebuild rule to share.
    fn bind(
        &mut self,
        span: Span,
        name: String,
        ty: &ArcSort,
        value: ResolvedExpr,
    ) -> Vec<ResolvedNCommand> {
        if self.share_tables && ty.is_eq_sort() {
            let (table, id, needs_decl) = self.slots.assign(&name, ty.name(), &span);
            let call = table_call(&table, &self.key_sort, ty);
            let mut out = vec![];
            if needs_decl {
                out.push(GenericNCommand::Function(ResolvedFunctionDecl {
                    name: table,
                    subtype: FunctionSubtype::Custom,
                    schema: Schema {
                        input: vec![self.key_sort.name().to_owned()],
                        outputs: vec![ty.name().to_owned()],
                    },
                    resolved_schema: call.clone(),
                    merge: None,
                    cost: None,
                    unextractable: true,
                    internal_hidden: false,
                    internal_let: true,
                    span: span.clone(),
                    term_constructor: None,
                    identity_vals: None,
                    internal_term_node: false,
                    internal_global_table: true,
                }));
            }
            out.push(GenericNCommand::CoreAction(GenericAction::Set(
                span.clone(),
                call,
                vec![GenericExpr::Lit(span, Literal::Int(id))],
                value,
            )));
            return out;
        }

        let call = ResolvedCall::Func(FuncType {
            name: name.clone(),
            subtype: FunctionSubtype::Custom,
            input: vec![],
            outputs: vec![ty.clone()],
        });
        vec![
            GenericNCommand::Function(ResolvedFunctionDecl {
                name,
                subtype: FunctionSubtype::Custom,
                schema: Schema {
                    input: vec![],
                    outputs: vec![ty.name().to_owned()],
                },
                resolved_schema: call.clone(),
                merge: None,
                cost: None,
                unextractable: true,
                internal_hidden: false,
                internal_let: true,
                span: span.clone(),
                term_constructor: None,
                identity_vals: None,
                internal_term_node: false,
                internal_global_table: false,
            }),
            GenericNCommand::CoreAction(GenericAction::Set(span, call, vec![], value)),
        ]
    }

    fn remove_globals_cmd(&mut self, cmd: ResolvedNCommand) -> Vec<ResolvedNCommand> {
        match cmd {
            GenericNCommand::CoreAction(action) => match action {
                GenericAction::Let(span, name, expr) => {
                    let ty = expr.output_type();
                    let value = self.expr(expr);
                    self.bind(span, name.name, &ty, value)
                }
                _ => vec![GenericNCommand::CoreAction(self.action(action))],
            },
            // Rewrite global references but leave the block's own `let`s local.
            GenericNCommand::CoreActions(actions) => {
                let slots = &*self.slots;
                let key_sort = &self.key_sort;
                vec![GenericNCommand::CoreActions(actions.visit_actions(
                    &mut |action| remove_globals_action(action, slots, key_sort),
                ))]
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
                let mut new_acts: Vec<_> = acts.into_iter().map(|a| self.action(a)).collect();
                let value = self.expr(value);
                let mut out = self.bind(span, name.name, &ty, value);
                // `bind` ends with the `set`; run the block's own actions first.
                let Some(GenericNCommand::CoreAction(set)) = out.pop() else {
                    unreachable!("bind ends with the global's set action")
                };
                new_acts.push(set);
                out.push(GenericNCommand::CoreActions(GenericActions(new_acts)));
                out
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
                        GenericFact::Eq(
                            new.span(),
                            read_global(old, self.slots, &self.key_sort, new.span()),
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
                        .map(|fact| {
                            fact.clone().visit_exprs(&mut |e| {
                                replace_global_vars(e, self.slots, &self.key_sort)
                            })
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
            _ => {
                let slots = &*self.slots;
                let key_sort = &self.key_sort;
                vec![cmd.visit_exprs(&mut |e| replace_global_vars(e, slots, key_sort))]
            }
        }
    }
}
