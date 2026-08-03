//! Remove global variables from the program by translating them into table
//! reads: each global becomes one row of its sort's shared table.
//! This requires type information, so it is done after type checking.
//! When a globally-bound primitive value is used in the actions of a rule,
//! we add a new variable to the query bound to the primitive value.

use crate::*;
use crate::{core::ResolvedCall, typechecking::FuncType};
use egglog_ast::generic_ast::{GenericAction, GenericExpr, GenericFact, GenericRule};

/// Where each global lives: a row of its sort's shared table.
#[derive(Clone, Debug, Default)]
pub(crate) struct GlobalSlots {
    /// Sort -> the one table its globals share. Named by the fresh generator, so
    /// no program can declare a function that collides with it, and so it does
    /// not count towards the size of the program's own data.
    tables: HashMap<String, String>,
    /// Global name -> (table, slot id).
    slots: HashMap<String, (String, i64)>,
    /// (table, slot id) -> global name, for reading a slotted global back out.
    names: HashMap<(String, i64), String>,
    /// Table -> next unused slot id.
    next_id: HashMap<String, i64>,
    /// Globals slotted since the last [`Self::take_new`]. A slotted global has no
    /// function declaration of its own, so name checking reads them from here.
    newly_slotted: Vec<NewSlot>,
}

/// A row reserved for a global, and what the name meant before.
#[derive(Clone, Debug)]
pub(crate) struct NewSlot {
    pub(crate) name: String,
    pub(crate) span: Span,
    displaced: Option<(String, i64)>,
    /// The sort whose table this reservation declared, if it declared one.
    declared: Option<String>,
    /// Whether the global's name has been registered for shadow checking, and so
    /// has to be unregistered if the command is rejected.
    pub(crate) named: bool,
}

impl GlobalSlots {
    /// The row `global` was written to.
    pub(crate) fn slot(&self, global: &str) -> Option<(&str, i64)> {
        self.slots
            .get(global)
            .map(|(table, id)| (table.as_str(), *id))
    }

    /// The global stored at `id` of `table`, if that row holds one.
    pub(crate) fn global_at(&self, table: &str, id: i64) -> Option<&str> {
        self.names
            .get(&(table.to_owned(), id))
            .map(std::string::String::as_str)
    }

    /// The globals slotted since the last call, which the caller must name-check
    /// and then either keep or hand back to [`Self::give_back`].
    pub(crate) fn take_new(&mut self) -> Vec<NewSlot> {
        std::mem::take(&mut self.newly_slotted)
    }

    /// Return a batch from [`Self::take_new`], to be resolved once the whole
    /// command has either been accepted or rejected.
    pub(crate) fn put_back(&mut self, slots: Vec<NewSlot>) {
        let pending = std::mem::replace(&mut self.newly_slotted, slots);
        self.newly_slotted.extend(pending);
    }

    /// Release rows reserved for a command that was then rejected, restoring what
    /// each name meant before it. Their ids are not reused. A table the command
    /// declared goes with it, so the next global of that sort declares one again.
    pub(crate) fn give_back(&mut self, slots: Vec<NewSlot>) {
        for slot in slots.into_iter().rev() {
            if let Some((table, id)) = self.slots.remove(&slot.name) {
                self.names.remove(&(table, id));
            }
            if let Some(displaced) = slot.displaced {
                self.names.insert(displaced.clone(), slot.name.clone());
                self.slots.insert(slot.name, displaced);
            }
            if let Some(sort) = slot.declared
                && let Some(table) = self.tables.remove(&sort)
            {
                self.next_id.remove(&table);
            }
        }
    }

    /// Reserve `global` a row of its sort's table, returning the row and whether
    /// the table still needs declaring.
    fn assign(
        &mut self,
        global: &str,
        sort: &str,
        span: &Span,
        fresh: &mut SymbolGen,
    ) -> (String, i64, bool) {
        let first = !self.tables.contains_key(sort);
        let table = self
            .tables
            .entry(sort.to_owned())
            .or_insert_with(|| fresh.fresh(&format!("Globals_{sort}")))
            .clone();
        let id = self.next_id.entry(table.clone()).or_default();
        let assigned = *id;
        *id += 1;
        let displaced = self
            .slots
            .insert(global.to_owned(), (table.clone(), assigned));
        self.names
            .insert((table.clone(), assigned), global.to_owned());
        self.newly_slotted.push(NewSlot {
            name: global.to_owned(),
            span: span.clone(),
            displaced,
            declared: first.then(|| sort.to_owned()),
            named: false,
        });
        (table, assigned, first)
    }
}

struct GlobalRemover<'a> {
    fresh: &'a mut SymbolGen,
    slots: &'a mut GlobalSlots,
    /// The `i64` sort, for the shared tables' key column.
    key_sort: ArcSort,
    /// Whether globals may share one table per sort. False once the program has
    /// been encoded, where a new shared table would get no view.
    share_tables: bool,
}

/// Removes all globals from a program.
/// No top level lets are allowed after this pass,
/// nor any variable that references a global.
/// Every reference becomes a read of the row the global was written to. Globals
/// of a sort share one table, so its schema is emitted once per sort rather than
/// once per global:
/// ```ignore
/// (let e (Num 3))
/// (Add e e)
/// ```
/// becomes
/// ```ignore
/// (function @Globals_Math (i64) Math :no-merge)
/// (set (@Globals_Math 0) (Num 3))
/// (Add (@Globals_Math 0) (@Globals_Math 0))
/// ```
///
/// If later, a global is referenced in a rule:
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
    assert!(
        var.is_global_ref,
        "{} is not a global reference",
        var.name.clone()
    );
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
/// shared table, or the global's own nullary function if it has no slot.
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
            vec![GenericExpr::Lit(span, Literal::Int(id))],
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
    /// writes it. Globals of a sort share one table, declared on first use.
    fn bind(
        &mut self,
        span: Span,
        name: String,
        ty: &ArcSort,
        value: ResolvedExpr,
    ) -> Vec<ResolvedNCommand> {
        if self.share_tables {
            let (table, id, needs_decl) = self.slots.assign(&name, ty.name(), &span, self.fresh);
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
            // result inside the `fail` — except the shared tables, which are hoisted
            // out. A `fail` asserts that a binding fails and stops at the first
            // command that does, so a table left inside might never be declared
            // while a later global still expects it to exist.
            GenericNCommand::Fail(span, cmds) => {
                let mut tables = vec![];
                let mut removed = vec![];
                for cmd in cmds {
                    for cmd in self.remove_globals_cmd(cmd) {
                        match &cmd {
                            GenericNCommand::Function(fdecl) if fdecl.internal_global_table => {
                                tables.push(cmd)
                            }
                            _ => removed.push(cmd),
                        }
                    }
                }
                tables.push(GenericNCommand::Fail(span, removed));
                tables
            }
            _ => {
                let slots = &*self.slots;
                let key_sort = &self.key_sort;
                vec![cmd.visit_exprs(&mut |e| replace_global_vars(e, slots, key_sort))]
            }
        }
    }
}
