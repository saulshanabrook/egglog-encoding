//! Parse and typecheck original slotted source before proof checking.

use super::HashMap;
use super::bindings::GlobalNames;
use super::context::{ColumnKind, Constructor, ProofContext, SourceError};
use super::guards::{self, GUARDS, validator_name};
use super::program::ResolvedSlottedProgram;
use crate::slotted::frontend::{
    declarations, expand_includes, name_rewrite, source_constructor, source_rewrite,
};
use crate::slotted::syntax::{self, Form};
use crate::slotted::var_sort::VarSort;
#[cfg(test)]
use egglog::TermDag;
use egglog::ast::{
    Action, Expr, Fact, FunctionDecl, GenericAction, GenericActions, ResolvedExpr, ResolvedExprExt,
    ResolvedFact, ResolvedNCommand, ResolvedRule, ResolvedVar, Rule, Schema, Sexp, Span,
};
use egglog::prelude::BaseSort;
use egglog::sort::{EqSort, UnitSort};
use egglog::util::{FreshGen, INTERNAL_SYMBOL_PREFIX, IndexMap, SymbolGen};
use egglog::{Context, EGraph, ResolvedCall};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;
use std::sync::Arc;

#[derive(Clone, Default)]
struct Scope {
    sorts: BTreeSet<String>,
    constructors: HashMap<String, Constructor>,
    globals: IndexMap<String, String>,
}

#[cfg(test)]
pub(super) fn resolve_rewrite(
    context: &ProofContext,
    dag: &TermDag,
    source: &egglog::ast::Rewrite,
) -> Result<ResolvedRule, SourceError> {
    Scope {
        sorts: context.sorts.clone(),
        constructors: context.constructors.clone(),
        globals: context
            .lets
            .iter()
            .map(|(name, &term)| {
                Ok((
                    name.clone(),
                    super::context::check_term_sort(context, dag, term, None)
                        .map_err(SourceError)?,
                ))
            })
            .collect::<Result<_, SourceError>>()?,
    }
    .resolve_rewrite(
        source,
        &Arc::new(ProofContext {
            constructors: context.constructors.clone(),
            ..Default::default()
        }),
    )
}

impl Scope {
    fn source_types(&self, span: &Span) -> Result<EGraph, SourceError> {
        let err = |e: &dyn Display| SourceError(e.to_string());
        let mut graph = EGraph::default();
        egglog::prelude::add_base_sort(&mut graph, VarSort, span.clone()).map_err(|e| err(&e))?;
        let mut symbols = SymbolGen::new(format!("{INTERNAL_SYMBOL_PREFIX}slotted-types-"));
        for name in &self.sorts {
            graph
                .add_sort(EqSort { name: name.clone() }, span.clone())
                .map_err(|e| err(&e))?;
        }
        for op in self.constructors.values() {
            let decl = FunctionDecl::constructor(
                span.clone(),
                op.name.clone(),
                Schema {
                    input: op.input_sorts().map(str::to_owned).collect(),
                    outputs: vec![op.sort.clone()],
                },
                None,
                false,
                false,
            );
            graph
                .type_info()
                .typecheck_function(&mut symbols, &decl)
                .map_err(|e| err(&e))?;
        }

        Ok(graph)
    }

    fn resolve_action(
        &self,
        span: &Span,
        action: Action,
    ) -> Result<GenericAction<ResolvedCall, ResolvedVar>, SourceError> {
        let mut graph = self.source_types(span)?;
        let mut names = BTreeSet::new();
        let action = action.visit_exprs(&mut |expr| {
            names.extend(expr.vars().filter(|name| name.starts_with('$')));
            expr
        });
        let mut bindings: IndexMap<_, _> = names
            .iter()
            .map(|name| (name.as_str(), (span.clone(), VarSort.to_arcsort())))
            .collect();
        for (name, sort) in &self.globals {
            bindings.insert(
                name.as_str(),
                (span.clone(), graph.get_sort_by_name(sort).unwrap().clone()),
            );
        }
        let mut symbols = SymbolGen::new(format!("{INTERNAL_SYMBOL_PREFIX}slotted-actions-"));
        let resolved = graph
            .type_info()
            .typecheck_standalone_actions(
                &mut symbols,
                &GenericActions(vec![action]),
                &bindings,
                Context::Full,
            )
            .map_err(|e| SourceError(e.to_string()))?;
        let [action] = resolved.0.as_slice() else {
            unreachable!("one source action retains its syntax")
        };
        Ok(action.clone().visit_exprs(&mut |expr| match expr {
            ResolvedExpr::Var(span, mut var) if self.globals.contains_key(&var.name) => {
                var.is_global_ref = true;
                ResolvedExpr::Var(span, var)
            }
            other => other,
        }))
    }

    pub(super) fn resolve_rewrite(
        &self,
        source: &egglog::ast::Rewrite,
        guards: &Arc<ProofContext>,
    ) -> Result<ResolvedRule, SourceError> {
        let err = |e: &dyn Display| SourceError(e.to_string());
        let mut graph = self.source_types(&source.span)?;
        guards::register(&mut graph, guards);
        super::substitution::register(&mut graph, guards);
        let source_terms: Vec<_> = std::iter::once(&source.lhs)
            .chain(std::iter::once(&source.rhs))
            .chain(source.conditions.iter().flat_map(|fact| match fact {
                Fact::Eq(_, a, b) => vec![a, b],
                Fact::Fact(Expr::Call(_, head, args)) if is_guard(head) => args.iter().collect(),
                Fact::Fact(expr) => vec![expr],
            }))
            .collect();
        let source_names: BTreeSet<_> = source_terms
            .iter()
            .flat_map(|expr| expr.vars())
            .chain(self.globals.keys().cloned())
            .collect();
        // Captured carrier globals and local payload variables have distinct scopes.
        let mut payload_vars = BTreeSet::new();
        for expr in &source_terms {
            expr.fold(&mut |expr, _: Vec<()>| {
                if let Expr::Call(_, head, args) = expr
                    && let Some(op) = self.constructors.get(head)
                {
                    for (arg, column) in args.iter().zip(&op.columns) {
                        if matches!(column, ColumnKind::Payload(_)) {
                            payload_vars.extend(arg.vars());
                        }
                    }
                }
            });
        }
        let GlobalNames {
            aliases,
            mut symbols,
        } = GlobalNames::new(self.globals.keys(), &payload_vars, source_names);
        let globals: IndexMap<_, _> = self
            .globals
            .iter()
            .map(|(name, sort)| (aliases[name].clone(), sort.clone()))
            .collect();
        fn capture(
            program: &Scope,
            expr: &Expr,
            payload: bool,
            aliases: &BTreeMap<String, String>,
        ) -> Expr {
            match expr {
                Expr::Var(span, name) if !payload && aliases.contains_key(name) => {
                    Expr::Var(span.clone(), aliases[name].clone())
                }
                Expr::Call(span, head, args) => Expr::Call(
                    span.clone(),
                    head.clone(),
                    args.iter()
                        .enumerate()
                        .map(|(i, arg)| {
                            let payload = program.constructors.get(head).is_some_and(|op| {
                                matches!(op.columns.get(i), Some(ColumnKind::Payload(_)))
                            });
                            capture(program, arg, payload, aliases)
                        })
                        .collect(),
                ),
                _ => expr.clone(),
            }
        }
        let lhs = capture(self, &source.lhs, false, &aliases);
        let rhs = capture(self, &source.rhs, false, &aliases);
        let mut body = vec![Fact::Fact(lhs.clone())];
        body.extend(source.conditions.iter().map(|fact| {
            match fact {
                Fact::Eq(span, a, b) => Fact::Eq(
                    span.clone(),
                    capture(self, a, false, &aliases),
                    capture(self, b, false, &aliases),
                ),
                Fact::Fact(Expr::Call(span, head, args)) if is_guard(head) => {
                    Fact::Fact(Expr::Call(
                        span.clone(),
                        head.clone(),
                        args.iter()
                            .map(|arg| capture(self, arg, false, &aliases))
                            .collect(),
                    ))
                }
                Fact::Fact(expr) => Fact::Fact(capture(self, expr, false, &aliases)),
            }
        }));
        let mut rule = Rule {
            span: source.span.clone(),
            head: GenericActions(vec![GenericAction::Union(source.span.clone(), lhs, rhs)]),
            body,
            name: source.name.clone(),
            ruleset: String::new(),
            eval_mode: Default::default(),
            no_decomp: false,
            include_subsumed: false,
        };
        // Slot literals have the rigid Var sort. Captured globals retain the
        // sort of their source term; constructor signatures infer all other locals.
        let var_ty = VarSort.to_arcsort();
        let mut bindings: IndexMap<_, _> = source_terms
            .iter()
            .flat_map(|expr| expr.vars())
            .filter(|name| name.starts_with('$') && !payload_vars.contains(name))
            .map(|name| (name, (source.span.clone(), var_ty.clone())))
            .collect();
        for (name, sort) in &globals {
            let ty = graph
                .get_sort_by_name(sort)
                .ok_or_else(|| SourceError(format!("unknown sort {sort}")))?
                .clone();
            bindings.insert(name.clone(), (source.span.clone(), ty));
        }
        let expression_sort = |expr: &Expr| match expr {
            Expr::Call(_, head, _) => self.constructors.get(head).map(|c| c.sort.clone()),
            Expr::Var(_, name) if name.starts_with('$') => Some("Var".into()),
            Expr::Var(_, name) => globals.get(name).cloned(),
            Expr::Lit(_, lit) => Some(egglog::sort::literal_sort(lit).name().to_owned()),
        };
        // Infer plain facts in their source context: guards return Unit, while
        // constructor patterns return the carrier. Remove these type constraints
        // after resolution; the checker sees the original facts.
        let plain_facts: Vec<_> = rule
            .body
            .iter_mut()
            .enumerate()
            .map(|(i, fact)| {
                let Fact::Fact(expr) = fact else {
                    // Equality-bound constructor patterns need the same result
                    // sort constraint as plain constructor facts. Otherwise a
                    // guard namesake can leave its children unconstrained.
                    if let Fact::Eq(span, a, b) = fact {
                        let binding = match (a, b) {
                            (Expr::Var(_, name), term @ Expr::Call(..))
                            | (term @ Expr::Call(..), Expr::Var(_, name)) => Some((name, term)),
                            _ => None,
                        };
                        if let Some((name, term)) = binding
                            && let Some(sort) = expression_sort(term)
                        {
                            bindings.entry(name.clone()).or_insert_with(|| {
                                (span.clone(), graph.get_sort_by_name(&sort).unwrap().clone())
                            });
                        }
                    }
                    return false;
                };
                let guard = i > 0 && matches!(expr, Expr::Call(_, head, _) if is_guard(head));
                if guard && let Expr::Call(_, head, _) = expr {
                    *head = validator_name(head).to_owned();
                }
                let name = symbols.fresh("source-fact");
                let sort = if guard {
                    Some(UnitSort.to_arcsort())
                } else {
                    expression_sort(expr).map(|sort| {
                        graph
                            .get_sort_by_name(&sort)
                            .expect("source sort is registered")
                            .clone()
                    })
                };
                if let Some(sort) = sort {
                    bindings.insert(name.clone(), (expr.span(), sort));
                }
                *fact = Fact::Eq(expr.span(), Expr::Var(expr.span(), name), expr.clone());
                true
            })
            .collect();
        let bindings = bindings
            .iter()
            .map(|(name, value)| (name.as_str(), value.clone()))
            .collect();
        let mut rule = graph
            .type_info()
            .typecheck_rule_with_bindings(&mut symbols, &rule, false, &bindings)
            .map_err(|e| err(&e))?;
        for (fact, plain) in rule.body.iter_mut().zip(plain_facts) {
            if plain {
                let ResolvedFact::Eq(_, _, expr) = fact else {
                    unreachable!("resolved fact retains its syntax")
                };
                *fact = ResolvedFact::Fact(expr.clone());
            }
        }
        for fact in &rule.body {
            if let ResolvedFact::Fact(ResolvedExpr::Call(_, ResolvedCall::Primitive(head), args)) =
                fact
            {
                let head = if head.name() == validator_name("!=") {
                    "!="
                } else {
                    head.name()
                };
                if !is_guard(head) {
                    return Err(SourceError(format!("unsupported source guard {head}")));
                }
                let valid = match head {
                    "!=" | "renaming-=" | "renaming-!=" => args.len() == 2,
                    "free" | "not-free" => args.len() >= 2,
                    "free-names-are" => !args.is_empty(),
                    _ => true,
                };
                if !valid {
                    return Err(SourceError(format!("wrong arity for {head}")));
                }
            }
        }
        let originals: BTreeMap<_, _> = aliases
            .into_iter()
            .map(|(name, alias)| (alias, name))
            .collect();
        Ok(rule.visit_exprs(&mut |expr| match expr {
            ResolvedExpr::Var(span, mut var) if originals.contains_key(&var.name) => {
                var.name = originals[&var.name].clone();
                var.is_global_ref = true;
                ResolvedExpr::Var(span, var)
            }
            other => other,
        }))
    }
}

fn is_guard(name: &str) -> bool {
    GUARDS.contains(&name)
}

/// Resolve the original slotted source visible at a proof query.
/// Rewrites become typed rules with their original conditions and nested terms.
/// Includes resolve from the working directory; push/pop determines the visible scope.
pub fn resolve_program<'a, 'src: 'a>(
    source: impl IntoIterator<Item = &'a Sexp<'src>>,
) -> Result<ResolvedSlottedProgram, SourceError> {
    let forms = source
        .into_iter()
        .map(|s| (syntax::convert(s), s.span()))
        .collect();
    let forms =
        expand_includes(forms, &mut BTreeSet::new()).map_err(|e| SourceError(e.to_string()))?;
    let mut reader = Reader::default();
    let mut scopes = Vec::new();
    let mut start = 0;
    for (i, (form, _)) in forms.iter().enumerate() {
        if let Ok((head @ ("push" | "pop"), args)) = form.call() {
            reader.region(&forms[start..i])?;
            if !args.is_empty() {
                return Err(SourceError(format!("slotted {head} takes no arguments")));
            }
            if head == "push" {
                scopes.push((reader.scope.clone(), reader.resolved.clone()));
            } else {
                (reader.scope, reader.resolved) = scopes
                    .pop()
                    .ok_or_else(|| SourceError("pop without a corresponding push".into()))?;
            }
            start = i + 1;
        }
    }
    reader.region(&forms[start..])?;
    reader.snapshot()
}

#[derive(Clone, Default)]
pub(in crate::slotted) struct Reader {
    scope: Scope,
    resolved: ResolvedSlottedProgram,
    rules: usize,
    rule_names: BTreeSet<String>,
}

impl Reader {
    fn region(&mut self, forms: &[(Form, Span)]) -> Result<(), SourceError> {
        self.declare(forms)?;
        for (form, span) in forms {
            self.command(form, span)?;
        }
        Ok(())
    }

    pub(in crate::slotted) fn declare(
        &mut self,
        forms: &[(Form, Span)],
    ) -> Result<(), SourceError> {
        let mut sorts = Vec::new();
        let mut constructors = Vec::new();
        for (form, _) in forms {
            declarations(form, &mut sorts, &mut constructors).map_err(SourceError)?;
        }
        let span = forms
            .first()
            .map(|(_, s)| s.clone())
            .unwrap_or_else(|| egglog::span!());
        for sort in sorts {
            if ["Var", "i64", "String", "Unit"].contains(&sort.as_str())
                || !self.scope.sorts.insert(sort.clone())
            {
                return Err(SourceError(format!(
                    "invalid or duplicate equality sort {sort}"
                )));
            }
            self.resolved.commands.push(ResolvedNCommand::Sort {
                span: span.clone(),
                name: sort,
                presort_and_args: None,
                uf: None,
                container_rebuild: None,
                proof_constructors: None,
                unionable: true,
            });
        }
        for form in constructors {
            let op = source_constructor(
                &form,
                self.scope.sorts.iter().map(String::as_str),
                self.scope.constructors.values(),
            )
            .map_err(SourceError)?;
            let decl = FunctionDecl::constructor(
                span.clone(),
                op.name.clone(),
                Schema::new(
                    op.input_sorts().map(str::to_owned).collect(),
                    op.sort.clone(),
                ),
                None,
                false,
                false,
            );
            let mut graph = self.scope.source_types(&span)?;
            let mut symbols =
                SymbolGen::new(format!("{INTERNAL_SYMBOL_PREFIX}slotted-declarations-"));
            let decl = graph
                .type_info()
                .typecheck_function(&mut symbols, &decl)
                .map_err(|e| SourceError(e.to_string()))?;
            let binders: Vec<_> = op
                .columns
                .iter()
                .enumerate()
                .filter_map(|(i, column)| (*column == ColumnKind::Binder).then_some(i))
                .collect();
            if !binders.is_empty() {
                self.resolved.binders.insert(op.name.clone(), binders);
            }
            self.resolved
                .commands
                .push(ResolvedNCommand::Function(decl));
            self.scope.constructors.insert(op.name.clone(), op);
        }
        Ok(())
    }

    pub(in crate::slotted) fn command(
        &mut self,
        form: &Form,
        span: &Span,
    ) -> Result<(), SourceError> {
        let (head, args) = form.call().map_err(SourceError)?;
        let command = match (head, args) {
            ("sort" | "constructor" | "datatype" | "datatype*", _) => return Ok(()),
            ("let", [name, value]) => {
                let name = name.symbol().map_err(SourceError)?;
                if name.starts_with('$') || self.scope.globals.contains_key(name) {
                    return Err(SourceError(format!("invalid or duplicate global {name}")));
                }
                let value = value.expr().map_err(SourceError)?;
                let action = self
                    .scope
                    .resolve_action(span, Action::Let(span.clone(), name.into(), value))?;
                let GenericAction::Let(_, _, value) = &action else {
                    unreachable!("resolved let")
                };
                self.scope
                    .globals
                    .insert(name.into(), value.output_type().name().to_owned());
                ResolvedNCommand::CoreAction(action)
            }
            ("union", [lhs, rhs]) => {
                let lhs = lhs.expr().map_err(SourceError)?;
                let rhs = rhs.expr().map_err(SourceError)?;
                let action = self
                    .scope
                    .resolve_action(span, Action::Union(span.clone(), lhs, rhs))?;
                let GenericAction::Union(_, lhs, _) = &action else {
                    unreachable!("resolved union")
                };
                if !self.scope.sorts.contains(lhs.output_type().name()) {
                    return Err(SourceError(
                        "union requires terms in an equality sort".into(),
                    ));
                }
                ResolvedNCommand::CoreAction(action)
            }
            ("extract", [value]) => {
                // Source extraction constructs its input. Retain that fact for
                // this certificate and later queries without exposing a global.
                let name = format!(
                    "{INTERNAL_SYMBOL_PREFIX}slotted-extract-{}",
                    self.resolved.commands.len()
                );
                let value = value.expr().map_err(SourceError)?;
                let action = self
                    .scope
                    .resolve_action(span, Action::Let(span.clone(), name, value))?;
                ResolvedNCommand::CoreAction(action)
            }
            ("rewrite", _) => {
                let mut rule = source_rewrite(args).map_err(SourceError)?;
                name_rewrite(&mut rule, self.rules, Some(&mut self.rule_names));
                self.rules += 1;
                ResolvedNCommand::NormRule {
                    rule: self.resolve_rewrite(&rule)?,
                }
            }
            (
                "run" | "run-schedule" | "ruleset" | "check" | "fail" | "print-size"
                | "print-function" | "print-stats" | "slotted-export" | "set-option",
                _,
            ) => return Ok(()),
            _ => return Err(SourceError(format!("unsupported source command {head}"))),
        };
        self.resolved.commands.push(command);
        Ok(())
    }

    pub(in crate::slotted) fn resolve_rewrite(
        &self,
        source: &egglog::ast::Rewrite,
    ) -> Result<ResolvedRule, SourceError> {
        self.scope
            .resolve_rewrite(source, &Arc::new(self.guard_context()))
    }

    pub(in crate::slotted) fn add_rewrite(
        &mut self,
        source: &egglog::ast::Rewrite,
    ) -> Result<(), SourceError> {
        let rule = self.resolve_rewrite(source)?;
        self.resolved
            .commands
            .push(ResolvedNCommand::NormRule { rule });
        Ok(())
    }

    fn guard_context(&self) -> ProofContext {
        ProofContext {
            constructors: self.scope.constructors.clone(),
            ..Default::default()
        }
    }

    pub(in crate::slotted) fn snapshot(&self) -> Result<ResolvedSlottedProgram, SourceError> {
        let mut program = self.resolved.clone();
        let mut graph = self.scope.source_types(&egglog::span!())?;
        guards::register(&mut graph, &Arc::new(self.guard_context()));
        super::substitution::register(&mut graph, &Arc::new(self.guard_context()));
        // Earlier rules may receive terms built with later constructor declarations.
        // Refresh only the primitive registrations; preserve their resolved arguments.
        for command in &mut program.commands {
            let ResolvedNCommand::NormRule { rule } = command else {
                continue;
            };
            let mut error = None;
            *rule = rule.clone().visit_exprs(&mut |expr| {
                let ResolvedExpr::Call(span, ResolvedCall::Primitive(head), args) = expr else {
                    return expr;
                };
                let types: Vec<_> = head
                    .input()
                    .iter()
                    .cloned()
                    .chain([head.output().clone()])
                    .collect();
                match ResolvedCall::from_resolution(
                    head.name(),
                    &types,
                    &*graph.type_info(),
                    Context::Read,
                    &span,
                ) {
                    Ok(head) => ResolvedExpr::Call(span, head, args),
                    Err(e) => {
                        error = Some(SourceError(e.to_string()));
                        ResolvedExpr::Call(span, ResolvedCall::Primitive(head), args)
                    }
                }
            });
            if let Some(error) = error {
                return Err(error);
            }
        }
        Ok(program)
    }
}
