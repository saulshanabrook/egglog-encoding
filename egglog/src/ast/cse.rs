//! Common-subexpression elimination over action scopes.
//!
//! Within one scope, a constructor application occurring more than once is bound
//! to a shared `let` and its occurrences rewritten to that variable:
//!
//! ```text
//! (Foo (Bar x) (Bar x))   ⟶   (let c (Bar x)) (Foo c c)
//! ```

use crate::{
    ast::{
        FunctionSubtype, GenericActions, GenericNCommand, ResolvedAction, ResolvedExpr,
        ResolvedExprExt, ResolvedNCommand, ResolvedVar,
    },
    core::ResolvedCall,
    util::{FreshGen, HashMap, SymbolGen},
};
use egglog_ast::generic_ast::GenericExpr;

/// Apply [`cse_actions`] to every action scope in `program`.
///
/// A rule head keeps its shape; a top-level action that gains shared `let`s
/// becomes a [`GenericNCommand::CoreActions`] block, so they stay local.
pub(crate) fn cse_program(
    program: Vec<ResolvedNCommand>,
    fresh: &mut SymbolGen,
) -> Vec<ResolvedNCommand> {
    program
        .into_iter()
        .map(|command| match command {
            GenericNCommand::NormRule { mut rule } => {
                rule.head = GenericActions(cse_actions(&rule.head.0, fresh));
                GenericNCommand::NormRule { rule }
            }
            GenericNCommand::CoreAction(action) => {
                let deduped = cse_actions(std::slice::from_ref(&action), fresh);
                // Nothing shared: keep the plain action.
                if deduped.len() == 1 {
                    GenericNCommand::CoreAction(deduped.into_iter().next().unwrap())
                } else {
                    GenericNCommand::CoreActions(GenericActions(deduped))
                }
            }
            GenericNCommand::CoreActions(actions) => {
                GenericNCommand::CoreActions(GenericActions(cse_actions(&actions.0, fresh)))
            }
            other => other,
        })
        .collect()
}

/// Bind each constructor application occurring more than once in this scope to a
/// shared `let`, returning the scope's actions with those `let`s prepended.
pub(crate) fn cse_actions(
    actions: &[ResolvedAction],
    fresh: &mut SymbolGen,
) -> Vec<ResolvedAction> {
    let mut counts: HashMap<String, usize> = HashMap::default();
    for action in actions {
        count_action_ctors(action, &mut counts);
    }
    if counts.values().all(|&c| c < 2) {
        return actions.to_vec();
    }
    let mut cache: HashMap<String, ResolvedVar> = HashMap::default();
    let mut out = vec![];
    for action in actions {
        let rewritten = cse_action(action, &counts, &mut cache, &mut out, fresh);
        out.push(rewritten);
    }
    out
}

/// Count each constructor sub-application (by its s-expr form) in `expr`.
fn count_ctor_subexprs(expr: &ResolvedExpr, counts: &mut HashMap<String, usize>) {
    if let GenericExpr::Call(_, call, args) = expr {
        for arg in args {
            count_ctor_subexprs(arg, counts);
        }
        if matches!(call, ResolvedCall::Func(ft) if ft.subtype == FunctionSubtype::Constructor) {
            *counts.entry(expr.to_string()).or_default() += 1;
        }
    }
}

/// Count constructor sub-applications across one action's expressions.
fn count_action_ctors(action: &ResolvedAction, counts: &mut HashMap<String, usize>) {
    match action {
        ResolvedAction::Let(_, _, e) | ResolvedAction::Expr(_, e) => count_ctor_subexprs(e, counts),
        ResolvedAction::Set(_, _, args, val) => {
            args.iter().for_each(|a| count_ctor_subexprs(a, counts));
            count_ctor_subexprs(val, counts);
        }
        ResolvedAction::Union(_, a, b) => {
            count_ctor_subexprs(a, counts);
            count_ctor_subexprs(b, counts);
        }
        ResolvedAction::Change(_, _, _, args) => {
            args.iter().for_each(|a| count_ctor_subexprs(a, counts));
        }
        ResolvedAction::Panic(..) => {}
    }
}

/// Rewrite one action, hoisting its repeated constructor sub-applications (per
/// `counts`) into shared `let`s pushed onto `out` before it.
fn cse_action(
    action: &ResolvedAction,
    counts: &HashMap<String, usize>,
    cache: &mut HashMap<String, ResolvedVar>,
    out: &mut Vec<ResolvedAction>,
    fresh: &mut SymbolGen,
) -> ResolvedAction {
    let mut go = |e: &ResolvedExpr| cse_expr(e, counts, cache, out, fresh);
    match action {
        ResolvedAction::Let(span, v, e) => ResolvedAction::Let(span.clone(), v.clone(), go(e)),
        ResolvedAction::Expr(span, e) => ResolvedAction::Expr(span.clone(), go(e)),
        ResolvedAction::Set(span, call, args, val) => {
            let args = args.iter().map(&mut go).collect();
            let val = go(val);
            ResolvedAction::Set(span.clone(), call.clone(), args, val)
        }
        ResolvedAction::Union(span, a, b) => ResolvedAction::Union(span.clone(), go(a), go(b)),
        ResolvedAction::Change(span, change, call, args) => {
            let args = args.iter().map(&mut go).collect();
            ResolvedAction::Change(span.clone(), *change, call.clone(), args)
        }
        ResolvedAction::Panic(..) => action.clone(),
    }
}

/// Rewrite one expression bottom-up, replacing each repeated constructor
/// application with a shared `let`-bound variable. Keyed by the original s-expr,
/// matching `counts`.
fn cse_expr(
    expr: &ResolvedExpr,
    counts: &HashMap<String, usize>,
    cache: &mut HashMap<String, ResolvedVar>,
    out: &mut Vec<ResolvedAction>,
    fresh: &mut SymbolGen,
) -> ResolvedExpr {
    let GenericExpr::Call(span, call, args) = expr else {
        return expr.clone();
    };
    let new_args = args
        .iter()
        .map(|a| cse_expr(a, counts, cache, out, fresh))
        .collect();
    let rewritten = GenericExpr::Call(span.clone(), call.clone(), new_args);
    let is_ctor =
        matches!(call, ResolvedCall::Func(ft) if ft.subtype == FunctionSubtype::Constructor);
    if !is_ctor || counts.get(&expr.to_string()).copied().unwrap_or(0) < 2 {
        return rewritten;
    }
    let key = expr.to_string();
    if let Some(v) = cache.get(&key) {
        return GenericExpr::Var(span.clone(), v.clone());
    }
    let var = ResolvedVar {
        name: fresh.fresh("cse"),
        sort: expr.output_type(),
        is_global_ref: false,
    };
    out.push(ResolvedAction::Let(span.clone(), var.clone(), rewritten));
    cache.insert(key, var.clone());
    GenericExpr::Var(span.clone(), var)
}
