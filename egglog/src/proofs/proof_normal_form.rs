use crate::ast::ResolvedNCommand;
use crate::core::ResolvedCall;
use crate::*;
use egglog_ast::generic_ast::GenericExpr;

/// Transforms queries into "proof normal form" by lifting subexpressions to the
/// top level, so that every primitive is applied only to variables, literals, or
/// other primitives. This is what lets the proof checker re-evaluate a primitive
/// directly (see `check_side_condition`) instead of needing a proof for each of a
/// primitive's arguments — the arguments are already bound elsewhere.
///
/// 1. A custom function call becomes its own top-level fact:
///    `(= (lower-bound a b) c)`.
/// 2. A constructor or function argument of a primitive is lifted to a fresh
///    variable: `(!= a (Const 0))` becomes `(= (Const 0) v)`, `(!= a v)`.
/// 3. A container-producing primitive is lifted out of any constructor into its
///    own side condition: `(WrapVec (vec-of e))` becomes `(= (vec-of e) v)`,
///    `(WrapVec v)`. Its proof is a contentless marker, which can't ride a
///    congruence step under the constructor.
///
/// A top-level primitive fact — an `Eq` on a primitive application or a bare
/// guard like `(> (+ a 1) 5)` or `(vec-of e)` — is already in normal form (its
/// arguments are normalized in place) and is verified by re-evaluation.
pub(crate) fn proof_form(
    prog: Vec<ResolvedNCommand>,
    fresh: &mut SymbolGen,
) -> Vec<ResolvedNCommand> {
    prog.into_iter()
        .map(|cmd| proof_form_cmd(cmd, fresh))
        .collect()
}

fn proof_form_cmd(cmd: ResolvedNCommand, fresh: &mut SymbolGen) -> ResolvedNCommand {
    cmd.visit_queries(&mut |query| {
        let mut new_query = vec![];
        for fact in query {
            let rewritten = proof_form_fact(fact, &mut new_query, fresh);
            new_query.push(rewritten);
        }
        new_query
    })
}

fn proof_form_fact(
    fact: ResolvedFact,
    res: &mut Vec<ResolvedFact>,
    fresh: &mut SymbolGen,
) -> ResolvedFact {
    match fact {
        ResolvedFact::Eq(
            span,
            ResolvedExpr::Call(span2, head @ ResolvedCall::Func(_), args),
            ResolvedExpr::Var(span3, v),
        ) if head.is_custom_func() => {
            let mut new_args = vec![];
            for arg in args {
                new_args.push(proof_form_expr(arg, res, fresh));
            }
            ResolvedFact::Eq(
                span,
                ResolvedExpr::Call(span2, head, new_args),
                ResolvedExpr::Var(span3, v),
            )
        }
        GenericFact::Eq(span, generic_expr, generic_expr2) => GenericFact::Eq(
            span,
            proof_form_expr(generic_expr, res, fresh),
            proof_form_expr(generic_expr2, res, fresh),
        ),
        GenericFact::Fact(generic_expr) => {
            GenericFact::Fact(proof_form_expr(generic_expr, res, fresh))
        }
    }
}

fn proof_form_expr(
    fact: ResolvedExpr,
    res: &mut Vec<ResolvedFact>,
    fresh: &mut SymbolGen,
) -> ResolvedExpr {
    match fact {
        ref fact @ ResolvedExpr::Call(
            ref span,
            ref head @ ResolvedCall::Func(ref func_type),
            ref args,
        ) if head.is_custom_func() => {
            // bind this to a new variable
            let new_args = args
                .iter()
                .map(|expr| proof_form_expr(expr.clone(), res, fresh))
                .collect();
            let resolved = GenericExpr::Var(
                span.clone(),
                ResolvedVar {
                    name: fresh.fresh("n"),
                    sort: func_type.outputs[0].clone(),
                    is_global_ref: false,
                },
            );
            res.push(ResolvedFact::Eq(
                span.clone(),
                ResolvedExpr::Call(span.clone(), head.clone(), new_args),
                resolved.clone(),
            ));
            log::warn!(
                "Input program not in proof normal form! All function calls must be top-level in query.
            Original fact: {fact}
            New top level fact: {}
            Replace with new variable {}
                ",
                res.last().unwrap(),
                resolved
            );

            resolved
        }
        ResolvedExpr::Call(span, head @ ResolvedCall::Primitive(_), args) => {
            // Normalize the whole argument first: a constructor may itself
            // contain container primitives that must become side conditions.
            // Custom functions are already lifted by recursion; lift any
            // remaining constructor call or global so the primitive can be
            // re-evaluated over local variables. Globals later become view
            // lookups, which cannot remain inside a container side condition.
            let mut new_args = vec![];
            for arg in args {
                let normalized = proof_form_expr(arg, res, fresh);
                if matches!(&normalized, ResolvedExpr::Call(_, ResolvedCall::Func(_), _))
                    || matches!(&normalized, ResolvedExpr::Var(_, var) if var.is_global_ref)
                {
                    let arg_span = normalized.span();
                    let fresh_var = GenericExpr::Var(
                        arg_span.clone(),
                        ResolvedVar {
                            name: fresh.fresh("v"),
                            sort: normalized.output_type(),
                            is_global_ref: false,
                        },
                    );
                    res.push(ResolvedFact::Eq(
                        arg_span.clone(),
                        normalized,
                        fresh_var.clone(),
                    ));
                    new_args.push(fresh_var);
                } else {
                    new_args.push(normalized);
                }
            }
            ResolvedExpr::Call(span, head, new_args)
        }
        ResolvedExpr::Call(span, head, args) => {
            // `head` is a constructor here (custom functions and primitives are
            // matched above). A container-producing primitive can't sit under a
            // constructor in proof normal form — it has no anchored proof and
            // can't ride a congruence step — so lift such an argument into its
            // own side-condition binding `(= (prim ...) v)` and pass `v`.
            let mut new_args = vec![];
            for arg in args {
                let normalized = proof_form_expr(arg, res, fresh);
                let lift = matches!(
                    &normalized,
                    ResolvedExpr::Call(_, ResolvedCall::Primitive(p), _)
                        if p.output().is_eq_container_sort()
                );
                if lift {
                    let (arg_span, sort) = match &normalized {
                        ResolvedExpr::Call(s, ResolvedCall::Primitive(p), _) => {
                            (s.clone(), p.output().clone())
                        }
                        _ => unreachable!(),
                    };
                    let fresh_var = GenericExpr::Var(
                        arg_span.clone(),
                        ResolvedVar {
                            name: fresh.fresh("v"),
                            sort,
                            is_global_ref: false,
                        },
                    );
                    res.push(ResolvedFact::Eq(arg_span, normalized, fresh_var.clone()));
                    new_args.push(fresh_var);
                } else {
                    new_args.push(normalized);
                }
            }
            ResolvedExpr::Call(span, head, new_args)
        }
        ResolvedExpr::Lit(..) | ResolvedExpr::Var(..) => fact,
    }
}
