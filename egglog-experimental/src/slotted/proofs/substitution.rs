//! Capture-avoiding substitution on source terms, independent of graph state.

use super::context::{ColumnKind, ProofContext, check_term_sort};
use super::terms::{FreshSlots, all_slots, slot_of, slot_term};
use crate::slotted::var_sort::VarSort;
use egglog::ast::Span;
use egglog::constraint::{SimpleTypeConstraint, TypeConstraint};
use egglog::prelude::BaseSort;
use egglog::{ArcSort, EGraph, Primitive, PurePrim, PureState, Term, TermDag, TermId, Value};
use std::collections::BTreeMap;
use std::sync::Arc;

/// Register the source substitution validator for each carrier signature.
pub(super) fn register(graph: &mut EGraph, context: &Arc<ProofContext>) {
    let sorts: std::collections::BTreeSet<_> = context
        .constructors
        .values()
        .map(|op| op.sort.clone())
        .collect();
    for name in sorts {
        let sort = graph.get_sort_by_name(&name).unwrap().clone();
        let context = context.clone();
        graph.add_pure_primitive(
            Substitution(sort),
            Some(Arc::new(move |dag, arguments| {
                let [body, variable, replacement] = arguments else {
                    return None;
                };
                let variable = slot_of(dag, *variable)?;
                substitute(&context, dag, *body, variable, *replacement).ok()
            })),
        );
    }
}

#[derive(Clone)]
struct Substitution(ArcSort);

impl Primitive for Substitution {
    fn name(&self) -> &str {
        "subst"
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        SimpleTypeConstraint::new(
            self.name(),
            vec![
                self.0.clone(),
                VarSort.to_arcsort(),
                self.0.clone(),
                self.0.clone(),
            ],
            span.clone(),
        )
        .into_box()
    }
}

impl PurePrim for Substitution {
    fn apply(&self, _: PureState<'_, '_>, _: &[Value]) -> Option<Value> {
        None
    }
}

/// Substitute free occurrences of a carrier's variable constructor. Binder
/// columns only scope their following child; payloads and other children retain
/// their meaning. The replacement is never traversed under the body's binders.
pub(in crate::slotted) fn substitute(
    context: &ProofContext,
    dag: &mut TermDag,
    body: TermId,
    variable: i64,
    replacement: TermId,
) -> Result<TermId, String> {
    let sort = check_term_sort(context, dag, body, None)?;
    check_term_sort(context, dag, replacement, Some(&sort))?;
    let mut worker = Substitute {
        context,
        variable,
        replacement,
        replacement_free: context.free_slots(dag, replacement),
        fresh: FreshSlots::new(
            all_slots(dag, body)
                .into_iter()
                .chain(all_slots(dag, replacement))
                .chain([variable]),
        ),
        memo: BTreeMap::new(),
    };
    worker.term(dag, body, &BTreeMap::new())
}

struct Substitute<'a> {
    context: &'a ProofContext,
    variable: i64,
    replacement: TermId,
    replacement_free: std::collections::BTreeSet<i64>,
    fresh: FreshSlots,
    // A shared DAG node can occur beneath distinct binding scopes.
    memo: BTreeMap<(TermId, BTreeMap<i64, i64>), TermId>,
}

impl Substitute<'_> {
    fn term(
        &mut self,
        dag: &mut TermDag,
        term: TermId,
        bound: &BTreeMap<i64, i64>,
    ) -> Result<TermId, String> {
        let key = (term, bound.clone());
        if let Some(&result) = self.memo.get(&key) {
            return Ok(result);
        }
        let Term::App(head, arguments) = dag.get(term).clone() else {
            return Err("substitution body must be a carrier term".into());
        };
        let op = &self.context.constructors[&head];
        if op.columns == [ColumnKind::Var] {
            let slot = slot_of(dag, arguments[0]).ok_or("expected a variable name")?;
            let result = if let Some(&renamed) = bound.get(&slot) {
                let renamed = slot_term(dag, renamed);
                dag.app(head, vec![renamed])
            } else if slot == self.variable {
                self.replacement
            } else {
                term
            };
            self.memo.insert(key, result);
            return Ok(result);
        }
        let covered = op
            .columns
            .iter()
            .rposition(|c| *c == ColumnKind::Binder)
            .and_then(|last| {
                op.columns
                    .iter()
                    .enumerate()
                    .skip(last + 1)
                    .find_map(|(i, c)| (*c == ColumnKind::Child).then_some(i))
            });
        let mut inner = bound.clone();
        let mut result = arguments.clone();
        for (i, column) in op.columns.iter().enumerate() {
            if *column == ColumnKind::Binder {
                let name = slot_of(dag, arguments[i]).ok_or("expected a binder name")?;
                let fresh = if self.replacement_free.contains(&name) {
                    self.fresh.fresh()
                } else {
                    name
                };
                inner.insert(name, fresh);
                result[i] = slot_term(dag, fresh);
            }
        }
        for (i, column) in op.columns.iter().enumerate() {
            if *column == ColumnKind::Child {
                result[i] = self.term(
                    dag,
                    arguments[i],
                    if Some(i) == covered { &inner } else { bound },
                )?;
            }
        }
        let result = dag.app(head, result);
        self.memo.insert(key, result);
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::slotted::proofs::resolve_program;
    use egglog::ast::parse_sexps;

    fn terms(source: &str) -> (ProofContext, TermDag) {
        let program = resolve_program(&parse_sexps(None, source).unwrap()).unwrap();
        let mut dag = TermDag::default();
        let context = program.context(&mut dag, BTreeMap::new()).unwrap();
        (context, dag)
    }

    #[test]
    fn avoids_capture_and_respects_shadowing() {
        let (context, mut dag) = terms(
            "(datatype E (V Var) (Lam Var E :binder 0) (Pair E E))
             (let body (Pair (Lam $1 (V $0)) (Lam $0 (V $0))))
             (let replacement (V $1))
             (let expected (Pair (Lam $2 (V $1)) (Lam $0 (V $0))))",
        );
        let result = substitute(
            &context,
            &mut dag,
            context.lets["body"],
            0,
            context.lets["replacement"],
        )
        .unwrap();
        assert!(context.alpha_eq(&mut dag, result, context.lets["expected"]));
        assert_eq!(context.free_slots(&dag, result), [1].into());
    }

    #[test]
    fn scopes_multiple_binders_past_payloads_and_preserves_uncovered_children() {
        let (context, mut dag) = terms(
            "(datatype E (V Var) (Pair E E)
                 (Bind E Var String Var i64 E E :binder 1 2))
             (let body (Bind (V $0) $0 \"payload\" $1 7 (Pair (V $0) (V $1)) (V $0)))
             (let replacement (V $1))
             (let expected (Bind (V $1) $0 \"payload\" $2 7 (Pair (V $0) (V $2)) (V $1)))",
        );
        let result = substitute(
            &context,
            &mut dag,
            context.lets["body"],
            0,
            context.lets["replacement"],
        )
        .unwrap();
        assert!(context.alpha_eq(&mut dag, result, context.lets["expected"]));
    }

    #[test]
    fn rejects_replacement_of_another_carrier() {
        let (context, mut dag) = terms(
            "(datatype E (V Var)) (datatype Other (A))
             (let body (V $0)) (let replacement (A))",
        );
        assert!(
            substitute(
                &context,
                &mut dag,
                context.lets["body"],
                0,
                context.lets["replacement"]
            )
            .is_err()
        );
    }

    #[test]
    fn source_rewrites_resolve_the_substitution_validator() {
        let source = resolve_program(
            &parse_sexps(
                None,
                "(datatype E (V Var) (Let E Var E :binder 1))
             (rewrite (Let value $x body) (subst body $x value) :name beta)",
            )
            .unwrap(),
        )
        .unwrap();
        let mut dag = TermDag::default();
        let context = source.context(&mut dag, BTreeMap::new()).unwrap();
        let (_, rhs) = context.rewrites["beta"].endpoints();
        let egglog::ast::ResolvedExpr::Call(_, egglog::ResolvedCall::Primitive(head), _) = rhs
        else {
            panic!("substitution must resolve to a primitive")
        };
        assert!(head.validator().is_some());
    }

    #[test]
    fn rule_proof_checks_substitution_and_rejects_a_captured_result() {
        use crate::slotted::proofs::{RulePremise, SlottedProofStore, check_proof};
        use egglog::proof::Proposition;
        let source = resolve_program(
            &parse_sexps(
                None,
                "(datatype E (V Var) (Lam Var E :binder 0) (Let E Var E :binder 1))
             (let b (Lam $1 (V $0))) (let replacement (V $1))
             (let input (Let replacement $0 b))
             (rewrite (Let value $x body) (subst body $x value) :name beta)",
            )
            .unwrap(),
        )
        .unwrap();
        let mut store = SlottedProofStore::default();
        let context = source
            .context(&mut store.term_dag, BTreeMap::new())
            .unwrap();
        let input = context.lets["input"];
        let body = context.lets["b"];
        let replacement = context.lets["replacement"];
        let x = slot_term(&mut store.term_dag, 0);
        let result = substitute(&context, &mut store.term_dag, body, 0, replacement).unwrap();
        let premise = store.fiat(input, input);
        let bindings = [
            ("body".into(), body),
            ("value".into(), replacement),
            ("$x".into(), x),
        ]
        .into_iter()
        .collect();
        let proof = store.rule(
            Proposition::new(input, result),
            "beta".into(),
            bindings,
            vec![RulePremise::Equality(premise)],
        );
        check_proof(&mut store, &source, proof).unwrap();
        let binder = slot_term(&mut store.term_dag, 1);
        let captured = store.term_dag.app("Lam".into(), vec![binder, replacement]);
        let mut corrupted = store.get(proof).clone();
        let crate::slotted::proofs::SlottedProof::Rule(rule) = &mut corrupted else {
            unreachable!()
        };
        rule.proposition.rhs = captured;
        let corrupted = store.add(corrupted);
        assert!(check_proof(&mut store, &source, corrupted).is_err());
    }
}
