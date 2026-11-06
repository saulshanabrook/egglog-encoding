use crate::slotted::proofs::terms::slot_term;
use crate::slotted::proofs::{
    ResolvedSlottedProgram, RulePremise, SlottedProofStore, check_proof, resolve_program,
};
use egglog::ast::{Literal, ResolvedExpr, ResolvedFact, ResolvedNCommand, parse_sexps};
use egglog::proof::Proposition;
use egglog::{PrimitiveValidator, ResolvedCall, TermDag, TermId};

fn program(source: &str) -> ResolvedSlottedProgram {
    resolve_program(&parse_sexps(None, source).unwrap()).unwrap()
}

fn validator(source: &ResolvedSlottedProgram) -> PrimitiveValidator {
    let rule = source
        .commands
        .iter()
        .find_map(|command| match command {
            ResolvedNCommand::NormRule { rule } => Some(rule),
            _ => None,
        })
        .unwrap();
    let ResolvedFact::Fact(ResolvedExpr::Call(_, ResolvedCall::Primitive(head), _)) = &rule.body[1]
    else {
        panic!("expected a resolved guard")
    };
    head.validator()
        .expect("source resolution must attach the validator")
        .clone()
}

fn variable(dag: &mut TermDag, slot: i64) -> TermId {
    let slot = slot_term(dag, slot);
    dag.app("V".into(), vec![slot])
}

#[test]
fn resolved_guards_have_validators_before_proof_checking() {
    for (guard, valid) in [
        ("(renaming-= x y)", true),
        ("(renaming-!= x y)", false),
        ("(!= x y)", false),
        ("(free $0 x)", false),
        ("(not-free $0 x)", true),
        ("(free-names-are x)", true),
    ] {
        let source = program(&format!(
            "(datatype E (V Var) (Lam Var E :binder 0) (Pair E E) (Hit))
             (rewrite (Pair x y) (Hit) :when ({guard}) :name r)"
        ));
        for slot in [0, 10, i64::MIN] {
            let mut dag = TermDag::default();
            let a = slot_term(&mut dag, slot);
            let b = slot_term(&mut dag, slot + 1);
            let va = variable(&mut dag, slot);
            let vb = variable(&mut dag, slot + 1);
            let lhs = dag.app("Lam".into(), vec![a, va]);
            let rhs = dag.app("Lam".into(), vec![b, vb]);
            let args = if guard.starts_with("(free-names-are") {
                vec![lhs]
            } else if guard.starts_with("(free ") || guard.starts_with("(not-free ") {
                vec![a, lhs]
            } else {
                vec![lhs, rhs]
            };
            let unit = dag.lit(Literal::Unit);
            assert_eq!(
                validator(&source)(&mut dag, &args),
                valid.then_some(unit),
                "{guard}"
            );
        }
    }
}

#[test]
fn guards_in_earlier_rules_use_later_active_binder_declarations() {
    let prefix = "(datatype E (V Var) (Pair E E) (A) (B) (Hit))
                  (let a (A)) (let b (B)) (let input (Pair a b))
                  (rewrite (Pair x y) (Hit) :when ((renaming-= x y)) :name r)";
    let earlier = program(prefix);
    let source = program(&format!(
        "{prefix}
         (push) (constructor Lam (E E) E) (pop)
         (push) (constructor Lam (Var E) E :binder 0)
         (union a (Pair (Lam $0 (V $0)) (V $0)))
         (union b (Pair (Lam $2 (V $2)) (V $3)))"
    ));
    let mut dag = TermDag::default();
    let s0 = slot_term(&mut dag, 0);
    let s2 = slot_term(&mut dag, 2);
    let v0 = variable(&mut dag, 0);
    let v2 = variable(&mut dag, 2);
    let v3 = variable(&mut dag, 3);
    let l0 = dag.app("Lam".into(), vec![s0, v0]);
    let l2 = dag.app("Lam".into(), vec![s2, v2]);
    let lhs = dag.app("Pair".into(), vec![l0, v0]);
    let rhs = dag.app("Pair".into(), vec![l2, v3]);
    let unit = dag.lit(Literal::Unit);
    assert_eq!(validator(&source)(&mut dag, &[lhs, rhs]), Some(unit));
    assert_eq!(validator(&earlier)(&mut dag, &[lhs, rhs]), None);

    let a = dag.app("A".into(), vec![]);
    let b = dag.app("B".into(), vec![]);
    let input = dag.app("Pair".into(), vec![a, b]);
    let hit = dag.app("Hit".into(), vec![]);
    let mut store = SlottedProofStore::new(dag);
    let root = store.fiat(input, input);
    let left = store.fiat(a, lhs);
    let right = store.fiat(b, rhs);
    let proof = store.rule(
        Proposition::new(input, hit),
        "r".into(),
        [("x".into(), a), ("y".into(), b)].into_iter().collect(),
        vec![
            RulePremise::Equality(root),
            RulePremise::RenamingEq { left, right },
        ],
    );
    check_proof(&mut store, &source, proof).unwrap();
    let simplified = store.simplify(proof);
    check_proof(&mut store, &source, simplified).unwrap();
}
