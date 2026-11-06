use super::*;
use crate::slotted::proofs::terms::slot_term;

#[test]
fn shared_renaming_premise_prints_with_a_let_binding() {
    let mut dag = TermDag::default();
    let a = slot_term(&mut dag, 0);
    let b = slot_term(&mut dag, 1);
    let mut store = SlottedProofStore::new(dag);
    let left = store.fiat(a, a);
    let right = store.fiat(b, b);
    let guard = RulePremise::RenamingEq { left, right };
    let proof = store.rule(
        Proposition::new(a, b),
        "r".into(),
        Default::default(),
        vec![guard, guard],
    );
    let text = store.proof_to_string(proof);
    assert!(text.contains("(let prf (RenamingEq"), "{text}");
    assert!(text.contains("(premises prf prf)"), "{text}");
}

#[test]
fn fresh_display_names_cover_permutation_only_coordinates() {
    let mut dag = TermDag::default();
    let a = slot_term(&mut dag, 10);
    dag.var("v1".into());
    let mut store = SlottedProofStore::new(dag)
        .with_slot_names(&BTreeMap::from([("$a".into(), 10), ("$v0".into(), 20)]));
    let refl = store.fiat(a, a);
    let proof = store.equivariance(refl, Renaming::new([(30, 31), (31, 30)]).unwrap());
    assert_eq!(
        store.proof_to_string(proof),
        "(Equivariance (= $a $a) (Fiat (= $a $a)) (renaming ($v2 $v3) ($v3 $v2)))"
    );
}

#[test]
fn malformed_steps_preserve_the_store_and_report_the_conflict() {
    let mut dag = TermDag::default();
    let a = slot_term(&mut dag, 0);
    let b = slot_term(&mut dag, 1);
    let fa = dag.app("F".into(), vec![a]);
    let mut store = SlottedProofStore::new(dag);
    let a_refl = store.fiat(a, a);
    let b_refl = store.fiat(b, b);
    let f_refl = store.fiat(fa, fa);
    let before = store.len();

    assert_eq!(
        store.trans(a_refl, b_refl),
        Err(MalformedStep::MiddleTermMismatch {
            left: "$0".into(),
            right: "$1".into(),
        })
    );
    assert_eq!(
        store.congr(f_refl, 0, b_refl),
        Err(MalformedStep::ChildMismatch {
            child: "$0".into(),
            premise_lhs: "$1".into(),
        })
    );
    for result in [store.congr(a_refl, 0, a_refl), store.project(a_refl, 0)] {
        assert_eq!(
            result,
            Err(MalformedStep::ExpectedApplication { term: "$0".into() })
        );
    }
    for result in [store.congr(f_refl, 1, a_refl), store.project(f_refl, 1)] {
        assert_eq!(
            result,
            Err(MalformedStep::ChildIndexOutOfBounds { index: 1, arity: 1 })
        );
    }
    assert_eq!(store.len(), before);
}

#[test]
fn rule_interning_ignores_substitution_order() {
    let mut dag = TermDag::default();
    let a = slot_term(&mut dag, 0);
    let b = slot_term(&mut dag, 1);
    let mut store = SlottedProofStore::new(dag);
    let left = store.fiat(a, a);
    let right = store.fiat(b, b);
    let bindings = [("x".into(), a), ("y".into(), b)];
    let premise = RulePremise::RenamingEq { left, right };
    let first = store.rule(
        Proposition::new(a, b),
        "r".into(),
        bindings.clone().into_iter().collect(),
        vec![premise],
    );
    let second = store.rule(
        Proposition::new(a, b),
        "r".into(),
        bindings.into_iter().rev().collect(),
        vec![premise],
    );
    assert_eq!(first, second);
}

#[test]
fn ordinary_rules_use_typed_equality_premises() {
    let mut dag = TermDag::default();
    let a = slot_term(&mut dag, 0);
    let mut store = SlottedProofStore::new(dag);
    let premise = store.fiat(a, a);
    let proof = store.ordinary(
        Proposition::new(a, a),
        Justification::Rule {
            name: "r".into(),
            substitution: Default::default(),
            premise_proofs: vec![premise],
        },
    );
    let SlottedProof::Rule(rule) = store.get(proof) else {
        panic!("rules must have typed premises")
    };
    assert_eq!(rule.premises, vec![RulePremise::Equality(premise)]);
    assert_eq!(store.proposition(proof), &Proposition::new(a, a));
    assert_eq!(
        proof,
        store.rule(
            Proposition::new(a, a),
            "r".into(),
            Default::default(),
            vec![RulePremise::Equality(premise)],
        )
    );
}
