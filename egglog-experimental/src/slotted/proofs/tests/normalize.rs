use super::*;
use crate::slotted::proofs::checker::check_proof_in_program as check_proof;
use crate::slotted::proofs::context::{ColumnKind, ProofContext};
use crate::slotted::proofs::terms::Renaming;
use egglog::TermDag;
use egglog::proof::Proposition;
use egglog::util::IndexMap;

#[test]
fn irrelevant_coordinates_do_not_expand_shared_proof_diamonds() {
    let mut dag = TermDag::default();
    let mut program = ProofContext::default();
    program.add_constructor("A", vec![]);
    program.add_let(&mut dag, "a", "(A)").unwrap();
    let a = program.lets["a"];
    let mut store = SlottedProofStore::new(dag);
    let base = store.fiat(a, a);
    let mut proof = base;
    for slot in 0..24 {
        let renamed = store.equivariance(
            proof,
            Renaming::new([(2 * slot, 2 * slot + 1), (2 * slot + 1, 2 * slot)]).unwrap(),
        );
        proof = store.trans(proof, renamed).unwrap();
    }
    check_proof(&mut store, &program, proof).unwrap();
    let normalized = store.simplify(proof);
    assert_eq!(normalized, base);
    check_proof(&mut store, &program, normalized).unwrap();
    assert!(store.len() < 100);
}

#[test]
fn transported_rules_keep_renaming_premises_in_source_coordinates() {
    let mut dag = TermDag::default();
    let mut program = ProofContext::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    for name in ["F", "G", "H"] {
        program.add_constructor(name, vec![ColumnKind::Child]);
    }
    for (name, term) in [
        ("a", "(F (V $0))"),
        ("b", "(H (V $1))"),
        ("input", "(Pair a b)"),
    ] {
        program.add_let(&mut dag, name, term).unwrap();
    }
    program.add_union(&mut dag, "a", "(G (V $0))").unwrap();
    program.add_union(&mut dag, "b", "(G (V $1))").unwrap();
    program
        .add_rewrite(
            &mut dag,
            r#"(rewrite (Pair x y) x :when ((renaming-= x y)) :name "r")"#,
        )
        .unwrap();
    let (a, b, input) = (program.lets["a"], program.lets["b"], program.lets["input"]);
    let mut store = SlottedProofStore::new(dag);
    let root = store.fiat(input, input);
    let left = store.fiat(a, program.unions[0].rhs);
    let right = store.fiat(b, program.unions[1].rhs);
    let left_reversed = store.sym(left);
    let left_twice = store.sym(left_reversed);
    let right_reversed = store.sym(right);
    let right_twice = store.sym(right_reversed);
    let substitution: IndexMap<_, _> = [("x".into(), a), ("y".into(), b)].into_iter().collect();
    let source = store.rule(
        Proposition::new(input, a),
        "r".into(),
        substitution.clone(),
        vec![
            RulePremise::Equality(root),
            RulePremise::RenamingEq {
                left: left_twice,
                right: right_twice,
            },
        ],
    );
    let transported = store.equivariance(source, Renaming::new([(0, 1), (1, 2), (2, 0)]).unwrap());
    let expected = check_proof(&mut store, &program, transported).unwrap();
    let normalized = store.simplify(transported);
    assert_eq!(
        check_proof(&mut store, &program, normalized).unwrap(),
        expected
    );
    let SlottedProof::Equivariance { proof, .. } = store.get(normalized) else {
        panic!("the rule conclusion requires a nonidentity renaming")
    };
    let SlottedProof::Rule(rule) = store.get(*proof) else {
        panic!("equivariance must remain above the source rule")
    };
    assert_eq!(rule.proposition, Proposition::new(input, a));
    assert_eq!(rule.substitution, substitution);
    assert_eq!(
        rule.premises,
        vec![
            RulePremise::Equality(root),
            RulePremise::RenamingEq { left, right }
        ]
    );
}

#[test]
fn transports_binder_children_and_preserves_source_axioms() {
    let mut dag = TermDag::default();
    let mut program = ProofContext::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("F", vec![ColumnKind::Child]);
    program.add_constructor("G", vec![ColumnKind::Child]);
    program.add_constructor("Wrap", vec![ColumnKind::Child]);
    program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
    for (name, term) in [
        ("f", "(F (V $0))"),
        ("g", "(G (V $0))"),
        ("lam", "(Lam $0 (F (V $0)))"),
        ("wrap", "(Wrap (Lam $0 (F (V $0))))"),
    ] {
        program.add_let(&mut dag, name, term).unwrap();
    }
    program.add_union(&mut dag, "f", "g").unwrap();
    let mut store = SlottedProofStore::new(dag);
    let union = store.fiat(program.lets["f"], program.lets["g"]);
    let lam = store.fiat(program.lets["lam"], program.lets["lam"]);
    let lam = store.congr(lam, 1, union).unwrap();
    let wrap = store.fiat(program.lets["wrap"], program.lets["wrap"]);
    let wrap = store.congr(wrap, 0, lam).unwrap();
    let root = store.equivariance(wrap, Renaming::new([(0, 1), (1, 2), (2, 0)]).unwrap());
    let expected = check_proof(&mut store, &program, root).unwrap();
    let normalized = store.simplify(root);
    assert_eq!(
        check_proof(&mut store, &program, normalized).unwrap(),
        expected
    );
    assert_eq!(
        store.term_dag.to_string(expected.rhs),
        "(Wrap (Lam $1 (G (V $1))))"
    );
    let SlottedProof::Equivariance { proof, .. } = store.get(normalized) else {
        panic!("keep the transport around the shared compound proof")
    };
    assert_eq!(*proof, wrap);
    let again = store.simplify(normalized);
    assert_eq!(store.proposition(again), &expected);
}

#[test]
fn inverse_transports_cancel_without_trusting_new_fiats() {
    let mut dag = TermDag::default();
    let mut program = ProofContext::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("F", vec![ColumnKind::Child]);
    program.add_let(&mut dag, "f", "(F (V $0))").unwrap();
    let mut store = SlottedProofStore::new(dag);
    let source = store.fiat(program.lets["f"], program.lets["f"]);
    let rho = Renaming::new([(0, 1), (1, 2), (2, 0)]).unwrap();
    let first = store.equivariance(source, rho.clone());
    let second = store.equivariance(first, rho.inverse());
    let normalized = store.simplify(second);
    assert_eq!(normalized, source);
    check_proof(&mut store, &program, normalized).unwrap();
    let transported = store.simplify(first);
    let p = store.proposition(transported).clone();
    let forged = store.fiat(p.lhs, p.rhs);
    assert!(check_proof(&mut store, &program, forged).is_err());
    check_proof(&mut store, &program, transported).unwrap();
}

#[test]
fn reflexive_detours_are_pruned_before_transporting_shared_proofs() {
    let mut dag = TermDag::default();
    let mut program = ProofContext::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    let mut term = None;
    for slot in 0..24 {
        let slot = super::super::terms::slot_term(&mut dag, slot);
        let body = dag.app("V".into(), vec![slot]);
        let lambda = dag.app("Lam".into(), vec![slot, body]);
        term = Some(match term {
            None => lambda,
            Some(term) => dag.app("Pair".into(), vec![term, lambda]),
        });
    }
    let term = term.unwrap();
    program.lets.insert("input".into(), term);
    let mut store = SlottedProofStore::new(dag);
    let mut proof = store.fiat(term, term);
    for slot in 0..12 {
        let renamed = store.equivariance(
            proof,
            Renaming::new([(2 * slot, 2 * slot + 1), (2 * slot + 1, 2 * slot)]).unwrap(),
        );
        let restored = store.alpha(renamed, term);
        let restored = store.sym(restored);
        let restored = store.alpha(restored, term);
        let restored = store.sym(restored);
        proof = store.trans(restored, proof).unwrap();
    }
    check_proof(&mut store, &program, proof).unwrap();
    let size = store.len();
    let normalized = store.simplify(proof);
    assert_eq!(store.proposition(normalized), &Proposition::new(term, term));
    check_proof(&mut store, &program, normalized).unwrap();
    assert!(
        store.len() < size + 100,
        "discarded detours must not be transported"
    );
}

#[test]
fn nonreflexive_transport_diamonds_preserve_proof_sharing() {
    let mut dag = TermDag::default();
    let mut program = ProofContext::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    program.add_constructor("F", vec![ColumnKind::Child]);
    program.add_constructor("G", vec![ColumnKind::Child]);
    let mut term = None;
    for slot in 0..16 {
        let slot = super::super::terms::slot_term(&mut dag, slot);
        let body = dag.app("V".into(), vec![slot]);
        let lambda = dag.app("Lam".into(), vec![slot, body]);
        term = Some(match term {
            None => lambda,
            Some(term) => dag.app("Pair".into(), vec![term, lambda]),
        });
    }
    let body = term.unwrap();
    program.lets.insert("body".into(), body);
    program.add_union(&mut dag, "(F body)", "(G body)").unwrap();
    let mut left = program.unions[0].lhs;
    let mut store = SlottedProofStore::new(dag);
    let mut proof = store.fiat(left, program.unions[0].rhs);
    for slot in 0..8 {
        let right = store.proposition(proof).rhs;
        let renamed = store.equivariance(
            proof,
            Renaming::new([(2 * slot, 2 * slot + 1), (2 * slot + 1, 2 * slot)]).unwrap(),
        );
        let restored = store.alpha(renamed, right);
        let restored = store.sym(restored);
        let restored = store.alpha(restored, left);
        let restored = store.sym(restored);
        left = store.term_dag.app("Pair".into(), vec![left, left]);
        let parent = store.fiat(left, left);
        let first = store.congr(parent, 0, proof).unwrap();
        proof = store.congr(first, 1, restored).unwrap();
    }
    program.lets.insert("input".into(), left);
    let expected = check_proof(&mut store, &program, proof).unwrap();
    let size = store.len();
    let simplified = store.simplify(proof);
    assert_eq!(
        check_proof(&mut store, &program, simplified).unwrap(),
        expected
    );
    assert!(
        store.len() <= size * 2,
        "simplification must preserve DAG sharing"
    );
    assert_eq!(store.simplify(simplified), simplified);
}
