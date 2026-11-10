use super::*;
use crate::slotted::proofs::checker::check_proof_in_program as check_proof;
use crate::slotted::proofs::context::{ColumnKind, Union};
use egglog::TermDag;

#[test]
fn rejected_shared_candidates_do_not_render_their_terms() {
    use crate::slotted::proofs::terms::slot_term;

    let mut dag = TermDag::default();
    let mut program = ProofContext::default();
    program.add_constructor("Z", vec![]);
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    program.add_constructor("V", vec![ColumnKind::Var]);
    let mut shared = dag.app("Z".into(), vec![]);
    for _ in 0..32 {
        shared = dag.app("Pair".into(), vec![shared, shared]);
    }
    let slot = slot_term(&mut dag, 0);
    let good = dag.app("V".into(), vec![slot]);
    let slot = slot_term(&mut dag, 1);
    let target = dag.app("V".into(), vec![slot]);
    program.lets.insert("bad".into(), shared);
    program.lets.insert("good".into(), good);
    let mut store = SlottedProofStore::new(dag);
    let bad = store.fiat(shared, shared);
    let good = store.fiat(good, good);
    let mut witnesses = Witnesses::new(&mut store, &program, vec![bad, good]);
    // Candidate order is by term ID, so the large shared terms fail first.
    let proof = witnesses.exists(target).unwrap();
    assert_eq!(witnesses.store.proposition(proof).rhs, target);
    check_proof(&mut store, &program, proof).unwrap();
}

#[test]
fn failed_equality_reports_both_terms() {
    let mut dag = TermDag::default();
    let mut program = ProofContext::default();
    for head in ["F", "G"] {
        program.add_constructor(head, vec![]);
    }
    let from = dag.app("F".into(), vec![]);
    let to = dag.app("G".into(), vec![]);
    program.lets.insert("input".into(), from);
    let mut store = SlottedProofStore::new(dag);
    let root = store.fiat(from, from);
    let mut witnesses = Witnesses::new(&mut store, &program, vec![root]);
    assert_eq!(
        witnesses.equality(from, to).unwrap_err(),
        "cannot reconstruct (F) = (G) from matched atoms"
    );
}

#[test]
fn witness_search_crosses_incompatible_shared_shapes() {
    for depth in [4, 32] {
        let mut dag = TermDag::default();
        let mut program = ProofContext::default();
        for head in ["Z", "M", "T"] {
            program.add_constructor(head, vec![]);
        }
        program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
        let mut shared = dag.app("Z".into(), vec![]);
        for _ in 0..depth {
            shared = dag.app("Pair".into(), vec![shared, shared]);
        }
        let middle = dag.app("M".into(), vec![]);
        let target = dag.app("T".into(), vec![]);
        program.lets.insert("input".into(), shared);
        program.unions.extend([
            Union {
                lhs: shared,
                rhs: middle,
            },
            Union {
                lhs: middle,
                rhs: target,
            },
        ]);
        let mut store = SlottedProofStore::new(dag);
        let root = store.fiat(shared, shared);
        let first = store.fiat(shared, middle);
        let second = store.fiat(middle, target);
        let mut witnesses = Witnesses::new(&mut store, &program, vec![root, first, second]);
        // Shape mismatch must skip costly Alpha but still follow both equalities.
        let proof = witnesses.equality(shared, target).unwrap();
        assert_eq!(
            witnesses.store.proposition(proof),
            &Proposition::new(shared, target)
        );
        // The checker recursively sorts every tree occurrence. Check the small
        // case; the deep DAG exercises reconstruction without expanding that tree.
        if depth == 4 {
            check_proof(&mut store, &program, proof).unwrap();
        }
    }
}

#[test]
fn reconstructs_nested_binders_after_a_shape_change() {
    let mut dag = TermDag::default();
    let mut program = ProofContext::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    for head in ["F", "G"] {
        program.add_constructor(head, vec![ColumnKind::Child]);
    }
    program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
    program
        .add_let(&mut dag, "input", "(F (G (Lam $0 (V $0))))")
        .unwrap();
    program
        .add_let(&mut dag, "target", "(F (Lam $3 (Lam $4 (V $4))))")
        .unwrap();
    program
        .add_union(&mut dag, "(G (Lam $1 (V $1)))", "(Lam $2 (Lam $1 (V $1)))")
        .unwrap();
    let target = program.lets.shift_remove("target").unwrap();
    let mut store = SlottedProofStore::new(dag);
    let root = store.fiat(program.lets["input"], program.lets["input"]);
    let union = store.fiat(program.unions[0].lhs, program.unions[0].rhs);
    let mut witnesses = Witnesses::new(&mut store, &program, vec![root, union]);
    let proof = witnesses.exists(target).unwrap();
    assert_eq!(witnesses.store.proposition(proof).rhs, target);
    let equality = witnesses.equality(program.lets["input"], target).unwrap();
    assert_eq!(
        witnesses.store.proposition(equality).lhs,
        program.lets["input"]
    );
    assert_eq!(witnesses.store.proposition(equality).rhs, target);
    check_proof(&mut store, &program, proof).unwrap();
    check_proof(&mut store, &program, equality).unwrap();
}

#[test]
fn reconstruction_preserves_shared_sibling_names() {
    let mut dag = TermDag::default();
    let mut program = ProofContext::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    program
        .add_let(&mut dag, "input", "(Pair (V $0) (V $0))")
        .unwrap();
    program
        .add_let(&mut dag, "target", "(Pair (V $1) (V $2))")
        .unwrap();
    let target = program.lets.shift_remove("target").unwrap();
    let mut store = SlottedProofStore::new(dag);
    let root = store.fiat(program.lets["input"], program.lets["input"]);
    let mut witnesses = Witnesses::new(&mut store, &program, vec![root]);
    assert!(witnesses.exists(target).is_err());
}

#[test]
fn reconstruction_tries_equal_children_before_renaming_them() {
    let mut dag = TermDag::default();
    let mut program = ProofContext::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    for head in ["F", "G", "H"] {
        program.add_constructor(head, vec![ColumnKind::Child]);
    }
    program
        .add_let(&mut dag, "input", "(Pair (V $0) (G (V $0)))")
        .unwrap();
    program
        .add_let(&mut dag, "target", "(Pair (V $0) (F (V $0)))")
        .unwrap();
    for (lhs, rhs) in [
        ("(G (V $0))", "(H (V $1))"),
        ("(G (V $0))", "(H (V $0))"),
        ("(H (V $0))", "(F (V $0))"),
    ] {
        program.add_union(&mut dag, lhs, rhs).unwrap();
    }
    let target = program.lets.shift_remove("target").unwrap();
    let mut store = SlottedProofStore::new(dag);
    let root = store.fiat(program.lets["input"], program.lets["input"]);
    let mut premises = vec![root];
    for union in &program.unions {
        premises.push(store.fiat(union.lhs, union.rhs));
    }
    let mut witnesses = Witnesses::new(&mut store, &program, premises);
    let proof = witnesses.exists(target).unwrap();
    assert_eq!(witnesses.store.proposition(proof).rhs, target);
    check_proof(&mut store, &program, proof).unwrap();
}

#[test]
fn renaming_guard_lifts_child_equalities_through_congruence() {
    let mut dag = TermDag::default();
    let mut program = ProofContext::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    for head in ["F", "G", "H"] {
        program.add_constructor(head, vec![ColumnKind::Child]);
    }
    program.add_let(&mut dag, "a", "(F (G (V $0)))").unwrap();
    program.add_let(&mut dag, "b", "(F (H (V $0)))").unwrap();
    program.add_let(&mut dag, "input", "(Pair a b)").unwrap();
    program
        .add_union(&mut dag, "(G (V $0))", "(H (V $0))")
        .unwrap();
    let mut store = SlottedProofStore::new(dag);
    let root = store.fiat(program.lets["input"], program.lets["input"]);
    let union = store.fiat(program.unions[0].lhs, program.unions[0].rhs);
    let mut witnesses = Witnesses::new(&mut store, &program, vec![root, union]);
    let proof = witnesses
        .renaming_equality(program.lets["a"], program.lets["b"])
        .unwrap();
    check_proof(&mut store, &program, proof).unwrap();
}
