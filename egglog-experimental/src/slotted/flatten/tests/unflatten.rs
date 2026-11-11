use super::*;
use crate::slotted::proofs::checker::check_proof_in_program as check_proof;
use crate::slotted::proofs::context::ColumnKind;
use egglog::TermDag;

#[test]
fn congruence_restores_binders_in_independent_scopes() {
    let mut dag = TermDag::default();
    let mut program = ProofContext::default();
    program.add_constructor("Start", vec![]);
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
    program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
    program.add_constructor("Box", vec![ColumnKind::Child]);
    program.add_let(&mut dag, "input", "(Box (Start))").unwrap();
    program
        .add_rewrite(
            &mut dag,
            "(rewrite (Start) (Pair (Lam $x (V $x)) (Lam $x (V $x))) :name duplicate)",
        )
        .unwrap();
    program
        .add_let(&mut dag, "target", "(Pair (Lam $0 (V $0)) (Lam $0 (V $0)))")
        .unwrap();
    let target = program.lets.shift_remove("target").unwrap();
    let start = dag.app("Start".into(), vec![]);
    let slot = crate::slotted::proofs::terms::slot_term(&mut dag, 0);
    let mut store = SlottedProofStore::new(dag);
    let root = store.fiat(program.lets["input"], program.lets["input"]);
    let exists = store.project(root, 0).unwrap();
    let rewrite = store.rule(
        Proposition::new(start, target),
        "duplicate".into(),
        [("$x".into(), slot)].into_iter().collect(),
        vec![RulePremise::Equality(exists)],
    );
    let proof = store.congr(root, 0, rewrite).unwrap();
    check_proof(&mut store, &program, proof).unwrap();
    let expected = store.proposition(proof).clone();
    let (mut store, proof) = lift(store, &program, &program, proof).unwrap();
    check_proof(&mut store, &program, proof).unwrap();
    assert_eq!(store.proposition(proof), &expected);
}

#[test]
fn refreshed_source_unions_replay_with_exact_endpoints() {
    let mut dag = TermDag::default();
    let mut program = ProofContext::default();
    program.add_constructor("V", vec![ColumnKind::Var]);
    program.add_constructor("Lam", vec![ColumnKind::Binder, ColumnKind::Child]);
    program
        .add_union(&mut dag, "(Lam $0 (V $0))", "(Lam $1 (V $2))")
        .unwrap();
    let mut flat = program.clone();
    flat.unions[0].lhs = program.refresh_binders(&mut dag, program.unions[0].lhs);
    flat.unions[0].rhs = program.refresh_binders(&mut dag, program.unions[0].rhs);
    let mut store = SlottedProofStore::new(dag);
    let proof = store.fiat(flat.unions[0].lhs, flat.unions[0].rhs);
    let expected = store.proposition(proof).clone();
    let (mut store, proof) = lift(store, &program, &flat, proof).unwrap();
    assert_eq!(store.proposition(proof), &expected);
    check_proof(&mut store, &program, proof).unwrap();
}

#[test]
fn shared_source_axioms_do_not_expand_into_trees() {
    for depth in [4, 48] {
        let mut dag = TermDag::default();
        let mut program = ProofContext::default();
        program.add_constructor("Z", vec![]);
        program.add_constructor("Pair", vec![ColumnKind::Child; 2]);
        let leaf = dag.app("Z".into(), vec![]);
        let mut term = leaf;
        for _ in 0..depth {
            term = dag.app("Pair".into(), vec![term, term]);
        }
        program.lets.insert("input".into(), term);
        let size = dag.size();
        let mut store = SlottedProofStore::new(dag);
        let proof = store.fiat(leaf, leaf);
        let (mut store, proof) = lift(store, &program, &program, proof).unwrap();
        assert!(store.len() < 5 * size);
        assert_eq!(store.proposition(proof), &Proposition::new(leaf, leaf));
        // Sorting in the checker visits tree occurrences. The large case checks
        // that reconstruction itself stays proportional to the shared DAG.
        if depth == 4 {
            check_proof(&mut store, &program, proof).unwrap();
        }
    }
}
