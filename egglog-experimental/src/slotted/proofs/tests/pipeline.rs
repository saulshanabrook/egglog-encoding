use super::*;
use crate::slotted::{Compiler, Options, ProofMode, new_egraph_with_proofs};

fn prove_query(source: &str, facts: usize) {
    let mut compiler = Compiler::new(Options {
        proof_mode: ProofMode::Prove,
        ..Default::default()
    });
    let encoded = compiler.compile_program(None, source).unwrap();
    assert_eq!(encoded.proofs.len(), 1);
    assert_eq!(encoded.proofs.values().next().unwrap().claims.len(), facts);
    let outputs = encoded.run(&mut new_egraph_with_proofs()).unwrap();
    assert!(
        outputs
            .iter()
            .any(|output| matches!(output, CommandOutput::UserDefined(_)))
    );
}

#[test]
fn multiple_equalities_and_pattern_variables_share_a_source_witness() {
    prove_query(
        "(datatype E (A) (B) (F E) (G E))
         (let a (F (A))) (let b (G (B)))
         (rewrite (A) (B) :name change)
         (run 1)
         (check (= a (F x)) (= b (G x)) (= x (B)))",
        3,
    );
}

#[test]
fn query_replays_non_involutive_coset_direction() {
    prove_query(
        "(datatype E (V Var) (Triple E E E))
         (let input (Triple (V $a) (V $b) (V $c)))
         (rewrite (Triple a b c) (Triple b c a) :name rotate)
         (run 1)
         (check (= input (Triple (V $b) (V $c) (V $a)))
                (= (Triple (V $b) (V $c) (V $a)) input))",
        2,
    );
}

#[test]
fn shared_slot_and_payload_witnesses_survive_query_instantiation() {
    prove_query(
        "(datatype E (V Var) (F E String i64) (Pair E E))
         (let input (Pair (F (V $a) \"hello\" 7) (F (V $a) \"hello\" 7)))
         (check (= input (Pair x x)) (= x (F (V $s) text number)))",
        2,
    );
}

#[test]
fn payload_witnesses_keep_their_scope_and_may_use_slot_spellings() {
    for payload in ["name", "$a"] {
        prove_query(
            &format!(
                "(datatype E (V Var) (N i64) (Pair E E))
             (let name $a) (let input (Pair (V name) (N 7)))
             (check (= input (Pair (V name) (N {payload}))))"
            ),
            1,
        );
    }
}

#[test]
fn constructor_existence_is_proved_with_the_same_shared_bindings() {
    prove_query(
        "(datatype E (A) (F E) (G E))
         (let a (F (A))) (let b (G (A)))
         (check (F x) (G x))",
        2,
    );
}

#[test]
fn conjunction_cannot_combine_incompatible_witnesses() {
    let mut compiler = Compiler::new(Options {
        proof_mode: ProofMode::Prove,
        ..Default::default()
    });
    let encoded = compiler
        .compile_program(
            None,
            "(datatype E (A) (B) (F E) (G E))
         (let a (F (A))) (let b (G (B)))
         (check (= a (F x)) (= b (G x)))",
        )
        .unwrap();
    assert!(encoded.run(&mut new_egraph_with_proofs()).is_err());
}

#[test]
fn restricted_group_elements_lift_to_checked_source_equalities() {
    let mut compiler = Compiler::new(Options {
        proof_mode: ProofMode::Prove,
        ..Default::default()
    });
    let encoded = compiler
        .compile_program(
            None,
            include_str!("../../../../tests/slotted/proof-group-restriction.egg"),
        )
        .unwrap();
    let mut graph = new_egraph_with_proofs();
    encoded.run(&mut graph).unwrap();
    let request = encoded.proofs.values().last().unwrap();
    let (program, _, dag) = request.contexts(&BTreeMap::new()).unwrap();
    let (egg, evidence) = super::super::lift_slots::tests::native_query(
        &mut graph,
        "(prove (= g (EclassGroup_0 c)) (> (set-length g) 1))",
        &program,
        &request.flattened,
        &request.names,
        dag,
    );
    let checked = super::super::lift_slots::tests::check_restricted_symmetries(
        &program,
        &request.names,
        super::super::lift_slots::NativeProofs {
            store: &egg,
            program: graph.proof_checking_program(),
        },
        &evidence,
    )
    .unwrap();
    assert!(
        checked > 0,
        "the proof must exercise a nonidentity restricted symmetry"
    );
}

#[test]
fn cached_shapes_follow_child_equalities_under_binders() {
    prove_query(
        "(datatype E (V Var) (U E) (F E) (Lam Var E :binder 0))
         (let input (Lam $a (F (U (V $a)))))
         (run 0)
         (union (U (V $a)) (V $a))
         (let target (Lam $b (F (V $b))))
         (run 0)
         (check (= input target))
         (extract input)",
        1,
    );
}
