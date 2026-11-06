use super::*;
use crate::slotted::{Compiler, Options, ProofMode, new_egraph_with_proofs};

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
    let outputs = graph
        .parse_and_run_program(None, "(prove (= g (EclassGroup_0 c)) (> (set-length g) 1))")
        .unwrap();
    let egg = outputs
        .into_iter()
        .find_map(|output| match output {
            CommandOutput::ProveExists { proof_store, .. } => Some(proof_store),
            _ => None,
        })
        .unwrap();
    let request = encoded.proofs.values().last().unwrap();
    let (program, _, dag) = request.contexts(&BTreeMap::new()).unwrap();
    let checked = super::super::lift_slots::tests::check_restricted_symmetries(
        &program,
        dag,
        &request.names,
        &egg,
    )
    .unwrap();
    assert!(
        checked > 0,
        "the proof must exercise a nonidentity restricted symmetry"
    );
}
