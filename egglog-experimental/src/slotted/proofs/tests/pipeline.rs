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
fn extraction_returns_a_source_checked_proof_of_the_selected_term() {
    for source in [
        "(datatype E (A) (B) (F E))
         (let input (F (A)))
         (rewrite (F x) x :name shrink)
         (run 1) (extract input)",
        "(datatype E (V Var) (Lam Var E :binder 0))
         (extract (Lam $a (V $a))) (check (= (Lam $a (V $a)) (Lam $b (V $b))))",
    ] {
        let mut compiler = Compiler::new(Options {
            proof_mode: ProofMode::Prove,
            ..Default::default()
        });
        let encoded = compiler.compile_program(None, source).unwrap();
        assert_eq!(encoded.extractions.len(), 1);
        let outputs = encoded.run(&mut new_egraph_with_proofs()).unwrap();
        let extracted = outputs
            .iter()
            .position(|out| matches!(out, CommandOutput::ExtractBest(..)))
            .unwrap();
        assert!(
            outputs[extracted + 1..]
                .iter()
                .any(|out| matches!(out, CommandOutput::UserDefined(_)))
        );
    }
}

#[test]
fn substitution_certifies_inputs_before_building_a_capture_avoiding_result() {
    prove_query(
        "(datatype E (V Var) (Lam Var E :binder 0) (Let E Var E :binder 1))
         (let input (Let (V $y) $x (Lam $y (V $x))))
         (rewrite (Let value $v body) (subst body $v value) :name beta)
         (run 1)
         (check (= input (Lam $z (V $y))))",
        1,
    );
}

#[test]
fn substitution_certifies_a_representative_changed_by_an_earlier_round() {
    prove_query(
        "(datatype E (V Var) (F E) (Let E Var E :binder 1))
         (let input (Let (V $y) $x (F (V $x))))
         (rewrite (F x) x :name shrink)
         (run 1)
         (rewrite (Let value $v body) (subst body $v value) :name beta)
         (run 1)
         (check (= input (V $y)))",
        1,
    );
}

#[test]
fn substitution_preserves_the_frames_of_repeated_binder_patterns() {
    prove_query(
        "(datatype E (V Var) (N i64) (Tag E) (Binop E E E) (Let E Var E :binder 1))
         (rewrite (Let value $x body) (subst body $x value) :name beta)
         (rewrite (Binop f (Let value $x a) (Let value $x b))
                  (Tag (Let value $x (Binop f a b)))
                  :when ((not-free $x f)) :name join-lets)
         (let input (Binop (N 1) (Let (V $a) $x (V $x)) (Let (V $a) $x (V $b))))
         (run 3)
         (check (= input (Tag (Binop (N 1) (V $a) (V $b)))))",
        1,
    );
}

#[test]
fn unused_binders_do_not_block_reconstruction_of_redundant_free_coordinates() {
    prove_query(
        "(datatype E (V Var) (N i64) (Pair E E) (Tag E) (Binop E E E) (Let E Var E :binder 1))
         (rewrite (Let value $x body) (subst body $x value) :name beta)
         (rewrite (Binop f (Let value $x a) (Let value $x b))
                  (Tag (Let value $x (Binop f a b)))
                  :when ((not-free $x f)) :name join-lets)
         (let input (Binop (N 1) (Let (V $a) $x (Pair (V $b) (V $c)))
                                (Let (V $a) $x (Pair (V $d) (V $x)))))
         (run 3)
         (check (= input (Tag (Binop (N 1) (Pair (V $b) (V $c)) (Pair (V $d) (V $a))))))",
        1,
    );
}

#[test]
fn substitution_evidence_follows_scopes_replay_and_graph_cloning() {
    let mut compiler = Compiler::new(Options {
        proof_mode: ProofMode::Prove,
        ..Default::default()
    });
    let program = compiler
        .compile_program(
            None,
            "(datatype E (V Var) (Let E Var E :binder 1))
         (let input (Let (V $y) $x (V $x)))
         (rewrite (Let value $v body) (subst body $v value) :name beta)
         (push) (run 1) (extract input) (pop)
         (fail (check (= input (V $y))))",
        )
        .unwrap();
    let mut graph = new_egraph_with_proofs();
    program
        .run_encoded(&mut graph, None, &program.to_string())
        .unwrap();
    assert!(
        graph
            .extension_state::<super::super::runtime_substitution::Evidence>()
            .is_none()
    );
    let run = compiler
        .compile_program(None, "(run 1) (check (= input (V $y)))")
        .unwrap();
    run.run(&mut graph).unwrap();
    let query = compiler
        .compile_program(None, "(check (= input (V $y))) (extract input)")
        .unwrap();
    query.run(&mut graph.clone()).unwrap();
}

#[test]
fn substitution_outputs_keep_slots_bound_only_by_side_patterns() {
    prove_query(
        "(datatype E (Z) (V Var) (Pair E E))
         (let argument (Pair (V $a) (V $b)))
         (let input (Z))
         (rewrite (Z) (subst body $x body)
                  :when ((= body (Pair (V $x) (V $y)))) :name side-substitution)
         (run 1)
         (check (= input (Pair argument (V $b))))",
        1,
    );
}

#[test]
fn raw_action_replay_skips_popped_bindings_unions_and_substitution_outputs() {
    prove_query(
        "(datatype E (V Var) (F E) (Let E Var E :binder 1))
         (rewrite (Let value $v body) (subst body $v value) :name beta)
         (push)
         (let scoped (Let (V $p) $q (V $q)))
         (union (F (V $p)) (V $p))
         (run 2)
         (pop)
         (let scoped (Let (V $a) $b (V $b)))
         (run 1)
         (let later (Let scoped $c (F (V $c))))
         (run 1)
         (union (F (V $a)) (V $a))
         (check (= scoped (V $a)) (= later (V $a)))",
        2,
    );
}

#[test]
fn substitution_batches_requests_from_multiple_carriers() {
    let mut compiler = Compiler::new(Options {
        proof_mode: ProofMode::Prove,
        ..Default::default()
    });
    let program = compiler
        .compile_program(
            None,
            "(datatype E (V Var) (Let E Var E :binder 1))
         (datatype T (TV Var) (TLet T Var T :binder 1))
         (let input (Let (V $y) $x (V $x)))
         (let other (TLet (TV $b) $a (TV $a)))
         (rewrite (Let value $v body) (subst body $v value) :name beta)
         (rewrite (TLet value $v body) (subst body $v value) :name type-beta)
         (run 2)
         (check (= input (V $y))) (check (= other (TV $b)))",
        )
        .unwrap();
    program.run(&mut new_egraph_with_proofs()).unwrap();
}

#[test]
fn substitution_outputs_are_not_accepted_as_source_axioms() {
    let mut compiler = Compiler::new(Options {
        proof_mode: ProofMode::Prove,
        ..Default::default()
    });
    let mut graph = new_egraph_with_proofs();
    compiler
        .compile_program(
            None,
            "(datatype E (V Var) (F E) (Let E Var E :binder 1))
         (let input (Let (V $y) $x (F (V $x))))
         (rewrite (Let value $v body) (subst body $v value) :name beta)
         (run 1)",
        )
        .unwrap()
        .run(&mut graph)
        .unwrap();
    let query = compiler
        .compile_program(None, "(check (= input (F (V $y))))")
        .unwrap();
    query.run(&mut graph).unwrap();
    *graph.extension_state_or_default::<super::super::runtime_substitution::Evidence>() =
        Default::default();
    assert!(query.run(&mut graph).is_err());
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

#[test]
fn unchecked_production_materializes_valid_substitution_and_extraction_proofs() {
    let source = "(datatype E (V Var) (Lam Var E :binder 0) (Let E Var E :binder 1))
         (let input (Let (V $y) $x (Lam $y (V $x))))
         (rewrite (Let value $v body) (subst body $v value) :name beta)
         (run 1) (check (= input (Lam $z (V $y)))) (extract input)";
    for no_aliasing in [false, true] {
        let mut compiler = Compiler::new(Options {
            proof_mode: ProofMode::Extract,
            no_aliasing,
        });
        let program = compiler.compile_program(None, source).unwrap();
        assert!(program.proofs.values().all(|request| !request.verify));
        let outputs = program.run(&mut new_egraph_with_proofs()).unwrap();
        let checking =
            super::super::resolve_program(&egglog::ast::parse_sexps(None, source).unwrap())
                .unwrap();
        let mut count = 0;
        for output in outputs {
            if let CommandOutput::UserDefined(output) = output {
                let proofs = output
                    .as_ref()
                    .as_any()
                    .downcast_ref::<SourceProofs>()
                    .unwrap();
                for (store, root, _) in &proofs.0 {
                    let mut store = store.clone();
                    super::super::check_proof(&mut store, &checking, *root).unwrap();
                    count += 1;
                }
            }
        }
        assert_eq!(count, 2);
    }
}
