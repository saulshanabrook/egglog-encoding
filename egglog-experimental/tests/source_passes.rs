use egglog_experimental::{
    disequality_source_macros,
    slotted::{Compiler, Options, ProofMode, new_egraph, new_egraph_with_proofs},
};

#[test]
fn disequality_output_runs_directly_and_stacks_on_slotted() {
    let source = "(datatype E (A) (B) (C) (Pair E E))
        (separately-injective Pair)
        (disequal (A) (B))
        (let left (Pair (C) (A))) (let right (Pair (C) (B)))
        (check (known-disequal left right))
        (fail (check (known-disequal (A) (C))))
        (fail (check (contradiction)))
        (union left right)
        (check (= (A) (B)))
        (check (contradiction)) (extract left)";
    disequality_source_macros()
        .parse_and_run_program(None, source)
        .unwrap();
    for proof_mode in [ProofMode::Disabled, ProofMode::Check, ProofMode::Prove] {
        let mut graph = if proof_mode == ProofMode::Prove {
            new_egraph_with_proofs()
        } else {
            new_egraph()
        };
        Compiler::new(Options {
            proof_mode,
            ..Default::default()
        })
        .with_source_macros(disequality_source_macros())
        .compile_program(None, source)
        .unwrap()
        .run(&mut graph)
        .unwrap();
    }
}

#[test]
fn first_pass_does_not_assume_a_slotted_carrier() {
    let source = "(datatype A (A0) (A1)) (datatype B (B0) (B1) (Wrap A))
        (separately-injective Wrap)
        (disequal (A0) (A1)) (let b0 (Wrap (A0))) (let b1 (Wrap (A1)))
        (check (known-disequal b0 b1))
        (disequal (B0) (B1)) (union (B0) (B1)) (check (contradiction))";
    disequality_source_macros()
        .parse_and_run_program(None, source)
        .unwrap();
}

#[test]
fn named_rulesets_and_schedules_are_generic() {
    let source = "(datatype E (A) (B) (C))
        (ruleset first) (ruleset second)
        (rewrite (A) (B) :ruleset first) (rewrite (B) (C) :ruleset second)
        (let a (A)) (run 3) (fail (check (= a (B))))
        (run first 1) (check (= a (B))) (fail (check (= a (C))))
        (push) (run-schedule (seq (repeat 0 (run first)) (saturate (run second))))
        (check (= a (C))) (pop) (fail (check (= a (C))))
        (run-schedule (repeat 1 (seq (run second) (run first)))) (check (= a (C)))";
    for proof_mode in [ProofMode::Disabled, ProofMode::Check, ProofMode::Prove] {
        let mut graph = if proof_mode == ProofMode::Prove {
            new_egraph_with_proofs()
        } else {
            new_egraph()
        };
        Compiler::new(Options {
            proof_mode,
            ..Default::default()
        })
        .compile_program(None, source)
        .unwrap()
        .run(&mut graph)
        .unwrap();
    }
}

#[test]
fn primitive_payload_guards_are_generic() {
    let source = "(datatype E (Num i64) (Pair E E) (Hit))
        (rewrite (Pair (Num x) (Num y)) (Hit) :when ((!= x y) (= x 1)))
        (let yes (Pair (Num 1) (Num 2))) (let no (Pair (Num 1) (Num 1)))
        (let wrong (Pair (Num 2) (Num 3))) (run 1)
        (check (= yes (Hit))) (fail (check (= no (Hit)))) (fail (check (= wrong (Hit))))";
    Compiler::new(Options {
        proof_mode: ProofMode::Prove,
        ..Default::default()
    })
    .compile_program(None, source)
    .unwrap()
    .run(&mut new_egraph_with_proofs())
    .unwrap();
    let source = "(datatype E (Num i64)) (separately-injective Num)
        (let a (Num 1)) (let b (Num 2)) (check (known-disequal a b))
        (fail (check (contradiction))) (union a b) (check (contradiction))";
    disequality_source_macros()
        .parse_and_run_program(None, source)
        .unwrap();
    Compiler::new(Options {
        proof_mode: ProofMode::Prove,
        ..Default::default()
    })
    .with_source_macros(disequality_source_macros())
    .compile_program(None, source)
    .unwrap()
    .run(&mut new_egraph_with_proofs())
    .unwrap();
}
