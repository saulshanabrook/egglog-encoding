use egglog::CommandOutput;
use egglog_experimental::slotted::{Compiler, Options, ProofMode, new_egraph_with_proofs};
use std::process::Command;

fn compiler() -> Compiler {
    Compiler::new(Options {
        proof_mode: ProofMode::Prove,
        ..Default::default()
    })
}

#[test]
fn checking_program_excludes_axioms_after_the_query() {
    let declarations = "(datatype E (A) (B)) (let a (A)) (let b (B))";
    let early = compiler()
        .compile_program(None, &format!("{declarations} (check (= a b)) (union a b)"))
        .unwrap();
    let late = compiler()
        .compile_program(None, &format!("{declarations} (union a b) (check (= a b))"))
        .unwrap();
    let encoded = late.to_string();
    late.run_encoded(&mut new_egraph_with_proofs(), None, &encoded)
        .unwrap();
    assert!(
        early
            .run_encoded(&mut new_egraph_with_proofs(), None, &encoded)
            .is_err()
    );
}

#[test]
fn retained_rules_validate_terms_with_later_binders() {
    let mut compiler = compiler();
    let mut graph = new_egraph_with_proofs();
    compiler
        .compile_program(
            None,
            "(datatype E (V Var) (Pair E E) (Hit))
             (rewrite (Pair x y) (Hit) :when ((renaming-= x y)))",
        )
        .unwrap()
        .run(&mut graph)
        .unwrap();
    let outputs = compiler
        .compile_program(
            None,
            "(constructor Lam (Var E) E :binder 0)
             (let input (Pair (Pair (Lam $a (V $a)) (V $a))
                              (Pair (Lam $b (V $b)) (V $c))))
             (run 1)
             (check (= input (Hit)))",
        )
        .unwrap()
        .run(&mut graph)
        .unwrap();
    assert_eq!(
        outputs
            .iter()
            .filter(|o| matches!(o, CommandOutput::UserDefined(_)))
            .count(),
        1
    );
}

#[test]
fn cli_replays_desugared_proofs_with_explicit_source() {
    let directory =
        std::env::temp_dir().join(format!("slotted-proof-replay-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let source = directory.join("source.egg");
    let encoded = directory.join("encoded.egg");
    std::fs::write(
        &source,
        "(datatype E (V Var) (F E)) (let input (F (V $a)))
        (rewrite (F x) x) (run 1) (check (= input (V $a)))",
    )
    .unwrap();
    let binary = env!("CARGO_BIN_EXE_egglog-experimental");
    let lowered = Command::new(binary)
        .args(["--slotted", "--proofs", "--mode", "desugar"])
        .arg(&source)
        .output()
        .unwrap();
    assert!(
        lowered.status.success(),
        "{}",
        String::from_utf8_lossy(&lowered.stderr)
    );
    assert!(!String::from_utf8_lossy(&lowered.stdout).contains("(slotted-source"));
    std::fs::write(&encoded, &lowered.stdout).unwrap();
    let replay = Command::new(binary)
        .args(["--slotted-encoded", "--proofs", "--slotted-source"])
        .arg(&source)
        .arg(&encoded)
        .output()
        .unwrap();
    assert!(
        replay.status.success(),
        "{}",
        String::from_utf8_lossy(&replay.stderr)
    );
    assert!(String::from_utf8_lossy(&replay.stdout).contains("(Rule"));
    let missing = Command::new(binary)
        .args(["--slotted-encoded", "--proofs"])
        .arg(&encoded)
        .output()
        .unwrap();
    assert!(!missing.status.success());
    assert!(String::from_utf8_lossy(&missing.stderr).contains("--slotted-source"));
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn invalid_lowered_command_does_not_advance_the_compiler() {
    let mut compiler = compiler();
    assert!(
        compiler
            .compile_program(None, "(datatype E (A)) (print-size A extra)")
            .is_err()
    );
    compiler
        .compile_program(None, "(datatype E (A)) (let a (A)) (check (= a (A)))")
        .unwrap()
        .run(&mut new_egraph_with_proofs())
        .unwrap();
}

#[test]
fn failed_proof_repl_input_restores_compiler_and_graph() {
    use std::io::Write;
    use std::process::Stdio;
    let mut child = Command::new(env!("CARGO_BIN_EXE_egglog-experimental"))
        .args(["--slotted", "--proofs", "--mode", "interactive"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(b"(datatype E (A) (B) (F E)) (let input (F (A)))\n        (rewrite (F x) x) (run 1) (check (= input (A))) (check (= input (B)))\n        (check (= input (F (A)))) (fail (check (= input (A))))\n        (rewrite (F x) (B)) (run 1) (check (= input (B)))\n").unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert_eq!(stdout.matches("(error)").count(), 1, "{stdout}");
    assert_eq!(stdout.matches("(done)").count(), 3, "{stdout}");
    assert!(stdout.contains("(Rule"), "{stdout}");
}

#[test]
fn graph_parser_preserves_checked_compilation_and_failed_input_rollback() {
    let mut graph = new_egraph_with_proofs();
    let mut compiler = Compiler::for_egraph(
        Options {
            proof_mode: ProofMode::Prove,
            ..Default::default()
        },
        &graph,
    );
    assert!(
        compiler
            .compile_program(None, "(datatype E (A)) (print-size A extra)")
            .is_err()
    );
    let program = compiler
        .compile_program(
            None,
            "(datatype E (V Var) (F E)) (let a (F (V $x)))
         (rewrite (F x) x) (run 1) (check (= a (V $x))) (extract a)",
        )
        .unwrap();
    let outputs = program.run(&mut graph).unwrap();
    assert!(
        outputs
            .iter()
            .any(|output| matches!(output, CommandOutput::UserDefined(_)))
    );
    assert!(
        outputs
            .iter()
            .any(|output| matches!(output, CommandOutput::ExtractBest(..)))
    );
}
