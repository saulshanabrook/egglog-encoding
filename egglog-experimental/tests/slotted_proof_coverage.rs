#[path = "support/proof_coverage.rs"]
mod coverage;

use egglog_experimental::slotted::{
    CompileError, Compiler, Options, ProofMode, UnsupportedProofFeature,
};

#[test]
fn source_expectations_count_existential_and_multiple_fact_checks() {
    let source = r#"
        (datatype E (V Var) (N i64) (Pair E E))
        (let a (V $a))
        (check (= a (V $a)))
        (check (renaming-= (Pair a (N 1)) (Pair (V $b) (N 1))))
        (check (= a x))
        (check (= a a) (= a a))
        (check (!= a (N 1)))
        (fail (check (= a (N 1))))
        (push)
        (let b a)
        (check (= b a))
        (pop)
        (check (= b a))
    "#;
    assert_eq!(coverage::expected_proofs(source).unwrap(), 6);
    assert_eq!(
        coverage::expected_proofs("(datatype E (N i64))").unwrap(),
        0
    );
}

#[test]
fn unsupported_substitution_is_typed_and_does_not_commit_compiler_state() {
    let mut compiler = Compiler::new(Options {
        proof_mode: ProofMode::Prove,
        ..Default::default()
    });
    let error = compiler
        .compile(
            None,
            "(datatype E (V Var)) (rewrite (V $a) (subst (V $a) $a (V $b)))",
        )
        .unwrap_err();
    assert!(matches!(
        error,
        CompileError::UnsupportedProofFeature {
            feature: UnsupportedProofFeature::Substitution,
            ..
        }
    ));
    compiler.compile(None, "(datatype E (V Var))").unwrap();
    assert!(matches!(
        compiler.compile(None, "(let a (Missing))"),
        Err(CompileError::Parse(_))
    ));
}

#[test]
fn source_expectations_follow_includes_and_nullary_existence_checks() {
    let path =
        std::env::temp_dir().join(format!("slotted-proof-coverage-{}.egg", std::process::id()));
    std::fs::write(
        &path,
        "(datatype E (N) (Pair E E)) (let n (N)) (check (= n (N)))",
    )
    .unwrap();
    let source = format!(
        r#"
        (include "{}")
        (check (__internal-holds n N))
        (check (__internal-holds n Pair))
        (check (__internal-not-holds n Pair))
        (check (renaming-= n (N)))
    "#,
        path.display()
    );
    let expected = coverage::expected_proofs(&source);
    std::fs::remove_file(path).unwrap();
    assert_eq!(expected.unwrap(), 4);
}

#[test]
fn payload_variables_remain_local_even_when_their_names_are_globals() {
    let source = r#"
        (let n $a)
        (let value (N 1))
        (check (= value (N n)))
        (check (= value (N $a)))
        (check (= (V n) (V n)))
        (datatype* ((E (V Var) (N i64))))
    "#;
    assert_eq!(coverage::expected_proofs(source).unwrap(), 3);
}
