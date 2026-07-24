use egglog::EGraph;

const DEPTH_TEN_CHECK: &str = r#"
(check
  (= (Integral (Mul (Cos (Var "x")) (Var "x")) (Var "x"))
     (Sub a0
       (Sub a1
         (Sub a2
           (Sub a3
             (Sub a4
               (Sub a5
                 (Sub a6
                   (Sub a7
                     (Sub a8
                       (Sub a9 z10))))))))))))
"#;

const DEPTH_TWELVE_CHECK: &str = r#"
(check
  (= (Integral (Mul (Cos (Var "x")) (Var "x")) (Var "x"))
     (Sub a0
       (Sub a1
         (Sub a2
           (Sub a3
             (Sub a4
               (Sub a5
                 (Sub a6
                   (Sub a7
                     (Sub a8
                       (Sub a9
                         (Sub a10
                           (Sub a11 z12))))))))))))))
"#;

fn fixture_parts() -> (&'static str, &'static str) {
    let source = include_str!("math-microbenchmark.egg");
    let (setup, after_run) = source
        .split_once("(run 11)")
        .expect("Math benchmark must retain its explicit eleven-wave boundary");
    let (terminal_check, _) = after_run
        .split_once("(print-size Add)")
        .expect("Math benchmark must retain its terminal check before reporting");
    (setup, terminal_check)
}

fn check_boundary(proof_testing: bool, waves: usize, passing: &str, failing: &str) {
    let (setup, _) = fixture_parts();
    let mut egraph = if proof_testing {
        EGraph::new_with_proofs().with_proof_testing()
    } else {
        EGraph::default()
    };

    egraph
        .parse_and_run_program(None, &format!("{setup}\n(run {waves})"))
        .unwrap_or_else(|error| panic!("Math benchmark should run {waves} waves: {error}"));
    egraph
        .parse_and_run_program(None, passing)
        .unwrap_or_else(|error| {
            panic!("passing Math boundary check failed after wave {waves}: {error}")
        });
    assert!(
        egraph.parse_and_run_program(None, failing).is_err(),
        "failing Math boundary check unexpectedly succeeded after wave {waves}"
    );
}

#[test]
fn terminal_math_check_has_strict_two_by_two_wave_boundary() {
    let (_, terminal_check) = fixture_parts();

    for proof_testing in [false, true] {
        check_boundary(proof_testing, 10, DEPTH_TEN_CHECK, terminal_check);
        check_boundary(proof_testing, 11, terminal_check, DEPTH_TWELVE_CHECK);
    }
}
