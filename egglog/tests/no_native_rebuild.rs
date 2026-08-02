use egglog::*;

/// Under the term/proof encoding every union is an ordinary `set` into an
/// encoded union-find table, so the backend's own union-find stays empty and
/// its native rebuilding must never run. The backend asserts this (see
/// `egglog_bridge::EGraph::forbid_native_rebuild`), so running a workload that
/// exercises congruence, container rebuilding, and a custom `:merge` is enough
/// to catch a regression that leaks a union into the backend.
const WORKLOAD: &str = r#"
(datatype Math
    (Num i64)
    (Boxed i64)
    (Add Math Math)
    (Mul Math Math))
(sort MathVec (Vec Math))
(constructor Wrap (MathVec) Math)
(function Cost (Math) i64 :merge (min old new))

(rewrite (Add a b) (Add b a))
(rewrite (Mul a (Add b c)) (Add (Mul a b) (Mul a c)))
(rule ((= e (Boxed n))) ((union e (Num n))))
(rule ((= e (Num n))) ((set (Cost e) 1)))

(Mul (Num 2) (Add (Num 3) (Num 4)))
(Wrap (vec-of (Boxed 3) (Boxed 4)))

(run 5)
(check (= (Mul (Num 2) (Add (Num 3) (Num 4)))
          (Add (Mul (Num 2) (Num 3)) (Mul (Num 2) (Num 4)))))
(check (Wrap (vec-of (Num 3) (Num 4))))
"#;

#[test]
fn term_encoding_never_uses_native_rebuild() {
    EGraph::new_with_term_encoding()
        .parse_and_run_program(None, WORKLOAD)
        .unwrap();
}

#[test]
fn proof_mode_never_uses_native_rebuild() {
    EGraph::new_with_proofs()
        .parse_and_run_program(None, WORKLOAD)
        .unwrap();
}
