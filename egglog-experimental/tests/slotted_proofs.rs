use egglog::{CommandOutput, EGraph};
use egglog_experimental::slotted::{
    Compiler, Options, ProofMode, new_egraph, new_egraph_with_proofs,
};

fn compiler(mode: ProofMode) -> Compiler {
    Compiler::new(Options {
        proof_mode: mode,
        ..Default::default()
    })
}

fn prove(compiler: &mut Compiler, graph: &mut EGraph, source: &str) -> Vec<String> {
    let encoded = compiler.compile(None, source).unwrap();
    let count = encoded.matches("(prove-slotted ").count();
    let outputs = graph
        .parse_and_run_program(None, &encoded)
        .unwrap_or_else(|error| panic!("{source}\n{error}"));
    let proofs = outputs
        .into_iter()
        .filter_map(|o| match o {
            CommandOutput::UserDefined(text) => Some(text.to_string()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(proofs.len(), count);
    proofs
}

#[test]
fn demo_proof_snapshots() {
    for (name, source) in [
        (
            "demo_rewrite",
            r#"(datatype U (F U))
(let input (F $a))
(rewrite (F x) x :name "unwrap")
(run 1)
(check (= input $a))"#,
        ),
        (
            "demo_nested_conditions",
            r#"(datatype U (F U) (G U) (H U) (A))
(let input (F (G (A))))
(let side (H (A)))
(rewrite (F (G x)) (H x) :when ((= (G x) y) (H x)) :name "nested")
(run 1)
(check (= input side))"#,
        ),
        (
            "demo_renaming_guard",
            r#"(datatype U (Pair U U) (F U) (G U) (Hit))
(union (F $a) (G $a))
(let input (Pair $a $b))
(let side (G $b))
(rewrite (Pair $x $y) (Hit) :when ((renaming-= (F $x) (G $y))) :name "guard")
(run 1)
(check (= input (Hit)))"#,
        ),
        (
            "demo_alpha_renaming",
            "(datatype U (Lam U U :binder 0))\n\
             (let input (Lam $a $a))\n\
             (run 0)\n\
             (check (= input (Lam $b $b)))",
        ),
        (
            "demo_binder_congruence",
            r#"(datatype U (Wrap U) (Lam U U :binder 0) (F U) (G U))
(let input (Wrap (Lam $a (F $a))))
(rewrite (F x) (G x) :name "f-to-g")
(run 1)
(check (= input (Wrap (Lam $b (G $b)))))"#,
        ),
        (
            "demo_redundant_slot",
            "(datatype U (Mul U U) (Zero))\n\
             (let input (Mul $a (Zero)))\n\
             (union input (Zero))\n\
             (run 0)\n\
             (check (= (Mul $b (Zero)) (Zero)))",
        ),
        (
            "demo_fresh_names",
            r#"(datatype U (F U) (Pair U U))
(let reserved (Pair $v0 $v2))
(let input (F $a))
(rewrite (F v1) v1 :name "unwrap")
(run 1)
(check (= input $a))"#,
        ),
    ] {
        let proofs = prove(
            &mut compiler(ProofMode::Prove),
            &mut new_egraph_with_proofs(),
            source,
        );
        assert_eq!(proofs.len(), 1);
        insta::assert_snapshot!(name, format!("Source:\n{source}\n\nProof:\n{}", proofs[0]));
    }
}

#[test]
fn nested_guards_with_globals_use_source_terms() {
    for predicate in ["=", "renaming-="] {
        for (lhs, term_slot, guard_slot) in [("input", "$a", "$s"), ("(Pair x y)", "slot", "slot")]
        {
            let source = format!(
                r#"(datatype U (Pair U U) (F U) (G U) (H U) (Hit))
(let slot $a)
(union (G {term_slot}) (H {term_slot}))
(let input (Pair (F (G {term_slot})) (F (H {term_slot}))))
(rewrite {lhs} (Hit) :when (({predicate} (F (G {guard_slot})) (F (H {guard_slot})))) :name "same")
(run 1)
(check (= input (Hit)))"#,
            );
            prove(
                &mut compiler(ProofMode::Prove),
                &mut new_egraph_with_proofs(),
                &source,
            );
        }
    }
}

#[test]
fn claims_instantiate_query_slots_without_renaming_globals() {
    for source in [
        "(datatype U (F U)) (let p (F $a)) (check (= p (F $b)))",
        "(datatype U (F U)) (let p (F $a)) (let fixed $b)
         (check (= p (F $b))) (fail (check (= p (F fixed))))",
        "(datatype U (F U)) (let fixed $a) (let p (F fixed))
         (check (= (F fixed) (F $b)))",
        "(datatype U (F U)) (let p (F $a)) (let q (F $b))
         (check (renaming-= p q)) (fail (check (= p q)))",
        "(datatype U (Pair U U)) (let p (Pair $a $b))
         (check (= p (Pair $b $a)))",
        "(datatype U (Pair U U)) (let p (Pair $a $a))
         (check (= p (Pair $b $b)))",
        "(datatype U (Lam U U :binder 0) (Pair U U))
         (let p (Lam $a (Pair $a $b)))
         (check (= p (Lam $b (Pair $b $c))))",
        "(datatype U (F U)) (let _p (F $a))
         (check (= _p (F $b)))",
        "(datatype U (F U)) (let p (F $a))
         (check (= p (F $+0)))",
        "(datatype U (Pair U U)) (let p (Pair $a $b))
         (check (= p (Pair $+0 $0)))",
    ] {
        let ordinary = compiler(ProofMode::Disabled).compile(None, source).unwrap();
        new_egraph().parse_and_run_program(None, &ordinary).unwrap();
        let proofs = prove(
            &mut compiler(ProofMode::Prove),
            &mut new_egraph_with_proofs(),
            source,
        );
        assert_eq!(proofs.len(), 1, "{source}");
    }
}

#[test]
fn named_slots_survive_scopes_and_successive_inputs() {
    let mut compiler = compiler(ProofMode::Prove);
    let mut graph = new_egraph_with_proofs();
    for (source, expected, absent) in [
        (
            "(datatype U (F U)) (let p (F $alpha)) (run 0) (check (= p (F $alpha)))",
            "$alpha",
            "$discard",
        ),
        (
            "(push) (let q (F $discard)) (run 0) (check (= q (F $discard))) (pop)",
            "$discard",
            "$after",
        ),
        (
            "(let r (F $after)) (run 0) (check (= r (F $after)))",
            "$after",
            "$discard",
        ),
    ] {
        let proofs = prove(&mut compiler, &mut graph, source);
        assert_eq!(proofs.len(), 1);
        assert!(proofs[0].contains(expected), "{}", proofs[0]);
        assert!(!proofs[0].contains(absent), "{}", proofs[0]);
        assert!(!proofs[0].contains("922337203685477"), "{}", proofs[0]);
    }
}

#[test]
fn rust_frontend_lifts_and_checks_surface_proofs() {
    for source in [
        include_str!("slotted/paper/figure-3.egg"),
        include_str!("slotted/proof-conditions.egg"),
        include_str!("slotted/binder-scope.egg"),
        include_str!("slotted/bare-slot-union.egg"),
        include_str!("slotted/symmetry-with-redundancy.egg"),
        include_str!("slotted/named-slots.egg"),
        include_str!("../benches/slotted/logic/first-order-logic.egg"),
        include_str!("../benches/slotted/logic/first-order-logic2.egg"),
    ] {
        let proofs = prove(
            &mut compiler(ProofMode::Prove),
            &mut new_egraph_with_proofs(),
            source,
        );
        assert!(!proofs.is_empty());
        assert!(proofs.iter().all(|p| p.contains("(= ")));
    }
}

#[test]
fn reconstruction_uses_the_compilers_fresh_names() {
    for (input, rewrite, result) in [
        ("(F (A) (B))", r#"(rewrite (F _p b) b :name "root")"#, "(B)"),
        (
            "(F (G (A)) (B))",
            r#"(rewrite (F (G a) _t1) _t1 :name "nested")"#,
            "(B)",
        ),
        (
            "(F (G (A)) (B))",
            r#"(rewrite (F (G a) p) (G p) :name "reordered")"#,
            "(G (B))",
        ),
        (
            "(F (G (H (A))) (B))",
            r#"(rewrite (F a _w0_1) _w0_1 :when ((= a (G (H b)))) :name "side")"#,
            "(B)",
        ),
        (
            "(F (A) (B))",
            r#"(rewrite (F a _a) (G _a) :name "class-labels")"#,
            "(G (B))",
        ),
    ] {
        let source = format!(
            "(datatype U (A) (B) (F U U) (G U) (H U))
             (let x {input}) {rewrite} (run 1) (check (= x {result}))"
        );
        let proofs = prove(
            &mut compiler(ProofMode::Prove),
            &mut new_egraph_with_proofs(),
            &source,
        );
        assert_eq!(proofs.len(), 1, "{rewrite}");
    }
}

#[test]
fn side_patterns_can_bind_the_proved_rewrite_root() {
    for (input, rewrites, rounds, claim) in [
        (
            "(F (G $a $b) (Null))",
            r#"(rewrite child (H $x $y)
                :when ((= parent (F child n)) (= child (G $x $y))) :name "child")"#,
            1,
            "(= (G $a $b) (H $a $b))",
        ),
        (
            "(F (G $a $b) (Null))",
            r#"(rewrite child n :when ((= parent (F child n))) :name "child")"#,
            1,
            "(= (G $a $b) (Null))",
        ),
        (
            "(F (Null) (Null))",
            r#"(rewrite (Null) (G $x $y) :name "build")
               (rewrite child (H $x $y)
                :when ((= parent (F child n)) (= child (G $x $y))) :name "child")"#,
            2,
            "(= (Null) (H $a $b))",
        ),
    ] {
        let source = format!(
            "(datatype U (F U U) (G U U) (H U U) (Null))
             (let input {input}) {rewrites} (run {rounds}) (check {claim})"
        );
        let proofs = prove(
            &mut compiler(ProofMode::Prove),
            &mut new_egraph_with_proofs(),
            &source,
        );
        assert_eq!(proofs.len(), 1);
        assert!(proofs[0].contains("(name \"child\")"));
    }
}

#[test]
fn recursive_rule_premises_keep_their_own_bindings() {
    for (a, b) in [("(A)", "(B)"), ("(Num 1)", "(Num 2)")] {
        let proofs = prove(
            &mut compiler(ProofMode::Prove),
            &mut new_egraph_with_proofs(),
            &format!(
                r#"
        (datatype U (A) (B) (Num i64) (Pair U U) (F U) (G U))
        (let input (Pair (F {a}) (F {b})))
        (rewrite (F x) (G x) :name "inner")
        (rewrite (Pair (G x) y) (Pair x z) :when ((= y (G z))) :name "outer")
        (run 2)
        (check (= input (Pair {a} {b})))
    "#
            ),
        );
        assert_eq!(proofs.len(), 1);
        assert!(proofs[0].contains("(name \"inner\")"));
        assert!(proofs[0].contains("(name \"outer\")"));
    }
}

#[test]
fn fresh_slots_avoid_negative_source_slots() {
    for slot in [-1, -2, i64::MIN] {
        let proofs = prove(
            &mut compiler(ProofMode::Prove),
            &mut new_egraph_with_proofs(),
            &format!(
                "(datatype U (Pair U U) (G U) (F U))
                 (let p (Pair $0 $1))
                 (let g (G $0))
                 (union p g)
                 (let f (F (Pair ${slot} $2)))
                 (run 0)
                 (check (= f (F (G ${slot}))))"
            ),
        );
        assert_eq!(proofs.len(), 1);
    }
}

#[test]
fn binder_freshness_handles_the_smallest_slot() {
    let proofs = prove(
        &mut compiler(ProofMode::Prove),
        &mut new_egraph_with_proofs(),
        &format!(
            "(datatype U (Lam U U :binder 0))
             (let x (Lam ${0} ${0}))
             (run 0)
             (check (= x (Lam $1 $1)))",
            i64::MIN,
        ),
    );
    assert_eq!(proofs.len(), 1);
}

#[test]
fn source_state_restores_with_scopes_and_successive_inputs() {
    let mut compiler = compiler(ProofMode::Prove);
    let mut graph = new_egraph_with_proofs();
    prove(
        &mut compiler,
        &mut graph,
        r#"
        (datatype U (Num i64) (F U))
        (let x (Num 1))
        (push)
        (datatype V (Local))
        (let y (F x))
        (rewrite (F a) a :name "temporary")
        (run 1)
        (check (= y x))
    "#,
    );
    let proofs = prove(
        &mut compiler,
        &mut graph,
        r#"
        (pop)
        (datatype V (Replacement))
        (let y (Replacement))
        (let z (F x))
        (run 0)
        (check (= y (Replacement)))
        (check (= x (Num 1)))
        (fail (check (= z x)))
    "#,
    );
    assert_eq!(proofs.len(), 2);
    assert!(proofs.iter().all(|p| !p.contains("temporary")));
}

#[test]
fn encoded_claim_is_checked_against_its_source() {
    let mut compiler = compiler(ProofMode::Prove);
    let encoded = compiler
        .compile(
            None,
            r#"
        (datatype U (Num i64) (F U))
        (let x (F $alpha))
        (rewrite (F _p) _p)
        (run 1)
        (check (= x $alpha))
    "#,
        )
        .unwrap();
    let mut graph = new_egraph_with_proofs();
    let printed = graph
        .parse_program(None, &encoded)
        .unwrap()
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n");
    assert!(graph.parse_and_run_program(None, &printed).is_ok());
    // Leave the encoded query true while changing only its surface claim.
    let corrupt = encoded.replace(
        "(prove-slotted (= U (\"x\"",
        "(prove-slotted (= U (\"(Num 2)\"",
    );
    assert_ne!(corrupt, encoded);
    assert!(
        new_egraph_with_proofs()
            .parse_and_run_program(None, &corrupt)
            .is_err()
    );
}

#[test]
fn quoted_source_payloads_round_trip() {
    let proofs = prove(
        &mut compiler(ProofMode::Prove),
        &mut new_egraph_with_proofs(),
        r#"
        (datatype U (Text String) (F U))
        (let x (F (Text "a\"b\\c")))
        (rewrite (F a) a)
        (run 1)
        (check (= x (Text "a\"b\\c")))
    "#,
    );
    assert_eq!(proofs.len(), 1);
}

#[test]
fn unsupported_substitution_does_not_change_compiler_state() {
    let mut compiler = compiler(ProofMode::Prove);
    let error = compiler
        .compile(None, "(datatype U (F U)) (rewrite (F x) (subst x $0 x))")
        .unwrap_err();
    assert!(error.to_string().contains("no proof translation"));
    assert!(compiler.compile(None, "(datatype U (F U U))").is_ok());
}

#[test]
fn original_guards_are_checked_independently_of_flattening() {
    let source = r#"(datatype U (F U) (G U))
(let input (F $a))
(rewrite (F $s) (G $s) :when ((free $s (F $s))) :name "guard")
(run 1)
(check (= input (G $a)))"#;
    let encoded = compiler(ProofMode::Prove).compile(None, source).unwrap();
    new_egraph_with_proofs()
        .parse_and_run_program(None, &encoded)
        .unwrap();
    let corrupt = encoded
        .lines()
        .map(|line| {
            if line.starts_with("(set (SlottedRuleSource ") {
                line.replace("(free $s (F $s))", "(not-free $s (F $s))")
            } else {
                line.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    assert_ne!(encoded, corrupt);
    let error = new_egraph_with_proofs()
        .parse_and_run_program(None, &corrupt)
        .unwrap_err();
    assert!(error.to_string().contains("not-free fails"), "{error}");
}

#[test]
fn source_rule_globals_keep_their_declaration_scope() {
    for source in [
        r#"(datatype U (F U) (G U) (A))
(rewrite (F x) (G x) :name "local")
(let x (F (A)))
(run 1)
(check (= x (G (A))))"#,
        r#"(datatype U (F U) (G U))
(let fixed $a)
(let input (F fixed))
(rewrite (F fixed) (G fixed) :name "global")
(run 1)
(check (= input (G fixed)))"#,
        r#"(datatype U (F U) (G U))
(let fixed $a)
(let input (F fixed))
(rewrite input (G fixed) :name "global-root")
(run 1)
(check (= input (G fixed)))"#,
        r#"(datatype U (F U) (G U) (H U))
(let fixed (F $a))
(let input (H fixed))
(rewrite (H fixed) (G fixed) :name "global-term")
(run 1)
(check (= input (G fixed)))"#,
    ] {
        let proofs = prove(
            &mut compiler(ProofMode::Prove),
            &mut new_egraph_with_proofs(),
            source,
        );
        assert_eq!(proofs.len(), 1);
    }
}
