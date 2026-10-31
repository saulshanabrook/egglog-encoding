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
fn payload_is_a_valid_carrier_name() {
    let proofs = prove(
        &mut compiler(ProofMode::Prove),
        &mut new_egraph_with_proofs(),
        "(datatype payload (Vpayload Var) (F payload)) (let input (F (Vpayload $a))) (check (= input (F (Vpayload $a))))",
    );
    assert_eq!(proofs.len(), 1);
}

#[test]
fn demo_proof_snapshots() {
    for (name, source) in [
        (
            "demo_rewrite",
            r#"(datatype U (V Var) (F U))
(let input (F (V $a)))
(rewrite (F x) x :name "unwrap")
(run 1)
(check (= input (V $a)))"#,
        ),
        (
            "demo_nested_conditions",
            r#"(datatype U (V Var) (F U) (G U) (H U) (A))
(let input (F (G (A))))
(let side (H (A)))
(rewrite (F (G x)) (H x) :when ((= (G x) y) (H x)) :name "nested")
(run 1)
(check (= input side))"#,
        ),
        (
            "demo_renaming_guard",
            r#"(datatype U (V Var) (Pair U U) (F U) (G U) (Hit))
(union (F (V $a)) (G (V $a)))
(let input (Pair (V $a) (V $b)))
(let side (G (V $b)))
(rewrite (Pair (V $x) (V $y)) (Hit) :when ((renaming-= (F (V $x)) (G (V $y)))) :name "guard")
(run 1)
(check (= input (Hit)))"#,
        ),
        (
            "demo_nested_guard",
            r#"(datatype U (V Var) (Pair U U) (F U) (Hit))
(let input (Pair (V $a) (V $b)))
(let side (F (V $b)))
(rewrite (Pair (V $x) (V $y)) (Hit) :when ((not-free $x (F (V $y)))) :name "guard")
(run 1)
(check (= input (Hit)))"#,
        ),
        (
            "demo_multiple_guards",
            r#"(datatype U (V Var) (Pair U U) (Hit))
(let input (Pair (V $a) (V $b)))
(rewrite (Pair (V $x) (V $y)) (Hit)
  :when ((renaming-= (V $x) (V $y)) (not-free $x (V $y)) (!= (V $x) (V $y))) :name "guards")
(run 1)
(check (= input (Hit)))"#,
        ),
        (
            "demo_alpha_renaming",
            "(datatype U (V Var) (Lam Var U :binder 0))
(let input (Lam $a (V $a)))
(run 0)
(check (= input (Lam $b (V $b))))",
        ),
        (
            "demo_scoped_alpha",
            r#"(datatype U (V Var) (Lam Var U :binder 0))
(let input (Lam $a (Lam $a (V $a))))
(run 0)
(check (= input (Lam $b (Lam $c (V $c)))))"#,
        ),
        (
            "demo_binder_congruence",
            r#"(datatype U (V Var) (Wrap U) (Lam Var U :binder 0) (F U) (G U))
(let input (Wrap (Lam $a (F (V $a)))))
(rewrite (F x) (G x) :name "f-to-g")
(run 1)
(check (= input (Wrap (Lam $b (G (V $b))))))"#,
        ),
        (
            "demo_redundant_slot",
            "(datatype U (V Var) (Mul U U) (Zero))
(let input (Mul (V $a) (Zero)))
(union input (Zero))
(run 0)
(check (= (Mul (V $b) (Zero)) (Zero)))",
        ),
        (
            "demo_fresh_names",
            r#"(datatype U (V Var) (F U) (Pair U U))
(let reserved (Pair (V $v0) (V $v2)))
(let input (F (V $a)))
(rewrite (F v1) v1 :name "unwrap")
(run 1)
(check (= input (V $a)))"#,
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
                r#"(datatype U (V Var) (Pair U U) (F U) (G U) (H U) (Hit))
(let slot $a)
(union (G (V {term_slot})) (H (V {term_slot})))
(let input (Pair (F (G (V {term_slot}))) (F (H (V {term_slot})))))
(rewrite {lhs} (Hit) :when (({predicate} (F (G (V {guard_slot}))) (F (H (V {guard_slot}))))) :name "same")
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
        "(datatype U (V Var) (F U)) (let p (F (V $a))) (check (= p (F (V $b))))",
        "(datatype U (V Var) (F U)) (let p (F (V $a))) (let fixed $b)
         (check (= p (F (V $b)))) (fail (check (= p (F (V fixed)))))",
        "(datatype U (V Var) (F U)) (let fixed $a) (let p (F (V fixed)))
         (check (= (F (V fixed)) (F (V $b))))",
        "(datatype U (V Var) (F U)) (let p (F (V $a))) (let q (F (V $b)))
         (check (renaming-= p q)) (fail (check (= p q)))",
        "(datatype U (V Var) (Pair U U)) (let p (Pair (V $a) (V $b)))
         (check (= p (Pair (V $b) (V $a))))",
        "(datatype U (V Var) (Pair U U)) (let p (Pair (V $a) (V $a)))
         (check (= p (Pair (V $b) (V $b))))",
        "(datatype U (V Var) (Lam Var U :binder 0) (Pair U U))
         (let p (Lam $a (Pair (V $a) (V $b))))
         (check (= p (Lam $b (Pair (V $b) (V $c)))))",
        "(datatype U (V Var) (F U)) (let _p (F (V $a)))
         (check (= _p (F (V $b))))",
        "(datatype U (V Var) (F U)) (let p (F (V $a)))
         (check (= p (F (V $+0))))",
        "(datatype U (V Var) (Pair U U)) (let p (Pair (V $a) (V $b)))
         (check (= p (Pair (V $+0) (V $0))))",
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
            "(datatype U (V Var) (F U)) (let p (F (V $alpha))) (run 0) (check (= p (F (V $alpha))))",
            "$alpha",
            "$discard",
        ),
        (
            "(push) (let q (F (V $discard))) (run 0) (check (= q (F (V $discard)))) (pop)",
            "$discard",
            "$after",
        ),
        (
            "(let r (F (V $after))) (run 0) (check (= r (F (V $after))))",
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
            "(datatype U (V Var) (A) (B) (F U U) (G U) (H U))
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
            "(F (G (V $a) (V $b)) (Null))",
            r#"(rewrite child (H (V $x) (V $y))
                :when ((= parent (F child n)) (= child (G (V $x) (V $y)))) :name "child")"#,
            1,
            "(= (G (V $a) (V $b)) (H (V $a) (V $b)))",
        ),
        (
            "(F (G (V $a) (V $b)) (Null))",
            r#"(rewrite child n :when ((= parent (F child n))) :name "child")"#,
            1,
            "(= (G (V $a) (V $b)) (Null))",
        ),
        (
            "(F (Null) (Null))",
            r#"(rewrite (Null) (G (V $x) (V $y)) :name "build")
               (rewrite child (H (V $x) (V $y))
                :when ((= parent (F child n)) (= child (G (V $x) (V $y)))) :name "child")"#,
            2,
            "(= (Null) (H (V $a) (V $b)))",
        ),
    ] {
        let source = format!(
            "(datatype U (V Var) (F U U) (G U U) (H U U) (Null))
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
        (datatype U (V Var) (A) (B) (Num i64) (Pair U U) (F U) (G U))
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
                "(datatype U (V Var) (Pair U U) (G U) (F U))
                 (let p (Pair (V $0) (V $1)))
                 (let g (G (V $0)))
                 (union p g)
                 (let f (F (Pair (V ${slot}) (V $2))))
                 (run 0)
                 (check (= f (F (G (V ${slot})))))"
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
            "(datatype U (V Var) (Lam Var U :binder 0))
             (let x (Lam ${0} (V ${0})))
             (run 0)
             (check (= x (Lam $1 (V $1))))",
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
        (datatype U (VVar Var) (Num i64) (F U))
        (let x (Num 1))
        (push)
        (datatype V (VV Var) (Local))
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
        (datatype V (VV Var) (Replacement))
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
        (datatype U (V Var) (Num i64) (F U))
        (let x (F (V $alpha)))
        (rewrite (F _p) _p)
        (run 1)
        (check (= x (V $alpha)))
    "#,
        )
        .unwrap();
    for table in [
        "SlottedRuleSource",
        "SlottedLetSource",
        "SlottedUnionSource",
        "(relation SlottedCarrier ",
        "rule-names",
    ] {
        assert!(!encoded.contains(table), "source metadata table {table}");
    }
    assert!(encoded.contains("(slotted-source (rewrite (F _p) _p :when () :name"));
    let mut graph = new_egraph_with_proofs();
    let printed = graph
        .parse_program(None, &encoded)
        .unwrap()
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n");
    graph.parse_and_run_program(None, &printed).unwrap();
    // Leave the encoded query true while changing only its surface claim.
    let corrupt = encoded.replace("(prove-slotted (= (x ", "(prove-slotted (= ((Num 2) ");
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
        (datatype U (V Var) (Text String) (F U))
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
        .compile(
            None,
            "(datatype U (V Var) (F U)) (rewrite (F x) (subst x $0 x))",
        )
        .unwrap_err();
    assert!(error.to_string().contains("no proof translation"));
    assert!(
        compiler
            .compile(None, "(datatype U (V Var) (F U U))")
            .is_ok()
    );
}

#[test]
fn original_guards_are_checked_independently_of_flattening() {
    let source = r#"(datatype U (V Var) (F U) (G U))
(let input (F (V $a)))
(rewrite (F (V $s)) (G (V $s)) :when ((free $s (F (V $s)))) :name "guard")
(run 1)
(check (= input (G (V $a))))"#;
    let encoded = compiler(ProofMode::Prove).compile(None, source).unwrap();
    new_egraph_with_proofs()
        .parse_and_run_program(None, &encoded)
        .unwrap();
    let corrupt = encoded
        .lines()
        .map(|line| {
            if line.starts_with("(slotted-source (rewrite ") {
                line.replace("(free $s (F (V $s)))", "(not-free $s (F (V $s)))")
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
    assert!(
        error
            .to_string()
            .contains("Primitive 'slotted-proof-not-free' validation failed"),
        "{error}"
    );
}

#[test]
fn source_rule_globals_keep_their_declaration_scope() {
    for source in [
        r#"(datatype U (V Var) (F U) (G U) (A))
(rewrite (F x) (G x) :name "local")
(let x (F (A)))
(run 1)
(check (= x (G (A))))"#,
        r#"(datatype U (V Var) (F U) (G U))
(let fixed $a)
(let input (F (V fixed)))
(rewrite (F (V fixed)) (G (V fixed)) :name "global")
(run 1)
(check (= input (G (V fixed))))"#,
        r#"(datatype U (V Var) (F U) (G U))
(let fixed $a)
(let input (F (V fixed)))
(rewrite input (G (V fixed)) :name "global-root")
(run 1)
(check (= input (G (V fixed))))"#,
        r#"(datatype U (V Var) (F U) (G U) (H U))
(let fixed (F (V $a)))
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

#[test]
fn source_resolution_preserves_payload_locals_and_rigid_name_globals() {
    for source in [
        r#"(datatype U (V Var) (Num i64) (Pair U U))
        (let n $a)
        (let input (Pair (Num 2) (V n)))
        (rewrite (Pair (Num n) (V n)) (Pair (V n) (Num n)) :name "swap")
        (run 1)
        (check (= input (Pair (V n) (Num 2))))"#,
        r#"(datatype A (VA Var) (F A) (G A))
        (datatype B (VB Var) (H B) (J B))
        (let fixed $a)
        (let left (F (VA fixed)))
        (let right (H (VB fixed)))
        (rewrite (F (VA fixed)) (G (VA fixed)) :when () :name "a")
        (rewrite (H (VB fixed)) (J (VB fixed)) :name "b")
        (run 1)
        (check (= left (G (VA fixed))))
        (check (= right (J (VB fixed))))"#,
    ] {
        let proofs = prove(
            &mut compiler(ProofMode::Prove),
            &mut new_egraph_with_proofs(),
            source,
        );
        assert!(!proofs.is_empty());
    }
}

#[test]
fn retained_declarations_preserve_the_sort_of_earlier_axioms() {
    let mut compiler = compiler(ProofMode::Prove);
    let mut graph = new_egraph_with_proofs();
    prove(
        &mut compiler,
        &mut graph,
        r#"
        (datatype A (VA Var) (WA A))
        (let first $a)
        (let second $b)
        (union (VA first) (VA second))
        (rewrite (VA first) (VA second) :name "slots")
    "#,
    );
    let proofs = prove(
        &mut compiler,
        &mut graph,
        r#"
        (datatype B (VB Var) (WB B))
        (let wrapper (WA (VA first)))
        (check (= wrapper (WA (VA first))))
        (check (= wrapper wrapper))
    "#,
    );
    assert_eq!(proofs.len(), 2);
}

#[test]
fn guard_names_can_still_name_constructors() {
    let proofs = prove(
        &mut compiler(ProofMode::Prove),
        &mut new_egraph_with_proofs(),
        r#"
        (datatype U (V Var) (free) (K))
        (let input (free))
        (rewrite (free) (K))
        (run 1)
        (check (= input (K)))
    "#,
    );
    assert_eq!(proofs.len(), 1);
}

#[test]
fn constructor_and_guard_with_the_same_name_resolve_in_context() {
    let proofs = prove(
        &mut compiler(ProofMode::Prove),
        &mut new_egraph_with_proofs(),
        r#"
        (datatype U (V Var) (free U U) (Pair U U) (Hit))
        (let input (Pair (V $a) (V $b)))
        (let other (free (V $a) (V $b)))
        (rewrite (Pair (V $x) (V $y)) (Hit) :when ((free $x (Pair (V $x) (V $y)))))
        (rewrite (free (V $x) (V $y)) (Hit))
        (run 1)
        (check (= input (Hit)))
        (check (= other (Hit)))
    "#,
    );
    assert_eq!(proofs.len(), 2);
}

#[test]
fn native_variable_names_survive_source_replay() {
    for source in [
        r#"(datatype U (V Var) (F U) (K)) (let p (F (V $a)))
        (rewrite (F _) (K)) (run 1) (check (= p (K)))"#,
        r#"(datatype U (V Var) (F U)) (let p (F (V $a)))
        (rewrite (F _) _) (run 1) (check (= p (V $a)))"#,
        r#"(datatype U (V Var) (F U)) (let p (F (V $a)))
        (rewrite (F let) let) (run 1) (check (= p (V $a)))"#,
        r#"(datatype U (V Var) (Num i64) (Hit)) (let p (Num 1))
        (rewrite (Num $n) (Hit)) (run 1) (check (= p (Hit)))"#,
    ] {
        let proofs = prove(
            &mut compiler(ProofMode::Prove),
            &mut new_egraph_with_proofs(),
            source,
        );
        assert_eq!(proofs.len(), 1);
    }
}

#[test]
fn guard_operands_determine_their_carrier_despite_a_constructor_namesake() {
    let proofs = prove(
        &mut compiler(ProofMode::Prove),
        &mut new_egraph_with_proofs(),
        r#"
        (datatype A (VA Var) (free A A))
        (datatype B (VB Var) (Pair B B) (K))
        (let input (Pair (VB $a) (VB $b)))
        (rewrite (Pair (VB $x) (VB $y)) (K) :when ((free $x (Pair (VB $x) (VB $y)))))
        (run 1)
        (check (= input (K)))
    "#,
    );
    assert_eq!(proofs.len(), 1);
}
