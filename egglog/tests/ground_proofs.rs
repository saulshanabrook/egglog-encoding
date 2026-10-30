use egglog::{CommandOutput, EGraph, TermDag};

fn graph(program: &str) -> EGraph {
    let mut graph = EGraph::new_with_proofs();
    graph.parse_and_run_program(None, program).unwrap();
    graph
}

fn prove(graph: &mut EGraph, terms: &TermDag, left: usize, right: usize, sort: &str) -> String {
    let sort = graph.type_info().get_sort_by_name(sort).unwrap().clone();
    let before = graph.num_nodes();
    let (store, proof) = graph.prove_equal_terms(terms, left, right, sort).unwrap();
    assert_eq!(graph.num_nodes(), before, "certification must not add rows");
    assert_eq!(
        store.term_dag().to_string(store.get(proof).lhs()),
        terms.to_string(left)
    );
    assert_eq!(
        store.term_dag().to_string(store.get(proof).rhs()),
        terms.to_string(right)
    );
    store.proof_to_string(proof)
}

#[test]
fn both_endpoints_can_be_rule_derived() {
    let mut graph = graph(
        "(datatype E (A) (B) (C)) (A)
        (rule ((= a (A))) ((B) (C) (union (B) (C))) :name \"derive\")
        (run 1)",
    );
    let mut terms = TermDag::default();
    let b = terms.app("B".into(), vec![]);
    let c = terms.app("C".into(), vec![]);
    assert!(prove(&mut graph, &terms, b, c, "E").contains("derive"));
}

#[test]
fn certification_preserves_requested_order_and_duplicate_outputs() {
    let mut graph = graph(
        "(datatype E (A) (B) (C) (Missing)) (A)
        (rule ((= a (A))) ((B) (C) (union a (B)) (union a (C)))) (run 1)",
    );
    let sort = graph.type_info().get_sort_by_name("E").unwrap().clone();
    let mut terms = TermDag::default();
    let c = terms.app("C".into(), vec![]);
    let a = terms.app("A".into(), vec![]);
    let b = terms.app("B".into(), vec![]);
    let missing = terms.app("Missing".into(), vec![]);
    let before = graph.num_nodes();
    let (store, proofs) = graph
        .prove_extracted_terms(&terms, b, &[c, a, c, b], sort.clone())
        .unwrap();
    let endpoints = proofs
        .into_iter()
        .map(|id| {
            let proof = store.get(id);
            assert_eq!(store.term_dag().to_string(proof.lhs()), "(B)");
            store.term_dag().to_string(proof.rhs())
        })
        .collect::<Vec<_>>();
    assert_eq!(endpoints, ["(C)", "(A)", "(C)", "(B)"]);

    let (_, proofs) = graph
        .prove_extracted_terms(&terms, b, &[], sort.clone())
        .unwrap();
    assert!(proofs.is_empty());
    let error = graph
        .prove_extracted_terms(&terms, missing, &[], sort)
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("Could not find term (Missing) in the e-graph")
    );
    assert_eq!(graph.num_nodes(), before);
}

#[test]
fn congruence_certifies_syntax_that_was_never_inserted() {
    let mut graph = graph(
        "(datatype E (A) (B) (F E)) (F (A))
        (rule ((= a (A))) ((B) (union a (B))) :name \"derive\")
        (run 1)",
    );
    let mut terms = TermDag::default();
    let a = terms.app("A".into(), vec![]);
    let b = terms.app("B".into(), vec![]);
    let fa = terms.app("F".into(), vec![a]);
    let fb = terms.app("F".into(), vec![b]);
    prove(&mut graph, &terms, fb, fa, "E");
}

#[test]
fn missing_evidence_and_unequal_terms_fail_without_insertion() {
    let mut graph = graph("(datatype E (A) (B) (Missing)) (A) (B)");
    let sort = graph.type_info().get_sort_by_name("E").unwrap().clone();
    let mut terms = TermDag::default();
    let a = terms.app("A".into(), vec![]);
    let b = terms.app("B".into(), vec![]);
    let missing = terms.app("Missing".into(), vec![]);
    let before = graph.num_nodes();
    for (left, right) in [(a, b), (missing, a), (a, missing), (missing, missing)] {
        assert!(
            graph
                .prove_equal_terms(&terms, left, right, sort.clone())
                .is_err()
        );
        assert_eq!(graph.num_nodes(), before);
    }
}

#[test]
fn containers_reuse_existing_row_projections() {
    let mut graph = graph(
        "(datatype E (A) (B)) (sort V (Vec E)) (datatype Box (Wrap V))
        (Wrap (vec-of (A)))
        (rule ((= a (A))) ((B) (union a (B))) :name \"derive\")
        (run 1)",
    );
    let mut terms = TermDag::default();
    let a = terms.app("A".into(), vec![]);
    let b = terms.app("B".into(), vec![]);
    let va = terms.app("vec-of".into(), vec![a]);
    let vb = terms.app("vec-of".into(), vec![b]);
    let wa = terms.app("Wrap".into(), vec![va]);
    let wb = terms.app("Wrap".into(), vec![vb]);
    prove(&mut graph, &terms, wb, wa, "Box");
}

#[test]
fn shared_container_can_be_evaluated_then_proved_in_different_parents() {
    let mut graph = graph(
        "(datatype E (A) (B)) (sort V (Vec E))
        (datatype Box (Measured i64 V) (Wrap V) (Both Box Box))
        (Both (Measured 1 (vec-of (A))) (Wrap (vec-of (A))))
        (B) (union (A) (B)) (run 1)",
    );
    // The same vector is first an argument to scalar evaluation, then needs
    // existence evidence from two different constructor rows.
    let proofs = extracted(
        &mut graph,
        "(prove-extract (Both
            (Measured (vec-length (vec-of (B))) (vec-of (B)))
            (Wrap (vec-of (B)))))",
    );
    assert_eq!(
        proofs[0].0,
        "(Both (Measured 1 (vec-of (B))) (Wrap (vec-of (B))))"
    );
}

#[test]
fn container_roots_are_rejected_without_insertion() {
    let mut graph = graph("(datatype E (A)) (sort V (Vec E)) (A)");
    let sort = graph.type_info().get_sort_by_name("V").unwrap().clone();
    let mut terms = TermDag::default();
    let a = terms.app("A".into(), vec![]);
    let value = terms.app("vec-of".into(), vec![a]);
    let before = graph.num_nodes();
    let error = graph
        .prove_equal_terms(&terms, value, value, sort)
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("proof extraction does not support container roots (sort V)")
    );
    assert_eq!(graph.num_nodes(), before);
}

#[test]
fn function_roots_project_their_existing_output_evidence() {
    let mut graph = graph(
        "(datatype E (A) (B)) (function root () E :merge old)
        (set (root) (A)) (rewrite (A) (B)) (run 1)",
    );
    let sort = graph.type_info().get_sort_by_name("E").unwrap().clone();
    let mut terms = TermDag::default();
    let root = terms.app("root".into(), vec![]);
    let b = terms.app("B".into(), vec![]);
    let before = graph.num_nodes();
    let (store, proof) = graph.prove_equal_terms(&terms, root, b, sort).unwrap();
    assert_eq!(store.term_dag().to_string(store.get(proof).lhs()), "(A)");
    assert_eq!(store.term_dag().to_string(store.get(proof).rhs()), "(B)");
    assert_eq!(graph.num_nodes(), before);
}

fn extracted(graph: &mut EGraph, command: &str) -> Vec<(String, String)> {
    let before = graph.num_nodes();
    let outputs = graph.parse_and_run_program(None, command).unwrap();
    assert_eq!(
        graph.num_nodes(),
        before,
        "prove-extract must not insert rows"
    );
    let CommandOutput::ProveExtract {
        proof_store,
        proof_ids,
    } = outputs
        .iter()
        .find(|output| matches!(output, CommandOutput::ProveExtract { .. }))
        .unwrap()
    else {
        panic!("expected extraction proofs");
    };
    proof_ids
        .iter()
        .map(|id| {
            let proof = proof_store.get(*id);
            (
                proof_store.term_dag().to_string(proof.lhs()),
                proof_store.term_dag().to_string(proof.rhs()),
            )
        })
        .collect()
}

#[test]
fn command_proves_all_variants_without_inserting_the_input() {
    let mut graph = graph(
        r#"(datatype E (A) (B) (F E)) (F (A))
        (rule ((= a (A))) ((B) (union a (B))) :name "derive") (run 1)"#,
    );
    let proofs = extracted(&mut graph, "(prove-extract (F (B)) 3)");
    assert!(!proofs.is_empty());
    assert!(proofs.iter().all(|(left, _)| left == "(F (B))"));
    let before = graph.num_nodes();
    let error = graph
        .parse_and_run_program(None, "(prove-extract (F (F (A))))")
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("Could not find term (F (F (A))) in the e-graph"),
        "{error}"
    );
    assert_eq!(graph.num_nodes(), before);
}

#[test]
fn command_preserves_a_globals_original_term() {
    let mut graph = graph(
        r#"(datatype E (A) (B) (F E)) (let input (F (A)))
        (rewrite (A) (B)) (run 1)"#,
    );
    let proofs = extracted(&mut graph, "(prove-extract input)");
    assert_eq!(proofs[0].0, "(F (A))");
}

#[test]
fn container_normalization_and_nesting() {
    let mut graph = graph(
        r#"(datatype E (A) (B))
        (sort S (Set E)) (sort VV (Vec S)) (datatype Box (Wrap VV))
        (Wrap (vec-of (set-of (A) (B))))
        (union (A) (B)) (run 1)"#,
    );
    let proofs = extracted(
        &mut graph,
        "(prove-extract (Wrap (vec-of (set-of (A) (B)))))",
    );
    assert_eq!(proofs[0].0, "(Wrap (vec-of (set-of (A) (B))))");
}

#[test]
fn a_rule_derived_container_reuses_its_pre_rebuild_witness() {
    let mut graph = graph(
        r#"(datatype E (A) (B)) (sort S (Set E)) (sort V (Vec S))
        (datatype Box (Wrap V)) (A) (B)
        (rule ((= a (A)) (= b (B)))
              ((Wrap (vec-of (set-of a b)))) :name "build-container")
        (run 1) (union (A) (B)) (run 1)"#,
    );
    let proofs = extracted(
        &mut graph,
        "(prove-extract (Wrap (vec-of (set-of (A) (B)))))",
    );
    assert_eq!(proofs[0].0, "(Wrap (vec-of (set-of (A) (B))))");
    assert_eq!(proofs[0].1, "(Wrap (vec-of (set-of (A))))");
}

#[test]
fn normalization_cannot_invent_discarded_container_elements() {
    let mut graph = graph(
        "(datatype E (A) (B)) (sort S (Set E)) (datatype Box (Wrap S))
        (Wrap (set-of (A))) (B) (union (A) (B)) (run 1)",
    );
    let before = graph.num_nodes();
    let error = graph
        .parse_and_run_program(None, "(prove-extract (Wrap (set-of (A) (B))))")
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("Could not find term (set-of (A) (B)) in the e-graph"),
        "{error}"
    );
    assert_eq!(graph.num_nodes(), before);
}

#[test]
fn contextual_empty_containers_and_base_containers() {
    let mut graph = graph(
        r#"(datatype E (A)) (sort V (Vec E)) (sort VI (Vec i64))
        (datatype Box (Wrap V VI)) (Wrap (vec-empty) (vec-of 1 2))"#,
    );
    let proofs = extracted(
        &mut graph,
        "(prove-extract (Wrap (vec-empty) (vec-of 1 2)))",
    );
    assert_eq!(proofs[0].0, "(Wrap (vec-empty) (vec-of 1 2))");
}

#[test]
fn custom_function_container_arguments() {
    let mut graph = graph(
        r#"(datatype E (A)) (sort V (Vec E))
        (function get (V) E :merge old) (set (get (vec-of (A))) (A))"#,
    );
    let proofs = extracted(&mut graph, "(prove-extract (get (vec-of (A))))");
    assert_eq!(proofs[0], ("(A)".into(), "(A)".into()));
}

#[test]
fn container_roots_are_rejected_even_when_evidence_exists() {
    let mut graph = graph(
        r#"(datatype E (A)) (sort V (Vec E)) (sort VV (Vec V))
        (datatype Box (Wrap VV)) (Wrap (vec-of (vec-of (A))))
        (function root () V :merge old) (set (root) (vec-of (A)))"#,
    );
    let before = graph.num_nodes();
    for command in ["(prove-extract (vec-of (A)))", "(prove-extract (root))"] {
        let error = graph.parse_and_run_program(None, command).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("does not support container roots"),
            "{error}"
        );
        assert_eq!(graph.num_nodes(), before);
    }
    let mut terms = TermDag::default();
    let root = terms.app("root".into(), vec![]);
    let sort = graph.type_info().get_sort_by_name("V").unwrap().clone();
    let error = graph
        .prove_extracted_terms(&terms, root, &[], sort)
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("does not support container roots")
    );
    assert_eq!(graph.num_nodes(), before);
    extracted(&mut graph, "(prove-extract (Wrap (vec-of (vec-of (A)))))");
}

#[test]
fn container_selectors_project_elements_from_existing_functions() {
    let mut graph = graph(
        r#"(datatype E (A) (B)) (sort V (Vec E)) (sort VV (Vec V))
        (function root () VV :merge old) (set (root) (vec-of (vec-of (A))))
        (rewrite (A) (B)) (run 1)"#,
    );
    extracted(&mut graph, "(prove-extract (vec-get (vec-get (root) 0) 0))");
    assert_eq!(
        extracted(
            &mut graph,
            "(prove-extract (+ (vec-length (vec-get (root) 0)) 2))"
        )[0],
        ("3".into(), "3".into())
    );
}

#[test]
fn maps_reorder_keys_without_changing_proof_format() {
    let mut graph = graph(
        r#"(datatype E (A) (B)) (sort M (Map i64 E))
        (datatype Box (Wrap M)) (Wrap (map-of 2 (A) 1 (B)))
        (union (A) (B)) (run 1)"#,
    );
    let proofs = extracted(&mut graph, "(prove-extract (Wrap (map-of 2 (A) 1 (B))))");
    assert_eq!(proofs[0].0, "(Wrap (map-of 1 (B) 2 (A)))");
}

#[test]
fn encoded_replay_preserves_prove_extract() {
    let source = r#"(datatype E (A) (B) (F E)) (let input (F (A)))
        (rewrite (A) (B)) (run 1) (prove-extract input)"#;
    let encoded = EGraph::new_with_proofs()
        .resolve_program(None, source)
        .unwrap()
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n");
    let mut replay = EGraph::default();
    let program = replay.parse_program(None, source).unwrap();
    replay.set_proof_checking_program(program, false).unwrap();
    replay.ensure_no_reserved_symbols(false);
    let outputs = replay.parse_and_run_program(None, &encoded).unwrap();
    assert!(!CommandOutput::snapshot_proofs_only(&outputs).is_empty());
}

#[test]
fn scalar_evaluation_does_not_claim_temporary_container_existence() {
    let mut graph = graph("(datatype E (A)) (sort V (Vec E)) (A)");
    assert_eq!(
        extracted(&mut graph, "(prove-extract (vec-length (vec-of (A))))")[0],
        ("1".into(), "1".into())
    );
    assert_eq!(
        extracted(&mut graph, "(prove-extract (vec-get (vec-of (A)) 0))")[0],
        ("(A)".into(), "(A)".into())
    );
}

#[test]
fn late_globals_preserve_source_even_after_deletion() {
    let mut graph = graph(
        r#"(datatype E (A) (B)) (A) (B) (union (A) (B)) (run 1)
        (let input (B)) (delete (B))"#,
    );
    let proofs = extracted(&mut graph, "(prove-extract input)");
    assert_eq!(proofs[0].0, "(B)");
}

#[test]
fn failures_and_scope_restore_are_read_only() {
    let mut graph = graph("(datatype E (A)) (A)");
    let before = graph.num_nodes();
    for command in ["(prove-extract (A) -1)", "(prove-extract (A) true)"] {
        assert!(graph.parse_and_run_program(None, command).is_err());
        assert_eq!(graph.num_nodes(), before);
    }
    graph
        .parse_and_run_program(
            None,
            "(push) (sort V (Vec E)) (datatype Box (Wrap V)) (Wrap (vec-of (A)))",
        )
        .unwrap();
    extracted(&mut graph, "(prove-extract (Wrap (vec-of (A))))");
    graph.parse_and_run_program(None, "(pop)").unwrap();
    extracted(&mut graph, "(prove-extract (A))");
    assert!(
        graph
            .parse_and_run_program(None, "(prove-extract (Wrap (vec-of (A))))")
            .is_err()
    );
}

#[test]
fn global_aliases_keep_their_provenance() {
    let mut graph = graph(
        r#"(datatype E (A) (B)) (A) (B)
        (rewrite (B) (A)) (run 1) (let first (B)) (let second first) (delete (B))"#,
    );
    assert_eq!(extracted(&mut graph, "(prove-extract second)")[0].0, "(B)");

    let mut terms = TermDag::default();
    let alias = terms.app("second".into(), vec![]);
    let a = terms.app("A".into(), vec![]);
    // Unreachable malformed syntax does not affect certification.
    let invalid = terms.app("missing".into(), vec![usize::MAX]);
    let sort = graph.type_info().get_sort_by_name("E").unwrap().clone();
    let before = graph.num_nodes();
    let (store, proof) = graph
        .prove_equal_terms(&terms, alias, a, sort.clone())
        .unwrap();
    assert_eq!(store.term_dag().to_string(store.get(proof).lhs()), "(B)");
    assert_eq!(store.term_dag().to_string(store.get(proof).rhs()), "(A)");
    assert_eq!(graph.num_nodes(), before);
    for root in [invalid, usize::MAX] {
        assert!(
            graph
                .prove_equal_terms(&terms, root, a, sort.clone())
                .is_err()
        );
    }
}

#[test]
fn global_aliases_follow_rebindings_after_popped_scopes() {
    for bindings in [
        "(let original (A))
         (push) (let rebound original) (pop)
         (let rebound (B)) (let current rebound)",
        "(let first (A)) (let second (B))
         (push) (let rebound first)
         (push) (let nested rebound) (pop) (pop)
         (let rebound second) (let current rebound)",
        "(push) (let scoped (A)) (let rebound scoped) (pop)
         (let rebound (B)) (let current rebound)",
    ] {
        let mut graph = graph(&format!("(datatype E (A) (B)) {bindings}"));
        assert_eq!(
            extracted(&mut graph, "(prove-extract current)")[0],
            ("(B)".into(), "(B)".into()),
            "{bindings}"
        );
        let mut terms = TermDag::default();
        let current = terms.app("current".into(), vec![]);
        let b = terms.app("B".into(), vec![]);
        let sort = graph.type_info().get_sort_by_name("E").unwrap().clone();
        let before = graph.num_nodes();
        let (store, proof) = graph.prove_equal_terms(&terms, current, b, sort).unwrap();
        assert_eq!(store.term_dag().to_string(store.get(proof).lhs()), "(B)");
        assert_eq!(store.term_dag().to_string(store.get(proof).rhs()), "(B)");
        assert_eq!(graph.num_nodes(), before);
    }
}

#[test]
fn selector_can_return_a_nonleader() {
    let mut graph = graph("(datatype E (A) (B)) (sort V (Vec E)) (A) (B) (union (A) (B)) (run 1)");
    assert_eq!(
        extracted(&mut graph, "(prove-extract (vec-get (vec-of (B)) 0))")[0].0,
        "(B)"
    );
}

#[test]
fn repeated_equal_elements_keep_the_requested_representative_at_each_position() {
    let mut graph = graph(
        "(datatype E (A) (B)) (sort V (Vec E)) (datatype Box (Wrap V)) (Wrap (vec-of (A) (A))) (B) (union (A) (B)) (run 1)",
    );
    let proofs = extracted(&mut graph, "(prove-extract (Wrap (vec-of (A) (B))))");
    assert_eq!(proofs[0].0, "(Wrap (vec-of (A) (B)))");
}

#[test]
fn empty_container_roots_are_rejected_at_each_sort() {
    let mut graph = graph(
        "(datatype A (MakeA)) (datatype B (MakeB)) (sort As (Vec A)) (sort Bs (Vec B)) (datatype Box (Wrap Bs)) (Wrap (vec-empty))",
    );
    let mut terms = TermDag::default();
    let empty = terms.app("vec-empty".into(), vec![]);
    for name in ["As", "Bs"] {
        let sort = graph.type_info().get_sort_by_name(name).unwrap().clone();
        let error = graph
            .prove_equal_terms(&terms, empty, empty, sort)
            .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("does not support container roots")
        );
    }
    extracted(&mut graph, "(prove-extract (Wrap (vec-empty)))");
}

#[test]
fn container_primitives_use_the_types_of_their_result_elements() {
    let mut graph = graph(
        "(datatype E (A) (B)) (sort S (Set E)) (datatype Box (Wrap S)) (A) (Wrap (set-of (B))) (union (A) (B)) (run 1)",
    );
    let proofs = extracted(
        &mut graph,
        "(prove-extract (Wrap (set-intersect (set-of (B)) (set-of (B)))))",
    );
    assert_eq!(proofs[0].0, "(Wrap (set-of (B)))");
}

#[test]
fn proof_testing_certifies_plain_extracts_and_delimits_each_proof() {
    use egglog::ast::parse_sexps;

    let mut graph = EGraph::new_with_proofs().with_proof_testing();
    graph
        .parse_and_run_program(
            None,
            r#"
        (datatype E (A) (B) (C) (Missing)) (A)
        (rule ((= a (A))) ((B) (C) (union a (B)) (union a (C))) :name "derive")
        (run 1)
    "#,
        )
        .unwrap();
    let before = graph.num_nodes();
    let outputs = graph
        .parse_and_run_program(None, "(extract (C) 3) (extract (B))")
        .unwrap();
    let counts = outputs
        .iter()
        .filter_map(|output| match output {
            CommandOutput::ProveExtract { proof_ids, .. } => Some(proof_ids.len()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(counts, vec![3, 1]);
    let printed = CommandOutput::snapshot_proofs_only(&outputs);
    // Local let bindings must stay inside their proof's block. Parsing the
    // whole stream must recover exactly one top-level expression per proof.
    assert!(printed.contains("(let "));
    assert_eq!(parse_sexps(None, &printed).unwrap().len(), 4);
    assert_eq!(graph.num_nodes(), before);
    let error = graph
        .parse_and_run_program(None, "(extract (Missing))")
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("Could not find term (Missing) in the e-graph")
    );
    assert_eq!(graph.num_nodes(), before);
}
