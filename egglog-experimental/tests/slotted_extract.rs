use egglog::CommandOutput;
use egglog_experimental::slotted::{Compiler, new_egraph};

fn extract(source: &str) -> Vec<(u64, String)> {
    let mut compiler = Compiler::default();
    let mut graph = new_egraph();
    let program = compiler.compile(None, source).unwrap();
    let outputs = graph.parse_and_run_program(None, &program).unwrap();
    let extracted: Vec<_> = outputs
        .into_iter()
        .filter_map(|output| {
            if let CommandOutput::ExtractBest(dag, cost, term) = output {
                Some((cost, dag.to_string(term)))
            } else {
                None
            }
        })
        .collect();
    for (_, term) in &extracted {
        let check = compiler
            .compile(
                None,
                &format!(
                    "(push) (let reconstructed {term}) (check (= result reconstructed)) (pop)"
                ),
            )
            .unwrap();
        graph.parse_and_run_program(None, &check).unwrap();
    }
    extracted
}

#[test]
fn source_terms_preserve_free_names_and_freshen_binders() {
    let outputs = extract(
        "(datatype Expr (Lam Expr Expr :binder 0) (Pair Expr Expr))
         (let result (Lam $bound (Pair $bound $free)))
         (extract result)",
    );
    assert_eq!(outputs, [(4, "(Lam $0 (Pair $0 $free))".into())]);
}

#[test]
fn binder_scope_does_not_capture_other_children() {
    let outputs = extract(
        "(datatype Expr (Let Expr Expr Expr :binder 1) (Pair Expr Expr))
         (let result (Let $same $same (Pair $same $free)))
         (extract result)",
    );
    assert_eq!(outputs, [(5, "(Let $same $0 (Pair $0 $free))".into())]);
}

#[test]
fn nested_binders_and_numeric_free_names_remain_distinct() {
    let outputs = extract(
        "(datatype Expr (Lam Expr Expr :binder 0) (Pair Expr Expr))
         (let result (Lam $outer (Lam $inner (Pair $outer (Pair $inner $0)))))
         (extract result)",
    );
    assert_eq!(
        outputs,
        [(7, "(Lam $1 (Lam $2 (Pair $1 (Pair $2 $0))))".into())]
    );
}

#[test]
fn multiple_binders_cover_only_the_following_child() {
    let outputs = extract(
        "(datatype Expr (Bind Expr Expr Expr Expr :binder 0 1) (Pair Expr Expr))
         (let result (Bind $a $b (Pair $a $b) $a))
         (extract result)",
    );
    assert_eq!(outputs, [(5, "(Bind $0 $1 (Pair $0 $1) $a)".into())]);
}

#[test]
fn payloads_keep_their_source_positions_and_escaping() {
    let outputs = extract(
        r#"
        (datatype Expr (Tagged String Expr i64 Expr :binder 0))
        (let result (Tagged "a\"b\\c" $x 7 $x))
        (extract result)
    "#,
    );
    assert_eq!(outputs, [(2, r#"(Tagged "a\"b\\c" $0 7 $0)"#.into())]);
}

#[test]
fn bare_slots_and_aliases_can_be_extracted() {
    for slot in ["$free", "$-1", "$0", "$a0"] {
        let outputs = extract(&format!(
            "(sort Expr) (let original {slot}) (let result original) (extract result)"
        ));
        assert_eq!(outputs, [(1, slot.into())]);
    }
}

#[test]
fn extraction_uses_the_smallest_source_tree_at_the_current_leader() {
    let outputs = extract(
        "(datatype Expr (Num i64) (Pair Expr Expr) (Lam Expr Expr :binder 0))
         (let small (Lam $x (Num 1)))
         (let result (Pair (Num 2) (Num 3)))
         (union result small)
         (extract result)",
    );
    assert_eq!(outputs, [(2, "(Lam $0 (Num 1))".into())]);
}

#[test]
fn extraction_preserves_the_requested_names_after_slot_shrinking() {
    let outputs = extract(
        "(datatype Expr (Pair Expr Expr) (Wrap Expr))
         (let small (Wrap $right))
         (let result (Pair $left $right))
         (union result small)
         (extract result)",
    );
    assert_eq!(outputs, [(2, "(Wrap $right)".into())]);
}

#[test]
fn extraction_constructs_a_new_term_and_supports_multiple_carriers() {
    let mut compiler = Compiler::default();
    let source = compiler
        .compile(
            None,
            "(datatype* (A (Num i64)) (B (Wrap B))) (extract (Wrap $free)) (extract (Num 9))",
        )
        .unwrap();
    let outputs = new_egraph().parse_and_run_program(None, &source).unwrap();
    let outputs: Vec<_> = outputs
        .into_iter()
        .filter_map(|output| {
            if let CommandOutput::ExtractBest(dag, _, term) = output {
                Some(dag.to_string(term))
            } else {
                None
            }
        })
        .collect();
    assert_eq!(outputs, ["(Wrap $free)", "(Num 9)"]);
}

#[test]
fn a_class_without_a_finite_tree_returns_an_error() {
    let mut compiler = Compiler::default();
    let mut graph = new_egraph();
    let source = compiler
        .compile(
            None,
            "(datatype Expr (Null) (Wrap Expr)) (let result (Null)) (union result (Wrap result))",
        )
        .unwrap();
    graph.parse_and_run_program(None, &source).unwrap();
    graph
        .parse_and_run_program(None, "(delete (Null))")
        .unwrap();
    let source = compiler.compile(None, "(extract result)").unwrap();
    let error = graph.parse_and_run_program(None, &source).unwrap_err();
    assert!(
        error.to_string().contains("no finite tree representative"),
        "{error}"
    );
}
