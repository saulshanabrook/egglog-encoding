use egglog::{EGraph, Error, SerializeConfig, ast::sanitize_internal_names};

fn modes() -> [EGraph; 3] {
    [
        EGraph::default(),
        EGraph::new_with_term_encoding(),
        EGraph::new_with_proofs().with_proof_testing(),
    ]
}

fn global_tables(egraph: &EGraph) -> Vec<(&str, usize)> {
    let mut tables = egraph
        .functions_iter()
        .filter(|(_, f)| f.is_let_binding())
        .map(|(name, f)| (f.func_type().output().name(), egraph.get_size(name)))
        .collect::<Vec<_>>();
    tables.sort_unstable();
    tables
}

#[test]
fn shared_globals_keep_values_distinct_and_restore_scopes() {
    for mut egraph in modes() {
        egraph
            .parse_and_run_program(
                None,
                r#"
                (datatype Math (Num i64))
                (let $one 1)
                (let $two (+ $one 1))
                (let $a (Num $one))
                (let $b (Num $two))
                (let $alias $a)
                (fail (check (= $a $b)))
                (check (= $alias $a))
                (push)
                (let $temporary true)
                (let $scoped (Num 3))
                (union $a $b)
                (check (= $alias $b))
                (pop)
                (fail (check (= $a $b)))
                (let $temporary "restored")
                (check (= $temporary "restored"))
                "#,
            )
            .unwrap();
        assert_eq!(
            global_tables(&egraph),
            [("Math", 3), ("String", 1), ("i64", 2)]
        );
        assert_eq!(egraph.get_size("$a"), 1);
    }
}

#[test]
fn shared_globals_survive_failed_writes_and_rejected_declarations() {
    // Proof checking requires a program whose bindings can all be evaluated.
    for mut egraph in [EGraph::default(), EGraph::new_with_term_encoding()] {
        egraph
            .parse_and_run_program(
                None,
                "(datatype Math (Num i64)) (constructor $taken () Math)",
            )
            .unwrap();
        assert!(matches!(
            egraph.parse_and_run_program(None, "(let $taken 1)"),
            Err(Error::Shadowing(..))
        ));
        assert!(global_tables(&egraph).is_empty());
        assert!(
            egraph
                .parse_and_run_program(None, "(let $failed (/ 1 0))")
                .is_err()
        );
        assert_eq!(egraph.get_size("$failed"), 0);
        egraph
            .parse_and_run_program(
                None,
                r#"
                (let $good 2)
                (let $next 3)
                (check (= $good 2))
                (check (= $next 3))
                "#,
            )
            .unwrap();
        assert_eq!(global_tables(&egraph), [("i64", 2)]);
    }
}

#[test]
fn shared_globals_keep_source_names_in_output() {
    let source = r#"
        (datatype Math (Num i64))
        (let $a (Num 1))
        (let $alias $a)
        (let $n 2)
        (print-function $a)
        (print-function $n :mode csv)
    "#;
    for mut egraph in modes() {
        let outputs = egraph.parse_and_run_program(None, source).unwrap();
        let printed = outputs.iter().map(ToString::to_string).collect::<String>();
        assert!(printed.contains("($a) -> (Num 1)"), "{printed}");
        assert!(printed.contains("$n,2\n"), "{printed}");
        let serialized = egraph.serialize(SerializeConfig::default());
        let bindings = serialized
            .egraph
            .class_data
            .values()
            .filter_map(|data| data.extra.get("let"))
            .cloned()
            .collect::<Vec<_>>()
            .join(", ");
        assert!(bindings.contains("$a"), "{bindings}");
        assert!(bindings.contains("$alias"), "{bindings}");
    }
}

#[test]
fn shared_globals_desugaring_can_be_replayed() {
    let source = r#"
        (datatype Math (Num i64))
        (let $a (Num 1))
        (let $b (Num 2))
        (let $n 3)
        (check (= $a (Num 1)))
        (check (= $n 3))
        (print-function $a)
        (print-function $n :mode csv)
    "#;
    for mut egraph in [EGraph::default(), EGraph::new_with_term_encoding()] {
        let resolved = egraph.resolve_program(None, source).unwrap();
        let program = sanitize_internal_names(&resolved)
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        let mut replay = EGraph::default();
        let outputs = replay.parse_and_run_program(None, &program).unwrap();
        let printed = outputs.iter().map(ToString::to_string).collect::<String>();
        assert!(printed.contains("($a) -> (Num 1)"), "{printed}");
        assert!(printed.contains("$n,3\n"), "{printed}");
        assert_eq!(global_tables(&replay), [("Math", 2), ("i64", 1)]);
    }
}

#[test]
fn shared_globals_preserve_begin_local_scope() {
    let mut egraph = EGraph::default();
    egraph
        .parse_and_run_program(
            None,
            r#"
        (datatype Math (Num i64))
        (let $n 2)
        (let $block (begin (let local (+ $n 1)) (Num local)))
        (check (= $block (Num 3)))
        (let $next (begin (let local (+ $n 2)) (Num local)))
        (check (= $next (Num 4)))
    "#,
        )
        .unwrap();
    assert_eq!(global_tables(&egraph), [("Math", 2), ("i64", 1)]);
}
