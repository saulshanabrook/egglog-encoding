use super::*;

// Compare source preparation with the existing resolved-command compiler.
fn run_ground_action_oracle(
    graph: &mut EGraph,
    source: &str,
    direct: bool,
) -> Result<Vec<String>, Error> {
    if direct {
        return graph
            .parse_and_run_program(None, source)
            .map(|outputs| outputs.iter().map(ToString::to_string).collect());
    }
    let mut outputs = Vec::new();
    for command in graph.parse_program(None, source)? {
        for command in graph.resolve_command(command)?.desugared {
            outputs.extend(
                graph
                    .run_command(ExecutableCommand::Resolved(command))?
                    .iter()
                    .map(ToString::to_string),
            );
        }
    }
    Ok(outputs)
}

fn assert_action_graphs_equal(left: &EGraph, right: &EGraph) {
    assert_eq!(
        left.functions.keys().collect::<Vec<_>>(),
        right.functions.keys().collect::<Vec<_>>()
    );
    for (name, function) in &left.functions {
        let mut left_rows = Vec::new();
        left.backend.for_each(function.backend_id, |row| {
            left_rows.push((row.vals.to_vec(), row.subsumed))
        });
        let mut right_rows = Vec::new();
        right
            .backend
            .for_each(right.functions[name].backend_id, |row| {
                right_rows.push((row.vals.to_vec(), row.subsumed))
            });
        left_rows.sort();
        right_rows.sort();
        assert_eq!(left_rows, right_rows, "{name}");
    }
}

#[test]
fn ground_actions_match_compiled_execution() {
    for threads in [1, 4] {
        let mut direct = EGraph::default();
        let mut compiled = EGraph::default();
        for graph in [&mut direct, &mut compiled] {
            graph.backend.set_num_threads(threads);
            graph
                .parse_and_run_program(
                    None,
                    "(datatype T (A) (B) (N1) (N2) (Pair T T) (Num i64))
                     (relation seen (T))
                     (function missing (T) T :no-merge)
                     (function tuple-result (T) (T T) :merge (values old0 old1))
                     (index Occ missing (any 0 1))
                     (let $global (A))",
                )
                .unwrap();
        }
        for (source, succeeds) in [
            ("(Pair (N1) (Pair (N1) (N2)))", true),
            ("(seen (Pair (A) (A)))", true),
            ("(union (A) (A))", true),
            ("(Pair (B) (B))", true),
            ("(union (A) (B))", true),
            ("(union (A) (B))", true),
            ("(check (= (Pair (A) (A)) (Pair (B) (B))))", true),
            ("(push)", true),
            ("(constructor Temporary () T) (Temporary)", true),
            ("(pop)", true),
            ("(Temporary)", false),
            ("(Num (+ 1 2))", true),
            ("(Pair $global (N1))", true),
            ("(begin (Pair (N2) (N2)))", true),
            ("(begin (let local (N2)) (Pair local local))", true),
            ("(missing (Pair (N2) (A)))", false),
            ("(set (missing (N1)) (N2))", true),
            ("(delete (missing (N1)))", true),
            ("(tuple-result (A))", false),
            ("(Occ (A) (A) (B))", false),
            ("(Pair (A) unbound)", false),
            ("(Pair (A))", false),
        ] {
            let actual = run_ground_action_oracle(&mut direct, source, true);
            let expected = run_ground_action_oracle(&mut compiled, source, false);
            assert_eq!(actual.is_ok(), succeeds, "{source}: {actual:?}");
            assert_eq!(expected.is_ok(), succeeds, "{source}: {expected:?}");
            if let (Ok(actual), Ok(expected)) = (actual, expected) {
                assert_eq!(actual, expected, "{source}");
            }
            assert_action_graphs_equal(&direct, &compiled);
        }
    }
}

#[test]
fn ground_actions_check_eligibility_before_mutation() {
    for mode in 0..3 {
        let mut graph = match mode {
            0 => EGraph::default(),
            1 => EGraph::new_with_term_encoding(),
            _ => EGraph::new_with_proofs(),
        };
        graph
            .parse_and_run_program(
                None,
                "(datatype T (A) (N1) (N2) (Pair T T) (Num i64))
                     (let $global (A))",
            )
            .unwrap();
        if mode == 0 {
            graph
                .parse_and_run_program(
                    None,
                    "(function custom (T) T :no-merge)
                     (index Occ custom (any 0 1))",
                )
                .unwrap();
        }
        for (source, admitted) in [
            ("(Pair (N1) (N2))", true),
            ("(Pair (N1) (missing))", false),
            ("(union (N1) (+ 1 2))", false),
            ("(union (A) (Pair (A) (A)))", true),
            ("(Num 1)", false),
            ("(+ 1 2)", false),
            ("(custom (A))", false),
            ("(Pair $global (A))", false),
            ("(set (custom (A)) (N1))", false),
            ("(delete (custom (A)))", false),
            ("(begin (A))", false),
        ] {
            if mode != 0 && !admitted {
                continue;
            }
            let before = graph.clone();
            let commands = graph.parse_program(None, source).unwrap();
            let accepted = commands.iter().any(|command| match command {
                Command::Action(action) => graph
                    .prepare_ground_action(action, &mut GroundActionCache::default())
                    .is_some(),
                _ => false,
            });
            assert_eq!(accepted, admitted && mode == 0, "mode {mode}: {source}");
            assert_action_graphs_equal(&graph, &before);
            assert!(!graph.backend.flush_updates());
        }
    }
}

#[test]
fn ground_actions_keep_numeric_constructor_names_distinct() {
    let source = "(datatype T (A) (A1))
                      (begin (A) (A) (A) (A) (A))
                      (union (A) (A1))
                      (check (= (A) (A1)))";
    for direct in [true, false] {
        run_ground_action_oracle(&mut EGraph::default(), source, direct).unwrap();
    }
}

#[test]
fn insertion_batches_ignore_unrelated_globals_and_containers() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(
            None,
            "(datatype T (A) (B) (F T))
            (sort Unused (Vec T)) (let $unrelated 7)",
        )
        .unwrap();
    let actions = graph.parse_program(None, "(F (A)) (F (B))").unwrap();
    assert!(actions.iter().all(|command| {
        match command {
            Command::Action(action) => graph
                .prepare_ground_action(action, &mut GroundActionCache::default())
                .is_some(),
            _ => false,
        }
    }));
    graph
        .parse_and_run_program(None, "(F (A)) (F (B))")
        .unwrap();
    assert_eq!(graph.get_size("F"), 2);
    graph
        .parse_and_run_program(
            None,
            "(check (= $unrelated 7))
            (check (= (F (A)) (F (A))))",
        )
        .unwrap();
}

#[test]
fn batches_flush_for_keyed_reads_globals_and_deletes() {
    let source = "(datatype T (A) (B) (F T))
            (function f () i64 :no-merge)
            (function g () i64 :no-merge)
            (function out () i64 :no-merge)
            (function value (T) i64 :no-merge)
            (F (A)) (set (f) 1) (set (g) (f)) (check (= (g) 1))
            (delete (f)) (fail (check (= (f) 1)))
            (let $a (A)) (F $a)
            (set (value (A)) 7) (union (A) (B))
            (set (out) (value (B))) (check (= (out) 7))";
    for direct in [false, true] {
        run_ground_action_oracle(&mut EGraph::default(), source, direct).unwrap();
    }
}

#[test]
fn union_preserves_a_failing_merge_boundary() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(
            None,
            "(datatype T (A) (B) (C))
            (function value (T) i64 :no-merge)
            (set (value (A)) 0) (set (value (B)) 1)",
        )
        .unwrap();
    assert!(
        graph
            .parse_and_run_program(None, "(union (A) (B)) (C)")
            .is_err()
    );
    assert_eq!(graph.get_size("C"), 0);
}

#[test]
fn constructor_rows_remain_subsumed_after_union() {
    for direct in [false, true] {
        let mut graph = EGraph::default();
        run_ground_action_oracle(
            &mut graph,
            "(datatype T (A) (B) (F T))
                (F (A)) (subsume (F (A))) (union (A) (B)) (F (B))",
            direct,
        )
        .unwrap();
        let mut rows = Vec::new();
        graph
            .backend
            .for_each(graph.functions["F"].backend_id, |row| {
                rows.push(row.subsumed)
            });
        assert_eq!(rows, vec![true]);
    }
}

#[test]
fn completed_constructor_prefix_survives_macro_errors() {
    struct RejectCheck;
    impl CommandMacro for RejectCheck {
        fn transform(
            &self,
            command: Command,
            _: &mut SymbolGen,
            _: &TypeInfo,
        ) -> Result<Vec<Command>, Error> {
            if matches!(command, Command::Check(..)) {
                Err(Error::BackendError("expected macro error".into()))
            } else {
                Ok(vec![command])
            }
        }
    }
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(None, "(datatype T (A) (F T))")
        .unwrap();
    graph.command_macros.register(Arc::new(RejectCheck));
    assert!(
        graph
            .parse_and_run_program(None, "(F (A)) (check (= (A) (A)))")
            .is_err()
    );
    assert_eq!(graph.get_size("F"), 1);
}

#[test]
fn read_primitives_observe_completed_insertions() {
    #[derive(Clone)]
    struct ReadSize;
    impl Primitive for ReadSize {
        fn name(&self) -> &str {
            "read-f-size"
        }
        fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
            SimpleTypeConstraint::new(self.name(), vec![I64Sort.to_arcsort()], span.clone())
                .into_box()
        }
    }
    impl ReadPrim for ReadSize {
        fn apply<'a, 'db>(&self, state: ReadState<'a, 'db>, _: &[Value]) -> Option<Value> {
            Some(
                state
                    .base_values()
                    .get(state.table_size("F").unwrap() as i64),
            )
        }
    }
    let mut graph = EGraph::default();
    graph.add_read_primitive(ReadSize, None);
    graph
        .parse_and_run_program(
            None,
            "(datatype T (A) (B) (F T))
        (function result () i64 :no-merge)
        (F (A)) (F (B)) (set (result) (read-f-size))
        (check (= (result) 2))",
        )
        .unwrap();
}

#[test]
fn parser_and_command_macros_run_before_preparation() {
    struct RewriteA;
    impl CommandMacro for RewriteA {
        fn transform(
            &self,
            command: Command,
            _: &mut SymbolGen,
            _: &TypeInfo,
        ) -> Result<Vec<Command>, Error> {
            Ok(vec![match command {
                Command::Action(Action::Expr(span, Expr::Call(_, ref head, _))) if head == "A" => {
                    Command::Action(Action::Expr(
                        span.clone(),
                        Expr::Call(span, "B".into(), vec![]),
                    ))
                }
                command => command,
            }])
        }
    }
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(None, "(datatype T (A) (B) (F T))")
        .unwrap();
    graph.command_macros.register(Arc::new(RewriteA));
    graph
        .parser
        .add_expr_macro(Arc::new(SimpleMacro::new("Alias", |_, span, _| {
            Ok(Expr::Call(span, "B".into(), vec![]))
        })));
    graph
        .parse_and_run_program(None, "(A) (F (Alias))")
        .unwrap();
    assert_eq!(graph.get_size("A"), 0);
    assert_eq!(graph.get_size("B"), 1);
    assert_eq!(graph.get_size("F"), 1);
}

#[test]
fn declared_calls_with_primitive_alternatives_keep_ambiguity() {
    #[derive(Clone)]
    struct AlsoA(ArcSort);
    impl Primitive for AlsoA {
        fn name(&self) -> &str {
            "A"
        }
        fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
            SimpleTypeConstraint::new(self.name(), vec![self.0.clone()], span.clone()).into_box()
        }
    }
    impl PurePrim for AlsoA {
        fn apply(&self, _: PureState<'_, '_>, _: &[Value]) -> Option<Value> {
            unreachable!("ambiguous calls cannot execute")
        }
    }
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(None, "(datatype T (A))")
        .unwrap();
    let sort = graph.type_info.get_sort_by_name("T").unwrap().clone();
    graph.add_pure_primitive(AlsoA(sort), None);
    assert!(graph.parse_and_run_program(None, "(A)").is_err());
    assert_eq!(graph.get_size("A"), 0);
}

#[test]
fn ground_action_cache_keeps_call_validation_and_command_scope() {
    let mut initial = EGraph::default();
    initial
        .parse_and_run_program(None, "(datatype T (A) (F T)) (datatype U (B))")
        .unwrap();
    for source in ["(F (A)) (F (A) (A))", "(F (A)) (F (B))"] {
        let mut graph = initial.clone();
        assert!(graph.parse_and_run_program(None, source).is_err());
        assert_eq!(graph.get_size("F"), 1);
        assert_eq!(graph.get_size("B"), 0);
    }

    let mut graph = initial;
    assert!(
        graph
            .parse_and_run_program(
                None,
                "(push) (constructor Temporary () T) (Temporary) (pop) (Temporary)",
            )
            .is_err()
    );
    assert!(!graph.functions.contains_key("Temporary"));
    graph
        .parse_and_run_program(
            None,
            "
        (push)
        (constructor Reused () T)
        (Reused)
        (pop)
        (constructor Padding () T)
        (constructor Reused () T)
        (Reused)
        (check (= (Reused) (Reused)))
    ",
        )
        .unwrap();
    assert_eq!(graph.get_size("Padding"), 0);
    assert_eq!(graph.get_size("Reused"), 1);
}

#[test]
fn cached_calls_preserve_parser_macro_registration() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(None, "(datatype T (A) (B) (F T))")
        .unwrap();
    graph
        .parser
        .add_command_macro(Arc::new(SimpleMacro::new("replace-a", |_, _, parser| {
            parser.add_expr_macro(Arc::new(SimpleMacro::new("A", |_, span, _| {
                Ok(Expr::Call(span, "B".into(), vec![]))
            })));
            Ok(vec![])
        })));
    graph
        .parse_and_run_program(None, "(F (A)) (replace-a) (F (A))")
        .unwrap();
    assert_eq!(graph.get_size("A"), 1);
    assert_eq!(graph.get_size("B"), 1);
    assert_eq!(graph.get_size("F"), 2);
}

#[test]
fn argument_buffers_reset_between_wide_and_narrow_calls() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(
            None,
            "(datatype T (A) (B) (F T) (Wide T T T T T))
        (Wide (A) (A) (A) (A) (A)) (F (A))
        (Wide (B) (B) (B) (B) (B))",
        )
        .unwrap();
    assert_eq!(graph.get_size("Wide"), 2);
    assert_eq!(graph.get_size("F"), 1);
}

#[test]
fn repeated_nullary_calls_refresh_after_flushes_and_unions() {
    let source = format!(
        "(datatype T (A) (B) (F T))
(A)
{}
(union (A) (B))
{}
(check (= (F (A)) (F (B))))",
        "(F (B))\n".repeat(260),
        "(F (B))\n".repeat(260),
    );
    let mut graph = EGraph::default();
    let mut compiled = EGraph::default();
    run_ground_action_oracle(&mut graph, &source, true).unwrap();
    run_ground_action_oracle(&mut compiled, &source, false).unwrap();
    assert_eq!(graph.get_size("F"), 1);
    assert_action_graphs_equal(&graph, &compiled);
}

#[test]
fn nullary_caching_keeps_subsumed_constructor_rows() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(
            None,
            "(datatype T (A) (Pair T T))
        (A) (subsume (A)) (Pair (A) (A)) (Pair (A) (A))",
        )
        .unwrap();
    let mut rows = Vec::new();
    graph
        .backend
        .for_each(graph.functions["A"].backend_id, |row| {
            rows.push(row.subsumed)
        });
    assert_eq!(rows, vec![true]);
    assert_eq!(graph.get_size("Pair"), 1);
}
