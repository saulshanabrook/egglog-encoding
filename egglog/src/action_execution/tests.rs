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
                Command::Action(action) => graph.prepare_ground_action(action).is_some(),
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
