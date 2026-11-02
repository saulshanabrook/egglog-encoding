use super::*;

#[test]
fn source_and_materialized_commands_share_execution() {
    let source = "(datatype T (A) (B) (F T))
        (F (A)) (F (B)) (union (A) (B))
        (let $head (F (A))) (check (= $head (F (B))))
        (print-size F)";
    let mut streamed = EGraph::default();
    let actual = streamed.parse_and_run_program(None, source).unwrap();
    let mut materialized = EGraph::default();
    let program = materialized.parse_program(None, source).unwrap();
    let expected = materialized.run_program(program).unwrap();
    assert_eq!(
        actual.iter().map(ToString::to_string).collect::<Vec<_>>(),
        expected.iter().map(ToString::to_string).collect::<Vec<_>>()
    );
    assert_eq!(streamed.get_size("F"), materialized.get_size("F"));
}

#[test]
fn source_execution_commits_the_prefix_before_a_parse_error() {
    for mut graph in [EGraph::default(), EGraph::new_with_term_encoding()] {
        assert!(
            graph
                .parse_and_run_program(None, "(datatype T (A) (F T)) (F (A)) (")
                .is_err()
        );
        assert_eq!(graph.get_size("F"), 1);
    }
}

#[test]
fn materialized_and_proof_inputs_parse_before_execution() {
    let source = "(datatype T (A)) (A) (";
    let mut materialized = EGraph::default();
    assert!(materialized.parse_program(None, source).is_err());
    assert!(materialized.get_function("A").is_none());
    let mut proof = EGraph::new_with_proofs();
    assert!(proof.parse_and_run_program(None, source).is_err());
    assert!(proof.get_function("A").is_none());
}

#[test]
fn empty_parser_expansions_can_install_later_macros() {
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(None, "(datatype T (B) (F T))")
        .unwrap();
    graph.parser.add_command_macro(Arc::new(SimpleMacro::new(
        "install-alias",
        |_, _, parser| {
            parser.add_expr_macro(Arc::new(SimpleMacro::new("Alias", |_, span, _| {
                Ok(Expr::Call(span, "B".into(), vec![]))
            })));
            Ok(vec![])
        },
    )));
    graph
        .parse_and_run_program(None, "(install-alias) (F (Alias))")
        .unwrap();
    assert_eq!(graph.get_size("B"), 1);
    assert_eq!(graph.get_size("F"), 1);
}

#[test]
fn executed_commands_can_install_later_parser_macros() {
    struct InstallAlias;
    impl UserDefinedCommand for InstallAlias {
        fn update(&self, graph: &mut EGraph, _: &[Expr]) -> Result<Vec<CommandOutput>, Error> {
            graph
                .parser
                .add_expr_macro(Arc::new(SimpleMacro::new("Alias", |_, span, _| {
                    Ok(Expr::Call(span, "B".into(), vec![]))
                })));
            Ok(vec![])
        }
    }
    let mut graph = EGraph::default();
    graph
        .add_command("install-alias".into(), Arc::new(InstallAlias))
        .unwrap();
    graph
        .parse_and_run_program(
            None,
            "(datatype T (B) (F T))
        (install-alias) (F (Alias))",
        )
        .unwrap();
    assert_eq!(graph.get_size("B"), 1);
    assert_eq!(graph.get_size("F"), 1);
}

#[test]
fn includes_share_prefix_and_proof_parsing_boundaries() {
    let path = std::env::temp_dir().join(format!(
        "egglog-streamed-include-{}.egg",
        std::process::id(),
    ));
    std::fs::write(&path, "(F (A)) (").unwrap();
    let source = format!(
        "(datatype T (A) (B) (F T)) (include \"{}\") (B)",
        path.display()
    );
    let mut ordinary = EGraph::default();
    let ordinary_result = ordinary.parse_and_run_program(None, &source);
    let mut materialized = EGraph::default();
    let program = materialized.parse_program(None, &source).unwrap();
    let materialized_result = materialized.run_program(program);
    let mut proof = EGraph::new_with_proofs();
    let proof_result = proof.parse_and_run_program(None, &source);
    std::fs::remove_file(path).unwrap();
    assert!(ordinary_result.is_err());
    assert!(materialized_result.is_err());
    assert!(proof_result.is_err());
    assert_eq!(ordinary.get_size("F"), 1);
    assert_eq!(materialized.get_size("F"), 0);
    assert_eq!(proof.get_size("F"), 0);
    assert_eq!(ordinary.get_size("B"), 0);
    assert_eq!(materialized.get_size("B"), 0);
    assert_eq!(proof.get_size("B"), 0);
}

#[test]
fn source_admission_preserves_parser_overrides() {
    let mut initial = EGraph::default();
    initial
        .parse_and_run_program(None, "(datatype T (A) (B) (F T))")
        .unwrap();
    for kind in ["expression", "action", "command"] {
        let mut graph = initial.clone();
        match kind {
            "expression" => graph
                .parser
                .add_expr_macro(Arc::new(SimpleMacro::new("A", |_, span, _| {
                    Ok(Expr::Call(span, "B".into(), vec![]))
                }))),
            "action" => {
                graph
                    .parser
                    .add_action_macro(Arc::new(SimpleMacro::new("A", |_, span, _| {
                        Ok(vec![Action::Expr(
                            span.clone(),
                            Expr::Call(span, "B".into(), vec![]),
                        )])
                    })))
            }
            _ => graph
                .parser
                .add_command_macro(Arc::new(SimpleMacro::new("A", |_, span, _| {
                    Ok(vec![Command::Action(Action::Expr(
                        span.clone(),
                        Expr::Call(span, "B".into(), vec![]),
                    ))])
                }))),
        }
        let mut ast = graph.clone();
        let source = "(A) (F (A))";
        let commands = ast.parse_program(None, source).unwrap();
        graph.parse_and_run_program(None, source).unwrap();
        ast.run_program(commands).unwrap();
        for name in ["A", "B", "F"] {
            assert_eq!(graph.get_size(name), ast.get_size(name), "{kind}: {name}");
        }
        assert_eq!(graph.get_size("B"), 1);
        assert_eq!(graph.get_size("A"), usize::from(kind != "expression"));
    }
}

#[test]
fn default_deny_macro_capability_preserves_effects_and_error_prefix() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    struct RejectA(Arc<AtomicUsize>);
    impl CommandMacro for RejectA {
        fn transform(
            &self,
            command: Command,
            _: &mut SymbolGen,
            _: &TypeInfo,
        ) -> Result<Vec<Command>, Error> {
            self.0.fetch_add(1, Ordering::SeqCst);
            if matches!(&command, Command::Action(Action::Expr(_, Expr::Call(_, head, args)))
                if head == "Num" && matches!(args.as_slice(), [Expr::Lit(..)]))
            {
                return Ok(vec![Command::Action(Action::Expr(
                    span!(),
                    Expr::Call(span!(), "C".into(), vec![]),
                ))]);
            }
            if matches!(&command, Command::Action(Action::Expr(_, Expr::Call(_, head, _))) if head == "A")
            {
                Err(Error::BackendError("A rejected by macro".into()))
            } else {
                Ok(vec![command])
            }
        }
    }
    let mut graph = EGraph::default();
    graph
        .parse_and_run_program(None, "(datatype T (A) (B) (C) (F T) (Num i64))")
        .unwrap();
    let calls = Arc::new(AtomicUsize::new(0));
    graph
        .command_macros
        .register(Arc::new(RejectA(calls.clone())));
    assert!(
        graph
            .parse_and_run_program(None, "(F (B)) (Num 1) (A)")
            .is_err()
    );
    assert_eq!(calls.load(Ordering::SeqCst), 3);
    assert_eq!(graph.get_size("F"), 1);
    assert_eq!(graph.get_size("C"), 1);
    assert_eq!(graph.get_size("Num"), 0);
    assert_eq!(graph.get_size("A"), 0);
}

#[test]
fn declined_candidates_keep_conditional_command_macro_dispatch() {
    struct ReplacePrimitiveAction;
    impl CommandMacro for ReplacePrimitiveAction {
        fn preserves_closed_constructor_action(&self, _: Option<&str>) -> bool {
            true
        }
        fn transform(
            &self,
            command: Command,
            _: &mut SymbolGen,
            _: &TypeInfo,
        ) -> Result<Vec<Command>, Error> {
            if matches!(&command, Command::Action(Action::Expr(_, Expr::Call(_, head, args)))
                if head == "Num" && matches!(args.as_slice(), [Expr::Call(_, head, _)] if head == "+"))
            {
                // Primitive children are outside the closed-constructor promise.
                Ok(vec![Command::Action(Action::Expr(
                    span!(),
                    Expr::Call(span!(), "B".into(), vec![]),
                ))])
            } else {
                Ok(vec![command])
            }
        }
    }
    for materialized in [false, true] {
        let mut graph = EGraph::default();
        graph
            .parse_and_run_program(None, "(datatype T (A) (B) (Num i64))")
            .unwrap();
        graph
            .command_macros
            .register(Arc::new(ReplacePrimitiveAction));
        let source = "(A) (Num (+ 1 2))";
        if materialized {
            let commands = graph.parse_program(None, source).unwrap();
            graph.run_program(commands).unwrap();
        } else {
            graph.parse_and_run_program(None, source).unwrap();
        }
        assert_eq!(graph.get_size("A"), 1);
        assert_eq!(graph.get_size("B"), 1);
        assert_eq!(graph.get_size("Num"), 0);
    }
}

#[test]
fn expanded_action_fallback_keeps_remaining_output_without_reapplying_macros() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    struct Emit {
        commands: Vec<Command>,
        calls: Arc<AtomicUsize>,
    }
    impl CommandMacro for Emit {
        fn transform(
            &self,
            _: Command,
            _: &mut SymbolGen,
            _: &TypeInfo,
        ) -> Result<Vec<Command>, Error> {
            assert_eq!(self.calls.fetch_add(1, Ordering::SeqCst), 0);
            Ok(self.commands.clone())
        }
    }
    for materialized in [false, true] {
        let mut graph = EGraph::default();
        graph
            .parse_and_run_program(None, "(datatype T (A) (F T) (Num i64))")
            .unwrap();
        let commands = graph.parse_program(None, "(Num 1) (F (A))").unwrap();
        let calls = Arc::new(AtomicUsize::new(0));
        graph.command_macros.register(Arc::new(Emit {
            commands,
            calls: calls.clone(),
        }));
        if materialized {
            let commands = graph.parse_program(None, "(emit)").unwrap();
            graph.run_program(commands).unwrap();
        } else {
            graph.parse_and_run_program(None, "(emit)").unwrap();
        }
        assert_eq!(calls.load(Ordering::SeqCst), 1);
        assert_eq!(graph.get_size("Num"), 1);
        assert_eq!(graph.get_size("F"), 1);
    }
}

#[test]
fn raw_source_never_bypasses_builtin_dispatch_for_reserved_constructors() {
    let mut graph = EGraph::default();
    graph.ensure_no_reserved_symbols(false);
    graph.parse_and_run_program(None, "(sort T)").unwrap();
    for head in ["index", "set", "input", "output"] {
        graph
            .parse_and_run_program(None, &format!("(constructor {head} () T)"))
            .unwrap();
        assert!(
            graph
                .parse_and_run_program(None, &format!("({head})"))
                .is_err()
        );
        assert_eq!(graph.get_size(head), 0);
    }
}
