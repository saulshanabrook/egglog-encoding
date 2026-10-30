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
    let mut proof = EGraph::new_with_proofs();
    let proof_result = proof.parse_and_run_program(None, &source);
    std::fs::remove_file(path).unwrap();
    assert!(ordinary_result.is_err());
    assert!(proof_result.is_err());
    assert_eq!(ordinary.get_size("F"), 1);
    assert_eq!(proof.get_size("F"), 0);
    assert_eq!(ordinary.get_size("B"), 0);
    assert_eq!(proof.get_size("B"), 0);
}
