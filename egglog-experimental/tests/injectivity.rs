//! Injectivity checks needing error inspection, scope changes, and encoding parity.

use egglog::{EGraph, ast::Parser};
use egglog_experimental::{
    new_experimental_egraph, new_experimental_egraph_with_proof_testing,
    new_experimental_egraph_with_term_encoding,
};

const MODES: [fn() -> EGraph; 3] = [
    new_experimental_egraph,
    new_experimental_egraph_with_term_encoding,
    new_experimental_egraph_with_proof_testing,
];

#[test]
fn primitive_mismatch_in_any_position_panics() {
    for mode in MODES {
        for (left, right, argument) in [("1 2", "9 2", 0), ("1 2", "1 9", 1)] {
            let error = mode()
                .parse_and_run_program(
                    None,
                    &format!(
                        "(datatype Term (Leaf))
                         (constructor Num (i64 i64) Term :injective)
                         (union (Num {left}) (Num {right}))
                         (run-schedule (saturate injectivity))"
                    ),
                )
                .unwrap_err()
                .to_string();
            assert!(
                error.contains("injectivity violation in constructor `Num`"),
                "{error}"
            );
            assert!(
                error.contains(&format!("primitive argument {argument}")),
                "{error}"
            );
        }
    }
}

#[test]
fn mixed_argument_mismatch_panics_after_recursive_propagation() {
    for mode in MODES {
        let error = mode()
            .parse_and_run_program(
                None,
                r#"
                (datatype Term (Leaf String) (Wrap Term :injective))
                (constructor Tagged (Term i64 String) Term :injective)
                (union (Wrap (Tagged (Leaf "a") 7 "left"))
                       (Wrap (Tagged (Leaf "b") 7 "right")))
                (run-schedule (saturate injectivity))
                "#,
            )
            .unwrap_err()
            .to_string();
        assert!(
            error.contains("injectivity violation in constructor `Tagged`"),
            "{error}"
        );
        assert!(error.contains("primitive argument 2"), "{error}");
    }
}

#[test]
fn subsumed_rows_still_constrain_their_arguments() {
    for mode in MODES {
        mode()
            .parse_and_run_program(
                None,
                r#"
                (datatype Term (Leaf String) (Wrap Term :injective))
                (let a (Leaf "a"))
                (let b (Leaf "b"))
                (let x (Wrap a))
                (let y (Wrap b))
                (subsume (Wrap a))
                (union x y)
                (run-schedule (saturate injectivity))
                (check (= a b))
                "#,
            )
            .unwrap();
    }
}

#[test]
fn push_pop_redeclaration_has_fresh_rules_and_no_stale_metadata() {
    for mode in MODES {
        mode()
            .parse_and_run_program(
                None,
                r#"
                (datatype Term (Leaf String))
                (push)
                (constructor Wrap (Term) Term :injective)
                (union (Wrap (Leaf "old-a")) (Wrap (Leaf "old-b")))
                (run-schedule (saturate injectivity))
                (check (= (Leaf "old-a") (Leaf "old-b")))
                (pop)
                (constructor Wrap (Term) Term :injective)
                (union (Wrap (Leaf "new-a")) (Wrap (Leaf "new-b")))
                (run-schedule (saturate injectivity))
                (check (= (Leaf "new-a") (Leaf "new-b")))
                (push)
                (datatype Scoped (One) (Next Scoped :injective))
                (run-schedule (saturate injectivity))
                (pop)
                (datatype Scoped (One) (Next Scoped :injective))
                (union (Next (One)) (Next (Next (One))))
                (run-schedule (saturate injectivity))
                (check (= (One) (Next (One))))
                "#,
            )
            .unwrap();
    }
}

#[test]
fn container_arguments_are_rejected_before_installation() {
    for mode in MODES {
        for declaration in [
            "(constructor Bad (Terms) Term :injective)",
            "(datatype BadSort (Bad Terms :injective))",
            "(datatype* (BadSort (Bad Terms :injective)))",
            "(datatype* (BadSort (Bad LocalTerms :injective)) (sort LocalTerms (Vec i64)))",
        ] {
            let mut egraph = mode();
            egraph
                .parse_and_run_program(None, "(datatype Term (Leaf)) (sort Terms (Vec Term))")
                .unwrap();
            let error = egraph
                .parse_and_run_program(None, declaration)
                .unwrap_err()
                .to_string();
            assert!(
                error.contains("does not support container argument 0"),
                "{error}"
            );
            assert!(egraph.type_info().get_func_type("Bad").is_none());
            assert!(egraph.type_info().get_sort_by_name("BadSort").is_none());
        }
    }
}

#[test]
fn bare_egglog_rejects_injectivity_instead_of_ignoring_it() {
    for declaration in [
        "(constructor Bad (Term) Term :injective)",
        "(datatype BadSort (Bad BadSort :injective))",
        "(datatype* (BadSort (Bad BadSort :injective)))",
    ] {
        let mut egraph = EGraph::default();
        egraph.parse_and_run_program(None, "(sort Term)").unwrap();
        let error = egraph
            .parse_and_run_program(None, declaration)
            .unwrap_err()
            .to_string();
        assert!(
            error.contains(":injective requires egglog-experimental"),
            "{error}"
        );
        assert!(egraph.type_info().get_func_type("Bad").is_none());
        assert!(egraph.type_info().get_sort_by_name("BadSort").is_none());
    }
}

#[test]
fn declaration_roundtrip_preserves_all_options() {
    let program = r#"
    (constructor Node (Term i64) Term :cost 7 :unextractable :injective :internal-hidden :internal-role global)
    (datatype Term (Leaf i64 :injective :unextractable :cost 9))
    (datatype* (Other (Child Other :cost 3 :injective :unextractable)))
    "#;
    let commands = Parser::default()
        .get_program_from_string(None, program)
        .unwrap();
    for (command, cost) in commands.into_iter().zip([7, 9, 3]) {
        let printed = command.to_string();
        let reparsed = Parser::default()
            .get_program_from_string(None, &printed)
            .unwrap();
        assert_eq!(reparsed.len(), 1);
        // Spans reflect the reparsed text, so compare its stable surface form.
        assert_eq!(reparsed[0].to_string(), printed);
        assert!(printed.contains(":injective"));
        assert!(printed.contains(":unextractable"));
        assert!(printed.contains(&format!(":cost {cost}")));
        if cost == 7 {
            assert!(printed.contains(":internal-hidden"));
            assert!(printed.contains(":internal-role global"));
        }
    }
}

#[test]
fn dynamic_cost_wrapper_and_constructor_options_survive_lowering() {
    let mut egraph = new_experimental_egraph();
    egraph
        .parse_and_run_program(
            None,
            r#"
            (datatype Term (Leaf String))
            (with-dynamic-cost
              (constructor Wrap (Term) Term :cost 7 :injective))
            (union (Wrap (Leaf "a")) (Wrap (Leaf "b")))
            (run-schedule (saturate injectivity))
            (check (= (Leaf "a") (Leaf "b")))
            (set-cost (Wrap (Leaf "a")) 1)
            (extract (Wrap (Leaf "a")))
            "#,
        )
        .unwrap();
}

#[test]
fn nullary_and_distinct_constructors_need_no_disjointness_axiom() {
    for mode in MODES {
        mode()
            .parse_and_run_program(
                None,
                "(run-schedule (saturate injectivity))
                 (datatype Term (A :injective) (B :injective))
                 (union (A) (B))
                 (run-schedule (saturate injectivity))
                 (check (= (A) (B)))",
            )
            .unwrap();
    }
}
