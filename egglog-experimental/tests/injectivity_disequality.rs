//! Eager disequality propagation, read-only queries, and encoding parity.

use egglog::{EGraph, RawValues, Read, ast::Command, span};
use egglog_experimental::{
    new_experimental_egraph, new_experimental_egraph_for_proofs,
    new_experimental_egraph_with_proof_testing, new_experimental_egraph_with_term_encoding,
};

const MODES: [fn() -> EGraph; 3] = [
    new_experimental_egraph_for_proofs,
    new_experimental_egraph_with_term_encoding,
    new_experimental_egraph_with_proof_testing,
];

fn run_in_each_mode(program: &str) {
    for (mode, graph) in MODES.into_iter().enumerate() {
        graph()
            .parse_and_run_program(None, program)
            .unwrap_or_else(|error| panic!("mode {mode}: {error}\n{program}"));
    }
}

#[test]
fn native_fields_materialize_only_when_scheduled_and_queries_do_not_write() {
    let mut graph = new_experimental_egraph_for_proofs();
    graph
        .parse_and_run_program(
            None,
            "(datatype Input (A) (B))
             (datatype Output (Num i64 :injective) (Mixed Input i64 Input i64 :injective))
             (Num 1) (Num 2)
             (Mixed (A) 1 (B) 2) (Mixed (A) 9 (B) 2) (Mixed (A) 1 (B) 9)
             (fail (check (known-disequal? (Num 1) (Num 2))))
             (fail (check-contradiction))",
        )
        .unwrap();
    assert_eq!(graph.get_size("@disequality-ne-Input"), 0);
    assert_eq!(graph.get_size("@disequality-ne-Output"), 0);
    assert!(
        graph
            .type_info()
            .get_func_type("@disequality-ne-i64")
            .is_none()
    );
    assert!(
        graph
            .type_info()
            .get_func_type("@injectivity-constructors")
            .is_none()
    );
    let constructors = [graph.get_size("Num"), graph.get_size("Mixed")];
    graph
        .parse_and_run_program(None, "(run-schedule (saturate injectivity))")
        .unwrap();
    assert_eq!(graph.get_size("@disequality-ne-Output"), 8);
    assert_eq!(
        constructors,
        [graph.get_size("Num"), graph.get_size("Mixed")]
    );
    let rows = graph.num_tuples();
    let tables = graph.get_function_names();
    graph
        .parse_and_run_program(
            None,
            "(check (known-disequal? (Num 1) (Num 2)))
             (check (known-disequal? (Num 2) (Num 1)))
             (check (known-disequal? (Mixed (A) 1 (B) 2) (Mixed (A) 9 (B) 2)))
             (check (known-disequal? (Mixed (A) 1 (B) 2) (Mixed (A) 1 (B) 9)))
             (fail (check (known-disequal? (Num 1) (Num 1))))
             (fail (check (known-disequal? (A) (B))))",
        )
        .unwrap();
    assert_eq!(graph.num_tuples(), rows);
    assert_eq!(graph.get_function_names(), tables);
}

#[test]
fn eq_fields_propagate_at_each_position_and_respect_opt_in() {
    run_in_each_mode(
        "(datatype Term (A) (B) (C) (Pair Term Term :injective) (Other Term Term))
         (constructor Mixed (i64 Term i64 Term) Term :injective)
         (Pair (A) (C)) (Pair (B) (C)) (Pair (C) (A)) (Pair (C) (B))
         (Other (A) (C)) (Other (B) (C))
         (Mixed 1 (A) 2 (C)) (Mixed 1 (B) 2 (C))
         (Mixed 1 (C) 2 (A)) (Mixed 1 (C) 2 (B))
         (disequal (A) (B))
         (fail (check (known-disequal? (Pair (A) (C)) (Pair (B) (C)))))
         (run-schedule (saturate injectivity))
         (check (known-disequal? (Pair (A) (C)) (Pair (B) (C))))
         (check (known-disequal? (Pair (C) (A)) (Pair (C) (B))))
         (check (known-disequal? (Mixed 1 (A) 2 (C)) (Mixed 1 (B) 2 (C))))
         (check (known-disequal? (Mixed 1 (C) 2 (A)) (Mixed 1 (C) 2 (B))))
         (fail (check (known-disequal? (Other (A) (C)) (Other (B) (C)))))
         (fail (check (known-disequal? (Pair (A) (C)) (Pair (C) (A)))))
         (fail (check (known-disequal? (A) (C))))",
    );
}

#[test]
fn downward_propagation_requires_all_other_fields_equal() {
    run_in_each_mode(
        "(datatype Input (A) (B) (C) (D) (E) (G))
         (datatype Output (F Input :injective) (Pair Input Input :injective)
                          (Mixed Input i64 Input :injective))
         (disequal (F (B)) (F (A)))
         (disequal (Pair (C) (E)) (Pair (D) (G)))
         (disequal (Mixed (E) 1 (A)) (Mixed (G) 2 (A)))
         (run-schedule (saturate injectivity))
         (check (known-disequal? (A) (B)))
         (check (known-disequal? (B) (A)))
         (fail (check (known-disequal? (C) (D))))
         (fail (check (known-disequal? (E) (G))))
         (push)
         (union (E) (G))
         (run-schedule (saturate injectivity))
         (check (known-disequal? (C) (D)))
         (fail (check-contradiction))
         (pop)
         (fail (check (known-disequal? (C) (D))))
         (push)
         (disequal (Pair (A) (C)) (Pair (A) (D)))
         (run-schedule (saturate injectivity))
         (check (known-disequal? (C) (D)))
         (pop)
         (fail (check (known-disequal? (C) (D))))
         (disequal (Mixed (C) 7 (A)) (Mixed (D) 7 (A)))
         (run-schedule (saturate injectivity))
         (check (known-disequal? (C) (D)))",
    );
}

#[test]
fn unmarked_unary_declarations_propagate_only_when_scheduled() {
    for declaration in [
        "(sort Output) (constructor F (Input) Output)",
        "(datatype Output (F Input))",
        "(datatype* (Output (F Input)) (Recursive (Back Output Recursive)))",
    ] {
        run_in_each_mode(&format!(
            "(datatype Input (A) (B))
             {declaration}
             (disequal (F (A)) (F (B)))
             (fail (check (known-disequal? (A) (B))))
             (run-schedule (saturate injectivity))
             (check (known-disequal? (A) (B)))
             (check (known-disequal? (B) (A)))"
        ));
    }
}

#[test]
fn unmarked_nary_constructors_require_every_other_field_to_agree() {
    run_in_each_mode(
        "(datatype Input (A) (B) (C) (D) (E) (G))
         (datatype Output (Pair Input Input) (Mixed i64 Input i64 Input))
         (disequal (Pair (A) (C)) (Pair (B) (D)))
         (disequal (Mixed 1 (E) 2 (C)) (Mixed 1 (G) 9 (C)))
         (run-schedule (saturate injectivity))
         (fail (check (known-disequal? (A) (B))))
         (fail (check (known-disequal? (C) (D))))
         (fail (check (known-disequal? (E) (G))))
         (push)
         (union (C) (D))
         (run-schedule (saturate injectivity))
         (check (known-disequal? (A) (B)))
         (pop)
         (fail (check (known-disequal? (A) (B))))
         (disequal (Pair (C) (A)) (Pair (C) (B)))
         (disequal (Mixed 1 (C) 2 (E)) (Mixed 1 (C) 2 (G)))
         (run-schedule (saturate injectivity))
         (check (known-disequal? (A) (B)))
         (check (known-disequal? (E) (G)))",
    );
}

#[test]
fn unmarked_constructors_do_not_propagate_upward_or_decompose_equal_outputs() {
    run_in_each_mode(
        "(datatype Term (A) (B) (F Term) (Num i64))
         (F (A)) (F (B)) (Num 1) (Num 2)
         (disequal (A) (B))
         (run-schedule (saturate injectivity))
         (fail (check (known-disequal? (F (A)) (F (B)))))
         (fail (check (known-disequal? (Num 1) (Num 2))))
         (union (F (A)) (F (B)))
         (union (Num 1) (Num 2))
         (run-schedule (saturate injectivity))
         (fail (check (= (A) (B))))
         (fail (check-contradiction))",
    );
}

#[test]
fn unmarked_container_and_nonunionable_fields_are_equality_guards() {
    for declaration in [
        "(sort Items (Vec i64)) (datatype Output (WithItems Term Items Token))",
        "(datatype* (Output (WithItems Term Items Token)) (sort Items (Vec i64)))",
    ] {
        for mode in MODES {
            let mut graph = mode();
            graph
                .run_program(vec![Command::Sort {
                    span: span!(),
                    name: "Token".into(),
                    presort_and_args: None,
                    uf: None,
                    container_rebuild: None,
                    proof_constructors: None,
                    unionable: false,
                }])
                .unwrap();
            graph
                .parse_and_run_program(
                    None,
                    &format!(
                        "(datatype Term (A) (B) (C) (D))
         (constructor T0 () Token) (constructor T1 () Token)
         {declaration}
         (disequal (WithItems (A) (vec-of 1 2) (T0))
                   (WithItems (B) (vec-of 1 2) (T0)))
         (disequal (WithItems (C) (vec-of 1) (T0))
                   (WithItems (D) (vec-of 2) (T0)))
         (disequal (WithItems (C) (vec-of 1) (T0))
                   (WithItems (D) (vec-of 1) (T1)))
         (run-schedule (saturate injectivity))
         (check (known-disequal? (A) (B)))
         (fail (check (known-disequal? (C) (D))))"
                    ),
                )
                .unwrap();
        }
    }
}

#[test]
fn diagonal_disequality_is_a_known_limit_of_local_propagation() {
    run_in_each_mode(
        "(datatype Term (A) (B) (Pair Term Term))
         (disequal (Pair (A) (A)) (Pair (B) (B)))
         (run-schedule (saturate injectivity))
         (fail (check (known-disequal? (A) (B))))
         (push)
         (union (A) (B))
         (check-contradiction)
         (pop)
         (fail (check-contradiction))",
    );
}

#[test]
fn declarations_without_disequality_rules_do_not_install_support() {
    let mut graph = new_experimental_egraph_for_proofs();
    graph
        .run_program(vec![Command::Sort {
            span: span!(),
            name: "Token".into(),
            presort_and_args: None,
            uf: None,
            container_rebuild: None,
            proof_constructors: None,
            unionable: false,
        }])
        .unwrap();
    graph
        .parse_and_run_program(
            None,
            "(datatype Term (A) (Num i64) (Empty :injective))
             (sort Items (Vec Term))
             (constructor Container (Items) Term)
             (constructor Internal (Term) Term :internal-role global)
             (constructor Inert (Term) Token)
             (constructor Marked (Term) Token :injective)
             (relation Relation (Term))
             (run-schedule (saturate injectivity))",
        )
        .unwrap();
    for sort in ["Term", "Items", "Token", "i64", "@RelationSort"] {
        assert!(
            graph
                .type_info()
                .get_func_type(&format!("@disequality-ne-{sort}"))
                .is_none(),
            "unexpected Ne support for {sort}"
        );
    }
}

#[test]
fn primitive_inputs_do_not_supply_reverse_witnesses_for_overlapping_eq_ids() {
    let mut graph = new_experimental_egraph_for_proofs();
    graph
        .parse_and_run_program(
            None,
            "(datatype Input (A) (B))
             (datatype Output (Num i64 :injective)) (A) (B)",
        )
        .unwrap();
    let a = graph
        .read(|state| state.eclass_of("A", RawValues(vec![])))
        .unwrap()
        .unwrap();
    let b = graph
        .read(|state| state.eclass_of("B", RawValues(vec![])))
        .unwrap()
        .unwrap();
    // Deliberately collide primitive inputs with the equality IDs.
    let left = graph.value_to_base::<i64>(a);
    let right = graph.value_to_base::<i64>(b);
    assert_eq!(graph.base_to_value(left), a);
    assert_eq!(graph.base_to_value(right), b);
    graph
        .parse_and_run_program(
            None,
            &format!(
                "(disequal (Num {left}) (Num {right}))
                 (run-schedule (saturate injectivity))
                 (check (known-disequal? (Num {left}) (Num {right})))
                 (fail (check (known-disequal? (A) (B))))"
            ),
        )
        .unwrap();
}

#[test]
fn ordinary_seminaive_queries_track_new_relation_rows() {
    run_in_each_mode(
        "(datatype Term (A) (B) (Num i64 :injective))
         (A) (B) (Num 1) (Num 2)
         (relation Found (Term Term))
         (rule ((known-disequal? x y)) ((Found x y)))
         (ruleset later)
         (rule () ((disequal (A) (B))) :ruleset later)
         (run 1)
         (fail (check (Found (A) (B))))
         (run later 1)
         (run 1)
         (check (Found (A) (B)))
         (fail (check (Found (Num 1) (Num 2))))
         (run-schedule (saturate injectivity))
         (run 1)
         (check (Found (Num 1) (Num 2)))
         (check (Found (Num 2) (Num 1)))
         (fail (check (Found (Num 1) (Num 1))))",
    );
}

#[test]
fn query_only_relations_are_empty_and_assertions_remain_explicit() {
    run_in_each_mode(
        "(datatype Term (A) (B)) (A) (B)
         (fail (check (known-disequal? (A) (B))))
         (disequal (A) (B))
         (check (known-disequal? (A) (B)))
         (run-schedule (saturate injectivity))
         (check (known-disequal? (B) (A)))
         (disequal (A) (A))
         (check (known-disequal? (A) (A)))
         (check-contradiction)",
    );
}

#[test]
fn finite_cycles_and_deep_structures_reach_a_fixed_point() {
    run_in_each_mode(
        "(datatype Term (A) (B) (Wrap Term :injective) (Num i64 :injective))
         (union (A) (Wrap (A))) (union (B) (Wrap (B)))
         (run-schedule (saturate injectivity))
         (fail (check (known-disequal? (A) (B))))
         (union (A) (Num 1)) (union (B) (Num 2))
         (run-schedule (saturate injectivity))
         (check (known-disequal? (A) (B)))",
    );
    let depth = 32;
    let left = format!("{}(A){}", "(Wrap ".repeat(depth), ")".repeat(depth));
    let right = format!("{}(B){}", "(Wrap ".repeat(depth), ")".repeat(depth));
    for assertion in [
        "(disequal (A) (B))".into(),
        format!("(disequal {left} {right})"),
    ] {
        let mut graph = new_experimental_egraph_for_proofs();
        graph
            .parse_and_run_program(
                None,
                &format!(
                    "(datatype Term (A) (B) (Wrap Term :injective))
                     (let left {left}) (let right {right}) {assertion}
                     (run-schedule (saturate injectivity))
                     (check (known-disequal? left right))
                     (check (known-disequal? (A) (B)))"
                ),
            )
            .unwrap();
        assert_eq!(graph.get_size("Wrap"), 2 * depth);
    }
}

#[test]
fn scoped_rules_and_relations_follow_pop_and_failed_declarations() {
    for mode in MODES {
        let mut graph = mode();
        graph
            .parse_and_run_program(
                None,
                "(datatype Term (A) (B))
                 (push)
                 (constructor F (Term) Term :injective)
                 (disequal (F (A)) (F (B)))
                 (run-schedule (saturate injectivity))
                 (check (known-disequal? (A) (B)))
                 (pop)
                 (constructor F (Term) Term)
                 (F (A)) (F (B))
                 (fail (check (known-disequal? (A) (B))))
                 (disequal (A) (B))",
            )
            .unwrap();
        assert!(
            graph
                .parse_and_run_program(None, "(constructor F (Term) Term :injective)")
                .is_err()
        );
        graph
            .parse_and_run_program(
                None,
                "(run-schedule (saturate injectivity))
                 (fail (check (known-disequal? (F (A)) (F (B)))))
                 (push)
                 (datatype Scoped (X) (Y) (G Scoped))
                 (disequal (G (X)) (G (Y)))
                 (run-schedule (saturate injectivity))
                 (check (known-disequal? (X) (Y)))
                 (pop)
                 (datatype Scoped (X) (Y) (G Scoped))
                 (G (X)) (G (Y))
                 (run-schedule (saturate injectivity))
                 (fail (check (known-disequal? (X) (Y))))",
            )
            .unwrap();
    }
}

#[test]
fn subsumed_rows_and_current_canonical_ids_participate() {
    for assertion in ["(disequal a b)", "(disequal fa fb)"] {
        run_in_each_mode(&format!(
            "(datatype Term (A) (B) (C) (D) (F Term :injective))
             (let a (A)) (let b (B)) (let fa (F a)) (let fb (F b))
             (subsume (F a)) {assertion}
             (union a (C)) (union b (D))
             (run-schedule (saturate injectivity))
             (check (known-disequal? fa fb))
             (check (known-disequal? (C) (D)))"
        ));
    }
    run_in_each_mode(
        "(datatype Term (A) (B) (C) (D) (F Term))
         (let fa (F (A))) (let fb (F (B)))
         (subsume (F (A)))
         (disequal fa fb)
         (union (A) (C)) (union (B) (D))
         (run-schedule (saturate injectivity))
         (check (known-disequal? (C) (D)))",
    );
}

#[test]
fn mutual_datatypes_install_all_eq_field_relations() {
    run_in_each_mode(
        "(datatype* (Input (A) (B) (Back Output :injective))
                     (Output (F Input :injective)))
         (F (A)) (F (B)) (Back (F (A))) (Back (F (B)))
         (disequal (A) (B))
         (run-schedule (saturate injectivity))
         (check (known-disequal? (F (A)) (F (B))))
         (check (known-disequal? (Back (F (A))) (Back (F (B)))))",
    );
}

#[test]
fn nested_unit_queries_and_query_contexts_work() {
    run_in_each_mode(
        "(datatype Term (A) (B) (C) (Wrap Term))
         (disequal (A) (B))
         (check (= () (known-disequal? (A) (B))))
         (fail (check (= () (known-disequal? (A) (C)))))
         (relation Found (Term Term))
         (rule ((= () (known-disequal? x y))) ((Found x y)))
         (run 1)
         (run 1 :until (known-disequal? (A) (B)))
         (check (Found (A) (B)))
         (rewrite (Wrap x) x :when ((known-disequal? x (B))))
         (Wrap (A)) (run 1)
         (check (= (Wrap (A)) (A)))",
    );
}

#[test]
fn extended_schedule_until_queries_are_read_only() {
    let mut graph = new_experimental_egraph();
    graph
        .parse_and_run_program(
            None,
            "(datatype Term (A) (B)) (A) (B)
         (relation Tick ()) (ruleset ticking)
         (rule () ((Tick)) :ruleset ticking)
         (disequal (A) (B))
         (run-schedule (seq (repeat 1 (run ticking :until (known-disequal? (A) (B))))))
         (fail (check (Tick)))
         (run-schedule (run ticking :until (= () (known-disequal? (A) (A)))))
         (check (Tick))
         (fail (check (known-disequal? (A) (A))))",
        )
        .unwrap();
    let error = graph
        .parse_and_run_program(None, "(run-schedule (eval (known-disequal? (A) (A))))")
        .unwrap_err()
        .to_string();
    assert!(error.contains("only supported in query facts"), "{error}");
}

#[test]
fn query_operand_sorts_can_be_inferred_from_the_rule_head() {
    run_in_each_mode(
        "(datatype Term (A) (B)) (datatype Other (C))
         (relation Found (Term Term))
         (rule ((known-disequal? x y)) ((Found x y)))
         (disequal (A) (B)) (run 1)
         (check (Found (A) (B)))",
    );
}

#[test]
fn queries_and_fresh_assertion_actions_share_inference() {
    run_in_each_mode(
        "(datatype Term (A) (B))
         (disequal (A) (B))
         (relation Fresh (Term Term))
         (rule ((known-disequal? x y))
               ((let z (unstable-fresh! Term)) (disequal z x) (Fresh z x)))
         (run 1)
         (check (Fresh z (A)) (known-disequal? z (A)))",
    );
}

#[test]
fn predicate_requires_two_values_of_the_same_unionable_eq_sort() {
    for mode in MODES {
        for source in [
            "(check (known-disequal? 1 2))",
            "(relation P (i64)) (check (known-disequal? (P 1) (P 2)))",
            "(datatype A (X)) (datatype B (Y)) (check (known-disequal? (X) (Y)))",
            "(datatype A (X)) (check (known-disequal? (X)))",
            "(sort Items (Vec i64)) (check (known-disequal? (vec-of 1) (vec-of 2)))",
        ] {
            assert!(
                mode().parse_and_run_program(None, source).is_err(),
                "{source}"
            );
        }
    }
}

#[test]
fn action_expression_queries_are_rejected_without_inserting_pairs() {
    for mode in MODES {
        for source in [
            "(known-disequal? (A) (B))",
            "(let query (known-disequal? (A) (B)))",
            "(begin (known-disequal? (A) (B)))",
            "(rule () ((known-disequal? (A) (B))))",
            "(function f (Term) Unit :merge (known-disequal? (A) (B)))",
            "(extract (known-disequal? (A) (B)))",
            "(output \"/tmp/known-disequal-output\" (known-disequal? (A) (B)))",
        ] {
            let mut graph = mode();
            graph
                .parse_and_run_program(None, "(datatype Term (A) (B)) (A) (B)")
                .unwrap();
            let error = graph
                .parse_and_run_program(None, source)
                .unwrap_err()
                .to_string();
            assert!(
                error.contains("only supported in query facts"),
                "{source}: {error}"
            );
            graph
                .parse_and_run_program(None, "(fail (check (known-disequal? (A) (B))))")
                .unwrap();
        }
    }
}

#[test]
fn bypassing_query_lowering_fails_without_panicking() {
    let mut graph = new_experimental_egraph_for_proofs();
    graph
        .parse_and_run_program(
            None,
            "(datatype Term (A) (B)) (disequal (A) (B))
         (sort Query (UnstableFn (Term Term) Unit))
         (function query () Query :no-merge)",
        )
        .unwrap();
    let error = graph
        .parse_and_run_program(None, "(set (query) (unstable-fn \"known-disequal?\"))")
        .unwrap_err()
        .to_string();
    assert!(error.contains("only supported in query facts"), "{error}");
    let mut commands = graph
        .parse_program(None, "(known-disequal? (A) (B))")
        .unwrap();
    let egglog::ast::Command::Action(egglog::ast::Action::Expr(_, expr)) = commands.pop().unwrap()
    else {
        panic!("expected query expression action");
    };
    assert!(graph.eval_expr(&expr).is_err());
}

#[test]
fn keep_best_recomputes_derived_pairs_from_retained_constructors() {
    new_experimental_egraph_for_proofs()
        .parse_and_run_program(
            None,
            "(datatype Term (Num i64 :injective))
         (Num 1) (Num 2)
         (run-schedule (saturate injectivity))
         (keep-best \"Num\")
         (fail (check (known-disequal? (Num 1) (Num 2))))
         (run-schedule (saturate injectivity))
         (check (known-disequal? (Num 1) (Num 2)))",
        )
        .unwrap();
}
