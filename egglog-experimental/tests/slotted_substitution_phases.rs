//! Substitution preserves round-start reads in both matchers; nested runs converge.
use egglog_experimental::slotted::{Compiler, Options, new_egraph};

const LANGUAGE: &str = "(datatype E (V Var) (N i64) (F E) (G E) (Let E Var E :binder 1))";
const BETA: &str = "(rewrite (Let t $x body) (subst body $x t) :name \"beta\")";

fn run(compiler: &mut Compiler, graph: &mut egglog::EGraph, source: &str) {
    compiler
        .compile_program(None, source)
        .unwrap()
        .run(graph)
        .unwrap();
}

fn let_rows(graph: &egglog::EGraph) -> Vec<(Vec<egglog::Value>, egglog::Value)> {
    let mut rows = Vec::new();
    graph
        .constructor_enodes("Let", |node| {
            rows.push((node.children.to_vec(), node.eclass));
        })
        .unwrap();
    rows.sort();
    rows
}

#[test]
fn nested_substitution_stops_after_saturation() {
    for no_aliasing in [false, true] {
        let mut compiler = Compiler::new(Options {
            no_aliasing,
            ..Default::default()
        });
        let mut graph = new_egraph();
        run(
            &mut compiler,
            &mut graph,
            &format!(
                "{LANGUAGE} {BETA}
                 (let input (Let (N 7) $a (V $a)))
                 (run 30)
                 (check (= input (N 7)))"
            ),
        );
        let rounds = graph
            .get_overall_run_report()
            .iterations
            .iter()
            .filter(|iteration| iteration.name.is_empty())
            .count();
        if no_aliasing {
            assert!(
                rounds < 30,
                "unchanged nested substitution kept {rounds} rounds alive"
            );
        }
    }
}

#[test]
fn substitution_can_match_only_global_terms() {
    for no_aliasing in [false, true] {
        let mut compiler = Compiler::new(Options {
            no_aliasing,
            ..Default::default()
        });
        let mut graph = new_egraph();
        run(
            &mut compiler,
            &mut graph,
            &format!(
                "{LANGUAGE}
                 (let slot $a)
                 (let body (F (V slot)))
                 (let replacement (N 7))
                 (let input (Let replacement slot body))
                 (rewrite input (subst body slot replacement))
                 (run 30)
                 (check (= input (F (N 7))))"
            ),
        );
        let rounds = graph
            .get_overall_run_report()
            .iterations
            .iter()
            .filter(|iteration| iteration.name.is_empty())
            .count();
        if no_aliasing {
            assert!(
                rounds < 30,
                "nested global-only substitution did not converge"
            );
        }
    }
}

#[test]
fn global_rules_preserve_the_round_snapshot_in_either_order() {
    for no_aliasing in [false, true] {
        for beta_first in [false, true] {
            let global = "(rewrite body (V slot) :name \"shrink\")";
            let rules = if beta_first {
                format!("{BETA}\n{global}")
            } else {
                format!("{global}\n{BETA}")
            };
            run(
                &mut Compiler::new(Options {
                    no_aliasing,
                    ..Default::default()
                }),
                &mut new_egraph(),
                &format!(
                    "{LANGUAGE}
                     (let slot $a)
                     (let leaf (V slot))
                     (let body (F leaf))
                     (let input (Let (N 7) slot body))
                     {rules}
                     (run 1)
                     (check (= input (F (N 7))))
                     (fail (check (= input (N 7))))
                     (run 1)
                     (check (= input (N 7)))"
                ),
            );
        }
    }
}

#[test]
fn extraction_changes_are_revisited_without_new_let_rows_and_follow_scopes() {
    for no_aliasing in [false, true] {
        let mut compiler = Compiler::new(Options {
            no_aliasing,
            ..Default::default()
        });
        let mut graph = new_egraph();
        run(
            &mut compiler,
            &mut graph,
            &format!(
                "{LANGUAGE}
                 (let slot $a)
                 (let leaf (V slot))
                 (let body (F (F leaf)))
                 (let input (Let (N 7) slot body))
                 {BETA}
                 (run 1)
                 (check (= input (F (F (N 7)))))"
            ),
        );
        let before = let_rows(&graph);
        assert_eq!(before.len(), 1);
        run(
            &mut compiler,
            &mut graph,
            "(push)
             (rewrite body (G leaf))
             (run 1)
             (fail (check (= input (G (N 7)))))",
        );
        assert_eq!(
            let_rows(&graph),
            before,
            "only the body representative changed"
        );
        run(
            &mut compiler,
            &mut graph,
            "(run 1)
             (check (= input (G (N 7))))
             (pop)
             (run 30)
             (fail (check (= input (G (N 7)))))",
        );
        assert_eq!(let_rows(&graph), before);
        // A later input can install another global-only rule after beta and
        // after restoring both the compiler's rule registry and the graph.
        run(
            &mut compiler,
            &mut graph,
            "(rewrite body (G leaf))
             (run 2)
             (check (= input (G (N 7))))",
        );
    }
}
