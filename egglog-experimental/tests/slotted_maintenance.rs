//! Leader migration, cache freshness, and deterministic substitution regressions.
use egglog::ast::{Sexp, parse_sexps};
use egglog_experimental::slotted::{Compiler, export::export, new_egraph};
use egraph_isomorphism::{AnnotatedEGraph, Graph, Limits, Outcome, find_isomorphism, verify};
use std::{fs, path::PathBuf, process::Command};

struct Scratch(PathBuf);
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

const PERMUTATIONS: [[usize; 3]; 6] = [
    [0, 1, 2],
    [0, 2, 1],
    [1, 0, 2],
    [1, 2, 0],
    [2, 0, 1],
    [2, 1, 0],
];

fn machinery() -> (String, String) {
    let mut compiler = Compiler::default();
    let declarations = compiler
        .compile(None, include_str!("slotted/languages/toy.egg"))
        .unwrap();
    let maintenance = compiler.compile(None, "(run 0)").unwrap();
    (declarations, maintenance)
}

#[test]
fn leader_reversals_preserve_identities_and_symmetries() {
    let (base, maintenance) = machinery();
    for order in PERMUTATIONS {
        for reverse in [false, true] {
            for symmetric in [false, true] {
                let mut graph = new_egraph();
                let mut program = format!("{base}\n(let $v (SlottedVar_0 0))\n");
                for (name, ctor) in ["a", "b", "c"]
                    .into_iter()
                    .zip(order.map(|i| ["F", "G", "H"][i]))
                {
                    program += &format!("(let ${name} ({ctor} (map-of 0 0) $v (map-of 0 1) $v))\n");
                }
                // The old c -> b edge becomes a -> b after union, reversing the
                // leader ordering. Clearing followers must retain a's identity.
                program +=
                    &format!("{maintenance}\n(Equated_0 $c (map-of 0 1 1 0) $b)\n{maintenance}\n");
                if symmetric {
                    program += &format!("(Equated_0 $a (map-of 0 1 1 0) $a)\n{maintenance}\n");
                }
                program += if reverse {
                    "(union $c $a)\n"
                } else {
                    "(union $a $c)\n"
                };
                program += &format!(
                    "{maintenance}\n(check (RenamesToLeader_0 $a (map-of 0 0 1 1) $a))\n(check (= g (EclassGroup_0 $a)) (set-contains g (map-of 0 0 1 1)))\n"
                );
                if symmetric {
                    program +=
                        "(check (= g (EclassGroup_0 $a)) (set-contains g (map-of 0 1 1 0)))\n";
                }
                graph
                    .parse_and_run_program(None, &program)
                    .unwrap_or_else(|e| {
                        panic!("{order:?}, reverse={reverse}, symmetric={symmetric}: {e}")
                    });
            }
        }
    }
}

#[test]
fn child_unions_preserve_fresh_shapes_and_cosets() {
    let (base, maintenance) = machinery();
    let parents = [
        "(H (map-of 0 1 1 0) $a (map-of 0 0) $v)",
        "(H (map-of 0 0 1 1) $b (map-of 0 0) $v)",
        "(H (map-of 0 1 1 0) $b (map-of 0 0) $v)",
    ];
    for reverse in [false, true] {
        for order in PERMUTATIONS {
            let mut children = [
                "(let $a (F (map-of 0 0) $v (map-of 0 1) $v))",
                "(let $b (G (map-of 0 0) $v (map-of 0 1) $v))",
            ];
            if reverse {
                children.reverse();
            }
            let mut program = format!(
                "{base}\n(let $v (SlottedVar_0 0))\n{}\n{maintenance}\n(Equated_0 $b (map-of 0 1 1 0) $b)\n{maintenance}\n",
                children.join("\n")
            );
            for i in order {
                program += parents[i];
                program += "\n";
            }
            program += &format!(
                "{maintenance}\n(union $a $b)\n{maintenance}\n{}\n{maintenance}\n",
                parents[1].replace("$b", "$a")
            );
            // Colliding cache keys after the native union must not let an old
            // shape replace a freshly recomputed shape or coset set.
            program += r#"
(ruleset observe)
(relation Fresh ())
(relation ObservedReadings ())
(relation StaleReadings ())
(rule ((= c (H m1 c1 m2 c2))
       (= g1 (EclassGroup_0 c1)) (= g2 (EclassGroup_0 c2))
       (= direct (node-shape (vec-of m1 m2) (vec-of g1 g2)))
       (= (values s1 s2 back syms) (_shapeof_H m1 g1 m2 g2))
       (= s1 (vec-get direct 0)) (= s2 (vec-get direct 1))
       (= back (vec-get direct 2)) (= syms (symmetries-of direct 3)))
      ((Fresh)) :ruleset observe)
(rule ((= stored (CosetReps_0 c pinned))) ((ObservedReadings)) :ruleset observe)
(rule ((= stored (CosetReps_0 c pinned)) (= grp (EclassGroup_0 c))
       (!= stored (group-coset-reps grp pinned)))
      ((StaleReadings)) :ruleset observe)
(run observe 1)
(check (Fresh))
(check (ObservedReadings))
"#;
            let mut graph = new_egraph();
            graph.parse_and_run_program(None, &program).unwrap();
            assert_eq!(graph.get_size("H"), 1, "{reverse}, {order:?}");
            assert_eq!(graph.get_size("StaleReadings"), 0, "{reverse}, {order:?}");
        }
    }
}

fn render(form: &Sexp) -> String {
    match form {
        Sexp::Atom(s, _) => s.clone(),
        Sexp::Literal(l, _) => l.to_string(),
        Sexp::List(xs, _) => format!("({})", xs.iter().map(render).collect::<Vec<_>>().join(" ")),
    }
}

#[test]
fn substitution_is_independent_of_table_order() {
    let scratch =
        Scratch(std::env::temp_dir().join(format!("slotted-substitution-{}", std::process::id())));
    fs::create_dir(&scratch.0).unwrap();
    let input = scratch.0.join("input.egg");
    let output = scratch.0.join("graph.json");
    let source = include_str!("slotted/sdql-paper-mmm.egg");
    let forms = parse_sexps(None, source).unwrap();
    for rounds in [4, 12] {
        // Keep the fixture's rules, input, and delayed target, changing only the
        // user-round budget. The target is not expected to be reached this early.
        let program = forms
            .iter()
            .filter_map(|f| {
                let Sexp::List(xs, _) = f else { return None };
                match xs.first() {
                    Some(Sexp::Atom(h, _)) if h == "check" => None,
                    Some(Sexp::Atom(h, _)) if h == "run" && render(f) == "(run 30)" => {
                        Some(format!("(run {rounds})"))
                    }
                    _ => Some(render(f)),
                }
            })
            .collect::<Vec<_>>()
            .join("\n")
            .replace(
                "egglog-experimental/",
                &format!("{}/", env!("CARGO_MANIFEST_DIR")),
            );
        fs::write(
            &input,
            format!("{program}\n(slotted-export {:?})", output.to_str().unwrap()),
        )
        .unwrap();
        let mut baseline = None;
        for _ in 0..4 {
            // Fresh processes exercise randomized hash/table ordering, as well as
            // fresh graphs. Never reuse an export left by a previous process.
            if output.exists() {
                fs::remove_file(&output).unwrap();
            }
            let result = Command::new(env!("CARGO_BIN_EXE_egglog-experimental"))
                .args(["--slotted", input.to_str().unwrap()])
                .output()
                .unwrap();
            assert!(
                result.status.success(),
                "{}",
                String::from_utf8_lossy(&result.stderr)
            );
            let document: serde_json::Value =
                serde_json::from_slice(&fs::read(&output).unwrap()).unwrap();
            let counts = (
                document["counts"]["classes"].as_u64().unwrap(),
                document["counts"]["nodes"].as_u64().unwrap(),
            );
            let annotated: AnnotatedEGraph = serde_json::from_value(document).unwrap();
            let graph = Graph::try_from(&annotated).unwrap();
            if let Some((first_counts, first)) = &baseline {
                assert_eq!(*first_counts, counts, "{rounds} rounds");
                let outcome = find_isomorphism(first, &graph, Limits::default()).unwrap();
                let Outcome::Isomorphic { witness } = outcome else {
                    panic!("{rounds} rounds: {outcome:?}")
                };
                verify(first, &graph, &witness).unwrap();
            } else {
                baseline = Some((counts, graph));
            }
        }
    }
}

#[test]
fn exporting_does_not_run_another_user_round() {
    let encoded = Compiler::default()
        .compile(
            None,
            r#"
(datatype U (Null) (F U U))
(rewrite (Null) (F $a $a))
(let start (Null))
(run 1)
"#,
        )
        .unwrap();
    let mut graph = new_egraph();
    graph.parse_and_run_program(None, &encoded).unwrap();
    graph
        .parse_and_run_program(
            None,
            r#"(rule () ((panic "export exceeded the round budget")))"#,
        )
        .unwrap();
    let exported = export(&graph).unwrap();
    assert_eq!((exported.counts.classes, exported.counts.nodes), (2, 3));
}
