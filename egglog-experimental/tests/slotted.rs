use egglog::CommandOutput;
use egglog_experimental::slotted::{Compiler, Options, ProofMode, new_egraph_with_proofs};
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

const LANGUAGE: &str = "(datatype U (V Var) (Null) (F U U) (G U U) (H U U) (Lam Var U :binder 0))";

fn evaluate(compiler: &mut Compiler, graph: &mut egglog::EGraph, source: &str) {
    let encoded = compiler.compile(None, source).unwrap();
    graph.parse_and_run_program(None, &encoded).unwrap();
}

#[test]
fn string_payloads_preserve_quotes_and_backslashes() {
    let mut compiler = Compiler::default();
    let mut graph = egglog_experimental::slotted::new_egraph();
    evaluate(
        &mut compiler,
        &mut graph,
        r#"(datatype U (V Var) (Text String)) (let value (Text "a\"b\\c"))"#,
    );
    graph
        .parse_and_run_program(None, r#"(check (= text (Text "a\"b\\c")))"#)
        .unwrap();
}

#[test]
fn transformation_emits_ordinary_egglog() {
    let mut compiler = Compiler::default();
    let mut graph = egglog_experimental::slotted::new_egraph();
    evaluate(&mut compiler, &mut graph, LANGUAGE);
    evaluate(
        &mut compiler,
        &mut graph,
        r#"
        (rewrite (F a b) (G b a) :when () :name "swap")
        (let start (F (V $1) (V $2)))
        (run 1)
        (let slot_2 $2)
        (let slot_1 $1)
        (check (= start (G (V slot_2) (V slot_1))))
        (check (!= start (G (V slot_1) (V slot_2))))
        (check (free-names-are start slot_1 slot_2))
    "#,
    );
}

#[test]
fn checks_and_rule_guards_agree_on_equality() {
    // Each case runs in its own graph: firing a rule must not change another
    // case's premise. Expected answers distinguish class identity, free slots,
    // alpha-equivalence, sharing, symmetries, and redundant slots.
    let cases = [
        ("", "(V $a)", "(V $a)", true, true),
        ("", "(V $a)", "(V $b)", false, true),
        ("", "(Null)", "(Hit)", false, false),
        ("", "(F (V $a) (V $b))", "(G (V $a) (V $b))", false, false),
        ("", "(F (V $a) (V $b))", "(F (V $b) (V $a))", false, true),
        ("", "(F (V $a) (V $a))", "(F (V $a) (V $b))", false, false),
        ("", "(Lam $a (V $a))", "(Lam $b (V $b))", true, true),
        ("", "(Lam $x (V $a))", "(Lam $x (V $b))", false, true),
        ("", "(Lam $a (V $a))", "(Lam $x (V $a))", false, false),
        (
            "(union (F (V $a) (V $b)) (F (V $b) (V $a)))",
            "(F (V $a) (V $b))",
            "(F (V $b) (V $a))",
            true,
            true,
        ),
        (
            "(union (F (V $a) (V $b)) (G (V $a) (Null)))",
            "(F (V $a) (V $b))",
            "(F (V $a) (V $c))",
            true,
            true,
        ),
        (
            "(union (F (V $a) (V $b)) (G (V $a) (Null)))",
            "(F (V $a) (V $b))",
            "(F (V $b) (V $c))",
            false,
            true,
        ),
    ];
    for no_aliasing in [false, true] {
        for (prelude, lhs, rhs, equal, renamed) in cases {
            for (op, expected) in [
                ("=", equal),
                ("!=", !equal),
                ("renaming-=", renamed),
                ("renaming-!=", !renamed),
            ] {
                let mut compiler = Compiler::new(Options {
                    no_aliasing,
                    ..Default::default()
                });
                let mut graph = egglog_experimental::slotted::new_egraph();
                let check = format!("(check ({op} left right))");
                let check = if expected {
                    check
                } else {
                    format!("(fail {check})")
                };
                evaluate(
                    &mut compiler,
                    &mut graph,
                    &format!(
                        "{LANGUAGE}
                         (constructor Pair (U U) U)
                         (constructor Hit () U)
                         {prelude}
                         (let pair (Pair {lhs} {rhs}))
                         (let left {lhs})
                         (let right {rhs})
                         (run 0)
                         {check}
                         (rewrite (Pair a b) (Hit) :when (({op} a b)))
                         (run 1)
                         (check ({} pair Hit))",
                        if expected {
                            "__internal-holds"
                        } else {
                            "__internal-not-holds"
                        }
                    ),
                );
            }
        }
    }
}

#[test]
fn rule_comparisons_require_two_bound_variables() {
    let mut compiler = Compiler::default();
    compiler.compile(None, LANGUAGE).unwrap();
    for op in ["=", "!=", "renaming-=", "renaming-!="] {
        for args in ["a", "a b c", "a missing", "missing b"] {
            let source = format!("(rewrite (F a b) a :when (({op} {args})))");
            assert!(compiler.compile(None, &source).is_err(), "{source}");
        }
    }
}

#[test]
fn named_slots_persist_across_inputs_and_scopes() {
    let mut compiler = Compiler::default();
    let mut graph = egglog_experimental::slotted::new_egraph();
    evaluate(&mut compiler, &mut graph, LANGUAGE);
    evaluate(&mut compiler, &mut graph, "(let a (F (V $a) (V $a0)))");
    evaluate(
        &mut compiler,
        &mut graph,
        "(push) (let local (F (V $temp) (V $-9223372036854775808))) (pop)",
    );
    evaluate(
        &mut compiler,
        &mut graph,
        r#"
        (let b (F (V $a) (V $-9223372036854775808)))
        (run 0)
        (let slot_a $a)
        (let slot_a0 $a0)
        (check (= a (F (V slot_a) (V slot_a0))))
        (check (free-names-are a slot_a slot_a0))
        (let slot_minus_9223372036854775808 $-9223372036854775808)
        (check (free-names-are b slot_a slot_minus_9223372036854775808))
        (check (!= a b))
        (check (!= (V slot_a) (V slot_minus_9223372036854775808)))
    "#,
    );
    assert!(
        compiler
            .compile(None, "(let bad (F (V $fresh) missing))")
            .is_err()
    );
    evaluate(
        &mut compiler,
        &mut graph,
        "(let valid (F (V $fresh) (V $a))) (run 0) (let slot_fresh $fresh)\n(check (free-names-are valid slot_fresh slot_a))",
    );
}

#[test]
fn binder_columns_require_slots() {
    let mut compiler = Compiler::default();
    let mut graph = egglog_experimental::slotted::new_egraph();
    evaluate(&mut compiler, &mut graph, LANGUAGE);
    for source in [
        "(let bad (Lam (Null) (Null)))",
        "(let alias (F (V $a) (V $a))) (let bad (Lam alias (Null)))",
        "(rewrite (Lam x a) a)",
        "(rewrite (F x a) (Lam x a))",
        "(let bad (F (V $9223372036854775808) (V $a)))",
        "(let bad (F (V $) (V $a)))",
    ] {
        assert!(
            compiler.compile(None, source).is_err(),
            "accepted: {source}"
        );
    }
    evaluate(
        &mut compiler,
        &mut graph,
        r#"
        (constructor Tagged (String Var U) U :binder 0)
        (let id (Tagged "lambda" $a (V $a)))
        (run 0)
        (check (= id (Tagged "lambda" $b (V $b))))
        (check (free-names-are id))
    "#,
    );
}

#[test]
fn sorts_can_have_only_a_variable_constructor() {
    for declaration in [
        "(sort Expr)\n(constructor VExpr (Var) Expr)",
        "(datatype Expr (VExpr Var))",
    ] {
        let mut compiler = Compiler::default();
        let mut graph = egglog_experimental::slotted::new_egraph();
        evaluate(&mut compiler, &mut graph, declaration);
        evaluate(
            &mut compiler,
            &mut graph,
            r#"
            (run 0)
            (let slot_a $a)
            (let slot_b $b)
            (let a (VExpr slot_a))
            (let b (VExpr slot_b))
            (check (= a a))
            (check (!= a b))
            (check (renaming-= a b))
        "#,
        );
        assert_eq!(graph.get_size("VExpr"), 1);
    }
}

#[test]
fn slots_work_in_every_carrier_with_distinct_variable_constructors() {
    let mut compiler = Compiler::default();
    let mut graph = egglog_experimental::slotted::new_egraph();
    evaluate(
        &mut compiler,
        &mut graph,
        r#"
        (datatype*
            (Expr (VExpr Var) (Lam Var Expr :binder 0))
            (Named (Variable Var) (Name String) (Wrap Named))
            (Ty (VTy Var) (Pair Ty Ty)))
        (let id (Lam $a (VExpr $a)))
        (let name (Wrap (Name "x")))
        (let variable (Wrap (Variable $a)))
        (let ty (Pair (VTy $a) (VTy $b)))
        (run 0)
        (check (= id (Lam $b (VExpr $b))))
        (check (free-names-are name))
        (let slot_a $a)
        (check (free-names-are variable slot_a))
        (let slot_b $b)
        (check (free-names-are ty slot_a slot_b))
    "#,
    );
    for table in ["VExpr", "Variable", "VTy"] {
        assert_eq!(graph.get_size(table), 1);
    }
    assert!(compiler.compile(None, "(let bad (Lam $a name))").is_err());
    assert!(
        compiler
            .compile(None, "(datatype Bad (VBad Var) ($Var))")
            .is_err()
    );
}

#[test]
fn scopes_restore_declarations_globals_and_rules() {
    let mut compiler = Compiler::default();
    let mut graph = egglog_experimental::slotted::new_egraph();
    evaluate(
        &mut compiler,
        &mut graph,
        r#"
        (push)
        (datatype U (V Var) (F U))
        (let local (F (V $0)))
        (rewrite (F a) (F (F a)))
        (pop)
        (datatype U (V Var) (F U U))
        (let local (F (V $1) (V $2)))
        (run 0)
        (let slot_1 $1)
        (let slot_2 $2)
        (check (free-names-are local slot_1 slot_2))
    "#,
    );
    evaluate(
        &mut compiler,
        &mut graph,
        "(push) (datatype Local (VLocal Var) (Zero)) (let n (Zero)) (run 0)",
    );
    evaluate(
        &mut compiler,
        &mut graph,
        "(pop) (datatype Local (VLocal Var) (One)) (let n (One)) (run 0)",
    );
    assert!(compiler.compile(None, "(let bad (Zero))").is_err());
}

#[test]
fn compilation_errors_are_transactional_and_located() {
    let mut compiler = Compiler::default();
    let error = compiler
        .compile(
            Some("bad.egg".into()),
            "(datatype U (V Var) (F U))\n(let x missing)",
        )
        .unwrap_err();
    assert!(error.to_string().contains("bad.egg"));
    assert!(compiler.compile(None, LANGUAGE).is_ok());
    for source in [
        "(ruleset slotted-group)",
        r#"(datatype "bad)" (Variable Var) (Zero))"#,
        r#"(constructor "bad)" () U)"#,
        "(let x (F (V $0) (V $1))) (let x x)",
        "(constructor SlottedSlotLayout () U)",
        "(sort Idx)\n(constructor VIdx (Var) Idx)",
        "(rewrite (F a b) a :when (= a b))",
        "(rewrite (Lam x a) a)",
        "(constructor Broken (U U) U :binder 18446744073709551615)",
    ] {
        assert!(
            compiler.compile(None, source).is_err(),
            "accepted: {source}"
        );
    }
}

#[test]
fn matching_policy_changes_aliasing() {
    for no_aliasing in [false, true] {
        let mut compiler = Compiler::new(Options {
            no_aliasing,
            ..Default::default()
        });
        let mut graph = egglog_experimental::slotted::new_egraph();
        evaluate(&mut compiler, &mut graph, LANGUAGE);
        evaluate(
            &mut compiler,
            &mut graph,
            r#"
            (union (G (V $0) (Null)) (Null))
            (let start (F (V $1) (Null)))
            (let slot_1 $1)
            (rewrite (F a (G b n)) (H a b))
            (run 1)
        "#,
        );
        let claim = "(check (= start (H (V slot_1) (V slot_1))))";
        let claim = if no_aliasing {
            format!("(fail {claim})")
        } else {
            claim.to_owned()
        };
        evaluate(&mut compiler, &mut graph, &claim);
    }
}

#[test]
fn compatibility_cli_uses_the_same_matching_policy_for_checks_and_rules() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_egglog-experimental"))
        .args(["--slotted", "--slotted-no-aliasing", "--mode", "desugar"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    write!(child.stdin.take().unwrap(), "{LANGUAGE}\n(rewrite (F a (G b n)) (H a b))\n(check (= (F (V $a) (G (V $b) (Null))) (F (V $a) (G (V $b) (Null)))))").unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let encoded = String::from_utf8(output.stdout).unwrap();
    assert!(encoded.contains("(nested-atom ") && !encoded.contains("(atom "));

    let mut compiler = Compiler::new(Options {
        no_aliasing: true,
        ..Default::default()
    });
    compiler.compile(None, LANGUAGE).unwrap();
    let error = compiler
        .compile(None, "(rewrite (F a b) a :when ((= b (G x y))))")
        .unwrap_err();
    assert!(error.to_string().contains("single nested pattern"));
}

#[test]
fn checks_and_rule_guards_agree_on_free_names() {
    for no_aliasing in [false, true] {
        for (body, predicate, expected) in [
            ("(Lam $bound (V $a))", "free $a body", true),
            ("(Lam $bound (V $b))", "free $a body", false),
            ("(Lam $bound (V $a))", "not-free $a body", false),
            ("(Lam $bound (V $b))", "not-free $a body", true),
            ("(Lam $bound (V $a))", "free-names-are body $a", true),
            ("(Lam $bound (V $b))", "free-names-are body $a", false),
            ("(Lam $bound (V $bound))", "free-names-are body", true),
            ("(F (V $a) (V $b))", "free-names-are body $a", false),
        ] {
            let mut compiler = Compiler::new(Options {
                no_aliasing,
                ..Default::default()
            });
            let mut graph = egglog_experimental::slotted::new_egraph();
            let check = format!(
                "(check ({}))",
                predicate
                    .replace("body", "checked_body")
                    .replace("$a", "concrete_a")
            );
            let check = if expected {
                check
            } else {
                format!("(fail {check})")
            };
            let result = if expected {
                "__internal-holds"
            } else {
                "__internal-not-holds"
            };
            evaluate(
                &mut compiler,
                &mut graph,
                &format!(
                    r#"
{LANGUAGE}
(let seed (F (V $a) {body}))
(let checked_body {body})
(let concrete_a $a)
(run 0)
{check}
(rewrite (F (V $a) body) (Null) :when (({predicate})))
(run 1)
(check ({result} seed Null))
"#
                ),
            );
        }
    }
}

struct Temp(PathBuf);
impl Temp {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "slotted-cli-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Temp {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}
fn cli() -> Command {
    Command::new(env!("CARGO_BIN_EXE_egglog-experimental"))
}

#[test]
fn cli_reuses_files_includes_serialization_and_timing_reports() {
    let temp = Temp::new();
    std::fs::write(temp.0.join("language.egg"), LANGUAGE).unwrap();
    std::fs::write(
        temp.0.join("first.egg"),
        "(include \"language.egg\")\n(let input (F (V $a) (V $a0)))",
    )
    .unwrap();
    std::fs::write(
        temp.0.join("second.egg"),
        "(rewrite (F a b) (G b a))\n(run 1)\n(let slot_a0 $a0)\n(let slot_a $a)\n(check (= input (G (V slot_a0) (V slot_a))))",
    )
    .unwrap();
    let result = cli()
        .current_dir(&temp.0)
        .args([
            "--slotted",
            "--to-json",
            "--timing-summary",
            "timing.json",
            "first.egg",
            "second.egg",
        ])
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    for file in ["first.json", "second.json", "timing.json"] {
        let data = std::fs::read(temp.0.join(file)).unwrap();
        serde_json::from_slice::<serde_json::Value>(&data).unwrap();
    }
}

fn repl(source: &str) -> std::process::Output {
    let mut child = cli()
        .args(["--slotted", "--mode", "interactive"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut input = child.stdin.take().unwrap();
    writeln!(input, "{source}").unwrap();
    drop(input);
    child.wait_with_output().unwrap()
}

#[test]
fn cli_transforms_complete_stdin_commands() {
    let result = repl(&format!(
        "{LANGUAGE}\n(let input (F (V $a)\n (V $a0)))\n(let slot_a $a)\n(let slot_a0 $a0)\n(run 0)\n(check (free-names-are input slot_a slot_a0))"
    ));
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let stdout = String::from_utf8(result.stdout).unwrap();
    assert!(!stdout.contains("(error)"), "{stdout}");
    assert_eq!(stdout.matches("(done)").count(), 6, "{stdout}");
}

#[test]
fn cli_recovers_compiler_and_egraph_after_failed_inputs() {
    let result = repl(
        "(datatype U (VVar Var) (Null)) (function broken)
(datatype U (VVar Var) (Null) (One))
(let transient (Null)) (check (= (Null) (One))) (let later (One))
(fail (check (= (Null) (Null))))
(let transient (One)) (let later (Null)) (run 0)
(check (__internal-holds transient One)) (check (__internal-holds later Null))
(push)
(pop) (datatype V (VV Var) (Gone)) (check (= (Null) (One)))
(pop)
(datatype V (VV Var) (Kept)) (let x (Kept)) (run 0) (check (__internal-holds x Kept))
(datatype W (VW Var) (BadCtor)) (function cost (Missing) i64 :no-merge)
(datatype W (VW Var) (GoodCtor))
(let typed (GoodCtor)) (run 0) (check (__internal-holds typed GoodCtor))",
    );
    let stdout = String::from_utf8(result.stdout).unwrap();
    let stderr = String::from_utf8(result.stderr).unwrap();
    assert!(result.status.success(), "{stdout}\n{stderr}");
    assert_eq!(stdout.matches("(error)").count(), 4, "{stdout}\n{stderr}");
    assert_eq!(stdout.matches("(done)").count(), 9, "{stdout}\n{stderr}");
    assert!(!stderr.contains("panicked"), "{stderr}");
}

#[test]
fn cli_explains_flags_and_rejects_incompatible_modes() {
    let help = cli().arg("--help").output().unwrap();
    assert!(help.status.success());
    assert!(
        String::from_utf8(help.stdout)
            .unwrap()
            .contains("--slotted")
    );
    for flags in [
        vec!["--slotted-no-aliasing"],
        vec!["--slotted", "--proof-testing"],
    ] {
        let result = cli().args(flags).output().unwrap();
        assert_eq!(result.status.code(), Some(2));
        assert!(
            !String::from_utf8(result.stderr)
                .unwrap()
                .contains("panicked")
        );
    }
}

#[test]
fn side_patterns_can_bind_the_rewrite_root() {
    let mut compiler = Compiler::default();
    let mut graph = egglog_experimental::slotted::new_egraph();
    evaluate(&mut compiler, &mut graph, LANGUAGE);
    evaluate(
        &mut compiler,
        &mut graph,
        r#"
        (let start (F (G (V $a) (V $b)) (Null)))
        (rewrite child (H (V $x) (V $y)) :when ((= parent (F child n)) (= child (G (V $x) (V $y)))))
        (run 1)
        (check (= (G (V $a) (V $b)) (H (V $a) (V $b))))
        (check (!= (G (V $a) (V $b)) (H (V $b) (V $a))))
    "#,
    );
    for source in [
        "(rewrite missing (Null))",
        "(rewrite missing (Null) :when ((= other (Null))))",
    ] {
        assert!(compiler.compile(None, source).is_err(), "{source}");
    }
}

#[test]
fn proofs_keep_reused_rule_names_distinct_across_scopes() {
    let mut compiler = Compiler::new(Options {
        proof_mode: ProofMode::Prove,
        ..Default::default()
    });
    let program = compiler
        .compile(
            None,
            r#"
        (datatype U (V Var) (Num i64) (Wrap U))
        (push)
        (rewrite (Num n) (Wrap (Num n)) :name "repeat")
        (let a (Num 1))
        (run 1)
        (check (= a (Wrap (Num 1))))
        (pop)
        (push)
        (rewrite (Wrap x) x :name "repeat")
        (let b (Wrap (Num 2)))
        (run 1)
        (check (= b (Num 2)))
        (pop)
    "#,
        )
        .unwrap();
    let outputs = new_egraph_with_proofs()
        .parse_and_run_program(None, &program)
        .unwrap();
    assert_eq!(
        outputs
            .iter()
            .filter(|o| matches!(o, CommandOutput::UserDefined(_)))
            .count(),
        2
    );
}
