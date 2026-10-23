use egglog_experimental::slotted::{Compiler, Options};
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

const LANGUAGE: &str = "(datatype U (Null) (F U U) (G U U) (H U U) (Lam U U :binder 0))";

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
        r#"(datatype U (Text String)) (let value (Text "a\"b\\c"))"#,
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
        (let start (F $1 $2))
        (run 1)
        (check (= start (G $2 $1)))
        (check (!= start (G $1 $2)))
        (check (free-names-are start $1 $2))
    "#,
    );
}

#[test]
fn checks_and_rule_guards_agree_on_equality() {
    // Each case runs in its own graph: firing a rule must not change another
    // case's premise. Expected answers distinguish class identity, free slots,
    // alpha-equivalence, sharing, symmetries, and redundant slots.
    let cases = [
        ("", "$a", "$a", true, true),
        ("", "$a", "$b", false, true),
        ("", "(Null)", "(Hit)", false, false),
        ("", "(F $a $b)", "(G $a $b)", false, false),
        ("", "(F $a $b)", "(F $b $a)", false, true),
        ("", "(F $a $a)", "(F $a $b)", false, false),
        ("", "(Lam $a $a)", "(Lam $b $b)", true, true),
        ("", "(Lam $x $a)", "(Lam $x $b)", false, true),
        ("", "(Lam $a $a)", "(Lam $x $a)", false, false),
        (
            "(union (F $a $b) (F $b $a))",
            "(F $a $b)",
            "(F $b $a)",
            true,
            true,
        ),
        (
            "(union (F $a $b) (G $a (Null)))",
            "(F $a $b)",
            "(F $a $c)",
            true,
            true,
        ),
        (
            "(union (F $a $b) (G $a (Null)))",
            "(F $a $b)",
            "(F $b $c)",
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
                let mut compiler = Compiler::new(Options { no_aliasing });
                let mut graph = egglog_experimental::slotted::new_egraph();
                let check = format!("(check ({op} {lhs} {rhs}))");
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
        for args in ["a", "a b c", "a missing", "missing b", "a $x"] {
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
    evaluate(&mut compiler, &mut graph, "(let a (F $a $a0))");
    evaluate(
        &mut compiler,
        &mut graph,
        "(push) (let local (F $temp $-9223372036854775808)) (pop)",
    );
    evaluate(
        &mut compiler,
        &mut graph,
        r#"
        (let b (F $a $-9223372036854775808))
        (run 0)
        (check (= a (F $a $a0)))
        (check (free-names-are a $a $a0))
        (check (free-names-are b $a $-9223372036854775808))
        (check (!= a b))
        (check (!= $a $-9223372036854775808))
    "#,
    );
    assert!(
        compiler
            .compile(None, "(let bad (F $fresh missing))")
            .is_err()
    );
    evaluate(
        &mut compiler,
        &mut graph,
        "(let valid (F $fresh $a)) (run 0) (check (free-names-are valid $fresh $a))",
    );
}

#[test]
fn binder_columns_require_slots() {
    let mut compiler = Compiler::default();
    let mut graph = egglog_experimental::slotted::new_egraph();
    evaluate(&mut compiler, &mut graph, LANGUAGE);
    for source in [
        "(let bad (Lam (Null) (Null)))",
        "(let alias (F $a $a)) (let bad (Lam alias (Null)))",
        "(rewrite (Lam x a) a)",
        "(rewrite (F x a) (Lam x a))",
        "(let bad (F $9223372036854775808 $a))",
        "(let bad (F $ $a))",
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
        (constructor Tagged (String U U) U :binder 0)
        (let id (Tagged "lambda" $a $a))
        (run 0)
        (check (= id (Tagged "lambda" $b $b)))
        (check (free-names-are id))
    "#,
    );
}

#[test]
fn sorts_support_slots_without_user_constructors() {
    for declaration in ["(sort Expr)", "(datatype Expr)"] {
        let mut compiler = Compiler::default();
        let mut graph = egglog_experimental::slotted::new_egraph();
        evaluate(&mut compiler, &mut graph, declaration);
        evaluate(
            &mut compiler,
            &mut graph,
            r#"
            (run 0)
            (check (= $a $a))
            (check (!= $a $b))
            (check (renaming-= $a $b))
        "#,
        );
        assert_eq!(graph.get_size("SlottedVar_0"), 1);
    }
}

#[test]
fn slots_work_in_every_carrier_and_var_is_an_ordinary_name() {
    let mut compiler = Compiler::default();
    let mut graph = egglog_experimental::slotted::new_egraph();
    evaluate(
        &mut compiler,
        &mut graph,
        r#"
        (datatype*
            (Expr (Lam Expr Expr :binder 0))
            (Var (Name String) (Wrap Var))
            (Ty (Pair Ty Ty)))
        (let id (Lam $a $a))
        (let name (Wrap (Name "x")))
        (let variable (Wrap $a))
        (let ty (Pair $a $b))
        (run 0)
        (check (= id (Lam $b $b)))
        (check (free-names-are name))
        (check (free-names-are variable $a))
        (check (free-names-are ty $a $b))
    "#,
    );
    for table in ["SlottedVar_0", "SlottedVar_1", "SlottedVar_2"] {
        assert_eq!(graph.get_size(table), 1);
    }
    assert!(compiler.compile(None, "(let bad (Lam $a name))").is_err());
    assert!(compiler.compile(None, "(datatype Bad ($Var))").is_err());
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
        (datatype U (F U))
        (let local (F $0))
        (rewrite (F a) (F (F a)))
        (pop)
        (datatype U (F U U))
        (let local (F $1 $2))
        (run 0)
        (check (free-names-are local $1 $2))
    "#,
    );
    evaluate(
        &mut compiler,
        &mut graph,
        "(push) (datatype V (Zero)) (let n (Zero)) (run 0)",
    );
    evaluate(
        &mut compiler,
        &mut graph,
        "(pop) (datatype V (One)) (let n (One)) (run 0)",
    );
    assert!(compiler.compile(None, "(let bad (Zero))").is_err());
}

#[test]
fn compilation_errors_are_transactional_and_located() {
    let mut compiler = Compiler::default();
    let error = compiler
        .compile(
            Some("bad.egg".into()),
            "(datatype U (F U))\n(let x missing)",
        )
        .unwrap_err();
    assert!(error.to_string().contains("bad.egg"));
    assert!(compiler.compile(None, LANGUAGE).is_ok());
    for source in [
        "(ruleset slotted-group)",
        r#"(datatype "bad)" (Zero))"#,
        r#"(constructor "bad)" () U)"#,
        "(let x (F $0 $1)) (let x x)",
        "(constructor SlottedVar_0 () U)",
        "(sort Idx)",
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
fn matching_policy_changes_aliasing_and_checks_remain_unrestricted() {
    for no_aliasing in [false, true] {
        let mut compiler = Compiler::new(Options { no_aliasing });
        let mut graph = egglog_experimental::slotted::new_egraph();
        evaluate(&mut compiler, &mut graph, LANGUAGE);
        evaluate(
            &mut compiler,
            &mut graph,
            r#"
            (union (G $0 (Null)) (Null))
            (let start (F $1 (Null)))
            (rewrite (F a (G b n)) (H a b))
            (run 1)
        "#,
        );
        let claim = "(check (= start (H $1 $1)))";
        let claim = if no_aliasing {
            format!("(fail {claim})")
        } else {
            claim.to_owned()
        };
        evaluate(&mut compiler, &mut graph, &claim);
    }
}

#[test]
fn compatibility_cli_restricts_rules_but_not_checks() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_egglog-experimental"))
        .args(["--slotted", "--slotted-no-aliasing", "--mode", "desugar"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    write!(child.stdin.take().unwrap(), "{LANGUAGE}\n(rewrite (F a (G b n)) (H a b))\n(check (= (F $a (G $b (Null))) (F $a (G $b (Null)))))").unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let encoded = String::from_utf8(output.stdout).unwrap();
    assert!(encoded.contains("(nested-atom ") && encoded.contains("(atom "));

    let mut compiler = Compiler::new(Options { no_aliasing: true });
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
            ("(Lam $bound $a)", "free $a body", true),
            ("(Lam $bound $b)", "free $a body", false),
            ("(Lam $bound $a)", "not-free $a body", false),
            ("(Lam $bound $b)", "not-free $a body", true),
            ("(Lam $bound $a)", "free-names-are body $a", true),
            ("(Lam $bound $b)", "free-names-are body $a", false),
            ("(Lam $bound $bound)", "free-names-are body", true),
            ("(F $a $b)", "free-names-are body $a", false),
        ] {
            let mut compiler = Compiler::new(Options { no_aliasing });
            let mut graph = egglog_experimental::slotted::new_egraph();
            let check = format!("(check ({}))", predicate.replace("body", body));
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
(let seed (F $a {body}))
(run 0)
{check}
(rewrite (F $a body) (Null) :when (({predicate})))
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
        "(include \"language.egg\")\n(let input (F $a $a0))",
    )
    .unwrap();
    std::fs::write(
        temp.0.join("second.egg"),
        "(rewrite (F a b) (G b a))\n(run 1)\n(check (= input (G $a0 $a)))",
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
        "{LANGUAGE}\n(let input (F $a\n $a0))\n(run 0)\n(check (free-names-are input $a $a0))"
    ));
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let stdout = String::from_utf8(result.stdout).unwrap();
    assert!(!stdout.contains("(error)"), "{stdout}");
    assert_eq!(stdout.matches("(done)").count(), 4, "{stdout}");
}

#[test]
fn cli_recovers_compiler_and_egraph_after_failed_inputs() {
    let result = repl(
        "(datatype U (Null)) (function broken)\n\
         (datatype U (Null) (One))\n\
         (let transient (Null)) (check (= (Null) (One))) (let later (One))\n\
         (fail (check (= (Null) (Null))))\n\
         (let transient (One)) (let later (Null)) (run 0)\n\
         (check (__internal-holds transient One)) (check (__internal-holds later Null))\n\
         (push)\n\
         (pop) (datatype V (Gone)) (check (= (Null) (One)))\n\
         (pop)\n\
         (datatype V (Kept)) (let x (Kept)) (run 0) (check (__internal-holds x Kept))\n\
         (datatype W (BadCtor)) (function cost (Missing) i64 :no-merge)\n\
         (datatype W (GoodCtor))\n\
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
    for flags in [vec!["--slotted-no-aliasing"], vec!["--slotted", "--proofs"]] {
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
        (let start (F (G $a $b) (Null)))
        (rewrite child (H $x $y) :when ((= parent (F child n)) (= child (G $x $y))))
        (run 1)
        (check (= (G $a $b) (H $a $b)))
        (check (!= (G $a $b) (H $b $a)))
    "#,
    );
    for source in [
        "(rewrite missing (Null))",
        "(rewrite missing (Null) :when ((= other (Null))))",
    ] {
        assert!(compiler.compile(None, source).is_err(), "{source}");
    }
}
