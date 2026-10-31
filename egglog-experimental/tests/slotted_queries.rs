//! Public checks and rewrite guards share existential query semantics.
use egglog_experimental::slotted::{Compiler, Options, new_egraph};

const LANGUAGE: &str =
    "(datatype E (VE Var) (N i64) (F E E) (G E E) (Out E E) (Lam Var E :binder 0) (Hit))";

fn run(source: &str) {
    for no_aliasing in [false, true] {
        let program = Compiler::new(Options {
            no_aliasing,
            ..Default::default()
        })
        .compile(None, &format!("{LANGUAGE}\n{source}"))
        .unwrap();
        new_egraph().parse_and_run_program(None, &program).unwrap();
    }
}

#[test]
fn slots_are_local_to_each_check_and_globals_are_concrete() {
    run(r#"
        (let a $a)
        (let b $b)
        (let alias a)
        (let seed (F (VE a) (VE b)))
        (run 0)
        (check (F (VE $x) (VE $y)))
        (check (= (VE a) (VE $s)))
        (check (= (VE b) (VE $s)))
        (check (= (VE a) (VE alias)))
        (check (!= (VE a) (VE b)))
        (fail (check (= (VE a) (VE b))))
        (check (= (VE a) (VE $x)) (= (VE b) (VE $y)) (!= (VE $x) (VE $y)))
        (fail (check (= (VE a) (VE $x)) (= (VE b) (VE $x))))
        (check (= seed (F (VE a) (VE b))))
        (fail (check (= seed (F (VE b) (VE a)))))
    "#);
}

#[test]
fn guards_share_the_patterns_slot_assignment() {
    run(r#"
        (let a $a)
        (let b $b)
        (let shared (F (VE a) (VE a)))
        (let separate (F (VE a) (VE b)))
        (run 0)
        (check (= shared (F (VE $x) body)) (free $x body))
        (check (= separate (F (VE $x) body)) (not-free $x body))
        (fail (check (= shared (F (VE $x) body)) (not-free $x body)))
        (fail (check (= separate (F (VE $x) body)) (free $x body)))
        (check (free-names-are shared a))
        (check (free-names-are separate a b))
        (fail (check (free-names-are shared b)))
    "#);
}

#[test]
fn disequality_is_an_existential_guard() {
    run(r#"
        (let same (F (N 1) (N 1)))
        (let different (F (N 1) (N 2)))
        (run 0)
        (check (= p (F x y)) (= x y))
        (check (= p (F x y)) (!= x y))
        (fail (check (= same (F x y)) (!= x y)))
        (fail (check (= different (F x y)) (= x y)))
        (fail (check (G x y) (!= x y)))
    "#);
}

#[test]
fn global_bindings_respect_symmetries_and_redundant_slots() {
    run(r#"
        (let a $a)
        (let b $b)
        (let forward (F (VE a) (VE b)))
        (let backward (F (VE b) (VE a)))
        (union forward backward)
        (run 0)
        (check (= forward backward))
        (check (= x forward) (= x backward))
        (check (= x forward) (= x (F (VE b) (VE a))))
        (union (G (VE $a) (VE $b)) (N 0))
        (let redundant (G (VE a) (VE b)))
        (run 0)
        (check (= redundant (G (VE $x) (VE $y))))
        (check (free-names-are redundant))
    "#);
}

#[test]
fn a_guard_excludes_capture_of_a_concrete_global() {
    run(r#"
        (let a $a)
        (let term_a (VE a))
        (let identity (Lam $bound (VE $bound)))
        (let constant (Lam $bound term_a))
        (run 0)
        (check (= identity (Lam $x term_a)))
        (fail (check (= identity (Lam $x term_a)) (not-free $x term_a)))
        (check (= constant (Lam $x term_a)) (not-free $x term_a))
        (rewrite (Lam $x term_a) (Out term_a term_a) :when ((not-free $x term_a)))
        (run 1)
        (check (= constant (Out term_a term_a)))
        (fail (check (= identity (Out term_a term_a))))
    "#);
}

#[test]
fn checks_use_the_selected_aliasing_policy() {
    for no_aliasing in [false, true] {
        let mut compiler = Compiler::new(Options {
            no_aliasing,
            ..Default::default()
        });
        let mut graph = new_egraph();
        let source = format!(
            "{LANGUAGE}
             (union (G (VE $redundant) (N 0)) (N 0))
             (let seed (F (VE $a) (N 0)))
             (run 0)"
        );
        let encoded = compiler.compile(None, &source).unwrap();
        graph.parse_and_run_program(None, &encoded).unwrap();
        let check = "(check (F (VE $x) (G (VE $x) body)))";
        let check = if no_aliasing {
            format!("(fail {check})")
        } else {
            check.to_owned()
        };
        let encoded = compiler.compile(None, &check).unwrap();
        graph.parse_and_run_program(None, &encoded).unwrap();
    }
}

#[test]
fn globals_follow_leaders_in_checks_and_rewrites() {
    run(r#"
        (let a $a)
        (let b $b)
        (let older (G (VE b) (VE a)))
        (let fixed (F (VE a) (VE b)))
        (rewrite (F x y) (G y x))
        (run 1)
        (check (= fixed older))
        (check (= fixed (G (VE b) (VE a))))
        (fail (check (= fixed (G (VE a) (VE b)))))
        (let yes (Lam $bound (G (VE b) (VE a))))
        (let no (Lam $bound (G (VE a) (VE b))))
        (run 0)
        (check (= yes (Lam $query fixed)))
        (fail (check (= no (Lam $query fixed))))
        (rewrite (Lam $binder fixed) (Out (VE b) (VE a)))
        (run 1)
        (check (= yes (Out (VE b) (VE a))))
        (fail (check (= no (Out (VE b) (VE a)))))
    "#);
}

#[test]
fn checks_do_not_insert_terms_or_run_user_rules() {
    let mut compiler = Compiler::default();
    let mut graph = new_egraph();
    let init = compiler
        .compile(
            None,
            &format!(
                "{LANGUAGE}\n(let seed (F (VE $a) (VE $b))) (rewrite (F x y) (G y x)) (run 0)"
            ),
        )
        .unwrap();
    graph.parse_and_run_program(None, &init).unwrap();
    let before = graph.num_tuples();
    let checks = compiler
        .compile(
            None,
            "(check (F (VE $x) (VE $y))) (fail (check (G (VE $x) (VE $y)))) (fail (check (N 999)))",
        )
        .unwrap();
    graph.parse_and_run_program(None, &checks).unwrap();
    assert_eq!(before, graph.num_tuples());
}

#[test]
fn maintenance_is_automatic_without_applying_user_rewrites() {
    let mut compiler = Compiler::default();
    let mut graph = new_egraph();
    for source in [
        format!("{LANGUAGE} (rewrite (F x y) (G y x)) (let seed (F (VE $a) (VE $b)))"),
        "(check (F (VE $x) (VE $y))) (fail (check (G (VE $x) (VE $y))))".into(),
        "(union (N 1) (N 2)) (check (= (N 1) (N 2)))".into(),
        "(push) (let scoped (Lam $x (VE $x))) (check (free-names-are scoped)) (pop)".into(),
        "(check (F (VE $x) (VE $y))) (fail (check (G (VE $x) (VE $y)))) (run 1) (check (G (VE $x) (VE $y)))".into(),
    ] {
        let encoded = compiler.compile(None, &source).unwrap();
        graph.parse_and_run_program(None, &encoded).unwrap();
        egglog_experimental::slotted::export::export(&graph).unwrap();
    }
}
