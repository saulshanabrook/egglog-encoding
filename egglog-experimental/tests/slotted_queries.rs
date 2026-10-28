//! Public checks and rewrite guards share existential query semantics.
use egglog_experimental::slotted::{Compiler, Options, new_egraph};

const LANGUAGE: &str = "(datatype E (N i64) (F E E) (G E E) (Out E E) (Lam E E :binder 0) (Hit))";

fn run(source: &str) {
    for no_aliasing in [false, true] {
        let program = Compiler::new(Options { no_aliasing })
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
        (let seed (F a b))
        (run 0)
        (check (F $x $y))
        (check (= a $s))
        (check (= b $s))
        (check (= a alias))
        (check (!= a b))
        (fail (check (= a b)))
        (check (= a $x) (= b $y) (!= $x $y))
        (fail (check (= a $x) (= b $x)))
        (check (= seed (F a b)))
        (fail (check (= seed (F b a))))
    "#);
}

#[test]
fn guards_share_the_patterns_slot_assignment() {
    run(r#"
        (let a $a)
        (let b $b)
        (let shared (F a a))
        (let separate (F a b))
        (run 0)
        (check (= shared (F $x body)) (free $x body))
        (check (= separate (F $x body)) (not-free $x body))
        (fail (check (= shared (F $x body)) (not-free $x body)))
        (fail (check (= separate (F $x body)) (free $x body)))
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
        (let forward (F a b))
        (let backward (F b a))
        (union forward backward)
        (run 0)
        (check (= forward backward))
        (check (= x forward) (= x backward))
        (check (= x forward) (= x (F b a)))
        (union (G $a $b) (N 0))
        (let redundant (G a b))
        (run 0)
        (check (= redundant (G $x $y)))
        (check (free-names-are redundant))
    "#);
}

#[test]
fn a_guard_excludes_capture_of_a_concrete_global() {
    run(r#"
        (let a $a)
        (let identity (Lam $bound $bound))
        (let constant (Lam $bound a))
        (run 0)
        (check (= identity (Lam $x a)))
        (fail (check (= identity (Lam $x a)) (not-free $x a)))
        (check (= constant (Lam $x a)) (not-free $x a))
        (rewrite (Lam $x a) (Out a a) :when ((not-free $x a)))
        (run 1)
        (check (= constant (Out a a)))
        (fail (check (= identity (Out a a))))
    "#);
}

#[test]
fn checks_use_the_selected_aliasing_policy() {
    for no_aliasing in [false, true] {
        let mut compiler = Compiler::new(Options { no_aliasing });
        let mut graph = new_egraph();
        let source = format!(
            "{LANGUAGE}
             (union (G $redundant (N 0)) (N 0))
             (let seed (F $a (N 0)))
             (run 0)"
        );
        let encoded = compiler.compile(None, &source).unwrap();
        graph.parse_and_run_program(None, &encoded).unwrap();
        let check = "(check (F $x (G $x body)))";
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
        (let older (G b a))
        (let fixed (F a b))
        (rewrite (F x y) (G y x))
        (run 1)
        (check (= fixed older))
        (check (= fixed (G b a)))
        (fail (check (= fixed (G a b))))
        (let yes (Lam $bound (G b a)))
        (let no (Lam $bound (G a b)))
        (run 0)
        (check (= yes (Lam $query fixed)))
        (fail (check (= no (Lam $query fixed))))
        (rewrite (Lam $binder fixed) (Out b a))
        (run 1)
        (check (= yes (Out b a)))
        (fail (check (= no (Out b a))))
    "#);
}

#[test]
fn checks_do_not_insert_terms_or_run_user_rules() {
    let mut compiler = Compiler::default();
    let mut graph = new_egraph();
    let init = compiler
        .compile(
            None,
            &format!("{LANGUAGE}\n(let seed (F $a $b)) (rewrite (F x y) (G y x)) (run 0)"),
        )
        .unwrap();
    graph.parse_and_run_program(None, &init).unwrap();
    let before = graph.num_tuples();
    let checks = compiler
        .compile(
            None,
            "(check (F $x $y)) (fail (check (G $x $y))) (fail (check (N 999)))",
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
        format!("{LANGUAGE} (rewrite (F x y) (G y x)) (let seed (F $a $b))"),
        "(check (F $x $y)) (fail (check (G $x $y)))".into(),
        "(union (N 1) (N 2)) (check (= (N 1) (N 2)))".into(),
        "(push) (let scoped (Lam $x $x)) (check (free-names-are scoped)) (pop)".into(),
        "(check (F $x $y)) (fail (check (G $x $y))) (run 1) (check (G $x $y))".into(),
    ] {
        let encoded = compiler.compile(None, &source).unwrap();
        graph.parse_and_run_program(None, &encoded).unwrap();
        egglog_experimental::slotted::export::export(&graph).unwrap();
    }
}
