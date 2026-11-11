//! Rigid names and carrier-specific variable constructors.
use egglog_experimental::slotted::{
    Compiler, Options, ProofMode, new_egraph, new_egraph_with_proofs,
};

#[test]
fn variable_equalities_do_not_cross_carriers() {
    let source = r#"
        (datatype A (VA Var) (Lam Var A :binder 0))
        (datatype B (VB Var))
        (let a $a)
        (let b $b)
        (let left (VB a))
        (let right (VB b))
        (union (VA a) (VA b))
        (check (= (VA a) (VA b)))
        (check (!= left right))
        (fail (check (= left right)))
        (let identity (Lam $bound (VA $bound)))
        (check (= identity (Lam $renamed (VA $renamed))))
    "#;
    check(source);
}

#[test]
fn invocation_merges_preserve_binders_after_support_shrinks() {
    for symmetry_first in [false, true] {
        let symmetry = "(union (Pair (V $a) (V $b)) (Pair (V $b) (V $a)))";
        let restriction = "(union (Pair (V $a) (V $b)) (Pair (V $a) (V $c)))";
        let unions = if symmetry_first {
            format!("{symmetry}\n{restriction}")
        } else {
            format!("{restriction}\n{symmetry}")
        };
        check_inputs(&[
            r#"
                (datatype Expr (V Var) (Pair Expr Expr) (Lam Var Expr :binder 0))
                (let term (Lam $bound (Pair (V $bound) (V $free))))
            "#,
            &unions,
            r#"
                (check (= term (Lam $renamed (Pair (V $renamed) (V $free)))))
                (extract term)
            "#,
        ]);
    }
}

fn check(source: &str) {
    check_inputs(&[source]);
}

fn check_inputs(sources: &[&str]) {
    for proof_mode in [ProofMode::Disabled, ProofMode::Prove] {
        let mut compiler = Compiler::new(Options {
            proof_mode,
            ..Options::default()
        });
        let mut graph = if proof_mode == ProofMode::Prove {
            new_egraph_with_proofs()
        } else {
            new_egraph()
        };
        for source in sources {
            let encoded = compiler.compile_program(None, source).unwrap();
            encoded.run(&mut graph).unwrap();
            if proof_mode == ProofMode::Disabled {
                egglog_experimental::slotted::export::export(&graph).unwrap();
            }
        }
    }
}

#[test]
fn binders_do_not_require_a_variable_constructor() {
    check(
        r#"
        (sort Empty)
        (datatype Expr (Num i64) (Lambda Var Expr :binder 0))
        (let term (Lambda $x (Num 1)))
        (check (= term (Lambda $y (Num 1))))
        (extract term)
        (rewrite (Lambda $bound body) body :when ((not-free $bound body)))
        (run 1)
        (check (= term (Num 1)))
    "#,
    );
}

#[test]
fn a_variable_constructor_can_be_added_later_and_is_scoped() {
    check_inputs(&[
        "(sort Expr)",
        "(constructor Num (i64) Expr) (constructor Lambda (Var Expr) Expr :binder 0)",
        "(push) (constructor Temporary (Var) Expr) (let t (Temporary $a)) (pop)",
        "(constructor Name (Var) Expr) (let id (Lambda $x (Name $x)))",
        "(check (= id (Lambda $y (Name $y)))) (extract id)",
    ]);
}

#[test]
fn a_second_variable_constructor_is_rejected_across_inputs() {
    let mut compiler = Compiler::default();
    compiler
        .compile_program(None, "(datatype Expr (Name Var))")
        .unwrap();
    let error = compiler
        .compile_program(None, "(constructor AnotherName (Var) Expr)")
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("already has variable constructor Name")
    );
}

#[test]
fn substitution_without_a_variable_constructor_preserves_closed_bodies() {
    let source = r#"
        (datatype Expr (Num i64) (Lambda Var Expr :binder 0) (App Expr Expr))
        (let call (App (Lambda $x (Lambda $y (Num 1))) (Num 2)))
        (rewrite (App (Lambda $x body) arg) (subst body $x arg))
        (run 1)
        (check (= call (Lambda $z (Num 1))))
    "#;
    let encoded = Compiler::default().compile_program(None, source).unwrap();
    encoded.run(&mut new_egraph()).unwrap();
}

#[test]
fn bare_names_cannot_be_used_as_carrier_equalities() {
    for command in [
        "(union $a $b)",
        "(rewrite $a $b)",
        "(rewrite (V $a) $b)",
        "(union (V $a) $b)",
        "(check (= (V $a) $b))",
    ] {
        let source = format!("(datatype Math (V Var)) {command}");
        assert!(
            Compiler::default().compile_program(None, &source).is_err(),
            "{command}"
        );
    }
}

#[test]
fn builtin_var_sort_name_is_reserved() {
    let error = Compiler::default()
        .compile_program(None, "(datatype Math (Var Var))")
        .unwrap_err();
    assert!(error.to_string().contains("reserved"));
}

#[test]
fn a_concrete_global_binder_keeps_its_name() {
    check(
        r#"
        (datatype Math (V Var) (Wrap Math) (Lam Var Math :binder 0))
        (let binder $a)
        (let input (Wrap (V binder)))
        (rewrite (Wrap e) (Lam binder e))
        (run 1)
        (check (= input (Lam $bound (V $bound))))
    "#,
    );
}
