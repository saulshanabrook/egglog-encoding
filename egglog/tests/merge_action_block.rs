//! Integration tests for value-producing `:merge` action blocks: a `:merge` may run actions (e.g.
//! `set`) before its result expression, with `old`/`new` bound. Syntax: `:merge (<action>* <expr>)`
//! (a bare `:merge <expr>` is the no-actions case).

use egglog::EGraph;

fn run(prog: &str) -> Result<(), egglog::Error> {
    EGraph::default()
        .parse_and_run_program(None, prog)
        .map(|_| ())
}

#[test]
fn merge_action_block_runs_effect_and_returns_value() {
    // On a conflict `f`'s merge records the discarded (smaller) value into `discarded`, then keeps
    // the larger value. Asserts both the side effect and the merged result.
    run(r#"
        (function discarded (i64) i64 :merge new)
        (function f (i64) i64 :merge ((set (discarded (min old new)) 1) (max old new)))
        (set (f 0) 5)
        (set (f 0) 3)
        (check (= (f 0) 5))          ; result kept the larger value
        (check (= (discarded 3) 1))  ; the action recorded the discarded (smaller) value
        (fail (check (= (discarded 5) 1)))
    "#)
    .unwrap();
}

#[test]
fn merge_action_block_plain_expr_still_works() {
    // A bare `:merge <expr>` (no actions) is unchanged.
    run(r#"
        (function g (i64) i64 :merge (max old new))
        (set (g 0) 2)
        (set (g 0) 7)
        (check (= (g 0) 7))
    "#)
    .unwrap();
}

#[test]
fn merge_action_block_rejects_unsupported_action() {
    // Only `set` actions are lowered for now; other actions (here `let`) are a clear error until
    // the merge-as-actions interpreter lands.
    let err = run("(function g (i64) i64 :merge ((let x (+ old new)) old))").unwrap_err();
    assert!(
        err.to_string()
            .contains("not yet supported inside a :merge"),
        "expected an unsupported-action error, got: {err}"
    );
}
