//! Integration tests for value-producing `:merge` action blocks: a `:merge` may run actions
//! (`let`, `set`, `union`) before its result expression, with `old`/`new` bound. Syntax:
//! `:merge (<action>* <expr>)` (a bare `:merge <expr>` is the no-actions case).

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
fn merge_action_block_let_binding() {
    // A `let` binds an intermediate value that later actions and the result can reference.
    run(r#"
        (function discarded (i64) i64 :merge new)
        (function f (i64) i64
          :merge ((let smaller (min old new))
                  (let larger (max old new))
                  (set (discarded smaller) 1)
                  larger))
        (set (f 0) 5)
        (set (f 0) 3)
        (check (= (f 0) 5))          ; result is the `let`-bound larger value
        (check (= (discarded 3) 1))  ; the `set` used the `let`-bound smaller value
    "#)
    .unwrap();
}

#[test]
fn merge_action_block_union() {
    // A `union` action unifies the two conflicting eclasses of an eq-sort function.
    run(r#"
        (datatype Color (Red) (Green))
        (function pick (i64) Color :merge ((union old new) old))
        (set (pick 0) (Red))
        (set (pick 0) (Green))
        (check (= (Red) (Green)))
    "#)
    .unwrap();
}

#[test]
fn merge_action_block_let_in_tuple_merge() {
    // A `let` is in scope for a tuple-output `(values ...)` result too.
    run(r#"
        (function iv (i64) (i64 i64)
          :merge ((let lo (max old0 new0))
                  (values lo (min old1 new1))))
        (set (iv 0) (values 1 9))
        (set (iv 0) (values 4 2))
        (check (= (values 4 2) (iv 0)))  ; lo = max(1,4) = 4, hi = min(9,2) = 2
    "#)
    .unwrap();
}

#[test]
fn merge_action_block_rejects_unsupported_action() {
    // `set`/`let`/`union` are supported; other actions (here `panic`) are not meaningful during a
    // merge and are a clear error.
    let err = run(r#"(function g (i64) i64 :merge ((panic "boom") old))"#).unwrap_err();
    assert!(
        err.to_string().contains("not supported inside a :merge"),
        "expected an unsupported-action error, got: {err}"
    );
}
