//! Tests for the `slotted-subst` primitive.
//!
//! The encoding here is the smallest one that exercises it: a `Renaming` sort,
//! a class sort `U`, the normalised variable `(Var 0)`, and constructors whose
//! children each occupy a `Renaming` column followed by a `U` column. The full
//! slotted encoding's invariant rules are not needed -- the primitive reads
//! e-node rows, not `RenamesToLeader`.

use egglog::Error;
use egglog::prelude::*;

/// A binary node `H`, a payload-carrying unary node `Lbl`, and the two nodes a
/// beta step needs.
const SLOTTED: &str = "
(sort Renaming (Map i64 i64))
(sort U)
(constructor Var (i64) U)
(constructor Null () U)
(constructor H (Renaming U Renaming U) U)
(constructor Lbl (String Renaming U) U)
(constructor Lam (Renaming U Renaming U) U)
(constructor App (Renaming U Renaming U) U)
";

fn egraph(program: &str) -> Result<EGraph, Error> {
    let mut egraph = EGraph::default();
    egraph.parse_and_run_program(None, &format!("{SLOTTED}\n{program}"))?;
    Ok(egraph)
}

fn row_count(egraph: &mut EGraph, table: &str) -> usize {
    let mut count = 0;
    egraph
        .constructor_enodes(table, |_| count += 1)
        .expect("table exists");
    count
}

/// `h(var $0, var $1)[$0 := null]` is `h(null, var $1)`.
#[test]
fn substitutes_an_occurring_slot() -> Result<(), Error> {
    let mut egraph = egraph(
        "
(let $body (H (map-of 0 0) (Var 0) (map-of 0 1) (Var 0)))
(let $out (slotted-subst $body 0 (Var 0) (map-empty) (Null)))
(check (= $out (H (map-empty) (Null) (map-of 0 1) (Var 0))))
(fail (check (= $out $body)))
",
    )?;
    // The rebuilt node is the only one added.
    assert_eq!(row_count(&mut egraph, "H"), 2);
    Ok(())
}

/// A slot `body` does not name cannot occur in it, so `body` comes back as it
/// is and no row is added.
#[test]
fn a_slot_that_does_not_occur_is_a_no_op() -> Result<(), Error> {
    let mut egraph = egraph(
        "
(let $body (H (map-of 0 1) (Var 0) (map-of 0 2) (Var 0)))
(let $out (slotted-subst $body 0 (Var 0) (map-empty) (Null)))
(check (= $out $body))
",
    )?;
    assert_eq!(row_count(&mut egraph, "H"), 1);
    Ok(())
}

/// The occurrence is two levels down, and the subterms that cannot mention the
/// slot are shared rather than copied.
#[test]
fn substitutes_a_nested_occurrence() -> Result<(), Error> {
    let mut egraph = egraph(
        "
(let $inner (H (map-of 0 0) (Var 0) (map-of 0 1) (Var 0)))
(let $mid   (Lbl \"f\" (map-of 0 0 1 1) $inner))
(let $body  (H (map-of 0 0 1 1) $mid (map-of 0 2) (Var 0)))
(let $out (slotted-subst $body 0 (Var 0) (map-empty) (Null)))
(check (= $out
          (H (map-of 1 1)
             (Lbl \"f\" (map-of 1 1) (H (map-empty) (Null) (map-of 0 1) (Var 0)))
             (map-of 0 2) (Var 0))))
",
    )?;
    // `(Var 0)` at slot 2 is shared, so only the spine is rebuilt: two `H`
    // rows added, one `Lbl` row added.
    assert_eq!(row_count(&mut egraph, "H"), 4);
    assert_eq!(row_count(&mut egraph, "Lbl"), 2);
    Ok(())
}

/// A node may carry a slot its class does not. Carrying the frame change
/// through such an edge with `compose` would drop it; the slot has to survive.
#[test]
fn a_redundant_node_slot_survives_the_frame_change() -> Result<(), Error> {
    let mut egraph = egraph(
        "
;; `$c`'s node names slots {0, 7}...
(let $c (H (map-of 0 0) (Var 0) (map-of 0 7) (Var 0)))
;; ...while the edge reaching it says its class has only slot 0, so 7 is
;; redundant and outside the frame the substitution carries in.
(let $body (H (map-of 0 5) $c (map-of 0 6) (Var 0)))
(let $out (slotted-subst $body 5 (Var 0) (map-empty) (Null)))
(check (= x (H (map-empty) (Null) (map-of 0 7) (Var 0))))
(fail (check (= x (H (map-empty) (Null) (map-empty) (Var 0)))))
",
    )?;
    // The result keeps the redundant slot, so the outer edge names it.
    egraph.parse_and_run_program(
        None,
        "(check (= $out (H (map-of 7 7)
                          (H (map-empty) (Null) (map-of 0 7) (Var 0))
                          (map-of 0 6) (Var 0))))",
    )?;
    Ok(())
}

/// A class whose only e-node refers back to itself has no finite term, so the
/// primitive declines instead of walking the cycle forever.
///
/// A partial primitive that declines inside an action is a program error in
/// egglog -- an action has no "does not fire" -- so what this asserts is that
/// the call comes back at all, with that error.
#[test]
fn a_class_with_no_finite_term_declines() {
    let Err(err) = egraph(
        "
(let $ground (H (map-of 0 0) (Var 0) (map-empty) (Null)))
(let $cyclic (H (map-of 0 0) $ground (map-empty) (Null)))
(union $ground $cyclic)
;; only the self-referential node is left in the class
(delete (H (map-of 0 0) (Var 0) (map-empty) (Null)))

(let $out (slotted-subst $cyclic 0 (Var 0) (map-empty) (Null)))
",
    ) else {
        panic!("a class with no finite term cannot be substituted into")
    };
    assert!(
        err.to_string().contains("slotted-subst"),
        "unexpected error: {err}"
    );
}

/// The same shape with the grounding e-node left in place: extraction picks it
/// over the self-referential one, so the substitution goes through.
#[test]
fn a_cyclic_class_uses_its_grounded_enode() -> Result<(), Error> {
    egraph(
        "
(let $ground (H (map-of 0 0) (Var 0) (map-empty) (Null)))
(let $cyclic (H (map-of 0 0) $ground (map-empty) (Null)))
(union $ground $cyclic)

(let $out (slotted-subst $cyclic 0 (Var 0) (map-empty) (Null)))
(check (= $out (H (map-empty) (Null) (map-empty) (Null))))
",
    )?;
    Ok(())
}

/// A beta step from a `:naive` rule: `(App (Lam $0 h($0, $1)) null)` becomes
/// `h(null, $1)`. Every renaming here is an identity on the slots it covers, so
/// the lambda's frame, its body's frame and the application's frame agree and
/// the result can be unioned into the application directly.
#[test]
fn a_naive_rule_performs_a_beta_step() -> Result<(), Error> {
    egraph(
        "
(let $body (H (map-of 0 0) (Var 0) (map-of 0 1) (Var 0)))
(let $lam (Lam (map-of 0 0) (Var 0) (map-of 0 0 1 1) $body))
(let $redex (App (map-of 1 1) $lam (map-empty) (Null)))

(rule ((= e (App ml l mt t))
       (= l (Lam mx (Var 0) mb bod))
       (= x (map-get mx 0)))
      ((union e (slotted-subst bod x (Var 0) mt t)))
      :naive)
(run 1)

(check (= $redex (H (map-empty) (Null) (map-of 0 1) (Var 0))))
",
    )?;
    Ok(())
}

/// A payload column takes part in the node's identity and carries no slots, so
/// it is copied through unchanged.
#[test]
fn a_payload_column_is_copied_through() -> Result<(), Error> {
    egraph(
        "
(let $body (Lbl \"f\" (map-of 0 3) (Var 0)))
(let $out (slotted-subst $body 3 (Var 0) (map-of 0 9) (Var 0)))
(check (= $out (Lbl \"f\" (map-of 0 9) (Var 0))))
",
    )?;
    Ok(())
}

/// `slotted-subst-frame` answers the renaming placing the result in `body`'s
/// frame. Without it the two shortcut cases below are unreadable: each returns a
/// class that already existed, and only the renaming says where it sits.
#[test]
fn slotted_subst_frame_places_the_result_in_the_bodys_frame() -> Result<(), Error> {
    // Both halves read the database, so both are callable only from an action:
    // bind the answer with `let`, then compare it in a `check`.

    // A rebuilt root is spelled in the ambient frame, so its renaming is the
    // identity on the slots that survive: $0 is substituted away, $1 remains.
    egraph(
        "
(let $body (H (map-of 0 0) (Var 0) (map-of 0 1) (Var 0)))
(let $fr (slotted-subst-frame $body 0 (Var 0) (map-empty) (Null)))
(check (= $fr (map-of 1 1)))
",
    )?;

    // A body that cannot name the slot comes back as itself, under the renaming
    // it was reached by -- here the identity on its own two slots.
    egraph(
        "
(let $body (H (map-of 0 2) (Var 0) (map-of 0 3) (Var 0)))
(let $out (slotted-subst $body 0 (Var 0) (map-empty) (Null)))
(let $fr (slotted-subst-frame $body 0 (Var 0) (map-empty) (Null)))
(check (= $out $body))
(check (= $fr (map-of 2 2 3 3)))
",
    )?;

    // Substituting into the variable itself gives `t` under `t_ren`. The class is
    // `(Var 0)` whatever `t_ren` is, so the renaming carries all the information.
    // `(Var 0)` is bound by an earlier command so that its row is on the table
    // by the time the substitution reads it.
    egraph(
        "
(let $v (Var 0))
(let $out (slotted-subst $v 0 $v (map-of 0 7) $v))
(let $fr (slotted-subst-frame $v 0 $v (map-of 0 7) $v))
(check (= $out $v))
(check (= $fr (map-of 0 7)))
(fail (check (= $fr (map-of 0 0))))
",
    )?;
    Ok(())
}
