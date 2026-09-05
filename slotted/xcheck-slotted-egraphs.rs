// Cross-check of the egglog slotted-encoding test corpus
// (egglog-slotted/slotted/tests/*.egg) against the reference
// slotted-egraphs implementation.
//
// Mapping:  (App2 "f" a b)                 ~  (f a b)
//           (App1 "neg" a)                 ~  (neg a)
//           (Var n)                        ~  (var $n)
//           (Null)                         ~  null
//           (App2 "lambda" (Var v) body)   ~  (lambda $v body)
//           (check (= $a $b))              ~  eg.eq(a, b)
//           (check (RenamesToLeader $a m1 l) (RenamesToLeader $b m2 l))
//                                          ~  same e-class id after find

#![allow(unused)]
#![allow(non_snake_case)]

use slotted_egraphs::*;

define_language! {
    pub enum U {
        Lam(Bind<AppliedId>) = "lambda",
        Var(Slot) = "var",
        F(AppliedId, AppliedId) = "f",
        G(AppliedId, AppliedId) = "g",
        H(AppliedId, AppliedId) = "h",
        I(AppliedId, AppliedId) = "i",
        K(AppliedId, AppliedId) = "k",
        P(AppliedId, AppliedId) = "p",
        A(AppliedId, AppliedId) = "a",
        C(AppliedId, AppliedId) = "c",
        T(AppliedId, AppliedId) = "t",
        Mul(AppliedId, AppliedId) = "mul",
        Pair(AppliedId, AppliedId) = "pair",
        App(AppliedId, AppliedId) = "app",
        Neg(AppliedId) = "neg",
        Swp(AppliedId, AppliedId) = "swp",
        Q(AppliedId, AppliedId) = "q",
        N2(AppliedId, AppliedId) = "n",
        Sym(Symbol),
    }
}

type EG = EGraph<U>;

fn add(eg: &mut EG, s: &str) -> AppliedId {
    eg.add_expr(RecExpr::parse(s).unwrap())
}

fn uni(eg: &mut EG, a: &str, b: &str) {
    let x = add(eg, a);
    let y = add(eg, b);
    eg.union(&x, &y);
}

fn sat(eg: &mut EG, rws: Vec<Rewrite<U>>) {
    run_eqsat(eg, rws, 30, 10, |_| Ok(()));
}

fn rw(name: &'static str, a: &'static str, b: &'static str) -> Rewrite<U> {
    Rewrite::new(name, a, b)
}

// (check (= $a $b))
fn eq(eg: &EG, a: &str, b: &str) -> bool {
    let x = eg.lookup_expr(a);
    let y = eg.lookup_expr(b);
    eg.eq(&x, &y)
}

// (check (RenamesToLeader $a _ l) (RenamesToLeader $b _ l))
fn same_class(eg: &EG, a: &str, b: &str) -> bool {
    let x = eg.lookup_expr(a);
    let y = eg.lookup_expr(b);
    eg.find_applied_id(&x).id == eg.find_applied_id(&y).id
}

trait Lookup {
    fn lookup_expr(&self, s: &str) -> AppliedId;
}
impl Lookup for EG {
    fn lookup_expr(&self, s: &str) -> AppliedId {
        lookup_rec_expr(&RecExpr::parse(s).unwrap(), self).expect(s)
    }
}

// 4. ground alpha-equivalence
#[test]
fn t4() {
    let g = &mut EG::default();
    add(g, "(f (var $20) (var $1))");
    add(g, "(f (var $7) (var $8))");
    add(g, "(f (var $20) (var $1))");
    assert!(eq(g, "(f (var $20) (var $1))", "(f (var $20) (var $1))"));
    assert!(!eq(g, "(f (var $20) (var $1))", "(f (var $7) (var $8))"));
    assert!(same_class(
        g,
        "(f (var $20) (var $1))",
        "(f (var $7) (var $8))"
    ));
}

// 5. commutativity symmetry reaches the parent
#[test]
fn t5() {
    let g = &mut EG::default();
    add(g, "(g (f (var $1) (var $2)) null)");
    add(g, "(g (f (var $2) (var $1)) null)");
    add(g, "(g (f (var $1) (var $3)) null)");
    sat(g, vec![rw("comm", "(f ?x ?y)", "(f ?y ?x)")]);
    assert!(eq(
        g,
        "(g (f (var $1) (var $2)) null)",
        "(g (f (var $2) (var $1)) null)"
    ));
    assert!(!eq(
        g,
        "(g (f (var $1) (var $2)) null)",
        "(g (f (var $1) (var $3)) null)"
    ));
}

// 6. child symmetry => parent symmetry
#[test]
fn t6() {
    let g = &mut EG::default();
    uni(g, "(c (var $0) (var $1))", "(c (var $1) (var $0))");
    add(g, "(i (c (var $0) (var $1)) null)");
    add(g, "(i (c (var $1) (var $0)) null)");
    add(g, "(i (c (var $0) (var $2)) null)");
    sat(g, vec![]);
    assert!(eq(
        g,
        "(i (c (var $0) (var $1)) null)",
        "(i (c (var $1) (var $0)) null)"
    ));
    assert!(!eq(
        g,
        "(i (c (var $0) (var $1)) null)",
        "(i (c (var $0) (var $2)) null)"
    ));
}

// 7. group closure: a 3-cycle generates its square, not the transposition
#[test]
fn t7() {
    let g = &mut EG::default();
    add(g, "(p (p (var $0) (var $1)) (var $2))");
    add(g, "(p (p (var $1) (var $2)) (var $0))");
    add(g, "(p (p (var $2) (var $0)) (var $1))");
    add(g, "(p (p (var $1) (var $0)) (var $2))");
    uni(
        g,
        "(p (p (var $0) (var $1)) (var $2))",
        "(p (p (var $1) (var $2)) (var $0))",
    );
    sat(g, vec![]);
    assert!(eq(
        g,
        "(p (p (var $0) (var $1)) (var $2))",
        "(p (p (var $2) (var $0)) (var $1))"
    ));
    assert!(!eq(
        g,
        "(p (p (var $0) (var $1)) (var $2))",
        "(p (p (var $1) (var $0)) (var $2))"
    ));
}

// 8. redundancy from a union (paper Fig. 3)
#[test]
fn t8() {
    let g = &mut EG::default();
    uni(g, "(mul (var $7) null)", "null");
    add(g, "(mul (var $9) null)");
    add(g, "(mul (var $9) (var $7))");
    sat(g, vec![]);
    assert!(eq(g, "(mul (var $9) null)", "null"));
    assert!(eq(g, "(mul (var $7) null)", "(mul (var $9) null)"));
    assert!(!eq(g, "(mul (var $9) (var $7))", "null"));
}

// 9. redundancy from a rewrite, propagated into the parent
#[test]
fn t9() {
    let g = &mut EG::default();
    add(g, "(f (mul (var $7) null) (var $8))");
    add(g, "(f (mul (var $9) null) (var $8))");
    add(g, "(f null (var $8))");
    add(g, "(f (mul (var $7) null) (var $3))");
    sat(g, vec![rw("mul0", "(mul ?x null)", "null")]);
    assert!(eq(
        g,
        "(f (mul (var $7) null) (var $8))",
        "(f (mul (var $9) null) (var $8))"
    ));
    assert!(eq(g, "(f (mul (var $7) null) (var $8))", "(f null (var $8))"));
    assert!(!eq(
        g,
        "(f (mul (var $7) null) (var $8))",
        "(f (mul (var $7) null) (var $3))"
    ));
}

// 10. redundancy closed under the permutation group's orbits.
// NOTE: the .egg test does the symmetry union first; in that order slotted-egraphs
// panics ("SlotMap::index($f1): index missing!", src/group/mod.rs:167).  Unions are
// order-independent semantically, so the reference answer is taken from the other
// order, which the crate handles: the merged class ends up with no slots at all.
#[test]
fn t10() {
    let g = &mut EG::default();
    uni(g, "(f (var $0) (var $1))", "(g (var $0) null)");
    uni(g, "(f (var $0) (var $1))", "(f (var $1) (var $0))");
    add(g, "(g (var $5) null)");
    add(g, "(f (var $7) (var $8))");
    add(g, "null");
    sat(g, vec![]);
    assert!(eq(g, "(g (var $0) null)", "(g (var $5) null)"));
    assert!(eq(g, "(f (var $0) (var $1))", "(f (var $7) (var $8))"));
    assert!(!eq(g, "(f (var $0) (var $1))", "null"));
}

// 11. shifted slot sets make every slot redundant
#[test]
fn t11() {
    let g = &mut EG::default();
    uni(g, "(f (var $0) (var $1))", "(f (var $1) (var $2))");
    add(g, "(f (var $7) (var $8))");
    add(g, "null");
    sat(g, vec![]);
    assert!(eq(g, "(f (var $0) (var $1))", "(f (var $7) (var $8))"));
    assert!(!eq(g, "(f (var $0) (var $1))", "null"));
}

// 12. union chain with composed renamings
#[test]
fn t12() {
    let g = &mut EG::default();
    uni(g, "(f (var $1) (var $2))", "(g (var $2) (var $1))");
    uni(g, "(g (var $3) (var $4))", "(h (var $3) (var $4))");
    add(g, "(f (var $4) (var $3))");
    add(g, "(h (var $4) (var $3))");
    sat(g, vec![]);
    assert!(eq(g, "(f (var $4) (var $3))", "(h (var $3) (var $4))"));
    assert!(!eq(g, "(f (var $4) (var $3))", "(h (var $4) (var $3))"));
}

// 13. two merges of one pair generate a symmetry, which reaches the parent
#[test]
fn t13() {
    let g = &mut EG::default();
    uni(g, "(f (var $1) (var $2))", "(g (var $1) (var $2))");
    uni(g, "(f (var $1) (var $2))", "(g (var $2) (var $1))");
    add(g, "(f (var $2) (var $1))");
    add(g, "(f (var $1) (var $3))");
    add(g, "(h (f (var $1) (var $2)) null)");
    add(g, "(h (f (var $2) (var $1)) null)");
    sat(g, vec![]);
    assert!(eq(g, "(f (var $1) (var $2))", "(f (var $2) (var $1))"));
    assert!(eq(g, "(g (var $1) (var $2))", "(g (var $2) (var $1))"));
    assert!(eq(
        g,
        "(h (f (var $1) (var $2)) null)",
        "(h (f (var $2) (var $1)) null)"
    ));
    assert!(!eq(g, "(f (var $1) (var $2))", "(f (var $1) (var $3))"));
}

// 14. injectivity: k($5,$5) is not k($5,$6), not even up to renaming
#[test]
fn t14() {
    let g = &mut EG::default();
    add(g, "(k (var $5) (var $5))");
    add(g, "(k (var $5) (var $6))");
    sat(g, vec![]);
    assert!(!eq(g, "(k (var $5) (var $5))", "(k (var $5) (var $6))"));
    assert!(!same_class(
        g,
        "(k (var $5) (var $5))",
        "(k (var $5) (var $6))"
    ));
}

// 15. repeated pattern variable matches up to a symmetry of the child
#[test]
fn t15() {
    let g = &mut EG::default();
    uni(g, "(a (var $0) (var $1))", "(a (var $1) (var $0))");
    add(g, "(f (a (var $0) (var $1)) (a (var $1) (var $0)))");
    add(g, "(f (a (var $0) (var $1)) (a (var $0) (var $2)))");
    sat(g, vec![rw("dup", "(f ?x ?x)", "?x")]);
    assert!(eq(
        g,
        "(f (a (var $0) (var $1)) (a (var $1) (var $0)))",
        "(a (var $0) (var $1))"
    ));
    assert!(!eq(
        g,
        "(f (a (var $0) (var $1)) (a (var $0) (var $2)))",
        "(a (var $0) (var $1))"
    ));
}

// 16. ... and not without that symmetry
#[test]
fn t16() {
    let g = &mut EG::default();
    add(g, "(a (var $0) (var $1))");
    add(g, "(f (a (var $0) (var $1)) (a (var $1) (var $0)))");
    add(g, "(f (a (var $0) (var $1)) (a (var $0) (var $1)))");
    sat(g, vec![rw("dup", "(f ?x ?x)", "?x")]);
    assert!(eq(
        g,
        "(f (a (var $0) (var $1)) (a (var $0) (var $1)))",
        "(a (var $0) (var $1))"
    ));
    assert!(!eq(
        g,
        "(f (a (var $0) (var $1)) (a (var $1) (var $0)))",
        "(a (var $0) (var $1))"
    ));
}

// 17. three occurrences of one variable at three depths
#[test]
fn t17() {
    let g = &mut EG::default();
    uni(g, "(a (var $0) (var $1))", "(a (var $1) (var $0))");
    add(
        g,
        "(t (a (var $0) (var $1)) (t (a (var $1) (var $0)) (a (var $0) (var $1))))",
    );
    add(
        g,
        "(t (a (var $0) (var $1)) (t (a (var $1) (var $0)) (a (var $0) (var $2))))",
    );
    sat(g, vec![rw("tdup", "(t ?x (t ?x ?x))", "?x")]);
    assert!(eq(
        g,
        "(t (a (var $0) (var $1)) (t (a (var $1) (var $0)) (a (var $0) (var $1))))",
        "(a (var $0) (var $1))"
    ));
    assert!(!eq(
        g,
        "(t (a (var $0) (var $1)) (t (a (var $1) (var $0)) (a (var $0) (var $2))))",
        "(a (var $0) (var $1))"
    ));
}

// 18. rotation: renamings composed down and back up the pattern
#[test]
fn t18() {
    let g = &mut EG::default();
    add(g, "(f (g (var $1) (var $2)) (var $3))");
    add(g, "(g (var $1) (f (var $2) (var $3)))");
    add(g, "(f (g (var $5) (var $5)) (var $6))");
    add(g, "(g (var $5) (f (var $5) (var $6)))");
    add(g, "(g (var $2) (f (var $1) (var $3)))");
    sat(g, vec![rw("rot", "(f (g ?x ?y) ?z)", "(g ?x (f ?y ?z))")]);
    assert!(eq(
        g,
        "(f (g (var $1) (var $2)) (var $3))",
        "(g (var $1) (f (var $2) (var $3)))"
    ));
    assert!(eq(
        g,
        "(f (g (var $5) (var $5)) (var $6))",
        "(g (var $5) (f (var $5) (var $6)))"
    ));
    assert!(!eq(
        g,
        "(f (g (var $1) (var $2)) (var $3))",
        "(g (var $2) (f (var $1) (var $3)))"
    ));
}

// 19. lambda alpha-equivalence
#[test]
fn t19() {
    let g = &mut EG::default();
    add(g, "(lambda $0 (var $0))");
    add(g, "(lambda $5 (var $5))");
    add(g, "(lambda $0 (var $3))");
    add(g, "(lambda $5 (var $3))");
    add(g, "(lambda $0 (var $4))");
    sat(g, vec![]);
    assert!(eq(g, "(lambda $0 (var $0))", "(lambda $5 (var $5))"));
    assert!(eq(g, "(lambda $0 (var $3))", "(lambda $5 (var $3))"));
    assert!(!eq(g, "(lambda $0 (var $3))", "(lambda $0 (var $4))"));
    assert!(same_class(
        g,
        "(lambda $0 (var $3))",
        "(lambda $0 (var $4))"
    ));
    assert!(!eq(g, "(lambda $0 (var $0))", "(lambda $0 (var $3))"));
}

// 20. nested binders and capture avoidance
#[test]
fn t20() {
    let g = &mut EG::default();
    add(g, "(lambda $0 (lambda $1 (f (var $0) (var $1))))");
    add(g, "(lambda $7 (lambda $8 (f (var $7) (var $8))))");
    add(g, "(lambda $0 (lambda $1 (f (var $1) (var $0))))");
    add(g, "(lambda $0 (f (var $0) (var $3)))");
    add(g, "(lambda $3 (f (var $3) (var $0)))");
    sat(g, vec![]);
    assert!(eq(
        g,
        "(lambda $0 (lambda $1 (f (var $0) (var $1))))",
        "(lambda $7 (lambda $8 (f (var $7) (var $8))))"
    ));
    assert!(!eq(
        g,
        "(lambda $0 (lambda $1 (f (var $0) (var $1))))",
        "(lambda $0 (lambda $1 (f (var $1) (var $0))))"
    ));
    assert!(!eq(
        g,
        "(lambda $0 (f (var $0) (var $3)))",
        "(lambda $3 (f (var $3) (var $0)))"
    ));
    assert!(same_class(
        g,
        "(lambda $0 (f (var $0) (var $3)))",
        "(lambda $3 (f (var $3) (var $0)))"
    ));
}

// 21. rewriting under a binder, and losing the bound slot under a binder
#[test]
fn t21() {
    let g = &mut EG::default();
    add(g, "(lambda $0 (f (var $0) (var $3)))");
    add(g, "(lambda $0 (f (var $3) (var $0)))");
    add(g, "(lambda $7 (f (var $3) (var $7)))");
    add(g, "(lambda $0 (mul (var $0) null))");
    add(g, "(lambda $0 null)");
    add(g, "null");
    sat(
        g,
        vec![
            rw("comm", "(f ?x ?y)", "(f ?y ?x)"),
            rw("mul0", "(mul ?x null)", "null"),
        ],
    );
    assert!(eq(
        g,
        "(lambda $0 (f (var $0) (var $3)))",
        "(lambda $0 (f (var $3) (var $0)))"
    ));
    assert!(eq(
        g,
        "(lambda $0 (f (var $0) (var $3)))",
        "(lambda $7 (f (var $3) (var $7)))"
    ));
    assert!(eq(g, "(lambda $0 (mul (var $0) null))", "(lambda $0 null)"));
    assert!(!eq(g, "(lambda $0 (mul (var $0) null))", "null"));
}

// 22. a rule whose pattern is a binder
#[test]
fn t22() {
    let g = &mut EG::default();
    add(g, "(lambda $0 (pair (f (var $0) (var $3)) (var $4)))");
    add(
        g,
        "(pair (lambda $0 (f (var $0) (var $3))) (lambda $5 (var $4)))",
    );
    add(
        g,
        "(pair (lambda $0 (f (var $3) (var $0))) (lambda $5 (var $4)))",
    );
    sat(
        g,
        vec![rw(
            "push",
            "(lambda $v (pair ?a ?b))",
            "(pair (lambda $v ?a) (lambda $v ?b))",
        )],
    );
    assert!(eq(
        g,
        "(lambda $0 (pair (f (var $0) (var $3)) (var $4)))",
        "(pair (lambda $0 (f (var $0) (var $3))) (lambda $5 (var $4)))"
    ));
    assert!(!eq(
        g,
        "(lambda $0 (pair (f (var $0) (var $3)) (var $4)))",
        "(pair (lambda $0 (f (var $3) (var $0))) (lambda $5 (var $4)))"
    ));
}

// 23. eta
#[test]
fn t23() {
    let g = &mut EG::default();
    add(g, "(lambda $0 (app null (var $0)))");
    add(g, "null");
    add(g, "(lambda $7 (app (g (var $2) null) (var $7)))");
    add(g, "(g (var $2) null)");
    add(g, "(lambda $7 (app null (var $2)))");
    sat(
        g,
        vec![rw("eta", "(lambda $v (app ?f (var $v)))", "?f")],
    );
    assert!(eq(g, "(lambda $0 (app null (var $0)))", "null"));
    assert!(eq(
        g,
        "(lambda $7 (app (g (var $2) null) (var $7)))",
        "(g (var $2) null)"
    ));
    assert!(!eq(g, "(lambda $7 (app null (var $2)))", "null"));
}

// 24. unary constructor
#[test]
fn t24() {
    let g = &mut EG::default();
    add(g, "(neg (var $3))");
    add(g, "(neg (var $4))");
    add(g, "(neg (neg (var $3)))");
    add(g, "(var $3)");
    add(g, "(neg (neg (var $4)))");
    sat(g, vec![rw("negneg", "(neg (neg ?x))", "?x")]);
    assert!(!eq(g, "(neg (var $3))", "(neg (var $4))"));
    assert!(same_class(g, "(neg (var $3))", "(neg (var $4))"));
    assert!(eq(g, "(neg (neg (var $3)))", "(var $3)"));
    assert!(!eq(g, "(neg (neg (var $3)))", "(neg (neg (var $4)))"));
}

// 27. the conclusion the fresh-slot rule should reach -- unioning f($0,$1) with
// h($1,$5) may make f's $0 redundant, but must not touch the variable class, so
// k($5) and k($6) stay apart.
#[test]
fn t27_conclusion() {
    let g = &mut EG::default();
    uni(g, "(f (var $0) (var $1))", "(h (var $1) (var $5))");
    add(g, "(k (var $5) null)");
    add(g, "(k (var $6) null)");
    sat(g, vec![]);
    assert!(!eq(g, "(k (var $5) null)", "(k (var $6) null)"));
}

// 25. slot variables in a pattern
#[test]
fn t25() {
    let g = &mut EG::default();
    add(g, "(f (var $1) (var $2))");
    add(g, "(f (var $2) (var $1))");
    add(g, "(f (g (var $1) null) (var $2))");
    add(g, "(f (var $2) (g (var $1) null))");
    sat(
        g,
        vec![rw(
            "swapvars",
            "(f (var $s) (var $t))",
            "(f (var $t) (var $s))",
        )],
    );
    assert!(eq(g, "(f (var $1) (var $2))", "(f (var $2) (var $1))"));
    assert!(!eq(
        g,
        "(f (g (var $1) null) (var $2))",
        "(f (var $2) (g (var $1) null))"
    ));
}

// 32. redundancy on the leaf class itself
#[test]
fn t32() {
    let g = &mut EG::default();
    uni(g, "(var $0)", "(var $7)");
    add(g, "(f (var $0) null)");
    add(g, "(f (var $7) null)");
    add(g, "(f (var $9) null)");
    add(g, "null");
    sat(g, vec![]);
    assert!(eq(g, "(var $0)", "(var $7)"));
    assert!(eq(g, "(f (var $0) null)", "(f (var $7) null)"));
    assert!(eq(g, "(f (var $0) null)", "(f (var $9) null)"));
    assert!(!eq(g, "(f (var $0) null)", "null"));
}

// 33. matching a class with two redundant slots (Def. 8 fresh slots)
#[test]
fn t33() {
    let g = &mut EG::default();
    uni(g, "(mul (var $7) (var $8))", "null");
    add(g, "(swp (var $1) (var $2))");
    add(g, "(swp (var $2) (var $1))");
    add(g, "(k (var $1) (var $2))");
    sat(g, vec![rw("comm", "(mul ?x ?y)", "(swp ?y ?x)")]);
    assert!(eq(g, "(swp (var $1) (var $2))", "null"));
    assert!(eq(g, "(swp (var $1) (var $2))", "(swp (var $2) (var $1))"));
    assert!(!eq(g, "(k (var $1) (var $2))", "null"));
}

// 11-extra. a parent of a slotless class must lose those slots
#[test]
fn t11_parent() {
    let g = &mut EG::default();
    uni(g, "(f (var $0) (var $1))", "(f (var $1) (var $2))");
    add(g, "(q (f (var $0) (var $1)) (var $5))");
    add(g, "(q (f (var $2) (var $3)) (var $5))");
    add(g, "(q (f (var $0) (var $1)) (var $6))");
    sat(g, vec![]);
    assert!(eq(g, "(q (f (var $0) (var $1)) (var $5))", "(q (f (var $2) (var $3)) (var $5))"));
    assert!(!eq(g, "(q (f (var $0) (var $1)) (var $5))", "(q (f (var $0) (var $1)) (var $6))"));
}

// 6-extra. one symmetric child at two positions, invoked differently
#[test]
fn t6_two_positions() {
    let g = &mut EG::default();
    uni(g, "(c (var $0) (var $1))", "(c (var $1) (var $0))");
    add(g, "(n (c (var $0) (var $1)) (c (var $0) (var $1)))");
    add(g, "(n (c (var $0) (var $1)) (c (var $1) (var $0)))");
    add(g, "(n (c (var $1) (var $0)) (c (var $0) (var $1)))");
    sat(g, vec![]);
    assert!(eq(g, "(n (c (var $0) (var $1)) (c (var $0) (var $1)))",
                  "(n (c (var $0) (var $1)) (c (var $1) (var $0)))"));
    assert!(eq(g, "(n (c (var $0) (var $1)) (c (var $0) (var $1)))",
                  "(n (c (var $1) (var $0)) (c (var $0) (var $1)))"));
}
