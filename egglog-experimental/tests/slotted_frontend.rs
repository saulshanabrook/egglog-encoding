//! Source grammar acceptance, diagnostics, and deterministic lowering.
use egglog_experimental::slotted::{Compiler, new_egraph};

fn evaluate(source: &str) -> Result<(), String> {
    let encoded = Compiler::default()
        .compile(None, source)
        .map_err(|e| e.to_string())?;
    new_egraph()
        .parse_and_run_program(None, &encoded)
        .map_err(|e| e.to_string())?;
    Ok(())
}

#[test]
fn accepted_source_forms() {
    let cases = [
        (
            true,
            "a nested call as the pattern",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rewrite (Add (Mul x y) z) (Nil) :name \"r\")\n",
        ),
        (
            true,
            "(= v <call>), a second pattern",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rewrite (Add x y) (Nil) :when ((= x (Mul p q))) :name \"r\")\n",
        ),
        (
            true,
            "(= x y), two variables identified",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rewrite (Add x y) (Nil) :when ((= x y)) :name \"r\")\n",
        ),
        (
            true,
            "(!= x y)",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rewrite (Add x y) (Nil) :when ((!= x y)) :name \"r\")\n",
        ),
        (
            true,
            "(renaming-= x y)",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rewrite (Add x y) (Nil) :when ((renaming-= x y)) :name \"r\")\n",
        ),
        (
            true,
            "(renaming-!= x y)",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rewrite (Add x y) (Nil) :when ((renaming-!= x y)) :name \"r\")\n",
        ),
        (
            true,
            "a bare call, meaning it exists",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rewrite (Add x y) (Nil) :when ((Mul x y)) :name \"r\")\n",
        ),
        (
            false,
            "a nullary constructor without its parens",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(let n Nil)\n",
        ),
        (
            true,
            "a payload literal",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rewrite (Add x y) (Nil) :when ((= x (N 2))) :name \"r\")\n",
        ),
        (
            true,
            "a payload variable",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rewrite (Add x y) (Nil) :when ((= x (N i))) :name \"r\")\n",
        ),
        (
            true,
            "free/not-free on a slot",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rewrite (Lam $v b) (Nil) :when ((not-free $v b)) :name \"r\")\n",
        ),
        (
            false,
            "an i64 primitive over payloads",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rewrite (Add x y) (Nil) :when ((> x y)) :name \"r\")\n",
        ),
        (
            true,
            "builds a term",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rewrite (Add x y) (Mul y x) :name \"r\")\n",
        ),
        (
            true,
            "a variable",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rewrite (Add x y) x :name \"r\")\n",
        ),
        (
            true,
            "a fresh slot, with no annotation",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rewrite (Add x y) (Lam $s (Add x y)) :name \"r\")\n",
        ),
        (
            false,
            "computing a payload",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rewrite (Add (N i) (N j)) (N (+ i j)) :name \"r\")\n",
        ),
        (
            true,
            ":name, as a string literal",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rewrite (Add x y) (Nil) :name \"r\")\n",
        ),
        (
            false,
            ":ruleset",
            "(ruleset rs)\n(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rewrite (Add x y) (Nil) :ruleset rs :name \"r\")\n",
        ),
        (
            false,
            ":subsume",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rewrite (Add x y) (Nil) :subsume :name \"r\")\n",
        ),
        (
            true,
            "slots without user constructors",
            "(sort M)\n(run 0)\n(check (!= $a $b))\n",
        ),
        (
            true,
            "datatype",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(let a (N 1))\n(run 0)\n",
        ),
        (
            true,
            "sort plus constructor",
            "(sort M)\n(constructor N (i64) M)\n(let a (N 1))\n(run 0)\n",
        ),
        (
            true,
            "relation",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(relation R (M M))\n",
        ),
        (
            true,
            "function with :merge",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(function Cost (M) i64 :merge (min old new))\n",
        ),
        (
            false,
            "constructor :cost",
            "(sort M)\n(constructor N (i64) M :cost 5)\n",
        ),
        (
            true,
            "datatype*, with independent homogeneous sorts",
            "(datatype* (A (A0) (F A)) (B (B0) (G B)))\n(let a (F (A0)))\n(let b (G (B0)))\n(run 0)\n",
        ),
        (
            false,
            "rule",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(rule ((= a (Nil))) ())\n",
        ),
        (
            false,
            "birewrite",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(birewrite (Add x y) (Add y x) :name \"r\")\n",
        ),
        (
            false,
            "set, which needs rule",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(function C (M) i64 :no-merge)\n(rule ((= a (Nil))) ((set (C a) 1)))\n",
        ),
        (
            true,
            "push and pop",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(push)\n(let a (Nil))\n(pop)\n",
        ),
        (
            true,
            "extract, selecting either carrier",
            "(datatype* (A (A0)) (B (B0)))\n(let a (A0))\n(let b (B0))\n(run 0)\n(extract a)\n(extract b)\n",
        ),
        (
            true,
            "print-size",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(let a (Nil))\n(run 0)\n(print-size)\n",
        ),
        (
            false,
            "run-schedule, which would skip the phasing",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(let a (Nil))\n(run-schedule (run 1))\n",
        ),
        (
            true,
            "a source variable named like the generated root",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(let start (Add $1 $2))\n(rewrite (Add _p b) (Mul b _p))\n(run 1)\n(check (= start (Mul $2 $1)))\n",
        ),
        (
            true,
            "a source variable containing a question mark",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(let start (Add $1 $2))\n(rewrite (Add ?_p b) (Mul b ?_p))\n(run 1)\n(check (= start (Mul $2 $1)))\n",
        ),
        (
            true,
            "a source variable named like a nested temporary",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(let start (Add (Mul $1 $2) $3))\n(rewrite (Add (Mul _t1 b) c) (Mul c _t1))\n(run 1)\n(check (= start (Mul $3 $1)))\n",
        ),
        (
            true,
            "a source variable named like a side-pattern root",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(let start (Add $1 $2))\n(let other (Mul $1 $2))\n(rewrite (Add _fact0 b) (Mul b _fact0) :when ((Mul _fact0 b)))\n(run 1)\n(check (= start (Mul $2 $1)))\n",
        ),
        (
            true,
            "a source variable named like a guard root",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(let start (Lam $1 $2))\n(rewrite (Lam $v _cond0) (App _cond0 _cond0) :when ((not-free $v (Lam $v _cond0))))\n(run 1)\n(check (= start (App $2 $2)))\n",
        ),
        (
            true,
            "a source variable named like a nested side-pattern temporary",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(let start (Add (Mul (Mul $1 $2) $3) $4))\n(rewrite (Add a _w0_1) (Mul _w0_1 p) :when ((= a (Mul (Mul p q) r))))\n(run 1)\n(check (= start (Mul $4 $1)))\n",
        ),
        (
            true,
            "equivalent numbered slot spellings",
            "(datatype M (N i64) (Add M M) (Mul M M) (Lam M M :binder 0) (App M M) (Nil))\n(let start (Add $01 $+1))\n(let zero (Add $-0 $+0))\n(run 0)\n(check (free-names-are start $1))\n(check (= start (Add $1 $1)))\n(check (free-names-are zero $0))\n(check (= zero (Add $0 $0)))\n",
        ),
        (
            true,
            "constructor names colliding with derived RHS locals",
            "(datatype U (Start U) (F U) (F_slots U) (F_edge U) (Pair U U))\n(let start (Start $0))\n(rewrite (Start a) (Pair (F a) (Pair (F_slots a) (F_edge a))))\n(run 1)\n(check (= start (Pair (F $0) (Pair (F_slots $0) (F_edge $0)))))\n",
        ),
    ];
    for (accepted, name, source) in cases {
        let result = evaluate(source);
        assert_eq!(result.is_ok(), accepted, "{name}: {result:?}");
    }
}

#[test]
fn refused_source_forms_have_diagnostics() {
    let cases = [
        (
            "a matching-order annotation",
            "(datatype M (F M M))\n(rewrite (F a b) a :lead 0)\n",
            "unsupported rewrite option :lead",
        ),
        (
            "an unbound variable whose name differs by a question mark",
            "(datatype M (F M))\n(rewrite (F ?x) x)\n",
            "is not bound",
        ),
        (
            "a fresh annotation for a right-hand-side slot",
            "(datatype M (F M) (Lam M M :binder 0))\n(rewrite (F e) (Lam $s e) :fresh $s)\n",
            "unsupported rewrite option :fresh",
        ),
        (
            "a fresh annotation for a matched slot",
            "(datatype M (F M) (G M))\n(rewrite (F $x) (G $x) :fresh $x)\n",
            "unsupported rewrite option :fresh",
        ),
        (
            "a slot in a payload column",
            "(datatype M (Num i64)) (let bad (Num $a))",
            "ground payloads must be literals",
        ),
        (
            "a binder over payload columns",
            "(datatype M (Lam i64 M :binder 0))\n",
            "must cover a following child",
        ),
        (
            "a term in a ground binder column",
            "(datatype M (Null) (IConst) (Succ M) (Mul M M) (Lam M M :binder 0))\n(let bad (Lam (Null) (Null)))\n",
            "takes a slot literal",
        ),
        (
            "a global in a binder column",
            "(datatype M (Null) (IConst) (Succ M) (Mul M M) (Lam M M :binder 0))\n(let alias (Succ $a))\n(let bad (Lam alias (Null)))\n",
            "takes a slot literal",
        ),
        (
            "a pattern variable in a binder result column",
            "(datatype M (Null) (IConst) (Succ M) (Mul M M) (Lam M M :binder 0))\n(rewrite (Succ x) (Lam x x))\n",
            "takes a slot literal",
        ),
        (
            "a constructor name starting with $",
            "(datatype M ($Var M) (N))\n",
            "constructor names cannot start with $",
        ),
        (
            "an out-of-range numeric slot",
            "(datatype M (Null) (IConst) (Succ M) (Mul M M) (Lam M M :binder 0))\n(let bad (Succ $9223372036854775808))\n",
            "signed 64-bit",
        ),
        (
            "an empty slot name",
            "(datatype M (Null) (IConst) (Succ M) (Mul M M) (Lam M M :binder 0))\n(let bad (Succ $))\n",
            "invalid slot literal",
        ),
        (
            "a global named with a `$`",
            "(datatype M (Null) (IConst) (Succ M) (Mul M M) (Lam M M :binder 0))\n(let $I (IConst))\n",
            "must not start with $",
        ),
        (
            "a global bound to a bare slot invocation",
            "(datatype M (Null) (IConst) (Succ M) (Mul M M) (Lam M M :binder 0))\n(let v $7)\n",
            "cannot currently store",
        ),
        (
            "a bare `:when` fact without the list",
            "(datatype M (Null) (IConst) (Succ M) (Mul M M) (Lam M M :binder 0))\n(rewrite (Mul a b) a :when (= a (Succ p)) :name \"r\")\n",
            "takes a list of facts",
        ),
        (
            "several `:when` clauses",
            "(datatype M (Null) (IConst) (Succ M) (Mul M M) (Lam M M :binder 0))\n(rewrite (Mul a b) a :when ((= a (Succ p))) :when ((= b (Succ q))) :name \"r\")\n",
            "one list",
        ),
        (
            "egglog's `:cost`, which extraction here would not honour",
            "(sort M)\n(constructor Succ (M) M :cost 5)\n",
            "option :cost is not supported",
        ),
        (
            "an unknown declaration option",
            "(sort M)\n(constructor Succ (M) M :wat 1)\n",
            "option :wat is not supported",
        ),
        (
            "a nullary constructor without its parens, in a term",
            "(datatype M (Null) (IConst) (Succ M) (Mul M M) (Lam M M :binder 0))\n(let n Null)\n",
            "needs parentheses",
        ),
        (
            "a nullary constructor without its parens, in a pattern",
            "(datatype M (Null) (IConst) (Succ M) (Mul M M) (Lam M M :binder 0))\n(rewrite (Succ Null) (Null) :name \"r\")\n",
            "needs parentheses",
        ),
        (
            "a negative binder position",
            "(sort M)\n(constructor F (M M) M :binder -1)\n",
            "binder position",
        ),
        (
            "an out-of-range binder position",
            "(sort M)\n(constructor F (M M) M :binder 2)\n",
            "binder position",
        ),
        (
            "duplicate binder positions",
            "(sort M)\n(constructor F (M M) M :binder 0 0)\n",
            "duplicate",
        ),
        (
            "non-contiguous nested binders",
            "(sort M)\n(constructor F (M M M M) M :binder 0 2)\n",
            "contiguous",
        ),
        (
            "a binder without a covered child",
            "(sort M)\n(constructor F (M M) M :binder 1)\n",
            "following child",
        ),
        (
            "a cross-sort slotted child",
            "(sort A)\n(sort B)\n(constructor A0 () A)\n(constructor B0 () B)\n(constructor F (A B) A)\n",
            "cross-sort slotted children",
        ),
        (
            "a sort the machinery already declares",
            "(sort Idx)\n(constructor F (Idx) Idx)\n",
            "is reserved",
        ),
        (
            "a cross-sort union",
            "(datatype* (A (A0)) (B (B0)))\n(let a (A0))\n(let b (B0))\n(union a b)\n",
            "cannot compare terms of different equality sorts",
        ),
        (
            "a global used at the wrong sort",
            "(datatype* (A (A0)) (B (B0) (G B)))\n(let a (A0))\n(let bad (G a))\n",
            "expected B",
        ),
        (
            "a cross-sort equality check",
            "(datatype* (A (A0)) (B (B0)))\n(check (= (A0) (B0)))\n",
            "cannot compare terms of different equality sorts",
        ),
        (
            "a cross-sort renaming equality check",
            "(datatype* (A (A0)) (B (B0)))\n(check (renaming-= (A0) (B0)))\n",
            "cannot compare terms of different equality sorts",
        ),
        (
            "a holds check naming a constructor from another sort",
            "(datatype* (A (A0)) (B (B0)))\n(check (__internal-holds (A0) B0))\n",
            "holds compares different carrier sorts",
        ),
        (
            "a cross-sort rewrite result",
            "(datatype* (A (A0)) (B (B0)))\n(rewrite (A0) (B0) :name \"bad\")\n",
            "B0 produces B, expected A",
        ),
        (
            "a cross-sort side pattern",
            "(datatype* (A (A0)) (B (B0)))\n(rewrite (A0) (A0) :when ((B0)) :name \"bad\")\n",
            "cross-sort multipatterns",
        ),
        (
            "an ambiguous top-level slot comparison",
            "(datatype* (A (A0)) (B (B0)))\n(check (= $0 $1))\n",
            "no equality-sort context",
        ),
        (
            "a multi-sort encoding-name collision",
            "(sort A)\n(sort B)\n(constructor SlottedVar_0 () A)\n(constructor B0 () B)\n",
            "reserved by the slotted",
        ),
        (
            "a duplicate equality sort declaration",
            "(sort A)\n(sort A)\n(constructor A0 () A)\n",
            "sort \"A\" is declared more than once",
        ),
        (
            "a duplicate constructor declaration",
            "(sort A)\n(constructor A0 () A)\n(constructor A0 () A)\n",
            "constructor \"A0\" is declared more than once",
        ),
        (
            "a payload-layout name collision",
            "(sort U)\n(constructor SlottedPayloadLayout () U)\n",
            "reserved by the slotted",
        ),
        (
            "a machinery phase ruleset collision",
            "(datatype M (Null) (IConst) (Succ M) (Mul M M) (Lam M M :binder 0))\n(ruleset slotted-group)\n",
            "reserved by the slotted",
        ),
        (
            "a program that declares nothing",
            "(run 1)\n",
            "no equality sort is declared",
        ),
        (
            "a named ruleset that the slotted schedule cannot select",
            "(datatype M (Null) (IConst) (Succ M) (Mul M M) (Lam M M :binder 0))\n(ruleset custom)\n(rewrite (Succ a) a :name \"custom-rule\" :ruleset custom)\n",
            "named rulesets are not supported",
        ),
        (
            "a pattern variable in a binder column",
            "(datatype M (Null) (IConst) (Succ M) (Mul M M) (Lam M M :binder 0))\n(rewrite (Lam x (Succ x)) (Null))\n",
            "takes a slot literal",
        ),
        (
            "a binder of a different carrier",
            "(datatype* (A (A0)) (B (Lam A B :binder 0)))\n",
            "cross-sort slotted children are not supported",
        ),
        (
            "an unbound rewrite root",
            "(datatype M (Null) (IConst) (Succ M) (Mul M M) (Lam M M :binder 0))\n(rewrite x (Mul x x) :name \"r\")\n",
            "needs a constructor pattern",
        ),
        (
            "egglog's `rule`, which this language does not have",
            "(datatype M (Null) (IConst) (Succ M) (Mul M M) (Lam M M :binder 0))\n(rule ((= a (Null))) ())\n",
            "not supported by the slotted frontend",
        ),
        (
            "a payload variable the right-hand side names and no pattern binds",
            "(sort M)\n(constructor N (i64) M)\n(constructor A (M M) M)\n(rewrite (A x y) (N j) :name \"r\")\n",
            "is not bound",
        ),
    ];
    for (name, source, phrase) in cases {
        let error = evaluate(source).expect_err(name);
        assert!(
            error.contains(phrase),
            "{name}: expected {phrase:?}, got {error}"
        );
    }
}

#[test]
fn repeated_compilation_preserves_scopes() {
    let source = r#"
(datatype M (Nil) (N i64) (Add M M))
(push)
(let y (Nil))
(pop)
(rewrite (Add x y) (Add y x))
(let x (Nil))
(let seed (Add (N 1) (N 2)))
(run 1)
(check (= seed (Add (N 2) (N 1))))
"#;
    assert_eq!(
        Compiler::default().compile(None, source).unwrap(),
        Compiler::default().compile(None, source).unwrap()
    );
    evaluate(source).unwrap();
}
