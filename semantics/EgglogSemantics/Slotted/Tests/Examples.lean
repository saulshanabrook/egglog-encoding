import EgglogSemantics.Slotted.Tests.Bounded
import EgglogSemantics.Slotted.Tests.Parse
import EgglogSemantics.Impl.Observe

/-!
# The slotted specification on the paper's examples

Each program is written in the reference's syntax, parsed by `Slotted/Tests/Parse.lean`, and
run by the bounded evaluator over the slot universe given with it. A `check` the evaluator
finds to hold is a positive statement: by `closure_sound` the equalities it rests on are
`SCong`-derivable, and the redundancies it rests on are `Redundant`. A `fail` the evaluator
confirms is a bounded statement: no derivation was found inside the universe. Each guard
says which of its outcomes are which.

The last group is the conservative-extension test: on programs without slots and with no
binders, the slotted outcome agrees with the plain interpreter's.
-/

namespace Egglog.Slotted.Examples

open Egglog.Slotted.Bounded

set_option linter.hashCommand false

/-- The outcome of each check of a file, in order, over the slot universe `S`. -/
def outcomes (S : List Slot) (src : String) : List (Option Bool) :=
  ((parseFile src).toOption.getD []).map fun c => Bounded.observe S c.program

/-- What the file asserts of each check. -/
def expected (src : String) : List (Option Bool) :=
  ((parseFile src).toOption.getD []).map fun c => some (c.expected == .ok)

/-! Literal pattern slots have no assignment choice. Distinct literals cannot collapse,
and a literal cannot be changed even to a fresh name. -/

#guard (Closure.unify [] (.var "$x") (Term.slot "$x")).isSome
#guard (Closure.unify [] (.var "$x") (Term.slot "$y")).isNone

/-! ### The paper's example

The literal `$v` in the rule stays fixed; renamed representatives supply its matches.
The distribution rule moves the factor `5` under two sums whose binder it does not mention.
Positive: the distributed form, with fresh bound names `$k`, `$l`, is reached. Bounded: the
form with the body `Mul($l, $l)` is not. -/

def paper : String :=
  "(datatype Expr (Num i64) (Mul Expr Expr) (Sum Expr Expr :binder 0))\n\
   (let t (Mul (Num 5) (Sum $i (Sum $j (Mul $i $j)))))\n\
   (rewrite (Mul x (Sum $v b)) (Sum $v (Mul x b)) :when ((not-free $v x)))\n\
   (run 2)\n\
   (check (= t (Sum $k (Sum $l (Mul (Num 5) (Mul $k $l))))))\n\
   (fail (check (= t (Sum $k (Sum $l (Mul (Num 5) (Mul $l $l)))))))\n"

#guard outcomes ["$i", "$j", "$k", "$l", "$v"] paper = [some true, some false]
#guard expected paper = [some true, some false]

/-! ### α-equivalence of bound names

Positive: the identity with another bound name, and the constant function with another
bound name. Bounded: the identity is not the constant function, and a bound name does not
match a distinct pattern slot. -/

def alpha : String :=
  "(datatype E (V Var) (Lam Var E :binder 0) (App E E))\n\
   (let id (Lam $a (V $a)))\n\
   (let k (Lam $a (V $c)))\n\
   (check (= id (Lam $b (V $b))))\n\
   (check (= k (Lam $b (V $c))))\n\
   (fail (check (= id k)))\n\
   (fail (check (= id (Lam $b (V $d)))))\n"

#guard outcomes ["$a", "$b", "$c", "$d"] alpha = [some true, some true, some false, some false]
#guard expected alpha = [some true, some true, some false, some false]

/-! ### A symmetry from a union (`paper/enode-collisions.egg`)

`C($0, $1) = C($1, $0)` makes `C` commutative. Positive: the symmetry lifts through `I` by
congruence, and through two positions of `N` independently. Bounded: the unrelated
`I(C($0, $2), Null)` stays apart. -/

def symmetry : String :=
  "(sort U)\n\
   (constructor C (U U) U) (constructor I (U U) U) (constructor N (U U) U)\n\
   (constructor Null () U)\n\
   (let c01 (C $0 $1))\n\
   (union c01 (C $1 $0))\n\
   (let i01 (I (C $0 $1) (Null)))\n\
   (let i10 (I (C $1 $0) (Null)))\n\
   (let i02 (I (C $0 $2) (Null)))\n\
   (let n1 (N (C $0 $1) (C $0 $1)))\n\
   (let n2 (N (C $0 $1) (C $1 $0)))\n\
   (check (= i01 i10))\n\
   (fail (check (= i01 i02)))\n\
   (check (= n1 n2))\n"

#guard outcomes ["$0", "$1", "$2"] symmetry = [some true, some false, some true]
#guard expected symmetry = [some true, some false, some true]

/-! ### A redundant slot (`paper/figure-3.egg`)

`Mul($7, Null) = Null` makes `$7` redundant: the class does not depend on it. Positive:
`Mul($9, Null)` is `Null` too, and the product has no live free slot. Bounded:
`Mul($9, $7)` stays apart from `Null`. -/

def redundant : String :=
  "(sort U)\n\
   (constructor Mul (U U) U) (constructor Null () U)\n\
   (let m7 (Mul $7 (Null)))\n\
   (union m7 (Null))\n\
   (let m9 (Mul $9 (Null)))\n\
   (let m97 (Mul $9 $7))\n\
   (check (= m9 (Null)))\n\
   (check (free-names-are m7))\n\
   (fail (check (= m97 (Null))))\n"

#guard outcomes ["$7", "$9", "$a"] redundant = [some true, some true, some false]
#guard expected redundant = [some true, some true, some false]

/-! ### Every slot redundant (`paper/var-xy-eq-yz.egg`)

`F($0, $1) = F($1, $2)` forces every slot redundant: the class has no live free slot.
Positive: both assertions. -/

def allRedundant : String :=
  "(sort U)\n\
   (constructor F (U U) U)\n\
   (let f01 (F $0 $1))\n\
   (let f12 (F $1 $2))\n\
   (union f01 f12)\n\
   (check (= f01 f12))\n\
   (check (free-names-are f01))\n"

#guard outcomes ["$0", "$1", "$2", "$3"] allRedundant = [some true, some true]
#guard expected allRedundant = [some true, some true]

/-! ### A capture excluded by `not-free`

The factor `$i` is free under a sum binding `$i`, so the distribution rule must not move it
inside. Bounded: the captured form is not reached. Positive: the original, with its bound
name changed, is. -/

def capture : String :=
  "(datatype Expr (Num i64) (Mul Expr Expr) (Sum Expr Expr :binder 0))\n\
   (let u (Mul $i (Sum $i (Num 5))))\n\
   (rewrite (Mul x (Sum $v b)) (Sum $v (Mul x b)) :when ((not-free $v x)))\n\
   (run 2)\n\
   (fail (check (= u (Sum $k (Mul $k (Num 5))))))\n\
   (check (= u (Mul $i (Sum $k (Num 5)))))\n"

#guard outcomes ["$i", "$k", "$l", "$v"] capture = [some false, some true]
#guard expected capture = [some false, some true]

/-! ### Equality modulo renaming (`paper/fgh-transitive-symmetry.egg`)

`F($1, $2) = G($2, $1)` and `G($1, $2) = H($1, $2)` carry the swap through. Positive:
`F($1, $2) = H($2, $1)`, and `F($1, $2)` equals `H($1, $2)` modulo renaming. Bounded: they
are not equal as written. -/

def transitiveSymmetry : String :=
  "(sort U)\n\
   (constructor F (U U) U) (constructor G (U U) U) (constructor H (U U) U)\n\
   (let f12 (F $1 $2))\n\
   (let g21 (G $2 $1))\n\
   (let g12 (G $1 $2))\n\
   (let h12 (H $1 $2))\n\
   (let h21 (H $2 $1))\n\
   (union f12 g21)\n\
   (union g12 h12)\n\
   (check (= f12 h21))\n\
   (check (renaming-= f12 h12))\n\
   (fail (check (= f12 h12)))\n"

#guard outcomes ["$1", "$2", "$3", "$4"] transitiveSymmetry = [some true, some true, some false]
#guard expected transitiveSymmetry = [some true, some true, some false]

/-! ### Conservative extension

Programs without slots, under the empty binder signature and the empty slot universe, have
the same outcome under the slotted evaluator and the plain interpreter. -/

/-- The plain interpreter's outcome. -/
def plain (src : String) : Option Bool :=
  ((Program.ofEgg src).toOption.map fun P => (Egglog.observe P).map (·.succeeded)).getD none

/-- The slotted evaluator's outcome for the same plain program. -/
def slotted (src : String) : Option Bool :=
  ((Program.ofEgg src).toOption.map fun P => Bounded.observe [] ⟨P, Binders.none⟩).getD none

def plainUnion : String :=
  "(constructor A () M) (constructor F (M) M)\n\
   (F (A))\n\
   (rule ((F x)) ((union (F x) x)))\n\
   (run 1)\n\
   (check (= (F (A)) (A)))\n"

def plainFailed : String :=
  "(constructor A () M) (constructor B () M) (constructor F (M) M)\n\
   (F (A)) (B)\n\
   (rule ((F x)) ((union (F x) x)))\n\
   (run 1)\n\
   (check (= (F (A)) (B)))\n"

def plainSaturate : String :=
  "(constructor A () M) (constructor F (M M) M) (constructor G (M) M)\n\
   (F (A) (G (A)))\n\
   (rule ((F a b)) ((union (F a b) (F b a)))) (rule ((F (G x) y)) ((union (G x) y)))\n\
   (run-schedule (saturate (run)))\n\
   (check (= (A) (G (A))))\n"

def plainDisequality : String :=
  "(constructor A () M) (constructor B () M) (constructor F (M M) M)\n\
   (F (A) (B))\n\
   (rule ((F x y) (!= x y)) ((union x y)))\n\
   (run 1)\n\
   (check (= (A) (B)))\n"

#guard [plainUnion, plainFailed, plainSaturate, plainDisequality].map plain =
  [some true, some false, some true, some true]
#guard [plainUnion, plainFailed, plainSaturate, plainDisequality].map slotted =
  [some true, some false, some true, some true]

end Egglog.Slotted.Examples
