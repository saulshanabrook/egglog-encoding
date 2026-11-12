import EgglogSemantics.Slotted.Encode
import EgglogSemantics.Slotted.Target.Interp
import EgglogSemantics.Slotted.Tests.Parse

/-!
# The slotted pass on the paper's example

The distribution example is parsed, compiled by the slotted pass and run by the target
interpreter: the distributed form with fresh bound names is reached, and the form whose
body is `Mul($l, $l)` is not. The primitive catalogue is exercised on the values the paper's
rules compute.
-/

namespace Egglog.Slotted.Tests

open Egglog.Slotted.Target

set_option linter.hashCommand false

private def paper : String :=
  "(datatype Expr (Num i64) (Mul Expr Expr) (Sum Expr Expr :binder 0))\n\
   (let t (Mul (Num 5) (Sum $i (Sum $j (Mul $i $j)))))\n\
   (rewrite (Mul x (Sum $v b)) (Sum $v (Mul x b)) :when ((not-free $v x)))\n\
   (run 2)\n\
   (check (= t (Sum $k (Sum $l (Mul (Num 5) (Mul $k $l))))))\n\
   (fail (check (= t (Sum $k (Sum $l (Mul (Num 5) (Mul $l $l)))))))\n"

/-- The outcomes the pass and the interpreter give the file's checks, in order. -/
private def outcomes (src : String) : List (Option Bool) :=
  ((parseFile src).toOption.getD []).map fun c =>
    match compile c.program.binders c.program.plain with
    | .ok P => observe P
    | .error _ => none

#guard outcomes paper = [some true, some false]

/-! ### The primitives -/

private def ren (ps : List (Slot × Slot)) : Term := encodeRen ps
private def set (ss : List Slot) : Term := encodeSet ss
private def ev (f : FnName) (args : List Term) : Option Term := Prim.eval f args

#guard ev "@comp" [ren [("$a", "$b")], ren [("$x", "$a")]] = some (ren [("$x", "$b")])
#guard ev "@inv" [ren [("$a", "$b")]] = some (ren [("$b", "$a")])
#guard ev "@restrict" [ren [("$a", "$b"), ("$c", "$d")], set ["$c"]] = some (ren [("$c", "$d")])
#guard ev "@img" [ren [("$a", "$b"), ("$c", "$d")]] = some (set ["$b", "$d"])
#guard ev "@isPerm" [ren [("$a", "$b"), ("$b", "$a")], set ["$a", "$b"]] = some (encodeBool true)
#guard ev "@isPerm" [ren [("$a", "$b")], set ["$a", "$b"]] = some (encodeBool false)
-- `align` refuses an inconsistent or non-injective union.
#guard ev "@align" [ren [("$a", "$b")], ren [("$c", "$d")]] = some (ren [("$a", "$b"), ("$c", "$d")])
#guard ev "@align" [ren [("$a", "$b")], ren [("$a", "$c")]] = none
#guard ev "@align" [ren [("$a", "$b")], ren [("$c", "$b")]] = none
-- Collide composes a stale symmetry on three slots through smaller child maps.
-- Only the path $y ↦ $a ↦ $b ↦ $x survives both partial compositions.
#guard Prim.norm? (.app "@align" [
    .app "@comp" [ren [("$b", "$x")],
      .app "@comp" [ren [("$a", "$b"), ("$b", "$a"), ("$c", "$c")],
        .app "@inv" [ren [("$a", "$y"), ("$b", "$z")]]]],
    ren [("$w", "$v")]]) = some (ren [("$y", "$x"), ("$w", "$v")])
-- `extend` names the missing slots outside the image and the avoided set.
#guard ev "@extend" [ren [("$a", "$0")], set ["$a", "$b"], set ["$1"]] =
  some (ren [("$a", "$0"), ("$b", "$2")])
-- A unification map on three placeholders: unify merges, refine enumerates the two aliasings of the
-- touched blocks that no clique forbids, anchor names the blocks.
private def U0 : Term := ren [("$@0", "$@0"), ("$@1", "$@1"), ("$@2", "$@2")]
private def C1 : Term := encodeSets [["$@0", "$@1"]]
#guard ev "@unify1" [U0, .slot "$@1", .slot "$@2", C1, set []] =
  some (ren [("$@0", "$@0"), ("$@1", "$@1"), ("$@2", "$@1")])
#guard ev "@unify1" [U0, .slot "$@0", .slot "$@1", C1, set []] = none
#guard (ev "@refine" [U0, C1, set [], set ["$@0", "$@2"]]).bind Prim.elements =
  some [ren [("$@0", "$@0"), ("$@1", "$@1"), ("$@2", "$@0")], U0]
#guard ev "@anchor" [U0, ren [("$i", "$@1")]] =
  some (ren [("$@0", "$0"), ("$@1", "$i"), ("$@2", "$1")])
#guard (ev "@perms" [set ["$a", "$b"]]).bind Prim.elements =
  some (canonTerms [ren (Renaming.id ["$a", "$b"]), ren [("$a", "$b"), ("$b", "$a")]])

-- Inversion requires an injection; unification maps can share a value but cannot be inverted.
#guard ev "@inv" [ren [("$a", "$c"), ("$b", "$c")]] = none
#guard ev "@ren" [.app "@pair" [.slot "$a", .slot "$b"],
  .app "@pair" [.slot "$a", .slot "$c"]] = none

-- Fixed literal identities are independent of clique constraints. A placeholder may
-- join a literal, but two literals never merge, even when C is empty.
private def fixedU : Term := ren (Renaming.id ["$@0", "$x", "$y"])
private def fixedP : Term := set ["$x", "$y"]
#guard ev "@unify1" [fixedU, .slot "$@0", .slot "$x", encodeSets [], fixedP] =
  some (ren [("$@0", "$x"), ("$x", "$x"), ("$y", "$y")])
#guard ev "@unify1" [fixedU, .slot "$x", .slot "$y", encodeSets [], fixedP] = none
#guard ((ev "@refine" [fixedU, encodeSets [], fixedP, set ["$@0", "$x", "$y"]]).bind
  decodeRens).map List.length = some 3

/-! ### Target matching boundaries -/

-- Primitive keys and results need not have been stored as rows.
private def freshQuery : Query :=
  [.eq (.var "m") (.app "@fresh" [.app "@set" [.app "$unseen" []], .app "@set" []]),
   .eq (.app "@dom" [.var "m"]) (.app "@set" [.app "$unseen" []])]
#guard observe ⟨.run [], freshQuery⟩ = some true
-- Ordinary literals still require existence, and a computed primitive atom does not.
#guard observe ⟨.run [], [.ne (.lit (.int 1)) (.lit (.int 2))]⟩ = some false
#guard observe ⟨.run [], [.expr (.app "@id" [.app "@set" []])]⟩ = some true

private def a : Expr := .app "A" []
private def b : Expr := .app "B" []
private def fa : Expr := .app "F" [a]
private def fb : Expr := .app "F" [b]
private def merged : Schedule := .run [⟨[], [.expr fa, .union a b]⟩]
-- `F(B)` is an unstored spelling of the stored `F(A)`; subsumption removes both.
#guard observe ⟨merged, [.expr fb]⟩ = some true
#guard observe ⟨.seq merged (.run [⟨[], [.subsume "F" [a]]⟩]), [.expr fb]⟩ = some false

/-! ### Explicit rejection boundaries -/

private def rejects (src : String) : Bool :=
  match parseComplete src with
  | .error _ => false
  | .ok (cs, P) => (compile P.binders P.plain).toOption.isNone ||
      cs.any fun c => (compile c.program.binders c.program.plain).toOption.isNone

#guard rejects "(A) (rule ((A)) (unbound)) (run 1) (check (A))"
#guard rejects "(A) (rule ((A)) ((union x x))) (run 1) (check (A))"
#guard rejects "(let s $x) (union s (A)) (check (A))"
#guard rejects "(let s $x) (check (= s s))"
#guard rejects "(let s $@private) (V s) (check (V $x))"
#guard rejects "(let s $x) (A) (rewrite (A) (V s)) (run 1) (check (A))"
#guard rejects "(A) (rewrite (A) (free $x (A))) (run 1) (check (A))"
#guard rejects "(Num 1) (check (= (Num 1) 1))"

end Egglog.Slotted.Tests
