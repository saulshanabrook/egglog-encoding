import Mathlib.Data.List.Forall2
import EgglogSemantics.Spec.Database

/-!
# Congruence

`Cong db a b` says `a = b` is derivable in `db`. It replaces the Redex
`Congruence-Reduction` together with `restore-congruence`: those compute a closed
set of equality pairs by iterating a reduction relation to a fixpoint, and here
the closure is an inductive predicate instead. Nothing in the semantics needs the
closed set — the only place the Redex reads it is the `valid-subst` side
conditions, which ask `Cong` directly.

The Redex's fifth rule, "presence of children", is absent because it changes the
term set rather than the relation; it is `Database.WF.subtermClosed`.

Reflexivity is restricted to terms the database holds, as in the Redex: an e-graph
knows nothing about a term it does not contain, and that restriction is what makes
the witness condition in e-matching bite.
-/

namespace Egglog
mutual

/-- The congruence closure of `db`'s asserted equalities. -/
inductive Cong (db : Database) : Term → Term → Prop where
  | assert {a b : Term} : (a, b) ∈ db.eqs → Cong db a b
  | refl {a : Term} : a ∈ db.terms → Cong db a a
  | symm {a b : Term} : Cong db a b → Cong db b a
  | trans {a b c : Term} : Cong db a b → Cong db b c → Cong db a c
  | congr {f : FnName} {as bs : List Term} :
      Term.app f as ∈ db.terms → Term.app f bs ∈ db.terms → CongList db as bs →
      Cong db (.app f as) (.app f bs)

/-- Pointwise `Cong` over argument lists.

Companion of `Cong.congr`. `List.Forall₂ (Cong db)` would say the same thing, but
passing `Cong db` as a parameter of another inductive is not a legal recursive
occurrence, so the two are declared mutually and `CongList.forall₂` bridges them. -/
inductive CongList (db : Database) : List Term → List Term → Prop where
  | nil : CongList db [] []
  | cons {a b : Term} {as bs : List Term} :
      Cong db a b → CongList db as bs → CongList db (a :: as) (b :: bs)

end

namespace CongList
variable {db : Database}

end CongList
namespace Cong
variable {db : Database}

variable {db : Database}

/-- `Cong db` is an equivalence on the subtype of `db.terms`. This is the e-graph
viewed as a set of e-classes: `Quotient` of this setoid is `db`'s e-classes. -/
def setoid (db : Database) : Setoid {t : Term // t ∈ db.terms} where
  r a b := Cong db a.val b.val
  iseqv := ⟨fun a => .refl a.property, .symm, .trans⟩

end Cong
end Egglog
