import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Sort
import EgglogSemantics.Slotted.Spec.Slots

/-!
# Primitive values as canonical terms

The slotted pass needs slot sets, renamings, lists of renamings, lists of slot sets and
booleans as values, and the plain specification has only terms. A value is therefore a term
in a **canonical form** under a reserved `@`-head: a slot set is `@set(s₁, …, sₙ)` with its
names sorted and distinct, a renaming is `@ren(@pair(s₁, t₁), …)` sorted by key, a list of
renamings is `@rens(m₁, …)` sorted and distinct, a list of slot sets is `@sets(A₁, …)`, and
the booleans are `@true()` and `@false()`. Two values are equal exactly when their canonical
terms are, so the plain congruence, which never equates a value with anything else, compares
values correctly. This module has the encoders, the decoders and the order they use;
`Prim.lean` has the operations.
-/

namespace Egglog.Slotted.Target

/-- The heads of the value forms. -/
def setName : FnName := "@set"
def renName : FnName := "@ren"
def pairName : FnName := "@pair"
def rensName : FnName := "@rens"
def setsName : FnName := "@sets"
def trueName : FnName := "@true"
def falseName : FnName := "@false"

/-- A slot set: sorted, distinct names. -/
abbrev SlotSet := List Slot

/-- Sort names, each once. -/
def canonSlots (A : List Slot) : SlotSet := A.dedup.mergeSort fun a b => decide (a ≤ b)

/-- `a ≤ b` in the term order `Term.blt`. -/
def termLe (a b : Term) : Bool := !Term.blt b a

/-- Sort terms, each once, in the term order. -/
def canonTerms (ts : List Term) : List Term := ts.dedup.mergeSort termLe

/-! ### Encoders -/

/-- The slot set `A` as a value. -/
def encodeSet (A : List Slot) : Term := .app setName ((canonSlots A).map Term.slot)

/-- The renaming `m` as a value, sorted by key. `m` is read as a function: the first entry
for each key counts, as `Renaming.apply` reads it. -/
def encodeRen (m : Renaming) : Term :=
  let keys := canonSlots m.dom
  .app renName (keys.filterMap fun k => (m.apply k).map fun v => .app pairName [.slot k, .slot v])

/-- A list of renamings as a value: sorted, each once. -/
def encodeRens (ms : List Renaming) : Term := .app rensName (canonTerms (ms.map encodeRen))

/-- A list of slot sets as a value, each once, in the given order. -/
def encodeSets (As : List (List Slot)) : Term := .app setsName (As.map encodeSet).dedup

def encodeBool (b : Bool) : Term := if b then .app trueName [] else .app falseName []

/-! ### Decoders -/

/-- The slot a term is, if it is one. -/
def decodeSlot : Term → Option Slot := Term.slotName?

/-- The slots of a slot set value, in its stored order; `none` for anything else. -/
def decodeSet : Term → Option (List Slot)
  | .app f args => if f = setName then args.mapM decodeSlot else none
  | _ => none

def decodePair : Term → Option (Slot × Slot)
  | .app f [a, b] => if f = pairName then do pure (← decodeSlot a, ← decodeSlot b) else none
  | _ => none

/-- The renaming a value holds, in its stored order; `none` for anything else. -/
def decodeRen : Term → Option Renaming
  | .app f args => if f = renName then args.mapM decodePair else none
  | _ => none

/-- The renamings of a list value. -/
def decodeRens : Term → Option (List Renaming)
  | .app f args => if f = rensName then args.mapM decodeRen else none
  | _ => none

/-- The slot sets of a list value. -/
def decodeSets : Term → Option (List (List Slot))
  | .app f args => if f = setsName then args.mapM decodeSet else none
  | _ => none

def decodeBool : Term → Option Bool
  | .app f [] => if f = trueName then some true else if f = falseName then some false else none
  | _ => none

/-! ### Fresh names

Final slot names minted by the pass's primitives are the least unused of `$0, $1, …`;
placeholders, used by unification, are `$@0, $@1, …`. Both are slot names, so they live in
the same value kinds as source slots. -/

/-- The `k`th canonical name. -/
def canonicalName (k : Nat) : Slot := "$" ++ toString k

/-- The `k`th placeholder. -/
def placeholder (k : Nat) : Slot := "$@" ++ toString k

/-- The first `n` names of `name 0, name 1, …` outside `avoid`. At most `avoid.length`
names of the enumeration are skipped, which bounds the scan. -/
def freshNamesFrom (name : Nat → Slot) (n : Nat) (avoid : List Slot) : List Slot :=
  go (n + avoid.length) 0 n []
where
  go : Nat → Nat → Nat → List Slot → List Slot
    | 0, _, _, acc => acc.reverse
    | fuel + 1, k, need, acc =>
      if need = 0 then acc.reverse
      else if name k ∈ avoid then go fuel (k + 1) need acc
      else go fuel (k + 1) (need - 1) (name k :: acc)

/-- The first `n` canonical names outside `avoid`. -/
def freshNames (n : Nat) (avoid : List Slot) : List Slot := freshNamesFrom canonicalName n avoid

/-- The first `n` placeholders outside `avoid`. -/
def freshPlaceholders (n : Nat) (avoid : List Slot) : List Slot :=
  freshNamesFrom placeholder n avoid

end Egglog.Slotted.Target
