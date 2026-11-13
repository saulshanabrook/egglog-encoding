import Mathlib.Logic.Relation
import EgglogSemantics.Slotted.Spec.Binders

/-!
# Slots, free slots, renamings, and the action of a renaming

A slot `$s` is a distinguished nullary symbol: the term `Term.app "$s" []`. Its name is spelled
with the `$`, so a slot is recognised by its head alone and no string surgery is needed. The
free slots of a term are the slots not bound by a binder above them; a renaming is a finite
partial injection on slots; and its action `m * t` renames the free slots of `t` through `m`
while giving every bound name a fresh one. The action is a relation, `Renames`: each choice of
fresh names is a result, and all results are α-equivalent.
-/

namespace Egglog.Slotted

/-- A slot name, spelled with its `$`, such as `"$i"`. -/
abbrev Slot := String

/-- Whether a symbol is a slot: a name starting with `$`. -/
def isSlotName (f : FnName) : Bool := f.startsWith "$"

/-- The slot `$s` as a term: the distinguished nullary symbol. -/
def _root_.Egglog.Term.slot (s : Slot) : Term := .app s []

/-- The slot a term is, if it is one. -/
def _root_.Egglog.Term.slotName? : Term → Option Slot
  | .app f [] => if isSlotName f then some f else none
  | _ => none

/-- Whether a term is a slot. -/
def _root_.Egglog.Term.isSlot (t : Term) : Bool := t.slotName?.isSome

/-- Whether an application `f(args)` is the slot `f`: a slot name applied to no arguments. -/
def isSlotApp (f : FnName) (args : List Term) : Bool := isSlotName f && args.isEmpty

/-! ### Free slots -/

/-- The slot names among the terms bound in argument `i` of `f(args)`: `B_i` as names. -/
def boundNames (bind : Binders) (f : FnName) (args : List Term) (i : Nat) : List Slot :=
  (bind.boundIn f args i).filterMap Term.slotName?

mutual

/-- `slots(t)`: the free slots of `t`. A slot is free in itself; an application contributes
the free slots of each term child, less the names bound in that child, and nothing from its
binding positions. -/
@[blueprint "def:slotted-slots"
  (statement := /--
  \[
  \operatorname{slots}(\$s)=\{\$s\}\qquad
  \operatorname{slots}(f(t_1,\ldots,t_n))
    =\bigcup_{i:\,(i,\_)\notin\operatorname{bind}(f)}
      \bigl(\operatorname{slots}(t_i)\setminus B_i(f(t_1,\ldots,t_n))\bigr)
  \]
  -/)
  (latexEnv := "paperfragment")]
def slots (bind : Binders) : Term → List Slot
  | .lit _ => []
  | .app f args =>
    if isSlotApp f args then [f] else slotsArgs bind f args args 0

/-- `slots` over the arguments from position `k` of `f(all)`. -/
def slotsArgs (bind : Binders) (f : FnName) (all : List Term) : List Term → Nat → List Slot
  | [], _ => []
  | a :: as, k =>
    (if bind.isBinding f k then []
      else (slots bind a).filter fun s => s ∉ boundNames bind f all k)
      ∪ slotsArgs bind f all as (k + 1)

end

mutual

/-- Every slot name occurring in `t`, free or bound. Fresh names avoid all of them. -/
def allSlots : Term → List Slot
  | .lit _ => []
  | .app f args => if isSlotApp f args then [f] else allSlotsList args

def allSlotsList : List Term → List Slot
  | [] => []
  | a :: as => allSlots a ∪ allSlotsList as

end

/-- A term whose binding positions all hold slot literals, throughout. -/
inductive WellBound (bind : Binders) : Term → Prop where
  | lit (l : Lit) : WellBound bind (.lit l)
  | app {f : FnName} {args : List Term} :
      (∀ j, bind.isBinding f j = true → ∀ a, args[j]? = some a → a.isSlot = true) →
      (∀ a ∈ args, WellBound bind a) → WellBound bind (.app f args)

/-! ### Renamings -/

/-- A renaming: a list of pairs `(s, m(s))`. `Renaming.WF` makes it a finite partial
injection; the operations below are the paper's. -/
@[blueprint "def:slotted-renaming"
  (title := /-- Renamings -/)
  (statement := /-- A renaming $m$ is a finite partial injection on slots, with domain
  $\operatorname{dom}(m)$, image $\operatorname{img}(m)$, inverse $m^{-1}$, composition
  $(m\circ m')(s)=m(m'(s))$, restriction $m|_A$ to the slots in $A$, the identity
  $\mathrm{id}_A=[s\mapsto s\mid s\in A]$, and the update
  $m_s^r=(m\setminus\{\$s\})\cup[\$s\mapsto\$r]$, which agrees with $m$ except that it sends
  $\$s$ to $\$r$. -/)]
abbrev Renaming := List (Slot × Slot)

namespace Renaming

/-- `m(s)`: the first image recorded for `s`. -/
def apply (m : Renaming) (s : Slot) : Option Slot := (m.find? (·.1 == s)).map (·.2)

/-- `dom(m)`. -/
def dom (m : Renaming) : List Slot := m.map Prod.fst

/-- `img(m)`. -/
def img (m : Renaming) : List Slot := m.map Prod.snd

/-- Functional and injective: a finite partial injection. -/
def WF (m : Renaming) : Prop :=
  (∀ p ∈ m, ∀ q ∈ m, p.1 = q.1 → p.2 = q.2) ∧ (∀ p ∈ m, ∀ q ∈ m, p.2 = q.2 → p.1 = q.1)

instance (m : Renaming) : Decidable m.WF := inferInstanceAs (Decidable (_ ∧ _))

/-- `m⁻¹`. -/
def inv (m : Renaming) : Renaming := m.map Prod.swap

/-- `m ∘ m'`: `s ↦ m(m'(s))`, defined where both steps are. -/
def comp (m m' : Renaming) : Renaming :=
  m'.filterMap fun p => (m.apply p.2).map fun s => (p.1, s)

/-- `m|_A`. -/
def restrict (m : Renaming) (A : List Slot) : Renaming := m.filter fun p => p.1 ∈ A

/-- `id_A`. -/
def id (A : List Slot) : Renaming := A.map fun s => (s, s)

/-- `m_s^r`: `m` with `s` sent to `r` and its previous image for `s`, if any, removed. -/
def update (m : Renaming) (s r : Slot) : Renaming := (s, r) :: m.filter fun p => p.1 != s

/-- Whether `m` is defined on every slot of `A`: the definedness side condition of `m * t`. -/
def Covers (m : Renaming) (A : List Slot) : Prop := ∀ s ∈ A, s ∈ m.dom

instance (m : Renaming) (A : List Slot) : Decidable (m.Covers A) :=
  inferInstanceAs (Decidable (∀ s ∈ A, s ∈ m.dom))

end Renaming

/-! ### The action `m * t` -/

/-- What the action does at one argument position: a binding position receives its fresh
name; a term child is renamed by the map for its position. -/
inductive Plan where
  | fresh (r : Slot)
  | child (m : Renaming)

/-- The fresh names chosen for the binding positions of an application, one per position. -/
abbrev FreshChoice := List (Nat × Slot)

/-- The renaming for the child at position `i` of `f(args)` under `m` with the fresh names
`ρ`: `m` updated, at every bound name `$s` of position `i` whose binder is position `j`, to
`m_s^{ρ(j)}`. A position no binder covers keeps `m`. -/
def childMap (bind : Binders) (m : Renaming) (f : FnName) (args : List Term) (ρ : FreshChoice)
    (i : Nat) : Renaming :=
  (bind f).foldl (fun acc ji =>
    if ji.2 = i then
      match (args[ji.1]?).bind Term.slotName?, ρ.lookup ji.1 with
      | some s, some r => acc.update s r
      | _, _ => acc
    else acc) m

/-- The plan for every position of `f(args)`. -/
def plans (bind : Binders) (m : Renaming) (f : FnName) (args : List Term) (ρ : FreshChoice) :
    List Plan :=
  (List.range args.length).map fun k =>
    match ρ.lookup k with
    | some r => .fresh r
    | none => .child (childMap bind m f args ρ k)

/-- `ρ` chooses one fresh name per binding position of `f`: pairwise distinct, absent from
the term, and outside `dom(m) ∪ img(m)`. -/
def Fresh (bind : Binders) (f : FnName) (args : List Term) (m : Renaming) (ρ : FreshChoice) :
    Prop :=
  (∀ j, bind.isBinding f j = true ↔ j ∈ ρ.map Prod.fst) ∧ (ρ.map Prod.fst).Nodup ∧
    (ρ.map Prod.snd).Nodup ∧
    ∀ r ∈ ρ.map Prod.snd, r ∉ allSlots (.app f args) ∧ r ∉ m.dom ∧ r ∉ m.img

mutual

/-- `Renames m t t'`: `t'` is a result of `m * t`. A slot goes through `m`; a literal stays;
an application gives its binding positions fresh names and renames each child by the map for
its position. The relation holds only when `slots(t) ⊆ dom(m)`, since a free slot outside the
domain has no image. -/
@[blueprint "def:slotted-action"
  (statement := /--
  \[
  \begin{aligned}
  m*\$s&=m(\$s)\\
  m*f(t_1,\ldots,t_n)&=f(t_1',\ldots,t_n')
    \quad\text{for pairwise distinct fresh names $\$r_j$ at the binding positions $j$,}\\
  t_j'&=\$r_j\quad\text{for }(j,\_)\in\operatorname{bind}(f),\\
  t_i'&=m_i*t_i\quad\text{otherwise, where }
    m_i=m\,{}^{r_{j_1}}_{s_{j_1}}\cdots{}^{r_{j_k}}_{s_{j_k}}\\
  &\phantom{=}\text{for the binders }(j_1,i),\ldots,(j_k,i)\in\operatorname{bind}(f)
    \text{ with }t_{j_l}=\$s_{j_l};\\
  m*\SumZeroTen(\$s,t)&=\SumZeroTen(\$r,m_s^r*t)\quad\text{for example.}
  \end{aligned}
  \]
  -/)
  (latexEnv := "paperfragment")]
inductive Renames (bind : Binders) : Renaming → Term → Term → Prop where
  | slot {m : Renaming} {s s' : Slot} :
      isSlotName s = true → m.apply s = some s' → Renames bind m (Term.slot s) (Term.slot s')
  | lit {m : Renaming} {l : Lit} : Renames bind m (.lit l) (.lit l)
  | app {m : Renaming} {f : FnName} {args args' : List Term} {ρ : FreshChoice} :
      isSlotApp f args = false → Fresh bind f args m ρ →
      RenamesList bind (plans bind m f args ρ) args args' →
      Renames bind m (.app f args) (.app f args')

/-- `Renames` over the arguments, position by position, following the plans. -/
inductive RenamesList (bind : Binders) : List Plan → List Term → List Term → Prop where
  | nil : RenamesList bind [] [] []
  | fresh {r : Slot} {ps : List Plan} {a : Term} {as as' : List Term} :
      RenamesList bind ps as as' →
      RenamesList bind (.fresh r :: ps) (a :: as) (Term.slot r :: as')
  | child {m : Renaming} {ps : List Plan} {a a' : Term} {as as' : List Term} :
      Renames bind m a a' → RenamesList bind ps as as' →
      RenamesList bind (.child m :: ps) (a :: as) (a' :: as')

end

/-- One α-step: a result of the identity on the free slots, which changes bound names only. -/
def AlphaStep (bind : Binders) (t u : Term) : Prop :=
  Renames bind (Renaming.id (slots bind t)) t u

/-- α-equivalence: the equivalence generated by α-steps. The paper identifies α-equivalent
terms through the `Rename` rule, whose two sides may use different fresh names. -/
def AlphaEq (bind : Binders) : Term → Term → Prop := Relation.EqvGen (AlphaStep bind)

end Egglog.Slotted
