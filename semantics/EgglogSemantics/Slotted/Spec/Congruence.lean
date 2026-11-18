import EgglogSemantics.Spec.Match
import EgglogSemantics.Slotted.Spec.Slots

/-!
# Slotted congruence

`SCong bind db a b` is the plain congruence closure of the asserted equations, closed in
addition under renaming: the paper's `Rename` rule. Every slot term exists outright, since a
slot is a name rather than a row, and congruence replaces term children only: a binding
position is a field of the head. From the closure come the redundant slots of a term (the
slots the class does not depend on), the live free slots `FS`, the representatives closed
under renaming `reps'`, the live terms `live'`, and the slotted meaning of a state.
-/

namespace Egglog.Slotted

mutual

/-- The slotted congruence closure: the plain rules, reflexivity of slot terms, and
`Rename`, which closes known equations under every renaming defined on both sides. The two
sides may use different fresh bound names, so α-equivalent spellings of an existing term are
congruent. -/
@[blueprint "def:slotted-congruence"
  (statement := /--
  \begin{mathpar}
  \ir{Rename}{t\sim_E u\\
    \operatorname{slots}(t)\cup\operatorname{slots}(u)\subseteq\operatorname{dom}(m)}
    {m*t\sim_E m*u}
  \end{mathpar}
  -/)
  (latexEnv := "paperfragment")]
inductive SCong (bind : Binders) (db : Database) : Term → Term → Prop where
  | direct {a b : Term} : (a, b) ∈ db.eqs → SCong bind db a b
  | slot {s : Slot} : isSlotName s = true → SCong bind db (Term.slot s) (Term.slot s)
  /-- A child of an existing application exists; by induction, so does every subterm. -/
  | child {f : FnName} {as : List Term} {s : Term} :
      SCong bind db (.app f as) (.app f as) → s ∈ as → SCong bind db s s
  | symm {a b : Term} : SCong bind db a b → SCong bind db b a
  | trans {a b c : Term} : SCong bind db a b → SCong bind db b c → SCong bind db a c
  | congr {f : FnName} {as bs : List Term} :
      SCong bind db (.app f as) (.app f as) →
      SCongArgs bind db f 0 as bs → SCong bind db (.app f as) (.app f bs)
  | rename {m : Renaming} {t u t' u' : Term} :
      SCong bind db t u → m.WF → m.Covers (slots bind t) → m.Covers (slots bind u) →
      Renames bind m t t' → Renames bind m u u' → SCong bind db t' u'

/-- Pointwise `SCong` over the arguments of `f` from position `k`: a term child may change to
a congruent one; a binding position is a field of the head and must agree. -/
inductive SCongArgs (bind : Binders) (db : Database) :
    FnName → Nat → List Term → List Term → Prop where
  | nil {f : FnName} {k : Nat} : SCongArgs bind db f k [] []
  | cons {f : FnName} {k : Nat} {a b : Term} {as bs : List Term} :
      (bind.isBinding f k = true → a = b) → (bind.isBinding f k = false → SCong bind db a b) →
      SCongArgs bind db f (k + 1) as bs → SCongArgs bind db f k (a :: as) (b :: bs)

end

/-! ### Redundant slots -/

/-- `s` is redundant in `t`: renaming `s` alone, to a name `r` fresh for `t`, gives a term
congruent to `t`. `$x·0 ∼ 0` makes `$x` redundant in `$x·0`, since then `$y·0 ∼ 0` too. -/
def Redundant (bind : Binders) (db : Database) (t : Term) (s : Slot) : Prop :=
  ∃ (r : Slot) (t' : Term), isSlotName r = true ∧ r ∉ allSlots t ∧
    Renames bind ((Renaming.id (slots bind t)).update s r) t t' ∧ SCong bind db t t'

/-- `FS(E, t)`: the free slots of `t` that are not redundant, the slots its class depends
on. The free-name guards read it. -/
def liveSlots (bind : Binders) (db : Database) (t : Term) : Set Slot :=
  {s | s ∈ slots bind t ∧ ¬ Redundant bind db t s}

/-! ### Representatives and live terms -/

/-- The least stored spelling of each slotted class, in the term order. -/
def sreps (bind : Binders) (db : Database) : Set Term :=
  {t | t ∈ db.terms ∧ ∀ s ∈ db.terms, SCong bind db s t → ¬ Term.blt s t}

/-- `reps'(E)`: the representatives closed under renaming and α-conversion. A query variable
is bound to one of them: a stored representative under any renaming of its free slots. -/
@[blueprint "def:slotted-reps"
  (statement := /--
  \[
  \begin{gathered}
  \operatorname{reps}'(E)\triangleq
    \{\,m*t\mid t\in\operatorname{reps}(E),\
      \operatorname{slots}(t)\subseteq\operatorname{dom}(m)\,\}
  \\
  \operatorname{live}'(E,X)\triangleq\operatorname{live}(E,X')\quad\text{where}\quad
    X'=\{\,m*u\mid u\in X,\ \operatorname{slots}(u)\subseteq\operatorname{dom}(m)\,\}
  \end{gathered}
  \]
  -/)
  (latexEnv := "paperfragment")]
def reps' (bind : Binders) (db : Database) : Set Term :=
  {t' | ∃ t ∈ sreps bind db, ∃ m : Renaming,
    m.WF ∧ m.Covers (slots bind t) ∧ Renames bind m t t'}

/-- `X'`: the subsumed rows closed under renaming and α-conversion. -/
def subsumed' (bind : Binders) (db : Database) : Set Term :=
  {u' | ∃ u ∈ db.subsumed, ∃ m : Renaming,
    m.WF ∧ m.Covers (slots bind u) ∧ Renames bind m u u'}

/-- Two spellings of one row under the slotted congruence: the same head over congruent term
children and the same binding fields. -/
def SameRow' (bind : Binders) (db : Database) (s t : Term) : Prop :=
  ∃ f as bs, s = .app f as ∧ t = .app f bs ∧ SCongArgs bind db f 0 as bs

/-- `live'(E, X)`: everything that exists under the slotted congruence, in any spelling,
except the subsumed rows closed under renaming, in any spelling. -/
def live' (bind : Binders) (db : Database) : Set Term :=
  {t | SCong bind db t t ∧ ¬ ∃ u ∈ subsumed' bind db, SameRow' bind db t u}

/-- States with the same slotted congruence and the same live terms: the slotted `G ≡ G'`,
which the slotted fixpoint test reads. -/
structure SameMeaning' (bind : Binders) (d₁ d₂ : Database) : Prop where
  congr : ∀ a b, SCong bind d₁ a b ↔ SCong bind d₂ a b
  live : ∀ t, t ∈ live' bind d₁ ↔ t ∈ live' bind d₂

end Egglog.Slotted
