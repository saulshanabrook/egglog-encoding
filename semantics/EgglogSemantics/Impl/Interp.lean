import EgglogSemantics.Impl.Closure
import EgglogSemantics.Spec.Match

/-!
# A finite reference interpreter

`FDatabase` stores held terms, asserted equations and subsumed rows. `exec` runs a program's
schedule from the empty state; `FDatabase.holds` decides its final check. Matching binds
variables to class representatives and reads live rows. Each round matches against the
pre-state, then adds every successful firing's writes and subsumptions, as `RunRules` does.
Saturations use a finite pass budget and return `none` on exhaustion.
-/

namespace Egglog

/-! ### The term index -/
/-- An application the database holds, keyed by its head: the row of a relation, or the
node of a constructor. -/
@[ext]
structure Row where
  fn : FnName
  args : List Term
  deriving DecidableEq

/-- The row of `t`'s root, if it has one. -/
def Term.ctorRow : Term → List Row
  | .lit _ => []
  | .app f as => [⟨f, as⟩]

/-- The rows of all of `t`'s subterms, in `subtermList`'s order. -/
def Term.ctorRowList (t : Term) : List Row :=
  t.subtermList.flatMap Term.ctorRow

mutual

/-- The subterms of `t` that neither `ts` nor `new` holds, consed onto `new`, newest first,
visiting nothing below a term `ts` holds. Every list the interpreter builds is closed under
subterms (`FDatabase.Closed`), so nothing below a recorded term is missing. -/
def Term.record (ts : List Term) : Term → List Term → List Term
  | t, new =>
    if t ∈ ts || t ∈ new then new else
      t :: match t with
        | .lit _ => new
        | .app _ args => Term.recordArgs ts args new

/-- `Term.record` over an argument list, first argument first, so that it ends up deepest:
`subtermList`'s reverse creation order. -/
def Term.recordArgs (ts : List Term) : List Term → List Term → List Term
  | [], new => new
  | a :: as, new => Term.recordArgs ts as (Term.record ts a new)

end

namespace Term

/-- A term list closed under subterms. -/
def ListClosed (ts : List Term) : Prop := ∀ t ∈ ts, ∀ s ∈ t.subtermList, s ∈ ts

theorem record_of_mem {ts : List Term} {t : Term} (new : List Term) (h : t ∈ ts) :
    record ts t new = new := by
  unfold record; rw [if_pos (by simp [h])]

/-- `t` is recorded, unless it was already. -/
theorem self_mem_record (ts : List Term) (t : Term) (new : List Term) :
    t ∈ ts ∨ t ∈ record ts t new := by
  unfold record; split
  · rename_i h
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact Or.inl (of_decide_eq_true h)
    · exact Or.inr (of_decide_eq_true h)
  · exact Or.inr (List.mem_cons_self ..)

mutual

/-- Recording keeps everything recorded so far. -/
theorem record_mono (ts : List Term) : ∀ (t : Term) (new : List Term),
    ∀ s ∈ new, s ∈ record ts t new
  | .lit _, new, s, hs => by
    unfold record; split
    · exact hs
    · exact List.mem_cons_of_mem _ hs
  | .app _ args, new, s, hs => by
    unfold record; split
    · exact hs
    · exact List.mem_cons_of_mem _ (recordArgs_mono ts args new s hs)

theorem recordArgs_mono (ts : List Term) : ∀ (as : List Term) (new : List Term),
    ∀ s ∈ new, s ∈ recordArgs ts as new
  | [], _, _, hs => hs
  | a :: as, new, s, hs => recordArgs_mono ts as (record ts a new) s (record_mono ts a new s hs)

end

mutual

/-- Recording adds only subterms of `t`. -/
theorem mem_record (ts : List Term) : ∀ (t : Term) (new : List Term) {s : Term},
    s ∈ record ts t new → s ∈ t.subtermList ∨ s ∈ new
  | .lit _, new, s, hs => by
    unfold record at hs; split at hs
    · exact Or.inr hs
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact Or.inl (List.mem_cons_self ..)
      · exact Or.inr hs
  | .app _ args, new, s, hs => by
    unfold record at hs; split at hs
    · exact Or.inr hs
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact Or.inl (List.mem_cons_self ..)
      · rcases mem_recordArgs ts args new hs with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h

theorem mem_recordArgs (ts : List Term) : ∀ (as : List Term) (new : List Term) {s : Term},
    s ∈ recordArgs ts as new → s ∈ subtermListL as ∨ s ∈ new
  | [], _, _, hs => Or.inr hs
  | a :: as, new, s, hs => by
    rcases mem_recordArgs ts as (record ts a new) hs with h | h
    · exact Or.inl (List.mem_append_left _ h)
    · rcases mem_record ts a new h with h | h
      · exact Or.inl (List.mem_append_right _ h)
      · exact Or.inr h

end

mutual

/-- Onto a closed list, recording records every subterm of `t`, and the list stays
closed. -/
theorem record_spec (ts : List Term) : ∀ (t : Term) (new : List Term),
    ListClosed (new ++ ts) →
    ListClosed (record ts t new ++ ts) ∧ ∀ s ∈ t.subtermList, s ∈ record ts t new ++ ts
  | .lit _, new, hc => by
    unfold record; split
    · rename_i h
      refine ⟨hc, fun s hs => ?_⟩
      rw [List.mem_singleton.mp hs]
      rcases (Bool.or_eq_true _ _).mp h with h | h
      · exact List.mem_append_right _ (of_decide_eq_true h)
      · exact List.mem_append_left _ (of_decide_eq_true h)
    · refine ⟨fun u hu s hs => ?_, fun s hs => ?_⟩
      · rcases List.mem_cons.mp hu with rfl | hu
        · rw [List.mem_singleton.mp hs]; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hc u hu s hs)
      · rw [List.mem_singleton.mp hs]; exact List.mem_cons_self ..
  | .app f args, new, hc => by
    unfold record; split
    · rename_i h
      refine ⟨hc, fun s hs => ?_⟩
      have ht : Term.app f args ∈ new ++ ts := by
        rcases (Bool.or_eq_true _ _).mp h with h | h
        · exact List.mem_append_right _ (of_decide_eq_true h)
        · exact List.mem_append_left _ (of_decide_eq_true h)
      exact hc _ ht s hs
    · obtain ⟨hc', hsub⟩ := recordArgs_spec ts args new hc
      refine ⟨fun u hu s hs => ?_, fun s hs => ?_⟩
      · rcases List.mem_cons.mp hu with rfl | hu
        · rcases List.mem_cons.mp hs with rfl | hs
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (hsub s hs)
        · exact List.mem_cons_of_mem _ (hc' u hu s hs)
      · rcases List.mem_cons.mp hs with rfl | hs
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hsub s hs)

theorem recordArgs_spec (ts : List Term) : ∀ (as : List Term) (new : List Term),
    ListClosed (new ++ ts) →
    ListClosed (recordArgs ts as new ++ ts) ∧
      ∀ s ∈ subtermListL as, s ∈ recordArgs ts as new ++ ts
  | [], _, hc => ⟨hc, fun _ hs => by simp [subtermListL] at hs⟩
  | a :: as, new, hc => by
    obtain ⟨hc₁, h₁⟩ := record_spec ts a new hc
    obtain ⟨hc₂, h₂⟩ := recordArgs_spec ts as (record ts a new) hc₁
    refine ⟨hc₂, fun s hs => ?_⟩
    rcases List.mem_append.mp hs with hs | hs
    · exact h₂ s hs
    · rcases List.mem_append.mp (h₁ s hs) with h | h
      · exact List.mem_append_left _ (recordArgs_mono ts as _ s h)
      · exact List.mem_append_right _ h

end

/-- A subterm of a member of an argument list is in the list's subterms. -/
theorem mem_subtermListL_of_mem {s a : Term} : ∀ {args : List Term}, a ∈ args →
    s ∈ a.subtermList → s ∈ Term.subtermListL args
  | [], h, _ => by simp at h
  | b :: bs, h, hs => by
      simp only [Term.subtermListL]
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_append_right _ hs
      · exact List.mem_append_left _ (mem_subtermListL_of_mem h hs)

/-- `IsSubterm` lands in `subtermList`, which is what subterm closure of a list is about. -/
theorem mem_subtermList_of_isSubterm : ∀ {s t : Term}, Term.IsSubterm s t →
    s ∈ t.subtermList
  | _, _, .refl t => by cases t <;> exact List.mem_cons_self ..
  | _, _, .arg ha h =>
      List.mem_cons_of_mem _ (mem_subtermListL_of_mem ha (mem_subtermList_of_isSubterm h))

/-- Every term is its own subterm. -/
theorem self_mem_subtermList (t : Term) : t ∈ t.subtermList := by
  cases t <;> exact List.mem_cons_self ..

end Term

/-! ### Finite databases -/
/-- The executable counterpart of `Database`. Every component is a `List`; membership,
not multiplicity or order, is what it denotes. -/
structure FDatabase where
  terms : List Term
  /-- The index: one row per held application, subsumed or not. -/
  rows : List Row
  eqs : List (Term × Term)
  /-- The subsumed rows, as written; a spelling with congruent children counts as subsumed
  too (`FDatabase.isSubsumed`). -/
  subsumed : List Term

namespace FDatabase
/-- Project into the mathematical assertion store. Under implicit subterm existence and
congruent spellings, the projection's term set is the list only when the list is closed
under subterms; the lemmas relating the two belong with the proofs. -/
def toDatabase (d : FDatabase) : Database where
  eqs := {p | p.1 = p.2 ∧ p.1 ∈ d.terms} ∪
    {p | p ∈ d.eqs ∧ p.1 ∈ d.terms ∧ p.2 ∈ d.terms}
  subsumed := {t | t ∈ d.subsumed}

/-- The initial database. -/
def empty : FDatabase where
  terms := []
  rows := []
  eqs := []
  subsumed := []

/-- Insert `t` and all of its subterms, and index the applications among them.

`Term.record` stops at a subterm the list already holds, which is what keeps this linear in
what is new rather than in the size of `t`'s tree. `FDatabase.Closed`, which every state
the interpreter builds satisfies, is what makes that exact: `mem_addTerm_terms` reads
precisely `t.subtermList` back. -/
def addTerm (t : Term) (d : FDatabase) : FDatabase :=
  let new := Term.record d.terms t []
  { d with terms := new ++ d.terms, rows := new.flatMap Term.ctorRow ++ d.rows }

@[simp] theorem addTerm_eqs {d : FDatabase} {t : Term} : (d.addTerm t).eqs = d.eqs := rfl

/-- The term list is closed under subterms. Every state the interpreter builds satisfies
it; `addTerm` relies on it to stop at a recorded subterm. -/
def SubtermClosed (d : FDatabase) : Prop := Term.ListClosed d.terms

theorem mem_addTerm_terms_imp {d : FDatabase} {t s : Term} (h : s ∈ (d.addTerm t).terms) :
    s ∈ t.subtermList ∨ s ∈ d.terms := by
  rcases List.mem_append.mp h with h | h
  · rcases Term.mem_record d.terms t [] h with h | h
    · exact Or.inl h
    · simp at h
  · exact Or.inr h

/-- A term the list held it still holds. -/
theorem mem_addTerm_of_mem {d : FDatabase} {t s : Term} (hs : s ∈ d.terms) :
    s ∈ (d.addTerm t).terms :=
  List.mem_append_right _ hs

theorem self_mem_addTerm (d : FDatabase) (t : Term) : t ∈ (d.addTerm t).terms := by
  rcases Term.self_mem_record d.terms t [] with h | h
  · exact List.mem_append_right _ h
  · exact List.mem_append_left _ h

/-- Under subterm closure, `addTerm` records exactly the subterms of `t`. -/
theorem mem_addTerm_terms {d : FDatabase} (hc : d.SubtermClosed) {t s : Term} :
    s ∈ (d.addTerm t).terms ↔ s ∈ t.subtermList ∨ s ∈ d.terms :=
  ⟨mem_addTerm_terms_imp, fun h =>
    h.elim ((Term.record_spec d.terms t [] hc).2 s) mem_addTerm_of_mem⟩

/-- Subterm closure survives an `addTerm`. -/
theorem SubtermClosed.addTerm {d : FDatabase} (hc : d.SubtermClosed) (t : Term) :
    (d.addTerm t).SubtermClosed :=
  (Term.record_spec d.terms t [] hc).1

theorem mem_addTerm_rows_imp {d : FDatabase} {t : Term} {r : Row}
    (h : r ∈ (d.addTerm t).rows) : r ∈ t.ctorRowList ∨ r ∈ d.rows := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨s, hs, hr⟩ := List.mem_flatMap.mp h
    rcases Term.mem_record d.terms t [] hs with hs | hs
    · exact Or.inl (List.mem_flatMap.mpr ⟨s, hs, hr⟩)
    · simp at hs
  · exact Or.inr h

/-- A row the index held it still holds. -/
theorem mem_addTerm_rows_of_mem {d : FDatabase} {t : Term} {r : Row} (h : r ∈ d.rows) :
    r ∈ (d.addTerm t).rows :=
  List.mem_append_right _ h

/-- A term the list holds adds nothing. -/
theorem addTerm_of_mem {d : FDatabase} {t : Term} (h : t ∈ d.terms) : d.addTerm t = d := by
  unfold addTerm
  rw [Term.record_of_mem [] h]
  rfl

/-- `addTerm` over a list. -/
def addTerms (ts : List Term) (d : FDatabase) : FDatabase :=
  ts.foldl (fun e t => e.addTerm t) d

/-- Assert `a = b`, inserting both terms. -/
def addEq (a b : Term) (d : FDatabase) : FDatabase :=
  { (d.addTerm a).addTerm b with eqs := ((a, b) :: d.eqs).dedup }

/-- Subsume the row `t`, inserting it. Each subsumed row is listed once. -/
def subsume (t : Term) (d : FDatabase) : FDatabase :=
  let d' := d.addTerm t
  { d' with subsumed := if d'.subsumed.contains t then d'.subsumed else t :: d'.subsumed }

/-- Union two databases. `Database.sUnion`, computed, at the two-operand shape
`execRunRules` folds with. -/
def union (d₁ d₂ : FDatabase) : FDatabase :=
  { d₁ with terms := (d₁.terms ++ d₂.terms).dedup, rows := (d₁.rows ++ d₂.rows).dedup,
            eqs := (d₁.eqs ++ d₂.eqs).dedup, subsumed := (d₁.subsumed ++ d₂.subsumed).dedup }

/-- The list invariant: every equation names terms the list holds, and the list is closed
under subterms. The first is what makes `toDatabase`'s restriction invisible; the second is
what lets `addTerm` stop at a recorded subterm. -/
structure Closed (d : FDatabase) : Prop where
  eqs : ∀ p ∈ d.eqs, p.1 ∈ d.terms ∧ p.2 ∈ d.terms
  subterms : d.SubtermClosed

theorem empty_closed : Closed empty :=
  ⟨by simp [empty], by simp [SubtermClosed, Term.ListClosed, empty]⟩

/-- `addTerm` only grows `terms`. -/
theorem Closed.addTerm {d : FDatabase} (h : d.Closed) (t : Term) : (d.addTerm t).Closed where
  eqs := fun p hp => ⟨mem_addTerm_of_mem (h.eqs p hp).1, mem_addTerm_of_mem (h.eqs p hp).2⟩
  subterms := h.subterms.addTerm t

/-- **The one writer that introduces a pair**, and it inserts both sides. -/
theorem Closed.addEq {d : FDatabase} (h : d.Closed) (a b : Term) :
    (FDatabase.addEq a b d).Closed where
  eqs := fun p hp => by
    simp only [FDatabase.addEq, List.mem_dedup, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨mem_addTerm_of_mem (self_mem_addTerm d a), self_mem_addTerm _ b⟩
    · exact ⟨mem_addTerm_of_mem (mem_addTerm_of_mem (h.eqs p hp).1),
        mem_addTerm_of_mem (mem_addTerm_of_mem (h.eqs p hp).2)⟩
  subterms := (h.subterms.addTerm a).addTerm b

/-- `union` concatenates `eqs` and `terms` together. -/
theorem Closed.union {d₁ d₂ : FDatabase} (h₁ : d₁.Closed) (h₂ : d₂.Closed) :
    (d₁.union d₂).Closed where
  eqs := fun p hp => by
    simp only [FDatabase.union, List.mem_dedup, List.mem_append] at hp ⊢
    rcases hp with hp | hp
    · exact ⟨Or.inl (h₁.eqs p hp).1, Or.inl (h₁.eqs p hp).2⟩
    · exact ⟨Or.inr (h₂.eqs p hp).1, Or.inr (h₂.eqs p hp).2⟩
  subterms := fun u hu s hs => by
    simp only [FDatabase.union, List.mem_dedup, List.mem_append] at hu ⊢
    rcases hu with hu | hu
    · exact Or.inl (h₁.subterms u hu s hs)
    · exact Or.inr (h₂.subterms u hu s hs)

/-- `terms` as a `Finset`, for the closure. -/
def termsF (d : FDatabase) : Finset Term := d.terms.toFinset

/-- `eqs` as a `Finset`. -/
def eqsF (d : FDatabase) : Finset (Term × Term) := d.eqs.toFinset

/-- The interpreter's invariant, stated on the denotation. -/
def WF (d : FDatabase) : Prop := d.toDatabase.WF

/-- The congruence closure of `d`, computed. -/
def closureF (d : FDatabase) : Finset (Term × Term) := closureTotal d.termsF d.eqsF

/-- Whether two tuples are pointwise congruent. -/
def congrTuple (cl : Finset (Term × Term)) (as bs : List Term) : Bool :=
  as.length == bs.length && (as.zip bs).all fun q => decide (q ∈ cl)

/-- Whether the database already holds every subterm of every one of `ts`, which is when
`addTerms ts` leaves `termsF` — and so `closureF` — alone. -/
def holdsAll (d : FDatabase) (ts : List Term) : Bool :=
  ts.all fun t => t.subtermList.all fun s => decide (s ∈ d.terms)

/-- `Database.reps` under the closure `cl`: the held terms with no held, congruent, smaller
term. These are the values a query variable can take, one per class. -/
def repsWith (cl : Finset (Term × Term)) (d : FDatabase) : List Term :=
  d.terms.filter fun t => !(d.terms.any fun s => decide ((s, t) ∈ cl) && Term.blt s t)

/-- `Database.reps`, computed. -/
def reps (d : FDatabase) : List Term := d.repsWith d.closureF

theorem mem_repsWith_terms {cl : Finset (Term × Term)} {d : FDatabase} {t : Term}
    (h : t ∈ d.repsWith cl) : t ∈ d.terms := (List.mem_filter.mp h).1

/-- Whether a held application of `f` has children congruent to `ts` under `cl`. -/
def hasCtorRow (cl : Finset (Term × Term)) (d : FDatabase) (f : FnName) (ts : List Term) :
    Bool :=
  d.rows.any fun r => decide (r.fn = f) && FDatabase.congrTuple cl ts r.args

/-- `Database.SameRow`, computed under `cl`: the same head over congruent children. -/
def sameRow (cl : Finset (Term × Term)) : Term → Term → Bool
  | .app f as, .app g bs => f == g && FDatabase.congrTuple cl as bs
  | _, _ => false

/-- Whether the row `t` is subsumed: some subsumed row has its head and congruent children. -/
def isSubsumed (cl : Finset (Term × Term)) (d : FDatabase) (t : Term) : Bool :=
  d.subsumed.any fun u => FDatabase.sameRow cl t u

end FDatabase

/-! ### Enumerating substitutions -/
/-- Every assignment of `vars` to `terms`, with the domain in `vars`' order. -/
def assignments (terms : List Term) : List Var → List Env
  | [] => [[]]
  | v :: vs => terms.flatMap fun t => (assignments terms vs).map fun σ => (v, t) :: σ

/-- `σ` cut down to `vars` and put in `vars`' order. Used both to canonicalize a
substitution the spec produced and to restrict a query substitution to one pattern. -/
def Env.canon (vars : List Var) (σ : Env) : Env :=
  vars.filterMap fun v => (Env.lookup v σ).map fun t => (v, t)

/-! ### E-matching -/
/-- The free variables of a query: the variables the enumerator assigns. -/
def Query.freeVars (q : Query) (σ : Env) : List Var :=
  q.foldr (fun p acc => p.freeVars σ ∪ acc) []

/-- An application's head and operands; `none` for anything else. -/
def Expr.ctorAtom : Expr → Option (FnName × List Expr)
  | .app f args => some (f, args)
  | _ => none

/-! #### Matching under a supplied closure

The tests below take the store's congruence closure `cl`. Pattern operands may denote
unstored terms; `closureWith` extends the store with those instances for comparison. -/

/-- `(d.addTerms ts).closureF`, given `d`'s own closure `cl` to reuse where `ts` adds
nothing. `closureWith_eq` is the equation; nothing else should call this with a `cl` that is
not `d.closureF`. -/
def FDatabase.closureWith (cl : Finset (Term × Term)) (d : FDatabase) (ts : List Term) :
    Finset (Term × Term) :=
  if d.holdsAll ts then cl else (d.addTerms ts).closureF

/-- `Database.live`, computed under `cl`: the instance is congruent to a held term in the
store extended with it, and no subsumed row has its head and congruent children. -/
def FDatabase.liveWith (cl : Finset (Term × Term)) (d : FDatabase) (t : Term) : Bool :=
  match t with
  | .app f ts =>
    if d.holdsAll ts then d.hasCtorRow cl f ts && !d.isSubsumed cl t
    else
      let cl' := d.closureWith cl [t]
      decide (∃ w ∈ d.terms, (w, t) ∈ cl') && !d.isSubsumed cl' t
  | .lit _ =>
    let cl' := d.closureWith cl [t]
    decide (∃ w ∈ d.terms, (w, t) ∈ cl')

mutual

/-- `Expr.Matches`, computed under `cl`: the expression evaluates and every application it
reads is live. -/
def exprHoldsWith (cl : Finset (Term × Term)) (d : FDatabase) (σ : Env) : Expr → Bool
  | .lit l => d.liveWith cl (.lit l)
  | .var v => (Env.lookup v σ).isSome
  | .app f args =>
      exprsHoldWith cl d σ args &&
        match Expr.evalList args σ with
        | some ts => d.liveWith cl (.app f ts)
        | none => false
  | .min a b => exprHoldsWith cl d σ a && exprHoldsWith cl d σ b

/-- `exprHoldsWith` over an argument list. -/
def exprsHoldWith (cl : Finset (Term × Term)) (d : FDatabase) (σ : Env) : List Expr → Bool
  | [] => true
  | e :: es => exprHoldsWith cl d σ e && exprsHoldWith cl d σ es

end

/-- `Matches`, computed under `cl`: a pattern that is an expression holds as that
expression; an equality or disequality needs both sides to hold and compares them through
the closure of the store extended with the instances. -/
def patternHoldsWith (cl : Finset (Term × Term)) (d : FDatabase) (p : Pattern) (σ : Env) :
    Bool :=
  match p with
  | .expr e => exprHoldsWith cl d σ e
  | .eq e₁ e₂ =>
    exprHoldsWith cl d σ e₁ && exprHoldsWith cl d σ e₂ &&
      match e₁.eval σ, e₂.eval σ with
      | some t₁, some t₂ => decide ((t₁, t₂) ∈ d.closureWith cl [t₁, t₂])
      | _, _ => false
  | .ne e₁ e₂ =>
    exprHoldsWith cl d σ e₁ && exprHoldsWith cl d σ e₂ &&
      match e₁.eval σ, e₂.eval σ with
      | some t₁, some t₂ => !decide ((t₁, t₂) ∈ d.closureWith cl [t₁, t₂])
      | _, _ => false

/-- `patternHoldsWith` at the store's own closure, which computes exactly the
specification's `Cong`. -/
def patternHolds (d : FDatabase) (p : Pattern) (σ : Env) : Bool :=
  patternHoldsWith d.closureF d p σ

/-- The substitutions satisfying a whole query: every variable bound to a representative. -/
def matchQuery (d : FDatabase) (q : Query) : List Env :=
  (assignments d.reps (Query.freeVars q [])).filter fun σ =>
    q.all fun p => patternHolds d p (Env.canon (p.freeVars []) σ)

/-! ### Matching with a shared closure

`matchQueryWith` uses the store's closure for held instances and extends it for unstored
ones. Its result agrees with `matchQuery`. -/

/-- `addTerm` only grows `terms`. -/
theorem FDatabase.mem_terms_addTerm {d : FDatabase} {t s : Term} (h : s ∈ d.terms) :
    s ∈ (d.addTerm t).terms :=
  FDatabase.mem_addTerm_of_mem h

/-- **A term the database already holds adds nothing to the candidate universe.** -/
theorem FDatabase.termsF_addTerm_of_mem {d : FDatabase} {t : Term}
    (h : ∀ s ∈ t.subtermList, s ∈ d.terms) : (d.addTerm t).termsF = d.termsF := by
  rw [FDatabase.addTerm_of_mem (h t (Term.self_mem_subtermList t))]

/-- …and so nothing to the closure, `addTerm` not touching `eqs`. -/
theorem FDatabase.closureF_addTerm_of_mem {d : FDatabase} {t : Term}
    (h : ∀ s ∈ t.subtermList, s ∈ d.terms) : (d.addTerm t).closureF = d.closureF := by
  unfold FDatabase.closureF
  rw [FDatabase.termsF_addTerm_of_mem h]
  rfl

/-- `addTerms` over a list the database already holds, likewise. -/
theorem FDatabase.closureF_addTerms_of_mem {ts : List Term} : ∀ {d : FDatabase},
    (∀ t ∈ ts, ∀ s ∈ t.subtermList, s ∈ d.terms) →
    (d.addTerms ts).closureF = d.closureF := by
  induction ts with
  | nil => intro _ _; rfl
  | cons t ts ih =>
    intro d h
    have hstep : ∀ u ∈ ts, ∀ s ∈ u.subtermList, s ∈ (d.addTerm t).terms := fun u hu s hs =>
      FDatabase.mem_terms_addTerm (h u (List.mem_cons_of_mem _ hu) s hs)
    calc (d.addTerms (t :: ts)).closureF = ((d.addTerm t).addTerms ts).closureF := rfl
      _ = (d.addTerm t).closureF := ih hstep
      _ = d.closureF := FDatabase.closureF_addTerm_of_mem (h t (List.mem_cons_self ..))

/-- `addTerms` over a concatenation is `addTerms` twice. -/
theorem FDatabase.addTerms_append (d : FDatabase) (ts us : List Term) :
    d.addTerms (ts ++ us) = (d.addTerms ts).addTerms us :=
  List.foldl_append ..

/-- **What the reuse is allowed to be.** -/
theorem FDatabase.closureWith_eq (d : FDatabase) (ts : List Term) :
    d.closureWith d.closureF ts = (d.addTerms ts).closureF := by
  unfold FDatabase.closureWith
  split
  · rename_i h
    simp only [FDatabase.holdsAll, List.all_eq_true, decide_eq_true_eq] at h
    exact (FDatabase.closureF_addTerms_of_mem h).symm
  · rfl

/-- At `d`'s own closure it is `patternHolds`, by definition. -/
theorem patternHoldsWith_eq (d : FDatabase) (p : Pattern) (σ : Env) :
    patternHoldsWith d.closureF d p σ = patternHolds d p σ := rfl

/-- `matchQuery` with the closure computed once, as a parameter. -/
def matchQueryWith (cl : Finset (Term × Term)) (d : FDatabase) (q : Query) : List Env :=
  (assignments (d.repsWith cl) (Query.freeVars q [])).filter fun σ =>
    q.all fun p => patternHoldsWith cl d p (Env.canon (p.freeVars []) σ)

def matchQueryFast (d : FDatabase) (q : Query) : List Env :=
  matchQueryWith d.closureF d q

/-- At `d`'s own closure, `matchQueryWith` is `matchQuery`. -/
theorem matchQueryWith_eq (d : FDatabase) (q : Query) :
    matchQueryWith d.closureF d q = matchQuery d q := by
  simp only [matchQueryWith, matchQuery, FDatabase.reps, patternHoldsWith_eq]

/-- **The fast path is the slow path**, on the nose. -/
theorem matchQueryFast_eq (d : FDatabase) (q : Query) : matchQueryFast d q = matchQuery d q :=
  matchQueryWith_eq d q

/-! ### Pruning the candidate cross product

`matchQueryWith` assigns every free variable before it checks anything. Nothing of a
candidate reaches a pattern's check but the pattern's **own** variables, so a prefix that
already falsifies a pattern falsifies every extension of it, and those extensions need
never be built. `matchPrune` is the same enumeration, in the same order, with each pattern
checked at the depth that binds its last variable, and `matchPrune_eq` is the equality. -/
/-- The patterns a substitution already decides: those whose free variables it binds. -/
def Query.decided (d : FDatabase) (pre : Env) (q : Query) : Query :=
  q.filter fun p => (p.freeVars []).all fun v => decide (v ∈ Env.dom pre)

/-- `lookup` reads past an extension that cannot rebind. -/
private theorem lookup_append_dom {v : Var} {σ₁ σ₂ : Env} (h : v ∈ Env.dom σ₁) :
    Env.lookup v (σ₁ ++ σ₂) = Env.lookup v σ₁ := by
  induction σ₁ with
  | nil => simp [Env.dom] at h
  | cons b σ ih =>
    obtain ⟨w, t⟩ := b
    by_cases hv : v = w
    · simp [Env.lookup, hv]
    · simp only [Env.dom, List.map_cons, List.mem_cons] at h
      simp [Env.lookup, hv, ih (h.resolve_left hv)]

/-- A pattern's operand environment does not move once its variables are bound. -/
theorem Env.canon_append_of_dom {vars : List Var} {pre σ : Env}
    (h : ∀ v ∈ vars, v ∈ Env.dom pre) : Env.canon vars (pre ++ σ) = Env.canon vars pre := by
  induction vars with
  | nil => rfl
  | cons w ws ih =>
    have hw := lookup_append_dom (σ₂ := σ) (h w List.mem_cons_self)
    have hws := ih fun v hv => h v (List.mem_cons_of_mem _ hv)
    simp only [Env.canon, List.filterMap_cons, hw] at *
    rw [hws]

/-- `filter` distributes over `flatMap`. -/
private theorem filter_flatMap {α β : Type} (p : β → Bool) (f : α → List β) (l : List α) :
    (l.flatMap f).filter p = l.flatMap fun a => (f a).filter p := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.filter_append, ih]

/-- `filter` past a `map`, as the composed predicate. -/
private theorem filter_map_comp {α β : Type} (p : β → Bool) (f : α → β) (l : List α) :
    (l.map f).filter p = (l.filter fun a => p (f a)).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p (f a) <;> simp [h, ih]

/-- The enumeration of `vs` out of `ts`, extending `pre`, with every decided pattern checked
as it is decided. -/
def matchPrune (cl : Finset (Term × Term)) (d : FDatabase) (q : Query) (ts : List Term)
    (pre : Env) : List Var → List Env
  | [] =>
      if q.all fun p => patternHoldsWith cl d p (Env.canon (p.freeVars []) pre) then [[]]
      else []
  | v :: vs =>
      ts.flatMap fun t =>
        let pre' := pre ++ [(v, t)]
        if (Query.decided d pre' q).all fun p =>
              patternHoldsWith cl d p (Env.canon (p.freeVars []) pre') then
          (matchPrune cl d q ts pre' vs).map fun σ => (v, t) :: σ
        else []

/-- **Pruning drops exactly the candidates the final filter would have.** -/
theorem matchPrune_eq (cl : Finset (Term × Term)) (d : FDatabase) (q : Query)
    (ts : List Term) :
    ∀ (vs : List Var) (pre : Env), matchPrune cl d q ts pre vs
      = (assignments ts vs).filter fun σ =>
          q.all fun p => patternHoldsWith cl d p (Env.canon (p.freeVars []) (pre ++ σ)) := by
  intro vs
  induction vs with
  | nil =>
    intro pre
    simp [matchPrune, assignments, List.filter_cons, List.append_nil]
  | cons v vs ih =>
    intro pre
    rw [matchPrune, assignments, filter_flatMap]
    refine List.flatMap_congr fun t _ => ?_
    rw [filter_map_comp]
    by_cases hg : (Query.decided d (pre ++ [(v, t)]) q).all fun p =>
        patternHoldsWith cl d p (Env.canon (p.freeVars []) (pre ++ [(v, t)]))
    · rw [if_pos hg, ih (pre ++ [(v, t)])]
      congr 1
      refine List.filter_congr fun σ _ => ?_
      simp only [List.append_assoc, List.singleton_append]
    · -- the prefix already falsifies a pattern, so no extension of it survives
      have hnil : ((assignments ts vs).filter fun σ =>
          q.all fun p => patternHoldsWith cl d p
            (Env.canon (p.freeVars []) (pre ++ (v, t) :: σ))) = [] := by
        rw [Bool.not_eq_true, List.all_eq_false] at hg
        obtain ⟨p, hp, hfail⟩ := hg
        obtain ⟨hpq, hdecB⟩ := List.mem_filter.mp hp
        have hdec : ∀ w ∈ p.freeVars [], w ∈ Env.dom (pre ++ [(v, t)]) := fun w hw =>
          of_decide_eq_true (List.all_eq_true.mp hdecB w hw)
        refine List.filter_eq_nil_iff.mpr fun σ _ hall => hfail ?_
        have hp' := List.all_eq_true.mp hall p hpq
        rw [show pre ++ (v, t) :: σ = (pre ++ [(v, t)]) ++ σ by simp,
          Env.canon_append_of_dom hdec] at hp'
        exact hp'
      rw [if_neg hg, hnil, List.map_nil]

/-- `matchQueryWith`, pruned. -/
def matchQueryPruned (cl : Finset (Term × Term)) (d : FDatabase) (q : Query) : List Env :=
  matchPrune cl d q (d.repsWith cl) [] (Query.freeVars q [])

theorem matchQueryPruned_eq (cl : Finset (Term × Term)) (d : FDatabase) (q : Query) :
    matchQueryPruned cl d q = matchQueryWith cl d q := by
  rw [matchQueryPruned, matchPrune_eq, matchQueryWith]
  simp

/-- The pruned enumeration is `matchQueryWith`. Compiled code goes to `matchQueryJoin`
below, which narrows this one's candidate lists and is proved equal through it. -/
theorem matchQueryWith_eq_pruned : @matchQueryWith = @matchQueryPruned := by
  funext cl d q
  exact (matchQueryPruned_eq cl d q).symm

/-! ### Joining over the index

`matchJoin` narrows variable candidates using application rows compatible with the bound
prefix. A join requires determined operands, held operand values and held candidates.
Nested application reads can constrain variables before the enclosing application is
determined. `matchJoin_eq` establishes agreement with `matchPrune`. -/
/-- What a join reads off one operand: a literal's own term, or a variable's binding.
`none` at an operand the prefix has yet to determine, and at `min`. An application
can be read once its variables are bound; `joinPlan` also checks that its value is held. -/
def joinOperand (ρ : Env) : Expr → Option Term
  | .lit l => some (.lit l)
  | .var w => Env.lookup w ρ
  | .app f as => Expr.eval (.app f as) ρ
  | .min _ _ => none

/-- `joinOperand` over an atom's operand list. -/
def joinKnown (ρ : Env) (es : List Expr) : List (Option Term) := es.map (joinOperand ρ)

mutual

/-- An operand a join can read structurally; ordering operations are excluded. -/
def joinExprDrivable : Expr → Bool
  | .lit _ | .var _ => true
  | .app _ as => joinDrivable as
  | .min _ _ => false

/-- Whether all operands, including their nested applications, avoid `min`. -/
def joinDrivable : List Expr → Bool
  | [] => true
  | e :: es => joinExprDrivable e && joinDrivable es

end

/-- Application operands must already have a value before the enclosing row is read.
Their recursive reads can drive the still-unbound variables independently. -/
def joinReady (ρ : Env) (es : List Expr) : Bool :=
  es.all fun e => match e with
    | .app f as => (Expr.eval (.app f as) ρ).isSome
    | .min _ _ => false
    | _ => true

/-- Whether a row is consistent with what the operands are known to be: at every determined
operand, the row's column there is congruent to it. -/
def joinConsistent (cl : Finset (Term × Term)) (ks : List (Option Term)) (xs : List Term) :
    Bool :=
  ks.length == xs.length && (ks.zip xs).all fun p =>
    match p.1 with
    | none => true
    | some t => decide ((t, p.2) ∈ cl)

/-- One atom, ready to narrow. -/
structure JoinAtom where
  /-- The atom's free variables — `Pattern.freeVars`, computed once. -/
  vars : List Var
  /-- The operands. -/
  keys : List Expr
  /-- The rows the prefix has not ruled out, rescanned for every candidate. -/
  rows : List Row

/-- One application read as a narrowing step. The environment is restricted to the
original pattern's variables, also for plans obtained from nested reads. -/
def joinAtomPlan (cl : Finset (Term × Term)) (d : FDatabase) (pre : Env) (v : Var)
    (vars : List Var) (f : FnName) (as : List Expr) : Option JoinAtom :=
  let ρ := Env.canon vars pre
  if joinDrivable as && joinReady ρ as &&
      (as.any fun e => match e with | .var w => w == v | _ => false) then
    let ka := joinKnown ρ as
    if d.holdsAll (ka.filterMap id) then
      some ⟨vars, as,
        d.rows.filter fun r =>
          (r.fn == f) && !d.subsumed.contains (.app r.fn r.args) && joinConsistent cl ka r.args⟩
    else none
  else none

mutual

/-- The application reads required by a matching expression, including nested reads. -/
def joinExprPlans (cl : Finset (Term × Term)) (d : FDatabase) (pre : Env) (v : Var)
    (vars : List Var) : Expr → List JoinAtom
  | .app f as =>
      (joinAtomPlan cl d pre v vars f as).toList ++ joinArgsPlans cl d pre v vars as
  | _ => []

def joinArgsPlans (cl : Finset (Term × Term)) (d : FDatabase) (pre : Env) (v : Var)
    (vars : List Var) : List Expr → List JoinAtom
  | [] => []
  | e :: es => joinExprPlans cl d pre v vars e ++ joinArgsPlans cl d pre v vars es

end

/-- The application reads of an expression atom; equality and ordering do not drive. -/
def joinPlan (cl : Finset (Term × Term)) (d : FDatabase) (pre : Env) (v : Var) :
    Pattern → List JoinAtom
  | .expr e => joinExprPlans cl d pre v ((Pattern.expr e).freeVars []) e
  | _ => []

/-- Whether the atom's surviving rows still admit `v ↦ t`. -/
def JoinAtom.keeps (a : JoinAtom) (cl : Finset (Term × Term)) (pre : Env)
    (v : Var) (t : Term) : Bool :=
  let ρ := Env.canon a.vars (pre ++ [(v, t)])
  a.rows.any fun r => joinConsistent cl (joinKnown ρ a.keys) r.args

/-- The candidates for `v` under `pre`: `ts`, narrowed by every atom the index can drive,
fewest surviving rows first. `held` is `d.holdsAll ts`, computed once per query. -/
def joinCands (cl : Finset (Term × Term)) (d : FDatabase) (q : Query) (held : Bool)
    (ts : List Term) (pre : Env) (v : Var) : List Term :=
  if held then
    let plans := (q.flatMap (joinPlan cl d pre v)).mergeSort fun a b =>
      decide (a.rows.length ≤ b.rows.length)
    ts.filter fun t => plans.all fun a => a.keeps cl pre v t
  else ts

/-- `matchPrune`'s enumeration, with each variable's candidates read off the index. -/
def matchJoin (cl : Finset (Term × Term)) (d : FDatabase) (q : Query) (ts : List Term)
    (held : Bool) (pre : Env) : List Var → List Env
  | [] =>
      if q.all fun p => patternHoldsWith cl d p (Env.canon (p.freeVars []) pre) then [[]]
      else []
  | v :: vs =>
      (joinCands cl d q held ts pre v).flatMap fun t =>
        let pre' := pre ++ [(v, t)]
        if (Query.decided d pre' q).all fun p =>
              patternHoldsWith cl d p (Env.canon (p.freeVars []) pre') then
          (matchJoin cl d q ts held pre' vs).map fun σ => (v, t) :: σ
        else []

/-! #### That the narrowing drops nothing

A candidate some full substitution satisfies the query on is one every atom's rows admit,
so the filter keeps it. The converse is not asked for; the final check is still
`patternHoldsWith`'s. -/
/-- `lookup` reads past a prefix that binds. -/
private theorem lookup_append_some {w : Var} {t : Term} {σ₁ σ₂ : Env}
    (h : Env.lookup w σ₁ = some t) : Env.lookup w (σ₁ ++ σ₂) = some t := by
  induction σ₁ with
  | nil => simp [Env.lookup] at h
  | cons b σ ih =>
    obtain ⟨u, s⟩ := b
    simp only [List.cons_append, Env.lookup] at h ⊢
    by_cases hw : w = u
    · simp only [if_pos hw] at h ⊢; exact h
    · simp only [if_neg hw] at h ⊢; exact ih h

/-- `lookup` reads past a prefix that does not bind. -/
private theorem lookup_append_none {w : Var} {σ₁ σ₂ : Env} (h : Env.lookup w σ₁ = none) :
    Env.lookup w (σ₁ ++ σ₂) = Env.lookup w σ₂ := by
  induction σ₁ with
  | nil => rfl
  | cons b σ ih =>
    obtain ⟨u, s⟩ := b
    simp only [List.cons_append, Env.lookup] at h ⊢
    by_cases hw : w = u
    · simp only [if_pos hw] at h; exact absurd h (by simp)
    · simp only [if_neg hw] at h ⊢; exact ih h

/-- **`Env.canon` is a restriction and nothing else**: it forgets the variables outside
`vars` and moves none of the others. -/
theorem Env.lookup_canon_eq (vars : List Var) (ρ : Env) (w : Var) :
    Env.lookup w (Env.canon vars ρ) = if w ∈ vars then Env.lookup w ρ else none := by
  induction vars with
  | nil => simp [Env.canon, Env.lookup]
  | cons u us ih =>
    simp only [Env.canon, List.filterMap_cons]
    cases hu : Env.lookup u ρ with
    | none =>
      by_cases hw : w = u
      · subst hw; simp only [Env.canon] at ih; simp [ih, hu]
      · simp only [Env.canon] at ih; simp [ih, hw]
    | some s =>
      by_cases hw : w = u
      · subst hw; simp [Env.lookup, hu]
      · simp only [Env.canon] at ih
        simp [Env.lookup, hw, ih]

/-- A binding `lookup` finds is one the list holds. -/
private theorem mem_of_lookup {w : Var} {t : Term} {σ : Env} (h : Env.lookup w σ = some t) :
    (w, t) ∈ σ := by
  induction σ with
  | nil => simp [Env.lookup] at h
  | cons b σ ih =>
    obtain ⟨u, s⟩ := b
    simp only [Env.lookup] at h
    by_cases hw : w = u
    · subst hw
      rw [if_pos rfl, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
    · simp only [if_neg hw] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- `assignments` binds from its own list. -/
private theorem assignments_snd {ts : List Term} : ∀ {vs : List Var} {σ : Env},
    σ ∈ assignments ts vs → ∀ b ∈ σ, b.2 ∈ ts := by
  intro vs
  induction vs with
  | nil => intro σ hσ b hb; simp only [assignments, List.mem_singleton] at hσ; simp [hσ] at hb
  | cons v vs ih =>
    intro σ hσ b hb
    simp only [assignments, List.mem_flatMap, List.mem_map] at hσ
    obtain ⟨t, ht, τ, hτ, rfl⟩ := hσ
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ht
    · exact ih hτ b hb

/-- Restriction to `vars` preserves an extension. -/
private theorem lookup_canon_mono {E : Env} {vars : List Var} {ρ ρ' : Env}
    (h : ∀ w y, Env.lookup w ρ = some y → Env.lookup w ρ' = some y) (w : Var) (y : Term)
    (hw : Env.lookup w (E ++ Env.canon vars ρ) = some y) :
    Env.lookup w (E ++ Env.canon vars ρ') = some y := by
  cases hE : Env.lookup w E with
  | some z => rw [lookup_append_some hE] at hw ⊢; exact hw
  | none =>
    rw [lookup_append_none hE] at hw ⊢
    rw [Env.lookup_canon_eq] at hw ⊢
    by_cases hm : w ∈ vars
    · rw [if_pos hm] at hw ⊢; exact h w y hw
    · rw [if_neg hm] at hw; exact absurd hw (by simp)

/-- `Expr.evalList` at a cons. -/
private theorem evalList_cons {e : Expr} {es : List Expr} {ρ : Env}
    {ks : List Term} (h : Expr.evalList (e :: es) ρ = some ks) :
    ∃ x ks', Expr.eval e ρ = some x ∧ Expr.evalList es ρ = some ks' ∧ ks = x :: ks' := by
  revert h
  simp only [Expr.evalList]
  cases he : Expr.eval e ρ with
  | none => simp
  | some x =>
    cases hl : Expr.evalList es ρ with
    | none => simp
    | some ks' =>
      simp only [Option.bind_some, Option.map_some, Option.some.injEq]
      intro h
      exact ⟨x, ks', rfl, rfl, h.symm⟩

mutual

/-- An extension cannot change a value the prefix already determined. -/
private theorem eval_mono {ρ ρ' : Env}
    (hmono : ∀ w y, Env.lookup w ρ = some y → Env.lookup w ρ' = some y) :
    ∀ (e : Expr) {t : Term}, Expr.eval e ρ = some t → Expr.eval e ρ' = some t
  | .lit _, _, h => h
  | .var w, _, h => hmono w _ h
  | .app f as, _, h => by
      obtain ⟨ts, hs, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [Expr.eval, evalList_mono hmono as hs, Option.map_some]
  | .min a b, _, h => by
      obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [Expr.eval, eval_mono hmono a hx, eval_mono hmono b hy,
        Option.bind_some, Option.map_some]

private theorem evalList_mono {ρ ρ' : Env}
    (hmono : ∀ w y, Env.lookup w ρ = some y → Env.lookup w ρ' = some y) :
    ∀ (es : List Expr) {ts : List Term}, Expr.evalList es ρ = some ts →
      Expr.evalList es ρ' = some ts
  | [], _, h => h
  | e :: es, _, h => by
      obtain ⟨t, ts, he, hes, rfl⟩ := evalList_cons h
      simp only [Expr.evalList, eval_mono hmono e he, evalList_mono hmono es hes,
        Option.bind_some, Option.map_some]

end

/-- A determined join key is the full instance's value. -/
private theorem joinOperand_eval {ρ ρ' : Env}
    (hmono : ∀ w y, Env.lookup w ρ = some y → Env.lookup w ρ' = some y)
    {e : Expr} {t : Term} (h : joinOperand ρ e = some t) : Expr.eval e ρ' = some t := by
  cases e with
  | lit _ => exact h
  | var w => exact hmono w _ h
  | app f as => exact eval_mono hmono (.app f as) h
  | min _ _ => simp [joinOperand] at h

/-- `holdsAll` is a `List.all`. -/
private theorem holdsAll_of_mem {d : FDatabase} {L : List Term} {x : Term}
    (h : d.holdsAll L = true) (hx : x ∈ L) : d.holdsAll [x] = true := by
  simp only [FDatabase.holdsAll, List.all_eq_true] at h ⊢
  intro s hs
  simp only [List.mem_singleton] at hs
  subst hs
  exact h _ hx

private theorem holdsAll_of_forall {d : FDatabase} {L : List Term}
    (h : ∀ x ∈ L, d.holdsAll [x] = true) : d.holdsAll L = true := by
  simp only [FDatabase.holdsAll, List.all_eq_true] at h ⊢
  intro x hx
  exact h x hx x (by simp)

/-- **Every operand's value is a term the database holds**, given that the determined ones
are and that the enumeration binds only from a list that is. -/
private theorem joinKnown_holds {d : FDatabase} {ρ ρ' : Env}
    (hmono : ∀ w y, Env.lookup w ρ = some y → Env.lookup w ρ' = some y)
    (hnew : ∀ w y, Env.lookup w ρ = none → Env.lookup w ρ' = some y →
      d.holdsAll [y] = true) :
    ∀ {es : List Expr} {ks : List Term}, joinReady ρ es = true →
      Expr.evalList es ρ' = some ks →
      d.holdsAll ((joinKnown ρ es).filterMap id) = true →
      ∀ x ∈ ks, d.holdsAll [x] = true := by
  intro es
  induction es with
  | nil => intro ks _ hev _ x hx; simp only [Expr.evalList, Option.some.injEq] at hev
           subst hev; simp at hx
  | cons e es ih =>
    intro ks hdr hev hk x hx
    obtain ⟨y, ks', hey, hes, rfl⟩ := evalList_cons hev
    simp only [joinReady, List.all_cons, Bool.and_eq_true] at hdr
    have hknown : d.holdsAll ((joinKnown ρ es).filterMap id) = true := by
      refine holdsAll_of_forall fun z hz => holdsAll_of_mem hk ?_
      simp only [joinKnown, List.map_cons, List.filterMap_cons] at hz ⊢
      cases hop : joinOperand ρ e with
      | none => simpa [hop] using hz
      | some w => simp only [id]; exact List.mem_cons_of_mem _ hz
    have hhead : d.holdsAll [y] = true := by
      match e with
      | .app f as =>
        obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hdr.1
        have hzy := (eval_mono hmono (.app f as) hz).symm.trans hey
        cases Option.some.inj hzy
        refine holdsAll_of_mem hk ?_
        simp only [joinKnown, List.map_cons, List.filterMap_cons, joinOperand, hz, id]
        exact List.mem_cons_self ..
      | .min _ _ => simp at hdr
      | .lit l =>
        simp only [Expr.eval, Option.some.injEq] at hey
        subst hey
        refine holdsAll_of_mem hk ?_
        simp only [joinKnown, List.map_cons, List.filterMap_cons, joinOperand, id]
        exact List.mem_cons_self ..
      | .var w =>
        have hey : Env.lookup w ρ' = some y := by simpa only [Expr.eval] using hey
        cases hw : Env.lookup w ρ with
        | none => exact hnew w y hw hey
        | some z =>
          have hzy : z = y := by
            have h' := hmono w z hw
            rw [hey] at h'
            exact (Option.some.injEq .. ▸ h').symm
          subst hzy
          refine holdsAll_of_mem hk ?_
          simp only [joinKnown, List.map_cons, List.filterMap_cons, joinOperand, hw, id]
          exact List.mem_cons_self ..
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hhead
    · exact ih hdr.2 hes hknown x hx

/-- `congrTuple` at a cons. -/
private theorem congrTuple_cons {cl : Finset (Term × Term)} {x : Term} {ks xs : List Term}
    (h : FDatabase.congrTuple cl (x :: ks) xs = true) :
    ∃ y xs', xs = y :: xs' ∧ (x, y) ∈ cl ∧ FDatabase.congrTuple cl ks xs' = true := by
  cases xs with
  | nil => simp [FDatabase.congrTuple] at h
  | cons y xs' =>
    simp only [FDatabase.congrTuple, List.length_cons, beq_iff_eq, Nat.add_right_cancel_iff,
      List.zip_cons_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨y, xs', rfl, h.2.1, h.1, h.2.2⟩

/-- **What the index is asked is implied by what the atom will be asked.** A row congruent
to the whole instance is consistent with the part of it the prefix has determined. -/
private theorem joinConsistent_of_congrTuple {cl : Finset (Term × Term)}
    {ρ ρ' : Env} (hmono : ∀ w y, Env.lookup w ρ = some y → Env.lookup w ρ' = some y) :
    ∀ {es : List Expr} {ks xs : List Term},
      Expr.evalList es ρ' = some ks →
      FDatabase.congrTuple cl ks xs = true →
      joinConsistent cl (joinKnown ρ es) xs = true := by
  intro es
  induction es with
  | nil =>
    intro ks xs hev hct
    simp only [Expr.evalList, Option.some.injEq] at hev
    subst hev
    simp only [FDatabase.congrTuple, List.length_nil, beq_iff_eq, Bool.and_eq_true] at hct
    cases xs with
    | nil => simp [joinConsistent, joinKnown]
    | cons _ _ => simp at hct
  | cons e es ih =>
    intro ks xs hev hct
    obtain ⟨y, ks', hey, hes, rfl⟩ := evalList_cons hev
    obtain ⟨z, xs', rfl, hzy, hct'⟩ := congrTuple_cons hct
    have htail := ih hes hct'
    have hhead : ∀ s, joinOperand ρ e = some s → (s, z) ∈ cl := by
      intro s hs
      have he := (joinOperand_eval hmono hs).symm.trans hey
      cases Option.some.inj he
      exact hzy
    simp only [joinKnown, List.map_cons, joinConsistent, List.length_cons, beq_iff_eq,
      List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at htail ⊢
    refine ⟨?_, ?_, ?_⟩
    · omega
    · cases hop : joinOperand ρ e with
      | none => simp
      | some s => simpa using hhead s hop
    · exact htail.2

/-- What one ready application plan promises. -/
private theorem joinAtomPlan_ctor {cl : Finset (Term × Term)} {d : FDatabase} {pre : Env}
    {v : Var} {vars : List Var} {as : List Expr} {f : FnName} {a : JoinAtom}
    (h : joinAtomPlan cl d pre v vars f as = some a) :
    joinReady (Env.canon vars pre) as = true ∧ a.vars = vars ∧ a.keys = as ∧
      d.holdsAll ((joinKnown (Env.canon a.vars pre) as).filterMap id) = true ∧
      ∀ r ∈ d.rows, r.fn = f → d.subsumed.contains (.app r.fn r.args) = false →
        joinConsistent cl (joinKnown (Env.canon a.vars pre) as) r.args = true →
        r ∈ a.rows := by
  simp only [joinAtomPlan] at h
  split at h
  · rename_i hg
    split at h
    · rename_i hh
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hg
      refine ⟨hg.1.2, rfl, rfl, hh, ?_⟩
      intro r hr hf hs h1
      have hbf : (r.fn == f) = true := by simp [hf]
      have hs' : Term.app r.fn r.args ∉ d.subsumed := by simpa using hs
      exact List.mem_filter.mpr ⟨hr, by simp [hbf, hs', h1]⟩
    · simp at h
  · simp at h

mutual

/-- A matching expression satisfies every application read its plans use. -/
private theorem joinExprPlans_holds {cl : Finset (Term × Term)} {d : FDatabase}
    {pre σ : Env} {v : Var} {vars : List Var} {a : JoinAtom} : ∀ (e : Expr),
    exprHoldsWith cl d σ e = true → a ∈ joinExprPlans cl d pre v vars e →
    ∃ f as, joinAtomPlan cl d pre v vars f as = some a ∧
      patternHoldsWith cl d (.expr (.app f as)) σ = true
  | .lit _, _, ha => by simp [joinExprPlans] at ha
  | .var _, _, ha => by simp [joinExprPlans] at ha
  | .min _ _, _, ha => by simp [joinExprPlans] at ha
  | .app f as, hh, ha => by
      rcases List.mem_append.mp ha with ha | ha
      · exact ⟨f, as, by simpa using ha, hh⟩
      · exact joinArgsPlans_holds as (Bool.and_eq_true_iff.mp hh).1 ha

private theorem joinArgsPlans_holds {cl : Finset (Term × Term)} {d : FDatabase}
    {pre σ : Env} {v : Var} {vars : List Var} {a : JoinAtom} : ∀ (es : List Expr),
    exprsHoldWith cl d σ es = true → a ∈ joinArgsPlans cl d pre v vars es →
    ∃ f as, joinAtomPlan cl d pre v vars f as = some a ∧
      patternHoldsWith cl d (.expr (.app f as)) σ = true
  | [], _, ha => by simp [joinArgsPlans] at ha
  | e :: es, hh, ha => by
      rcases List.mem_append.mp ha with ha | ha
      · exact joinExprPlans_holds e (Bool.and_eq_true_iff.mp hh).1 ha
      · exact joinArgsPlans_holds es (Bool.and_eq_true_iff.mp hh).2 ha

end

/-- What `patternHoldsWith` promises at an application atom: its operands evaluate, and
once their values are all held, a held application of the head with congruent children
that is not a subsumed row as written. -/
private theorem patternHoldsWith_ctor {cl : Finset (Term × Term)} {d : FDatabase}
    {e : Expr} {as : List Expr} {f : FnName} {σ : Env}
    (hc : e.ctorAtom = some (f, as))
    (h : patternHoldsWith cl d (.expr e) σ = true) :
    ∃ ks, Expr.evalList as σ = some ks ∧
      (d.holdsAll ks = true → ∃ r ∈ d.rows, r.fn = f ∧
        FDatabase.congrTuple cl ks r.args = true ∧
        d.subsumed.contains (.app r.fn r.args) = false) := by
  cases e with
  | app g args =>
    simp only [Expr.ctorAtom, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [patternHoldsWith, exprHoldsWith, Bool.and_eq_true] at h
    cases hev : Expr.evalList args σ with
    | none => rw [hev] at h; simp at h
    | some ks =>
      rw [hev] at h
      refine ⟨ks, rfl, fun hks => ?_⟩
      have hl := h.2
      simp only [FDatabase.liveWith, if_pos hks, Bool.and_eq_true, Bool.not_eq_true'] at hl
      obtain ⟨hrow, hsub⟩ := hl
      simp only [FDatabase.hasCtorRow, List.any_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at hrow
      obtain ⟨r, hr, hf, hcm⟩ := hrow
      refine ⟨r, hr, hf, hcm, ?_⟩
      by_contra hmem
      simp only [Bool.not_eq_false, List.contains_iff_mem] at hmem
      have : d.isSubsumed cl (.app g ks) = true := by
        simp only [FDatabase.isSubsumed, List.any_eq_true]
        exact ⟨_, hmem, by simp [FDatabase.sameRow, hf, hcm]⟩
      rw [this] at hsub
      exact Bool.noConfusion hsub
  | lit _ => simp [Expr.ctorAtom] at hc
  | var _ => simp [Expr.ctorAtom] at hc
  | min _ _ => simp [Expr.ctorAtom] at hc

/-- **The narrowing keeps every candidate a full substitution supports.** -/
theorem joinCands_mem {cl : Finset (Term × Term)} {d : FDatabase} {q : Query} {held : Bool}
    {ts : List Term} {pre : Env} {v : Var} {t : Term} {σ : Env}
    (hheld : held = true → ∀ u ∈ ts, d.holdsAll [u] = true)
    (htm : t ∈ ts) (hσ : ∀ b ∈ σ, b.2 ∈ ts)
    (hall : (q.all fun p => patternHoldsWith cl d p
        (Env.canon (p.freeVars []) (pre ++ [(v, t)] ++ σ))) = true) :
    t ∈ joinCands cl d q held ts pre v := by
  simp only [joinCands]
  split
  · rename_i hb
    refine List.mem_filter.mpr ⟨htm, List.all_eq_true.mpr fun a ha => ?_⟩
    have ha' : a ∈ q.flatMap (joinPlan cl d pre v) :=
      ((List.mergeSort_perm _ _).mem_iff).mp ha
    obtain ⟨p, hp, hpa⟩ := List.mem_flatMap.mp ha'
    have hph := List.all_eq_true.mp hall p hp
    match p, hpa, hph with
    | .eq _ _, hpa, _ => simp [joinPlan] at hpa
    | .ne _ _, hpa, _ => simp [joinPlan] at hpa
    | .expr e, hpa, hph =>
      obtain ⟨f, as, hplan, hph⟩ := joinExprPlans_holds e hph hpa
      obtain ⟨hda, hav, hak, hka, hrow⟩ := joinAtomPlan_ctor hplan
      obtain ⟨ks, hek, hrows⟩ := patternHoldsWith_ctor rfl hph
      -- the three environments: the node's, the candidate's, and the full substitution's
      set vars := (Pattern.expr e).freeVars [] with hvars
      set ρ₀ := Env.canon vars pre with hρ₀
      set ρ₁ := Env.canon vars (pre ++ [(v, t)]) with hρ₁
      set ρ₂ := Env.canon vars (pre ++ [(v, t)] ++ σ) with hρ₂
      have mono₀ : ∀ w y, Env.lookup w ρ₀ = some y → Env.lookup w ρ₂ = some y := by
        rw [hρ₀, hρ₂]
        exact lookup_canon_mono (E := [])
          fun w y hw => lookup_append_some (lookup_append_some hw)
      have mono₁ : ∀ w y, Env.lookup w ρ₁ = some y → Env.lookup w ρ₂ = some y := by
        rw [hρ₁, hρ₂]
        exact lookup_canon_mono (E := []) fun w y hw => lookup_append_some hw
      have hnew : ∀ w y, Env.lookup w ρ₀ = none → Env.lookup w ρ₂ = some y →
          d.holdsAll [y] = true := by
        intro w y h0 h2
        rw [hρ₀, Env.lookup_canon_eq] at h0
        rw [hρ₂, Env.lookup_canon_eq] at h2
        by_cases hmv : w ∈ vars
        · rw [if_pos hmv] at h0 h2
          rw [List.append_assoc, lookup_append_none h0, List.singleton_append,
            Env.lookup] at h2
          by_cases hwv : w = v
          · rw [if_pos hwv, Option.some.injEq] at h2
            subst h2; exact hheld hb t htm
          · rw [if_neg hwv] at h2
            exact hheld hb y (hσ (w, y) (mem_of_lookup h2))
        · rw [if_neg hmv] at h2; simp at h2
      -- every operand's value is held, so the atom took the index branch
      have hks : ∀ x ∈ ks, d.holdsAll [x] = true := by
        rw [hav] at hka
        exact joinKnown_holds mono₀ hnew hda hek hka
      obtain ⟨r, hr, hrf, hcm, hns⟩ := hrows (holdsAll_of_forall hks)
      -- the row survives the prefix, so it is one of the atom's, and it admits `t`
      have hin : r ∈ a.rows := by
        refine hrow r hr hrf hns ?_
        rw [hav]
        exact joinConsistent_of_congrTuple mono₀ hek hcm
      refine List.any_eq_true.mpr ⟨r, hin, ?_⟩
      rw [hak, hav]
      exact joinConsistent_of_congrTuple mono₁ hek hcm
  · exact htm

/-- `filter` past a `flatMap` that is empty wherever the filter rejects. -/
private theorem flatMap_filter_eq {α β : Type} (P : α → Bool) (F : α → List β) :
    ∀ l : List α, (∀ t ∈ l, P t = false → F t = []) →
      (l.filter P).flatMap F = l.flatMap F := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x l ih =>
    intro h
    by_cases hx : P x
    · simp only [List.filter_cons, if_pos hx, List.flatMap_cons]
      rw [ih fun t ht => h t (List.mem_cons_of_mem _ ht)]
    · simp only [Bool.not_eq_true] at hx
      rw [List.filter_cons, if_neg (by simp [hx]), List.flatMap_cons,
        h x List.mem_cons_self hx, List.nil_append]
      exact ih fun t ht => h t (List.mem_cons_of_mem _ ht)

/-- **The join is the pruned enumeration**, on the nose: the same substitutions, in the
same order. -/
theorem matchJoin_eq (cl : Finset (Term × Term)) (d : FDatabase) (q : Query)
    (ts : List Term) (held : Bool) (hheld : held = true → ∀ u ∈ ts, d.holdsAll [u] = true) :
    ∀ (vs : List Var) (pre : Env),
      matchJoin cl d q ts held pre vs = matchPrune cl d q ts pre vs := by
  intro vs
  induction vs with
  | nil => intro pre; rfl
  | cons v vs ih =>
    intro pre
    rw [matchJoin, matchPrune]
    simp only [ih]
    simp only [joinCands]
    split
    · rename_i hb
      refine flatMap_filter_eq _ _ ts fun t ht hp => ?_
      split
      · rename_i hg
        refine List.map_eq_nil_iff.mpr (List.eq_nil_iff_forall_not_mem.mpr fun τ hτ => ?_)
        rw [matchPrune_eq] at hτ
        obtain ⟨hτa, hτp⟩ := List.mem_filter.mp hτ
        have := joinCands_mem (held := held) hheld ht (assignments_snd hτa) hτp
        simp only [joinCands, if_pos hb, List.mem_filter] at this
        rw [this.2] at hp
        exact Bool.noConfusion hp
      · rfl
    · rfl

/-- Match a query using application joins, with class representatives as candidates. -/
def matchQueryJoin (cl : Finset (Term × Term)) (d : FDatabase) (q : Query) : List Env :=
  matchJoin cl d q (d.repsWith cl) (d.holdsAll (d.repsWith cl)) [] (Query.freeVars q [])

theorem matchQueryJoin_eq (cl : Finset (Term × Term)) (d : FDatabase) (q : Query) :
    matchQueryJoin cl d q = matchQueryWith cl d q := by
  rw [matchQueryJoin, matchJoin_eq cl d q (d.repsWith cl) (d.holdsAll (d.repsWith cl))
    (fun h u hu => holdsAll_of_mem h hu)]
  exact matchQueryPruned_eq cl d q

/-- **The join is `matchQuery`**: at `d`'s own closure it produces the same substitutions,
in the same order, binding the same variables in the same order. -/
theorem matchQueryJoin_eq_matchQuery (d : FDatabase) (q : Query) :
    matchQueryJoin d.closureF d q = matchQuery d q :=
  (matchQueryJoin_eq d.closureF d q).trans (matchQueryWith_eq d q)

/-- **What points compiled code at the join** — every caller of `matchQueryWith`, which
after the `csimp` below is every caller of `matchQuery` too. -/
@[csimp] theorem matchQueryWith_eq_join : @matchQueryWith = @matchQueryJoin := by
  funext cl d q
  exact (matchQueryJoin_eq cl d q).symm

/-- The join at `d`'s own closure. -/
def matchQueryJoinAt (d : FDatabase) (q : Query) : List Env := matchQueryJoin d.closureF d q

theorem matchQuery_eq_matchQueryFast : @matchQuery = @matchQueryFast := by
  funext d q
  exact (matchQueryFast_eq d q).symm

/-- Query matching agrees with the join implementation; `csimp` selects it for execution. -/
@[csimp] theorem matchQuery_eq_join : @matchQuery = @matchQueryJoinAt := by
  funext d q
  exact (matchQueryJoin_eq_matchQuery d q).symm

/-! ### Running -/
/-- `evalAction`, computed. Every action only adds: a subsume inserts its row and marks it. -/
def execAction (σ : Env) (d : FDatabase) : Action → Option FDatabase
  | .expr e => (e.eval σ).map fun t => d.addTerm t
  | .union e₁ e₂ =>
      (e₁.eval σ).bind fun t₁ => (e₂.eval σ).bind fun t₂ =>
        if t₁.isLit || t₂.isLit then none else some (d.addEq t₁ t₂)
  | .subsume f es => (Expr.evalList es σ).map fun ts => d.subsume (.app f ts)

/-- `evalActions`, computed. -/
def execActions (σ : Env) (d : FDatabase) : List Action → Option FDatabase
  | [] => some d
  | a :: as => (execAction σ d a).bind fun d' => execActions σ d' as

/-! #### Rounds

Match every rule against the pre-state, then add the firings' writes and subsumptions.
A head with any stuck action contributes nothing. -/
/-- Apply one firing to `acc`; leave `acc` unchanged if any head action is stuck. -/
def fireInto (r : Rule) (acc : FDatabase) (σ : Env) : FDatabase :=
  match execActions σ acc r.actions with
  | some d' => d'
  | none => acc

/-- One round of `rs` under the pre-state's closure `cl`: match every rule against the
pre-state, then apply every firing. -/
def execRunRulesWith (cl : Finset (Term × Term)) (rs : List Rule) (d : FDatabase) :
    FDatabase :=
  let firings := rs.map fun r => (r, matchQueryWith cl d r.query)
  firings.foldl (fun acc rs => rs.2.foldl (fireInto rs.1) acc) d

/-- One round of the rules `rs`, with one congruence closure for the whole round. -/
def execRunRules (rs : List Rule) (d : FDatabase) : FDatabase :=
  execRunRulesWith d.closureF rs d

/-- Whether two states agree on every field. -/
def FDatabase.sameData (d e : FDatabase) : Bool :=
  e.terms == d.terms && e.rows == d.rows && e.eqs == d.eqs && e.subsumed == d.subsumed

/-- Rounds of `rs` until nothing changes, bounded by fuel that **fails** rather than
returning a prefix: rules that really do diverge make the run `none`, which the difftest
reports as a mismatch, rather than presenting a half-run state as a saturation. -/
def FDatabase.runSaturateF (rs : List Rule) : Nat → FDatabase → Option FDatabase
  | 0, d => if d.sameData (execRunRules rs d) then some d else none
  | n + 1, d =>
      if d.sameData (execRunRules rs d) then some d
      else FDatabase.runSaturateF rs n (execRunRules rs d)

/-- `runSaturateF` with the round computed **once**. -/
def FDatabase.runSaturateFast (rs : List Rule) : Nat → FDatabase → Option FDatabase
  | 0, d => if d.sameData (execRunRules rs d) then some d else none
  | n + 1, d =>
      let e := execRunRules rs d
      if d.sameData e then some d else FDatabase.runSaturateFast rs n e

theorem FDatabase.runSaturateFast_eq (rs : List Rule) (n : Nat) (d : FDatabase) :
    FDatabase.runSaturateFast rs n d = FDatabase.runSaturateF rs n d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    simp only [FDatabase.runSaturateFast, FDatabase.runSaturateF, ih]

@[csimp] theorem FDatabase.runSaturateF_eq_fast :
    @FDatabase.runSaturateF = @FDatabase.runSaturateFast := by
  funext rs n d
  exact (FDatabase.runSaturateFast_eq rs n d).symm

mutual

/-- Execute a schedule, allowing at most `fuel` state-changing passes per saturation
followed by a final stability check. Return `none` if any saturation exhausts its budget. -/
def execSchedule (fuel : Nat) (d : FDatabase) : Schedule → Option FDatabase
  | .run rs => some (execRunRules rs d)
  | .seq S₁ S₂ => (execSchedule fuel d S₁).bind fun e => execSchedule fuel e S₂
  | .saturate S => execSaturate fuel fuel d S
termination_by S => (sizeOf S, 0)

/-- Execute passes of `S` until one leaves the stored data unchanged. The pass counter
allows that many changing passes followed by one stability check; exhaustion returns
`none`. Nested saturations each receive the budget `fuel`. -/
def execSaturate (fuel : Nat) : Nat → FDatabase → Schedule → Option FDatabase
  | 0, d, S => (execSchedule fuel d S).bind fun e => if d.sameData e then some e else none
  | n + 1, d, S => (execSchedule fuel d S).bind fun e =>
      if d.sameData e then some e else execSaturate fuel n e S
termination_by n _ S => (sizeOf S, n + 1)

end

/-- Default budget of state-changing passes per saturation, followed by a stability check.
Exhaustion does not distinguish divergence from a terminating run that needs more passes. -/
def runFuel : Nat := 64

/-- The final check, computed: `QueryHolds` on the final state, an ordinary query over its
live rows. -/
def FDatabase.holds (d : FDatabase) (q : Query) : Bool := !(matchQuery d q).isEmpty

/-- Run a program's schedule from the initial database. The final check is read off the
result with `FDatabase.holds`; `observe` combines the two. -/
def exec (P : Program) : Option FDatabase := execSchedule runFuel FDatabase.empty P.schedule

/-! ### Row counts

What `egglog/tests/files.rs` snapshots is one row per distinct *canonical* argument
tuple. On this side that is the number of congruence classes of `f`-applications, which
is what a differential test compares. -/
/-- Whether two argument lists are pointwise related by `cl`. -/
def congrArgs (cl : Finset (Term × Term)) (as bs : List Term) : Bool :=
  as.length == bs.length && (as.zip bs).all fun q => decide (q ∈ cl)

/-- The argument lists of `d`'s `f`-applications. -/
def FDatabase.argLists (d : FDatabase) (f : FnName) : List (List Term) :=
  d.rows.filterMap fun r => if r.fn = f then some r.args else none

/-- The number of rows egglog's table for `f` would hold: one per congruence class of
argument lists. Each list is mapped to its whole class and the distinct classes counted,
so no representative has to be chosen. -/
def FDatabase.rowCount (d : FDatabase) (f : FnName) : Nat :=
  let cl := d.closureF
  let args := (d.argLists f).toFinset
  (args.image fun as => args.filter fun bs => congrArgs cl as bs).card

/-- The per-function row counts, as `files.rs` prints them. -/
def FDatabase.rowCounts (d : FDatabase) (fs : List FnName) : List (FnName × Nat) :=
  fs.map fun f => (f, d.rowCount f)

end Egglog
