import EgglogSemantics.Spec.Database
import EgglogSemantics.Proofs.Term

namespace Egglog
namespace Env
@[simp] theorem lookup_nil {v : Var} : lookup v [] = none := rfl

@[simp] theorem lookup_cons {v w : Var} {t : Term} {σ : Env} :
    lookup v ((w, t) :: σ) = if v = w then some t else lookup v σ := rfl

@[simp] theorem dom_nil : dom [] = [] := rfl

@[simp] theorem dom_cons {v : Var} {t : Term} {σ : Env} :
    dom ((v, t) :: σ) = v :: dom σ := rfl

theorem mem_dom_of_mem {b : Var × Term} {σ : Env} (h : b ∈ σ) : b.1 ∈ dom σ :=
  List.mem_map_of_mem h

theorem mem_dom_iff {v : Var} {σ : Env} : v ∈ dom σ ↔ ∃ t, (v, t) ∈ σ := by
  constructor
  · intro h
    obtain ⟨⟨w, t⟩, hb, rfl⟩ := List.mem_map.mp h
    exact ⟨t, hb⟩
  · rintro ⟨t, hb⟩
    exact mem_dom_of_mem hb

@[simp] theorem dom_append {σ₁ σ₂ : Env} : dom (σ₁ ++ σ₂) = dom σ₁ ++ dom σ₂ :=
  List.map_append ..

theorem lookup_isSome_iff_mem_dom {v : Var} {σ : Env} :
    (lookup v σ).isSome ↔ v ∈ dom σ := by
  induction σ with
  | nil => simp
  | cons b σ ih =>
    obtain ⟨w, t⟩ := b
    by_cases h : v = w <;> simp [h, ih]

theorem lookup_eq_none_iff {v : Var} {σ : Env} : lookup v σ = none ↔ v ∉ dom σ := by
  induction σ with
  | nil => simp
  | cons b σ ih =>
    obtain ⟨w, t⟩ := b
    by_cases h : v = w <;> simp [h, ih]

/-- Appending environments never fails, unlike the Redex `Env-Union`, because the
only appends this semantics performs are of a substitution onto the globals, whose
domains are disjoint (`Pattern.freeVars_lookup_eq_none`). `lookup` is left-biased, so
`σ₁` shadows `σ₂` — the same as `Env-Union2` prepending `Env_1`. -/
theorem lookup_append_of_not_mem {v : Var} {σ₁ σ₂ : Env} (h : v ∉ dom σ₁) :
    lookup v (σ₁ ++ σ₂) = lookup v σ₂ := by
  induction σ₁ with
  | nil => rfl
  | cons b σ ih =>
    obtain ⟨w, t⟩ := b
    simp only [dom_cons, List.mem_cons, not_or] at h
    simp [h.1, ih h.2]

theorem lookup_append_of_mem {v : Var} {σ₁ σ₂ : Env} (h : v ∈ dom σ₁) :
    lookup v (σ₁ ++ σ₂) = lookup v σ₁ := by
  induction σ₁ with
  | nil => simp at h
  | cons b σ ih =>
    obtain ⟨w, t⟩ := b
    by_cases hv : v = w
    · simp [hv]
    · simp only [dom_cons, List.mem_cons] at h
      simp [hv, ih (h.resolve_left hv)]

theorem mem_of_lookup {v : Var} {t : Term} {σ : Env} (h : lookup v σ = some t) :
    (v, t) ∈ σ := by
  induction σ with
  | nil => simp at h
  | cons b σ ih =>
    obtain ⟨w, u⟩ := b
    by_cases hv : v = w
    · subst hv
      rw [lookup_cons, if_pos rfl] at h
      cases h
      simp
    · rw [lookup_cons, if_neg hv] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- With no duplicate variables, `lookup` is just membership. -/
theorem lookup_eq_some_iff_mem {v : Var} {t : Term} {σ : Env} (hnd : (dom σ).Nodup) :
    lookup v σ = some t ↔ (v, t) ∈ σ := by
  induction σ with
  | nil => simp
  | cons b σ ih =>
    obtain ⟨w, u⟩ := b
    rw [dom_cons, List.nodup_cons] at hnd
    by_cases hv : v = w
    · subst hv
      simp only [lookup_cons, ↓reduceIte, Option.some.injEq, List.mem_cons, Prod.mk.injEq,
        true_and]
      exact ⟨fun h => Or.inl h.symm,
        fun h => h.elim Eq.symm fun hmem => absurd (mem_dom_of_mem hmem) hnd.1⟩
    · simp only [lookup_cons, hv, ↓reduceIte, List.mem_cons, Prod.mk.injEq, ih hnd.2,
        false_and, false_or]

theorem Agree.refl (σ : Env) : Agree σ σ := fun _ => rfl

theorem Agree.symm {σ₁ σ₂ : Env} (h : Agree σ₁ σ₂) : Agree σ₂ σ₁ := fun v => (h v).symm

theorem Agree.trans {σ₁ σ₂ σ₃ : Env} (h₁ : Agree σ₁ σ₂) (h₂ : Agree σ₂ σ₃) :
    Agree σ₁ σ₃ := fun v => (h₁ v).trans (h₂ v)

/-- Reordering a duplicate-free environment's bindings changes no lookup. This is
what makes `ValidEnv`'s use of `Perm` — where the Redex `valid-env` pins the order —
observationally harmless. -/
theorem Agree.of_perm {σ₁ σ₂ : Env} (h : σ₁.Perm σ₂) (hnd : (dom σ₁).Nodup) :
    Agree σ₁ σ₂ := by
  have hp : (dom σ₁).Perm (dom σ₂) := h.map Prod.fst
  intro v
  cases hl : lookup v σ₁ with
  | some t =>
    exact ((lookup_eq_some_iff_mem (hp.nodup hnd)).mpr
      (h.mem_iff.mp ((lookup_eq_some_iff_mem hnd).mp hl))).symm
  | none =>
    rw [lookup_eq_none_iff] at hl
    exact (lookup_eq_none_iff.mpr fun hv => hl (hp.mem_iff.mpr hv)).symm

/-- Agreement survives a shared prefix, which is how a substitution's agreement
lifts to the globals it is appended to. -/
theorem Agree.append_left (ρ : Env) {σ₁ σ₂ : Env} (h : Agree σ₁ σ₂) :
    Agree (ρ ++ σ₁) (ρ ++ σ₂) := by
  intro v
  by_cases hv : v ∈ dom ρ
  · rw [lookup_append_of_mem hv, lookup_append_of_mem hv]
  · rw [lookup_append_of_not_mem hv, lookup_append_of_not_mem hv]
    exact h v

end Env
namespace Database
@[simp] theorem addTerm_terms {t : Term} {db : Database} :
    (db.addTerm t).terms = db.terms ∪ t.subterms := rfl

@[simp] theorem addTerm_eqs {t : Term} {db : Database} : (db.addTerm t).eqs = db.eqs := rfl

@[simp] theorem addTerm_sig {t : Term} {db : Database} : (db.addTerm t).sig = db.sig := rfl

@[simp] theorem addTerm_env {t : Term} {db : Database} : (db.addTerm t).env = db.env := rfl

@[simp] theorem addTerm_rules {t : Term} {db : Database} :
    (db.addTerm t).rules = db.rules := rfl

theorem mem_addTerm (t : Term) (db : Database) : t ∈ (db.addTerm t).terms :=
  Or.inr (Term.IsSubterm.refl t)

@[simp] theorem addEq_terms {a b : Term} {db : Database} :
    (db.addEq a b).terms = db.terms ∪ a.subterms ∪ b.subterms := rfl

@[simp] theorem addEq_eqs {a b : Term} {db : Database} :
    (db.addEq a b).eqs = insert (a, b) db.eqs := rfl

@[simp] theorem addEq_env {a b : Term} {db : Database} : (db.addEq a b).env = db.env := rfl

@[simp] theorem addEq_rules {a b : Term} {db : Database} :
    (db.addEq a b).rules = db.rules := rfl

@[simp] theorem addEq_sig {a b : Term} {db : Database} : (db.addEq a b).sig = db.sig := rfl

@[simp] theorem sUnion_terms {db : Database} {S : Set Database} :
    (db.sUnion S).terms = db.terms ∪ ⋃ d ∈ S, d.terms := rfl

@[simp] theorem sUnion_eqs {db : Database} {S : Set Database} :
    (db.sUnion S).eqs = db.eqs ∪ ⋃ d ∈ S, d.eqs := rfl

@[simp] theorem sUnion_env {db : Database} {S : Set Database} :
    (db.sUnion S).env = db.env := rfl

@[simp] theorem sUnion_rows {db : Database} {S : Set Database} :
    (db.sUnion S).rows = db.rows ∪ ⋃ d ∈ S, d.rows := rfl

@[simp] theorem sUnion_rules {db : Database} {S : Set Database} :
    (db.sUnion S).rules = db.rules := rfl

@[simp] theorem sUnion_sig {db : Database} {S : Set Database} :
    (db.sUnion S).sig = db.sig := rfl

/-- Two `EnvAgree` databases with the same environment and rules imposed are equal.
This is what turns agreement back into equality once `evalLocalActions` restores the
caller's environment. -/
theorem EnvAgree.eq_of_env_rules {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (σ : Env)
    (R : Set Rule) :
    ({ d₁ with env := σ, rules := R } : Database) = { d₂ with env := σ, rules := R } := by
  rw [show d₁.sig = d₂.sig from h.sig, show d₁.terms = d₂.terms from h.terms,
    show d₁.rows = d₂.rows from h.rows, show d₁.eqs = d₂.eqs from h.eqs]

/-! ### `addTerms` and `addRow`

`addTerms` is a fold, so its untouched fields need an induction rather than `rfl`. -/
@[simp] theorem addTerms_sig {db : Database} {ts : List Term} :
    (db.addTerms ts).sig = db.sig := by
  induction ts generalizing db with
  | nil => rfl
  | cons t ts ih => exact ih

@[simp] theorem addTerms_eqs {db : Database} {ts : List Term} :
    (db.addTerms ts).eqs = db.eqs := by
  induction ts generalizing db with
  | nil => rfl
  | cons t ts ih => exact ih

@[simp] theorem addTerms_env {db : Database} {ts : List Term} :
    (db.addTerms ts).env = db.env := by
  induction ts generalizing db with
  | nil => rfl
  | cons t ts ih => exact ih

@[simp] theorem addTerms_rules {db : Database} {ts : List Term} :
    (db.addTerms ts).rules = db.rules := by
  induction ts generalizing db with
  | nil => rfl
  | cons t ts ih => exact ih

@[simp] theorem addRow_sig {db : Database} {f : FnName} {as vs : List Term} :
    (db.addRow f as vs).sig = db.sig := by simp [Database.addRow]

@[simp] theorem addRow_eqs {db : Database} {f : FnName} {as vs : List Term} :
    (db.addRow f as vs).eqs = db.eqs := by simp [Database.addRow]

@[simp] theorem addRow_env {db : Database} {f : FnName} {as vs : List Term} :
    (db.addRow f as vs).env = db.env := by simp [Database.addRow]

@[simp] theorem addRow_rules {db : Database} {f : FnName} {as vs : List Term} :
    (db.addRow f as vs).rules = db.rules := by simp [Database.addRow]

namespace EnvAgree
theorem addTerm {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (t : Term) :
    (d₁.addTerm t).EnvAgree (d₂.addTerm t) :=
  ⟨h.sig, by simp [Database.addTerm, h.terms], by simp [Database.addTerm, h.rows],
    h.eqs, h.rules, h.env⟩

theorem addTerms {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (ts : List Term) :
    (d₁.addTerms ts).EnvAgree (d₂.addTerms ts) := by
  induction ts generalizing d₁ d₂ with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm t)

theorem addRow {d₁ d₂ : Database} (h : d₁.EnvAgree d₂) (f : FnName) (as vs : List Term) :
    (d₁.addRow f as vs).EnvAgree (d₂.addRow f as vs) :=
  let h' := (h.addTerms as).addTerms vs
  ⟨h'.sig, h'.terms, by simp [Database.addRow, h'.rows], h'.eqs, h'.rules, h'.env⟩

end EnvAgree
namespace Contained
theorem refl (db : Database) : Contained db db := ⟨subset_rfl, subset_rfl, subset_rfl⟩

theorem trans {d₁ d₂ d₃ : Database} (h₁ : Contained d₁ d₂) (h₂ : Contained d₂ d₃) :
    Contained d₁ d₃ :=
  ⟨h₁.terms.trans h₂.terms, h₁.rows.trans h₂.rows, h₁.eqs.trans h₂.eqs⟩

theorem addTerm (t : Term) (db : Database) : Contained db (db.addTerm t) :=
  ⟨Set.subset_union_left, Set.subset_union_left, subset_rfl⟩

theorem addTerms (ts : List Term) (db : Database) : Contained db (db.addTerms ts) := by
  induction ts generalizing db with
  | nil => exact refl db
  | cons t ts ih => exact (addTerm t db).trans (ih (db := db.addTerm t))

theorem addEq (a b : Term) (db : Database) : Contained db (db.addEq a b) :=
  ⟨fun _ h => Or.inl (Or.inl h), fun _ h => Or.inl (Or.inl h), Set.subset_insert _ _⟩

theorem addRow (f : FnName) (as vs : List Term) (db : Database) :
    Contained db (db.addRow f as vs) :=
  ((addTerms as db).trans (addTerms vs _)).trans
    ⟨subset_rfl, Set.subset_insert _ _, subset_rfl⟩

theorem sUnion (db : Database) (S : Set Database) : Contained db (db.sUnion S) :=
  ⟨Set.subset_union_left, Set.subset_union_left, Set.subset_union_left⟩

theorem mem_sUnion {db d : Database} {S : Set Database} (h : d ∈ S) :
    Contained d (db.sUnion S) :=
  ⟨fun _ ht => Or.inr (Set.mem_biUnion h ht), fun _ ht => Or.inr (Set.mem_biUnion h ht),
    fun _ ht => Or.inr (Set.mem_biUnion h ht)⟩

end Contained
namespace WF
theorem empty : WF Database.empty where
  subtermClosed := by simp [Database.empty]
  eqsInTerms := by simp [Database.empty]
  envInTerms := by simp [Database.empty]

theorem addTerm {db : Database} (h : WF db) (t : Term) : WF (db.addTerm t) where
  subtermClosed := by
    rintro s (hs | hs)
    · exact (h.subtermClosed s hs).trans Set.subset_union_left
    · exact (Term.subterms_subset_of_mem hs).trans Set.subset_union_right
  eqsInTerms p hp := ⟨Or.inl (h.eqsInTerms p hp).1, Or.inl (h.eqsInTerms p hp).2⟩
  envInTerms b hb := Or.inl (h.envInTerms b hb)

theorem addTerms {db : Database} (h : WF db) (ts : List Term) : WF (db.addTerms ts) := by
  induction ts generalizing db with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm t)

/-- A `set` adds terms and one row; `WF` says nothing about rows (`Database.RowsWF`
does), so this is `addTerms` twice. -/
theorem addRow {db : Database} (h : WF db) (f : FnName) (as vs : List Term) :
    WF (db.addRow f as vs) :=
  ⟨((h.addTerms as).addTerms vs).subtermClosed, ((h.addTerms as).addTerms vs).eqsInTerms,
    ((h.addTerms as).addTerms vs).envInTerms⟩

theorem addEq {db : Database} (h : WF db) (a b : Term) : WF (db.addEq a b) := by
  refine ⟨((h.addTerm a).addTerm b).subtermClosed, ?_, ((h.addTerm a).addTerm b).envInTerms⟩
  rintro p (rfl | hp)
  · exact ⟨Or.inl (Or.inr a.self_mem_subterms), Or.inr b.self_mem_subterms⟩
  · exact ⟨Or.inl (Or.inl (h.eqsInTerms p hp).1), Or.inl (Or.inl (h.eqsInTerms p hp).2)⟩

theorem sUnion {db : Database} (h : WF db) {S : Set Database}
    (hS : ∀ d ∈ S, WF d) : WF (db.sUnion S) where
  subtermClosed := by
    rintro t (ht | ht)
    · exact (h.subtermClosed t ht).trans Set.subset_union_left
    · obtain ⟨d, hd, ht⟩ := Set.mem_iUnion₂.mp ht
      exact ((hS d hd).subtermClosed t ht).trans
        (Set.subset_union_of_subset_right (Set.subset_biUnion_of_mem hd) _)
  eqsInTerms := by
    rintro p (hp | hp)
    · exact ⟨Or.inl (h.eqsInTerms p hp).1, Or.inl (h.eqsInTerms p hp).2⟩
    · obtain ⟨d, hd, hp⟩ := Set.mem_iUnion₂.mp hp
      exact ⟨Or.inr (Set.mem_biUnion hd ((hS d hd).eqsInTerms p hp).1),
        Or.inr (Set.mem_biUnion hd ((hS d hd).eqsInTerms p hp).2)⟩
  envInTerms b hb := Or.inl (h.envInTerms b hb)

end WF
/-! ### Constructor rows

`CtorRows db` says the row set is exactly the one the term set induces. It is one of the
two hypotheses `Proofs/Merge.lean`'s `mcong_iff_cong` takes — `AllConstructors` is the
other — so this is the first half of making that theorem apply to a database a program
can actually produce. `Proofs/Step.lean` carries it along the step relations, where the
side condition `Action.SetLegal` enters.

Everything here is one observation: `ctorRowsOf` is a comprehension whose only
dependence on the term set is a single membership test, so it commutes with unions. -/
/-- `Term.ctorRows` *is* `ctorRowsOf` of the subterms, which is why `addTerm` preserves
`CtorRows` by set algebra alone. -/
theorem ctorRowsOf_subterms {t : Term} : ctorRowsOf t.subterms = t.ctorRows := rfl

theorem ctorRowsOf_empty : ctorRowsOf ∅ = ∅ := by
  ext r; simp [ctorRowsOf]

theorem ctorRowsOf_union {s t : Set Term} :
    ctorRowsOf (s ∪ t) = ctorRowsOf s ∪ ctorRowsOf t := by
  ext r
  simp only [ctorRowsOf, Set.mem_setOf_eq, Set.mem_union]
  tauto

namespace CtorRows
theorem empty : Database.empty.CtorRows := ctorRowsOf_empty.symm

theorem addTerm {db : Database} (h : db.CtorRows) (t : Term) :
    (db.addTerm t).CtorRows := by
  change db.rows ∪ t.ctorRows = ctorRowsOf (db.terms ∪ t.subterms)
  rw [ctorRowsOf_union, ctorRowsOf_subterms, h]

theorem addTerms {db : Database} (h : db.CtorRows) (ts : List Term) :
    (db.addTerms ts).CtorRows := by
  induction ts generalizing db with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm t)

theorem addEq {db : Database} (h : db.CtorRows) (a b : Term) :
    (db.addEq a b).CtorRows := (h.addTerm a).addTerm b

/-- A `set` preserves `CtorRows` exactly when it writes the row a constructor would.

The side condition is not decoration: `addRow f as [v]` for any other `v` writes a row
`ctorRowsOf` does not contain, and `not_ctorRows_addRow` below is that failure at its
smallest. Ruling the bad case out statically is `Action.SetLegal`. -/
theorem addRow {db : Database} (h : db.CtorRows) (f : FnName) (as : List Term) :
    (db.addRow f as [.app f as]).CtorRows := by
  have hd : ((db.addTerms as).addTerms [Term.app f as]).CtorRows := (h.addTerms as).addTerms _
  have hmem : Term.app f as ∈ ((db.addTerms as).addTerms [Term.app f as]).terms :=
    Database.mem_addTerm _ _
  change insert (Row.mk f as [Term.app f as])
    ((db.addTerms as).addTerms [Term.app f as]).rows =
      ctorRowsOf ((db.addTerms as).addTerms [Term.app f as]).terms
  rw [hd, Set.insert_eq_self.mpr (show _ ∈ ctorRowsOf _ from ⟨rfl, hmem⟩)]

/-- What `(run)` needs: if every operand's rows are induced by its own terms, the
union's rows are induced by the union's terms. -/
theorem sUnion {db : Database} (h : db.CtorRows) {S : Set Database}
    (hS : ∀ d ∈ S, d.CtorRows) : (db.sUnion S).CtorRows := by
  change db.rows ∪ (⋃ d ∈ S, d.rows) = ctorRowsOf (db.terms ∪ ⋃ d ∈ S, d.terms)
  ext r
  simp only [Set.mem_union, Set.mem_iUnion, ctorRowsOf, Set.mem_setOf_eq, exists_prop]
  constructor
  · rintro (hr | ⟨d, hd, hr⟩)
    · rw [h] at hr; exact ⟨hr.1, Or.inl hr.2⟩
    · rw [hS d hd] at hr; exact ⟨hr.1, Or.inr ⟨d, hd, hr.2⟩⟩
  · rintro ⟨hout, ht | ⟨d, hd, ht⟩⟩
    · exact Or.inl (by rw [h]; exact ⟨hout, ht⟩)
    · exact Or.inr ⟨d, hd, by rw [hS d hd]; exact ⟨hout, ht⟩⟩

end CtorRows
/-- A row whose output is not the application it is keyed at is one no `ctorRowsOf`
contains, so a database holding it is outside `CtorRows`. Every counterexample below is
this lemma plus a row. -/
theorem not_ctorRows_of_mem {db : Database} {r : Row} (hr : r ∈ db.rows)
    (hout : r.out ≠ [.app r.fn r.args]) : ¬db.CtorRows :=
  fun hc => hout (hc ▸ hr : r ∈ ctorRowsOf db.terms).1

/-- **`CtorRows` really does fail on an unrestricted `set`.**

The smallest witness: `(set (f) 0)` on the empty database writes `⟨f, [], [0]⟩`, whose
output is a literal, and no row of `ctorRowsOf` has a literal output. This is the whole
reason `Action.SetLegal` exists — without a side condition ruling this out, no step of
the semantics preserves `CtorRows`. -/
theorem not_ctorRows_addRow :
    ¬(Database.empty.addRow "f" [] [.lit (.int 0)]).CtorRows :=
  not_ctorRows_of_mem (Set.mem_insert _ _) (by simp)

end Database
end Egglog
