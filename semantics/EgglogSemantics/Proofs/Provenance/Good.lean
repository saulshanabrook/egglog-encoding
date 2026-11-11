import EgglogSemantics.Provenance.Log
import EgglogSemantics.Proofs.Subsume
import EgglogSemantics.Proofs.DiagonalRound
import EgglogSemantics.Proofs.Finite

/-! The states a union-free program reaches: every equation is reflexive and every subsumed
row is an application the state holds. On such a state matching sees only the held terms
and the subsumed rows, and two such states have one meaning exactly when they agree on
both. -/

namespace Egglog.Provenance

/-! ### Log rows -/

/-- A log row: an application of a name with the log prefix. -/
def IsLog (t : Term) : Prop := isLog t = true

theorem isLog_app {f : FnName} {ts : List Term} :
    isLog (.app f ts) = firePrefix.isPrefixOf f := rfl

theorem isLog_lit {l : Lit} : isLog (.lit l) = false := rfl

theorem not_isLog_lit (l : Lit) : ¬ IsLog (.lit l) := by simp [IsLog, isLog_lit]

theorem isLog_app_iff {f : FnName} {ts : List Term} :
    IsLog (.app f ts) ↔ firePrefix.isPrefixOf f = true := Iff.rfl

theorem not_isLog_app {f : FnName} {ts : List Term} (hf : firePrefix.isPrefixOf f = false) :
    ¬ IsLog (.app f ts) := by simp [IsLog, isLog_app, hf]

/-- The log names: `fireName k` has the log prefix. -/
theorem isPrefixOf_fireName (k : Nat) : firePrefix.isPrefixOf (fireName k) = true := by
  rw [fireName, String.isPrefixOf, String.startsWith_string_iff, String.toList_append]
  exact ⟨(toString k).toList, rfl⟩

theorem isLog_fireName (k : Nat) (ts : List Term) : IsLog (.app (fireName k) ts) :=
  isPrefixOf_fireName k

theorem mem_eraseLog {ts : List Term} {t : Term} : t ∈ eraseLog ts ↔ t ∈ ts ∧ ¬ IsLog t := by
  simp [eraseLog, IsLog]

@[simp] theorem Database.eraseLog_subsumed (d : Database) : d.eraseLog.subsumed = d.subsumed := rfl

theorem Database.mem_eraseLog_eqs {d : Database} {q : Term × Term} :
    q ∈ d.eraseLog.eqs ↔ q ∈ d.eqs ∧ ¬ IsLog q.1 := by
  simp [Database.eraseLog, IsLog]

/-! ### Good states -/

/-- Every equation is reflexive, and every subsumed row is an application the state holds. -/
structure Good (d : Database) : Prop where
  diag : d.Diag
  marks : ∀ t ∈ d.subsumed, (∃ f ts, t = .app f ts) ∧ t ∈ d.terms

namespace Good

variable {d e : Database}

theorem wf (h : Good d) : d.WF := ⟨fun p hp _ => h.diag p hp⟩

theorem noUnions (h : Good d) : d.NoUnions := ⟨h.diag⟩

theorem reps_eq (h : Good d) : d.reps = d.terms := h.diag.reps_eq_terms

theorem cong_iff (h : Good d) {a b : Term} : Cong d a b ↔ a = b ∧ a ∈ d.terms :=
  Cong.iff_eq_and_mem_of_diag h.diag

theorem cong_self_iff (h : Good d) {a : Term} : Cong d a a ↔ a ∈ d.terms := by
  rw [h.cong_iff]; simp

theorem marks_subset (h : Good d) : d.subsumed ⊆ d.terms := fun _ ht => (h.marks _ ht).2

/-- A term is live exactly when it is held and not subsumed. -/
theorem live_iff (h : Good d) {t : Term} : t ∈ d.live ↔ t ∈ d.terms ∧ t ∉ d.subsumed := by
  unfold Database.live
  simp only [Set.mem_setOf_eq, h.cong_self_iff]
  apply and_congr_right
  intro ht
  constructor
  · intro hn hs
    obtain ⟨⟨f, ts, rfl⟩, _⟩ := h.marks t hs
    exact hn ⟨_, hs, Database.SameRow.self_app (Database.toCong ht)⟩
  · rintro hn ⟨u, hu, hr⟩
    exact hn (hr.eq_of_diag h.diag ▸ hu)

theorem subsumed_iff (h : Good d) {t : Term} : t ∈ d.subsumed ↔ t ∈ d.terms ∧ t ∉ d.live := by
  rw [h.live_iff]
  constructor
  · intro hs; exact ⟨h.marks_subset hs, fun hl => hl.2 hs⟩
  · rintro ⟨ht, hl⟩; by_contra hs; exact hl ⟨ht, hs⟩

/-- Two good states have one meaning exactly when they hold the same terms and subsume
the same rows. -/
theorem sameMeaning_iff (hd : Good d) (he : Good e) :
    d.SameMeaning e ↔ d.terms = e.terms ∧ d.subsumed = e.subsumed := by
  constructor
  · intro h
    have ht := h.terms_eq_of_diag hd.diag he.diag
    refine ⟨ht, ?_⟩
    ext t
    rw [hd.subsumed_iff, he.subsumed_iff, ht, h.live t]
  · rintro ⟨ht, hs⟩
    refine Database.SameMeaning.of_congr (fun a b => ?_) hs
    rw [hd.cong_iff, he.cong_iff, ht]

theorem sameMeaning_of (hd : Good d) (he : Good e) (ht : d.terms = e.terms)
    (hs : d.subsumed = e.subsumed) : d.SameMeaning e :=
  (hd.sameMeaning_iff he).mpr ⟨ht, hs⟩

theorem terms_eq_of_sameMeaning (hd : Good d) (he : Good e) (h : d.SameMeaning e) :
    d.terms = e.terms := ((hd.sameMeaning_iff he).mp h).1

theorem subsumed_eq_of_sameMeaning (hd : Good d) (he : Good e) (h : d.SameMeaning e) :
    d.subsumed = e.subsumed := ((hd.sameMeaning_iff he).mp h).2

theorem empty : Good Database.empty where
  diag := fun _ hp => hp.elim
  marks := fun _ ht => ht.elim

end Good

/-! ### Rounds -/

theorem Action.mark_isApp {σ : Env} {a : Action} {X : Set Term} (h : a.mark σ = some X)
    {t : Term} (ht : t ∈ X) : ∃ f ts, t = .app f ts := by
  cases a with
  | expr e | union e f =>
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ht.elim
  | subsume f es =>
    obtain ⟨ts, _, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain rfl := ht
    exact ⟨f, ts, rfl⟩

theorem Action.marks_isApp {σ : Env} {as : List Action} {X : Set Term}
    (h : Action.marks σ as = some X) {t : Term} (ht : t ∈ X) : ∃ f ts, t = .app f ts := by
  induction as generalizing X with
  | nil => cases Option.some.inj h; exact ht.elim
  | cons a as ih =>
    obtain ⟨Y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨Z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ht.elim (fun ht => Action.mark_isApp hy ht) (fun ht => ih hz ht)

theorem RunMarks.isApp {rs : List Rule} {db : Database} {t : Term} (ht : t ∈ RunMarks rs db) :
    ∃ f ts, t = .app f ts := by
  obtain ⟨X, ⟨r, _, σ, _, hx⟩, ht⟩ := ht
  exact Action.marks_isApp hx ht

/-- The terms of a round: the pre-state's and the subterms of the written pairs. -/
theorem RunRules.mem_terms_iff {R : List Rule} {d : Database} {t : Term} :
    t ∈ (RunRules R d).terms ↔
      t ∈ d.terms ∨ ∃ p ∈ RunWrites R d, t ∈ p.1.subterms ∨ t ∈ p.2.subterms := by
  rw [RunRules.eq_pair]
  simp only [Database.mem_terms_iff, Set.mem_union]
  constructor
  · rintro ⟨p, hp | hp, ht⟩
    · exact Or.inl ⟨p, hp, ht⟩
    · exact Or.inr ⟨p, hp, ht⟩
  · rintro (⟨p, hp, ht⟩ | ⟨p, hp, ht⟩)
    · exact ⟨p, Or.inl hp, ht⟩
    · exact ⟨p, Or.inr hp, ht⟩

theorem RunRules.terms_subset (R : List Rule) (d : Database) : d.terms ⊆ (RunRules R d).terms :=
  fun _ ht => RunRules.mem_terms_iff.mpr (Or.inl ht)

theorem RunRules.eqs_subset (R : List Rule) (d : Database) : d.eqs ⊆ (RunRules R d).eqs := by
  rw [RunRules.eq_pair]; exact Set.subset_union_left

theorem RunRules.subsumed_subset (R : List Rule) (d : Database) :
    d.subsumed ⊆ (RunRules R d).subsumed := by
  rw [RunRules.eq_pair]; exact Set.subset_union_left

theorem Good.runRules {d : Database} (h : Good d) {R : List Rule} (hu : ∀ r ∈ R, r.UnionFree) :
    Good (RunRules R d) where
  diag := RunRules.diag h.noUnions hu
  marks := by
    intro t ht
    have hterms : t ∈ (RunRules R d).terms := by
      rw [RunRules.eq_pair] at ht
      rcases ht with ht | ht
      · exact RunRules.terms_subset R d (h.marks t ht).2
      · have := RunMarks.mem_writes ht
        rw [RunRules.eq_pair]
        exact ⟨(t, t), Or.inr this, Or.inl (Term.self_mem_subterms t)⟩
    refine ⟨?_, hterms⟩
    rw [RunRules.eq_pair] at ht
    rcases ht with ht | ht
    · exact (h.marks t ht).1
    · exact RunMarks.isApp ht

/-- A round from two good states with the same terms and subsumed rows reaches two states
with the same terms and subsumed rows. -/
theorem Good.round_same {d e : Database} (hd : Good d) (he : Good e) (ht : d.terms = e.terms)
    (hs : d.subsumed = e.subsumed) (R : List Rule) :
    (RunRules R d).terms = (RunRules R e).terms ∧
      (RunRules R d).subsumed = (RunRules R e).subsumed := by
  have hm : d.SameMeaning e := hd.sameMeaning_of he ht hs
  have hw := RunWrites.eq_of_sameMeaning_terms hm ht R
  have hx := RunMarks.eq_of_sameMeaning_terms hm ht R
  constructor
  · ext t
    rw [RunRules.mem_terms_iff, RunRules.mem_terms_iff, ht, hw]
  · rw [RunRules.eq_pair, RunRules.eq_pair]
    simp only
    rw [hs, hx]

/-- The pre-state of a finite execution is contained in its result. -/
theorem Reach.contained' {S : Schedule} {d e : Database} (h : Reach d S e) : d.Contained e := by
  induction h with
  | run => exact ⟨RunRules.eqs_subset _ _, RunRules.subsumed_subset _ _⟩
  | seq _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | fixpoint _ _ ih => exact ih
  | again _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Egglog.Provenance
