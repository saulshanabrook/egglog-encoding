import EgglogSemantics.Proofs.DiagonalRound
import EgglogSemantics.Proofs.StatePreservation

/-! Subsumption retains equations, columns, and historical existence. -/

namespace Egglog

/-- On a diagonal store, semantic existence is exactly stored subterm membership. -/
theorem Cong.iff_eq_and_mem_of_diag {db : Database} (hd : db.Diag) {a b : Term} :
    Cong db a b ↔ a = b ∧ a ∈ db.terms := by
  constructor
  · intro h
    induction h using Cong.rec (motive_2 := fun as bs _ => as = bs) with
    | direct hp => exact ⟨hd _ hp, ⟨_, hp, Or.inl (.refl _)⟩⟩
    | child _ hs ih => exact ⟨rfl, db.subtermClosed _ ih.2 (.arg hs (.refl _))⟩
    | symm _ ih => exact ⟨ih.1.symm, ih.1 ▸ ih.2⟩
    | trans _ _ ih ih' => exact ⟨ih.1.trans ih'.1, ih.2⟩
    | congr _ _ ih ih' => exact ⟨congrArg _ ih', ih.2⟩
    | nil => rfl
    | cons _ _ ih ih' => exact congrArg₂ List.cons ih.1 ih'
  · rintro ⟨rfl, ha⟩
    exact Database.toCong ha

/-- Marking rows leaves congruence unchanged. -/
theorem Database.cong_addSubsumed_iff (db : Database) (X : Set Term) (a b : Term) :
    Cong (db.addSubsumed X) a b ↔ Cong db a b :=
  Cong.iff_of_eqs_eq (d := db.addSubsumed X) (e := db) rfl

/-- An asserted subsume retains the row and all its columns. -/
theorem Database.mem_subsume_terms (db : Database) (t s : Term) (hs : s ∈ t.subterms) :
    s ∈ ((db.addTerm t).addSubsumed {t}).terms := by
  exact Database.addTerm_terms ▸ Or.inr hs

/-- Marks only hide rows from lookups; forgetting them restores semantic existence. -/
theorem Database.live_forgetSubsumed (db : Database) :
    db.forgetSubsumed.live = {t | Cong db t t} := by
  ext t
  simp only [Database.live_of_subsumed_empty (db := db.forgetSubsumed) rfl, Set.mem_setOf_eq,
    Cong.iff_of_eqs_eq (d := db.forgetSubsumed) (e := db) rfl]

/-- Every mark names a term that semantically exists. -/
def Database.MarksExist (db : Database) : Prop :=
  ∀ t ∈ db.subsumed, Cong db t t

theorem Database.MarksExist.empty : Database.empty.MarksExist := by
  simp [Database.MarksExist, Database.empty]

theorem Action.mark_mem_write {σ : Env} {a : Action} {W : Set (Term × Term)}
    {X : Set Term} (hw : a.write σ = some W) (hx : a.mark σ = some X)
    {t : Term} (ht : t ∈ X) : (t, t) ∈ W := by
  cases a with
  | expr e | union e f =>
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hx
    exact ht.elim
  | subsume f es =>
    obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp hx
    obtain rfl := ht
    have hW : W = {(.app f ts, .app f ts)} :=
      (Option.some.inj (by simpa [Action.write, hts] using hw)).symm
    exact hW ▸ Set.mem_singleton _

theorem Action.marks_mem_writes {σ : Env} {as : List Action} {W : Set (Term × Term)}
    {X : Set Term} (hw : Action.writes σ as = some W) (hx : Action.marks σ as = some X)
    {t : Term} (ht : t ∈ X) : (t, t) ∈ W := by
  induction as generalizing W X with
  | nil => cases Option.some.inj hx; exact ht.elim
  | cons a as ih =>
    obtain ⟨U, hu, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨V, hv, rfl⟩ := Option.map_eq_some_iff.mp hw
    obtain ⟨Y, hy, hx⟩ := Option.bind_eq_some_iff.mp hx
    obtain ⟨Z, hz, rfl⟩ := Option.map_eq_some_iff.mp hx
    exact ht.elim (fun ht => Or.inl (Action.mark_mem_write hu hy ht))
      (fun ht => Or.inr (ih hv hz ht))

theorem RunMarks.mem_writes {rs : List Rule} {db : Database} {t : Term}
    (ht : t ∈ RunMarks rs db) : (t,t) ∈ RunWrites rs db := by
  obtain ⟨X, ⟨r, hr, σ, hσ, hx⟩, ht⟩ := ht
  have hs : (Action.writes σ r.actions).isSome = true := by
    rw [← Action.marks_isSome, hx]; rfl
  obtain ⟨W, hw⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨W, ⟨r, hr, σ, hσ, hw⟩, Action.marks_mem_writes hw hx ht⟩

theorem RunRules.marksExist {rs : List Rule} {db : Database} (h : db.MarksExist) :
    (RunRules rs db).MarksExist := by
  rw [RunRules.eq_pair]
  intro t ht
  rcases ht with ht | ht
  · exact (h t ht).mono_eqs Set.subset_union_left
  · exact .direct (Or.inr (RunMarks.mem_writes ht))

theorem Database.SameRow.eq_of_diag {db : Database} (hd : db.Diag) {s t : Term}
    (h : db.SameRow s t) : s = t := by
  obtain ⟨f, as, bs, rfl, rfl, hc⟩ := h
  rw [hc.eq_of_diag hd]

theorem Database.SameRow.self_app {db : Database} {f : FnName} {ts : List Term}
    (h : Cong db (.app f ts) (.app f ts)) : db.SameRow (.app f ts) (.app f ts) := by
  refine ⟨f, ts, ts, rfl, rfl, CongList.forall₂.mpr ?_⟩
  exact List.forall₂_same.mpr (fun t ht => h.subterm (.arg ht (.refl _)))

theorem Database.SameMeaning.app_marks_iff_of_diag {d e : Database}
    (h : d.SameMeaning e) (hd : d.Diag) (he : e.Diag)
    (hmd : d.MarksExist) (hme : e.MarksExist) (f : FnName) (ts : List Term) :
    Term.app f ts ∈ d.subsumed ↔ Term.app f ts ∈ e.subsumed := by
  have forward {d e : Database} (h : d.SameMeaning e) (he : e.Diag)
      (hm : d.MarksExist) (ht : Term.app f ts ∈ d.subsumed) :
      Term.app f ts ∈ e.subsumed := by
    classical
    by_contra hn
    have hl : Term.app f ts ∈ e.live := ⟨(h.congr _ _).mp (hm _ ht), by
      rintro ⟨u, hu, hr⟩
      exact hn (hr.eq_of_diag he ▸ hu)⟩
    exact ((h.live _).mpr hl).2 ⟨_, ht, Database.SameRow.self_app (hm _ ht)⟩
  exact ⟨forward h he hmd, forward h.symm hd hme⟩

/-- Literal marks are unobservable; application marks determine liveness. -/
theorem Database.SameMeaning.of_congr_app_marks {d e : Database}
    (hc : ∀ a b, Cong d a b ↔ Cong e a b)
    (hx : ∀ f ts, Term.app f ts ∈ d.subsumed ↔ Term.app f ts ∈ e.subsumed) :
    d.SameMeaning e := by
  refine ⟨hc, fun t => and_congr (hc t t) (not_congr ?_)⟩
  constructor
  · rintro ⟨_, hu, f, as, bs, rfl, rfl, hab⟩
    exact ⟨_, (hx f bs).mp hu, f, as, bs, rfl, rfl,
      (CongList.iff_of_congr hc).mp hab⟩
  · rintro ⟨_, hu, f, as, bs, rfl, rfl, hab⟩
    exact ⟨_, (hx f bs).mpr hu, f, as, bs, rfl, rfl,
      (CongList.iff_of_congr hc).mpr hab⟩

theorem Database.SameMeaning.addEqs_of_app_marks {d e : Database}
    (h : d.SameMeaning e)
    (hx : ∀ f ts, Term.app f ts ∈ d.subsumed ↔ Term.app f ts ∈ e.subsumed)
    (W : Set (Term × Term)) : (d.addEqs W).SameMeaning (e.addEqs W) := by
  apply Database.SameMeaning.of_congr_app_marks (d := d.addEqs W) (e := e.addEqs W)
    (hx := hx)
  have forward {d e : Database} (hc : ∀ a b, Cong d a b → Cong e a b)
      {a b : Term} (ht : Cong (d.addEqs W) a b) : Cong (e.addEqs W) a b := by
    apply Cong.of_assertions ?_ ht
    intro p hp
    exact hp.elim (fun hp => (hc _ _ (.direct hp)).mono_eqs Set.subset_union_left)
      (fun hp => .direct (Or.inr hp))
  exact fun a b => ⟨forward (fun a b => (h.congr a b).mp),
    forward (fun a b => (h.congr a b).mpr)⟩

end Egglog
