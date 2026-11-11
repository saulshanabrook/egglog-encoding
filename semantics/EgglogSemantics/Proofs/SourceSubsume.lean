import EgglogSemantics.Proofs.SourceModel
import EgglogSemantics.Proofs.Subsume

/-! Ordering-free rounds preserve source meaning even when heads subsume rows. Marks are
transported by their constructor and congruent children, including after new unions. -/

namespace Egglog

theorem Database.SameRow.trans {d : Database} {s t u : Term}
    (h : d.SameRow s t) (h' : d.SameRow t u) : d.SameRow s u := by
  obtain ⟨f, as, bs, rfl, rfl, hab⟩ := h
  obtain ⟨g, cs, ds, heq, rfl, hcd⟩ := h'
  obtain ⟨rfl, rfl⟩ := Term.app.inj heq
  exact ⟨f, as, ds, rfl, rfl, hab.trans hcd⟩

theorem Database.SameRow.mono {d e : Database} {s t : Term}
    (h : d.SameRow s t) (hc : ∀ a b, Cong d a b → Cong e a b) : e.SameRow s t := by
  obtain ⟨f, as, bs, rfl, rfl, hab⟩ := h
  refine ⟨f, as, bs, rfl, rfl, CongList.forall₂.mpr ?_⟩
  exact (CongList.forall₂.mp hab).imp (fun _ _ h => hc _ _ h)

/-- A subsumed application has a marked spelling in every equivalent state. -/
theorem Database.SameMeaning.marked {d e : Database} (h : d.SameMeaning e)
    (hm : d.MarksExist) {f : FnName} {as : List Term} (hs : Term.app f as ∈ d.subsumed) :
    ∃ u ∈ e.subsumed, e.SameRow (.app f as) u := by
  classical
  by_contra hn
  have hl : Term.app f as ∈ e.live := ⟨(h.congr _ _).mp (hm _ hs), hn⟩
  exact ((h.live _).mpr hl).2 ⟨_, hs, Database.SameRow.self_app (hm _ hs)⟩

namespace SourceMeaning
open InferredFacts

private theorem endpoints {d : Database} {p : Term × Term} (h : p ∈ d.eqs) :
    p.1 ∈ d.terms ∧ p.2 ∈ d.terms :=
  ⟨⟨p, h, Or.inl (.refl _)⟩, ⟨p, h, Or.inr (.refl _)⟩⟩

private theorem eval_cong_held {d : Database} (hd : d.WF) {σ τ : Env}
    (hσ : EnvRelated d σ τ) {e : Expr} (hn : e.OrderingFree) {t u : Term}
    (ht : e.eval σ = some t) (hu : e.eval τ = some u) (hh : u ∈ d.terms) : Cong d t u := by
  obtain ⟨u', hu', hi⟩ := eval_interpret (hσ.interpret hd) e hn ht
  have huu : u' = u := Option.some.inj (hu'.symm.trans hu)
  subst u'
  exact congr_of_interpret t hh (hi.trans (interpret_of_held_core u hh))

private theorem evalList_cong_held {d : Database} (hd : d.WF) {σ τ : Env}
    (hσ : EnvRelated d σ τ) {es : List Expr} (hn : Expr.OrderingFreeList es) {ts us : List Term}
    (ht : Expr.evalList es σ = some ts) (hu : Expr.evalList es τ = some us)
    (hh : ∀ u ∈ us, u ∈ d.terms) : CongList d ts us := by
  obtain ⟨us', hu', hi⟩ := evalList_interpret (hσ.interpret hd) es hn ht
  have huu : us' = us := Option.some.inj (hu'.symm.trans hu)
  subst us'
  apply congrList_of_interpret ts hh
  rw [hi, interpretList_eq_map]
  exact List.map_congr_left fun u hu => interpret_of_held_core u (hh u hu)

private theorem write_cong {d : Database} (hd : d.WF) {σ τ : Env}
    (hσ : EnvRelated d σ τ) {a : Action} (hn : a.OrderingFree) {W V : Set (Term × Term)}
    (hw : a.write σ = some W) (hv : a.write τ = some V) (hV : V ⊆ d.eqs) :
    ∀ q ∈ W, Cong d q.1 q.2 := by
  cases a with
  | expr e =>
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hw
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp hv
    have hc := eval_cong_held hd hσ hn ht hu (endpoints (hV rfl)).1
    rintro q rfl
    exact hc.trans hc.symm
  | union a b =>
    obtain ⟨s, hs, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨t, ht, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨u, hu, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨v, hv', hv⟩ := Option.bind_eq_some_iff.mp hv
    split at hw
    next => cases hw
    next =>
      split at hv
      next => cases hv
      next =>
        obtain rfl := Option.some.inj hw
        obtain rfl := Option.some.inj hv
        have he := hV (Set.mem_singleton (u, v))
        have hsu := eval_cong_held hd hσ hn.1 hs hu (endpoints he).1
        have htv := eval_cong_held hd hσ hn.2 ht hv' (endpoints he).2
        rintro q rfl
        exact hsu.trans ((Cong.direct he).trans htv.symm)
  | subsume f es =>
    obtain ⟨ts, ht, rfl⟩ := Option.map_eq_some_iff.mp hw
    obtain ⟨us, hu, rfl⟩ := Option.map_eq_some_iff.mp hv
    have hh := (endpoints (hV (Set.mem_singleton _))).1
    have hc := eval_cong_held hd hσ (e := .app f es) (t := .app f ts) (u := .app f us) hn
      (by simp [Expr.eval, ht]) (by simp [Expr.eval, hu]) hh
    rintro q rfl
    exact hc.trans hc.symm

private theorem writes_cong {d : Database} (hd : d.WF) {σ τ : Env}
    (hσ : EnvRelated d σ τ) {as : List Action} (hn : Actions.OrderingFree as)
    {W V : Set (Term × Term)} (hw : Action.writes σ as = some W)
    (hv : Action.writes τ as = some V) (hV : V ⊆ d.eqs) : ∀ q ∈ W, Cong d q.1 q.2 := by
  induction as generalizing W V with
  | nil => obtain rfl := Option.some.inj hw; simp
  | cons a as ih =>
    obtain ⟨W₁, hw₁, hw⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨W₂, hw₂, rfl⟩ := Option.map_eq_some_iff.mp hw
    obtain ⟨V₁, hv₁, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨V₂, hv₂, rfl⟩ := Option.map_eq_some_iff.mp hv
    intro q hq
    exact hq.elim (write_cong hd hσ hn.1 hw₁ hv₁ (fun _ h => hV (Or.inl h)) q)
      (ih hn.2 hw₂ hv₂ (fun _ h => hV (Or.inr h)) q)

private theorem mark_transport {d : Database} (hd : d.WF) {σ τ : Env}
    (hσ : EnvRelated d σ τ) {a : Action} (hn : a.OrderingFree) {X Y : Set Term}
    (hx : a.mark σ = some X) (hy : a.mark τ = some Y) (hY : Y ⊆ d.terms) :
    ∀ t ∈ X, ∃ u ∈ Y, d.SameRow t u := by
  cases a with
  | expr _ | union _ _ =>
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hx
    simp
  | subsume f es =>
    obtain ⟨ts, ht, rfl⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨us, hu, rfl⟩ := Option.map_eq_some_iff.mp hy
    have hh := hY (Set.mem_singleton (Term.app f us))
    have hc := evalList_cong_held hd hσ hn ht hu
      (fun u hu => d.subtermClosed _ hh (.arg hu (.refl _)))
    rintro t rfl
    exact ⟨_, rfl, f, ts, us, rfl, rfl, hc⟩

private theorem marks_transport {d : Database} (hd : d.WF) {σ τ : Env}
    (hσ : EnvRelated d σ τ) {as : List Action} (hn : Actions.OrderingFree as)
    {X Y : Set Term} (hx : Action.marks σ as = some X) (hy : Action.marks τ as = some Y)
    (hY : Y ⊆ d.terms) : ∀ t ∈ X, ∃ u ∈ Y, d.SameRow t u := by
  induction as generalizing X Y with
  | nil => obtain rfl := Option.some.inj hx; simp
  | cons a as ih =>
    obtain ⟨X₁, hx₁, hx⟩ := Option.bind_eq_some_iff.mp hx
    obtain ⟨X₂, hx₂, rfl⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨Y₁, hy₁, hy⟩ := Option.bind_eq_some_iff.mp hy
    obtain ⟨Y₂, hy₂, rfl⟩ := Option.map_eq_some_iff.mp hy
    intro t ht
    rcases ht with ht | ht
    · obtain ⟨u, hu, hr⟩ := mark_transport hd hσ hn.1 hx₁ hy₁ (fun _ h => hY (Or.inl h)) t ht
      exact ⟨u, Or.inl hu, hr⟩
    · obtain ⟨u, hu, hr⟩ := ih hn.2 hx₂ hy₂ (fun _ h => hY (Or.inr h)) t ht
      exact ⟨u, Or.inr hu, hr⟩

/-- A source round always extends the stored equations and marks. -/
theorem round_contains (d : Database) (R : List Rule) : d.Contained (RunRules R d) := by
  rw [RunRules.eq_pair]
  exact ⟨Set.subset_union_left, Set.subset_union_left⟩

private theorem firing_rebind {d e : Database} (hd : d.WF) (he : e.WF)
    (h : d.SameMeaning e) (hre : e.HasReps) {r : Rule} (hn : r.OrderingFree)
    {σ : Env} (hσ : QueryMatches d r.query σ) :
    ∃ τ, QueryMatches e r.query τ ∧ EnvRelated e σ τ := by
  obtain ⟨σ', hσ', hag⟩ := hσ.exists_validQuerySubst
  obtain ⟨τ, hτ, hr⟩ := validQuerySubst_transport hd he h hre hn.1 hσ'
  obtain ⟨τ', hτ', hag'⟩ := hτ.exists_queryMatches
  refine ⟨τ', hτ', fun v t ht => ?_⟩
  obtain ⟨u, hu, hc⟩ := hr v t ((hag v).trans ht)
  exact ⟨u, (hag' v).trans hu, hc⟩

private theorem round_congr_forward {d e : Database} (hd : d.WF) (he : e.WF)
    (h : d.SameMeaning e) (hre : e.HasReps) {R : List Rule}
    (hn : ∀ r ∈ R, r.OrderingFree)
    (hf : ∀ r ∈ R, ∀ τ, QueryMatches e r.query τ → ∃ V, Action.writes τ r.actions = some V)
    {a b : Term} (hc : Cong (RunRules R d) a b) : Cong (RunRules R e) a b := by
  apply Cong.of_assertions ?_ hc
  intro q hq
  rw [RunRules.eq_pair] at hq
  rcases hq with hq | ⟨W, ⟨r, hr, σ, hσ, hw⟩, hq⟩
  · exact ((h.congr _ _).mp (.direct hq)).mono (round_contains e R)
  · obtain ⟨τ, hτ, hrel⟩ := firing_rebind hd he h hre (hn r hr) hσ
    obtain ⟨V, hv⟩ := hf r hr τ hτ
    apply writes_cong (RunRules.wf he) (hrel.mono (round_contains e R)) (hn r hr).2 hw hv ?_ q hq
    intro q hq
    rw [RunRules.eq_pair]
    exact Or.inr ⟨V, ⟨r, hr, τ, hτ, hv⟩, hq⟩

private theorem round_marks_forward {d e : Database} (hd : d.WF) (he : e.WF)
    (h : d.SameMeaning e) (hm : d.MarksExist) (hre : e.HasReps) {R : List Rule}
    (hn : ∀ r ∈ R, r.OrderingFree)
    (hf : ∀ r ∈ R, ∀ τ, QueryMatches e r.query τ → ∃ V, Action.writes τ r.actions = some V)
    {f : FnName} {ts : List Term} (ht : Term.app f ts ∈ (RunRules R d).subsumed) :
    ∃ u ∈ (RunRules R e).subsumed, (RunRules R e).SameRow (.app f ts) u := by
  rw [RunRules.eq_pair] at ht
  rcases ht with ht | ⟨X, ⟨r, hr, σ, hσ, hx⟩, ht⟩
  · obtain ⟨u, hu, hs⟩ := h.marked hm ht
    exact ⟨u, (round_contains e R).subsumed hu,
      hs.mono (fun _ _ h => h.mono (round_contains e R))⟩
  · obtain ⟨τ, hτ, hrel⟩ := firing_rebind hd he h hre (hn r hr) hσ
    obtain ⟨V, hv⟩ := hf r hr τ hτ
    obtain ⟨Y, hy⟩ : ∃ Y, Action.marks τ r.actions = some Y := by
      apply Option.isSome_iff_exists.mp
      rw [Action.marks_isSome, hv]; rfl
    have hYs : Y ⊆ (RunRules R e).subsumed := by
      intro u hu
      rw [RunRules.eq_pair]
      exact Or.inr ⟨Y, ⟨r, hr, τ, hτ, hy⟩, hu⟩
    have hYt : Y ⊆ (RunRules R e).terms := by
      intro u hu
      apply (endpoints (p := (u, u)) ?_).1
      rw [RunRules.eq_pair]
      exact Or.inr ⟨V, ⟨r, hr, τ, hτ, hv⟩, Action.marks_mem_writes hv hy hu⟩
    obtain ⟨u, hu, hs⟩ := marks_transport (RunRules.wf he)
      (hrel.mono (round_contains e R)) (hn r hr).2 hx hy hYt _ ht
    exact ⟨u, hYs hu, hs⟩

/-- Ordering-free source rounds preserve congruence and live rows, allowing subsumption. -/
theorem round_sameMeaning_subsume {d e : Database} (hd : d.WF) (he : e.WF)
    (h : d.SameMeaning e) (hmd : d.MarksExist) (hme : e.MarksExist)
    (hrd : d.HasReps) (hre : e.HasReps) {R : List Rule} (hn : ∀ r ∈ R, r.OrderingFree)
    (hfd : ∀ r ∈ R, ∀ σ, QueryMatches d r.query σ → ∃ W, Action.writes σ r.actions = some W)
    (hfe : ∀ r ∈ R, ∀ σ, QueryMatches e r.query σ → ∃ W, Action.writes σ r.actions = some W) :
    (RunRules R d).SameMeaning (RunRules R e) := by
  have hc : ∀ a b, Cong (RunRules R d) a b ↔ Cong (RunRules R e) a b := fun a b =>
    ⟨round_congr_forward hd he h hre hn hfe, round_congr_forward he hd h.symm hrd hn hfd⟩
  refine ⟨hc, fun t => and_congr (hc t t) (not_congr ?_)⟩
  constructor
  · rintro ⟨_, hu, f, ts, us, rfl, rfl, hs⟩
    obtain ⟨u, hu, hr⟩ := round_marks_forward hd he h hmd hre hn hfe hu
    exact ⟨u, hu, (Database.SameRow.mono ⟨f, ts, us, rfl, rfl, hs⟩
      (fun _ _ h => (hc _ _).mp h)).trans hr⟩
  · rintro ⟨_, hu, f, ts, us, rfl, rfl, hs⟩
    obtain ⟨u, hu, hr⟩ := round_marks_forward he hd h.symm hme hrd hn hfd hu
    exact ⟨u, hu, (Database.SameRow.mono ⟨f, ts, us, rfl, rfl, hs⟩
      (fun _ _ h => (hc _ _).mpr h)).trans hr⟩

end SourceMeaning
end Egglog
