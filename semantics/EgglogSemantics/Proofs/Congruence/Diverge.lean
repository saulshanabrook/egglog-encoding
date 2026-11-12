import EgglogSemantics.Proofs.Congruence.Simulate
import EgglogSemantics.Proofs.Divergence

/-! Divergence correspondence for the congruence pass: a source schedule has a
nonterminating execution exactly when its compilation does. -/

namespace Egglog.Congruence

variable {P : Program}

/-! ### Divergence excludes finite results -/

theorem not_reach_of_infinitePasses {S : Schedule} {d e : Database}
    (hr : Reach d (.saturate S) e) (hi : InfinitePasses S d) : False := by
  generalize hT : Schedule.saturate S = T at hr
  induction hr with
  | run => cases hT
  | seq => cases hT
  | @fixpoint d e S' hp heq _ =>
    cases hT
    obtain ⟨trace, h0, hstep⟩ := hi
    have h1 := hstep 0
    rw [h0] at h1
    exact h1.2 (hp.det h1.1 ▸ heq)
  | @again d e₁ e S' hp _ _ _ ih₂ =>
    cases hT
    obtain ⟨trace, h0, hstep⟩ := hi
    have h1 := hstep 0
    rw [h0] at h1
    refine ih₂ ⟨fun n => trace (n + 1), (hp.det h1.1).symm, fun n => hstep (n + 1)⟩ rfl

/-- A diverging schedule reaches no state. -/
theorem Diverges.not_reach {S : Schedule} {d e : Database} (hd : Diverges d S)
    (hr : Reach d S e) : False := by
  induction hd generalizing e with
  | seqLeft _ ih =>
    obtain ⟨m, h₁, _⟩ := Reach.seq_inv hr
    exact ih h₁
  | seqRight h₁ _ ih =>
    obtain ⟨m, h₁', h₂⟩ := Reach.seq_inv hr
    rw [← h₁.det h₁'] at h₂
    exact ih h₂
  | body _ ih =>
    obtain ⟨d₁, hp, _⟩ := cmdStep_saturate_iff.mp hr
    exact ih hp
  | later h₁ hn _ ih =>
    obtain ⟨d₂, hp, h⟩ := cmdStep_saturate_iff.mp hr
    rcases h with ⟨heq, rfl⟩ | ⟨_, ht⟩
    · exact hn (h₁.det hp ▸ heq)
    · exact ih (h₁.det hp ▸ ht)
  | forever hi => exact not_reach_of_infinitePasses hr hi

/-! ### Transporting infinite traces -/

/-- The forward simulation for a partner relation. -/
theorem fwd_relC (hP : P.Fragment) (hO : P.schedule.OrderingFree) {S : Schedule}
    (hS : S.rules ⊆ P.rules) {src d e : Database} (hsrc : SrcInv P src) (hrel : RelC P src d)
    (hr : Reach src S e) : ∃ d', Reach d (encS P S) d' ∧ RelC P e d' := by
  obtain ⟨x, hx, hm, hd, hc⟩ := hrel
  obtain ⟨d', x', hd', hx', hm', hrel', hc', _⟩ := sim_fwd hP hO S hS hsrc hx hm hd hc hr
  exact ⟨d', hd', x', hx', hm', hrel', hc'⟩

/-- The backward simulation for a partner relation. -/
theorem bwd_relC (hP : P.Fragment) (hO : P.schedule.OrderingFree) {S : Schedule}
    (hS : S.rules ⊆ P.rules) {src d d' : Database} (hsrc : SrcInv P src) (hrel : RelC P src d)
    (hr : Reach d (encS P S) d') : ∃ e, Reach src S e ∧ RelC P e d' := by
  obtain ⟨x, hx, hm, hd, hc⟩ := hrel
  obtain ⟨e, x', he, hx', hm', hrel', hc', _⟩ := sim_bwd hP hO S hS hsrc hx hm hd hc hr
  exact ⟨e, he, x', hx', hm', hrel', hc'⟩

theorem RelC.not_sameMeaning {src e d d' : Database} (h₁ : RelC P src d) (h₂ : RelC P e d')
    (hn : ¬ src.SameMeaning e) : ¬ d.SameMeaning d' := by
  obtain ⟨x, hx, hm, hd, _⟩ := h₁
  obtain ⟨y, hy, hm', hd', _⟩ := h₂
  exact not_sameMeaning_of_source hx hy hm hm' hd hd' hn

theorem RelC.sameMeaning {src e d d' : Database} (h₁ : RelC P src d) (h₂ : RelC P e d')
    (h : d.SameMeaning d') : src.SameMeaning e := by
  by_contra hn
  exact h₁.not_sameMeaning h₂ hn h

/-- A source trace of changing passes gives a compiled one. -/
theorem infinitePasses_fwd (hP : P.Fragment) (hO : P.schedule.OrderingFree) {S : Schedule}
    (hS : S.rules ⊆ P.rules) {src d : Database} (hsrc : SrcInv P src) (hrel : RelC P src d)
    (hi : InfinitePasses S src) : InfinitePasses (encS P S) d := by
  obtain ⟨trace, h0, hstep⟩ := hi
  have hinv : ∀ n, SrcInv P (trace n) := by
    intro n
    induction n with
    | zero => rw [h0]; exact hsrc
    | succ n ih => exact ih.reach hP hS (hstep n).1
  -- The compiled trace, chosen pass by pass.
  let step : ∀ n, {d' // RelC P (trace n) d'} → {d' // RelC P (trace (n + 1)) d'} := fun n p =>
    ⟨Classical.choose (fwd_relC hP hO hS (hinv n) p.2 (hstep n).1),
      (Classical.choose_spec (fwd_relC hP hO hS (hinv n) p.2 (hstep n).1)).2⟩
  have hstepR : ∀ n (p : {d' // RelC P (trace n) d'}), Reach p.1 (encS P S) (step n p).1 :=
    fun n p => (Classical.choose_spec (fwd_relC hP hO hS (hinv n) p.2 (hstep n).1)).1
  let chain : ∀ n, {d' // RelC P (trace n) d'} := fun n =>
    Nat.rec (motive := fun n => {d' // RelC P (trace n) d'}) ⟨d, h0 ▸ hrel⟩ step n
  refine ⟨fun n => (chain n).1, rfl, fun n => ⟨?_, ?_⟩⟩
  · exact hstepR n (chain n)
  · intro hsame
    exact (hstep n).2 ((chain n).2.sameMeaning (chain (n + 1)).2 hsame)

/-- A compiled trace of changing passes gives a source trace, pass by pass. -/
theorem trace_bwd (hP : P.Fragment) (hO : P.schedule.OrderingFree) {S : Schedule}
    (hS : S.rules ⊆ P.rules) {src d : Database} (hsrc : SrcInv P src) (hrel : RelC P src d)
    {trace' : Nat → Database} (h0 : trace' 0 = d)
    (hstep : ∀ n, Reach (trace' n) (encS P S) (trace' (n + 1))) :
    ∃ trace : Nat → Database, trace 0 = src ∧
      (∀ n, Reach (trace n) S (trace (n + 1))) ∧ ∀ n, RelC P (trace n) (trace' n) := by
  -- States carry their invariant and relation.
  let Carrier := fun n => {e // SrcInv P e ∧ RelC P e (trace' n)}
  let step : ∀ n, Carrier n → Carrier (n + 1) := fun n p =>
    ⟨Classical.choose (bwd_relC hP hO hS p.2.1 p.2.2 (hstep n)),
      (p.2.1.reach hP hS (Classical.choose_spec (bwd_relC hP hO hS p.2.1 p.2.2 (hstep n))).1),
      (Classical.choose_spec (bwd_relC hP hO hS p.2.1 p.2.2 (hstep n))).2⟩
  have hstepR : ∀ n (p : Carrier n), Reach p.1 S (step n p).1 :=
    fun n p => (Classical.choose_spec (bwd_relC hP hO hS p.2.1 p.2.2 (hstep n))).1
  let chain : ∀ n, Carrier n := fun n =>
    Nat.rec (motive := Carrier) ⟨src, hsrc, h0 ▸ hrel⟩ step n
  refine ⟨fun n => (chain n).1, rfl, fun n => ?_, fun n => (chain n).2.2⟩
  exact hstepR n (chain n)

/-! ### Divergence -/

/-- The statement of divergence correspondence for a schedule. -/
def Div (P : Program) (S : Schedule) : Prop :=
  ∀ {src d : Database}, SrcInv P src → RelC P src d → (Diverges src S ↔ Diverges d (encS P S))

/-- A compiled run never diverges: the rebuild saturation terminates. -/
theorem run_not_diverges (hP : P.Fragment) {R : List Rule} (hR : ∀ r ∈ R, r ∈ P.rules)
    {src d : Database} (hrel : RelC P src d) :
    ¬ Diverges d (encS P (.run R)) := by
  intro h
  rcases Diverges.append_iff.mp h with h | ⟨mid, hmid, h⟩
  · exact not_cmdDiverges_of_allConstructors (S := .run _) trivial h
  · obtain ⟨x, hx, hm, hd, hc⟩ := hrel
    cases hmid
    have hrel' := run_rel hd hc hx.wf (fun r hr => ruleOk_of_fragment hP (hR r hr))
      (fun r hr σ hσ => source_writes_some hP hx (hR r hr) hσ)
      ((hx.runRules hP hR).avoids hP)
    obtain ⟨e, he⟩ := rebuild_exists (P := P) hrel'
    exact Diverges.not_reach h he

/-- After a source fixpoint the compiled saturation does not diverge. -/
theorem not_diverges_after_fixpoint (hP : P.Fragment) (hO : P.schedule.OrderingFree)
    {S : Schedule} (hS : S.rules ⊆ P.rules) {src e d : Database} (hsrc : SrcInv P src)
    (hp : Reach src S e) (heq : src.SameMeaning e) (hrel : RelC P e d) :
    ¬ Diverges d (.saturate (encS P S)) := by
  intro hdiv
  obtain ⟨x, hx, hm, hd, hc⟩ := hrel
  have he : SrcInv P e := hsrc.reach hP hS hp
  have hstable : ∀ x y, SrcInv P x → e.SameMeaning x → Reach x S y → e.SameMeaning y := by
    intro x y hx' hex hxy
    obtain ⟨y', hy', hey'⟩ := reach_transport hP hO hS hsrc hx' (heq.trans hex) hp
    rw [hy'.det hxy] at hey'
    exact hey'
  have hpass : ∀ x, SrcInv P x → e.SameMeaning x → ∃ y, Reach x S y := by
    intro x hx' hex
    obtain ⟨y', hy', _⟩ := reach_transport hP hO hS hsrc hx' (heq.trans hex) hp
    exact ⟨y', hy'⟩
  obtain ⟨d', _, hd', _⟩ := extra_passes hP hO (sim_fwd hP hO S hS) hstable hpass hx hm d x
    (Rounds.refl x) hm hd hc
  exact Diverges.not_reach hdiv hd'

/-- Divergence corresponds for every source schedule. -/
theorem sim_div (hP : P.Fragment) (hO : P.schedule.OrderingFree) :
    ∀ (S : Schedule), S.rules ⊆ P.rules → Div P S
  | .run R, hS => by
      rename_i src d
      intro hsrc hrel
      constructor
      · intro h; exact (not_cmdDiverges_of_allConstructors (S := .run R) trivial h).elim
      · intro h; exact (run_not_diverges hP (fun r hr => hS hr) hrel h).elim
  | .seq S₁ S₂, hS => by
      rename_i src d
      intro hsrc hrel
      have hS₁ : S₁.rules ⊆ P.rules := fun r hr => hS (List.mem_append_left _ hr)
      have hS₂ : S₂.rules ⊆ P.rules := fun r hr => hS (List.mem_append_right _ hr)
      have ih₁ : Div P S₁ := sim_div hP hO S₁ hS₁
      have ih₂ : Div P S₂ := sim_div hP hO S₂ hS₂
      change Diverges src (.seq S₁ S₂) ↔ Diverges d (.seq (encS P S₁) (encS P S₂))
      rw [Diverges.append_iff, Diverges.append_iff]
      constructor
      · rintro (h | ⟨mid, hmid, h⟩)
        · exact Or.inl ((ih₁ hsrc hrel).mp h)
        · obtain ⟨d₁, hd₁, hrel₁⟩ := fwd_relC hP hO hS₁ hsrc hrel hmid
          exact Or.inr ⟨d₁, hd₁, (ih₂ (hsrc.reach hP hS₁ hmid) hrel₁).mp h⟩
      · rintro (h | ⟨d₁, hd₁, h⟩)
        · exact Or.inl ((ih₁ hsrc hrel).mpr h)
        · obtain ⟨mid, hmid, hrel₁⟩ := bwd_relC hP hO hS₁ hsrc hrel hd₁
          exact Or.inr ⟨mid, hmid, (ih₂ (hsrc.reach hP hS₁ hmid) hrel₁).mpr h⟩
  | .saturate S, hS => by
      rename_i src d
      intro hsrc hrel
      have hS' : S.rules ⊆ P.rules := hS
      have ih : Div P S := sim_div hP hO S hS'
      change Diverges src (.saturate S) ↔ Diverges d (.saturate (encS P S))
      constructor
      · intro h
        generalize hT : Schedule.saturate S = T at h
        induction h generalizing d with
        | seqLeft => cases hT
        | seqRight => cases hT
        | body hb =>
          cases hT
          exact .body ((ih hsrc hrel).mp hb)
        | @later src e₁ S' hp hn _ ih₂ =>
          cases hT
          obtain ⟨d₁, hd₁, hrel₁⟩ := fwd_relC hP hO hS' hsrc hrel hp
          exact .later hd₁ (hrel.not_sameMeaning hrel₁ hn) (ih₂ (hsrc.reach hP hS' hp) hrel₁ rfl)
        | forever hi =>
          cases hT
          exact .forever (infinitePasses_fwd hP hO hS' hsrc hrel hi)
      · intro h
        change Diverges d (.saturate (encS P S)) at h
        generalize hT : Schedule.saturate (encS P S) = T at h
        induction h generalizing src with
        | seqLeft => cases hT
        | seqRight => cases hT
        | body hb =>
          cases hT
          exact .body ((ih hsrc hrel).mpr hb)
        | @later d d₁ S' hp hn hdiv ih₂ =>
          cases hT
          obtain ⟨e₁, he₁, hrel₁⟩ := bwd_relC hP hO hS' hsrc hrel hp
          by_cases hsame : src.SameMeaning e₁
          · exact (not_diverges_after_fixpoint hP hO hS' hsrc he₁ hsame hrel₁ hdiv).elim
          · exact .later he₁ hsame (ih₂ (hsrc.reach hP hS' he₁) hrel₁ rfl)
        | @forever d S' hi =>
          cases hT
          obtain ⟨trace', h0, hstep⟩ := hi
          obtain ⟨trace, h0', hpass, hrel'⟩ :=
            trace_bwd hP hO hS' hsrc hrel h0 (fun n => (hstep n).1)
          by_cases hall : ∀ n, ¬ (trace n).SameMeaning (trace (n + 1))
          · exact .forever ⟨trace, h0', fun n => ⟨hpass n, hall n⟩⟩
          · exfalso
            push Not at hall
            obtain ⟨n, hn⟩ := hall
            have hinv : SrcInv P (trace n) := by
              clear hn
              induction n with
              | zero => rw [h0']; exact hsrc
              | succ n ih => exact ih.reach hP hS' (hpass n)
            -- The compiled trace from `n + 1` is still infinite, yet the source has settled.
            have hdiv : Diverges (trace' (n + 1)) (.saturate (encS P S)) :=
              .forever ⟨fun k => trace' (n + 1 + k), rfl, fun k => by
                have := hstep (n + 1 + k)
                rwa [show n + 1 + k + 1 = n + 1 + (k + 1) by omega] at this⟩
            exact not_diverges_after_fixpoint hP hO hS' hinv (hpass n) hn (hrel' (n + 1)) hdiv

end Egglog.Congruence
