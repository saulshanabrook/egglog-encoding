import EgglogSemantics.Proofs.Congruence.Source
import EgglogSemantics.Proofs.Congruence.Fixpoint

/-! Finite execution correspondence for the congruence pass, up to source meaning.
The simulation relates a compiled state to a source state of the same meaning as the
source execution's result. Additional compiled passes after a source fixpoint terminate. -/

namespace Egglog.Congruence

variable {P : Program}

/-! ### The compiled schedule -/

/-- The compiled schedule, structurally. -/
def encS (P : Program) : Schedule → Schedule
  | .run rs => .seq (.run (rs.map (encodeRuleWith { subsumption := !P.schedule.subsumeFreeB }))) (.saturate (.run (maintenance (!P.schedule.subsumeFreeB) P)))
  | .saturate S => .saturate (encS P S)
  | .seq S₁ S₂ => .seq (encS P S₁) (encS P S₂)

theorem encodeRules_fst (i : Nat) (rs : List Rule) :
    (encodeRulesWith { subsumption := !P.schedule.subsumeFreeB } i rs).map Prod.fst = rs.map (encodeRuleWith { subsumption := !P.schedule.subsumeFreeB }) := by
  unfold encodeRulesWith
  rw [List.map_map]
  have : (Prod.fst ∘ fun ri : Rule × Nat =>
      (encodeRuleWith { subsumption := !P.schedule.subsumeFreeB } ri.1, RuleOrigin.source (i + ri.2))) = encodeRuleWith { subsumption := !P.schedule.subsumeFreeB } ∘ Prod.fst := by
    funext ri; rfl
  rw [this, ← List.map_map, List.zipIdx_map_fst]

theorem encodeSchedule_fst (P : Program) : ∀ (S : Schedule) (i : Nat),
    (encodeScheduleWith { subsumption := !P.schedule.subsumeFreeB } P S i).1 = encS P S
  | .run rs, i => by
      rcases hm : rebuildWith { subsumption := !P.schedule.subsumeFreeB } P with ⟨m, mo⟩
      have hm' := rebuild_eq (sub := !P.schedule.subsumeFreeB) P
      rw [hm] at hm'
      simp only at hm'
      simp only [encodeScheduleWith, hm, encS]
      rw [encodeRules_fst, hm']
  | .saturate S, i => by
      rcases h : encodeScheduleWith { subsumption := !P.schedule.subsumeFreeB } P S i with ⟨S', os, next⟩
      have ih := encodeSchedule_fst P S i
      rw [h] at ih
      simp only at ih
      simp only [encodeScheduleWith, h, encS, ih]
  | .seq S₁ S₂, i => by
      rcases h₁ : encodeScheduleWith { subsumption := !P.schedule.subsumeFreeB } P S₁ i with ⟨T₁, o₁, next⟩
      rcases h₂ : encodeScheduleWith { subsumption := !P.schedule.subsumeFreeB } P S₂ next with ⟨T₂, o₂, last⟩
      have ih₁ := encodeSchedule_fst P S₁ i
      have ih₂ := encodeSchedule_fst P S₂ next
      rw [h₁] at ih₁
      rw [h₂] at ih₂
      simp only at ih₁ ih₂
      simp only [encodeScheduleWith, h₁, h₂, encS, ih₁, ih₂]

theorem default_forProgram (P : Program) :
    ({} : Options).forProgram P = { subsumption := !P.schedule.subsumeFreeB } := by
  cases hs : P.schedule.subsumeFreeB <;> simp [Options.forProgram, hs]

theorem encode_schedule (P : Program) : (encode P).schedule = encS P P.schedule := by
  simp only [encode, compile, compileWith, default_forProgram]
  exact encodeSchedule_fst P P.schedule 0

theorem encode_check (P : Program) : (encode P).check = (encodeQueryWith {} P.check 0).1 := by
  simp only [encode, compile, compileWith, default_forProgram]

/-! ### The relation up to meaning -/

/-- The partner of a source state: same meaning, related to the compiled state. -/
def RelC (P : Program) (src d : Database) : Prop :=
  ∃ x, SrcInv P x ∧ src.SameMeaning x ∧ Rel (!P.schedule.subsumeFreeB) x d ∧ Canon d

/-- Two compiled states of one meaning have partners of one meaning. -/
theorem partners_sameMeaning {x y d e : Database} (hx : SrcInv P x) (hy : SrcInv P y)
    (hd : Rel (!P.schedule.subsumeFreeB) x d) (he : Rel (!P.schedule.subsumeFreeB) y e) (h : d.SameMeaning e) : x.SameMeaning y := by
  have hterms := h.terms_eq_of_diag hd.diag he.diag
  have hrow : ∀ k p, Row d k p ↔ Row e k p := by
    intro k p
    rw [← hd.shape.uf_mem_terms_iff, ← he.shape.uf_mem_terms_iff, hterms]
  apply Database.SameMeaning.of_congr_app_marks
  · intro a b
    rw [hd.cong, he.cong]
    have hv : (view d).eqs = (view e).eqs := by
      ext q
      exact hrow q.1 q.2
    exact Cong.iff_of_eqs_eq hv
  · intro f as
    rw [← hd.marker, ← he.marker]
    constructor
    · intro hm
      exact marker_atom_inv he.shape (hterms ▸ hm.mem_terms)
    · intro hm
      exact marker_atom_inv hd.shape (hterms.symm ▸ hm.mem_terms)

/-- A source pass that changes the meaning changes the compiled state too. -/
theorem not_sameMeaning_of_source {src e x y d d' : Database} (hx : SrcInv P x) (hy : SrcInv P y)
    (hsx : src.SameMeaning x) (hey : e.SameMeaning y) (hd : Rel (!P.schedule.subsumeFreeB) x d) (hd' : Rel (!P.schedule.subsumeFreeB) y d')
    (hn : ¬ src.SameMeaning e) : ¬ d.SameMeaning d' := fun h =>
  hn (hsx.trans ((partners_sameMeaning hx hy hd hd' h).trans hey.symm))

/-! ### One run -/

theorem sim_run (hP : P.Fragment) {R : List Rule} (hR : ∀ r ∈ R, r ∈ P.rules) {x d : Database}
    (hx : SrcInv P x) (hd : Rel (!P.schedule.subsumeFreeB) x d) (hc : Canon d) :
    ∃ d', Reach d (encS P (.run R)) d' ∧ Rel (!P.schedule.subsumeFreeB) (RunRules R x) d' ∧ Canon d' := by
  have hrel := run_rel hd hc hx.wf (fun r hr => ruleOk_of_fragment hP (hR r hr))
    (fun r hr σ hσ => source_writes_some hP hx (hR r hr) hσ)
    ((hx.runRules hP hR).avoids hP)
  obtain ⟨d', hd'⟩ := rebuild_exists (P := P) hrel
  obtain ⟨hrel', hc', _⟩ := rebuild_rel hrel (hx.runRules hP hR).ctors hd'
  exact ⟨d', .seq .run hd', hrel', hc'⟩

theorem sim_run_bwd (hP : P.Fragment) {R : List Rule} (hR : ∀ r ∈ R, r ∈ P.rules)
    {x d d' : Database} (hx : SrcInv P x) (hd : Rel (!P.schedule.subsumeFreeB) x d) (hc : Canon d)
    (hr : Reach d (encS P (.run R)) d') : Rel (!P.schedule.subsumeFreeB) (RunRules R x) d' ∧ Canon d' := by
  have hrel := run_rel hd hc hx.wf (fun r hr => ruleOk_of_fragment hP (hR r hr))
    (fun r hr σ hσ => source_writes_some hP hx (hR r hr) hσ)
    ((hx.runRules hP hR).avoids hP)
  obtain ⟨d₁, h₁, h₂⟩ := Reach.seq_inv hr
  cases h₁
  obtain ⟨hrel', hc', _⟩ := rebuild_rel hrel (hx.runRules hP hR).ctors h₂
  exact ⟨hrel', hc'⟩

/-! ### Extra compiled passes after a source fixpoint -/

/-- The statement of the forward simulation for a schedule. -/
def Fwd (P : Program) (S : Schedule) : Prop :=
  ∀ {src d x e : Database}, SrcInv P src → SrcInv P x → src.SameMeaning x → Rel (!P.schedule.subsumeFreeB) x d → Canon d →
    Reach src S e →
    ∃ d' x', Reach d (encS P S) d' ∧ SrcInv P x' ∧ e.SameMeaning x' ∧ Rel (!P.schedule.subsumeFreeB) x' d' ∧ Canon d' ∧
      Rounds P x x'

/-- The statement of the backward simulation for a schedule. -/
def Bwd (P : Program) (S : Schedule) : Prop :=
  ∀ {src d x d' : Database}, SrcInv P src → SrcInv P x → src.SameMeaning x → Rel (!P.schedule.subsumeFreeB) x d → Canon d →
    Reach d (encS P S) d' →
    ∃ e x', Reach src S e ∧ SrcInv P x' ∧ e.SameMeaning x' ∧ Rel (!P.schedule.subsumeFreeB) x' d' ∧ Canon d' ∧
      Rounds P x x'

/-- The universe of a stable state: terms over the program's vocabulary of bounded size. -/
theorem bounded_universe (hP : P.Fragment) (hO : P.schedule.OrderingFree) {x₀ : Database}
    (hx₀ : SrcInv P x₀) :
    ∃ U : Set Term, U.Finite ∧
      ∀ x, Rounds P x₀ x → x.SameMeaning x₀ → ∀ t ∈ x.terms, t ∈ U := by
  obtain ⟨M, hM⟩ := terms_bounded hP hO hx₀
  refine ⟨{t | Term.VocabIn P t ∧ t.nodeSize ≤ M},
    Term.finite_nodeSize_le P.ctorSet_finite P.litSet_finite M, fun x hr hm t ht => ?_⟩
  exact ⟨(hx₀.rounds hP hr).vocab t ht, hM x hr hm t ht⟩

/-- After the source has settled, the compiled saturation still terminates, at a state
related to a partner of the same meaning. -/
theorem extra_passes (hP : P.Fragment) (hO : P.schedule.OrderingFree) {S : Schedule}
    (ih : Fwd P S) {e : Database}
    (hstable : ∀ x y, SrcInv P x → e.SameMeaning x → Reach x S y → e.SameMeaning y)
    (hpass : ∀ x, SrcInv P x → e.SameMeaning x → ∃ y, Reach x S y)
    {x₀ : Database} (hx₀ : SrcInv P x₀) (hm₀ : e.SameMeaning x₀) :
    ∀ d x, Rounds P x₀ x → e.SameMeaning x → Rel (!P.schedule.subsumeFreeB) x d → Canon d →
      ∃ d' x', Reach d (.saturate (encS P S)) d' ∧ SrcInv P x' ∧ e.SameMeaning x' ∧ Rel (!P.schedule.subsumeFreeB) x' d' ∧
        Canon d' ∧ Rounds P x₀ x' := by
  obtain ⟨U, hU, hmem⟩ := bounded_universe hP hO hx₀
  intro d x hr hm hd hc
  induction hn : rank (rowSpace U) d using Nat.strong_induction_on generalizing d x with
  | _ n ihn =>
  have hx : SrcInv P x := hx₀.rounds hP hr
  obtain ⟨y, hy⟩ := hpass x hx hm
  obtain ⟨d₁, x₁, hd₁, hx₁, hyx₁, hrel₁, hc₁, hr₁⟩ :=
    ih hx hx (Database.SameMeaning.refl x) hd hc hy
  have hey : e.SameMeaning y := hstable x y hx hm hy
  have hex₁ : e.SameMeaning x₁ := hey.trans hyx₁
  have hr₁' : Rounds P x₀ x₁ := hr.trans hr₁
  by_cases hsame : d.SameMeaning d₁
  · exact ⟨d₁, x₁, .fixpoint hd₁ hsame, hx₁, hex₁, hrel₁, hc₁, hr₁'⟩
  · have hm₁ : x₁.SameMeaning x₀ := hex₁.symm.trans hm₀
    obtain ⟨hrows, hmarks⟩ := rows_subset_rowSpace hrel₁ (hmem x₁ hr₁' hm₁)
    have hcont := Reach.contained hd₁
    have hlt : rank (rowSpace U) d₁ < rank (rowSpace U) d :=
      rank_lt (rowSpace_finite hU) hd.diag hrel₁.diag hrows hmarks
        hcont.eqs hcont.subsumed hsame
    obtain ⟨d', x', hd', hx', hex', hrel', hc', hr'⟩ :=
      ihn (rank (rowSpace U) d₁) (hn ▸ hlt) d₁ x₁ hr₁' hex₁ hrel₁ hc₁ rfl
    exact ⟨d', x', .again hd₁ hsame hd', hx', hex', hrel', hc', hr'⟩

/-- The compiled passes after a source fixpoint stay related to its meaning. -/
theorem extra_passes_bwd {S : Schedule} (ih : Bwd P S) {e : Database}
    (hstable : ∀ x y, SrcInv P x → e.SameMeaning x → Reach x S y → e.SameMeaning y)
    {x₀ : Database} :
    ∀ {d d' x : Database}, Rounds P x₀ x → SrcInv P x → e.SameMeaning x → Rel (!P.schedule.subsumeFreeB) x d → Canon d →
      Reach d (.saturate (encS P S)) d' →
      ∃ x', SrcInv P x' ∧ e.SameMeaning x' ∧ Rel (!P.schedule.subsumeFreeB) x' d' ∧ Canon d' ∧ Rounds P x₀ x' := by
  intro d d' x hr hx hm hd hc hreach
  generalize hT : Schedule.saturate (encS P S) = T at hreach
  induction hreach generalizing x with
  | run => cases hT
  | seq => cases hT
  | fixpoint hp _ _ =>
    cases hT
    obtain ⟨y, x', hy, hx', hyx', hrel', hc', hr'⟩ :=
      ih hx hx (Database.SameMeaning.refl x) hd hc hp
    exact ⟨x', hx', (hstable x y hx hm hy).trans hyx', hrel', hc', hr.trans hr'⟩
  | again hp _ _ _ ih₂ =>
    cases hT
    obtain ⟨y, x₁, hy, hx₁, hyx₁, hrel₁, hc₁, hr₁⟩ :=
      ih hx hx (Database.SameMeaning.refl x) hd hc hp
    exact ih₂ (hr.trans hr₁) hx₁ ((hstable x y hx hm hy).trans hyx₁) hrel₁ hc₁ rfl

/-! ### The simulation -/

/-- Every finite source execution has a compiled execution related up to meaning. The
rules are ordering-free: a pass after the source has settled refires them at a partner
state, which shares the meaning but not necessarily the representatives. -/
theorem sim_fwd (hP : P.Fragment) (hO : P.schedule.OrderingFree) :
    ∀ (S : Schedule), S.rules ⊆ P.rules → Fwd P S
  | .run R, hS => by
      rename_i src d x e
      intro hsrc hx hm hd hc hr
      cases hr
      obtain ⟨d', hd', hrel', hc'⟩ := sim_run hP (fun r hr => hS hr) hx hd hc
      exact ⟨d', RunRules R x, hd', hx.runRules hP (fun r hr => hS hr),
        round_sameMeaning hP hO hsrc hx hm (fun r hr => hS hr), hrel', hc',
        Rounds.single (fun r hr => hS hr)⟩
  | .seq S₁ S₂, hS => by
      rename_i src d x e
      intro hsrc hx hm hd hc hr
      have hS₁ : S₁.rules ⊆ P.rules := fun r hr => hS (List.mem_append_left _ hr)
      have hS₂ : S₂.rules ⊆ P.rules := fun r hr => hS (List.mem_append_right _ hr)
      obtain ⟨mid, h₁, h₂⟩ := Reach.seq_inv hr
      obtain ⟨d₁, x₁, hd₁, hx₁, hm₁, hrel₁, hc₁, hr₁⟩ :=
        sim_fwd hP hO S₁ hS₁ hsrc hx hm hd hc h₁
      obtain ⟨d₂, x₂, hd₂, hx₂, hm₂, hrel₂, hc₂, hr₂⟩ :=
        sim_fwd hP hO S₂ hS₂ (hsrc.reach hP hS₁ h₁) hx₁ hm₁ hrel₁ hc₁ h₂
      exact ⟨d₂, x₂, .seq hd₁ hd₂, hx₂, hm₂, hrel₂, hc₂, hr₁.trans hr₂⟩
  | .saturate S, hS => by
      have hS' : S.rules ⊆ P.rules := hS
      have ihS : Fwd P S := sim_fwd hP hO S hS'
      rename_i src d x e
      intro hsrc hx hm hd hc hr
      generalize hT : Schedule.saturate S = T at hr
      induction hr generalizing d x with
      | run => cases hT
      | seq => cases hT
      | @fixpoint src e _ hp heq _ =>
        cases hT
        obtain ⟨d₁, x₁, hd₁, hx₁, hm₁, hrel₁, hc₁, hr₁⟩ := ihS hsrc hx hm hd hc hp
        have he : SrcInv P e := hsrc.reach hP hS' hp
        have hstable : ∀ x y, SrcInv P x → e.SameMeaning x → Reach x S y → e.SameMeaning y := by
          intro x y hx' hex hxy
          obtain ⟨y', hy', hey'⟩ := reach_transport hP hO hS' hsrc hx' (heq.trans hex) hp
          rw [hy'.det hxy] at hey'
          exact hey'
        have hpass : ∀ x, SrcInv P x → e.SameMeaning x → ∃ y, Reach x S y := by
          intro x hx' hex
          obtain ⟨y', hy', _⟩ := reach_transport hP hO hS' hsrc hx' (heq.trans hex) hp
          exact ⟨y', hy'⟩
        by_cases hsame : d.SameMeaning d₁
        · exact ⟨d₁, x₁, .fixpoint hd₁ hsame, hx₁, hm₁, hrel₁, hc₁, hr₁⟩
        · obtain ⟨d', x', hd', hx', hm', hrel', hc', hr'⟩ :=
            extra_passes hP hO ihS hstable hpass hx₁ hm₁ d₁ x₁ (Rounds.refl x₁) hm₁ hrel₁ hc₁
          exact ⟨d', x', .again hd₁ hsame hd', hx', hm', hrel', hc', hr₁.trans hr'⟩
      | @again src e₁ e _ hp hn _ _ ih₂ =>
        cases hT
        obtain ⟨d₁, x₁, hd₁, hx₁, hm₁, hrel₁, hc₁, hr₁⟩ := ihS hsrc hx hm hd hc hp
        have hne : ¬ d.SameMeaning d₁ := not_sameMeaning_of_source hx hx₁ hm hm₁ hd hrel₁ hn
        obtain ⟨d', x', hd', hx', hm', hrel', hc', hr'⟩ :=
          ih₂ (hsrc.reach hP hS' hp) hx₁ hm₁ hrel₁ hc₁ rfl
        exact ⟨d', x', .again hd₁ hne hd', hx', hm', hrel', hc', hr₁.trans hr'⟩

/-- Every finite compiled execution has a source execution related up to meaning. -/
theorem sim_bwd (hP : P.Fragment) (hO : P.schedule.OrderingFree) :
    ∀ (S : Schedule), S.rules ⊆ P.rules → Bwd P S
  | .run R, hS => by
      rename_i src d x d'
      intro hsrc hx hm hd hc hr
      obtain ⟨hrel', hc'⟩ := sim_run_bwd hP (fun r hr => hS hr) hx hd hc hr
      exact ⟨RunRules R src, RunRules R x, .run, hx.runRules hP (fun r hr => hS hr),
        round_sameMeaning hP hO hsrc hx hm (fun r hr => hS hr), hrel', hc',
        Rounds.single (fun r hr => hS hr)⟩
  | .seq S₁ S₂, hS => by
      rename_i src d x d'
      intro hsrc hx hm hd hc hr
      have hS₁ : S₁.rules ⊆ P.rules := fun r hr => hS (List.mem_append_left _ hr)
      have hS₂ : S₂.rules ⊆ P.rules := fun r hr => hS (List.mem_append_right _ hr)
      obtain ⟨mid, h₁, h₂⟩ := Reach.seq_inv hr
      obtain ⟨e₁, x₁, he₁, hx₁, hm₁, hrel₁, hc₁, hr₁⟩ :=
        sim_bwd hP hO S₁ hS₁ hsrc hx hm hd hc h₁
      obtain ⟨e₂, x₂, he₂, hx₂, hm₂, hrel₂, hc₂, hr₂⟩ :=
        sim_bwd hP hO S₂ hS₂ (hsrc.reach hP hS₁ he₁) hx₁ hm₁ hrel₁ hc₁ h₂
      exact ⟨e₂, x₂, .seq he₁ he₂, hx₂, hm₂, hrel₂, hc₂, hr₁.trans hr₂⟩
  | .saturate S, hS => by
      have hS' : S.rules ⊆ P.rules := hS
      have ihS : Bwd P S := sim_bwd hP hO S hS'
      rename_i src d x d'
      intro hsrc hx hm hd hc hr
      change Reach d (.saturate (encS P S)) d' at hr
      generalize hT : Schedule.saturate (encS P S) = T at hr
      induction hr generalizing src x with
      | run => cases hT
      | seq => cases hT
      | @fixpoint d d₁ _ hp heq _ =>
        cases hT
        obtain ⟨e₁, x₁, he₁, hx₁, hm₁, hrel₁, hc₁, hr₁⟩ := ihS hsrc hx hm hd hc hp
        have hsame : src.SameMeaning e₁ :=
          hm.trans ((partners_sameMeaning hx hx₁ hd hrel₁ heq).trans hm₁.symm)
        exact ⟨e₁, x₁, .fixpoint he₁ hsame, hx₁, hm₁, hrel₁, hc₁, hr₁⟩
      | @again d d₁ d' _ hp hn _ _ ih₂ =>
        cases hT
        obtain ⟨e₁, x₁, he₁, hx₁, hm₁, hrel₁, hc₁, hr₁⟩ := ihS hsrc hx hm hd hc hp
        have he₁' : SrcInv P e₁ := hsrc.reach hP hS' he₁
        by_cases hsame : src.SameMeaning e₁
        · -- The source has settled; the compiled passes continue at its meaning.
          have hstable : ∀ x y, SrcInv P x → e₁.SameMeaning x → Reach x S y →
              e₁.SameMeaning y := by
            intro x y hx' hex hxy
            obtain ⟨y', hy', hey'⟩ :=
              reach_transport hP hO hS' hsrc hx' (hsame.trans hex) he₁
            rw [hy'.det hxy] at hey'
            exact hey'
          obtain ⟨x', hx', hm', hrel', hc', hr'⟩ := extra_passes_bwd ihS hstable
            (x₀ := x₁) (Rounds.refl x₁) hx₁ hm₁ hrel₁ hc₁ (by assumption)
          exact ⟨e₁, x', .fixpoint he₁ hsame, hx', hm', hrel', hc', hr₁.trans hr'⟩
        · obtain ⟨e, x', he, hx', hm', hrel', hc', hr'⟩ := ih₂ he₁' hx₁ hm₁ hrel₁ hc₁ rfl
          exact ⟨e, x', .again he₁ hsame he, hx', hm', hrel', hc', hr₁.trans hr'⟩

end Egglog.Congruence
