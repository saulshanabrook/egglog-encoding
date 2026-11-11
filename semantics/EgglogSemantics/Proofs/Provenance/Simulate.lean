import EgglogSemantics.Proofs.Provenance.Round
import Mathlib.Data.Set.Card

/-! Finite execution correspondence for provenance instrumentation, up to the original
state's meaning. Additional instrumented passes after the original settles terminate and
write only log rows. -/

namespace Egglog.Provenance

/-! ### The instrumented schedule -/

/-- `S'` instruments `S`: every run's rules are the instrumented rules of the original
run, under some indices. -/
inductive Instr : Schedule → Schedule → Prop where
  | run {R R' : List Rule} : InstrRules R R' → Instr (.run R) (.run R')
  | saturate {S S' : Schedule} : Instr S S' → Instr (.saturate S) (.saturate S')
  | seq {S₁ S₂ S₁' S₂' : Schedule} : Instr S₁ S₁' → Instr S₂ S₂' →
      Instr (.seq S₁ S₂) (.seq S₁' S₂')

theorem instrRules_zipIdx (R : List Rule) (k : Nat) :
    InstrRules R (R.zipIdx.map fun ri => encodeRule (k + ri.2) ri.1) where
  orig := by
    intro r' hr'
    obtain ⟨ri, hri, rfl⟩ := List.mem_map.mp hr'
    have hmem : ri.1 ∈ R := by
      have := List.mem_map_of_mem (f := Prod.fst) hri
      rwa [List.zipIdx_map_fst] at this
    exact ⟨ri.1, hmem, k + ri.2, rfl⟩
  inst := by
    intro r hr
    have hr' : r ∈ R.zipIdx.map Prod.fst := by rw [List.zipIdx_map_fst]; exact hr
    obtain ⟨ri, hri, hfst⟩ := List.mem_map.mp hr'
    exact ⟨k + ri.2, List.mem_map.mpr ⟨ri, hri, by rw [hfst]⟩⟩

/-- The pass instruments every schedule. -/
theorem encodeSchedule_instr : ∀ (S : Schedule) (k : Nat), Instr S (encodeSchedule S k).1
  | .run R, k => .run (instrRules_zipIdx R k)
  | .saturate S, k => by
      rcases h : encodeSchedule S k with ⟨S', n⟩
      have ih := encodeSchedule_instr S k
      rw [h] at ih
      simp only [encodeSchedule, h]
      exact .saturate ih
  | .seq S₁ S₂, k => by
      rcases h₁ : encodeSchedule S₁ k with ⟨T₁, n⟩
      rcases h₂ : encodeSchedule S₂ n with ⟨T₂, m⟩
      have ih₁ := encodeSchedule_instr S₁ k
      have ih₂ := encodeSchedule_instr S₂ n
      rw [h₁] at ih₁
      rw [h₂] at ih₂
      simp only [encodeSchedule, h₁, h₂]
      exact .seq ih₁ ih₂

theorem encode_some {P P' : Program} (h : encode P = some P') :
    programOk P = true ∧ P'.schedule = (encodeSchedule P.schedule 0).1 ∧ P'.check = P.check := by
  unfold encode at h
  split at h
  · cases h; exact ⟨by assumption, rfl, rfl⟩
  · cases h

/-! ### The relation up to meaning -/

/-- The partner of an original state: same meaning, related to the instrumented state. -/
def RelC (P : Program) (d d' : Database) : Prop := ∃ x, d.SameMeaning x ∧ Rel P x d'

namespace RelC

variable {P : Program} {d e d' e' : Database}

theorem of_rel (h : Rel P d d') : RelC P d d' := ⟨d, .refl d, h⟩

theorem trans_sameMeaning (h : RelC P d d') (hm : d.SameMeaning e) : RelC P e d' :=
  let ⟨x, hx, hr⟩ := h
  ⟨x, hm.symm.trans hx, hr⟩

theorem good' (h : RelC P d d') : Good d' := h.choose_spec.2.good'

theorem sameMeaning_of_inst (hP : programOk P = true) (h₁ : RelC P d d') (h₂ : RelC P e e')
    (h : d'.SameMeaning e') : d.SameMeaning e := by
  obtain ⟨x, hx, hrx⟩ := h₁
  obtain ⟨y, hy, hry⟩ := h₂
  exact hx.trans ((Rel.sameMeaning_of_inst hP hrx hry h).trans hy.symm)

theorem not_sameMeaning (hP : programOk P = true) (h₁ : RelC P d d') (h₂ : RelC P e e')
    (hn : ¬ d.SameMeaning e) : ¬ d'.SameMeaning e' :=
  fun h => hn (h₁.sameMeaning_of_inst hP h₂ h)

theorem terms_eq (hP : programOk P = true) (hd : Inv P d) (h : RelC P d d') :
    d.terms = {t ∈ d'.terms | ¬ IsLog t} := by
  obtain ⟨x, hx, hr⟩ := h
  rw [hd.good.terms_eq_of_sameMeaning hr.inv.good hx]
  exact hr.terms_eq hP

theorem terms_sub (hP : programOk P = true) (hd : Inv P d) (h : RelC P d d') :
    d.terms ⊆ d'.terms := by
  rw [h.terms_eq hP hd]; exact fun _ ht => ht.1

theorem mem_terms_of_not_log (hP : programOk P = true) (hd : Inv P d) (h : RelC P d d')
    {t : Term} (ht : t ∈ d'.terms) (hl : ¬ IsLog t) : t ∈ d.terms := by
  rw [h.terms_eq hP hd]; exact ⟨ht, hl⟩

theorem subsumed_eq (hd : Inv P d) (h : RelC P d d') : d'.subsumed = d.subsumed := by
  obtain ⟨x, hx, hr⟩ := h
  rw [hr.subsumed]
  exact (hd.good.subsumed_eq_of_sameMeaning hr.inv.good hx).symm

theorem log_mem_eqs (hP : programOk P = true) (h : RelC P d d') {t : Term} (hl : IsLog t)
    (ht : t ∈ d'.terms) : (t, t) ∈ d'.eqs :=
  h.choose_spec.2.log_mem_eqs hP hl ht

theorem queryMatches_iff (hP : programOk P = true) (hd : Inv P d) (h : RelC P d d') {q : Query}
    (hk : Query.VarsKeyed q) (hq : LogFreeQuery q) {σ : Env} :
    QueryMatches d' q σ ↔ QueryMatches d q σ := by
  obtain ⟨x, hx, hr⟩ := h
  rw [Provenance.queryMatches_iff (hr.shadow hP) hk hq]
  have ht := hd.good.terms_eq_of_sameMeaning hr.inv.good hx
  exact ⟨fun hm => QueryMatches.sameMeaning hx.symm ht.symm hm,
    fun hm => QueryMatches.sameMeaning hx ht hm⟩

end RelC

/-! ### The log rows a pass can write -/

/-- A row some rule of `S'` writes under a substitution over `T`. -/
def Writable (T : Set Term) (S' : Schedule) (t : Term) : Prop :=
  ∃ r' ∈ S'.rules, ∃ σ : Env, (∀ b ∈ σ, b.2 ∈ T) ∧ (Env.dom σ).Perm r'.query.vars ∧
    ∃ a ∈ r'.actions, ∃ W, a.write σ = some W ∧ (t, t) ∈ W

theorem Writable.mono {T T' : Set Term} {S' S'' : Schedule} (hT : T ⊆ T')
    (hS : S'.rules ⊆ S''.rules) {t : Term} (h : Writable T S' t) : Writable T' S'' t :=
  let ⟨r', hr', σ, hσ, hperm, a, ha, W, hW, ht⟩ := h
  ⟨r', hS hr', σ, fun b hb => hT (hσ b hb), hperm, a, ha, W, hW, ht⟩

/-- The log rows of `e'` beyond `d'` are writable over `T`. -/
def LogBound (T : Set Term) (S' : Schedule) (d' e' : Database) : Prop :=
  ∀ t, IsLog t → (t, t) ∈ e'.eqs → (t, t) ∈ d'.eqs ∨ Writable T S' t

theorem LogBound.mono {T T' : Set Term} {S' S'' : Schedule} {d' e' : Database} (hT : T ⊆ T')
    (hS : S'.rules ⊆ S''.rules) (h : LogBound T S' d' e') : LogBound T' S'' d' e' :=
  fun t hl ht => (h t hl ht).imp_right (Writable.mono hT hS)

theorem LogBound.trans {T : Set Term} {S' : Schedule} {d' m' e' : Database}
    (h₁ : LogBound T S' d' m') (h₂ : LogBound T S' m' e') : LogBound T S' d' e' :=
  fun t hl ht => (h₂ t hl ht).elim (fun hm => h₁ t hl hm) Or.inr

theorem write_rows_finite (σ : Env) (a : Action) :
    {t | ∃ W, a.write σ = some W ∧ (t, t) ∈ W}.Finite := by
  cases hw : a.write σ with
  | none =>
    apply Set.finite_empty.subset
    rintro t ⟨W, hW, _⟩
    cases hW
  | some W =>
    apply ((Action.write_finite hw).image Prod.fst).subset
    rintro t ⟨W', hW', ht⟩
    cases Option.some.inj hW'
    exact ⟨(t, t), ht, rfl⟩

/-- Over a finite set of terms, finitely many rows are writable. -/
theorem writable_finite {T : Set Term} (hT : T.Finite) (S' : Schedule) :
    {t | Writable T S' t}.Finite := by
  have hσ : ∀ r' : Rule,
      {σ : Env | (∀ b ∈ σ, b.2 ∈ T) ∧ (Env.dom σ).Perm r'.query.vars}.Finite := by
    intro r'
    apply (finite_lists ((List.finite_toSet r'.query.vars).prod hT) r'.query.vars.length).subset
    rintro σ ⟨hT', hperm⟩
    refine ⟨by simpa [Env.dom] using hperm.length_eq, fun b hb => ?_⟩
    exact ⟨hperm.subset (List.mem_map.mpr ⟨b, hb, rfl⟩), hT' b hb⟩
  apply ((List.finite_toSet S'.rules).biUnion fun r' _ => (hσ r').biUnion fun σ _ =>
    (List.finite_toSet r'.actions).biUnion fun a _ => write_rows_finite σ a).subset
  rintro t ⟨r', hr', σ, hT', hperm, a, ha, W, hW, ht⟩
  exact Set.mem_iUnion₂.mpr ⟨r', hr', Set.mem_iUnion₂.mpr ⟨σ, ⟨hT', hperm⟩,
    Set.mem_iUnion₂.mpr ⟨a, ha, W, hW, ht⟩⟩⟩

/-! ### The simulation statements -/

/-- The forward simulation for a schedule: every finite execution of the original has an
instrumented execution related up to meaning, whose new log rows are writable over the
terms the original reaches. -/
def Fwd (P : Program) (S S' : Schedule) : Prop :=
  ∀ {d d' e : Database}, Inv P d → RelC P d d' → Reach d S e →
    ∃ e', Reach d' S' e' ∧ RelC P e e' ∧ LogBound e.terms S' d' e'

/-- The backward simulation for a schedule. -/
def Bwd (P : Program) (S S' : Schedule) : Prop :=
  ∀ {d d' e' : Database}, Inv P d → RelC P d d' → Reach d' S' e' →
    ∃ e, Reach d S e ∧ RelC P e e'

variable {P : Program}

/-! ### One run -/

theorem run_fwd (hP : programOk P = true) {R R' : List Rule} (hR : ∀ r ∈ R, r ∈ P.rules)
    (hK : ∀ r ∈ R, Query.VarsKeyed r.query) (hI : InstrRules R R') {d d' : Database}
    (hd : Inv P d) (hrel : RelC P d d') :
    RelC P (RunRules R d) (RunRules R' d') ∧
      LogBound (RunRules R d).terms (.run R') d' (RunRules R' d') := by
  obtain ⟨x, hx, hrx⟩ := hrel
  refine ⟨⟨RunRules R x, hd.round_sameMeaning hP hrx.inv hx hR, run_rel hP hR hK hI hrx⟩, ?_⟩
  intro t hl ht
  rw [RunRules.eq_pair] at ht
  rcases ht with ht | ht
  · exact Or.inl ht
  · obtain ⟨W, ⟨r', hr', σ, hσ, hW⟩, hp⟩ := ht
    obtain ⟨r, hr, j, rfl⟩ := hI.orig r' hr'
    rw [encodeRule_query] at hσ
    have hσ' : QueryMatches d r.query σ :=
      (RelC.queryMatches_iff hP hd ⟨x, hx, hrx⟩ (hK r hr) (logFreeQuery_of_mem hP (hR r hr))).mp hσ
    obtain ⟨a, ha, V, hV, hp⟩ := Action.mem_writes hW hp
    exact Or.inr ⟨encodeRule j r, hr', σ,
      fun b hb => RunRules.terms_subset R d (hσ'.1.mem_terms b hb), hσ'.1.1, a, ha, V, hV, hp⟩

/-! ### Extra instrumented passes after the original settles -/

/-- After the original settles, instrumented saturation terminates at a related state of
the same original meaning, with new log rows writable over the original terms. -/
theorem extra_passes (hP : programOk P = true) {S S' : Schedule} (hS : S.rules ⊆ P.rules)
    (ih : Fwd P S S') {e : Database} (he : Inv P e)
    (hstable : ∀ x y, Inv P x → e.SameMeaning x → Reach x S y → e.SameMeaning y)
    (hpass : ∀ x, Inv P x → e.SameMeaning x → ∃ y, Reach x S y) :
    ∀ x x', Inv P x → e.SameMeaning x → RelC P x x' →
      ∃ e', Reach x' (.saturate S') e' ∧ RelC P e e' ∧ LogBound e.terms (.saturate S') x' e' := by
  have hU : {t | Writable e.terms S' t}.Finite := writable_finite he.terms_finite S'
  intro x x' hx hex hrel
  induction hn : ({t | Writable e.terms S' t} \ {t | (t, t) ∈ x'.eqs}).ncard
    using Nat.strong_induction_on generalizing x x' with
  | _ n ihn =>
  obtain ⟨y, hy⟩ := hpass x hx hex
  obtain ⟨y', hy', hrel', hlog⟩ := ih hx hrel hy
  have hey : e.SameMeaning y := hstable x y hx hex hy
  have hyinv : Inv P y := hx.reach hP hS hy
  have hyt : y.terms = e.terms := hyinv.good.terms_eq_of_sameMeaning he.good hey.symm
  have hlog' : LogBound e.terms (.saturate S') x' y' := by
    rw [hyt] at hlog
    exact hlog
  have hrele : RelC P e y' := hrel'.trans_sameMeaning hey.symm
  by_cases hsame : x'.SameMeaning y'
  · exact ⟨y', .fixpoint hy' hsame, hrele, hlog'⟩
  · -- A pass that changes the instrumented state adds a log row.
    have hnew : ∃ t, IsLog t ∧ (t, t) ∈ y'.eqs ∧ (t, t) ∉ x'.eqs := by
      by_contra hno
      push Not at hno
      apply hsame
      apply hrel.good'.sameMeaning_of hrel'.good'
      · apply Set.Subset.antisymm
          fun _ ht => Database.mem_terms_of_eqs (Reach.contained' hy').eqs ht
        intro t ht
        by_cases hl : IsLog t
        · exact ⟨(t, t), hno t hl (hrel'.log_mem_eqs hP hl ht), Or.inl (Term.self_mem_subterms t)⟩
        · have hty : t ∈ y.terms := hrel'.mem_terms_of_not_log hP hyinv ht hl
          have htx : t ∈ x.terms := by
            rw [hx.good.terms_eq_of_sameMeaning he.good hex.symm, ← hyt]
            exact hty
          exact hrel.terms_sub hP hx htx
      · rw [hrel.subsumed_eq hx, hrel'.subsumed_eq hyinv,
          hx.good.subsumed_eq_of_sameMeaning he.good hex.symm,
          hyinv.good.subsumed_eq_of_sameMeaning he.good hey.symm]
    obtain ⟨t, hl, hty, htx⟩ := hnew
    have htU : t ∈ {t | Writable e.terms S' t} := by
      rcases hlog t hl hty with h | h
      · exact (htx h).elim
      · rw [hyt] at h
        exact h
    have hlt : ({t | Writable e.terms S' t} \ {t | (t, t) ∈ y'.eqs}).ncard <
        ({t | Writable e.terms S' t} \ {t | (t, t) ∈ x'.eqs}).ncard := by
      apply Set.ncard_lt_ncard _ (hU.subset Set.sdiff_subset)
      refine ⟨fun u hu => ⟨hu.1, fun hux => hu.2 ((Reach.contained' hy').eqs hux)⟩, fun hsub => ?_⟩
      exact (hsub ⟨htU, htx⟩).2 hty
    obtain ⟨e', he', hrel'', hlog''⟩ := ihn _ (hn ▸ hlt) y y' hyinv hey hrel' rfl
    exact ⟨e', .again hy' hsame he', hrel'', hlog'.trans hlog''⟩

/-- The instrumented passes after the original settles stay related to its meaning. -/
theorem extra_passes_bwd (hP : programOk P = true) {S S' : Schedule} (hS : S.rules ⊆ P.rules)
    (ih : Bwd P S S') {e : Database}
    (hstable : ∀ x y, Inv P x → e.SameMeaning x → Reach x S y → e.SameMeaning y) :
    ∀ {x x' e' : Database}, Inv P x → e.SameMeaning x → RelC P x x' →
      Reach x' (.saturate S') e' → RelC P e e' := by
  intro x x' e' hx hex hrel hr
  generalize hT : Schedule.saturate S' = T at hr
  induction hr generalizing x with
  | run => cases hT
  | seq => cases hT
  | fixpoint hp _ _ =>
    cases hT
    obtain ⟨y, hy, hrel'⟩ := ih hx hrel hp
    exact hrel'.trans_sameMeaning (hstable x y hx hex hy).symm
  | again hp _ _ _ ih₂ =>
    cases hT
    obtain ⟨y, hy, hrel'⟩ := ih hx hrel hp
    exact ih₂ (hx.reach hP hS hy) (hstable x y hx hex hy) hrel' rfl

/-- The pass that settles the original gives its stability and the existence of further
passes from any state of its meaning. -/
theorem stable_of_fixpoint (hP : programOk P = true) {S : Schedule} (hS : S.rules ⊆ P.rules)
    {d e : Database} (hd : Inv P d) (hp : Reach d S e) (heq : d.SameMeaning e) :
    (∀ x y, Inv P x → e.SameMeaning x → Reach x S y → e.SameMeaning y) ∧
      (∀ x, Inv P x → e.SameMeaning x → ∃ y, Reach x S y) := by
  constructor
  · intro x y hx hex hxy
    obtain ⟨y', hy', hey'⟩ := hd.reach_transport hP hS hx (heq.trans hex) hp
    rw [hy'.det hxy] at hey'
    exact hey'
  · intro x hx hex
    obtain ⟨y', hy', _⟩ := hd.reach_transport hP hS hx (heq.trans hex) hp
    exact ⟨y', hy'⟩

/-! ### The simulation -/

/-- Every finite execution of the original has an instrumented execution related up to
meaning. -/
theorem sim_fwd (hP : programOk P = true) : ∀ {S S' : Schedule}, Instr S S' →
    S.rules ⊆ P.rules → (∀ r ∈ S.rules, Query.VarsKeyed r.query) → Fwd P S S' := by
  intro S S' hI
  induction hI with
  | @run R R' hI =>
    intro hS hK d d' e hd hrel hr
    cases hr
    obtain ⟨hrel', hlog⟩ := run_fwd hP (fun r hr => hS hr) hK hI hd hrel
    exact ⟨_, .run, hrel', hlog⟩
  | @seq S₁ S₂ S₁' S₂' _ _ ih₁ ih₂ =>
    intro hS hK d d' e hd hrel hr
    have hS₁ : S₁.rules ⊆ P.rules := fun r hr => hS (List.mem_append_left _ hr)
    have hS₂ : S₂.rules ⊆ P.rules := fun r hr => hS (List.mem_append_right _ hr)
    have hK₁ : ∀ r ∈ S₁.rules, Query.VarsKeyed r.query :=
      fun r hr => hK r (List.mem_append_left _ hr)
    have hK₂ : ∀ r ∈ S₂.rules, Query.VarsKeyed r.query :=
      fun r hr => hK r (List.mem_append_right _ hr)
    obtain ⟨m, h₁, h₂⟩ := Reach.seq_inv hr
    obtain ⟨m', hm', hrelm, hlog₁⟩ := ih₁ hS₁ hK₁ hd hrel h₁
    obtain ⟨e', he', hrele, hlog₂⟩ := ih₂ hS₂ hK₂ (hd.reach hP hS₁ h₁) hrelm h₂
    refine ⟨e', .seq hm' he', hrele, ?_⟩
    have hme : m.terms ⊆ e.terms :=
      fun _ ht => Database.mem_terms_of_eqs (Reach.contained' h₂).eqs ht
    exact (hlog₁.mono hme fun _ h => List.mem_append_left _ h).trans
      (hlog₂.mono subset_rfl fun _ h => List.mem_append_right _ h)
  | @saturate S S' _ ih =>
    intro hS hK d d' e hd hrel hr
    have hS' : S.rules ⊆ P.rules := hS
    have hK' : ∀ r ∈ S.rules, Query.VarsKeyed r.query := hK
    have ihS : Fwd P S S' := ih hS' hK'
    generalize hT : Schedule.saturate S = T at hr
    induction hr generalizing d' with
    | run => cases hT
    | seq => cases hT
    | @fixpoint d e _ hp heq _ =>
      cases hT
      obtain ⟨e₁', he₁', hrel₁, hlog₁⟩ := ihS hd hrel hp
      have he : Inv P e := hd.reach hP hS' hp
      obtain ⟨hstable, hpass⟩ := stable_of_fixpoint hP hS' hd hp heq
      by_cases hsame : d'.SameMeaning e₁'
      · exact ⟨e₁', .fixpoint he₁' hsame, hrel₁, hlog₁.mono subset_rfl fun _ h => h⟩
      · obtain ⟨e', he', hrel', hlog'⟩ :=
          extra_passes hP hS' ihS he hstable hpass e e₁' he (Database.SameMeaning.refl e) hrel₁
        exact ⟨e', .again he₁' hsame he', hrel',
          (hlog₁.mono subset_rfl fun _ h => h).trans hlog'⟩
    | @again d e₁ e _ hp hn hrest _ ih₂ =>
      cases hT
      obtain ⟨e₁', he₁', hrel₁, hlog₁⟩ := ihS hd hrel hp
      have hne : ¬ d'.SameMeaning e₁' := hrel.not_sameMeaning hP hrel₁ hn
      obtain ⟨e', he', hrel', hlog'⟩ := ih₂ (hd.reach hP hS' hp) hrel₁ rfl
      refine ⟨e', .again he₁' hne he', hrel', ?_⟩
      have h₁e : e₁.terms ⊆ e.terms :=
        fun _ ht => Database.mem_terms_of_eqs (Reach.contained' hrest).eqs ht
      exact (hlog₁.mono h₁e fun _ h => h).trans hlog'

/-- Every finite instrumented execution has an execution of the original related up to
meaning. -/
theorem sim_bwd (hP : programOk P = true) : ∀ {S S' : Schedule}, Instr S S' →
    S.rules ⊆ P.rules → (∀ r ∈ S.rules, Query.VarsKeyed r.query) → Bwd P S S' := by
  intro S S' hI
  induction hI with
  | @run R R' hI =>
    intro hS hK d d' e' hd hrel hr
    cases hr
    exact ⟨_, .run, (run_fwd hP (fun r hr => hS hr) hK hI hd hrel).1⟩
  | @seq S₁ S₂ S₁' S₂' _ _ ih₁ ih₂ =>
    intro hS hK d d' e' hd hrel hr
    have hS₁ : S₁.rules ⊆ P.rules := fun r hr => hS (List.mem_append_left _ hr)
    have hS₂ : S₂.rules ⊆ P.rules := fun r hr => hS (List.mem_append_right _ hr)
    have hK₁ : ∀ r ∈ S₁.rules, Query.VarsKeyed r.query :=
      fun r hr => hK r (List.mem_append_left _ hr)
    have hK₂ : ∀ r ∈ S₂.rules, Query.VarsKeyed r.query :=
      fun r hr => hK r (List.mem_append_right _ hr)
    obtain ⟨m', h₁, h₂⟩ := Reach.seq_inv hr
    obtain ⟨m, hm, hrelm⟩ := ih₁ hS₁ hK₁ hd hrel h₁
    obtain ⟨e, he, hrele⟩ := ih₂ hS₂ hK₂ (hd.reach hP hS₁ hm) hrelm h₂
    exact ⟨e, .seq hm he, hrele⟩
  | @saturate S S' _ ih =>
    intro hS hK d d' e' hd hrel hr
    have hS' : S.rules ⊆ P.rules := hS
    have hK' : ∀ r ∈ S.rules, Query.VarsKeyed r.query := hK
    have ihS : Bwd P S S' := ih hS' hK'
    generalize hT : Schedule.saturate S' = T at hr
    induction hr generalizing d with
    | run => cases hT
    | seq => cases hT
    | @fixpoint d' e₁' _ hp heq _ =>
      cases hT
      obtain ⟨e₁, he₁, hrel₁⟩ := ihS hd hrel hp
      exact ⟨e₁, .fixpoint he₁ (hrel.sameMeaning_of_inst hP hrel₁ heq), hrel₁⟩
    | @again d' e₁' e' _ hp hn hrest _ ih₂ =>
      cases hT
      obtain ⟨e₁, he₁, hrel₁⟩ := ihS hd hrel hp
      have hinv₁ : Inv P e₁ := hd.reach hP hS' he₁
      by_cases hsame : d.SameMeaning e₁
      · -- The original has settled; the instrumented passes continue at its meaning.
        obtain ⟨hstable, _⟩ := stable_of_fixpoint hP hS' hd he₁ hsame
        exact ⟨e₁, .fixpoint he₁ hsame, extra_passes_bwd hP hS' ihS hstable hinv₁
          (Database.SameMeaning.refl e₁) hrel₁ hrest⟩
      · obtain ⟨e, he, hrel'⟩ := ih₂ hinv₁ hrel₁ rfl
        exact ⟨e, .again he₁ hsame he, hrel'⟩

/-- The forward simulation, for a partner relation. -/
theorem fwd_relC (hP : programOk P = true) {S S' : Schedule} (hI : Instr S S')
    (hS : S.rules ⊆ P.rules) (hK : ∀ r ∈ S.rules, Query.VarsKeyed r.query) {d d' e : Database}
    (hd : Inv P d) (hrel : RelC P d d') (hr : Reach d S e) :
    ∃ e', Reach d' S' e' ∧ RelC P e e' :=
  let ⟨e', he', hrel', _⟩ := sim_fwd hP hI hS hK hd hrel hr
  ⟨e', he', hrel'⟩

/-- The backward simulation, for a partner relation. -/
theorem bwd_relC (hP : programOk P = true) {S S' : Schedule} (hI : Instr S S')
    (hS : S.rules ⊆ P.rules) (hK : ∀ r ∈ S.rules, Query.VarsKeyed r.query) {d d' e' : Database}
    (hd : Inv P d) (hrel : RelC P d d') (hr : Reach d' S' e') :
    ∃ e, Reach d S e ∧ RelC P e e' :=
  sim_bwd hP hI hS hK hd hrel hr

end Egglog.Provenance
