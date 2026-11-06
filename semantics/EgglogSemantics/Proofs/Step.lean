import EgglogSemantics.Proofs.Writes

namespace Egglog

/-- Individual writes cannot equate a literal with another term. -/
theorem Action.write_litsIsolated {σ : Env} {a : Action} {W : Set (Term × Term)}
    (h : a.write σ = some W) : ∀ p ∈ W, p.1.isLit ∨ p.2.isLit → p.1 = p.2 := by
  cases a with
  | expr e =>
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp h
    rintro p rfl _
    rfl
  | union e₁ e₂ =>
    obtain ⟨t₁, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨t₂, _, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp at h
    · next hn =>
      cases Option.some.inj h
      rintro p rfl hp
      exact (hn (by simpa using hp)).elim
  | subsume e =>
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp h
    simp

theorem Action.writes_litsIsolated {σ : Env} {as : List Action} {W : Set (Term × Term)}
    (h : Action.writes σ as = some W) :
    ∀ p ∈ W, p.1.isLit ∨ p.2.isLit → p.1 = p.2 := by
  induction as generalizing W with
  | nil => cases Option.some.inj h; simp
  | cons a as ih =>
    obtain ⟨V, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨U, hu, rfl⟩ := Option.map_eq_some_iff.mp h
    intro p hp hl
    exact hp.elim (fun hp => Action.write_litsIsolated ha p hp hl)
      (fun hp => ih hu p hp hl)

theorem RuleResults.wf {db d : Database} (hw : db.WF) {r : Rule}
    (h : d ∈ RuleResults db r) : d.WF := by
  obtain ⟨σ, _, hstep⟩ := h
  exact evalActions_wf hw hstep


theorem RunRules.wf {R : List Rule} {db : Database} (hw : db.WF) : (RunRules R db).WF := by
  rw [RunRules.eq_sUnion]
  exact hw.sUnion (fun _ ⟨_, _, hd⟩ => RuleResults.wf hw hd)


theorem runRules_eq_self_iff (R : List Rule) (db : Database) (hdf : ∀ r ∈ R, r.SubsumeFree) :
    RunRules R db = db ↔
      ∀ r ∈ R, ∀ d ∈ RuleResults db r,
        Database.Contained d db := by
  rw [RunRules.eq_sUnion _ _]
  constructor
  · intro h r hr d hd
    rw [← h]
    exact Database.Contained.mem_sUnion ⟨r, hr, hd⟩
  · intro h
    apply Database.ext
    · refine Set.Subset.antisymm ?_ Set.subset_union_left
      rintro p (hp | hp)
      · exact hp
      · obtain ⟨d, ⟨r, hr, hd⟩, hp⟩ := Set.mem_iUnion₂.mp hp
        exact (h r hr d hd).eqs hp
    · refine Set.Subset.antisymm ?_ Set.subset_union_left
      rintro t (ht | ht)
      · exact ht
      · obtain ⟨d, ⟨r, hr, hd⟩, ht⟩ := Set.mem_iUnion₂.mp ht
        exact (h r hr d hd).subsumed ht

/-- Every finite nested schedule preserves well-formedness. -/
theorem Reach.wf {S : Schedule} {db d : Database}
    (h : Reach db S d) (hw : db.WF) : d.WF := by
  induction h with
  | run => exact RunRules.wf hw
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hw)
  | fixpoint _ _ ih => exact ih hw
  | again _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hw)

/-- Subsume-free schedules preserve the entire subsumed set. -/
theorem Reach.subsumed_eq {S : Schedule} {db d : Database}
    (h : Reach db S d) (hdf : ∀ r ∈ S.rules, r.SubsumeFree) :
    d.subsumed = db.subsumed := by
  induction h with
  | run => exact RunRules.subsumed_eq hdf
  | seq _ _ ih₁ ih₂ =>
      exact (ih₂ (fun r hr => hdf r (List.mem_append_right _ hr))).trans
        (ih₁ (fun r hr => hdf r (List.mem_append_left _ hr)))
  | fixpoint _ _ ih => exact ih hdf
  | again _ _ _ ih₁ ih₂ => exact (ih₂ hdf).trans (ih₁ hdf)

/-- A finite saturation is a sequence of passes of its body. -/
theorem Reach.saturate_reach {S : Schedule} {db d : Database}
    (h : Reach db (.saturate S) d) :
    Relation.ReflTransGen (fun a b => Reach a S b) db d := by
  generalize hs : Schedule.saturate S = T at h
  induction h with
  | run => cases hs
  | seq => cases hs
  | fixpoint hp _ _ => cases hs; exact .single hp
  | again hp _ _ _ ih => cases hs; exact (ih rfl).head hp

/-- A schedule has at most one finite result, even with nested saturation and deletion. -/
theorem Reach.det {S : Schedule} {db d₁ d₂ : Database}
    (h₁ : Reach db S d₁) (h₂ : Reach db S d₂) : d₁ = d₂ := by
  induction h₁ generalizing d₂ with
  | run => cases h₂; rfl
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₁ h₂ => obtain rfl := ih₁ h₁; exact ih₂ h₂
  | fixpoint _ he ih =>
    cases h₂ with
    | fixpoint h₂ _ => exact ih h₂
    | again h₂ hn _ => exact (hn (ih h₂ ▸ he)).elim
  | again _ hn _ ih₁ ih₂ =>
    cases h₂ with
    | fixpoint h₂ he => exact (hn ((ih₁ h₂).symm ▸ he)).elim
    | again h₂ _ ht => obtain rfl := ih₁ h₂; exact ih₂ ht

/-- Saturation determinism, with an arbitrary nested body. -/
theorem saturateReach_det {S : Schedule} {db d₁ d₂ : Database}
    (h₁ : Reach db (.saturate S) d₁) (h₂ : Reach db (.saturate S) d₂) : d₁ = d₂ :=
  h₁.det h₂

/-- Invert saturation into its first body pass and the stopping or repeating case. -/
theorem cmdStep_saturate_iff {S : Schedule} {db db' : Database} :
    Reach db (.saturate S) db' ↔ ∃ d, Reach db S d ∧
      ((db.SameMeaning d ∧ db' = d) ∨ (¬ db.SameMeaning d ∧ Reach d (.saturate S) db')) := by
  constructor
  · intro h
    cases h with
    | fixpoint hp he => exact ⟨_, hp, Or.inl ⟨he, rfl⟩⟩
    | again hp hn ht => exact ⟨_, hp, Or.inr ⟨hn, ht⟩⟩
  · rintro ⟨d, hp, (⟨he, rfl⟩ | ⟨hn, ht⟩)⟩
    · exact .fixpoint hp he
    · exact .again hp hn ht

/-- Invert a sequence at its schedule boundary. -/
theorem Reach.seq_inv {db d' : Database} {S₁ S₂ : Schedule}
    (h : Reach db (.seq S₁ S₂) d') : ∃ d, Reach db S₁ d ∧ Reach d S₂ d' := by
  cases h with | seq h₁ h₂ => exact ⟨_, h₁, h₂⟩

/-- The schedule-level form of command-list append. -/
theorem Reach.append {db d d' : Database} {S₁ S₂ : Schedule}
    (h₁ : Reach db S₁ d) (h₂ : Reach d S₂ d') : Reach db (.seq S₁ S₂) d' :=
  .seq h₁ h₂

theorem CongList.of_eqs_eq {d₁ d₂ : Database} (h : d₁.eqs = d₂.eqs) {as bs : List Term}
    (hc : CongList d₁ as bs) : CongList d₂ as bs := (CongList.iff_of_congr (fun _ _ => Cong.iff_of_eqs_eq h)).mp hc

@[inherit_doc CongList.of_eqs_eq]
theorem Database.mem_terms_of_eqs_eq {d₁ d₂ : Database} (h : d₁.eqs = d₂.eqs) {t : Term}
    (ht : t ∈ d₁.terms) : t ∈ d₂.terms := Database.terms_eq_of_eqs_eq h ▸ ht





def Term.Mentions (f : FnName) (t : Term) : Prop := ∃ args, Term.app f args ∈ t.subterms

theorem Term.mentions_head (f : FnName) (args : List Term) : Term.Mentions f (.app f args) :=
  ⟨args, Term.self_mem_subterms _⟩

theorem Term.not_mentions_lit {f : FnName} {l : Lit} : ¬ Term.Mentions f (.lit l) := by
  rintro ⟨args, h⟩; simp at h

theorem Term.mentions_of_subterm {f : FnName} {s t : Term} (h : s ∈ t.subterms)
    (hm : Term.Mentions f s) : Term.Mentions f t := hm.imp fun _ hs => hs.trans h

/-- An application mentions `f` by heading it or through an argument. -/
theorem Term.mentions_app {f g : FnName} {args : List Term}
    (h : Term.Mentions f (.app g args)) : g = f ∨ ∃ a ∈ args, Term.Mentions f a := by
  obtain ⟨cs, hs⟩ := h
  cases hs with
  | refl => exact Or.inl rfl
  | arg hmem hsub => exact Or.inr ⟨_, hmem, cs, hsub⟩

theorem Term.not_mentions_args {f g : FnName} {args : List Term}
    (h : ¬ Term.Mentions f (.app g args)) : ∀ t ∈ args, ¬ Term.Mentions f t :=
  fun t ht hm => h (Term.mentions_of_subterm (Term.arg_subterms ht t.self_mem_subterms) hm)

/-- No held term applies the chosen name. -/
structure Database.Avoids (db : Database) (f : FnName) : Prop where
  terms : ∀ t ∈ db.terms, ¬ Term.Mentions f t

theorem Database.Avoids.congr {f : FnName} {d₁ d₂ : Database} (heq : d₂.eqs = d₁.eqs)
    (h : d₁.Avoids f) : d₂.Avoids f :=
  ⟨fun t ht => h.terms t (Database.mem_terms_of_eqs_eq heq ht)⟩

theorem avoids_addTerm {f : FnName} {db : Database} {t : Term}
    (hav : ∀ s ∈ db.terms, ¬ Term.Mentions f s) (ht : ¬ Term.Mentions f t) :
    ∀ s ∈ (db.addTerm t).terms, ¬ Term.Mentions f s := by
  simp only [Database.addTerm_terms, Set.mem_union]
  rintro s (hs | hs)
  · exact hav s hs
  · exact fun hm => ht (Term.mentions_of_subterm hs hm)

theorem avoids_addEq {f : FnName} {db : Database} {a b : Term}
    (hav : ∀ s ∈ db.terms, ¬ Term.Mentions f s) (ha : ¬ Term.Mentions f a)
    (hb : ¬ Term.Mentions f b) : ∀ s ∈ (db.addEq a b).terms, ¬ Term.Mentions f s := by
  simp only [Database.addEq_terms, Set.mem_union]
  rintro s ((hs | hs) | hs)
  · exact hav s hs
  · exact fun hm => ha (Term.mentions_of_subterm hs hm)
  · exact fun hm => hb (Term.mentions_of_subterm hs hm)

/-- Adding terms that avoid a name preserves that invariant. -/
theorem avoids_addTerms {f : FnName} {db : Database} {ts : List Term}
    (hav : ∀ s ∈ db.terms, ¬ Term.Mentions f s)
    (ht : ∀ t ∈ ts, ¬ Term.Mentions f t) :
    ∀ s ∈ (db.addTerms ts).terms, ¬ Term.Mentions f s := by
  intro s hs
  rw [Database.addTerms_terms] at hs
  rcases hs with hs | ⟨t, hm, hs⟩
  · exact hav s hs
  · exact fun hmen => ht t hm (Term.mentions_of_subterm hs hmen)

end Egglog
