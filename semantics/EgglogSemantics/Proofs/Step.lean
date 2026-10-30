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
  | delete e =>
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
  constructor
  intro p hp hl
  rcases hp with hp | hp
  · exact (hw.deleteRows _).litsIsolated p hp hl
  · obtain ⟨W, ⟨r, _, σ, _, hW⟩, hp⟩ := hp
    exact Action.writes_litsIsolated hW p hp hl


theorem runRules_eq_self_iff (R : List Rule) (db : Database) (hdf : ∀ r ∈ R, r.DeleteFree) :
    RunRules R db = db ↔
      ∀ r ∈ R, ∀ d ∈ RuleResults db r,
        Database.Contained d db := by
  rw [RunRules.eq_sUnion _ _ hdf]
  constructor
  · intro h r hr d hd
    have hmem : d ∈ {d | ∃ r ∈ R, d ∈ RuleResults db r} :=
      ⟨r, hr, hd⟩
    have he : d.eqs ⊆
        (db.sUnion {d | ∃ r ∈ R, d ∈ RuleResults db r}).eqs := fun _ hp =>
      Or.inr (Set.mem_biUnion hmem hp)
    rw [h] at he
    exact ⟨he⟩
  · intro h
    refine Database.ext ?_
    refine Set.Subset.antisymm ?_ Set.subset_union_left
    rintro p (hp | hp)
    · exact hp
    · obtain ⟨d, ⟨r, hr, hd⟩, hp⟩ := Set.mem_iUnion₂.mp hp
      exact (h r hr d hd).eqs hp



theorem SaturateReach.wf {R : List Rule} {db d : Database}
    (h : SaturateReach R db d) (hw : db.WF) : d.WF := by
  induction h with
  | fixpoint => exact RunRules.wf hw
  | again _ _ ih => exact ih (RunRules.wf hw)


theorem SaturateReach.reach {R : List Rule} {db d : Database}
    (h : SaturateReach R db d) :
    Relation.ReflTransGen (fun a b => b = RunRules R a) db d := by
  induction h with
  | fixpoint => exact .single rfl
  | again _ _ ih => exact ih.head rfl

theorem saturateReach_det {R : List Rule} {db d₁ d₂ : Database}
    (h₁ : SaturateReach R db d₁) (h₂ : SaturateReach R db d₂) : d₁ = d₂ := by
  induction h₁ with
  | fixpoint he =>
    cases h₂ with
    | fixpoint => rfl
    | again hn _ => exact (hn he).elim
  | again hn _ ih =>
    cases h₂ with
    | fixpoint he => exact (hn he).elim
    | again _ ht => exact ih ht

theorem cmdStep_saturate_iff {R : List Rule} {db db' : Database} :
    CmdStep db (.saturate R) db' ↔ SaturateReach R db db' := Iff.rfl

theorem CmdStep.wf {db d : Database} {c : Cmd} (h : CmdStep db c d) (hw : db.WF) : d.WF := by
  cases c with
  | run R => subst d; exact RunRules.wf hw
  | saturate R => exact SaturateReach.wf h hw


theorem CongList.of_eqs_eq {d₁ d₂ : Database} (h : d₁.eqs = d₂.eqs) {as bs : List Term}
    (hc : CongList d₁ as bs) : CongList d₂ as bs := CongList.mono ⟨h.subset⟩ hc

@[inherit_doc CongList.of_eqs_eq]
theorem Database.mem_terms_of_eqs_eq {d₁ d₂ : Database} (h : d₁.eqs = d₂.eqs) {t : Term}
    (ht : t ∈ d₁.terms) : t ∈ d₂.terms := Database.Contained.terms ⟨h.subset⟩ ht





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

theorem ProgramStep.cons_inv {db d' : Database} {c : Cmd} {cs : List Cmd}
    (h : ProgramStep db (c :: cs) d') : ∃ d, CmdStep db c d ∧ ProgramStep d cs d' := by
  cases h with | cons hc hrest => exact ⟨_, hc, hrest⟩

theorem ProgramStep.nil_inv {db d' : Database} (h : ProgramStep db [] d') : db = d' := by
  cases h with | nil => rfl

/-- Running `p` then `q` is running `p ++ q`. What lets a concrete program be built a
prefix at a time. -/
theorem ProgramStep.append {db d d' : Database} {p q : List Cmd} (h₁ : ProgramStep db p d) :
    ProgramStep d q d' → ProgramStep db (p ++ q) d' := by
  induction h₁ with
  | nil => exact id
  | cons hc _ ih => exact fun h₂ => .cons hc (ih h₂)


theorem ProgramStep.wf {db d : Database} {p : List Cmd} (h : ProgramStep db p d)
    (hw : db.WF) : d.WF := by
  induction h with
  | nil => exact hw
  | cons hc _ ih => exact ih (hc.wf hw)


theorem CmdStep.det {db d₁ d₂ : Database} {c : Cmd}
    (h₁ : CmdStep db c d₁) (h₂ : CmdStep db c d₂) : d₁ = d₂ := by
  cases c with
  | run R => exact h₁.trans h₂.symm
  | saturate R => exact saturateReach_det h₁ h₂

theorem ProgramStep.det {db d₁ d₂ : Database} {p : List Cmd}
    (h₁ : ProgramStep db p d₁) (h₂ : ProgramStep db p d₂) : d₁ = d₂ := by
  induction h₁ with
  | nil => exact h₂.nil_inv
  | cons hc _ ih =>
    obtain ⟨mid, hc', ht⟩ := h₂.cons_inv
    obtain rfl := hc.det hc'
    exact ih ht

end Egglog
