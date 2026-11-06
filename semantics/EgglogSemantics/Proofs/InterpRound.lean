import EgglogSemantics.Proofs.InterpLookup

namespace Egglog

theorem execAction_preserves {P : FDatabase → Prop}
    (ht : ∀ d t, P d → P (d.addTerm t))
    (hu : ∀ d a b, P d → ¬(a.isLit ∨ b.isLit) → P (d.addEq a b))
    (hx : ∀ d t, P d → P (d.subsume t))
    {σ : Env} {d e : FDatabase} {a : Action} (hd : P d)
    (h : execAction σ d a = some e) : P e := by
  rcases execAction_eq_some h with ⟨_, t, _, _, rfl⟩ |
    ⟨_, _, t, u, _, _, _, hl, rfl⟩ | ⟨f, _, ts, _, _, rfl⟩
  · exact ht d t hd
  · exact hu d t u hd hl
  · exact hx d (.app f ts) hd

theorem execActions_preserves {P : FDatabase → Prop}
    (ht : ∀ d t, P d → P (d.addTerm t))
    (hu : ∀ d a b, P d → ¬(a.isLit ∨ b.isLit) → P (d.addEq a b))
    (hx : ∀ d t, P d → P (d.subsume t))
    {σ : Env} {d e : FDatabase} {as : List Action} (hd : P d)
    (h : execActions σ d as = some e) : P e := by
  induction as generalizing d with
  | nil => cases Option.some.inj h; exact hd
  | cons a as ih =>
    obtain ⟨m, hm, he⟩ := Option.bind_eq_some_iff.mp h
    exact ih (execAction_preserves ht hu hx hd hm) he

theorem execAction_closed {σ : Env} {d e : FDatabase} (he : d.Closed)
    {a : Action} (h : execAction σ d a = some e) : e.Closed :=
  execAction_preserves (fun _ t h => h.addTerm t) (fun _ a b h _ => h.addEq a b)
    (fun _ t h => h.subsume t) he h

theorem execActions_closed {σ : Env} {d e : FDatabase} (he : d.Closed)
    {as : List Action} (h : execActions σ d as = some e) : e.Closed :=
  execActions_preserves (fun _ t h => h.addTerm t) (fun _ a b h _ => h.addEq a b)
    (fun _ t h => h.subsume t) he h

theorem execAction_subtermClosed {σ : Env} {d e : FDatabase} (he : d.SubtermClosed)
    {a : Action} (h : execAction σ d a = some e) : e.SubtermClosed :=
  execAction_preserves (fun _ t h => h.addTerm t) (fun _ a b h _ => h.addEq a b)
    (fun _ t h => h.subsume t) he h

theorem execActions_subtermClosed {σ : Env} {d e : FDatabase} (he : d.SubtermClosed)
    {as : List Action} (h : execActions σ d as = some e) : e.SubtermClosed :=
  execActions_preserves (fun _ t h => h.addTerm t) (fun _ a b h _ => h.addEq a b)
    (fun _ t h => h.subsume t) he h

/-- All successful actions implement the same writes and marks. -/
theorem execAction_spec {σ : Env} {d : FDatabase} (he : d.Closed) (a : Action) :
    match a.write σ, a.mark σ, execAction σ d a with
    | none, none, none => True
    | some W, some X, some e => e.Closed ∧
        e.toDatabase.SameMeaning ((d.toDatabase.addEqs W).addSubsumed X) ∧
        e.toDatabase.subsumed = d.toDatabase.subsumed ∪ X
    | _, _, _ => False := by
  cases a with
  | expr ex =>
    cases hv : ex.eval σ with
    | none => simp [Action.write, Action.mark, execAction, hv]
    | some t =>
      simp only [Action.write, Action.mark, execAction, hv, Option.map_some]
      refine ⟨he.addTerm t, ?_, by simp [FDatabase.toDatabase]⟩
      simpa [Database.addEqs, Database.addTerm, Set.union_singleton] using
        (FDatabase.toDatabase_addTerm he (t := t))
  | union ex ey =>
    cases hx : ex.eval σ <;> cases hy : ey.eval σ <;>
      simp only [Action.write, Action.mark, execAction, hx, hy, Option.bind_none,
        Option.bind_some, Option.map_none]
    rename_i a b
    by_cases hn : a.isLit ∨ b.isLit
    · simp [hn]
    · simp only [Bool.or_eq_true, hn, ↓reduceIte, Option.map_some]
      refine ⟨he.addEq a b, ?_, by simp [FDatabase.toDatabase]⟩
      simpa [Database.addEqs, Database.addEq, Set.union_singleton] using
        (FDatabase.toDatabase_addEq he (a := a) (b := b))
  | subsume f es =>
    cases hv : Expr.evalList es σ with
    | none => simp [Action.write, Action.mark, execAction, hv]
    | some ts =>
      simp only [Action.write, Action.mark, execAction, hv, Option.map_some]
      refine ⟨he.subsume (.app f ts), ?_, ?_⟩
      · simpa [Database.addEqs, Database.addTerm, Set.union_singleton] using
          FDatabase.toDatabase_subsume he (.app f ts)
      · rw [FDatabase.toDatabase_subsume_eq]
        rfl

theorem execActions_spec {σ : Env} {d : FDatabase} (he : d.Closed) (as : List Action) :
    match Action.writes σ as, Action.marks σ as, execActions σ d as with
    | none, none, none => True
    | some W, some X, some e => e.Closed ∧
        e.toDatabase.SameMeaning ((d.toDatabase.addEqs W).addSubsumed X) ∧
        e.toDatabase.subsumed = d.toDatabase.subsumed ∪ X
    | _, _, _ => False := by
  induction as generalizing d with
  | nil =>
    exact ⟨he, by simpa [Database.addEqs] using Database.SameMeaning.refl d.toDatabase,
      by simp⟩
  | cons a as ih =>
    have ha := execAction_spec (σ := σ) he a
    cases hw : a.write σ <;> cases hx : a.mark σ <;> cases hr : execAction σ d a <;>
      simp only [hw, hx, hr] at ha
    · simp [Action.writes, Action.marks, execActions, hw, hx, hr]
    · rename_i W X mid
      have ht := ih ha.1
      cases hW : Action.writes σ as <;> cases hX : Action.marks σ as <;>
        cases hE : execActions σ mid as <;> simp only [hW, hX, hE] at ht
      · simp [Action.writes, Action.marks, execActions, hw, hx, hr, hW, hX, hE]
      · rename_i V Y out
        simp only [Action.writes, Action.marks, execActions, hw, hx, hr, hW, hX, hE,
          Option.bind_some, Option.map_some]
        refine ⟨ht.1, ?_, ?_⟩
        · simpa only [Database.addEqs, Database.addSubsumed, Set.union_assoc] using
            ht.2.1.trans ((FDatabase.meaning_addEqs ha.2.1 V ha.2.2).addSubsumed Y)
        · exact ht.2.2.trans (by rw [ha.2.2, Set.union_assoc])

theorem execAction_toDatabase {σ : Env} {d e : FDatabase} (he : d.Closed)
    {a : Action} (h : execAction σ d a = some e) :
    ∃ out, evalAction σ d.toDatabase a = some out ∧ e.toDatabase.SameMeaning out := by
  have hs := execAction_spec (σ := σ) he a
  rw [h] at hs
  cases hw : a.write σ <;> cases hx : a.mark σ <;> simp only [hw, hx] at hs
  rename_i W X
  exact ⟨_, by simp [evalAction_eq_write_mark, hw, hx], hs.2.1⟩

theorem execActions_toDatabase {σ : Env} {d e : FDatabase} (he : d.Closed)
    {as : List Action} (h : execActions σ d as = some e) :
    ∃ out, evalActions σ d.toDatabase as = some out ∧ e.toDatabase.SameMeaning out := by
  have hs := execActions_spec (σ := σ) he as
  rw [h] at hs
  cases hw : Action.writes σ as <;> cases hx : Action.marks σ as <;> simp only [hw, hx] at hs
  rename_i W X
  exact ⟨_, by simp [evalActions_eq_writes_marks, hw, hx], hs.2.1⟩


theorem execRunRules_induction_ruleset {R : List Rule} {d : FDatabase}
    {P : FDatabase → Prop}
    (hd : P d)
    (hf : ∀ r ∈ R, ∀ σ ∈ matchQuery d r.query,
      ∀ acc, P acc → P (fireInto r acc σ)) : P (execRunRules R d) := by
  have hfold : ∀ (xs : List (Rule × List Env)),
      (∀ rs ∈ xs, rs.1 ∈ R ∧
        ∀ σ ∈ rs.2, σ ∈ matchQuery d rs.1.query) →
      ∀ acc, P acc → P (xs.foldl (fun acc rs => rs.2.foldl (fireInto rs.1) acc) acc) := by
    intro xs
    induction xs with
    | nil => exact fun _ _ hp => hp
    | cons rs xs ih =>
      intro hx acc hp
      apply ih (fun rs hr => hx rs (by simp [hr]))
      have hr := hx rs (by simp)
      have hin : ∀ (ss : List Env), (∀ σ ∈ ss, σ ∈ matchQuery d rs.1.query) →
          ∀ acc, P acc → P (ss.foldl (fireInto rs.1) acc) := by
        intro ss
        induction ss with
        | nil => exact fun _ _ hp => hp
        | cons σ ss ih =>
          intro hs acc hp
          exact ih (fun σ hm => hs σ (by simp [hm])) _
            (hf rs.1 hr.1 σ (hs σ (by simp)) acc hp)
      exact hin rs.2 hr.2 acc hp
  unfold execRunRules execRunRulesWith
  apply hfold
  · intro rs hrs
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrs
    exact ⟨hr,
      fun σ hσ => by simpa only [matchQueryWith_eq] using hσ⟩
  · exact hd

private noncomputable def firingWrites (rs : Rule × Env) : Set (Term × Term) :=
  (Action.writes rs.2 rs.1.actions).getD ∅

private noncomputable def firingMarks (rs : Rule × Env) : Set Term :=
  (Action.marks rs.2 rs.1.actions).getD ∅

private theorem fireInto_spec {d : FDatabase} (he : d.Closed) (rs : Rule × Env) :
    (fireInto rs.1 d rs.2).Closed ∧
      (fireInto rs.1 d rs.2).toDatabase.SameMeaning
        ((d.toDatabase.addEqs (firingWrites rs)).addSubsumed (firingMarks rs)) ∧
      (fireInto rs.1 d rs.2).toDatabase.subsumed = d.toDatabase.subsumed ∪ firingMarks rs := by
  have h := execActions_spec (σ := rs.2) he rs.1.actions
  unfold fireInto firingWrites firingMarks
  cases hw : Action.writes rs.2 rs.1.actions <;>
    cases hx : Action.marks rs.2 rs.1.actions <;>
    cases hr : execActions rs.2 d rs.1.actions <;> simp only [hw, hx, hr] at h ⊢
  · exact ⟨he, by simpa [Database.addEqs] using Database.SameMeaning.refl d.toDatabase,
      by simp⟩
  · exact h

private noncomputable def firingWritesAll : List (Rule × Env) → Set (Term × Term)
  | [] => ∅
  | rs :: rss => firingWrites rs ∪ firingWritesAll rss

private noncomputable def firingMarksAll : List (Rule × Env) → Set Term
  | [] => ∅
  | rs :: rss => firingMarks rs ∪ firingMarksAll rss

private theorem mem_firingWritesAll {p : Term × Term} {rss : List (Rule × Env)} :
    p ∈ firingWritesAll rss ↔ ∃ rs ∈ rss, p ∈ firingWrites rs := by
  induction rss with
  | nil => simp [firingWritesAll]
  | cons rs rss ih => simp [firingWritesAll, ih, or_and_right, exists_or]

private theorem mem_firingMarksAll {p : Term} {rss : List (Rule × Env)} :
    p ∈ firingMarksAll rss ↔ ∃ rs ∈ rss, p ∈ firingMarks rs := by
  induction rss with
  | nil => simp [firingMarksAll]
  | cons rs rss ih => simp [firingMarksAll, ih, or_and_right, exists_or]

private theorem fold_firings_spec {d : FDatabase} (he : d.Closed)
    (rss : List (Rule × Env)) :
    let out := rss.foldl (fun acc rs => fireInto rs.1 acc rs.2) d
    out.Closed ∧ out.toDatabase.SameMeaning
      ((d.toDatabase.addEqs (firingWritesAll rss)).addSubsumed (firingMarksAll rss)) ∧
    out.toDatabase.subsumed = d.toDatabase.subsumed ∪ firingMarksAll rss := by
  induction rss generalizing d with
  | nil => exact ⟨he, by simpa [firingWritesAll, firingMarksAll, Database.addEqs] using
      Database.SameMeaning.refl d.toDatabase, by simp [firingMarksAll]⟩
  | cons rs rss ih =>
    obtain ⟨he', hh, hx⟩ := fireInto_spec he rs
    obtain ⟨ho, hh', hx'⟩ := ih he'
    refine ⟨ho, ?_, ?_⟩
    · simpa only [firingWritesAll, firingMarksAll, Database.addEqs, Database.addSubsumed,
        Set.union_assoc, List.foldl_cons] using
        hh'.trans ((FDatabase.meaning_addEqs hh (firingWritesAll rss) hx).addSubsumed
          (firingMarksAll rss))
    · exact hx'.trans (by rw [hx, Set.union_assoc]; rfl)

private def roundFirings (R : List Rule) (d : FDatabase) : List (Rule × Env) :=
  R.flatMap fun r => (matchQuery d r.query).map (r, ·)

/-- Firings are collected in the pre-state, then applied in sequence. -/
theorem execRunRules_eq_fold {d : FDatabase} (R : List Rule) : execRunRules R d =
    (R.map fun r => (r, matchQuery d r.query)).foldl
      (fun acc rs => rs.2.foldl (fireInto rs.1) acc) d := by
  simp only [execRunRules, execRunRulesWith, matchQueryWith_eq]

theorem execRunRules_eq_fold_of_subsumeFree {d : FDatabase} (R : List Rule)
    (_hd : ∀ r ∈ R, r.SubsumeFree) : execRunRules R d =
    (R.map fun r => (r, matchQuery d r.query)).foldl
      (fun acc rs => rs.2.foldl (fireInto rs.1) acc) d := execRunRules_eq_fold R

private theorem execRunRules_eq_firings {d : FDatabase} (R : List Rule) :
    execRunRules R d = (roundFirings R d).foldl (fun acc rs => fireInto rs.1 acc rs.2) d := by
  simp only [execRunRules, execRunRulesWith, matchQueryWith_eq, roundFirings,
    List.foldl_flatMap, List.foldl_map]

private theorem mem_roundFirings {R : List Rule} {d : FDatabase} {rs : Rule × Env} :
    rs ∈ roundFirings R d ↔ rs.1 ∈ R ∧ rs.2 ∈ matchQuery d rs.1.query := by
  rcases rs with ⟨r, σ⟩
  simp [roundFirings, List.mem_flatMap, and_assoc]

private theorem mem_firingWrites {p : Term × Term} {rs : Rule × Env} :
    p ∈ firingWrites rs ↔ ∃ W, Action.writes rs.2 rs.1.actions = some W ∧ p ∈ W := by
  unfold firingWrites
  cases Action.writes rs.2 rs.1.actions <;> simp

private theorem mem_firingMarks {p : Term} {rs : Rule × Env} :
    p ∈ firingMarks rs ↔ ∃ X, Action.marks rs.2 rs.1.actions = some X ∧ p ∈ X := by
  unfold firingMarks
  cases Action.marks rs.2 rs.1.actions <;> simp

private theorem firingWritesAll_eq {R : List Rule} {d : FDatabase} (he : d.Closed)
    (hi : d.IndexOk) (hj : d.IndexCurrent) :
    firingWritesAll (roundFirings R d) = RunWrites R d.toDatabase := by
  ext p
  constructor
  · intro hp
    obtain ⟨⟨r, σ⟩, hrs, hp⟩ := mem_firingWritesAll.mp hp
    obtain ⟨hr, hσ⟩ := mem_roundFirings.mp hrs
    obtain ⟨W, hW, hp⟩ := mem_firingWrites.mp hp
    obtain ⟨τ, hτ, hag⟩ := validQuerySubst_of_mem_matchQuery he hi hj hσ
    obtain ⟨ρ, hρ, hag'⟩ := hτ.exists_queryMatches
    have hag'' : Env.Agree ρ σ := fun v => (hag' v).trans (hag v)
    exact Set.mem_sUnion.mpr ⟨W, ⟨r, hr, ρ, hρ,
      (Action.writes_agree hag'' _).trans hW⟩, hp⟩
  · rintro ⟨W, ⟨r, hr, σ, hσ, hW⟩, hp⟩
    obtain ⟨τ, hτ, hag⟩ := hσ.exists_validQuerySubst
    obtain ⟨hmem, hag'⟩ := mem_matchQuery_of_validQuerySubst he hi hj hτ
    have hag'' : Env.Agree (Env.canon (Query.freeVars r.query []) τ) σ :=
      fun v => (hag' v).symm.trans (hag v)
    apply mem_firingWritesAll.mpr
    refine ⟨(r, _), mem_roundFirings.mpr ⟨hr, hmem⟩, mem_firingWrites.mpr ?_⟩
    exact ⟨W, (Action.writes_agree hag'' _).trans hW, hp⟩


private theorem firingMarksAll_eq {R : List Rule} {d : FDatabase} (he : d.Closed)
    (hi : d.IndexOk) (hj : d.IndexCurrent) :
    firingMarksAll (roundFirings R d) = RunMarks R d.toDatabase := by
  ext p
  constructor
  · intro hp
    obtain ⟨⟨r, σ⟩, hrs, hp⟩ := mem_firingMarksAll.mp hp
    obtain ⟨hr, hσ⟩ := mem_roundFirings.mp hrs
    obtain ⟨W, hW, hp⟩ := mem_firingMarks.mp hp
    obtain ⟨τ, hτ, hag⟩ := validQuerySubst_of_mem_matchQuery he hi hj hσ
    obtain ⟨ρ, hρ, hag'⟩ := hτ.exists_queryMatches
    have hag'' : Env.Agree ρ σ := fun v => (hag' v).trans (hag v)
    exact Set.mem_sUnion.mpr ⟨W, ⟨r, hr, ρ, hρ,
      (Action.marks_agree hag'' _).trans hW⟩, hp⟩
  · rintro ⟨W, ⟨r, hr, σ, hσ, hW⟩, hp⟩
    obtain ⟨τ, hτ, hag⟩ := hσ.exists_validQuerySubst
    obtain ⟨hmem, hag'⟩ := mem_matchQuery_of_validQuerySubst he hi hj hτ
    have hag'' : Env.Agree (Env.canon (Query.freeVars r.query []) τ) σ :=
      fun v => (hag' v).symm.trans (hag v)
    apply mem_firingMarksAll.mpr
    refine ⟨(r, _), mem_roundFirings.mpr ⟨hr, hmem⟩, mem_firingMarks.mpr ?_⟩
    exact ⟨W, (Action.marks_agree hag'' _).trans hW, hp⟩


/-- Every action adds data, so every round preserves closure. -/
theorem closed_execRunRules {R : List Rule} {d : FDatabase} (he : d.Closed) :
    (execRunRules R d).Closed := by
  rw [execRunRules_eq_firings]
  exact (fold_firings_spec he _).1

/-- A round computes all writes and marks from the pre-state matches. -/
theorem execRunRules_RunRules {R : List Rule} {d : FDatabase} (he : d.Closed)
    (hi : d.IndexOk) (hj : d.IndexCurrent) :
    (execRunRules R d).toDatabase.SameMeaning (RunRules R d.toDatabase) := by
  rw [execRunRules_eq_firings, RunRules.eq_pair, ← firingWritesAll_eq he hi hj,
    ← firingMarksAll_eq he hi hj]
  exact (fold_firings_spec he _).2.1

theorem execRunRules_subsumed {R : List Rule} {d : FDatabase} (he : d.Closed)
    (hi : d.IndexOk) (hj : d.IndexCurrent) :
    (execRunRules R d).toDatabase.subsumed =
      d.toDatabase.subsumed ∪ RunMarks R d.toDatabase := by
  rw [execRunRules_eq_firings, ← firingMarksAll_eq he hi hj]
  exact (fold_firings_spec he _).2.2

theorem execRunRules_subsumed_of_subsumeFree {R : List Rule} {d : FDatabase}
    (he : d.Closed) (hi : d.IndexOk) (hj : d.IndexCurrent) (hd : ∀ r ∈ R, r.SubsumeFree) :
    (execRunRules R d).toDatabase.subsumed = d.toDatabase.subsumed := by
  rw [execRunRules_subsumed he hi hj, RunMarks.eq_empty hd, Set.union_empty]

theorem execRunRules_index {R : List Rule} {d : FDatabase}
    (hi : d.IndexOk) (hj : d.IndexCurrent) :
    (execRunRules R d).IndexOk ∧ (execRunRules R d).IndexCurrent := by
  apply execRunRules_induction_ruleset (P := fun e => e.IndexOk ∧ e.IndexCurrent) ⟨hi, hj⟩
  intro r _ σ _ acc h
  unfold fireInto
  split
  · rename_i e he
    exact execActions_preserves (P := fun e => e.IndexOk ∧ e.IndexCurrent)
      (fun _ t h => ⟨h.1.addTerm t, h.2.addTerm t⟩)
      (fun _ a b h _ => ⟨h.1.addEq a b, h.2.addEq a b⟩)
      (fun _ t h => ⟨h.1.subsume t, h.2.subsume t⟩) h he
  · exact h

end Egglog
