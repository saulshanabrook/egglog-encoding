import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finite.Prod
import EgglogSemantics.Proofs.Step

/-! Finite mathematical executions have finite stores. No executable representation is
needed: rule matching ranges over finitely many substitutions at each finite state.
`Database.FiniteStore` tracks the equation set. -/

namespace Egglog

/-- Lists of a fixed length over a finite set form a finite set. -/
theorem finite_lists {α : Type*} {S : Set α} (hS : S.Finite) (n : Nat) :
    {xs : List α | xs.length = n ∧ ∀ x ∈ xs, x ∈ S}.Finite := by
  induction n with
  | zero =>
      apply (Set.finite_singleton []).subset
      intro xs hx
      simpa only [List.length_eq_zero_iff, Set.mem_singleton_iff] using hx.1
  | succ n ih =>
      apply (hS.image2 List.cons ih).subset
      intro xs hx
      cases xs with
      | nil => simp at hx
      | cons x xs =>
          exact ⟨x, hx.2 x (by simp), xs,
            ⟨by simpa using hx.1, fun y hy => hx.2 y (by simp [hy])⟩, rfl⟩

theorem ValidEnv.finite {db : Database} (ht : db.terms.Finite) (vs : List Var) :
    {σ | ValidEnv vs db σ}.Finite := by
  apply (finite_lists ((List.finite_toSet vs).prod ht) vs.length).subset
  intro σ hσ
  refine ⟨by simpa [Env.dom] using hσ.1.length_eq, ?_⟩
  intro b hb
  exact ⟨hσ.1.subset (List.mem_map.mpr ⟨b, hb, rfl⟩), hσ.2 b hb⟩

theorem ValidSubst.finite {db : Database} (ht : db.terms.Finite) (p : Pattern) :
    {σ | ValidSubst db p σ}.Finite :=
  (ValidEnv.finite ht (p.freeVars [])).subset fun _ h => h.1

theorem Env.UnionAll.eq_flatten {σs : List Env} {σ : Env} (h : Env.UnionAll σs σ) :
    σ = σs.flatten := by
  induction h with
  | nil => rfl
  | single => simp
  | step hu _ ih => simpa [hu.2, List.append_assoc] using ih

theorem ValidQuerySubst.finite {db : Database} (ht : db.terms.Finite) (q : Query) :
    {σ | ValidQuerySubst db q σ}.Finite := by
  have hseq : {σs | List.Forall₂ (ValidSubst db) q σs}.Finite := by
    induction q with
    | nil =>
        apply (Set.finite_singleton []).subset
        intro σs h; cases h; rfl
    | cons p ps ih =>
        apply ((ValidSubst.finite ht p).image2 List.cons ih).subset
        intro σs h
        cases h with
        | cons hp hps => exact ⟨_, hp, _, hps, rfl⟩
  apply (hseq.image List.flatten).subset
  rintro σ ⟨σs, hs, hu⟩
  exact ⟨σs, hs, hu.eq_flatten.symm⟩

theorem Term.finite_subterms (t : Term) : t.subterms.Finite := by
  apply (List.finite_toSet t.subtermList).subset
  intro s hs
  exact (Term.mem_subtermList t).mpr hs

/-- A finite assertion set has finitely many subterms. -/
theorem Database.finite_terms {db : Database} (h : db.eqs.Finite) : db.terms.Finite := by
  apply (h.biUnion (fun p _ => p.1.finite_subterms.union p.2.finite_subterms)).subset
  intro t ht
  obtain ⟨p, hp, ht⟩ := Database.mem_terms_iff.mp ht
  exact Set.mem_iUnion₂.mpr ⟨p, hp, ht⟩

theorem Database.finite_addTerm {db : Database} (h : db.eqs.Finite) (t : Term) :
    (db.addTerm t).eqs.Finite := h.insert _

theorem Database.finite_addTerms {db : Database} (h : db.eqs.Finite) (ts : List Term) :
    (db.addTerms ts).eqs.Finite := by
  induction ts generalizing db with
  | nil => exact h
  | cons t ts ih => exact ih (Database.finite_addTerm h t)

theorem Database.finite_addEq {db : Database} (h : db.eqs.Finite) (a b : Term) :
    (db.addEq a b).eqs.Finite :=
  h.insert _

theorem QueryMatches.finite {db : Database} (ht : db.terms.Finite) (q : Query) :
    {σ | QueryMatches db q σ}.Finite :=
  (ValidEnv.finite ht q.vars).subset fun _ h => h.1

/-- The rows a deletion removes are held, so finitely many when the equations are. -/
theorem Database.finite_deletedRows {db : Database} (h : db.eqs.Finite) (X : Set Term) :
    (db.deletedRows X).Finite :=
  (h.image Prod.fst).subset fun r hr => ⟨(r, r), hr.1, rfl⟩

theorem Database.finite_deleteRows {db : Database} (h : db.eqs.Finite)
    (X : Set Term) : (db.deleteRows X).eqs.Finite := by
  apply (h.subset Set.sdiff_subset).union
  apply (((Database.finite_deletedRows h X).biUnion fun t _ => List.finite_toSet t.children).image
    (fun c => (c, c))).subset
  rintro p ⟨t, ht, c, hc, rfl⟩
  exact ⟨c, Set.mem_iUnion₂.mpr ⟨t, ht, hc⟩, rfl⟩

theorem evalAction_finite {σ : Env} {db d : Database} {a : Action} (h : db.eqs.Finite)
    (he : evalAction σ db a = some d) : d.eqs.Finite := by
  rcases evalAction_eq_some he with ⟨_, t, _, _, rfl⟩ |
    ⟨_, _, a, b, _, _, _, _, rfl⟩ | ⟨_, t, _, _, rfl⟩
  · exact Database.finite_addTerm h t
  · exact Database.finite_addEq h a b
  · exact Database.finite_deleteRows h {t}

theorem evalActions_finite {σ : Env} {as : List Action} {db d : Database} (h : db.eqs.Finite)
    (he : evalActions σ db as = some d) : d.eqs.Finite := by
  induction as generalizing db with
  | nil => cases he; exact h
  | cons a as ih =>
    obtain ⟨mid, hm, hd⟩ := Option.bind_eq_some_iff.mp he
    exact ih (evalAction_finite h hm) hd

theorem evalLocalActions_finite {as : List Action} {db d : Database} {σ : Env}
    (h : db.eqs.Finite) (he : evalActions σ db as = some d) : d.eqs.Finite :=
  evalActions_finite h he

theorem RuleResults.finite {db : Database} (ht : db.terms.Finite) (r : Rule) :
    (RuleResults db r).Finite := by
  classical
  apply ((ValidQuerySubst.finite ht r.query).image
    (fun σ => (evalActions σ db r.actions).getD db)).subset
  rintro d ⟨σ, hσ, hd⟩
  exact ⟨σ, hσ, by simp [hd]⟩

theorem Action.write_finite {σ : Env} {a : Action} {W : Set (Term × Term)}
    (h : a.write σ = some W) : W.Finite := by
  cases a with
  | expr e =>
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact Set.finite_singleton _
  | union a b =>
    obtain ⟨t, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u, _, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · simp at h
    · cases Option.some.inj h; exact Set.finite_singleton _
  | delete e =>
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact Set.finite_empty

theorem Action.erase_finite {σ : Env} {a : Action} {X : Set Term}
    (h : a.erase σ = some X) : X.Finite := by
  cases a with
  | expr _ | union _ _ =>
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact Set.finite_empty
  | delete e =>
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
    exact Set.finite_singleton _

theorem Action.writes_finite {σ : Env} {as : List Action} {W : Set (Term × Term)}
    (h : Action.writes σ as = some W) : W.Finite := by
  induction as generalizing W with
  | nil => cases Option.some.inj h; exact Set.finite_empty
  | cons a as ih =>
    obtain ⟨V, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨U, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (Action.write_finite ha).union (ih ht)

theorem Action.erases_finite {σ : Env} {as : List Action} {W : Set (Term)}
    (h : Action.erases σ as = some W) : W.Finite := by
  induction as generalizing W with
  | nil => cases Option.some.inj h; exact Set.finite_empty
  | cons a as ih =>
    obtain ⟨V, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨U, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (Action.erase_finite ha).union (ih ht)

theorem RunWrites.finite {db : Database} (he : db.eqs.Finite)
    (R : List Rule) : (RunWrites R db).Finite := by
  have hfin : (⋃ r ∈ {r | r ∈ R}, ⋃ σ ∈ {σ | QueryMatches db r.query σ},
      (Action.writes σ r.actions).getD ∅).Finite :=
    (List.finite_toSet R).biUnion fun r _ =>
      (QueryMatches.finite (Database.finite_terms he) r.query).biUnion
      fun σ _ => by
        cases hw : Action.writes σ r.actions with
        | none => exact Set.finite_empty
        | some W => exact Action.writes_finite hw
  apply hfin.subset
  rintro p ⟨W, ⟨r, hr, σ, hσ, hw⟩, hp⟩
  exact Set.mem_iUnion₂.mpr ⟨r, hr, Set.mem_iUnion₂.mpr ⟨σ, hσ, by simpa [hw] using hp⟩⟩

theorem RunErases.finite {db : Database} (he : db.eqs.Finite)
    (R : List Rule) : (RunErases R db).Finite := by
  have hfin : (⋃ r ∈ {r | r ∈ R}, ⋃ σ ∈ {σ | QueryMatches db r.query σ},
      (Action.erases σ r.actions).getD ∅).Finite :=
    (List.finite_toSet R).biUnion fun r _ =>
      (QueryMatches.finite (Database.finite_terms he) r.query).biUnion
      fun σ _ => by
        cases hw : Action.erases σ r.actions with
        | none => exact Set.finite_empty
        | some W => exact Action.erases_finite hw
  apply hfin.subset
  rintro p ⟨W, ⟨r, hr, σ, hσ, hw⟩, hp⟩
  exact Set.mem_iUnion₂.mpr ⟨r, hr, Set.mem_iUnion₂.mpr ⟨σ, hσ, by simpa [hw] using hp⟩⟩

theorem RunRules.finite_eqs {db : Database} (he : db.eqs.Finite)
    (R : List Rule) : (RunRules R db).eqs.Finite :=
  (Database.finite_deleteRows he (RunErases R db)).union (RunWrites.finite he R)

theorem SaturateReach.finite {R : List Rule} {db d : Database}
    (h : SaturateReach R db d) (he : db.eqs.Finite) :
    d.eqs.Finite := by
  induction h with
  | fixpoint => exact RunRules.finite_eqs he R
  | again _ _ ih => exact ih (RunRules.finite_eqs he R)

theorem CmdStep.finite {db d : Database} {c : Cmd} (h : CmdStep db c d)
    (he : db.eqs.Finite) : d.eqs.Finite := by
  cases c with
  | run R => subst d; exact RunRules.finite_eqs he R
  | saturate R => exact SaturateReach.finite h he

theorem ProgramStep.finite {db d : Database} {P : List Cmd} (h : ProgramStep db P d)
    (he : db.eqs.Finite) : d.eqs.Finite := by
  induction h with
  | nil => exact he
  | cons hc _ ih =>
      exact ih (hc.finite he)

theorem ProgramStep.finite_from_empty {d : Database} {P : List Cmd}
    (h : ProgramStep Database.empty P d) : d.eqs.Finite :=
  h.finite Set.finite_empty

/-- The assertion set is finite. -/
structure Database.FiniteStore (db : Database) : Prop where
  eqs : db.eqs.Finite

namespace Database.FiniteStore

theorem of_eqs_rules {db : Database} (he : db.eqs.Finite) :
    db.FiniteStore := ⟨he⟩

theorem empty : Database.empty.FiniteStore :=
  of_eqs_rules Set.finite_empty

theorem addTerm {db : Database} (h : db.FiniteStore) (t : Term) :
    (db.addTerm t).FiniteStore :=
  of_eqs_rules (Database.finite_addTerm h.eqs t)

theorem addTerms {db : Database} (h : db.FiniteStore) (ts : List Term) :
    (db.addTerms ts).FiniteStore := by
  induction ts generalizing db with
  | nil => exact h
  | cons t ts ih => exact ih (h.addTerm t)

theorem addEq {db : Database} (h : db.FiniteStore) (a b : Term) :
    (db.addEq a b).FiniteStore :=
  of_eqs_rules (Database.finite_addEq h.eqs a b)

theorem deleteRows {db : Database} (h : db.FiniteStore) (X : Set Term) :
    (db.deleteRows X).FiniteStore := ⟨Database.finite_deleteRows h.eqs X⟩

end Database.FiniteStore

theorem evalAction_finiteStore {σ : Env} {db d : Database} {a : Action} (h : db.FiniteStore)
    (he : evalAction σ db a = some d) : d.FiniteStore :=
  ⟨evalAction_finite h.eqs he⟩

theorem evalActions_finiteStore {σ : Env} {as : List Action} {db d : Database}
    (h : db.FiniteStore) (he : evalActions σ db as = some d) : d.FiniteStore :=
  ⟨evalActions_finite h.eqs he⟩

theorem evalLocalActions_finiteStore {as : List Action} {db d : Database} {σ : Env}
    (h : db.FiniteStore) (he : evalActions σ db as = some d) : d.FiniteStore :=
  evalActions_finiteStore h he

theorem RunRules.finiteStore {db : Database} (h : db.FiniteStore) (R : List Rule) :
    (RunRules R db).FiniteStore := ⟨RunRules.finite_eqs h.eqs R⟩

theorem SaturateReach.finiteStore {R : List Rule} {db d : Database}
    (h : SaturateReach R db d) (hf : db.FiniteStore) : d.FiniteStore :=
  ⟨h.finite hf.eqs⟩

theorem CmdStep.finiteStore {db d : Database} {c : Cmd}
    (h : CmdStep db c d) (hf : db.FiniteStore) : d.FiniteStore :=
  ⟨h.finite hf.eqs⟩

theorem ProgramStep.finiteStore {db d : Database} {P : List Cmd}
    (h : ProgramStep db P d) (hf : db.FiniteStore) : d.FiniteStore := by
  induction h with
  | nil => exact hf
  | cons hc _ ih => exact ih (hc.finiteStore hf)

/-- Finite mathematical executions from the empty database have finite stores. -/
theorem ProgramStep.finiteStore_from_empty {d : Database} {P : List Cmd}
    (h : ProgramStep Database.empty P d) : d.FiniteStore :=
  h.finiteStore Database.FiniteStore.empty

end Egglog
