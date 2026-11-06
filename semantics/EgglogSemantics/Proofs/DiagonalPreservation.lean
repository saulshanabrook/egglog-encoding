import EgglogSemantics.Proofs.Diagonal

namespace Egglog

theorem evalAction_diag {σ : Env} {db db' : Database} {a : Action} (hu : a.UnionFree)
    (hd : db.Diag) (h : evalAction σ db a = some db') : db'.Diag := by
  rcases evalAction_eq_some h with ⟨_, t, _, _, rfl⟩ |
    ⟨_, _, _, _, rfl, _⟩ | ⟨f, _, ts, _, _, rfl⟩
  · exact hd.addTerm t
  · exact hu.elim
  · exact (hd.addTerm (.app f ts)).addSubsumed {.app f ts}

theorem evalActions_diag {σ : Env} {db db' : Database} {as : List Action}
    (hu : Actions.UnionFree as) (hd : db.Diag)
    (h : evalActions σ db as = some db') : db'.Diag := by
  induction as generalizing db with
  | nil => cases Option.some.inj h; exact hd
  | cons a as ih =>
    obtain ⟨mid, ha, ht⟩ := Option.bind_eq_some_iff.mp h
    exact ih hu.2 (evalAction_diag hu.1 hd ha) ht

theorem evalLocalActions_diag {σ : Env} {db db' : Database} {as : List Action}
    (hu : Actions.UnionFree as) (hd : db.Diag)
    (h : evalActions σ db as = some db') : db'.Diag := evalActions_diag hu hd h

theorem Action.write_diag {σ : Env} {a : Action} (hu : a.UnionFree)
    {W : Set (Term × Term)} (h : a.write σ = some W) : ∀ p ∈ W, p.1 = p.2 := by
  cases a with
  | expr e =>
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp h
    rintro p rfl
    rfl
  | union _ _ => exact hu.elim
  | subsume e =>
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.mp h
    simp

theorem Action.writes_diag {σ : Env} {as : List Action} (hu : Actions.UnionFree as)
    {W : Set (Term × Term)} (h : Action.writes σ as = some W) :
    ∀ p ∈ W, p.1 = p.2 := by
  induction as generalizing W with
  | nil => cases Option.some.inj h; simp
  | cons a as ih =>
    obtain ⟨V, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨U, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    intro p hp
    exact hp.elim (Action.write_diag hu.1 ha p) (ih hu.2 ht p)

theorem RunRules.diag {R : List Rule} {db : Database}
    (hn : db.NoUnions) (hu : ∀ r ∈ R, r.UnionFree) :
    (RunRules R db).Diag := by
  rw [RunRules.eq_pair]
  rintro p (hp | hp)
  · exact hn.diag p hp
  · obtain ⟨W, ⟨r, hr, σ, _, hW⟩, hp⟩ := hp
    exact Action.writes_diag (hu r hr) hW p hp

theorem RunRules.noUnions {R : List Rule} {db : Database}
    (hn : db.NoUnions) (hu : ∀ r ∈ R, r.UnionFree) :
    (RunRules R db).NoUnions := ⟨RunRules.diag hn hu⟩

theorem Database.NoUnions.empty : Database.empty.NoUnions :=
  ⟨by simp [Database.Diag, Database.empty]⟩

theorem Reach.noUnions {S : Schedule} {d e : Database}
    (h : Reach d S e) (hn : d.NoUnions) (hu : S.UnionFree) : e.NoUnions := by
  induction h with
  | run => exact RunRules.noUnions hn hu
  | seq _ _ ih₁ ih₂ =>
    exact ih₂ (ih₁ hn (fun r hr => hu r (List.mem_append_left _ hr)))
      (fun r hr => hu r (List.mem_append_right _ hr))
  | fixpoint _ _ ih => exact ih hn hu
  | again _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hn hu) hu

end Egglog
