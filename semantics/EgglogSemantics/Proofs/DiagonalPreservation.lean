import EgglogSemantics.Proofs.Diagonal

namespace Egglog

theorem evalAction_diag {σ : Env} {db db' : Database} {a : Action} (hu : a.UnionFree)
    (hd : db.Diag) (h : evalAction σ db a = some db') : db'.Diag := by
  rcases evalAction_eq_some h with ⟨_, t, _, _, rfl⟩ |
    ⟨_, _, _, _, rfl, _⟩ | ⟨_, t, _, _, rfl⟩
  · exact hd.addTerm t
  · exact hu.elim
  · exact hd.deleteRows {t}

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
  | delete e =>
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
  rintro p (hp | hp)
  · exact hn.diag.deleteRows _ p hp
  · obtain ⟨W, ⟨r, hr, σ, _, hW⟩, hp⟩ := hp
    exact Action.writes_diag (hu r hr) hW p hp

theorem RunRules.noUnions {R : List Rule} {db : Database}
    (hn : db.NoUnions) (hu : ∀ r ∈ R, r.UnionFree) :
    (RunRules R db).NoUnions := ⟨RunRules.diag hn hu⟩

theorem SaturateReach.noUnions {R : List Rule} {d e : Database}
    (h : SaturateReach R d e) (hn : d.NoUnions) (hu : ∀ r ∈ R, r.UnionFree) : e.NoUnions := by
  induction h with
  | fixpoint => exact RunRules.noUnions hn hu
  | again _ _ ih => exact ih (RunRules.noUnions hn hu)

theorem CmdStep.noUnions {A B : Database} (hn : A.NoUnions) {c : Cmd} (hu : c.UnionFree)
    (h : CmdStep A c B) : B.NoUnions := by
  cases c with
  | run R => subst B; exact RunRules.noUnions hn hu
  | saturate R => exact SaturateReach.noUnions h hn hu

theorem Database.NoUnions.empty : Database.empty.NoUnions := by
  constructor <;> simp [Database.Diag, Database.empty]

theorem ProgramStep.noUnions {d e : Database} {p : List Cmd} (h : ProgramStep d p e)
    (hn : d.NoUnions) (hu : ∀ c ∈ p, c.UnionFree) : e.NoUnions := by
  induction h with
  | nil => exact hn
  | cons hc _ ih => exact ih (hc.noUnions hn (hu _ (by simp))) (fun c hc => hu c (by simp [hc]))

end Egglog
