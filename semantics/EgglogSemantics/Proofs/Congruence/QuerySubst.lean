import EgglogSemantics.Proofs.Match

/-! Mathematical construction of query substitutions from one common assignment. -/

namespace Egglog.Congruence

def sourceSubst (env : Env) (g : Var → Term) (p : Pattern) : Env :=
  (p.freeVars env).map fun v => (v, g v)

theorem dom_sourceSubst {env : Env} {g : Var → Term} {p : Pattern} :
    Env.dom (sourceSubst env g p) = p.freeVars env := by
  simp [sourceSubst, Env.dom, List.map_map, Function.comp_def]

theorem lookup_sourceSubst {env : Env} {g : Var → Term} {p : Pattern} {v : Var}
    (hv : v ∈ p.freeVars env) : Env.lookup v (sourceSubst env g p) = some (g v) :=
  (Env.lookup_eq_some_iff_mem (by rw [dom_sourceSubst]; exact p.freeVars_nodup env)).mpr
    (List.mem_map.mpr ⟨v, hv, rfl⟩)

theorem lookup_nil_sourceSubst {g : Var → Term} {p : Pattern} {v : Var} (hv : v ∈ p.vars) :
    Env.lookup v (sourceSubst [] g p) = some (g v) :=
  lookup_sourceSubst (p.mem_freeVars.mpr ⟨hv, by simp [Env.dom]⟩)

theorem Query.vars_nodup (q : Query) : (Query.vars q).Nodup := by
  induction q with
  | nil => simp [Query.vars]
  | cons p ps ih => exact List.Nodup.union _ ih

/-- Join a family of matching patterns at one valued assignment. This construction is
mathematical; it does not invoke the executable matcher. -/
theorem validQuerySubst_of_assignment {src : Database} {q : Query} {g : Var → Term}
    (hgt : ∀ v ∈ Query.vars q, g v ∈ src.values)
    (hm : ∀ p ∈ q, Matches src p (sourceSubst [] g p)) :
    ∃ τ, ValidQuerySubst src q τ ∧ (∀ b ∈ τ, b.1 ∈ Query.vars q) ∧
      ∀ v ∈ Query.vars q, Env.lookup v τ = some (g v) := by
  have hmem : ∀ p ∈ q, ∀ v ∈ p.vars, v ∈ Query.vars q := fun p hp v hv =>
    Query.mem_vars.mpr ⟨p, hp, hv⟩
  have hvalid : ∀ p ∈ q, ValidSubst src p (sourceSubst [] g p) := by
    intro p hp
    refine ⟨⟨by rw [dom_sourceSubst], ?_⟩, hm p hp⟩
    rintro b hb
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    exact (hgt v (hmem p hp v (p.mem_freeVars.mp hv).1)).1
  have hnd : (Env.dom (Query.vars q |>.map fun v => (v, g v))).Nodup := by
    simpa [Env.dom, List.map_map, Function.comp_def] using Query.vars_nodup q
  have hrefines : ∀ ρ ∈ q.map (sourceSubst [] g),
      Env.Refines ρ (Query.vars q |>.map fun v => (v, g v)) := by
    rintro ρ hρ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hρ
    rintro b hb
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
    exact (Env.lookup_eq_some_iff_mem hnd).mpr
      (List.mem_map.mpr ⟨v, hmem p hp v (p.mem_freeVars.mp hv).1, rfl⟩)
  obtain ⟨τ, hu, hrτ⟩ := Env.exists_unionAll _ hrefines
  have hself : ∀ ρ ∈ q.map (sourceSubst [] g), Env.Refines ρ ρ := by
    rintro ρ hρ
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hρ
    exact Env.Refines.self_of_nodup (by rw [dom_sourceSubst]; exact p.freeVars_nodup _)
  obtain ⟨hall, -⟩ := hu.refines_of_mem hself
  refine ⟨τ, ⟨_, List.forall₂_map_self hvalid, hu⟩, ?_, fun v hv => ?_⟩
  · intro b hb
    obtain ⟨v, hv, heq⟩ := List.mem_map.mp (Env.mem_of_lookup (hrτ b hb))
    obtain rfl : v = b.1 := congrArg Prod.fst heq
    exact hv
  obtain ⟨p, hp, hvp⟩ := Query.mem_vars.mp hv
  exact hall _ (List.mem_map.mpr ⟨p, hp, rfl⟩) (v, g v)
    (List.mem_map.mpr ⟨v, p.mem_freeVars.mpr ⟨hvp, by simp [Env.dom]⟩, rfl⟩)

/-- Restricting a common matching environment to each pattern supplies a valid query
substitution with exactly the same values on the query's variables. -/
theorem validQuerySubst_of_matches {d : Database} {q : Query} {ρ : Env}
    (hv : ∀ v ∈ Query.vars q, ∃ t, Env.lookup v ρ = some t ∧ t ∈ d.values)
    (hm : ∀ p ∈ q, Matches d p ρ) :
    ∃ σ, ValidQuerySubst d q σ ∧
      ∀ v ∈ Query.vars q, Env.lookup v σ = Env.lookup v ρ := by
  let g : Var → Term := fun v => (Env.lookup v ρ).getD (.lit (.int 0))
  have hg : ∀ v ∈ Query.vars q, Env.lookup v ρ = some (g v) ∧ g v ∈ d.values := by
    intro v hvq
    obtain ⟨t, ht, hmem⟩ := hv v hvq
    simpa [g, ht] using hmem
  obtain ⟨σ, hσ, _, hlookup⟩ := validQuerySubst_of_assignment (fun v hv => (hg v hv).2)
    (fun p hp => (hm p hp).of_agreeOn fun v hv => by
      rw [(hg v (Query.mem_vars.mpr ⟨p, hp, hv⟩)).1, lookup_nil_sourceSubst hv])
  exact ⟨σ, hσ, fun v hv => (hlookup v hv).trans (hg v hv).1.symm⟩

end Egglog.Congruence
