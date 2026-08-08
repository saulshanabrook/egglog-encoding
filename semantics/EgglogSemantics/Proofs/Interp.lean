import EgglogSemantics.Impl.Interp
import EgglogSemantics.Proofs.Closure
import EgglogSemantics.Proofs.Scope

namespace Egglog
namespace FDatabase
@[simp] theorem toDatabase_terms {d : FDatabase} :
    d.toDatabase.terms = {t | t ∈ d.terms} := rfl

@[simp] theorem toDatabase_eqs {d : FDatabase} : d.toDatabase.eqs = {p | p ∈ d.eqs} := rfl

@[simp] theorem toDatabase_env {d : FDatabase} : d.toDatabase.env = d.env := rfl

@[simp] theorem toDatabase_rules {d : FDatabase} :
    d.toDatabase.rules = {r | r ∈ d.rules} := rfl

@[simp] theorem toDatabase_empty : empty.toDatabase = Database.empty := by
  simp [empty, toDatabase, Database.empty]

@[simp] theorem toDatabase_addTerm {t : Term} {d : FDatabase} :
    (d.addTerm t).toDatabase = d.toDatabase.addTerm t := by
  simp only [addTerm, toDatabase, Database.addTerm]
  congr 1
  · ext s
    simp [List.mem_dedup, Term.mem_subtermList, Term.subterms, Or.comm]
  · ext r
    simp [List.mem_dedup, Or.comm]

@[simp] theorem toDatabase_addEq {a b : Term} {d : FDatabase} :
    (d.addEq a b).toDatabase = d.toDatabase.addEq a b := by
  simp only [addEq, addTerm, toDatabase, Database.addEq, Database.addTerm]
  congr 1
  · ext s
    simp only [Set.mem_setOf_eq, List.mem_dedup, List.mem_append, Term.mem_subtermList,
      Set.mem_union, Term.mem_subterms]
    tauto
  · ext r
    simp only [Set.mem_setOf_eq, List.mem_dedup, List.mem_append, Term.mem_ctorRowList,
      Set.mem_union]
    tauto
  · ext p
    simp [List.mem_dedup, Set.insert_def, Or.comm]

@[simp] theorem toDatabase_setRows {d : FDatabase} {L : List Row} :
    ({ d with rows := L } : FDatabase).toDatabase =
      { d.toDatabase with rows := {r | r ∈ L} } := rfl

@[simp] theorem toDatabase_addTerms {ts : List Term} {d : FDatabase} :
    (d.addTerms ts).toDatabase = d.toDatabase.addTerms ts := by
  induction ts generalizing d with
  | nil => rfl
  | cons t ts ih => simpa [addTerms, Database.addTerms] using ih (d := d.addTerm t)

@[simp] theorem toDatabase_addRow {f : FnName} {as vs : List Term} {d : FDatabase} :
    (d.addRow f as vs).toDatabase = d.toDatabase.addRow f as vs := by
  have hb : ((d.addTerms as).addTerms vs).toDatabase
      = Database.addTerms vs (Database.addTerms as d.toDatabase) := by
    rw [toDatabase_addTerms, toDatabase_addTerms]
  have hr := congrArg Database.rows hb
  rw [Set.ext_iff] at hr
  show ({ (d.addTerms as).addTerms vs with
      rows := (⟨f, as, vs⟩ :: ((d.addTerms as).addTerms vs).rows).dedup } :
    FDatabase).toDatabase = _
  rw [toDatabase_setRows, hb]
  simp only [Database.addRow]
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, List.mem_dedup, List.mem_cons, Set.mem_insert_iff]
  have := hr r
  simp only [FDatabase.toDatabase, Set.mem_setOf_eq] at this
  tauto

@[simp] theorem mem_terms_union {d₁ d₂ : FDatabase} {t : Term} :
    t ∈ (d₁.union d₂).terms ↔ t ∈ d₁.terms ∨ t ∈ d₂.terms := by
  simp [FDatabase.union, List.mem_dedup]

@[simp] theorem mem_rows_union {d₁ d₂ : FDatabase} {r : Row} :
    r ∈ (d₁.union d₂).rows ↔ r ∈ d₁.rows ∨ r ∈ d₂.rows := by
  simp [FDatabase.union, List.mem_dedup]

@[simp] theorem mem_eqs_union {d₁ d₂ : FDatabase} {p : Term × Term} :
    p ∈ (d₁.union d₂).eqs ↔ p ∈ d₁.eqs ∨ p ∈ d₂.eqs := by
  simp [FDatabase.union, List.mem_dedup]

@[simp] theorem coe_termsF {d : FDatabase} : ↑d.termsF = d.toDatabase.terms := by
  ext t; simp [termsF, toDatabase]

@[simp] theorem coe_eqsF {d : FDatabase} : ↑d.eqsF = d.toDatabase.eqs := by
  ext p; simp [eqsF, toDatabase]

@[simp] theorem toDatabase_setEnv {d : FDatabase} {σ : Env} :
    ({ d with env := σ } : FDatabase).toDatabase = { d.toDatabase with env := σ } := rfl

@[simp] theorem toDatabase_restore {d d' : FDatabase} :
    ({ d' with env := d.env, rules := d.rules } : FDatabase).toDatabase
      = { d'.toDatabase with env := d.toDatabase.env, rules := d.toDatabase.rules } := rfl

/-- `WF` gives exactly the side condition the closure needs. -/
theorem eqsF_subset_candidates {d : FDatabase} (h : d.WF) :
    d.eqsF ⊆ candidates d.termsF := by
  intro p hp
  have hp' : p ∈ d.toDatabase.eqs := by rw [← coe_eqsF]; exact hp
  obtain ⟨h₁, h₂⟩ := h.eqsInTerms p hp'
  rw [← coe_termsF] at h₁ h₂
  exact mem_candidates.mpr ⟨h₁, h₂⟩

@[simp] theorem mem_union_terms {d₁ d₂ : FDatabase} {t : Term} :
    t ∈ (d₁.union d₂).terms ↔ t ∈ d₁.terms ∨ t ∈ d₂.terms := by
  simp [union, List.mem_dedup]

@[simp] theorem mem_union_eqs {d₁ d₂ : FDatabase} {p : Term × Term} :
    p ∈ (d₁.union d₂).eqs ↔ p ∈ d₁.eqs ∨ p ∈ d₂.eqs := by
  simp [union, List.mem_dedup]

@[simp] theorem union_sig {d₁ d₂ : FDatabase} : (d₁.union d₂).sig = d₁.sig := rfl

@[simp] theorem union_env {d₁ d₂ : FDatabase} : (d₁.union d₂).env = d₁.env := rfl

@[simp] theorem union_rules {d₁ d₂ : FDatabase} : (d₁.union d₂).rules = d₁.rules := rfl

/-- `closureF` decides `Cong` on the database `d` denotes, given the well-formedness the
interpreter maintains: every asserted equality's endpoints are terms `d` holds. -/
theorem mem_closureF_iff {d : FDatabase} (h : d.eqsF ⊆ candidates d.termsF) {a b : Term} :
    (a, b) ∈ d.closureF ↔ Cong d.toDatabase a b :=
  mem_closureTotal_iff coe_termsF.symm coe_eqsF.symm h

/-- `closureF` decides `Cong` on a well-formed database. -/
theorem mem_closureF_iff_of_wf {d : FDatabase} (h : d.WF) {a b : Term} :
    (a, b) ∈ d.closureF ↔ Cong d.toDatabase a b :=
  mem_closureF_iff (eqsF_subset_candidates h)

end FDatabase
theorem mem_assignments {terms : List Term} {vars : List Var} {σ : Env} :
    σ ∈ assignments terms vars ↔ Env.dom σ = vars ∧ ∀ b ∈ σ, b.2 ∈ terms := by
  induction vars generalizing σ with
  | nil =>
    simp only [assignments, List.mem_singleton]
    refine ⟨fun h => by simp [h], fun h => ?_⟩
    simpa [Env.dom] using h.1
  | cons v vs ih =>
    simp only [assignments, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨t, ht, τ, hτ, rfl⟩
      obtain ⟨hd, hv⟩ := ih.mp hτ
      refine ⟨by simp [hd], fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ht
      · exact hv b hb
    · rintro ⟨hd, hv⟩
      match σ with
      | [] => simp at hd
      | (w, t) :: τ =>
        simp only [Env.dom_cons, List.cons.injEq] at hd
        obtain ⟨rfl, hd⟩ := hd
        exact ⟨t, hv (w, t) (by simp), τ, ih.mpr ⟨hd, fun b hb => hv b (by simp [hb])⟩, rfl⟩

theorem Env.mem_canon {vars : List Var} {σ : Env} {b : Var × Term}
    (h : b ∈ Env.canon vars σ) : b.1 ∈ vars ∧ Env.lookup b.1 σ = some b.2 := by
  obtain ⟨v, hv, hb⟩ := List.mem_filterMap.mp h
  cases hlk : Env.lookup v σ with
  | none => rw [hlk] at hb; simp at hb
  | some t =>
    rw [hlk] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    exact ⟨hb ▸ hv, hb ▸ hlk⟩

theorem Env.dom_canon_subset {vars : List Var} {σ : Env} :
    Env.dom (Env.canon vars σ) ⊆ vars := fun _ hv =>
  (Env.mem_canon (Env.mem_dom_iff.mp hv).choose_spec).1

theorem Env.canon_cons_none {v : Var} {vs : List Var} {σ : Env}
    (h : Env.lookup v σ = none) : Env.canon (v :: vs) σ = Env.canon vs σ := by
  simp [canon, h]

theorem Env.canon_cons_some {v : Var} {vs : List Var} {σ : Env} {t : Term}
    (h : Env.lookup v σ = some t) : Env.canon (v :: vs) σ = (v, t) :: Env.canon vs σ := by
  simp [canon, h]

theorem Env.dom_canon {vars : List Var} {σ : Env}
    (h : ∀ v ∈ vars, (Env.lookup v σ).isSome) : Env.dom (Env.canon vars σ) = vars := by
  induction vars with
  | nil => rfl
  | cons v vs ih =>
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h v (by simp))
    rw [canon_cons_some ht, dom_cons, ih fun w hw => h w (by simp [hw])]

theorem Env.lookup_canon {vars : List Var} {σ : Env} (hnd : vars.Nodup) {v : Var}
    (hv : v ∈ vars) : Env.lookup v (Env.canon vars σ) = Env.lookup v σ := by
  induction vars with
  | nil => simp at hv
  | cons w vs ih =>
    rw [List.nodup_cons] at hnd
    cases hlk : Env.lookup w σ with
    | none =>
      rw [canon_cons_none hlk]
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [hlk]
        exact Env.lookup_eq_none_iff.mpr fun hc => hnd.1 (Env.dom_canon_subset hc)
      · exact ih hnd.2 hv
    | some t =>
      rw [canon_cons_some hlk, Env.lookup_cons]
      rcases List.mem_cons.mp hv with rfl | hv
      · simp [hlk]
      · rw [if_neg (fun hc : v = w => hnd.1 (hc ▸ hv)), ih hnd.2 hv]

/-- Canonicalizing a substitution whose domain is a duplicate-free permutation of `vars`
changes no lookup. This is what lets the enumerator emit one representative per
`Env.Agree` class where the spec admits the whole class. -/
theorem Env.agree_canon {vars : List Var} {σ : Env} (hnd : vars.Nodup)
    (hperm : (Env.dom σ).Perm vars) : Env.Agree σ (Env.canon vars σ) := by
  intro v
  by_cases hv : v ∈ vars
  · exact (Env.lookup_canon hnd hv).symm
  · rw [Env.lookup_eq_none_iff.mpr fun hc => hv (hperm.mem_iff.mp hc),
      Env.lookup_eq_none_iff.mpr fun hc => hv (Env.dom_canon_subset hc)]

@[simp] theorem Query.freeVars_nil {σ : Env} : Query.freeVars [] σ = [] := rfl

@[simp] theorem Query.freeVars_cons {p : Pattern} {ps : Query} {σ : Env} :
    Query.freeVars (p :: ps) σ = p.freeVars σ ∪ Query.freeVars ps σ := rfl

theorem Query.mem_freeVars {q : Query} {σ : Env} {v : Var} :
    v ∈ Query.freeVars q σ ↔ ∃ p ∈ q, v ∈ p.freeVars σ := by
  induction q with
  | nil => simp
  | cons p ps ih =>
    simp only [Query.freeVars_cons, List.mem_union_iff, List.mem_cons, ih]
    aesop

theorem Query.freeVars_nodup (q : Query) (σ : Env) : (Query.freeVars q σ).Nodup := by
  induction q with
  | nil => simp
  | cons p ps ih => exact List.Nodup.union _ ih

/-- A pattern's free variables are among the query's, so a substitution for the query
restricts to one for each pattern. -/
theorem Query.freeVars_subset {q : Query} {σ : Env} {p : Pattern} (hp : p ∈ q) :
    p.freeVars σ ⊆ Query.freeVars q σ := fun _ hv => Query.mem_freeVars.mpr ⟨p, hp, hv⟩

/-- Restricting a query substitution to one pattern gives a substitution with exactly that
pattern's free variables as its domain, and it agrees with the original there. These are
the two facts `patternHolds_iff` and `ValidSubst.of_agree` need. -/
theorem Env.dom_canon_of_subset {vars vars' : List Var} {σ : Env} (hsub : vars ⊆ vars')
    (hdom : Env.dom σ = vars') : Env.dom (Env.canon vars σ) = vars :=
  Env.dom_canon fun v hv =>
    Env.lookup_isSome_iff_mem_dom.mpr (by rw [hdom]; exact hsub hv)

namespace FDatabase
theorem WF.addTerm {d : FDatabase} (h : d.WF) (t : Term) : (d.addTerm t).WF := by
  rw [FDatabase.WF, toDatabase_addTerm]; exact Database.WF.addTerm h t

theorem WF.addEq {d : FDatabase} (h : d.WF) (a b : Term) : (d.addEq a b).WF := by
  rw [FDatabase.WF, toDatabase_addEq]; exact Database.WF.addEq h a b

theorem mem_closureF_addTerm {d : FDatabase} (hw : d.WF) {t a b : Term} :
    (a, b) ∈ (d.addTerm t).closureF ↔ Cong (d.toDatabase.addTerm t) a b := by
  rw [mem_closureF_iff_of_wf (hw.addTerm t), toDatabase_addTerm]

theorem mem_closureF_addTerm₂ {d : FDatabase} (hw : d.WF) {t₁ t₂ a b : Term} :
    (a, b) ∈ ((d.addTerm t₁).addTerm t₂).closureF
      ↔ Cong ((d.toDatabase.addTerm t₁).addTerm t₂) a b := by
  rw [mem_closureF_iff_of_wf ((hw.addTerm t₁).addTerm t₂), toDatabase_addTerm,
    toDatabase_addTerm]

/-- `congrTuple` decides pointwise congruence. What `patternHolds` needs for a tuple
destructure, which compares a row's key *and* value columns. -/
theorem congrTuple_iff {d : FDatabase} (hw : d.WF) {xs ys : List Term} :
    FDatabase.congrTuple d.closureF xs ys = true ↔ CongList d.toDatabase xs ys := by
  rw [FDatabase.congrTuple, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    CongList.forall₂, List.forall₂_iff_zip]
  constructor
  · rintro ⟨hlen, hall⟩
    exact ⟨hlen, fun {a b} hab =>
      (mem_closureF_iff_of_wf hw).mp (by simpa using hall (a, b) hab)⟩
  · rintro ⟨hlen, hall⟩
    exact ⟨hlen, fun q hq => by
      simpa using (mem_closureF_iff_of_wf hw).mpr (hall (a := q.1) (b := q.2) (by simpa using hq))⟩

end FDatabase
theorem patternHolds_iff {d : FDatabase} (hw : d.WF) {p : Pattern} {σ : Env}
    (hv : ValidEnv (p.freeVars d.env) d.toDatabase σ) :
    patternHolds d p σ = true ↔ ValidSubst d.toDatabase p σ := by
  cases p with
  | values vs f as =>
    cases hu : Expr.evalList vs (d.env ++ σ) with
    | none =>
      simp only [patternHolds, hu, Bool.false_eq_true, false_iff]
      intro h
      cases h with
      | values _ hu' _ _ _ _ =>
        rw [FDatabase.toDatabase_env, hu] at hu'
        simp at hu'
    | some us =>
      cases ht : Expr.evalList as (d.env ++ σ) with
      | none =>
        simp only [patternHolds, hu, ht, Bool.false_eq_true, false_iff]
        intro h
        cases h with
        | values _ _ ht' _ _ _ =>
          rw [FDatabase.toDatabase_env, ht] at ht'
          simp at ht'
      | some ts =>
        simp only [patternHolds, hu, ht, List.any_eq_true, Bool.and_eq_true,
          decide_eq_true_eq, FDatabase.congrTuple_iff hw]
        constructor
        · rintro ⟨r, hr, ⟨hfn, hkey⟩, hval⟩
          subst hfn
          exact .values hv hu ht hkey hval hr
        · intro h
          cases h with
          | values _ hu' ht' hkey hval hrow =>
            rw [FDatabase.toDatabase_env, hu] at hu'
            rw [FDatabase.toDatabase_env, ht] at ht'
            cases hu'
            cases ht'
            exact ⟨_, hrow, ⟨rfl, hkey⟩, hval⟩
  | expr e =>
    cases hev : e.eval (d.env ++ σ) with
    | none =>
      simp only [patternHolds, hev, Bool.false_eq_true, false_iff]
      intro h
      cases h with
      | expr _ _ he _ =>
        rw [FDatabase.toDatabase_env, hev] at he
        simp at he
    | some t =>
      simp only [patternHolds, hev, decide_eq_true_eq]
      constructor
      · rintro ⟨w, hwm, hcl⟩
        exact .expr hv hwm hev ((FDatabase.mem_closureF_addTerm hw).mp hcl)
      · intro h
        cases h with
        | expr _ hwm he hc =>
          rw [FDatabase.toDatabase_env, hev] at he
          cases he
          exact ⟨_, hwm, (FDatabase.mem_closureF_addTerm hw).mpr hc⟩
  | eq e₁ e₂ =>
    cases hev₁ : e₁.eval (d.env ++ σ) with
    | none =>
      simp only [patternHolds, hev₁, Bool.false_eq_true, false_iff]
      intro h
      cases h with
      | eq _ _ he₁ _ _ _ =>
        rw [FDatabase.toDatabase_env, hev₁] at he₁
        simp at he₁
    | some t₁ =>
      cases hev₂ : e₂.eval (d.env ++ σ) with
      | none =>
        simp only [patternHolds, hev₁, hev₂, Bool.false_eq_true, false_iff]
        intro h
        cases h with
        | eq _ _ _ he₂ _ _ =>
          rw [FDatabase.toDatabase_env, hev₂] at he₂
          simp at he₂
      | some t₂ =>
        simp only [patternHolds, hev₁, hev₂, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨heq, w, hwm, hcl⟩
          exact .eq hv hwm hev₁ hev₂ ((FDatabase.mem_closureF_addTerm₂ hw).mp hcl)
            ((FDatabase.mem_closureF_addTerm₂ hw).mp heq)
        · intro h
          cases h with
          | eq _ hwm he₁ he₂ hcw hceq =>
            rw [FDatabase.toDatabase_env, hev₁] at he₁
            rw [FDatabase.toDatabase_env, hev₂] at he₂
            cases he₁
            cases he₂
            exact ⟨(FDatabase.mem_closureF_addTerm₂ hw).mpr hceq,
              _, hwm, (FDatabase.mem_closureF_addTerm₂ hw).mpr hcw⟩

/-- Restricting a query substitution to one pattern gives a `valid-env` for that pattern.
This is the hypothesis `patternHolds_iff` needs, discharged from what `assignments`
guarantees. -/
theorem validEnv_canon {d : FDatabase} {q : Query} {σ : Env} {p : Pattern} (hp : p ∈ q)
    (hdom : Env.dom σ = Query.freeVars q d.env) (hval : ∀ b ∈ σ, b.2 ∈ d.terms) :
    ValidEnv (p.freeVars d.env) d.toDatabase (Env.canon (p.freeVars d.env) σ) := by
  constructor
  · rw [Env.dom_canon_of_subset (Query.freeVars_subset hp) hdom]
  · exact fun b hb => hval b (Env.mem_of_lookup (Env.mem_canon hb).2)

/-- The enumerator produces exactly the substitutions that assign the query's free
variables to terms the database holds and satisfy every pattern under restriction.

What is left between this and `ValidQuerySubst` is repackaging: the spec takes one
substitution per pattern and joins them with `Env.UnionAll`, where this restricts a single
substitution. `Env.agree_canon` is what makes the two interchangeable. -/
theorem mem_matchQuery_iff {d : FDatabase} (hw : d.WF) {q : Query} {σ : Env} :
    σ ∈ matchQuery d q ↔
      Env.dom σ = Query.freeVars q d.env ∧ (∀ b ∈ σ, b.2 ∈ d.terms) ∧
        ∀ p ∈ q, ValidSubst d.toDatabase p (Env.canon (p.freeVars d.env) σ) := by
  simp only [matchQuery, List.mem_filter, mem_assignments, List.all_eq_true]
  constructor
  · rintro ⟨⟨hdom, hval⟩, hall⟩
    exact ⟨hdom, hval, fun p hp =>
      (patternHolds_iff hw (validEnv_canon hp hdom hval)).mp (hall p hp)⟩
  · rintro ⟨hdom, hval, hall⟩
    exact ⟨⟨hdom, hval⟩, fun p hp =>
      (patternHolds_iff hw (validEnv_canon hp hdom hval)).mpr (hall p hp)⟩

/-- A restricted substitution refines the one it came from. -/
theorem Env.refines_canon {vars : List Var} {σ : Env} : Env.Refines (Env.canon vars σ) σ :=
  fun _ hb => (Env.mem_canon hb).2

/-- Every substitution the enumerator produces is, up to `Env.Agree`, one the spec admits.

The two differ in shape only: the spec joins one substitution per pattern with
`Env.UnionAll`, and the enumerator restricts a single one. `Env.exists_unionAll` builds the
join out of the restrictions, which are pairwise compatible because they all refine `σ`. -/
theorem validQuerySubst_of_mem_matchQuery {d : FDatabase} (hw : d.WF) {q : Query} {σ : Env}
    (h : σ ∈ matchQuery d q) :
    ∃ τ, ValidQuerySubst d.toDatabase q τ ∧ Env.Agree τ σ := by
  obtain ⟨hdom, hval, hall⟩ := (mem_matchQuery_iff hw).mp h
  obtain ⟨τ, hu, hr⟩ := Env.exists_unionAll (σ := σ)
    (q.map fun p => Env.canon (p.freeVars d.env) σ) (by
      intro ρ hρ
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hρ
      exact Env.refines_canon)
  refine ⟨τ, ⟨_, List.forall₂_map_self hall, hu⟩, Env.agree_of_refines hr ?_⟩
  -- `σ` binds only the query's free variables, and each is bound by some restriction
  intro v hv
  rw [hdom] at hv
  obtain ⟨p, hp, hvp⟩ := Query.mem_freeVars.mp hv
  refine hu.mem_dom_iff.mpr ⟨Env.canon (p.freeVars d.env) σ, List.mem_map_of_mem hp, ?_⟩
  rw [Env.dom_canon_of_subset (Query.freeVars_subset hp) hdom]
  exact hvp

/-- Restricting twice is restricting once. -/
theorem Env.canon_canon {vars vars' : List Var} {σ : Env} (hsub : vars ⊆ vars')
    (hnd : vars'.Nodup) : Env.canon vars (Env.canon vars' σ) = Env.canon vars σ := by
  induction vars with
  | nil => rfl
  | cons v vs ih =>
    have hl : Env.lookup v (Env.canon vars' σ) = Env.lookup v σ :=
      Env.lookup_canon hnd (hsub (by simp))
    have hs : vs ⊆ vars' := fun w hw => hsub (by simp [hw])
    cases hlk : Env.lookup v σ with
    | none =>
      rw [Env.canon_cons_none (by rw [hl, hlk]), Env.canon_cons_none hlk, ih hs]
    | some t =>
      rw [Env.canon_cons_some (by rw [hl, hlk]), Env.canon_cons_some hlk, ih hs]

/-- Conversely, every substitution the spec admits has a representative in the enumerator's
output: restricting it to the query's free variables puts it in the canonical form
`assignments` produces, and no lookup can tell the two apart. -/
theorem mem_matchQuery_of_validQuerySubst {d : FDatabase} (hw : d.WF) {q : Query} {τ : Env}
    (h : ValidQuerySubst d.toDatabase q τ) :
    Env.canon (Query.freeVars q d.env) τ ∈ matchQuery d q ∧
      Env.Agree τ (Env.canon (Query.freeVars q d.env) τ) := by
  have hmd : ∀ v, v ∈ Env.dom τ ↔ v ∈ Query.freeVars q d.env := fun v => by
    rw [h.mem_dom_iff, Query.mem_freeVars, FDatabase.toDatabase_env]
  have hbound : ∀ v ∈ Query.freeVars q d.env, (Env.lookup v τ).isSome := fun v hv =>
    Env.lookup_isSome_iff_mem_dom.mpr ((hmd v).mpr hv)
  have hdom : Env.dom (Env.canon (Query.freeVars q d.env) τ) = Query.freeVars q d.env :=
    Env.dom_canon hbound
  have hag : Env.Agree τ (Env.canon (Query.freeVars q d.env) τ) :=
    (Env.agree_of_refines Env.refines_canon (fun v hv => by
      rw [hdom]; exact (hmd v).mp hv)).symm
  refine ⟨(mem_matchQuery_iff hw).mpr ⟨hdom, ?_, ?_⟩, hag⟩
  · exact fun b hb => h.mem_terms b (Env.mem_of_lookup (Env.mem_canon hb).2)
  · intro p hp
    obtain ⟨σs, hall, hu⟩ := h
    obtain ⟨σp, hσp, hvs⟩ := hall.flip.exists_left hp
    have hpsub : p.freeVars d.env ⊆ Query.freeVars q d.env := Query.freeVars_subset hp
    have hpdom : Env.dom (Env.canon (p.freeVars d.env) τ) = p.freeVars d.env :=
      Env.dom_canon fun v hv => hbound v (hpsub hv)
    have hsc : ∀ ρ ∈ σs, Env.Refines ρ ρ := by
      intro ρ hρ
      obtain ⟨p', -, hvs'⟩ := hall.exists_left hρ
      exact Env.Refines.self_of_nodup (hvs'.validEnv.1.symm.nodup (p'.freeVars_nodup _))
    have hrp : Env.Refines σp τ := (hu.refines_of_mem hsc).1 σp hσp
    rw [Env.canon_canon hpsub (Query.freeVars_nodup q d.env)]
    refine hvs.of_agree (fun v => ?_) hpdom
    by_cases hv : v ∈ p.freeVars d.env
    · rw [Env.lookup_canon (p.freeVars_nodup _) hv]
      cases hlk : Env.lookup v σp with
      | none =>
        rw [Env.lookup_eq_none_iff] at hlk
        exact absurd (hvs.validEnv.1.mem_iff.mpr hv) hlk
      | some t => exact (hrp (v, t) (Env.mem_of_lookup hlk)).symm
    · rw [Env.lookup_eq_none_iff.mpr fun hc => hv (hvs.validEnv.1.mem_iff.mp hc),
        Env.lookup_eq_none_iff.mpr fun hc => hv (hpdom ▸ hc)]

/-! ### Refinement: actions

The interpreter's actions denote the spec's. These are the pieces the `runRules` refinement
will be threaded through; what remains is the e-matching enumerator and the fold. -/
theorem execAction_toDatabase {d : FDatabase} {a : Action} :
    (execAction d a).map FDatabase.toDatabase = evalAction d.toDatabase a := by
  cases a with
  | expr e =>
    cases hv : e.eval d.env with
    | none => simp [execAction, evalAction, hv]
    | some t => simp [execAction, evalAction, hv]
  | letBind v e =>
    cases hv : e.eval d.env with
    | none => simp [execAction, evalAction, hv]
    | some t => simp [execAction, evalAction, hv]
  | union e₁ e₂ =>
    cases hv₁ : e₁.eval d.env with
    | none => simp [execAction, evalAction, hv₁]
    | some t₁ =>
      cases hv₂ : e₂.eval d.env with
      | none => simp [execAction, evalAction, hv₁, hv₂]
      | some t₂ => simp [execAction, evalAction, hv₁, hv₂]
  | set f args out =>
    cases hv₁ : Expr.evalList args d.env with
    | none => simp [execAction, evalAction, hv₁]
    | some as =>
      cases hv₂ : Expr.evalList out d.env with
      | none => simp [execAction, evalAction, hv₁, hv₂]
      | some vs => simp [execAction, evalAction, hv₁, hv₂]

theorem execActions_toDatabase {d : FDatabase} {as : List Action} :
    (execActions d as).map FDatabase.toDatabase = evalActions d.toDatabase as := by
  induction as generalizing d with
  | nil => rfl
  | cons a as ih =>
    cases hv : execAction d a with
    | none =>
      have : evalAction d.toDatabase a = none := by rw [← execAction_toDatabase, hv]; rfl
      simp [execActions, hv, this]
    | some d' =>
      have : evalAction d.toDatabase a = some d'.toDatabase := by
        rw [← execAction_toDatabase, hv]; rfl
      simp [execActions, hv, this, ih]

theorem execLocalActions_toDatabase {d : FDatabase} {as : List Action} {σ : Env} :
    (execLocalActions d as σ).map FDatabase.toDatabase
      = evalLocalActions d.toDatabase as σ := by
  rw [execLocalActions, Option.map_map,
    show FDatabase.toDatabase ∘ (fun d' : FDatabase =>
        ({ d' with env := d.env, rules := d.rules } : FDatabase))
      = (fun db' : Database =>
          ({ db' with env := d.toDatabase.env, rules := d.toDatabase.rules } : Database))
        ∘ FDatabase.toDatabase from by funext d'; rfl,
    ← Option.map_map, execActions_toDatabase]
  rfl

section Fold
variable {α : Type}

theorem mem_terms_foldl {g : FDatabase → α → FDatabase} {C : α → Term → Prop}
    (hg : ∀ acc a t, t ∈ (g acc a).terms ↔ t ∈ acc.terms ∨ C a t)
    (l : List α) (init : FDatabase) (t : Term) :
    t ∈ (l.foldl g init).terms ↔ t ∈ init.terms ∨ ∃ a ∈ l, C a t := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, hg]; aesop

theorem mem_eqs_foldl {g : FDatabase → α → FDatabase} {C : α → Term × Term → Prop}
    (hg : ∀ acc a p, p ∈ (g acc a).eqs ↔ p ∈ acc.eqs ∨ C a p)
    (l : List α) (init : FDatabase) (p : Term × Term) :
    p ∈ (l.foldl g init).eqs ↔ p ∈ init.eqs ∨ ∃ a ∈ l, C a p := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, hg]; aesop

theorem mem_rows_foldl {g : FDatabase → α → FDatabase} {C : α → Row → Prop}
    (hg : ∀ acc a q, q ∈ (g acc a).rows ↔ q ∈ acc.rows ∨ C a q)
    (l : List α) (init : FDatabase) (r : Row) :
    r ∈ (l.foldl g init).rows ↔ r ∈ init.rows ∨ ∃ a ∈ l, C a r := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih, hg]; aesop

theorem sig_foldl {g : FDatabase → α → FDatabase} (hg : ∀ acc a, (g acc a).sig = acc.sig)
    (l : List α) (init : FDatabase) : (l.foldl g init).sig = init.sig := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih, hg]

theorem env_foldl {g : FDatabase → α → FDatabase} (hg : ∀ acc a, (g acc a).env = acc.env)
    (l : List α) (init : FDatabase) : (l.foldl g init).env = init.env := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih, hg]

theorem rules_foldl {g : FDatabase → α → FDatabase} (hg : ∀ acc a, (g acc a).rules = acc.rules)
    (l : List α) (init : FDatabase) : (l.foldl g init).rules = init.rules := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih, hg]

end Fold
theorem mem_terms_fireInto {d : FDatabase} {r : Rule} {acc : FDatabase} {σ : Env} {t : Term} :
    t ∈ (fireInto d r acc σ).terms ↔
      t ∈ acc.terms ∨ ∃ d', Fired d r σ d' ∧ t ∈ d'.terms := by
  unfold fireInto Fired
  cases execLocalActions d r.actions σ <;> simp

theorem mem_eqs_fireInto {d : FDatabase} {r : Rule} {acc : FDatabase} {σ : Env}
    {p : Term × Term} :
    p ∈ (fireInto d r acc σ).eqs ↔ p ∈ acc.eqs ∨ ∃ d', Fired d r σ d' ∧ p ∈ d'.eqs := by
  unfold fireInto Fired
  cases execLocalActions d r.actions σ <;> simp

theorem mem_rows_fireInto {d : FDatabase} {r : Rule} {acc : FDatabase} {σ : Env}
    {q : Row} :
    q ∈ (fireInto d r acc σ).rows ↔ q ∈ acc.rows ∨ ∃ d', Fired d r σ d' ∧ q ∈ d'.rows := by
  unfold fireInto Fired
  cases execLocalActions d r.actions σ <;> simp

theorem sig_fireInto {d : FDatabase} {r : Rule} {acc : FDatabase} {σ : Env} :
    (fireInto d r acc σ).sig = acc.sig := by
  unfold fireInto; cases execLocalActions d r.actions σ <;> rfl

theorem env_fireInto {d : FDatabase} {r : Rule} {acc : FDatabase} {σ : Env} :
    (fireInto d r acc σ).env = acc.env := by
  unfold fireInto; cases execLocalActions d r.actions σ <;> rfl

theorem rules_fireInto {d : FDatabase} {r : Rule} {acc : FDatabase} {σ : Env} :
    (fireInto d r acc σ).rules = acc.rules := by
  unfold fireInto; cases execLocalActions d r.actions σ <;> rfl

theorem mem_terms_fireRule {d acc : FDatabase} {r : Rule} {t : Term} :
    t ∈ (fireRule d acc r).terms ↔
      t ∈ acc.terms ∨ ∃ σ ∈ matchQuery d r.query, ∃ d', Fired d r σ d' ∧ t ∈ d'.terms :=
  mem_terms_foldl (g := fireInto d r) (C := fun σ t => ∃ d', Fired d r σ d' ∧ t ∈ d'.terms)
    (fun _ _ _ => mem_terms_fireInto) _ _ _

theorem mem_eqs_fireRule {d acc : FDatabase} {r : Rule} {p : Term × Term} :
    p ∈ (fireRule d acc r).eqs ↔
      p ∈ acc.eqs ∨ ∃ σ ∈ matchQuery d r.query, ∃ d', Fired d r σ d' ∧ p ∈ d'.eqs :=
  mem_eqs_foldl (g := fireInto d r) (C := fun σ p => ∃ d', Fired d r σ d' ∧ p ∈ d'.eqs)
    (fun _ _ _ => mem_eqs_fireInto) _ _ _

theorem mem_rows_fireRule {d acc : FDatabase} {r : Rule} {q : Row} :
    q ∈ (fireRule d acc r).rows ↔
      q ∈ acc.rows ∨ ∃ σ ∈ matchQuery d r.query, ∃ d', Fired d r σ d' ∧ q ∈ d'.rows :=
  mem_rows_foldl (g := fireInto d r) (C := fun σ q => ∃ d', Fired d r σ d' ∧ q ∈ d'.rows)
    (fun _ _ _ => mem_rows_fireInto) _ _ _

theorem sig_fireRule {d acc : FDatabase} {r : Rule} : (fireRule d acc r).sig = acc.sig :=
  sig_foldl (g := fireInto d r) (fun _ _ => sig_fireInto) _ _

theorem env_fireRule {d acc : FDatabase} {r : Rule} : (fireRule d acc r).env = acc.env :=
  env_foldl (g := fireInto d r) (fun _ _ => env_fireInto) _ _

theorem rules_fireRule {d acc : FDatabase} {r : Rule} :
    (fireRule d acc r).rules = acc.rules :=
  rules_foldl (g := fireInto d r) (fun _ _ => rules_fireInto) _ _

theorem mem_terms_execRunRules {d : FDatabase} {t : Term} :
    t ∈ (execRunRules d).terms ↔ t ∈ d.terms ∨
      ∃ r ∈ d.rules, ∃ σ ∈ matchQuery d r.query, ∃ d', Fired d r σ d' ∧ t ∈ d'.terms :=
  mem_terms_foldl (g := fireRule d)
    (C := fun r t => ∃ σ ∈ matchQuery d r.query, ∃ d', Fired d r σ d' ∧ t ∈ d'.terms)
    (fun _ _ _ => mem_terms_fireRule) _ _ _

theorem mem_eqs_execRunRules {d : FDatabase} {p : Term × Term} :
    p ∈ (execRunRules d).eqs ↔ p ∈ d.eqs ∨
      ∃ r ∈ d.rules, ∃ σ ∈ matchQuery d r.query, ∃ d', Fired d r σ d' ∧ p ∈ d'.eqs :=
  mem_eqs_foldl (g := fireRule d)
    (C := fun r p => ∃ σ ∈ matchQuery d r.query, ∃ d', Fired d r σ d' ∧ p ∈ d'.eqs)
    (fun _ _ _ => mem_eqs_fireRule) _ _ _

theorem mem_rows_execRunRules {d : FDatabase} {q : Row} :
    q ∈ (execRunRules d).rows ↔ q ∈ d.rows ∨
      ∃ r ∈ d.rules, ∃ σ ∈ matchQuery d r.query, ∃ d', Fired d r σ d' ∧ q ∈ d'.rows :=
  mem_rows_foldl (g := fireRule d)
    (C := fun r q => ∃ σ ∈ matchQuery d r.query, ∃ d', Fired d r σ d' ∧ q ∈ d'.rows)
    (fun _ _ _ => mem_rows_fireRule) _ _ _

@[simp] theorem sig_execRunRules {d : FDatabase} : (execRunRules d).sig = d.sig :=
  sig_foldl (g := fireRule d) (fun _ _ => sig_fireRule) _ _

@[simp] theorem env_execRunRules {d : FDatabase} : (execRunRules d).env = d.env :=
  env_foldl (g := fireRule d) (fun _ _ => env_fireRule) _ _

@[simp] theorem rules_execRunRules {d : FDatabase} : (execRunRules d).rules = d.rules :=
  rules_foldl (g := fireRule d) (fun _ _ => rules_fireRule) _ _

/-- A firing's result denotes the spec's. -/
theorem fired_toDatabase {d : FDatabase} {r : Rule} {σ : Env} {d' : FDatabase}
    (h : Fired d r σ d') : evalLocalActions d.toDatabase r.actions σ = some d'.toDatabase := by
  rw [← execLocalActions_toDatabase, h]; rfl

/-- One round of the interpreter denotes one round of the spec.

The two enumerate different substitutions — the interpreter its canonical ones, the spec
every `Env.UnionAll` decomposition — and `evalLocalActions_agree` is what makes them
contribute the same databases. -/
theorem execRunRules_toDatabase {d : FDatabase} (hw : d.WF) :
    (execRunRules d).toDatabase = runRules d.toDatabase := by
  refine Database.ext ?_ ?_ ?_ ?_ ?_ ?_
  · simp [FDatabase.toDatabase, runRules, Database.sUnion]
  · ext t
    simp only [FDatabase.toDatabase, Set.mem_setOf_eq, mem_terms_execRunRules, runRules,
      Database.sUnion_terms, Set.mem_union, Set.mem_iUnion₂, exists_prop]
    constructor
    · rintro (ht | ⟨r, hr, σ, hσ, d', hf, ht⟩)
      · exact Or.inl ht
      · obtain ⟨τ, hτ, hag⟩ := validQuerySubst_of_mem_matchQuery hw hσ
        refine Or.inr ⟨d'.toDatabase, ⟨r, hr, τ, hτ, ?_⟩, ht⟩
        rw [evalLocalActions_agree r.actions hag]
        exact fired_toDatabase hf
    · rintro (ht | ⟨e, ⟨r, hr, τ, hτ, hev⟩, ht⟩)
      · exact Or.inl ht
      · obtain ⟨hmem, hag⟩ := mem_matchQuery_of_validQuerySubst hw hτ
        have hev' : evalLocalActions d.toDatabase r.actions
            (Env.canon (Query.freeVars r.query d.env) τ) = some e := by
          rw [← evalLocalActions_agree r.actions hag]; exact hev
        have hmap := execLocalActions_toDatabase (d := d) (as := r.actions)
          (σ := Env.canon (Query.freeVars r.query d.env) τ)
        rw [hev'] at hmap
        obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hmap
        exact Or.inr ⟨r, hr, _, hmem, d', hd', ht⟩
  · ext q
    simp only [FDatabase.toDatabase, Set.mem_setOf_eq, mem_rows_execRunRules, runRules,
      Database.sUnion_rows, Set.mem_union, Set.mem_iUnion₂, exists_prop]
    constructor
    · rintro (hq | ⟨r, hr, σ, hσ, d', hf, hq⟩)
      · exact Or.inl hq
      · obtain ⟨τ, hτ, hag⟩ := validQuerySubst_of_mem_matchQuery hw hσ
        refine Or.inr ⟨d'.toDatabase, ⟨r, hr, τ, hτ, ?_⟩, hq⟩
        rw [evalLocalActions_agree r.actions hag]
        exact fired_toDatabase hf
    · rintro (hq | ⟨e, ⟨r, hr, τ, hτ, hev⟩, hq⟩)
      · exact Or.inl hq
      · obtain ⟨hmem, hag⟩ := mem_matchQuery_of_validQuerySubst hw hτ
        have hev' : evalLocalActions d.toDatabase r.actions
            (Env.canon (Query.freeVars r.query d.env) τ) = some e := by
          rw [← evalLocalActions_agree r.actions hag]; exact hev
        have hmap := execLocalActions_toDatabase (d := d) (as := r.actions)
          (σ := Env.canon (Query.freeVars r.query d.env) τ)
        rw [hev'] at hmap
        obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hmap
        exact Or.inr ⟨r, hr, _, hmem, d', hd', hq⟩
  · ext p
    simp only [FDatabase.toDatabase, Set.mem_setOf_eq, mem_eqs_execRunRules, runRules,
      Database.sUnion_eqs, Set.mem_union, Set.mem_iUnion₂, exists_prop]
    constructor
    · rintro (hp | ⟨r, hr, σ, hσ, d', hf, hp⟩)
      · exact Or.inl hp
      · obtain ⟨τ, hτ, hag⟩ := validQuerySubst_of_mem_matchQuery hw hσ
        refine Or.inr ⟨d'.toDatabase, ⟨r, hr, τ, hτ, ?_⟩, hp⟩
        rw [evalLocalActions_agree r.actions hag]
        exact fired_toDatabase hf
    · rintro (hp | ⟨e, ⟨r, hr, τ, hτ, hev⟩, hp⟩)
      · exact Or.inl hp
      · obtain ⟨hmem, hag⟩ := mem_matchQuery_of_validQuerySubst hw hτ
        have hev' : evalLocalActions d.toDatabase r.actions
            (Env.canon (Query.freeVars r.query d.env) τ) = some e := by
          rw [← evalLocalActions_agree r.actions hag]; exact hev
        have hmap := execLocalActions_toDatabase (d := d) (as := r.actions)
          (σ := Env.canon (Query.freeVars r.query d.env) τ)
        rw [hev'] at hmap
        obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hmap
        exact Or.inr ⟨r, hr, _, hmem, d', hd', hp⟩
  · simp [FDatabase.toDatabase, runRules, Database.sUnion]
  · simp [FDatabase.toDatabase, runRules, Database.sUnion]

theorem FDatabase.empty_wf : FDatabase.empty.WF := by
  rw [FDatabase.WF, toDatabase_empty]; exact Database.WF.empty

theorem execCmd_toDatabase {d : FDatabase} (hw : d.WF) {c : Cmd} :
    (execCmd d c).map FDatabase.toDatabase = stepCmd d.toDatabase c := by
  cases c with
  | action a => exact execAction_toDatabase
  | rule r =>
    simp only [execCmd, stepCmd, Option.map_some, Option.some.injEq]
    refine Database.ext rfl rfl rfl rfl rfl ?_
    ext r'
    simp [FDatabase.toDatabase]
  | run => simp only [execCmd, stepCmd, Option.map_some, execRunRules_toDatabase hw]
  | decl f dc => simp [execCmd, stepCmd, FDatabase.toDatabase]

/-- Well-formedness of the interpreter's state comes free from the refinement: it is the
spec's, and `stepCmd_wf` preserves that. -/
theorem execCmd_wf {d d' : FDatabase} (hw : d.WF) {c : Cmd} (h : execCmd d c = some d') :
    d'.WF := by
  have hc := execCmd_toDatabase hw (c := c)
  rw [h, Option.map_some] at hc
  exact stepCmd_wf hw hc.symm

theorem execProgram_toDatabase {d : FDatabase} (hw : d.WF) {p : Program} :
    (execProgram d p).map FDatabase.toDatabase = runProgram d.toDatabase p := by
  induction p generalizing d with
  | nil => rfl
  | cons c cs ih =>
    have hc := execCmd_toDatabase hw (c := c)
    cases h : execCmd d c with
    | none =>
      rw [h, Option.map_none] at hc
      simp [execProgram, h, ← hc]
    | some d' =>
      rw [h, Option.map_some] at hc
      simp only [execProgram, h, Option.bind_some, runProgram_cons, ← hc, Option.bind_some]
      exact ih (execCmd_wf hw h)

/-- **The refinement theorem**: running a program with the interpreter denotes running it
with the semantics.

Everything the interpreter is tested on — the `#guard` cases in `Examples.lean` and the
differential test against egglog — therefore says something about the specification. -/
theorem exec_toDatabase {p : Program} : (exec p).map FDatabase.toDatabase = run p := by
  rw [exec, run, ← FDatabase.toDatabase_empty]
  exact execProgram_toDatabase FDatabase.empty_wf

end Egglog
