import EgglogSemantics.Impl.Interp
import EgglogSemantics.Proofs.Closure
import EgglogSemantics.Proofs.Scope

/-!
# The interpreter refines the specification

`Impl/Interp.lean`'s `exec` computes what `Spec/Step.lean`'s `ProgramStep` relates, on the
constructor fragment.

Two conditions run through the whole file. `FDatabase.EqsInTerms` is what makes
`toDatabase` a homomorphism: the denotation keeps an equation only where the term list
holds both of its sides, so a list carrying an equation between terms it does not hold
denotes something `addTerm` cannot track. `Signature.AllConstructors` is what makes
`matchQuery`'s enumeration from `FDatabase.valueTerms` agree with `ValidEnv`'s from
`terms`, what puts the row atom on `patternHolds`' entry-term branch, and what makes the
merge phase empty.
-/

namespace Egglog
/-! ### The closure computes `Cong`

`FDatabase.toDatabase` writes the term list into the diagonal of `eqs`, and `closureF`'s
seed is `eqs` alone. The two still agree, because `stepAdds` derives the diagonal of the
candidate universe itself: the seed does not have to carry it. -/

/-- `closure` decides `Cong` when the seed carries the database's equations **up to
reflexive pairs**, which is the slack `FDatabase.toDatabase`'s diagonal introduces. -/
theorem mem_closure_iff_of_diag {db : Database} {terms : Finset Term}
    {rel : Finset (Term × Term)} (hterms : db.terms = ↑terms) (h : rel ⊆ candidates terms)
    (hsub : ∀ p ∈ rel, p ∈ db.eqs) (hsup : ∀ p ∈ db.eqs, p.1 = p.2 ∨ p ∈ rel)
    {a b : Term} : (a, b) ∈ closure terms rel h ↔ Cong db a b := by
  have hdiag : ∀ t ∈ terms, (t, t) ∈ closure terms rel h := by
    intro t ht
    rw [← closure_fixpoint h]
    refine mem_congStep.mpr (Or.inr ⟨mem_candidates.mpr ⟨ht, ht⟩, ?_⟩)
    simp only [stepAdds, Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl (Or.inl (Or.inl trivial))
  refine ⟨fun hp =>
    closure_sound hterms rel h (fun p hp' => Cong.assert (hsub p hp')) (a, b) hp, fun hc => ?_⟩
  refine hc.le (R := fun x y => (x, y) ∈ closure terms rel h) ?_ ?_ ?_ ?_
  · intro x y hxy
    rcases hsup (x, y) hxy with heq | hmem
    · have hx : x ∈ db.terms := (Cong.assert hxy).mem_left
      have hxy' : x = y := heq
      rw [hterms] at hx
      exact hxy' ▸ hdiag x hx
    · exact subset_closure h hmem
  · intro x y hxy
    have hcand := mem_candidates.mp (closure_subset h hxy)
    rw [← closure_fixpoint h]
    refine mem_congStep.mpr (Or.inr ⟨mem_candidates.mpr ⟨hcand.2, hcand.1⟩, ?_⟩)
    simp only [stepAdds, Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl (Or.inl (Or.inr hxy))
  · intro x y z hxy hyz
    have hx := mem_candidates.mp (closure_subset h hxy)
    have hz := mem_candidates.mp (closure_subset h hyz)
    rw [← closure_fixpoint h]
    refine mem_congStep.mpr (Or.inr ⟨mem_candidates.mpr ⟨hx.1, hz.2⟩, ?_⟩)
    simp only [stepAdds, Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl (Or.inr ⟨y, hx.2, hxy, hyz⟩)
  · intro f as bs ha hb hz
    rw [← closure_fixpoint h]
    refine mem_congStep.mpr (Or.inr ⟨mem_candidates.mpr ?_, ?_⟩)
    · rw [hterms] at ha hb; exact ⟨ha, hb⟩
    · simp only [stepAdds, Bool.or_eq_true]
      exact Or.inr (congrPair_app_iff.mpr ⟨rfl, hz⟩)

namespace FDatabase
/-! ### What the denotation holds -/
attribute [simp] toDatabase_terms

@[simp] theorem mem_toDatabase_terms {d : FDatabase} {t : Term} :
    t ∈ d.toDatabase.terms ↔ t ∈ d.terms := by rw [toDatabase_terms]; exact Iff.rfl

/-- The denotation's equations: the diagonal of the term list, plus the asserted list
restricted to it. -/
theorem mem_toDatabase_eqs {d : FDatabase} {p : Term × Term} :
    p ∈ d.toDatabase.eqs ↔
      (p.1 = p.2 ∧ p.1 ∈ d.terms) ∨ (p ∈ d.eqs ∧ p.1 ∈ d.terms ∧ p.2 ∈ d.terms) := Iff.rfl

/-- **`EqsInTerms` is exactly what makes the restriction invisible.** Every lemma below
that pushes `toDatabase` through a writer is this fact plus set algebra. -/
theorem mem_toDatabase_eqs_of_eqsInTerms {d : FDatabase} (he : d.EqsInTerms)
    {p : Term × Term} :
    p ∈ d.toDatabase.eqs ↔ (p.1 = p.2 ∧ p.1 ∈ d.terms) ∨ p ∈ d.eqs := by
  rw [mem_toDatabase_eqs]
  exact or_congr_right ⟨fun h => h.1, fun h => ⟨h, (he p h).1, (he p h).2⟩⟩

@[simp] theorem toDatabase_env {d : FDatabase} : d.toDatabase.env = d.env := rfl

@[simp] theorem toDatabase_sig {d : FDatabase} : d.toDatabase.sig = d.sig := rfl

@[simp] theorem toDatabase_rules {d : FDatabase} :
    d.toDatabase.rules = {r | r ∈ d.rules} := rfl

@[simp] theorem toDatabase_empty : empty.toDatabase = Database.empty := by
  refine Database.ext rfl ?_ rfl ?_
  · ext p; simp [empty, toDatabase, Database.empty]
  · ext r; simp [empty, toDatabase, Database.empty]

@[simp] theorem toDatabase_setEnv {d : FDatabase} {σ : Env} :
    ({ d with env := σ } : FDatabase).toDatabase = { d.toDatabase with env := σ } := rfl

@[simp] theorem toDatabase_restore {d d' : FDatabase} :
    ({ d' with env := d.env, rules := d.rules } : FDatabase).toDatabase
      = { d'.toDatabase with env := d.toDatabase.env, rules := d.toDatabase.rules } := rfl

theorem toDatabase_consRule {d : FDatabase} {r : Rule} :
    ({ d with rules := r :: d.rules } : FDatabase).toDatabase
      = { d.toDatabase with rules := insert r d.toDatabase.rules } := by
  refine Database.ext rfl rfl rfl ?_
  ext r'
  simp [FDatabase.toDatabase]

/-! ### `EqsInTerms` is preserved by the field updates the interpreter performs -/
theorem EqsInTerms.setEnv {d : FDatabase} (he : d.EqsInTerms) (σ : Env) :
    ({ d with env := σ } : FDatabase).EqsInTerms := he

theorem EqsInTerms.restore {d d' : FDatabase} (he : d'.EqsInTerms) :
    ({ d' with env := d.env, rules := d.rules } : FDatabase).EqsInTerms := he

theorem EqsInTerms.consRule {d : FDatabase} (he : d.EqsInTerms) (r : Rule) :
    ({ d with rules := r :: d.rules } : FDatabase).EqsInTerms := he

theorem EqsInTerms.setSig {d : FDatabase} (he : d.EqsInTerms) (sig : Signature) :
    ({ d with sig := sig } : FDatabase).EqsInTerms := he

theorem EqsInTerms.addTerms {d : FDatabase} (he : d.EqsInTerms) :
    ∀ ts : List Term, (d.addTerms ts).EqsInTerms := by
  intro ts
  induction ts generalizing d with
  | nil => exact he
  | cons t ts ih => exact ih (he.addTerm t)

/-! ### The writers commute with the denotation -/
theorem toDatabase_addTerm {d : FDatabase} (he : d.EqsInTerms) {t : Term} :
    (d.addTerm t).toDatabase = d.toDatabase.addTerm t := by
  refine Database.ext rfl ?_ rfl rfl
  ext p
  obtain ⟨p₁, p₂⟩ := p
  simp only [FDatabase.addTerm, toDatabase, Database.addTerm, Set.mem_union, Set.mem_setOf_eq,
    List.mem_dedup, List.mem_append, Term.mem_subtermList, Term.mem_subterms]
  constructor
  · rintro (⟨heq, hs | hs⟩ | ⟨hp, -, -⟩)
    · exact Or.inr ⟨p₁, hs, by rw [heq]⟩
    · exact Or.inl (Or.inl ⟨heq, hs⟩)
    · exact Or.inl (Or.inr ⟨hp, (he _ hp).1, (he _ hp).2⟩)
  · rintro ((⟨heq, hs⟩ | ⟨hp, h₁, h₂⟩) | ⟨s, hs, heq⟩)
    · exact Or.inl ⟨heq, Or.inr hs⟩
    · exact Or.inr ⟨hp, Or.inr h₁, Or.inr h₂⟩
    · rw [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact Or.inl ⟨rfl, Or.inl hs⟩

theorem toDatabase_addTerms {d : FDatabase} (he : d.EqsInTerms) {ts : List Term} :
    (d.addTerms ts).toDatabase = d.toDatabase.addTerms ts := by
  induction ts generalizing d with
  | nil => rfl
  | cons t ts ih =>
    rw [show d.addTerms (t :: ts) = (d.addTerm t).addTerms ts from rfl,
      show Database.addTerms (t :: ts) d.toDatabase
        = (d.toDatabase.addTerm t).addTerms ts from rfl,
      ih (he.addTerm t), toDatabase_addTerm he]

/-- Asserting a pair between terms the list already holds. The `EqsInTerms` condition is
not needed: the pair's own restriction is discharged by the two memberships. -/
theorem toDatabase_consEq {d : FDatabase} {a b : Term} (ha : a ∈ d.terms) (hb : b ∈ d.terms) :
    ({ d with eqs := ((a, b) :: d.eqs).dedup } : FDatabase).toDatabase
      = { d.toDatabase with eqs := insert (a, b) d.toDatabase.eqs } := by
  refine Database.ext rfl ?_ rfl rfl
  ext p
  simp only [toDatabase, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, List.mem_dedup,
    List.mem_cons]
  constructor
  · rintro (⟨heq, hm⟩ | ⟨rfl | hp, h₁, h₂⟩)
    · exact Or.inr (Or.inl ⟨heq, hm⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨hp, h₁, h₂⟩)
  · rintro (rfl | (⟨heq, hm⟩ | ⟨hp, h₁, h₂⟩))
    · exact Or.inr ⟨Or.inl rfl, ha, hb⟩
    · exact Or.inl ⟨heq, hm⟩
    · exact Or.inr ⟨Or.inr hp, h₁, h₂⟩

theorem toDatabase_addEq {d : FDatabase} (he : d.EqsInTerms) {a b : Term} :
    (d.addEq a b).toDatabase = d.toDatabase.addEq a b := by
  have ha : a ∈ ((d.addTerm a).addTerm b).terms := by
    simp only [FDatabase.addTerm, List.mem_dedup, List.mem_append, Term.mem_subtermList]
    exact Or.inr (Or.inl (Term.self_mem_subterms a))
  have hb : b ∈ ((d.addTerm a).addTerm b).terms := by
    simp only [FDatabase.addTerm, List.mem_dedup, List.mem_append, Term.mem_subtermList]
    exact Or.inl (Term.self_mem_subterms b)
  rw [show d.addEq a b
      = ({ (d.addTerm a).addTerm b with
            eqs := ((a, b) :: ((d.addTerm a).addTerm b).eqs).dedup } : FDatabase) from rfl,
    toDatabase_consEq ha hb, toDatabase_addTerm (he.addTerm a), toDatabase_addTerm he]
  rfl

/-- `addRow` records the entry term, which is all `evalAction`'s `set` case does; the
index row is not part of the denotation. -/
theorem toDatabase_addRow {d : FDatabase} (he : d.EqsInTerms) {f : FnName} {as vs : List Term} :
    (d.addRow f as vs).toDatabase = d.toDatabase.addTerm (.app f (as ++ vs)) := by
  rw [← toDatabase_addTerm (t := .app f (as ++ vs)) he]
  rfl

/-! ### Unions -/
@[simp] theorem mem_terms_union {d₁ d₂ : FDatabase} {t : Term} :
    t ∈ (d₁.union d₂).terms ↔ t ∈ d₁.terms ∨ t ∈ d₂.terms := by
  simp [FDatabase.union, List.mem_dedup]

@[simp] theorem mem_rows_union {d₁ d₂ : FDatabase} {r : Row} :
    r ∈ (d₁.union d₂).rows ↔ r ∈ d₁.rows ∨ r ∈ d₂.rows := by
  simp [FDatabase.union, List.mem_dedup]

@[simp] theorem mem_eqs_union {d₁ d₂ : FDatabase} {p : Term × Term} :
    p ∈ (d₁.union d₂).eqs ↔ p ∈ d₁.eqs ∨ p ∈ d₂.eqs := by
  simp [FDatabase.union, List.mem_dedup]

@[simp] theorem union_sig {d₁ d₂ : FDatabase} : (d₁.union d₂).sig = d₁.sig := rfl

@[simp] theorem union_env {d₁ d₂ : FDatabase} : (d₁.union d₂).env = d₁.env := rfl

@[simp] theorem union_rules {d₁ d₂ : FDatabase} : (d₁.union d₂).rules = d₁.rules := rfl

@[simp] theorem coe_termsF {d : FDatabase} : ↑d.termsF = d.toDatabase.terms := by
  ext t; simp [termsF]

/-! ### `closureF` decides `Cong`

No side condition: `closureTotal` restricts its seed to the candidate universe, and the
denotation restricts its equations to the same term list, so the two restrictions are the
one restriction. -/
theorem mem_closureF_iff {d : FDatabase} {a b : Term} :
    (a, b) ∈ d.closureF ↔ Cong d.toDatabase a b := by
  refine mem_closure_iff_of_diag coe_termsF.symm (Finset.filter_subset _ _) ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp
    exact mem_toDatabase_eqs.mpr (Or.inr ⟨List.mem_toFinset.mp hp.2,
      List.mem_toFinset.mp (mem_candidates.mp hp.1).1,
      List.mem_toFinset.mp (mem_candidates.mp hp.1).2⟩)
  · intro p hp
    rcases mem_toDatabase_eqs.mp hp with ⟨heq, -⟩ | ⟨hp', h₁, h₂⟩
    · exact Or.inl heq
    · exact Or.inr (Finset.mem_filter.mpr
        ⟨mem_candidates.mpr ⟨List.mem_toFinset.mpr h₁, List.mem_toFinset.mpr h₂⟩,
          List.mem_toFinset.mpr hp'⟩)

end FDatabase
/-! ### Enumerating substitutions -/
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
/-! ### Well-formedness transfers through the bridge -/
theorem WF.addTerm {d : FDatabase} (h : d.WF) (he : d.EqsInTerms) (t : Term) :
    (d.addTerm t).WF := by
  rw [FDatabase.WF, toDatabase_addTerm he]; exact Database.WF.addTerm h t

theorem WF.addEq {d : FDatabase} (h : d.WF) (he : d.EqsInTerms) (a b : Term)
    (hlit : a.isLit ∨ b.isLit → a = b) : (d.addEq a b).WF := by
  rw [FDatabase.WF, toDatabase_addEq he]; exact Database.WF.addEq h a b hlit

theorem WF.addTerms {d : FDatabase} (h : d.WF) (he : d.EqsInTerms) (ts : List Term) :
    (d.addTerms ts).WF := by
  rw [FDatabase.WF, toDatabase_addTerms he]; exact Database.WF.addTerms h ts

theorem empty_wf : FDatabase.empty.WF := by
  rw [FDatabase.WF, toDatabase_empty]; exact Database.WF.empty

theorem mem_closureF_addTerm {d : FDatabase} (he : d.EqsInTerms) {t a b : Term} :
    (a, b) ∈ (d.addTerm t).closureF ↔ Cong (d.toDatabase.addTerm t) a b := by
  rw [mem_closureF_iff, toDatabase_addTerm he]

theorem mem_closureF_addTerm₂ {d : FDatabase} (he : d.EqsInTerms) {t₁ t₂ a b : Term} :
    (a, b) ∈ ((d.addTerm t₁).addTerm t₂).closureF
      ↔ Cong ((d.toDatabase.addTerm t₁).addTerm t₂) a b := by
  rw [mem_closureF_iff, toDatabase_addTerm (he.addTerm t₁), toDatabase_addTerm he]

/-- `congrTuple` decides pointwise congruence. -/
theorem congrTuple_iff {d : FDatabase} {xs ys : List Term} :
    FDatabase.congrTuple d.closureF xs ys = true ↔ CongList d.toDatabase xs ys := by
  rw [FDatabase.congrTuple, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    CongList.forall₂, List.forall₂_iff_zip]
  constructor
  · rintro ⟨hlen, hall⟩
    exact ⟨hlen, fun {a b} hab => mem_closureF_iff.mp (by simpa using hall (a, b) hab)⟩
  · rintro ⟨hlen, hall⟩
    exact ⟨hlen, fun q hq => by
      simpa using mem_closureF_iff.mpr (hall (a := q.1) (b := q.2) (by simpa using hq))⟩

/-- `congrTuple_iff` at the database a `Pattern.values` atom extends with its operands: an
operand is an expression, so it may denote a term the program never built, and it belongs
to no congruence class until it is added. -/
theorem congrTuple_addTerms_iff {d : FDatabase} (he : d.EqsInTerms) {ts us xs ys : List Term} :
    FDatabase.congrTuple ((d.addTerms ts).addTerms us).closureF xs ys = true ↔
      CongList ((d.toDatabase.addTerms ts).addTerms us) xs ys := by
  rw [congrTuple_iff, toDatabase_addTerms (he.addTerms ts), toDatabase_addTerms he]

/-! ### The terms a rule variable may be bound to

`matchQuery` enumerates `valueTerms`, `ValidEnv` asks for `terms`. The two coincide
exactly where no name is a merge function, which is the fragment `exec` runs. -/
theorem mem_terms_of_mem_valueTerms {d : FDatabase} {t : Term} (h : t ∈ d.valueTerms) :
    t ∈ d.terms := List.mem_of_mem_filter h

theorem mem_valueTerms {d : FDatabase} (hsig : d.sig.AllConstructors) {t : Term}
    (h : t ∈ d.terms) : t ∈ d.valueTerms := by
  refine List.mem_filter.mpr ⟨h, ?_⟩
  cases t with
  | lit l => rfl
  | app f as =>
    change (d.sig.mergeOf f).isNone = true
    rw [hsig f]; rfl

end FDatabase
/-! ### E-matching -/
/-- **The e-matcher is exactly the specification's matching relation.**

`patternHolds` decides matching through `closureF`, which computes `Cong`, and the
specification compares up to `Cong` too, so there is no gap to close.

`hsig` is what the read atom needs: with no merge function declared, `patternHolds` decides
a `Pattern.values` atom at the entry term `f(a…, v…)`, which is the term `Matches.values`
asks about. `hv` is not a restriction: it is a consequence of the conclusion
(`ValidSubst.validEnv`), and requiring it is what lets the `false` cases be discharged
without inverting. -/
theorem patternHolds_iff {d : FDatabase} (he : d.EqsInTerms)
    (hsig : d.sig.AllConstructors) {p : Pattern} {σ : Env}
    (hv : ValidEnv (p.freeVars d.env) d.toDatabase σ) :
    patternHolds d p σ = true ↔ ValidSubst d.toDatabase p σ := by
  cases p with
  | values vs f as =>
    have hm : (d.sig.mergeOf f).isSome = false := by rw [hsig f]; rfl
    cases hev₁ : Expr.evalList d.sig vs (d.env ++ σ) with
    | none =>
      simp only [patternHolds, hev₁, Bool.false_eq_true, false_iff]
      intro h
      cases h.2 with
      | values _ _ hus _ =>
        rw [FDatabase.toDatabase_env, FDatabase.toDatabase_sig, hev₁] at hus
        simp at hus
    | some us =>
      cases hev₂ : Expr.evalList d.sig as (d.env ++ σ) with
      | none =>
        simp only [patternHolds, hev₁, hev₂, Bool.false_eq_true, false_iff]
        intro h
        cases h.2 with
        | values _ hts _ _ =>
          rw [FDatabase.toDatabase_env, FDatabase.toDatabase_sig, hev₂] at hts
          simp at hts
      | some ts =>
        simp only [patternHolds, hev₁, hev₂, hm, Bool.false_eq_true, if_false,
          decide_eq_true_eq]
        constructor
        · rintro ⟨w, hwm, hcl⟩
          exact ⟨hv, .values (FDatabase.mem_toDatabase_terms.mpr hwm) hev₂ hev₁
            (congOn_singleton.mpr ((FDatabase.mem_closureF_addTerm he).mp hcl))⟩
        · intro h
          cases h.2 with
          | values hwm hts hus hc =>
            rw [FDatabase.toDatabase_env, FDatabase.toDatabase_sig, hev₂] at hts
            rw [FDatabase.toDatabase_env, FDatabase.toDatabase_sig, hev₁] at hus
            cases hts
            cases hus
            exact ⟨_, FDatabase.mem_toDatabase_terms.mp hwm,
              (FDatabase.mem_closureF_addTerm he).mpr (congOn_singleton.mp hc)⟩
  | expr e =>
    cases hev : e.eval d.sig (d.env ++ σ) with
    | none =>
      simp only [patternHolds, hev, Bool.false_eq_true, false_iff]
      intro h
      cases h.2 with
      | expr _ hee _ =>
        rw [FDatabase.toDatabase_env, FDatabase.toDatabase_sig, hev] at hee
        simp at hee
    | some t =>
      simp only [patternHolds, hev, decide_eq_true_eq]
      constructor
      · rintro ⟨w, hwm, hcl⟩
        exact ⟨hv, .expr (FDatabase.mem_toDatabase_terms.mpr hwm) hev (congOn_singleton.mpr
          ((FDatabase.mem_closureF_addTerm he).mp hcl))⟩
      · intro h
        cases h.2 with
        | expr hwm hee hc =>
          rw [FDatabase.toDatabase_env, FDatabase.toDatabase_sig, hev] at hee
          cases hee
          exact ⟨_, FDatabase.mem_toDatabase_terms.mp hwm,
            (FDatabase.mem_closureF_addTerm he).mpr (congOn_singleton.mp hc)⟩
  | eq e₁ e₂ =>
    cases hev₁ : e₁.eval d.sig (d.env ++ σ) with
    | none =>
      simp only [patternHolds, hev₁, Bool.false_eq_true, false_iff]
      intro h
      cases h.2 with
      | eq _ he₁ _ _ _ =>
        rw [FDatabase.toDatabase_env, FDatabase.toDatabase_sig, hev₁] at he₁
        simp at he₁
    | some t₁ =>
      cases hev₂ : e₂.eval d.sig (d.env ++ σ) with
      | none =>
        simp only [patternHolds, hev₁, hev₂, Bool.false_eq_true, false_iff]
        intro h
        cases h.2 with
        | eq _ _ he₂ _ _ =>
          rw [FDatabase.toDatabase_env, FDatabase.toDatabase_sig, hev₂] at he₂
          simp at he₂
      | some t₂ =>
        simp only [patternHolds, hev₁, hev₂, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨heq, w, hwm, hcl⟩
          exact ⟨hv, .eq (FDatabase.mem_toDatabase_terms.mpr hwm) hev₁ hev₂
            (congOn_pair.mpr ((FDatabase.mem_closureF_addTerm₂ he).mp hcl))
            (congOn_pair.mpr ((FDatabase.mem_closureF_addTerm₂ he).mp heq))⟩
        · intro h
          cases h.2 with
          | eq hwm he₁ he₂ hcw hceq =>
            rw [FDatabase.toDatabase_env, FDatabase.toDatabase_sig, hev₁] at he₁
            rw [FDatabase.toDatabase_env, FDatabase.toDatabase_sig, hev₂] at he₂
            cases he₁
            cases he₂
            exact ⟨(FDatabase.mem_closureF_addTerm₂ he).mpr (congOn_pair.mp hceq),
              _, FDatabase.mem_toDatabase_terms.mp hwm,
              (FDatabase.mem_closureF_addTerm₂ he).mpr (congOn_pair.mp hcw)⟩

/-- Restricting a query substitution to one pattern gives a `ValidEnv` for that pattern.
This is the hypothesis `patternHolds_iff` needs, discharged from what `assignments`
guarantees. -/
theorem validEnv_canon {d : FDatabase} {q : Query} {σ : Env} {p : Pattern} (hp : p ∈ q)
    (hdom : Env.dom σ = Query.freeVars q d.env) (hval : ∀ b ∈ σ, b.2 ∈ d.valueTerms) :
    ValidEnv (p.freeVars d.env) d.toDatabase (Env.canon (p.freeVars d.env) σ) := by
  constructor
  · rw [Env.dom_canon_of_subset (Query.freeVars_subset hp) hdom]
  · exact fun b hb => FDatabase.mem_toDatabase_terms.mpr
      (FDatabase.mem_terms_of_mem_valueTerms (hval b (Env.mem_of_lookup (Env.mem_canon hb).2)))

/-- The enumerator produces exactly the substitutions that assign the query's free
variables to values the database holds and satisfy every pattern under restriction.

What is left between this and `ValidQuerySubst` is repackaging: the spec takes one
substitution per pattern and joins them with `Env.UnionAll`, where this restricts a single
substitution. `Env.agree_canon` is what makes the two interchangeable. -/
theorem mem_matchQuery_iff {d : FDatabase} (he : d.EqsInTerms)
    (hsig : d.sig.AllConstructors) {q : Query} {σ : Env} :
    σ ∈ matchQuery d q ↔
      Env.dom σ = Query.freeVars q d.env ∧ (∀ b ∈ σ, b.2 ∈ d.valueTerms) ∧
        ∀ p ∈ q, ValidSubst d.toDatabase p (Env.canon (p.freeVars d.env) σ) := by
  simp only [matchQuery, List.mem_filter, mem_assignments, List.all_eq_true]
  constructor
  · rintro ⟨⟨hdom, hval⟩, hall⟩
    exact ⟨hdom, hval, fun p hp =>
      (patternHolds_iff he hsig (validEnv_canon hp hdom hval)).mp (hall p hp)⟩
  · rintro ⟨hdom, hval, hall⟩
    exact ⟨⟨hdom, hval⟩, fun p hp =>
      (patternHolds_iff he hsig (validEnv_canon hp hdom hval)).mpr (hall p hp)⟩

/-- A restricted substitution refines the one it came from. -/
theorem Env.refines_canon {vars : List Var} {σ : Env} : Env.Refines (Env.canon vars σ) σ :=
  fun _ hb => (Env.mem_canon hb).2

/-- Every substitution the enumerator produces is, up to `Env.Agree`, one the spec admits.

The two differ in shape only: the spec joins one substitution per pattern with
`Env.UnionAll`, and the enumerator restricts a single one. `Env.exists_unionAll` builds the
join out of the restrictions, which are pairwise compatible because they all refine `σ`. -/
theorem validQuerySubst_of_mem_matchQuery {d : FDatabase} (he : d.EqsInTerms)
    (hsig : d.sig.AllConstructors) {q : Query} {σ : Env} (h : σ ∈ matchQuery d q) :
    ∃ τ, ValidQuerySubst d.toDatabase q τ ∧ Env.Agree τ σ := by
  obtain ⟨hdom, hval, hall⟩ := (mem_matchQuery_iff he hsig).mp h
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
`assignments` produces, and no lookup can tell the two apart.

`AllConstructors` is what closes the one gap in the other direction: the enumerator assigns
from `FDatabase.valueTerms`, and with no merge function declared that is every term. -/
theorem mem_matchQuery_of_validQuerySubst {d : FDatabase} (he : d.EqsInTerms)
    (hsig : d.sig.AllConstructors) {q : Query} {τ : Env}
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
  refine ⟨(mem_matchQuery_iff he hsig).mpr ⟨hdom, ?_, ?_⟩, hag⟩
  · exact fun b hb => FDatabase.mem_valueTerms hsig (FDatabase.mem_toDatabase_terms.mp
      (h.mem_terms b (Env.mem_of_lookup (Env.mem_canon hb).2)))
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
    refine ValidSubst.of_agree hvs (fun v => ?_) hpdom
    by_cases hv : v ∈ p.freeVars d.env
    · rw [Env.lookup_canon (p.freeVars_nodup _) hv]
      cases hlk : Env.lookup v σp with
      | none =>
        rw [Env.lookup_eq_none_iff] at hlk
        exact absurd ((ValidSubst.validEnv hvs).1.mem_iff.mpr hv) hlk
      | some t => exact (hrp (v, t) (Env.mem_of_lookup hlk)).symm
    · rw [Env.lookup_eq_none_iff.mpr fun hc => hv ((ValidSubst.validEnv hvs).1.mem_iff.mp hc),
        Env.lookup_eq_none_iff.mpr fun hc => hv (hpdom ▸ hc)]

/-! ### Refinement: actions -/
/-- What one action produces, per case. Every fact below about `execAction` is a four-way
`rcases` on this rather than a repeat of the case analysis. -/
theorem execAction_eq_some {d d' : FDatabase} {a : Action} (h : execAction d a = some d') :
    (∃ t, d' = d.addTerm t) ∨ (∃ v t, d' = { d.addTerm t with env := (v, t) :: d.env }) ∨
      (∃ t₁ t₂, ¬ (t₁.isLit ∨ t₂.isLit) ∧ d' = d.addEq t₁ t₂) ∨
      (∃ f as vs, d' = d.addRow f as vs) := by
  cases a with
  | expr e =>
    cases hv : e.eval d.sig d.env with
    | none => simp [execAction, hv] at h
    | some t =>
      simp only [execAction, hv, Option.map_some, Option.some.injEq] at h
      exact Or.inl ⟨t, h.symm⟩
  | letBind v e =>
    cases hv : e.eval d.sig d.env with
    | none => simp [execAction, hv] at h
    | some t =>
      simp only [execAction, hv, Option.map_some, Option.some.injEq] at h
      exact Or.inr (Or.inl ⟨v, t, h.symm⟩)
  | union e₁ e₂ =>
    cases hv₁ : e₁.eval d.sig d.env with
    | none => simp [execAction, hv₁] at h
    | some t₁ =>
      cases hv₂ : e₂.eval d.sig d.env with
      | none => simp [execAction, hv₁, hv₂] at h
      | some t₂ =>
        simp only [execAction, hv₁, hv₂, Option.bind_some] at h
        split at h
        · simp at h
        · rename_i hlit
          simp only [Option.some.injEq] at h
          exact Or.inr (Or.inr (Or.inl ⟨t₁, t₂, by simpa using hlit, h.symm⟩))
  | set f args out =>
    cases hv₁ : Expr.evalList d.sig args d.env with
    | none => simp [execAction, hv₁] at h
    | some as =>
      cases hv₂ : Expr.evalList d.sig out d.env with
      | none => simp [execAction, hv₁, hv₂] at h
      | some vs =>
        simp only [execAction, hv₁, hv₂, Option.bind_some, Option.map_some,
          Option.some.injEq] at h
        exact Or.inr (Or.inr (Or.inr ⟨f, as, vs, h.symm⟩))

theorem execAction_eqsInTerms {d d' : FDatabase} (he : d.EqsInTerms) {a : Action}
    (h : execAction d a = some d') : d'.EqsInTerms := by
  rcases execAction_eq_some h with ⟨t, rfl⟩ | ⟨v, t, rfl⟩ | ⟨t₁, t₂, -, rfl⟩ |
    ⟨f, as, vs, rfl⟩
  · exact he.addTerm t
  · exact (he.addTerm t).setEnv _
  · exact he.addEq t₁ t₂
  · exact he.addRow f as vs

theorem execAction_rules {d d' : FDatabase} {a : Action} (h : execAction d a = some d') :
    d'.rules = d.rules := by
  rcases execAction_eq_some h with ⟨t, rfl⟩ | ⟨v, t, rfl⟩ | ⟨t₁, t₂, -, rfl⟩ |
    ⟨f, as, vs, rfl⟩ <;>
    rfl

theorem execActions_eqsInTerms {as : List Action} : ∀ {d d' : FDatabase}, d.EqsInTerms →
    execActions d as = some d' → d'.EqsInTerms := by
  induction as with
  | nil => intro d d' he h; exact (Option.some.injEq .. ▸ h : d = d') ▸ he
  | cons a as ih =>
    intro d d' he h
    cases hv : execAction d a with
    | none => rw [execActions, hv] at h; simp at h
    | some e =>
      rw [execActions, hv, Option.bind_some] at h
      exact ih (execAction_eqsInTerms he hv) h

theorem execLocalActions_eqsInTerms {d d' : FDatabase} (he : d.EqsInTerms) {as : List Action}
    {σ : Env} (h : execLocalActions d as σ = some d') : d'.EqsInTerms := by
  cases hv : execActions { d with env := d.env ++ σ } as with
  | none => rw [execLocalActions, hv] at h; simp at h
  | some e =>
    rw [execLocalActions, hv, Option.map_some, Option.some.injEq] at h
    exact h ▸ (execActions_eqsInTerms (he.setEnv _) hv).restore

theorem execAction_toDatabase {d : FDatabase} (he : d.EqsInTerms) {a : Action} :
    (execAction d a).map FDatabase.toDatabase = evalAction d.toDatabase a := by
  cases a with
  | expr e =>
    cases hv : e.eval d.sig d.env with
    | none => simp [execAction, evalAction, hv]
    | some t => simp [execAction, evalAction, hv, FDatabase.toDatabase_addTerm he]
  | letBind v e =>
    cases hv : e.eval d.sig d.env with
    | none => simp [execAction, evalAction, hv]
    | some t => simp [execAction, evalAction, hv, FDatabase.toDatabase_addTerm he]
  | union e₁ e₂ =>
    cases hv₁ : e₁.eval d.sig d.env with
    | none => simp [execAction, evalAction, hv₁]
    | some t₁ =>
      cases hv₂ : e₂.eval d.sig d.env with
      | none => simp [execAction, evalAction, hv₁, hv₂]
      | some t₂ =>
        by_cases hlit : t₁.isLit ∨ t₂.isLit
        · simp [execAction, evalAction, hv₁, hv₂, hlit]
        · simp [execAction, evalAction, hv₁, hv₂, hlit, FDatabase.toDatabase_addEq he]
  | set f args out =>
    cases hv₁ : Expr.evalList d.sig args d.env with
    | none => simp [execAction, evalAction, hv₁]
    | some as =>
      cases hv₂ : Expr.evalList d.sig out d.env with
      | none => simp [execAction, evalAction, hv₁, hv₂]
      | some vs => simp [execAction, evalAction, hv₁, hv₂, FDatabase.toDatabase_addRow he]

theorem execActions_toDatabase {as : List Action} : ∀ {d : FDatabase}, d.EqsInTerms →
    (execActions d as).map FDatabase.toDatabase = evalActions d.toDatabase as := by
  induction as with
  | nil => intro d _; rfl
  | cons a as ih =>
    intro d he
    cases hv : execAction d a with
    | none =>
      have : evalAction d.toDatabase a = none := by rw [← execAction_toDatabase he, hv]; rfl
      simp [execActions, hv, this]
    | some d' =>
      have hd : evalAction d.toDatabase a = some d'.toDatabase := by
        rw [← execAction_toDatabase he, hv]; rfl
      simp [execActions, hv, hd, ih (execAction_eqsInTerms he hv)]

theorem execLocalActions_toDatabase {d : FDatabase} (he : d.EqsInTerms) {as : List Action}
    {σ : Env} :
    (execLocalActions d as σ).map FDatabase.toDatabase
      = evalLocalActions d.toDatabase as σ := by
  rw [execLocalActions, Option.map_map,
    show FDatabase.toDatabase ∘ (fun d' : FDatabase =>
        ({ d' with env := d.env, rules := d.rules } : FDatabase))
      = (fun db' : Database =>
          ({ db' with env := d.toDatabase.env, rules := d.toDatabase.rules } : Database))
        ∘ FDatabase.toDatabase from by funext d'; rfl,
    ← Option.map_map, execActions_toDatabase (he.setEnv _)]
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

theorem eqsInTerms_foldl {g : FDatabase → α → FDatabase}
    (hg : ∀ acc a, acc.EqsInTerms → (g acc a).EqsInTerms)
    (l : List α) {init : FDatabase} (h : init.EqsInTerms) :
    (l.foldl g init).EqsInTerms := by
  induction l generalizing init with
  | nil => exact h
  | cons a l ih => exact ih (hg init a h)

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

theorem eqsInTerms_fireInto {d : FDatabase} (he : d.EqsInTerms) {r : Rule} {acc : FDatabase}
    (ha : acc.EqsInTerms) {σ : Env} : (fireInto d r acc σ).EqsInTerms := by
  unfold fireInto
  cases hv : execLocalActions d r.actions σ with
  | none => exact ha
  | some d' => exact ha.union (execLocalActions_eqsInTerms he hv)

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

theorem eqsInTerms_fireRule {d acc : FDatabase} (he : d.EqsInTerms) (ha : acc.EqsInTerms)
    {r : Rule} : (fireRule d acc r).EqsInTerms :=
  eqsInTerms_foldl (g := fireInto d r) (fun _ _ h => eqsInTerms_fireInto he h) _ ha

theorem sig_fireRule {d acc : FDatabase} {r : Rule} : (fireRule d acc r).sig = acc.sig :=
  sig_foldl (g := fireInto d r) (fun _ _ => sig_fireInto) _ _

theorem env_fireRule {d acc : FDatabase} {r : Rule} : (fireRule d acc r).env = acc.env :=
  env_foldl (g := fireInto d r) (fun _ _ => env_fireInto) _ _

theorem rules_fireRule {d acc : FDatabase} {r : Rule} :
    (fireRule d acc r).rules = acc.rules :=
  rules_foldl (g := fireInto d r) (fun _ _ => rules_fireInto) _ _

/-- A round folds over `R`'s rules, so every membership lemma below reads the filter back
off as the side condition `r.ruleset = R`. -/
theorem mem_rules_filter {R : RulesetName} {d : FDatabase} {r : Rule} :
    r ∈ d.rules.filter (fun r => r.ruleset == R) ↔ r ∈ d.rules ∧ r.ruleset = R := by
  simp [List.mem_filter]

theorem mem_terms_execRunRules {R : RulesetName} {d : FDatabase} {t : Term} :
    t ∈ (execRunRules R d).terms ↔ t ∈ d.terms ∨
      ∃ r ∈ d.rules, r.ruleset = R ∧
        ∃ σ ∈ matchQuery d r.query, ∃ d', Fired d r σ d' ∧ t ∈ d'.terms := by
  rw [execRunRules, mem_terms_foldl (g := fireRule d)
    (C := fun r t => ∃ σ ∈ matchQuery d r.query, ∃ d', Fired d r σ d' ∧ t ∈ d'.terms)
    (fun _ _ _ => mem_terms_fireRule)]
  simp only [mem_rules_filter, and_assoc]

theorem mem_eqs_execRunRules {R : RulesetName} {d : FDatabase} {p : Term × Term} :
    p ∈ (execRunRules R d).eqs ↔ p ∈ d.eqs ∨
      ∃ r ∈ d.rules, r.ruleset = R ∧
        ∃ σ ∈ matchQuery d r.query, ∃ d', Fired d r σ d' ∧ p ∈ d'.eqs := by
  rw [execRunRules, mem_eqs_foldl (g := fireRule d)
    (C := fun r p => ∃ σ ∈ matchQuery d r.query, ∃ d', Fired d r σ d' ∧ p ∈ d'.eqs)
    (fun _ _ _ => mem_eqs_fireRule)]
  simp only [mem_rules_filter, and_assoc]

theorem mem_rows_execRunRules {R : RulesetName} {d : FDatabase} {q : Row} :
    q ∈ (execRunRules R d).rows ↔ q ∈ d.rows ∨
      ∃ r ∈ d.rules, r.ruleset = R ∧
        ∃ σ ∈ matchQuery d r.query, ∃ d', Fired d r σ d' ∧ q ∈ d'.rows := by
  rw [execRunRules, mem_rows_foldl (g := fireRule d)
    (C := fun r q => ∃ σ ∈ matchQuery d r.query, ∃ d', Fired d r σ d' ∧ q ∈ d'.rows)
    (fun _ _ _ => mem_rows_fireRule)]
  simp only [mem_rules_filter, and_assoc]

theorem eqsInTerms_execRunRules {R : RulesetName} {d : FDatabase} (he : d.EqsInTerms) :
    (execRunRules R d).EqsInTerms :=
  eqsInTerms_foldl (g := fireRule d) (fun _ _ h => eqsInTerms_fireRule he h) _ he

@[simp] theorem sig_execRunRules {R : RulesetName} {d : FDatabase} :
    (execRunRules R d).sig = d.sig :=
  sig_foldl (g := fireRule d) (fun _ _ => sig_fireRule) _ _

@[simp] theorem env_execRunRules {R : RulesetName} {d : FDatabase} :
    (execRunRules R d).env = d.env :=
  env_foldl (g := fireRule d) (fun _ _ => env_fireRule) _ _

@[simp] theorem rules_execRunRules {R : RulesetName} {d : FDatabase} :
    (execRunRules R d).rules = d.rules :=
  rules_foldl (g := fireRule d) (fun _ _ => rules_fireRule) _ _

/-- A firing's result denotes the spec's. -/
theorem fired_toDatabase {d : FDatabase} (he : d.EqsInTerms) {r : Rule} {σ : Env}
    {d' : FDatabase} (h : Fired d r σ d') :
    evalLocalActions d.toDatabase r.actions σ = some d'.toDatabase := by
  rw [← execLocalActions_toDatabase he, h]; rfl

/-- What one round of `R`'s firings contribute, as a predicate on the databases they
produce. Both `terms` and `eqs` of a round are the pre-state's plus what this collects, so
the correspondence with `RuleResults` is proved once. -/
def Fires (R : RulesetName) (d : FDatabase) (P : Database → Prop) : Prop :=
  ∃ r ∈ d.rules, r.ruleset = R ∧
    ∃ σ ∈ matchQuery d r.query, ∃ d' : FDatabase, Fired d r σ d' ∧ P d'.toDatabase

/-- **The two rounds union in the same databases.**

The interpreter enumerates its canonical substitutions and the spec every `Env.UnionAll`
decomposition; `evalLocalActions_agree` is what makes them contribute the same states. The
ruleset is carried along untouched: both sides read it off the same rule. -/
theorem fires_iff {R : RulesetName} {d : FDatabase} (he : d.EqsInTerms)
    (hsig : d.sig.AllConstructors) {P : Database → Prop} :
    Fires R d P ↔
      ∃ D, (∃ r ∈ d.toDatabase.rules, r.ruleset = R ∧ D ∈ RuleResults d.toDatabase r) ∧ P D := by
  constructor
  · rintro ⟨r, hr, hR, σ, hσ, d', hf, hP⟩
    obtain ⟨τ, hτ, hag⟩ := validQuerySubst_of_mem_matchQuery he hsig hσ
    refine ⟨d'.toDatabase, ⟨r, hr, hR, τ, hτ, ?_⟩, hP⟩
    rw [evalLocalActions_agree r.actions hag]
    exact fired_toDatabase he hf
  · rintro ⟨D, ⟨r, hr, hR, τ, hτ, hev⟩, hP⟩
    obtain ⟨hmem, hag⟩ := mem_matchQuery_of_validQuerySubst he hsig hτ
    have hev' : evalLocalActions d.toDatabase r.actions
        (Env.canon (Query.freeVars r.query d.env) τ) = some D := by
      rw [← evalLocalActions_agree r.actions hag]; exact hev
    have hmap := execLocalActions_toDatabase he (d := d) (as := r.actions)
      (σ := Env.canon (Query.freeVars r.query d.env) τ)
    rw [hev'] at hmap
    obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hmap
    exact ⟨r, hr, hR, _, hmem, d', hd', hP⟩

theorem mem_eqs_toDatabase_execRunRules {R : RulesetName} {d : FDatabase} (he : d.EqsInTerms)
    {p : Term × Term} :
    p ∈ (execRunRules R d).toDatabase.eqs ↔
      p ∈ d.toDatabase.eqs ∨ Fires R d (fun D => p ∈ D.eqs) := by
  rw [FDatabase.mem_toDatabase_eqs_of_eqsInTerms (eqsInTerms_execRunRules he),
    FDatabase.mem_toDatabase_eqs_of_eqsInTerms he, mem_terms_execRunRules, mem_eqs_execRunRules]
  constructor
  · rintro (⟨heq, ht | ⟨r, hr, hR, σ, hσ, d', hf, ht⟩⟩ | (hp | ⟨r, hr, hR, σ, hσ, d', hf, hp⟩))
    · exact Or.inl (Or.inl ⟨heq, ht⟩)
    · exact Or.inr ⟨r, hr, hR, σ, hσ, d', hf,
        (FDatabase.mem_toDatabase_eqs_of_eqsInTerms
          (execLocalActions_eqsInTerms he hf)).mpr (Or.inl ⟨heq, ht⟩)⟩
    · exact Or.inl (Or.inr hp)
    · exact Or.inr ⟨r, hr, hR, σ, hσ, d', hf,
        (FDatabase.mem_toDatabase_eqs_of_eqsInTerms
          (execLocalActions_eqsInTerms he hf)).mpr (Or.inr hp)⟩
  · rintro ((⟨heq, ht⟩ | hp) | ⟨r, hr, hR, σ, hσ, d', hf, hP⟩)
    · exact Or.inl ⟨heq, Or.inl ht⟩
    · exact Or.inr (Or.inl hp)
    · rcases (FDatabase.mem_toDatabase_eqs_of_eqsInTerms
        (execLocalActions_eqsInTerms he hf)).mp hP with ⟨heq, ht⟩ | hp
      · exact Or.inl ⟨heq, Or.inr ⟨r, hr, hR, σ, hσ, d', hf, ht⟩⟩
      · exact Or.inr (Or.inr ⟨r, hr, hR, σ, hσ, d', hf, hp⟩)

/-- **One round of the interpreter denotes one round of the spec.**

This is `RunRules`, the rule-firing half of a round; the merge phase is empty here because
`exec` runs the constructor fragment, where `MergeStep` never fires
(`MergeStep.not_of_allConstructors`). -/
theorem execRunRules_RunRules {R : RulesetName} {d : FDatabase} (he : d.EqsInTerms)
    (hsig : d.sig.AllConstructors) :
    (execRunRules R d).toDatabase = RunRules R d.toDatabase := by
  refine Database.ext ?_ ?_ ?_ ?_
  · change (execRunRules R d).sig = _
    rw [sig_execRunRules]; rfl
  · ext p
    rw [mem_eqs_toDatabase_execRunRules he, fires_iff he hsig]
    simp only [RunRules, Database.sUnion_eqs, Set.mem_union, Set.mem_iUnion₂, Set.mem_setOf_eq,
      exists_prop]
  · change (execRunRules R d).env = _
    rw [env_execRunRules]; rfl
  · change {r | r ∈ (execRunRules R d).rules} = _
    rw [rules_execRunRules]; rfl

/-! ### A saturating run

`runSaturateF` is `Impl/Merge.lean`'s `mergeSaturateF` pattern one level up, and it wants
the same two facts: what it returns is a fixpoint of the round, and what it returns is an
iterate of it. Neither mentions the specification, so both are read straight off the
recursion. -/

/-- Two states with the same fields denote the same database. `FDatabase.sameData` decides
three of the five the denotation reads; a round fixes the other two. -/
theorem toDatabase_eq_of_fields {d e : FDatabase} (hsig : d.sig = e.sig)
    (ht : d.terms = e.terms) (hq : d.eqs = e.eqs) (henv : d.env = e.env)
    (hrules : d.rules = e.rules) : d.toDatabase = e.toDatabase := by
  unfold FDatabase.toDatabase
  rw [hsig, ht, hq, henv, hrules]

/-- **`runSaturateF` never claims a saturation it has not reached.** -/
theorem runSaturateF_sameData {R : RulesetName} : ∀ (n : Nat) {d e : FDatabase},
    d.runSaturateF R n = some e → e.sameData (execRunRules R e) = true := by
  intro n
  induction n with
  | zero =>
    intro d e h
    rw [FDatabase.runSaturateF] at h
    split at h
    · rename_i hs; rw [Option.some.injEq] at h; exact h ▸ hs
    · exact absurd h (by simp)
  | succ n ih =>
    intro d e h
    rw [FDatabase.runSaturateF] at h
    split at h
    · rename_i hs; rw [Option.some.injEq] at h; exact h ▸ hs
    · exact ih h

/-- **And what it returns is an iterate of the round**, so the specification can follow it
one `RunStep` at a time. -/
theorem runSaturateF_iterate {R : RulesetName} : ∀ (n : Nat) {d e : FDatabase},
    d.runSaturateF R n = some e → ∃ k, (execRunRules R)^[k] d = e := by
  intro n
  induction n with
  | zero =>
    intro d e h
    rw [FDatabase.runSaturateF] at h
    split at h
    · rw [Option.some.injEq] at h; exact ⟨0, h⟩
    · exact absurd h (by simp)
  | succ n ih =>
    intro d e h
    rw [FDatabase.runSaturateF] at h
    split at h
    · rw [Option.some.injEq] at h; exact ⟨0, h⟩
    · obtain ⟨k, hk⟩ := ih h
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

theorem eqsInTerms_iterate {R : RulesetName} : ∀ (k : Nat) {d : FDatabase}, d.EqsInTerms →
    ((execRunRules R)^[k] d).EqsInTerms := by
  intro k
  induction k with
  | zero => intro d he; exact he
  | succ k ih =>
    intro d he
    rw [Function.iterate_succ_apply']
    exact eqsInTerms_execRunRules (ih he)

theorem execRunRules_iterate_sig {R : RulesetName} : ∀ (k : Nat) {d : FDatabase},
    ((execRunRules R)^[k] d).sig = d.sig := by
  intro k
  induction k with
  | zero => intro d; rfl
  | succ k ih => intro d; rw [Function.iterate_succ_apply', sig_execRunRules]; exact ih

/-- **The specification takes one `RunStep` per interpreter round.** -/
theorem execRunRules_iterate {R : RulesetName} : ∀ (k : Nat) {d : FDatabase}, d.EqsInTerms →
    d.sig.AllConstructors →
      Relation.ReflTransGen (RunStep R) d.toDatabase ((execRunRules R)^[k] d).toDatabase := by
  intro k
  induction k with
  | zero => intro d _ _; exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro d he hsig
    have hex : ((execRunRules R)^[k] d).sig.AllConstructors := by
      rw [execRunRules_iterate_sig k]; exact hsig
    rw [Function.iterate_succ_apply']
    refine (ih he hsig).tail ?_
    change MergeClosure (RunRules R ((execRunRules R)^[k] d).toDatabase) _
    rw [← execRunRules_RunRules (eqsInTerms_iterate k he) hex]
    exact Relation.ReflTransGen.refl

/-! #### The witness version

`runSaturate` is `runSaturateF` without the fuel. It is not what `exec` runs — no caller can
produce an `Acc` witness for a ruleset whose saturation is the question — but it is where the
statement without a side condition lives, and it is what pins the fuel's incompleteness on
the fuel rather than on the design. -/
theorem runSaturate_of_settled {R : RulesetName} {d : FDatabase}
    (h : Acc (FDatabase.RunRel R) d) (hs : d.sameData (execRunRules R d) = true) :
    FDatabase.runSaturate R d h = d := by
  cases h with
  | intro hx => simp only [FDatabase.runSaturate, hs, dif_pos]

theorem runSaturate_step {R : RulesetName} {d : FDatabase}
    (h : Acc (FDatabase.RunRel R) d) (hs : ¬ d.sameData (execRunRules R d) = true) :
    FDatabase.runSaturate R d h
      = FDatabase.runSaturate R (execRunRules R d) (h.inv ⟨rfl, hs⟩) := by
  cases h with
  | intro hx => exact dif_neg hs

/-- **The fuel agrees with the witness whenever it answers.** So the fuel never invents an
answer, and `runSaturateF` returning `none` is the *only* way the two differ. -/
theorem runSaturateF_eq_runSaturate {R : RulesetName} : ∀ (n : Nat) {d e : FDatabase}
    (h : Acc (FDatabase.RunRel R) d), d.runSaturateF R n = some e →
    FDatabase.runSaturate R d h = e := by
  intro n
  induction n with
  | zero =>
    intro d e h hf
    rw [FDatabase.runSaturateF] at hf
    split at hf
    · rename_i hs
      rw [Option.some.injEq] at hf
      rw [runSaturate_of_settled h hs, hf]
    · exact absurd hf (by simp)
  | succ n ih =>
    intro d e h hf
    rw [FDatabase.runSaturateF] at hf
    split at hf
    · rename_i hs
      rw [Option.some.injEq] at hf
      rw [runSaturate_of_settled h hs, hf]
    · rename_i hs
      rw [runSaturate_step h hs]
      exact ih _ hf

/-- **The witness version reaches the specification's fixpoint, unconditionally.** No fuel
and no `≠ none`: given only that the ruleset saturates at all, which is what the `Acc`
witness says, `runSaturate` lands on a `SaturateReach`. Whatever `exec_programStep` has to
carry is therefore the *fuel's*, not the semantics'. -/
theorem runSaturate_saturateReach {R : RulesetName} : ∀ {d : FDatabase}
    (h : Acc (FDatabase.RunRel R) d), d.EqsInTerms → d.sig.AllConstructors →
    SaturateReach R d.toDatabase (FDatabase.runSaturate R d h).toDatabase := by
  intro d h
  induction h with
  | @intro x hx ih =>
    intro he hsig
    by_cases hs : x.sameData (execRunRules R x) = true
    · rw [runSaturate_of_settled _ hs]
      simp only [FDatabase.sameData, Bool.and_eq_true, beq_iff_eq] at hs
      refine ⟨Relation.ReflTransGen.refl, ?_,
        fun db' hstep => (MergeStep.not_of_allConstructors hsig hstep).elim⟩
      rw [← execRunRules_RunRules he hsig]
      exact toDatabase_eq_of_fields sig_execRunRules hs.1.1 hs.2 env_execRunRules
        rules_execRunRules
    · rw [runSaturate_step _ hs]
      have hsx : (execRunRules R x).sig.AllConstructors := by
        rw [sig_execRunRules]; exact hsig
      obtain ⟨hreach, hsat⟩ :=
        ih (execRunRules R x) ⟨rfl, hs⟩ (eqsInTerms_execRunRules he) hsx
      refine ⟨Relation.ReflTransGen.head ?_ hreach, hsat⟩
      change MergeClosure (RunRules R x.toDatabase) _
      rw [← execRunRules_RunRules he hsig]
      exact Relation.ReflTransGen.refl

/-- **The interpreter's saturating run reaches the specification's fixpoint.**

The rounds are `runSaturateF_iterate` replayed as `RunStep`s; the fixpoint is
`runSaturateF_sameData` read through `execRunRules_RunRules`, which on the constructor
fragment is an *equality* and not a containment. `MergeSaturated` is free there —
`MergeStep.not_of_allConstructors`. -/
theorem runSaturateF_saturateReach {R : RulesetName} {n : Nat} {d e : FDatabase}
    (he : d.EqsInTerms) (hsig : d.sig.AllConstructors) (h : d.runSaturateF R n = some e) :
    SaturateReach R d.toDatabase e.toDatabase := by
  obtain ⟨k, hk⟩ := runSaturateF_iterate n h
  have hreach := execRunRules_iterate (R := R) k he hsig
  have hes := execRunRules_iterate_sig (R := R) k (d := d)
  have hee : e.EqsInTerms := hk ▸ eqsInTerms_iterate (R := R) k he
  rw [hk] at hes hreach
  have hesig : e.sig.AllConstructors := by rw [hes]; exact hsig
  have hsame := runSaturateF_sameData n h
  simp only [FDatabase.sameData, Bool.and_eq_true, beq_iff_eq] at hsame
  refine ⟨hreach, ?_, fun db' hstep => (MergeStep.not_of_allConstructors hesig hstep).elim⟩
  rw [← execRunRules_RunRules hee hesig]
  exact toDatabase_eq_of_fields sig_execRunRules hsame.1.1 hsame.2 env_execRunRules
    rules_execRunRules

/-! ### Refinement: commands and programs -/
/-- **The interpreter's command is the specification's `cmdEffect`**, on the four commands
that have one. -/
theorem execCmd_toDatabase {d : FDatabase} (he : d.EqsInTerms) (hsig : d.sig.AllConstructors)
    {c : Cmd} (hns : c.NoSaturate) :
    (execCmd d c).map FDatabase.toDatabase = cmdEffect d.toDatabase c := by
  cases c with
  | action a => exact execAction_toDatabase he
  | rule r =>
    rw [show execCmd d (.rule r) = some { d with rules := r :: d.rules } from rfl,
      Option.map_some, FDatabase.toDatabase_consRule]
    rfl
  | run R =>
    rw [show execCmd d (.run R) = some (execRunRules R d) from rfl, Option.map_some,
      execRunRules_RunRules he hsig]
    rfl
  | saturate R => exact (hns : False).elim
  | decl f dc => rfl

/-- **The interpreter's command is one the specification reaches.** The uniform statement:
`Cmd.saturate` has no `cmdEffect`, and `runSaturateF_saturateReach` is what stands in its
place. -/
theorem execCmd_cmdReach {d d' : FDatabase} (he : d.EqsInTerms)
    (hsig : d.sig.AllConstructors) {c : Cmd} (h : execCmd d c = some d') :
    cmdReach d.toDatabase c d'.toDatabase := by
  have hgen : ∀ c : Cmd, c.NoSaturate → execCmd d c = some d' →
      cmdReach d.toDatabase c d'.toDatabase := by
    intro c hns hc
    refine cmdReach_of_cmdEffect hns ?_
    rw [← execCmd_toDatabase he hsig hns, hc, Option.map_some]
  cases c with
  | saturate R => exact runSaturateF_saturateReach he hsig h
  | _ => exact hgen _ trivial h

theorem execCmd_eqsInTerms {d d' : FDatabase} (he : d.EqsInTerms) {c : Cmd}
    (h : execCmd d c = some d') : d'.EqsInTerms := by
  cases c with
  | action a => exact execAction_eqsInTerms he h
  | rule r =>
    rw [show execCmd d (.rule r) = some { d with rules := r :: d.rules } from rfl,
      Option.some.injEq] at h
    exact h ▸ he.consRule r
  | run R =>
    rw [show execCmd d (.run R) = some (execRunRules R d) from rfl, Option.some.injEq] at h
    exact h ▸ eqsInTerms_execRunRules he
  | saturate R =>
    obtain ⟨k, hk⟩ :=
      runSaturateF_iterate runFuel (show d.runSaturateF R runFuel = some d' from h)
    exact hk ▸ eqsInTerms_iterate k he
  | decl f dc =>
    rw [show execCmd d (.decl f dc) = some { d with sig := Function.update d.sig f (some dc) }
        from rfl, Option.some.injEq] at h
    exact h ▸ he.setSig _

theorem execCmd_sig {d d' : FDatabase} (he : d.EqsInTerms) (hsig : d.sig.AllConstructors)
    {c : Cmd} (h : execCmd d c = some d') :
    d'.sig = c.sigBind d.sig :=
  cmdReach_sig (execCmd_cmdReach he hsig h)

theorem execCmd_allConstructors {d d' : FDatabase} (he : d.EqsInTerms)
    (hsig : d.sig.AllConstructors) {c : Cmd} (hdecl : c.CtorDecl)
    (h : execCmd d c = some d') : d'.sig.AllConstructors := by
  rw [execCmd_sig he hsig h]; exact hsig.sigBind hdecl

/-- **One command, both ways.** The interpreter's step is exactly the specification's,
not merely one the specification permits.

`CmdStep` is a relation because the merge phase is one, so an `if and only if` is more
than bookkeeping: `←` says the interpreter reaches *every* state the specification allows.
It holds because on the constructor fragment there is no merge phase to choose in, which
is `MergeClosure.eq_of_allConstructors`.

`hs` is what `Cmd.saturate` costs, and **only** `Cmd.saturate`: on any other command the
left arm holds for free. A saturating run can exhaust `runFuel` on a ruleset the
specification does saturate, and then `←` fails; given an answer at all, determinism says
it is *the* answer, which is `CmdStep.det`. -/
theorem execCmd_cmdStep {d : FDatabase} (he : d.EqsInTerms) (hsig : d.sig.AllConstructors)
    {c : Cmd} (hdecl : c.CtorDecl) (hs : c.NoSaturate ∨ execCmd d c ≠ none) {D : Database} :
    (execCmd d c).map FDatabase.toDatabase = some D ↔ CmdStep d.toDatabase c D := by
  cases hce : execCmd d c with
  | none =>
    refine ⟨fun h => absurd h (by simp), fun hstep => ?_⟩
    obtain ⟨x, hreach, -⟩ := hstep
    have hns : c.NoSaturate := hs.resolve_right (by rw [hce]; simp)
    have hx : (execCmd d c).map FDatabase.toDatabase = some x := by
      rw [execCmd_toDatabase he hsig hns, cmdEffect_of_cmdReach hns hreach]
    rw [hce] at hx; simp at hx
  | some d' =>
    have hstep : CmdStep d.toDatabase c d'.toDatabase :=
      ⟨d'.toDatabase, execCmd_cmdReach he hsig hce, Relation.ReflTransGen.refl⟩
    rw [Option.map_some, Option.some.injEq]
    exact ⟨fun h => h ▸ hstep, fun h => CmdStep.det hsig hdecl hstep h⟩

theorem execProgram_programStep {p : Program} : ∀ {d : FDatabase}, d.EqsInTerms →
    d.sig.AllConstructors → p.CtorDecls → (p.NoSaturate ∨ execProgram d p ≠ none) →
    ∀ {D : Database},
      (execProgram d p).map FDatabase.toDatabase = some D ↔ ProgramStep d.toDatabase p D := by
  induction p with
  | nil =>
    intro d _ _ _ _ D
    rw [show execProgram d [] = some d from rfl, Option.map_some, Option.some.injEq]
    exact ⟨fun hd => hd ▸ .nil, fun hs => hs.nil_inv⟩
  | cons c cs ih =>
    intro d he hsig hdecl hs D
    have hc : Cmd.CtorDecl c := hdecl c (by simp)
    have hrest : Program.CtorDecls cs := fun c' hc' => hdecl c' (List.mem_cons_of_mem c hc')
    have hcons : execProgram d (c :: cs)
        = (execCmd d c).bind fun d' => execProgram d' cs := rfl
    cases hce : execCmd d c with
    | none =>
      rw [hcons, hce, Option.bind_none]
      refine ⟨fun h => absurd h (by simp), fun hstep => ?_⟩
      obtain ⟨e, hstep₁, -⟩ := hstep.cons_inv
      have hcs : (execCmd d c).map FDatabase.toDatabase = some e :=
        (execCmd_cmdStep he hsig hc
          (hs.imp (fun hns => hns c List.mem_cons_self)
            (fun hne hx => hne (by rw [hcons, hx, Option.bind_none])))).mpr hstep₁
      rw [hce] at hcs; simp at hcs
    | some d₁ =>
      have hstep₁ : CmdStep d.toDatabase c d₁.toDatabase :=
        ⟨d₁.toDatabase, execCmd_cmdReach he hsig hce, Relation.ReflTransGen.refl⟩
      have hs₁ : Program.NoSaturate cs ∨ execProgram d₁ cs ≠ none :=
        hs.imp (fun hns c' hc' => hns c' (List.mem_cons_of_mem c hc'))
          (fun hne => by rwa [hcons, hce, Option.bind_some] at hne)
      have ihx := ih (execCmd_eqsInTerms he hce) (execCmd_allConstructors he hsig hc hce)
        hrest hs₁ (D := D)
      rw [hcons, hce, Option.bind_some]
      refine ⟨fun hmap => .cons hstep₁ (ihx.mp hmap), fun hst => ?_⟩
      obtain ⟨e, hstep, hrestep⟩ := hst.cons_inv
      obtain rfl := CmdStep.det hsig hc hstep hstep₁
      exact ihx.mpr hrestep

/-- **The refinement theorem**: on the constructor fragment, the interpreter computes
exactly the states the semantics reaches — an `if and only if`, so a `#guard` or a
differential test constrains `Spec/` in both directions.

`hdecl` is not removable: `Falsity.exec_programStep_needs_ctorDecls` exhibits a program
whose only offence is a `:merge` declaration and two states the specification reaches, of
which the interpreter returns at most one. The row atom is included: with no merge function
declared, every entry is its own application, which `patternHolds` decides at the entry
term rather than through the index.

`hs` is what `Cmd.saturate` cost, and it is a **disjunction so that the fragment without one
pays nothing**: `Program.NoSaturate` is a syntactic condition, satisfied by every difftest
case and by every source program, and under it the iff is unconditional exactly as before.
The right arm is for a program that does saturate. There it is not removable: `runSaturateF`
gives up after `runFuel` rounds while `SaturateReach` has no fuel, so on a program the
specification saturates in more rounds the interpreter returns nothing while the
specification reaches a state — `←` failing. No constant fuel repairs that, since the round
count grows with the data rather than with the program text. The gap is the *fuel's* and not
the semantics': `runSaturate_saturateReach` is the same statement about `runSaturate`, with
no side condition at all. `→` is untouched in every case, and it is the direction a `#guard`
or a differential test uses. -/
theorem exec_programStep {p : Program} (hdecl : p.CtorDecls)
    (hs : p.NoSaturate ∨ exec p ≠ none) {D : Database} :
    (exec p).map FDatabase.toDatabase = some D ↔ ProgramStep Database.empty p D := by
  rw [show exec p = execProgram FDatabase.empty p from rfl, ← FDatabase.toDatabase_empty]
  exact execProgram_programStep FDatabase.empty_eqsInTerms
    (by intro f; simp [Signature.mergeOf, FDatabase.empty]) hdecl hs

end Egglog
