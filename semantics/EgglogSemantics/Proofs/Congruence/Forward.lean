import EgglogSemantics.Proofs.Congruence.QueryVars
import EgglogSemantics.Proofs.Congruence.LiveQuery
import EgglogSemantics.Proofs.Congruence.Flatten
import EgglogSemantics.Proofs.Source.FreshEnv

/-! Forward query completeness, following the original query in compiler order. -/

namespace Egglog.Congruence

/-- A flattened atom is answered by an indexed entry or structural equality of a held value. -/
inductive FlatRead (d : FDatabase) (ρ : Env) : Pattern → Prop where
  | entry {p : Pattern} : EntryRead d ρ p → FlatRead d ρ p
  | eq {a b : Expr} {i : Term} :
      a.eval d.sig ρ = some i → b.eval d.sig ρ = some i → i ∈ d.terms → FlatRead d ρ (.eq a b)

theorem FlatRead.bound {d : FDatabase} {ρ : Env} {p : Pattern} (h : FlatRead d ρ p)
    {v : Var} (hv : v ∈ p.freeVars []) : (Env.lookup v ρ).isSome := by
  cases h with
  | entry he => exact he.bound hv
  | eq ha hb _ =>
      have hm := ((Pattern.mem_freeVars _).mp hv).1
      rcases List.mem_union_iff.mp hm with hm | hm
      · exact Expr.lookup_isSome_of_mem_vars ha hm
      · exact Expr.lookup_isSome_of_mem_vars hb hm

theorem FlatRead.holds {d : FDatabase} {ρ : Env} {p : Pattern} (h : FlatRead d ρ p) :
    patternHolds d p (Env.canon (p.freeVars []) ρ) = true := by
  cases h with
  | entry he => exact he.holds
  | @eq a b i ha hb hi =>
      let σ := Env.canon ((Pattern.eq a b).freeVars []) ρ
      have hag : ∀ v ∈ (Pattern.eq a b).vars, Env.lookup v σ = Env.lookup v ρ := by
        intro v hv
        apply Env.lookup_canon (Pattern.freeVars_nodup _ [])
        exact (Pattern.mem_freeVars _).mpr ⟨hv, by simp⟩
      have ha' : a.eval d.sig σ = some i := by
        rw [Expr.eval_agreeOn a (fun v hv => hag v (List.mem_union_iff.mpr (Or.inl hv)))]
        exact ha
      have hb' : b.eval d.sig σ = some i := by
        rw [Expr.eval_agreeOn b (fun v hv => hag v (List.mem_union_iff.mpr (Or.inr hv)))]
        exact hb
      have hmem : i ∈ ((d.addTerm i).addTerm i).terms :=
        FDatabase.mem_addTerm_of_mem (FDatabase.mem_addTerm_of_mem hi)
      have hcl : (i, i) ∈ ((d.addTerm i).addTerm i).closureF :=
        Egglog.FDatabase.mem_closureF_iff.mpr (Cong.direct (Or.inl ⟨rfl, hmem⟩))
      change patternHolds d (.eq a b) σ = true
      simp only [patternHolds, ha', hb']
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hcl, decide_eq_true ⟨i, hi, hcl⟩⟩

theorem mem_matchQuery_of_flatReads {d : FDatabase} {ρ : Env} {q : Query}
    (hv : ∀ v i, Env.lookup v ρ = some i → i ∈ d.valueTerms)
    (hr : ∀ p ∈ q, FlatRead d ρ p) :
    Env.canon (Query.freeVars q []) ρ ∈ matchQuery d q := by
  apply mem_matchQuery_of_lookup
  · intro v hm
    obtain ⟨p, hp, hv⟩ := Query.mem_freeVars.mp hm
    exact (hr p hp).bound hv
  · exact fun v _ i hi => hv v i hi
  · exact fun p hp => (hr p hp).holds

mutual

/-- Traverse the original expression in compiler order, binding one fresh id per application. -/
theorem freshEnv_of_liveQueryRead {d : FDatabase} {ρ₀ : Env} :
    ∀ {e : Expr} {i : Term}, LiveQueryRead d ρ₀ e i → ∀ n,
      ∃ σ, FreshEnv d n (encodeQueryExpr e n).2.2 σ ∧
        ∀ ρ, (∀ b ∈ σ, Env.lookup b.1 ρ = some b.2) →
          (∀ v j, Env.lookup v ρ₀ = some j → Env.lookup v ρ = some j) →
          Expr.eval d.sig (encodeQueryExpr e n).1 ρ = some i ∧
          ∀ p ∈ (encodeQueryExpr e n).2.1, FlatRead d ρ p
  | _, _, .lit, _ => ⟨[], .nil, fun _ _ _ => ⟨rfl, by simp [encodeQueryExpr]⟩⟩
  | _, _, .var hi, _ => ⟨[], .nil, fun _ _ hext => ⟨hext _ _ hi, by simp [encodeQueryExpr]⟩⟩
  | _, _, @LiveQueryRead.app _ _ f args is i hl hd hr hc, n => by
      obtain ⟨σ₀, hf₀, hp₀⟩ := freshEnv_of_liveQueryReadList hl n
      let m := (encodeQueryArgs args n).2.2
      have htail : FreshEnv d m (m + 1) [(freshVar m, i)] := by
        refine ⟨?_, by simp [Env.dom], ?_⟩
        · intro b hb
          obtain rfl := List.mem_singleton.mp hb
          exact ⟨m, Nat.le_refl _, Nat.lt_succ_self _, rfl⟩
        · intro b hb
          obtain rfl := List.mem_singleton.mp hb
          exact hc i (by simp)
      refine ⟨σ₀ ++ [(freshVar m, i)], ?_, fun ρ hσ hext => ?_⟩
      · change FreshEnv d n (m + 1) _
        exact hf₀.append htail (le_encodeQueryArgs_next args n) (Nat.le_succ m)
      · obtain ⟨hargs, hatoms⟩ := hp₀ ρ (fun b hb => hσ b (List.mem_append_left _ hb)) hext
        have him : Env.lookup (freshVar m) ρ = some i := hσ (freshVar m, i) (by simp)
        have hout : Expr.evalList d.sig [.var (freshVar m)] ρ = some [i] := by
          simp [Expr.evalList, Expr.eval, him]
        refine ⟨him, fun p hp => ?_⟩
        change p ∈ (encodeQueryArgs args n).2.1 ++ [_] at hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hatoms p hp
        · obtain rfl := List.mem_singleton.mp hp
          exact .entry (entryRead_table hd (Expr.evalList_length hargs).symm
            hargs hout hr hc)

@[inherit_doc freshEnv_of_liveQueryRead]
theorem freshEnv_of_liveQueryReadList {d : FDatabase} {ρ₀ : Env} :
    ∀ {es : List Expr} {is : List Term}, LiveQueryReadList d ρ₀ es is → ∀ n,
      ∃ σ, FreshEnv d n (encodeQueryArgs es n).2.2 σ ∧
        ∀ ρ, (∀ b ∈ σ, Env.lookup b.1 ρ = some b.2) →
          (∀ v j, Env.lookup v ρ₀ = some j → Env.lookup v ρ = some j) →
          Expr.evalList d.sig (encodeQueryArgs es n).1 ρ = some is ∧
          ∀ p ∈ (encodeQueryArgs es n).2.1, FlatRead d ρ p
  | _, _, .nil, _ => ⟨[], .nil, fun _ _ _ => ⟨rfl, by simp [encodeQueryArgs]⟩⟩
  | _, _, @LiveQueryReadList.cons _ _ e i es is he hl, n => by
      obtain ⟨σ₁, hf₁, hp₁⟩ := freshEnv_of_liveQueryRead he n
      obtain ⟨σ₂, hf₂, hp₂⟩ := freshEnv_of_liveQueryReadList hl (encodeQueryExpr e n).2.2
      refine ⟨σ₁ ++ σ₂, ?_, fun ρ hσ hext => ?_⟩
      · change FreshEnv d n (encodeQueryArgs es (encodeQueryExpr e n).2.2).2.2 _
        exact hf₁.append hf₂ (le_encodeQueryExpr_next e n) (le_encodeQueryArgs_next es _)
      · obtain ⟨he₁, ha₁⟩ := hp₁ ρ (fun b hb => hσ b (List.mem_append_left _ hb)) hext
        obtain ⟨he₂, ha₂⟩ := hp₂ ρ (fun b hb => hσ b (List.mem_append_right _ hb)) hext
        refine ⟨?_, fun p hp => ?_⟩
        · change (Expr.eval _ _ ρ).bind _ = _
          rw [he₁, Option.bind_some, he₂]; rfl
        · change p ∈ (encodeQueryExpr e n).2.1 ++ _ at hp
          exact (List.mem_append.mp hp).elim (ha₁ p) (ha₂ p)

end

theorem le_encodePattern_next (p : Pattern) (n : Nat) : n ≤ (encodePattern p n).2 := by
  cases p with
  | expr e => exact le_encodeQueryExpr_next e n
  | eq a b =>
      change n ≤ (encodeQueryExpr b (encodeQueryExpr a n).2.2).2.2
      exact (le_encodeQueryExpr_next a n).trans (le_encodeQueryExpr_next b _)

theorem le_encodeQuery_next (q : Query) (n : Nat) : n ≤ (encodeQuery q n).2 := by
  induction q generalizing n with
  | nil => exact Nat.le_refl _
  | cons p ps ih =>
      exact (le_encodePattern_next p n).trans (ih (encodePattern p n).2)

/-- Preserve the compiler's left-then-right order for equalities, including existence. -/
theorem freshEnv_of_livePatternRead {d : FDatabase} {ρ₀ : Env}
    (hv : ∀ v i, Env.lookup v ρ₀ = some i → i ∈ d.valueTerms) :
    ∀ {p : Pattern}, LivePatternRead d ρ₀ p → p.Grounded → ∀ n,
      ∃ σ, FreshEnv d n (encodePattern p n).2 σ ∧
        ∀ ρ, (∀ b ∈ σ, Env.lookup b.1 ρ = some b.2) →
          (∀ v j, Env.lookup v ρ₀ = some j → Env.lookup v ρ = some j) →
          ∀ a ∈ (encodePattern p n).1, FlatRead d ρ a
  | _, .expr hr, _, n => by
      obtain ⟨σ, hf, hp⟩ := freshEnv_of_liveQueryRead hr n
      exact ⟨σ, hf, fun ρ hσ hext => (hp ρ hσ hext).2⟩
  | _, @LivePatternRead.eq _ _ a b i ha hb, hg, n => by
      obtain ⟨σ₁, hf₁, hp₁⟩ := freshEnv_of_liveQueryRead ha n
      obtain ⟨σ₂, hf₂, hp₂⟩ := freshEnv_of_liveQueryRead hb (encodeQueryExpr a n).2.2
      have hi : i ∈ d.terms := Egglog.FDatabase.mem_terms_of_mem_valueTerms
        (hg.elim (ha.output_value hv) (hb.output_value hv))
      refine ⟨σ₁ ++ σ₂, ?_, fun ρ hσ hext p hp => ?_⟩
      · change FreshEnv d n (encodeQueryExpr b (encodeQueryExpr a n).2.2).2.2 _
        exact hf₁.append hf₂ (le_encodeQueryExpr_next a n) (le_encodeQueryExpr_next b _)
      · obtain ⟨he₁, ha₁⟩ := hp₁ ρ (fun b hb => hσ b (List.mem_append_left _ hb)) hext
        obtain ⟨he₂, ha₂⟩ := hp₂ ρ (fun b hb => hσ b (List.mem_append_right _ hb)) hext
        change p ∈ (_ ++ _) ++ [_] at hp
        rcases List.mem_append.mp hp with hp | hp
        · exact (List.mem_append.mp hp).elim (ha₁ p) (ha₂ p)
        · obtain rfl := List.mem_singleton.mp hp
          exact .eq he₁ he₂ hi

/-- Adjacent original patterns receive disjoint ranges from the same variable supply. -/
theorem freshEnv_of_liveQuery {d : FDatabase} {ρ₀ : Env}
    (hv : ∀ v i, Env.lookup v ρ₀ = some i → i ∈ d.valueTerms) :
    ∀ q : Query, (∀ p ∈ q, LivePatternRead d ρ₀ p) → (∀ p ∈ q, p.Grounded) → ∀ n,
      ∃ σ, FreshEnv d n (encodeQuery q n).2 σ ∧
        ∀ ρ, (∀ b ∈ σ, Env.lookup b.1 ρ = some b.2) →
          (∀ v j, Env.lookup v ρ₀ = some j → Env.lookup v ρ = some j) →
          ∀ p ∈ (encodeQuery q n).1, FlatRead d ρ p
  | [], _, _, _ => ⟨[], .nil, fun _ _ _ => by simp [encodeQuery]⟩
  | p :: ps, hr, hg, n => by
      obtain ⟨σ₁, hf₁, hp₁⟩ :=
        freshEnv_of_livePatternRead hv (hr p List.mem_cons_self) (hg p List.mem_cons_self) n
      obtain ⟨σ₂, hf₂, hp₂⟩ := freshEnv_of_liveQuery hv ps
        (fun p hp => hr p (List.mem_cons_of_mem _ hp))
        (fun p hp => hg p (List.mem_cons_of_mem _ hp)) (encodePattern p n).2
      refine ⟨σ₁ ++ σ₂, ?_, fun ρ hσ hext a ha => ?_⟩
      · exact hf₁.append hf₂ (le_encodePattern_next p n) (le_encodeQuery_next ps _)
      · change a ∈ (encodePattern p n).1 ++ _ at ha
        exact (List.mem_append.mp ha).elim
          (hp₁ ρ (fun b hb => hσ b (List.mem_append_left _ hb)) hext a)
          (hp₂ ρ (fun b hb => hσ b (List.mem_append_right _ hb)) hext a)

/-- The generated substitution actually occurs in the executable flattened-query matcher. -/
theorem matchQuery_of_liveQuery {d : FDatabase} {ρ₀ : Env} {q : Query}
    (hv : ∀ v i, Env.lookup v ρ₀ = some i → i ∈ d.valueTerms)
    (hn : ∀ b ∈ ρ₀, ¬ "@".isPrefixOf b.1 = true)
    (hr : ∀ p ∈ q, LivePatternRead d ρ₀ p) (hg : ∀ p ∈ q, p.Grounded) (n : Nat) :
    ∃ ρ, Env.canon (Query.freeVars (encodeQuery q n).1 []) ρ ∈ matchQuery d (encodeQuery q n).1 ∧
      ∀ v i, Env.lookup v ρ₀ = some i → Env.lookup v ρ = some i := by
  obtain ⟨σ, hf, hp⟩ := freshEnv_of_liveQuery hv q hr hg n
  have hext : ∀ v i, Env.lookup v ρ₀ = some i → Env.lookup v (ρ₀ ++ σ) = some i :=
    fun _ _ hi => Env.lookup_append_of_some hi
  have hσ : ∀ b ∈ σ, Env.lookup b.1 (ρ₀ ++ σ) = some b.2 := by
    intro b hb
    obtain ⟨k, _, _, hk⟩ := hf.fresh b hb
    have hnone : Env.lookup b.1 ρ₀ = none := Env.lookup_eq_none_iff.mpr fun hmem => by
      obtain ⟨t, ht⟩ := Env.mem_dom_iff.mp hmem
      exact hn (b.1, t) ht (hk ▸ atPrefix_freshVar k)
    rw [Env.lookup_append_of_none hnone]
    exact Env.lookup_of_mem_nodup hb hf.nodup
  refine ⟨ρ₀ ++ σ, mem_matchQuery_of_flatReads ?_ (hp _ hσ hext), hext⟩
  intro v i hi
  cases hlk : Env.lookup v ρ₀ with
  | none =>
      rw [Env.lookup_append_of_none hlk] at hi
      exact hf.valued (v, i) (Env.mem_of_lookup hi)
  | some j =>
      rw [Env.lookup_append_of_some hlk] at hi
      exact (Option.some.inj hi) ▸ hv v j hlk

/-- Forward query completeness at a rebuilt target: the executable flattened query
matches, and its substitution retains canonical readings of the original source values. -/
theorem encodedQuery_match_of_source {P : Program} {d : FDatabase} {src querySrc : Database}
    (h : Rebuilt d) (htables : RebuildTables P d) (hs : SoundTerms d src)
    (hb : src.TermsBuild) (hctors : src.CtorsIn P)
    (hc : ∀ f, src.sig.IsCtor f → d.sig.IsCtor f) (hw : src.WF)
    (hcs : querySrc.sig.AllConstructors) (hun : UnionsRead d.toDatabase querySrc)
    (hex : ∀ t ∈ querySrc.terms, ∃ e, ViewRepr d.toDatabase t e) {σ : Env} {q : Query}
    (hof : ∀ p ∈ q, p.OrderingFree) (hk : Query.VarsKeyed q)
    (hg : ∀ p ∈ q, p.Grounded) (hn : ∀ v ∈ Query.vars q, ¬ "@".isPrefixOf v = true)
    (hm : ValidQuerySubst querySrc q σ) (n : Nat) :
    ∃ ρ, ρ ∈ matchQuery d (encodeQuery q n).1 ∧ Env.CanonicalReads d σ ρ := by
  obtain ⟨ρ₀, hρ₀, hdom, hreads, hv⟩ :=
    exists_live_query h htables hs hb hctors hc hw hcs hun hex hof hk hm
  have hvars : ∀ v ∈ Env.dom σ, v ∈ Query.vars q := by
    intro v hv
    obtain ⟨p, hp, hfv⟩ := hm.mem_dom_iff.mp hv
    exact Query.mem_vars.mpr ⟨p, hp, ((Pattern.mem_freeVars p).mp hfv).1⟩
  have hn₀ : ∀ b ∈ ρ₀, ¬ "@".isPrefixOf b.1 = true := by
    intro b hb
    exact hn b.1 (hvars b.1 (hdom ▸ Env.mem_dom_of_mem hb))
  obtain ⟨ρ, hmatch, hext⟩ := matchQuery_of_liveQuery hv hn₀ hreads hg n
  refine ⟨_, hmatch, fun v t ht => ?_⟩
  obtain ⟨i, hi, hrep, hroot⟩ := hρ₀ v t ht
  obtain ⟨p, hp, harg⟩ := hk v (hvars v (Env.mem_dom_of_mem (Env.mem_of_lookup ht)))
  have hvq := mem_vars_encodeQuery_of_argVar q n hof hp harg
  obtain ⟨p', hp', hvp'⟩ := Query.mem_vars.mp hvq
  have hvfree : v ∈ Query.freeVars (encodeQuery q n).1 [] :=
    Query.mem_freeVars.mpr ⟨p', hp', ((Pattern.mem_freeVars p').mpr ⟨hvp', by simp⟩)⟩
  refine ⟨i, ?_, hrep, hroot⟩
  rw [Env.lookup_canon (Query.freeVars_nodup _ _) hvfree]
  exact hext v i hi

end Egglog.Congruence
