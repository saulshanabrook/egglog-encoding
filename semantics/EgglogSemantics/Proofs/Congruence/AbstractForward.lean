import EgglogSemantics.Proofs.Congruence.QueryVars
import EgglogSemantics.Proofs.Congruence.AbstractQuery
import EgglogSemantics.Proofs.Congruence.Flatten
import EgglogSemantics.Proofs.Source.FreshBindings

/-! Completeness of flattened queries over mathematical databases. -/

namespace Egglog.Congruence.Abstract

/-- A view read refers to a declared target table. -/
def ViewDeclared (d : Database) : Prop :=
  ∀ f cs e, d.Out (viewName f) cs [e] →
    d.sig (viewName f) = some (tableDecl cs.length)

inductive FlatRead (d : Database) (ρ : Env) : Pattern → Prop where
  | entry {f : FnName} {es : List Expr} {ts : List Term} :
      (∃ decl, d.sig f = some decl ∧
        (decl.merge = none ∨ es.length = decl.entryWidth)) →
      Expr.evalList d.sig es ρ = some ts →
      Term.app f ts ∈ d.terms → FlatRead d ρ (.expr (.app f es))
  | eq {a b : Expr} {i : Term} :
      a.eval d.sig ρ = some i → b.eval d.sig ρ = some i → i ∈ d.values → FlatRead d ρ (.eq a b)

theorem FlatRead.bound {d : Database} {ρ : Env} {p : Pattern} (h : FlatRead d ρ p) (ho : p.OrderingFree)
    {v : Var} (hv : v ∈ p.vars) : (Env.lookup v ρ).isSome := by
  cases h with
  | entry _ he _ => exact Expr.lookup_isSome_of_mem_varsList ho he hv
  | eq ha hb _ =>
      rcases List.mem_union_iff.mp hv with hv | hv
      · exact Expr.lookup_isSome_of_mem_vars ho.1 ha hv
      · exact Expr.lookup_isSome_of_mem_vars ho.2 hb hv

theorem FlatRead.holds {d : Database} {ρ : Env} {p : Pattern} (h : FlatRead d ρ p) :
    Matches d p ρ := by
  cases h with
  | @entry f es ts hf he ht =>
      obtain ⟨decl, hd, hw⟩ := hf
      exact .atom (by rw [Expr.evalAtom_app_decl hd hw, he]; rfl) (Database.toCong ht)
  | @eq a b i ha hb ht => exact .equal ha hb (Database.toCong ht.1)

theorem validQuerySubst_of_flatReads {d : Database} {ρ : Env} {q : Query}
    (hv : ∀ v i, Env.lookup v ρ = some i → i ∈ d.values)
    (hr : ∀ p ∈ q, FlatRead d ρ p) (ho : ∀ p ∈ q, p.OrderingFree) :
    ∃ σ, ValidQuerySubst d q σ ∧
      ∀ v ∈ Query.vars q, Env.lookup v σ = Env.lookup v ρ := by
  apply validQuerySubst_of_matches ?_ (fun p hp => (hr p hp).holds)
  intro v hvq
  obtain ⟨p, hp, hvp⟩ := Query.mem_vars.mp hvq
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp ((hr p hp).bound (ho p hp) hvp)
  exact ⟨t, ht, hv v t ht⟩

mutual

/-- Traverse the original expression in compiler order, binding one fresh id per application. -/
theorem freshEnv_of_queryRead {d : Database} (hd : d.Diag) (hstore : d.StoreOk)
    (hdecl : ViewDeclared d) {ρ₀ : Env}
    (hval : ∀ v i, Env.lookup v ρ₀ = some i → i ∈ d.values) :
    ∀ {e : Expr} {i : Term}, QueryRead d ρ₀ e i → ∀ n,
      ∃ σ, FreshBindings d.values n (encodeQueryExpr e n).2.2 σ ∧
        ∀ ρ, (∀ b ∈ σ, Env.lookup b.1 ρ = some b.2) →
          (∀ v j, Env.lookup v ρ₀ = some j → Env.lookup v ρ = some j) →
          Expr.eval d.sig (encodeQueryExpr e n).1 ρ = some i ∧
          ∀ p ∈ (encodeQueryExpr e n).2.1, FlatRead d ρ p
  | _, _, .lit, _ => ⟨[], .nil, fun _ _ _ => ⟨rfl, by simp [encodeQueryExpr]⟩⟩
  | _, _, .var hi, _ => ⟨[], .nil, fun _ _ hext => ⟨hext _ _ hi,
      by simp [encodeQueryExpr]⟩⟩
  | _, _, @QueryRead.app _ _ f args is i hl ho, n => by
      have ht := ho.term hd
      have hc := out_values hd hstore ho
      obtain ⟨σ₀, hf₀, hp₀⟩ := freshEnv_of_queryReadList hd hstore hdecl hval hl n
      let m := (encodeQueryArgs args n).2.2
      have htail : FreshBindings d.values m (m + 1) [(freshVar m, i)] := by
        refine ⟨?_, by simp [Env.dom], ?_⟩
        · intro b hb
          obtain rfl := List.mem_singleton.mp hb
          exact ⟨m, Nat.le_refl _, Nat.lt_succ_self _, rfl⟩
        · intro b hb
          obtain rfl := List.mem_singleton.mp hb
          exact hc i (by simp)
      refine ⟨σ₀ ++ [(freshVar m, i)], ?_, fun ρ hσ hext => ?_⟩
      · change FreshBindings d.values n (m + 1) _
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
          exact .entry ⟨tableDecl is.length, hdecl f is i ho, Or.inr (by
            have hlen := Expr.evalList_length hargs
            simp [FnDecl.entryWidth, tableDecl, ← hlen])⟩
            (by rw [Expr.evalList_append_map, hargs, hout]; rfl) ht

@[inherit_doc freshEnv_of_queryRead]
theorem freshEnv_of_queryReadList {d : Database} (hd : d.Diag) (hstore : d.StoreOk)
    (hdecl : ViewDeclared d) {ρ₀ : Env}
    (hval : ∀ v i, Env.lookup v ρ₀ = some i → i ∈ d.values) :
    ∀ {es : List Expr} {is : List Term}, QueryReadList d ρ₀ es is → ∀ n,
      ∃ σ, FreshBindings d.values n (encodeQueryArgs es n).2.2 σ ∧
        ∀ ρ, (∀ b ∈ σ, Env.lookup b.1 ρ = some b.2) →
          (∀ v j, Env.lookup v ρ₀ = some j → Env.lookup v ρ = some j) →
          Expr.evalList d.sig (encodeQueryArgs es n).1 ρ = some is ∧
          ∀ p ∈ (encodeQueryArgs es n).2.1, FlatRead d ρ p
  | _, _, .nil, _ => ⟨[], .nil, fun _ _ _ => ⟨rfl, by simp [encodeQueryArgs]⟩⟩
  | _, _, @QueryReadList.cons _ _ e i es is he hl, n => by
      obtain ⟨σ₁, hf₁, hp₁⟩ := freshEnv_of_queryRead hd hstore hdecl hval he n
      obtain ⟨σ₂, hf₂, hp₂⟩ :=
        freshEnv_of_queryReadList hd hstore hdecl hval hl (encodeQueryExpr e n).2.2
      refine ⟨σ₁ ++ σ₂, ?_, fun ρ hσ hext => ?_⟩
      · change FreshBindings d.values n (encodeQueryArgs es (encodeQueryExpr e n).2.2).2.2 _
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
theorem freshEnv_of_patternRead {d : Database} (hd : d.Diag) (hstore : d.StoreOk)
    (hdecl : ViewDeclared d) {ρ₀ : Env}
    (hv : ∀ v i, Env.lookup v ρ₀ = some i → i ∈ d.values) :
    ∀ {p : Pattern}, PatternRead d ρ₀ p → p.Grounded → ∀ n,
      ∃ σ, FreshBindings d.values n (encodePattern p n).2 σ ∧
        ∀ ρ, (∀ b ∈ σ, Env.lookup b.1 ρ = some b.2) →
          (∀ v j, Env.lookup v ρ₀ = some j → Env.lookup v ρ = some j) →
          ∀ a ∈ (encodePattern p n).1, FlatRead d ρ a
  | _, .expr hr, _, n => by
      obtain ⟨σ, hf, hp⟩ := freshEnv_of_queryRead hd hstore hdecl hv hr n
      exact ⟨σ, hf, fun ρ hσ hext => (hp ρ hσ hext).2⟩
  | _, @PatternRead.eq _ _ a b i ha hb, hg, n => by
      obtain ⟨σ₁, hf₁, hp₁⟩ := freshEnv_of_queryRead hd hstore hdecl hv ha n
      obtain ⟨σ₂, hf₂, hp₂⟩ := freshEnv_of_queryRead hd hstore hdecl hv hb (encodeQueryExpr a n).2.2
      have hi : i ∈ d.values :=
        hg.elim (QueryRead.output_value hd hstore ha hv) (QueryRead.output_value hd hstore hb hv)
      refine ⟨σ₁ ++ σ₂, ?_, fun ρ hσ hext p hp => ?_⟩
      · change FreshBindings d.values n (encodeQueryExpr b (encodeQueryExpr a n).2.2).2.2 _
        exact hf₁.append hf₂ (le_encodeQueryExpr_next a n) (le_encodeQueryExpr_next b _)
      · obtain ⟨he₁, ha₁⟩ := hp₁ ρ (fun b hb => hσ b (List.mem_append_left _ hb)) hext
        obtain ⟨he₂, ha₂⟩ := hp₂ ρ (fun b hb => hσ b (List.mem_append_right _ hb)) hext
        change p ∈ (_ ++ _) ++ [_] at hp
        rcases List.mem_append.mp hp with hp | hp
        · exact (List.mem_append.mp hp).elim (ha₁ p) (ha₂ p)
        · obtain rfl := List.mem_singleton.mp hp
          exact .eq he₁ he₂ hi

/-- Adjacent original patterns receive disjoint ranges from the same variable supply. -/
theorem freshEnv_of_query {d : Database} (hd : d.Diag) (hstore : d.StoreOk)
    (hdecl : ViewDeclared d) {ρ₀ : Env}
    (hv : ∀ v i, Env.lookup v ρ₀ = some i → i ∈ d.values) :
    ∀ q : Query, (∀ p ∈ q, PatternRead d ρ₀ p) → (∀ p ∈ q, p.Grounded) → ∀ n,
      ∃ σ, FreshBindings d.values n (encodeQuery q n).2 σ ∧
        ∀ ρ, (∀ b ∈ σ, Env.lookup b.1 ρ = some b.2) →
          (∀ v j, Env.lookup v ρ₀ = some j → Env.lookup v ρ = some j) →
          ∀ p ∈ (encodeQuery q n).1, FlatRead d ρ p
  | [], _, _, _ => ⟨[], .nil, fun _ _ _ => by simp [encodeQuery]⟩
  | p :: ps, hr, hg, n => by
      obtain ⟨σ₁, hf₁, hp₁⟩ :=
        freshEnv_of_patternRead hd hstore hdecl hv
          (hr p List.mem_cons_self) (hg p List.mem_cons_self) n
      obtain ⟨σ₂, hf₂, hp₂⟩ := freshEnv_of_query hd hstore hdecl hv ps
        (fun p hp => hr p (List.mem_cons_of_mem _ hp))
        (fun p hp => hg p (List.mem_cons_of_mem _ hp)) (encodePattern p n).2
      refine ⟨σ₁ ++ σ₂, ?_, fun ρ hσ hext a ha => ?_⟩
      · exact hf₁.append hf₂ (le_encodePattern_next p n) (le_encodeQuery_next ps _)
      · change a ∈ (encodePattern p n).1 ++ _ at ha
        exact (List.mem_append.mp ha).elim
          (hp₁ ρ (fun b hb => hσ b (List.mem_append_left _ hb)) hext a)
          (hp₂ ρ (fun b hb => hσ b (List.mem_append_right _ hb)) hext a)

/-- Fresh bindings for all application occurrences coexist with the original variables. -/
theorem matchQuery_of_query {d : Database} (hd : d.Diag) (hstore : d.StoreOk)
    (hdecl : ViewDeclared d) {ρ₀ : Env} {q : Query}
    (hv : ∀ v i, Env.lookup v ρ₀ = some i → i ∈ d.values)
    (hn : ∀ b ∈ ρ₀, ¬ "@".isPrefixOf b.1 = true)
    (hr : ∀ p ∈ q, PatternRead d ρ₀ p) (hg : ∀ p ∈ q, p.Grounded)
    (ho : ∀ p ∈ q, p.OrderingFree) (n : Nat) :
    ∃ σ ρ, ValidQuerySubst d (encodeQuery q n).1 σ ∧
      (∀ v ∈ Query.vars (encodeQuery q n).1, Env.lookup v σ = Env.lookup v ρ) ∧
      ∀ v i, Env.lookup v ρ₀ = some i → Env.lookup v ρ = some i := by
  obtain ⟨σ, hf, hp⟩ := freshEnv_of_query hd hstore hdecl hv q hr hg n
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
  have hval : ∀ v i, Env.lookup v (ρ₀ ++ σ) = some i → i ∈ d.values := by
    intro v i hi
    cases hlk : Env.lookup v ρ₀ with
    | none =>
        rw [Env.lookup_append_of_none hlk] at hi
        exact hf.valued (v, i) (Env.mem_of_lookup hi)
    | some j =>
        rw [Env.lookup_append_of_some hlk] at hi
        exact (Option.some.inj hi) ▸ hv v j hlk
  obtain ⟨τ, hτ, hag⟩ := validQuerySubst_of_flatReads hval (hp _ hσ hext)
    (fun p hp => (encodeQuery_flat q n ho p hp).orderingFree)
  exact ⟨τ, ρ₀ ++ σ, hτ, hag, hext⟩

/-- A source match has a compiled match retaining canonical readings of each source
binding. The source being matched may precede the source justifying target entries. -/
theorem encodedQuery_match_of_source {d src querySrc : Database}
    (h : Rebuilt d) (hd : d.Diag) (hstore : d.StoreOk) (hdecl : ViewDeclared d)
    (he : EdgesSound d src) (hw : src.WF)
    (hcs : querySrc.sig.AllConstructors) (hun : UnionsRead d querySrc)
    (hex : ∀ t ∈ querySrc.terms, ∃ e, ViewRepr d t e) {σ : Env} {q : Query}
    (hof : ∀ p ∈ q, p.OrderingFree) (hk : Query.VarsKeyed q)
    (hg : ∀ p ∈ q, p.Grounded) (hn : ∀ v ∈ Query.vars q, ¬ "@".isPrefixOf v = true)
    (hm : ValidQuerySubst querySrc q σ) (n : Nat) :
    ∃ ρ, ValidQuerySubst d (encodeQuery q n).1 ρ ∧ CanonicalReads d σ ρ := by
  obtain ⟨ρ₀, hρ₀, hdom, hreads, hv⟩ := exists_queryRead h hd hstore he hw hcs hun hex hof hk hm
  have hvars : ∀ v ∈ Env.dom σ, v ∈ Query.vars q := by
    intro v hv
    obtain ⟨p, hp, hfv⟩ := hm.mem_dom_iff.mp hv
    exact Query.mem_vars.mpr ⟨p, hp, ((Pattern.mem_freeVars p).mp hfv).1⟩
  have hn₀ : ∀ b ∈ ρ₀, ¬ "@".isPrefixOf b.1 = true := by
    intro b hb
    exact hn b.1 (hvars b.1 (hdom ▸ Env.mem_dom_of_mem hb))
  obtain ⟨ρ, ρ', hmatch, hag, hext⟩ := matchQuery_of_query hd hstore hdecl hv hn₀ hreads hg hof n
  refine ⟨ρ, hmatch, fun v t ht => ?_⟩
  obtain ⟨i, hi, hrep, hroot⟩ := hρ₀ v t ht
  obtain ⟨p, hp, harg⟩ := hk v (hvars v (Env.mem_dom_of_mem (Env.mem_of_lookup ht)))
  refine ⟨i, ?_, hrep, hroot⟩
  rw [hag v (mem_vars_encodeQuery_of_argVar q n hof hp harg)]
  exact hext v i hi

/-- At a represented, rebuilt boundary, a complete existential query has a match on one
side exactly when its flattening has a match on the other. -/
theorem Rebuilt.queryHolds_iff {d src : Database} (h : Rebuilt d) (hd : d.Diag)
    (hstore : d.StoreOk) (htables : ViewTables d) (hdecl : ViewDeclared d)
    (he : EdgesSound d src) (hs : ViewsSound d src)
    (hw : src.WF) (hb : src.TermsBuild) (hc : src.sig.AllConstructors)
    (hex : ∀ t ∈ src.terms, ∃ e, ViewRepr d t e) (hun : UnionsJoined d src)
    {q : Query} (hof : ∀ p ∈ q, p.OrderingFree) (hg : ∀ p ∈ q, p.Grounded)
    (hk : Query.VarsKeyed q) (hn : ∀ v ∈ Query.vars q, ¬ "@".isPrefixOf v = true)
    (n : Nat) : QueryHolds src q ↔ QueryHolds d (encodeQuery q n).1 := by
  simp only [queryHolds_iff_validQuerySubst]
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨ρ, _, hdom, hr, hv⟩ := exists_queryRead h hd hstore he hw hc
      (unionsRead_of_unionsJoined (h.viewLeader he hw) hun) hex hof hk hσ
    have hnames : ∀ b ∈ ρ, ¬ "@".isPrefixOf b.1 = true := by
      intro b hb
      have hm : b.1 ∈ Env.dom σ := hdom ▸ Env.mem_dom_of_mem hb
      obtain ⟨p, hp, hvp⟩ := hσ.mem_dom_iff.mp hm
      exact hn b.1 (Query.mem_vars.mpr ⟨p, hp, (p.mem_freeVars.mp hvp).1⟩)
    obtain ⟨τ, _, ht, _, _⟩ := matchQuery_of_query hd hstore hdecl hv hnames hr hg hof n
    exact ⟨τ, ht⟩
  · rintro ⟨σ, hσ⟩
    obtain ⟨τ, ht, _, _⟩ := sourceMatch_of_encodedQuery hb hw hs hd hstore htables hof hg hk hσ
    exact ⟨τ, ht⟩

end Egglog.Congruence.Abstract
