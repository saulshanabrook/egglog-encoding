import EgglogSemantics.Proofs.Congruence.LiveCoverage
import EgglogSemantics.Proofs.Congruence.ActionExprs
import EgglogSemantics.Proofs.Diagonal
import EgglogSemantics.Proofs.Source.Domain

/-! Compiled source actions preserve represented facts using mathematical evaluation. -/

namespace Egglog.Congruence.Abstract

open Live

def EnvReads (d : Database) (σ ρ : Env) : Prop :=
  ∀ v t, Env.lookup v σ = some t →
    ∃ i, Env.lookup v ρ = some i ∧ i.IsValue d.sig ∧ Repr d t i

theorem EnvReads.mono {d e : Database} {σ ρ : Env} (h : EnvReads d σ ρ)
    (hsig : d.sig = e.sig) (hc : d.entries ⊆ e.entries) : EnvReads e σ ρ := by
  intro v t ht
  obtain ⟨i, hi, hv, hr⟩ := h v t ht
  exact ⟨i, hi, hsig ▸ hv, hr.mono hc⟩

private theorem evalActions_append_eq {d m e : Database} {as bs : List Action}
    (ha : evalActions d as = some m) (hb : evalActions m bs = some e) :
    evalActions d (as ++ bs) = some e := by
  induction as generalizing d with
  | nil => obtain rfl := Option.some.inj ha; exact hb
  | cons a as ih =>
      obtain ⟨n, hn, ha⟩ := Option.bind_eq_some_iff.mp ha
      simpa only [List.cons_append, evalActions, hn, Option.bind_some] using ih ha

private theorem evalAction_atom_of_eval {d : Database} {f : FnName} {es : List Expr}
    {ts : List Term} {k : Nat} (hf : d.sig f = some (tableDecl k))
    (hw : es.length = k + 1) (he : Expr.evalList d.sig es d.env = some ts) :
    evalAction d (.expr (.app f es)) = some (d.addTerm (.app f ts)) := by
  rw [evalAction, Expr.evalAtom_app_decl hf
    (Or.inr (by simpa [tableDecl, FnDecl.entryWidth] using hw)), he]
  rfl

private theorem row_addTerm {d : Database} (f : FnName) (cs : List Term) (i : Term)
    (hf : d.sig f = some (tableDecl cs.length)) :
    Entry.mk f cs [i] ∈ (d.addTerm (.app f (cs ++ [i]))).entries := by
  apply Database.mem_addTerm_entries.mpr
  exact Or.inr ⟨⟨tableDecl cs.length, hf, by simp [tableDecl], rfl, rfl⟩, .refl _⟩

private theorem write_self {d : Database} {e : Expr} {t : Term}
    (huf : d.sig ufName = some (tableDecl 1)) (he : e.eval d.sig d.env = some t) :
    evalAction d (.expr (.app ufName [e, e])) = some (d.addTerm (.app ufName [t, t])) :=
  evalAction_atom_of_eval huf rfl (by simp [Expr.evalList, he])

mutual

/-- A source build executes at a reading substitution and represents its source result.
The target id is the head expression evaluated at target ids, not the source term itself. -/
theorem encodeBuild_reads {sig : Signature} {σ : Env} :
    ∀ (e : Expr) {t : Term} {d : Database}, e.OrderingFree →
      (∀ f ∈ e.fns, sig.IsCtor f → d.sig.IsCtor f) →
      (∀ fk ∈ e.ctors, d.sig (viewName fk.1) = some (tableDecl fk.2)) →
      d.sig ufName = some (tableDecl 1) → EnvReads d σ d.env → e.eval sig σ = some t →
      ∃ i d', e.eval d.sig d.env = some i ∧
        evalActions d (encodeBuild e) = some d' ∧ Repr d' t i
  | .lit l, _, d, _, _, _, huf, _, he => by
      obtain rfl := Option.some.inj he
      exact ⟨.lit l, d.addTerm (.app ufName [.lit l, .lit l]), rfl,
        by simp [encodeBuild, evalActions, write_self huf (e := .lit l) rfl], .lit⟩
  | .var v, t, d, _, _, _, huf, hρ, he => by
      obtain ⟨i, hi, _hv, hr⟩ := hρ v t he
      have hi' : (Expr.var v).eval d.sig d.env = some i :=
        hi
      have hw := write_self huf hi'
      exact ⟨i, _, hi', by simp [encodeBuild, evalActions, hw],
        hr.mono (evalAction_entries_subset hw)⟩
  | .min _ _, _, _, hp, _, _, _, _, _ => (Expr.not_orderingFree_min hp).elim
  | .ite _ _ _ _, _, _, hp, _, _, _, _, _ => (Expr.not_orderingFree_ite hp).elim
  | .app f args, t, d, hp, hc, hd, huf, hρ, he => by
      have hctor : sig.IsCtor f := by
        by_contra hn
        rw [Expr.eval_app_not_ctor hn] at he
        contradiction
      rw [Expr.eval_app_ctor hctor] at he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      obtain ⟨is, m, his, hm, hviews⟩ := encodeBuildArgs_reads args
        (Expr.orderingFree_app hp)
        (fun g hg => hc g (by simp [Expr.fns, hg]))
        (fun fk hk => hd fk (List.mem_cons_of_mem _ hk)) huf hρ hts
      have htarget : (Expr.app f args).eval d.sig d.env = some (.app f is) := by
        rw [Expr.eval_app_ctor (hc f (by simp [Expr.fns]) hctor), his]; rfl
      have hsig := evalActions_sig hm
      have henv := evalActions_env hm
      have hcols : Expr.evalList m.sig (args ++ [.app f args]) m.env =
          some (is ++ [.app f is]) := by
        rw [hsig, henv]
        rw [Expr.evalList_append_map, his]
        simp only [Expr.evalList, htarget, Option.bind_some, Option.map_some]
      have hview : m.sig (viewName f) = some (tableDecl is.length) := by
        rw [hsig, Expr.evalList_length his]
        exact hd (f, args.length) List.mem_cons_self
      have hwrite := evalAction_atom_of_eval
        (by rw [hsig]; exact hd (f, args.length) List.mem_cons_self)
        (by simp) hcols
      have hself := write_self (d := m.addTerm (.app (viewName f) (is ++ [.app f is])))
        (by change m.sig ufName = _; rw [hsig]; exact huf)
        (by change (Expr.app f args).eval m.sig m.env = _; rw [hsig, henv]; exact htarget)
      refine ⟨.app f is,
        (m.addTerm (.app (viewName f) (is ++ [.app f is]))).addTerm
          (.app ufName [.app f is, .app f is]),
        htarget, evalActions_append_eq hm ?_, ?_⟩
      · simp only [evalActions, hwrite, Option.bind_some, hself]
      · apply Repr.mono (evalAction_entries_subset hself)
        exact .app (hviews.mono (evalAction_entries_subset hwrite))
          (row_addTerm (viewName f) is (.app f is) hview)

@[inherit_doc encodeBuild_reads]
theorem encodeBuildArgs_reads {sig : Signature} {σ : Env} :
    ∀ (es : List Expr) {ts : List Term} {d : Database}, Expr.OrderingFreeList es →
      (∀ f ∈ Expr.fnsList es, sig.IsCtor f → d.sig.IsCtor f) →
      (∀ fk ∈ Expr.ctorsList es, d.sig (viewName fk.1) = some (tableDecl fk.2)) →
      d.sig ufName = some (tableDecl 1) → EnvReads d σ d.env → Expr.evalList sig es σ = some ts →
      ∃ is d', Expr.evalList d.sig es d.env = some is ∧
        evalActions d (encodeBuildArgs es) = some d' ∧ ReprList d' ts is
  | [], _, d, _, _, _, _, _, he => by
      obtain rfl := Option.some.inj he
      exact ⟨[], d, rfl, rfl, .nil⟩
  | e :: es, _, d, hp, hc, hd, huf, hρ, he => by
      obtain ⟨t, ht, he⟩ := Option.bind_eq_some_iff.mp he
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp he
      obtain ⟨i, m, hi, hm, hv⟩ := encodeBuild_reads e (Expr.orderingFreeList_cons hp).1
        (fun f hf => hc f (by simp [Expr.fnsList, hf]))
        (fun fk hk => hd fk (by simp [Expr.ctorsList, hk])) huf hρ ht
      have hsig := evalActions_sig hm
      have henv := evalActions_env hm
      obtain ⟨is, d', his, hr, hvs⟩ := encodeBuildArgs_reads (d := m) es
        (Expr.orderingFreeList_cons hp).2
        (fun f hf hctor => by rw [hsig]; exact hc f (by simp [Expr.fnsList, hf]) hctor)
        (fun fk hk => by rw [hsig]; exact hd fk (by simp [Expr.ctorsList, hk]))
        (by rw [hsig]; exact huf)
        (by rw [henv]; exact hρ.mono hsig.symm (evalActions_entries_subset hm)) hts
      rw [hsig, henv] at his
      refine ⟨i :: is, d', ?_, evalActions_append_eq hm hr,
        .cons (hv.mono (evalActions_entries_subset hr)) hvs⟩
      simp only [Expr.evalList, hi, Option.bind_some, his, Option.map_some]

end

/-- The endpoint readings of an encoded union are joined by an explicit UF entry: the link
from the larger id, the other link being a self-loop. -/
theorem encodeUnion_reads {sig : Signature} {σ : Env} {a b : Expr} {ta tb : Term}
    {d : Database} (hp : ∀ e ∈ [a, b], e.OrderingFree)
    (hc : ∀ e ∈ [a, b], ∀ f ∈ e.fns, sig.IsCtor f → d.sig.IsCtor f)
    (hd : ∀ e ∈ [a, b], ∀ fk ∈ e.ctors, d.sig (viewName fk.1) = some (tableDecl fk.2))
    (huf : d.sig ufName = some (tableDecl 1)) (hρ : EnvReads d σ d.env)
    (ha : a.eval sig σ = some ta) (hb : b.eval sig σ = some tb) :
    ∃ i j d', evalActions d (encodeAction (.union a b)) = some d' ∧
      Repr d' ta i ∧ Repr d' tb j ∧
      Joined d' i j := by
  obtain ⟨i, m, hi, hm, hia⟩ := encodeBuild_reads a
    (hp a (by simp)) (hc a (by simp)) (hd a (by simp)) huf hρ ha
  have hsig := evalActions_sig hm
  have henv := evalActions_env hm
  obtain ⟨j, n, hj, hn, hjb⟩ := encodeBuild_reads (d := m) b
    (hp b (by simp))
    (fun f hf hctor => by rw [hsig]; exact hc b (by simp) f hf hctor)
    (fun fk hk => by rw [hsig]; exact hd b (by simp) fk hk)
    (by rw [hsig]; exact huf)
    (by rw [henv]; exact hρ.mono hsig.symm (evalActions_entries_subset hm)) hb
  have hbuild := evalActions_append_eq hm hn
  rw [hsig, henv] at hj
  have hsig' := evalActions_sig hbuild
  have henv' := evalActions_env hbuild
  have hi' : a.eval n.sig n.env = some i := by rw [hsig', henv']; exact hi
  have hj' : b.eval n.sig n.env = some j := by rw [hsig', henv']; exact hj
  have hmin := eval_min_ids hi' hj'
  have hcols₁ : Expr.evalList n.sig [a, .min a b] n.env = some [i, lowerId i j] := by
    simp only [Expr.evalList, hi', hmin, Option.bind_some, Option.map_some]
  have huf' : n.sig ufName = some (tableDecl 1) := by rw [hsig']; exact huf
  have hwrite₁ := evalAction_atom_of_eval huf' rfl hcols₁
  have hcols₂ : Expr.evalList (n.addTerm (.app ufName [i, lowerId i j])).sig [b, .min a b]
      (n.addTerm (.app ufName [i, lowerId i j])).env = some [j, lowerId i j] := by
    change Expr.evalList n.sig [b, .min a b] n.env = _
    simp only [Expr.evalList, hj', hmin, Option.bind_some, Option.map_some]
  have hwrite₂ := evalAction_atom_of_eval (d := n.addTerm (.app ufName [i, lowerId i j]))
    huf' rfl hcols₂
  refine ⟨i, j, (n.addTerm (.app ufName [i, lowerId i j])).addTerm (.app ufName [j, lowerId i j]),
    evalActions_append_eq hbuild ?_, ?_, ?_, ?_⟩
  · simp only [evalActions, hwrite₁, Option.bind_some, hwrite₂]
  · exact ((hia.mono (evalActions_entries_subset hn)).mono
      (evalAction_entries_subset hwrite₁)).mono
      (evalAction_entries_subset hwrite₂)
  · exact (hjb.mono (evalAction_entries_subset hwrite₁)).mono
      (evalAction_entries_subset hwrite₂)
  · have ho₁ := row_addTerm (d := n) ufName [i] (lowerId i j) huf'
    have ho₂ := row_addTerm (d := n.addTerm (.app ufName [i, lowerId i j]))
      ufName [j] (lowerId i j) huf'
    exact (Joined.edge (evalAction_entries_subset hwrite₂ ho₁)).trans (Joined.edge ho₂).symm

/-- Every successful source action has a successful compiled execution carrying its
new existence and union facts. This does not require rebuilding until the block ends. -/
theorem encodeAction_reads {src post : Database} {d : Database} {a : Action}
    (hcs : src.sig.AllConstructors) (hp : ∀ e ∈ actionExprs a, e.OrderingFree)
    (hc : ∀ e ∈ actionExprs a, ∀ f ∈ e.fns, src.sig.IsCtor f → d.sig.IsCtor f)
    (hd : ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors, d.sig (viewName fk.1) = some (tableDecl fk.2))
    (huf : d.sig ufName = some (tableDecl 1)) (hρ : EnvReads d src.env d.env)
    (h : Reads d src) (run : evalAction src a = some post) :
    ∃ d', evalActions d (encodeAction a) = some d' ∧ Reads d' post := by
  rcases evalAction_eq_some run with ⟨e, t, rfl, he, rfl⟩ |
    ⟨a, b, ta, tb, rfl, ha, hb, _, rfl⟩
  · rw [Expr.evalAtom_eq_eval hcs] at he
    obtain ⟨i, d', _, hr, hv⟩ := encodeBuild_reads e (hp e (by simp [actionExprs]))
      (hc e (by simp [actionExprs])) (hd e (by simp [actionExprs])) huf hρ he
    exact ⟨d', hr, (h.mono (evalActions_entries_subset hr)).addTerm hv⟩
  · obtain ⟨i, j, d', hr, hi, hj, ho⟩ := encodeUnion_reads hp hc hd huf hρ ha hb
    exact ⟨d', hr, (h.mono (evalActions_entries_subset hr)).addEq hi hj ho⟩

/-- Rule heads and global action blocks execute while retaining all source facts. -/
theorem encodeActions_reads {src post : Database} {d : Database} {as : List Action}
    (hcs : src.sig.AllConstructors) (hp : ∀ a ∈ as, ∀ e ∈ actionExprs a, e.OrderingFree)
    (hc : ∀ a ∈ as, ∀ e ∈ actionExprs a, ∀ f ∈ e.fns,
      src.sig.IsCtor f → d.sig.IsCtor f)
    (hd : ∀ a ∈ as, ∀ e ∈ actionExprs a, ∀ fk ∈ e.ctors,
      d.sig (viewName fk.1) = some (tableDecl fk.2))
    (huf : d.sig ufName = some (tableDecl 1)) (hρ : EnvReads d src.env d.env)
    (h : Reads d src) (run : evalActions src as = some post) :
    ∃ d', evalActions d (encodeActions as) = some d' ∧ Reads d' post := by
  induction as generalizing src d with
  | nil =>
      obtain rfl := Option.some.inj run
      exact ⟨d, rfl, h⟩
  | cons a as ih =>
      obtain ⟨mid, hm, hr⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨m, hfirst, hmid⟩ := encodeAction_reads hcs (hp a List.mem_cons_self)
        (hc a List.mem_cons_self) (hd a List.mem_cons_self) huf hρ h hm
      have hsig := evalActions_sig hfirst
      have henv := evalActions_env hfirst
      have hsrcsig := evalAction_sig hm
      have hsrcenv := evalAction_env hm
      obtain ⟨d', hrest, hpost⟩ := ih
        (by rw [hsrcsig]; exact hcs)
        (fun a ha => hp a (List.mem_cons_of_mem _ ha))
        (fun a ha e he f hf hctor => by
          rw [hsig]; exact hc a (List.mem_cons_of_mem _ ha) e he f hf (hsrcsig ▸ hctor))
        (fun a ha e he fk hk => by
          rw [hsig]; exact hd a (List.mem_cons_of_mem _ ha) e he fk hk)
        (by rw [hsig]; exact huf)
        (by rw [hsrcenv, henv]; exact hρ.mono hsig.symm (evalActions_entries_subset hfirst))
        hmid hr
      exact ⟨d', evalActions_append_eq hfirst hrest, hpost⟩

end Egglog.Congruence.Abstract
