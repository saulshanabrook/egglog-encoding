import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Proofs.DiagonalPreservation
import EgglogSemantics.Proofs.LiveTables
import EgglogSemantics.Proofs.Congruence.Properties

/-!
# Leader lookup in current tables

A merge-normal table has one output tuple per congruent key. In particular, a current
UF self-parent certifies a root: no competing parent or nontrivial parent path can
leave it. These statements use mathematical databases only.
-/

namespace Egglog

/-- Normalized outputs agree even when the lookup keys are merely congruent. -/
theorem MergeNormal.out_functional {d : Database} (hn : MergeNormal d)
    {f : FnName} {as bs old new : List Term} (hk : CongList d as bs)
    (ha : d.Out f as old) (hb : d.Out f bs new) : old = new := by
  obtain ⟨cs, hac, ha⟩ := ha
  obtain ⟨ds, hbd, hb⟩ := hb
  exact congrArg Entry.value
    (hn _ ha _ hb rfl (hac.symm.trans (hk.trans hbd)))

/-- An exact-key lookup has a unique current output. -/
theorem MergeNormal.out_unique {d : Database} (hn : MergeNormal d)
    {f : FnName} {as old new : List Term}
    (ha : d.Out f as old) (hb : d.Out f as new) : old = new := by
  obtain ⟨cs, hc, hr⟩ := ha
  exact hn.out_functional (hc.trans hc.symm) ⟨cs, hc, hr⟩ hb

namespace Congruence.Live

/-- A successful UF atom reads a current row through ordinary matching. -/
theorem uf_match_out {d : Database} (hd : d.Diag) (hs : d.StoreOk)
    (huf : d.sig ufName = some (tableDecl 1))
    {σ : Env} {v w : Var} {a r : Term}
    (ha : Env.lookup v σ = some a) (hr : Env.lookup w σ = some r)
    (hm : Matches d (.expr (.app ufName [.var v, .var w])) σ) :
    d.Out ufName [a] [r] := by
  cases hm using Matches.storedCases with
  | expr hx he hc =>
    have hev : (Expr.app ufName [.var v, .var w]).evalAtom d.sig σ =
        some (Entry.mk ufName [a] [r]).atom := by
      simp [Expr.evalAtom, huf, tableDecl, FnDecl.entryWidth, Expr.evalList,
        Expr.eval, ha, hr, Entry.atom, Entry.columns]
    obtain rfl := Option.some.inj (hev.symm.trans he)
    have ht : (Entry.mk ufName [a] [r]).atom ∈ d.terms :=
      (congOn_eq_of_diag hd hc) ▸ hx
    have hshape : (Entry.mk ufName [a] [r]).Shape d.sig :=
      ⟨tableDecl 1, huf, by simp [tableDecl], rfl, rfl⟩
    have hv : (Entry.mk ufName [a] [r]).Valid d.sig := by
      rcases hs.term ht with hv | ⟨row, hv, he⟩
      · exact (hshape.atom_not_value hv).elim
      · have hrow := hshape.atom_injective hv.shape he
        simpa only [hrow] using hv
    have hm := hs.entry_of_held_atom hv ht
    exact ⟨[a], .cons (Database.toCong (hs.columns _ hm a
      (by simp [Entry.columns]))) .nil, hm⟩

/-- Unlike a historical self-loop, a current self-parent rules out any other parent. -/
theorem self_parent_only {d : Database} (hn : MergeNormal d) {r p : Term}
    (hr : d.Out ufName [r] [r]) (hp : d.Out ufName [r] [p]) : p = r := by
  exact List.singleton_inj.mp (hn.out_unique hp hr)

/-- A parent walk starting at a certified root cannot reach another term. -/
theorem walk_from_self_parent {d : Database} (hn : MergeNormal d) {r p : Term}
    (hr : d.Out ufName [r] [r])
    (hw : Relation.ReflTransGen (fun a b => d.Out ufName [a] [b]) r p) : p = r := by
  induction hw with
  | refl => rfl
  | tail _ hs ih => exact self_parent_only hn hr (ih ▸ hs)

/-- The two positive lookups used by `leaderQuery` select a unique rooted parent. -/
theorem guarded_leader_unique {d : Database} (hn : MergeNormal d) {a r s : Term}
    (har : d.Out ufName [a] [r]) (hrr : d.Out ufName [r] [r])
    (has : d.Out ufName [a] [s]) :
    s = r ∧ ∀ p, d.Out ufName [r] [p] → p = r :=
  ⟨List.singleton_inj.mp (hn.out_unique has har), fun _ => self_parent_only hn hrr⟩

/-- The congruence compiler still uses no built-in equality between distinct ids. -/
theorem compiled_execution_diagonal {P : Program} {d : Database}
    (h : ProgramStep Database.empty (encode P) d) : d.Diag :=
  (h.noUnions Database.NoUnions.empty (encode_unionFree P)).diag

end Congruence.Live
end Egglog
