import EgglogSemantics.Proofs.Congruence.LeaderForward
import EgglogSemantics.Proofs.Congruence.LeaderSyntax
import EgglogSemantics.Proofs.Congruence.AbstractBuild

/-! Renaming source bindings lets the ordinary build proof handle leader-bound heads. -/

namespace Egglog.Congruence

def leaderEnv (σ : Env) : Env := σ.map fun b => (leaderVar b.1, b.2)

@[simp] theorem lookup_leaderEnv (σ : Env) (v : Var) :
    Env.lookup (leaderVar v) (leaderEnv σ) = Env.lookup v σ := by
  induction σ with
  | nil => rfl
  | cons b σ ih =>
      rcases b with ⟨w, t⟩
      by_cases h : v = w
      · subst w; simp [leaderEnv]
      · have hn : leaderVar v ≠ leaderVar w := fun he => h (leaderVar_injective he)
        simpa only [leaderEnv, List.map_cons, Env.lookup_cons, if_neg h, if_neg hn] using ih

theorem lookup_leaderEnv_inv {σ : Env} {v : Var} {t : Term}
    (h : Env.lookup v (leaderEnv σ) = some t) :
    ∃ w, v = leaderVar w ∧ Env.lookup w σ = some t := by
  obtain ⟨b, _, he⟩ := List.mem_map.mp (Env.mem_of_lookup h)
  have hv : v = leaderVar b.1 := (congrArg Prod.fst he).symm
  exact ⟨b.1, hv, by simpa [hv] using h⟩

@[simp] theorem eval_leaderEnv (e : Expr) (s : Signature) (σ : Env) :
    (leaderExpr e).eval s (leaderEnv σ) = e.eval s σ := by
  apply eval_leader_eq e (fun _ _ => Iff.rfl)
  intro v _
  simp [Expr.eval]

theorem evalAction_leaderEnv {d post : Database} {a : Action}
    (hc : d.sig.AllConstructors) (he : evalAction d a = some post) :
    evalAction { d with env := leaderEnv d.env } (leaderAction a) =
      some { post with env := leaderEnv post.env } := by
  rcases evalAction_eq_some he with ⟨e, t, rfl, ht, rfl⟩ |
    ⟨a, b, ta, tb, rfl, ha, hb, hn, rfl⟩
  · rw [Expr.evalAtom_eq_eval hc] at ht
    simp only [leaderAction, evalAction, Expr.evalAtom_eq_eval hc, eval_leaderEnv, ht,
      Option.map_some]
    rfl
  · simp only [leaderAction, evalAction, eval_leaderEnv, ha, hb, Option.bind_some,
      Bool.or_eq_true, if_neg hn]
    rfl

theorem evalActions_leaderEnv {d post : Database} {as : List Action}
    (hc : d.sig.AllConstructors) (he : evalActions d as = some post) :
    evalActions { d with env := leaderEnv d.env } (as.map leaderAction) =
      some { post with env := leaderEnv post.env } := by
  induction as generalizing d with
  | nil => obtain rfl := Option.some.inj he; rfl
  | cons a as ih =>
      obtain ⟨m, hm, hr⟩ := Option.bind_eq_some_iff.mp he
      simpa only [List.map_cons, evalActions, evalAction_leaderEnv hc hm, Option.bind_some]
        using ih (by rw [evalAction_sig hm]; exact hc) hr

namespace Abstract

theorem LeaderReads.envReads {d : Database} {σ ρ : Env} (h : LeaderReads d σ ρ)
    (hd : d.Diag)
    (hv : ∀ v i, Env.lookup v ρ = some i → i.IsValue d.sig) :
    EnvReads d (leaderEnv σ) ρ := by
  intro v t ht
  obtain ⟨w, rfl, hw⟩ := lookup_leaderEnv_inv ht
  obtain ⟨i, hi, hr, _⟩ := h w t hw
  exact ⟨i, hi, hv _ _ hi, Live.Repr.of_view hd hr⟩

end Abstract
end Egglog.Congruence
