import EgglogSemantics.Proofs.Setup

/-! Source constructor declarations and rule registrations preserve asserted equations. -/

namespace Egglog.Congruence

/-- Constructor declarations and rule registration preserve the source equations. -/
theorem source_setup_eqs {src post : Database} {c : Cmd} (hcs : src.sig.AllConstructors)
    (hc : c.DeclOrRule) (hdecl : c.CtorDecl) (hs : CmdStep src c post) :
    post.eqs = src.eqs := by
  obtain ⟨m, hm, hmerge⟩ := hs.reach
  have heq := hmerge.eq_of_allConstructors (cmdReach_allConstructors hcs hdecl hm)
  rw [heq]
  cases c with
  | decl f dc => subst hm; rfl
  | rule r => subst hm; rfl
  | run _ | saturate _ | check _ => exact hc.elim

end Egglog.Congruence
