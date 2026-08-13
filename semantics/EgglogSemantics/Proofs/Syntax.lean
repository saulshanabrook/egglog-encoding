import Mathlib.Data.List.Basic
import EgglogSemantics.Spec.Syntax

namespace Egglog
/-! ### Signatures -/
/-- A constructor has no merge specification. The converse fails at an undeclared name,
which is what "declaration is required" means. -/
theorem Signature.IsCtor.mergeOf {sig : Signature} {f : FnName} (h : sig.IsCtor f) :
    sig.mergeOf f = none := by
  obtain ⟨d, hd, hm⟩ := h
  rw [Signature.mergeOf, hd, Option.bind_some, hm]

/-- A name with a merge specification is not a constructor. -/
theorem Signature.not_isCtor {sig : Signature} {f : FnName} {m : MergeSpec}
    (hm : sig.mergeOf f = some m) : ¬ sig.IsCtor f := fun h => by
  rw [h.mergeOf] at hm; exact absurd hm (by simp)

/-- **An undeclared name is not a constructor.** The one direction the old reading had
backwards, and the whole content of the change: `Expr.eval` gets stuck on such a name. -/
theorem Signature.not_isCtor_of_none {sig : Signature} {f : FnName} (h : sig f = none) :
    ¬ sig.IsCtor f := fun ⟨_, hd, _⟩ => by rw [h] at hd; exact absurd hd (by simp)

/-- A declaration whose entry has no merge is a constructor. -/
theorem Signature.isCtor_of_decl {sig : Signature} {f : FnName} {d : FnDecl}
    (hd : sig f = some d) (hm : d.merge = none) : sig.IsCtor f := ⟨d, hd, hm⟩

/-- Under `AllConstructors` nothing has a merge specification, so every premise naming
one — a `MergeStep.collide`, a `NoMergeOk` obligation — is contradictory. -/
theorem Signature.AllConstructors.elim {sig : Signature} (h : sig.AllConstructors)
    {f : FnName} {m : MergeSpec} (hm : sig.mergeOf f = some m) : False := by
  rw [h f] at hm; exact absurd hm (by simp)

namespace Expr
@[simp] theorem vars_lit {l : Lit} : (Expr.lit l).vars = [] := rfl

@[simp] theorem vars_var {v : Var} : (Expr.var v).vars = [v] := rfl

@[simp] theorem vars_app {f : FnName} {args : List Expr} :
    (Expr.app f args).vars = Expr.varsList args := rfl

@[simp] theorem varsList_nil : Expr.varsList ([] : List Expr) = [] := rfl

@[simp] theorem varsList_cons {e : Expr} {es : List Expr} :
    Expr.varsList (e :: es) = e.vars ∪ Expr.varsList es := rfl

/-- A variable of an argument list is a variable of one of its arguments. -/
theorem mem_varsList {v : Var} {es : List Expr} (h : v ∈ Expr.varsList es) :
    ∃ e ∈ es, v ∈ e.vars := by
  induction es with
  | nil => simp at h
  | cons e es ih =>
    rw [varsList_cons, List.mem_union_iff] at h
    rcases h with h | h
    · exact ⟨e, List.mem_cons_self, h⟩
    · obtain ⟨e', he', hv⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ he', hv⟩

@[simp] theorem fns_lit {l : Lit} : (Expr.lit l).fns = [] := rfl

@[simp] theorem fns_var {v : Var} : (Expr.var v).fns = [] := rfl

@[simp] theorem fns_app {f : FnName} {args : List Expr} :
    (Expr.app f args).fns = f :: Expr.fnsList args := rfl

@[simp] theorem fnsList_nil : Expr.fnsList ([] : List Expr) = [] := rfl

@[simp] theorem fnsList_cons {e : Expr} {es : List Expr} :
    Expr.fnsList (e :: es) = e.fns ∪ Expr.fnsList es := rfl

/-- A function name of an argument list is a function name of one of its arguments. -/
theorem mem_fnsList {f : FnName} {es : List Expr} (h : f ∈ Expr.fnsList es) :
    ∃ e ∈ es, f ∈ e.fns := by
  induction es with
  | nil => simp at h
  | cons e es ih =>
    rw [fnsList_cons, List.mem_union_iff] at h
    rcases h with h | h
    · exact ⟨e, List.mem_cons_self, h⟩
    · obtain ⟨e', he', hv⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ he', hv⟩

end Expr
@[simp] theorem Query.vars_nil : Query.vars [] = [] := rfl

@[simp] theorem Query.vars_cons {p : Pattern} {ps : Query} :
    Query.vars (p :: ps) = p.vars ∪ Query.vars ps := rfl

end Egglog
