import Mathlib.Data.List.Dedup
import EgglogSemantics.Spec.Term

/-!
# Binder signatures

The slotted semantics extends the plain one with a binding annotation for every function
symbol: `bind(f)` is a set of pairs `(j, i)` saying that argument `j` of an application of
`f` supplies a slot name that is bound in argument `i`. A binding position is a fixed field of
the head, not a term child: congruence never replaces it, and a well-bound term holds a slot
literal there. The plain specification is untouched; a slotted program is a plain program
together with such a signature (`Slotted.Program` in `Spec/Step.lean`).
-/

namespace Egglog.Slotted

/-- The binder signature: `bind(f)` as the list of its pairs `(j, i)`. -/
@[blueprint "def:slotted-binders"
  (statement := /--
  \[
  \begin{gathered}
  \operatorname{bind}(f)\subseteq\mathbb N\times\mathbb N\qquad
  (j,i)\in\operatorname{bind}(f)\ \text{ means argument $j$ supplies a slot name bound in
    argument $i$}\\
  B_i(f(t_1,\ldots,t_n))\triangleq\{\,t_j\mid(j,i)\in\operatorname{bind}(f)\,\}
  \end{gathered}
  \]
  -/)
  (latexEnv := "paperfragment")]
def Binders := FnName → List (Nat × Nat)

namespace Binders

/-- The signature that binds nothing: the plain language. -/
def none : Binders := fun _ => []

/-- Whether position `j` of `f` is a binding position: `(j, _) ∈ bind(f)`. -/
def isBinding (bind : Binders) (f : FnName) (j : Nat) : Bool := (bind f).any (·.1 == j)

/-- The binding positions of `f`, each once, in order of first appearance. -/
def bindingPositions (bind : Binders) (f : FnName) : List Nat := ((bind f).map Prod.fst).dedup

/-- `B_i(f(args))`: the terms at the positions that bind a name in argument `i`. -/
def boundIn (bind : Binders) (f : FnName) (args : List Term) (i : Nat) : List Term :=
  (bind f).filterMap fun ji => if ji.2 = i then args[ji.1]? else Option.none

/-- A signature is well formed when no binding position binds in itself and no binding
position is itself covered by a binder. -/
def WF (bind : Binders) : Prop :=
  ∀ f, ∀ ji ∈ bind f, ji.1 ≠ ji.2 ∧ ∀ ki ∈ bind f, ki.2 ≠ ji.1

end Binders

end Egglog.Slotted
