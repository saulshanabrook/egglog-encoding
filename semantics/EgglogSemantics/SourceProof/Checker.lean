import EgglogSemantics.SourceProof.Evaluate
import EgglogSemantics.Source.Domain

/-! Certificates for a program: the original program, or its compilation, whose equations
are all reflexive. A proof cites the program's rules; arbitrary reflexivity cannot justify
a missing rule premise. The checker reads only the program, never a state of the e-graph.
-/

namespace Egglog.SourceProof

/-- **The checker's fragment**: the compiler's source fragment, restricted to programs that
test no disequality and take no minimum. A rule node is checked against its substitution
alone: a disequality is a syntactic test on the two instances, which is not sound once the
terms become equal in the final e-graph, and a minimum compares spellings, which the
representatives of the final e-graph need not be. -/
structure Fragment (P : Program) : Prop where
  /-- The program is in the compiler's fragment. -/
  fragment : P.Fragment
  /-- No rule or final check tests a disequality, and no rule subsumes a row. -/
  monotone : P.monotoneB = true
  /-- The source never computes with `min`. -/
  orderingFree : Program.OrderingFree P

instance (P : Program) : Decidable (Fragment P) :=
  decidable_of_iff (P.Fragment ∧ P.monotoneB = true ∧ Program.OrderingFree P)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.fragment, h.monotone, h.orderingFree⟩⟩

/-- The checker's fragment, decided. -/
def sourceOk (P : Program) : Bool := decide (Fragment P)

/-- The premise proofs a rule node carries, one per equality pattern in order, claim the
pattern's two instances; a bare pattern `e` is the paper's `e = e`, so its proof claims the
instance's reflexivity. A disequality, which only compiled programs use, carries no proof:
it is a test of the substitution, whose two instances must be bound and differ. -/
def premisesMatch (σ : Env) : Query → List Claim → Bool
  | [], [] => true
  | .expr e :: ps, c :: cs =>
    e.eval σ == some c.lhs && c.lhs == c.rhs && premisesMatch σ ps cs
  | .eq a b :: ps, c :: cs =>
    a.eval σ == some c.lhs && b.eval σ == some c.rhs && premisesMatch σ ps cs
  | .ne a b :: ps, cs =>
    (a.eval σ).isSome && (b.eval σ).isSome && a.eval σ != b.eval σ && premisesMatch σ ps cs
  | _, _ => false

/-- The facts justified by firing `r` under `σ`. The substitution must bind exactly the
query's variables, with every value a subterm of a premise instance. Premise claims must
match equality patterns in order, and every disequality must hold. -/
@[blueprint "def:proof-facts"
  (statement := /--
  \[
  \begin{aligned}
  \operatorname{refl}(t)&=\{\,s=s\mid s\text{ a subterm of }t\,\}\\
  \operatorname{facts}_\sigma(\kw{union}(e_1,e_2))
    &=\{\eval{e_1}=\eval{e_2},\ \eval{e_2}=\eval{e_1}\}
    \cup\operatorname{refl}(\eval{e_1})\cup\operatorname{refl}(\eval{e_2})\\
  \operatorname{facts}_\sigma(\kw{subsume}(f(e_1,\ldots,e_n)))&=\emptyset\\
  \operatorname{facts}_\sigma(\{h_1,\ldots,h_n\})
    &=\operatorname{facts}_\sigma(h_1)\cup\cdots\cup\operatorname{facts}_\sigma(h_n)
  \end{aligned}
  \]
  -/)
  (latexEnv := "paperfragment")]
def ruleFacts (r : Rule) (σ : Env) (premises : List Claim) : Option (List Claim) := do
  if decide ((Env.dom σ).Perm r.query.vars) && premisesMatch σ r.query premises then
    actionsFacts σ r.actions
  else none

/-- The root node, against the claims its subproofs state: `P ⊢ π : c`. -/
@[blueprint "def:proof-check"
  (statement := /--
  \begin{mathpar}
  \ir{Sym}{P\vdash\pi:s=t}{P\vdash\kw{sym}(\pi):t=s}
  \and
  \ir{Trans}{P\vdash\pi_1:s=t\\P\vdash\pi_2:t=u}{P\vdash\kw{trans}(\pi_1,\pi_2):s=u}
  \and
  \ir{Cong}{P\vdash\pi:s=f(t_1,\ldots,t_n)\\P\vdash\pi':t_k=t}
    {P\vdash\kw{cong}_k(\pi,\pi'):s=f(t_1,\ldots,t,\ldots,t_n)}
  \and
  \ir{Rule}{r_i=(p_1\land\cdots\land p_n\Rightarrow H)\\
    \sigma:\operatorname{FV}(p_1\land\cdots\land p_n)\to\mathit{Term}\\
    P\vdash\pi_j:\eval{e}=\eval{e'}\text{ for the $j$th equality pattern }e=e'\\
    \eval{e}\ne\eval{e'}\text{ for each disequality pattern }e\ne e'\\
    c\in\operatorname{facts}_\sigma(H)}
    {P\vdash\kw{rule}_i(c,\sigma;\pi_1,\ldots,\pi_m):c}
  \end{mathpar}
  -/)
  (latexEnv := "paperfragment")]
def checkNode (P : Program) : Proof → Bool
  | .rule c i σ ps => (do
      let r ← P.rules[i]?
      let fs ← ruleFacts r σ (ps.map Proof.claim)
      some (decide (c ∈ fs))).getD false
  | .symm _ => true
  | .trans p q => p.claim.rhs == q.claim.lhs
  | .congr p k q =>
      match p.claim.rhs with
      | .app _ args => args[k]? == some q.claim.lhs
      | .lit _ => false

mutual

/-- Every node is valid. -/
def valid (P : Program) : Proof → Bool
  | .rule c i σ ps => allValid P ps && checkNode P (.rule c i σ ps)
  | .symm p => valid P p && checkNode P (.symm p)
  | .trans p q => valid P p && valid P q && checkNode P (.trans p q)
  | .congr p k q => valid P p && valid P q && checkNode P (.congr p k q)

def allValid (P : Program) : List Proof → Bool
  | [] => true
  | p :: ps => valid P p && allValid P ps

end

/-- The claim of a proof whose every node is valid, against any program. -/
def checkIn (P : Program) (pf : Proof) : Option Claim :=
  if valid P pf then some pf.claim else none

/-- The claim of a proof whose every node is valid, against a source program in the
fragment. -/
def check (P : Program) (pf : Proof) : Option Claim := do
  if !sourceOk P then none else checkIn P pf

end Egglog.SourceProof
