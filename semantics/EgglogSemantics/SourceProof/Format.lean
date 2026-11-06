import EgglogSemantics.Spec.Step
import Architect

/-!
# Source proofs

A source proof is a derivation of an equation between terms from the rules of the original
program: a rule node is a firing with one subproof per premise and names the fact it takes
from the head; symmetry, transitivity and congruence follow the congruence rules of the
semantics, and their claims follow from their subproofs'. The paper's syntax is the
`@[blueprint]` statement of `Proof`.
-/

namespace Egglog.SourceProof

/-- An equation between two terms. -/
structure Claim where
  lhs : Term
  rhs : Term
  deriving DecidableEq

/-- A rule node cites a rule by its position in `Program.rules` and states its claim;
initial facts are empty-query rules. Every other node's claim is determined by its
subproofs. -/
@[blueprint "def:proof-syntax"
  (statement := /--
  \syntaxline{Claims}{c ::= t = t}
  \syntaxline{Proofs}{\pi ::= \kw{rule}_i(c,\sigma;\pi_1,\ldots,\pi_n)
    \mid\kw{sym}(\pi)\mid\kw{trans}(\pi,\pi)\mid\kw{cong}_k(\pi,\pi)}
  -/)
  (latexEnv := "paperfragment")]
inductive Proof where
  | rule (claim : Claim) (ruleIndex : Nat) (subst : Env) (premises : List Proof)
  | symm (proof : Proof)
  | trans (left right : Proof)
  | congr (base : Proof) (childIndex : Nat) (child : Proof)
  deriving BEq

/-- The claim a proof states. A congruence whose base does not end in an application, or
whose index is out of range, states its base's claim; `checkNode` rejects such a node. -/
def Proof.claim : Proof → Claim
  | .rule c _ _ _ => c
  | .symm p => ⟨p.claim.rhs, p.claim.lhs⟩
  | .trans p q => ⟨p.claim.lhs, q.claim.rhs⟩
  | .congr p k q =>
    match p.claim.rhs with
    | .app f args =>
      if k < args.length then ⟨p.claim.lhs, .app f (args.set k q.claim.rhs)⟩ else p.claim
    | .lit _ => p.claim

@[simp] theorem Proof.claim_rule (c : Claim) (i : Nat) (σ : Env) (ps : List Proof) :
    (Proof.rule c i σ ps).claim = c := rfl
@[simp] theorem Proof.claim_symm (p : Proof) :
    (Proof.symm p).claim = ⟨p.claim.rhs, p.claim.lhs⟩ := rfl
@[simp] theorem Proof.claim_trans (p q : Proof) :
    (Proof.trans p q).claim = ⟨p.claim.lhs, q.claim.rhs⟩ := rfl

def Proof.subproofs : Proof → List Proof
  | .rule _ _ _ ps => ps
  | .symm p => [p]
  | .trans p q | .congr p _ q => [p, q]

mutual

/-- Every node of the tree, in preorder. -/
def Proof.nodes : Proof → List Proof
  | p@(.rule _ _ _ qs) => p :: Proof.nodesAll qs
  | p@(.symm q) => p :: q.nodes
  | p@(.trans q r) | p@(.congr q _ r) => p :: (q.nodes ++ r.nodes)

def Proof.nodesAll : List Proof → List Proof
  | [] => []
  | q :: qs => q.nodes ++ Proof.nodesAll qs

end

end Egglog.SourceProof
