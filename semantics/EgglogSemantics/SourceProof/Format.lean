import EgglogSemantics.Spec.Step

namespace Egglog.SourceProof

structure Claim where
  lhs : Term
  rhs : Term
  deriving DecidableEq

/-- Every node states its claim. A rule node cites a rule by its position in
`Program.rules`; initial facts are empty-query rules. -/
inductive Proof where
  | symm (claim : Claim) (proof : Proof)
  | trans (claim : Claim) (left right : Proof)
  | congr (claim : Claim) (base : Proof) (childIndex : Nat) (child : Proof)
  | rule (claim : Claim) (ruleIndex : Nat) (subst : Env) (premises : List Proof)
  deriving BEq

def Proof.claim : Proof → Claim
  | .symm c _ | .trans c _ _ | .congr c _ _ _ | .rule c _ _ _ => c

@[simp] theorem Proof.claim_symm (c : Claim) (p : Proof) : (Proof.symm c p).claim = c := rfl
@[simp] theorem Proof.claim_trans (c : Claim) (p q : Proof) :
    (Proof.trans c p q).claim = c := rfl
@[simp] theorem Proof.claim_congr (c : Claim) (p : Proof) (k : Nat) (q : Proof) :
    (Proof.congr c p k q).claim = c := rfl
@[simp] theorem Proof.claim_rule (c : Claim) (i : Nat) (σ : Env) (ps : List Proof) :
    (Proof.rule c i σ ps).claim = c := rfl

def Proof.subproofs : Proof → List Proof
  | .symm _ p => [p]
  | .trans _ p q | .congr _ p _ q => [p, q]
  | .rule _ _ _ ps => ps

mutual

/-- Every node of the tree, in preorder. -/
def Proof.nodes : Proof → List Proof
  | p@(.symm _ q) => p :: q.nodes
  | p@(.trans _ q r) | p@(.congr _ q _ r) => p :: (q.nodes ++ r.nodes)
  | p@(.rule _ _ _ qs) => p :: Proof.nodesAll qs

def Proof.nodesAll : List Proof → List Proof
  | [] => []
  | q :: qs => q.nodes ++ Proof.nodesAll qs

end

end Egglog.SourceProof
