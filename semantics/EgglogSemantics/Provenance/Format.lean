import EgglogSemantics.SourceProof.Evaluate

namespace Egglog.Provenance

/-- Relational facts have existence evidence, without equality axioms. Every node states
its fact: `rule` cites a firing with one proof per premise, and `subterm` an established
fact containing it. -/
inductive Proof where
  | rule (fact : Term) (ruleIndex : Nat) (subst : Env) (premises : List Proof)
  | subterm (fact : Term) (parent : Proof)

def Proof.fact : Proof → Term
  | .rule t _ _ _ | .subterm t _ => t

@[simp] theorem Proof.fact_rule (t : Term) (i : Nat) (σ : Env) (ps : List Proof) :
    (Proof.rule t i σ ps).fact = t := rfl
@[simp] theorem Proof.fact_subterm (t : Term) (p : Proof) : (Proof.subterm t p).fact = t := rfl

def Proof.subproofs : Proof → List Proof
  | .rule _ _ _ ps => ps
  | .subterm _ p => [p]

end Egglog.Provenance
