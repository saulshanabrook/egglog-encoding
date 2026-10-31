import EgglogSemantics.Resugar.Query
import EgglogSemantics.Provenance.Extract
import EgglogSemantics.Resugar.Claim

namespace Egglog.Resugar

open SourceProof (Claim Proof)

def sourceSubst (vars : List Var) (σ : Env) : Option Env :=
  vars.mapM fun v => (Env.lookup v σ).map (v, ·)

/-- A maintenance firing's written row, justified from its premises in query order. Path
compression chains two edges; a UF collision chains the two parents through their key; a
congruence firing turns the second application into the first by congruence on each child,
and chains the two roots through them. -/
def rebuild (P : Program) (kind : Congruence.RebuildOrigin)
    (ps : List Proof) : Option Proof := do
  match kind with
  | .compress =>
    let p :: q :: _ := ps | none
    trans P p q
  | .collide =>
    let p :: q :: _ := ps | none
    let rev ← symm P q
    trans P rev p
  | .congruence _ =>
    let pa :: pb :: rest := ps | none
    let .app _ as := pa.claim.rhs | none
    let k := as.length
    let edges := rest.take (2 * k)
    let py :: pz :: _ := rest.drop (2 * k) | none
    if edges.length != 2 * k then none else
    let children ← (List.range k).mapM fun i => do
      let ea ← edges[2 * i]?
      let eb ← edges[2 * i + 1]?
      let rev ← symm P ea
      trans P eb rev
    let node ← replaceChildren P children pb
    let rev ← symm P pz
    let left ← trans P rev node
    trans P left py

/-- The proof `k` builds must establish the source claim of the relational fact. -/
def expect (P : Program) (fact : Term) (k : Claim → Option Proof) : Option Proof := do
  let c ← factClaim P fact
  let p ← k c
  if p.claim == c then some p else none

mutual

/-- Lift relational provenance to a source proof of the same fact's claim. `origins` has
one entry per rule of the compiled program, in the order of `Program.rules`. -/
def liftProof (P : Program) (origins : List Congruence.RuleOrigin) :
    Provenance.Proof → Option Proof
  | .subterm t parent => expect P t fun c => do
      let p ← liftProof P origins parent
      finish P p c
  | .rule t k σ premises => expect P t fun c => do
      let origin ← origins[k]?
      let ps ← liftAll P origins premises
      match origin with
      | .source index => do
        let r ← P.rules[index]?
        let σ' ← sourceSubst r.query.vars σ
        let sourcePremises ← query P σ' r.query ps
        node P (.rule c index σ' sourcePremises)
      | .rebuild kind => do
        let p ← rebuild P kind ps
        finish P p c

def liftAll (P : Program) (origins : List Congruence.RuleOrigin) :
    List Provenance.Proof → Option (List Proof)
  | [] => some []
  | p :: ps => do
    let q ← liftProof P origins p
    let qs ← liftAll P origins ps
    some (q :: qs)

end

/-- Check the relational proof against the compiled program, lift it, and check the
original source claim. -/
def lift (P : Program) (pf : Provenance.Proof) : Option Proof := do
  if !SourceProof.sourceOk P then none else do
    let compiled := Congruence.compile P
    let fact ← Provenance.check compiled.program pf
    let wanted ← factClaim P fact
    let result ← liftProof P compiled.origins pf
    if SourceProof.check P result == some wanted then some result else none

/-- Lift a source proof of every data row of the compiled program from the final state of
its instrumented run. -/
def extractAll (P : Program) (terms : List Term) : Option (List Proof) := do
  let rows ← Provenance.extract (Congruence.encode P) terms
  rows.mapM fun tp => lift P tp.2

end Egglog.Resugar
