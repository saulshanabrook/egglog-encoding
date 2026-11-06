import EgglogSemantics.Resugar.Query
import EgglogSemantics.Provenance.Log
import EgglogSemantics.Resugar.Claim
import Architect

namespace Egglog.Resugar

open SourceProof (Claim Proof)

def sourceSubst (vars : List Var) (σ : Env) : Option Env :=
  vars.mapM fun v => (Env.lookup v σ).map (v, ·)

/-- A maintenance firing's written row, justified from its premises in query order. Path
compression chains two edges; a UF collision chains the two parents through their key; a
congruence firing turns the second application into the first by congruence on each child,
and chains the two roots through them. `m` is the maintenance rule and `r` the row it
wrote. -/
@[blueprint "def:lift-rebuild"
  (statement := /--
  \begin{mathpar}
  \ir{Compress}{\rho_1\Uparrow\pi_1:a=b\\\rho_2\Uparrow\pi_2:b=c}
    {\kw{rule}_{\textsc{Compress}}((\mathtt{UF}(a,c)=\mathtt{UF}(a,c)),\sigma;\rho_1,\rho_2)
      \Uparrow\kw{trans}(\pi_1,\pi_2):a=c}
  \and
  \ir{Collide}{\rho_1\Uparrow\pi_1:a=b\\\rho_2\Uparrow\pi_2:a=c}
    {\kw{rule}_{\textsc{Collide}}((\mathtt{UF}(c,b)=\mathtt{UF}(c,b)),\sigma;\rho_1,\rho_2,\rho_3)
      \Uparrow\kw{trans}(\kw{sym}(\pi_2),\pi_1):c=b}
  \and
  \ir{Cong}{\rho_b\Uparrow\pi_b:f(b_1,\ldots,b_n)=f(b_1,\ldots,b_n)\\
    \rho_{a_i}\Uparrow\pi_{a_i}:a_i=r_i\\\rho_{b_i}\Uparrow\pi_{b_i}:b_i=r_i\ (\forall i)\\
    \rho_y\Uparrow\pi_y:f(a_1,\ldots,a_n)=y\\\rho_z\Uparrow\pi_z:f(b_1,\ldots,b_n)=z}
    {\kw{rule}_{\textsc{Cong}_f}((\mathtt{UF}(z,y)=\mathtt{UF}(z,y)),\sigma;
      \rho_a,\rho_b,\rho_{a_1},\rho_{b_1},\ldots,\rho_{a_n},\rho_{b_n},\rho_y,\rho_z,\rho_m)\\
      \Uparrow\kw{trans}(\kw{sym}(\pi_z),
      \kw{trans}(\kw{cong}_n(\cdots\kw{cong}_1(\pi_b,\pi_1)\cdots,\pi_n),\pi_y)):z=y}
  \end{mathpar}
  where $\pi_i=\kw{trans}(\pi_{b_i},\kw{sym}(\pi_{a_i})):b_i=a_i$.
  -/)
  (latexEnv := "paperfragment")]
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
  -- The canonical node views are an optimization of the congruence pass alone; proofs
  -- are extracted from the base compilation.
  | .view _ | .stale _ | .index _ | .rekey _ _ | .viewCongruence _ => none

/-- The proof `k` builds must establish the source claim of the relational fact. -/
def expect (P : Program) (fact : Term) (k : Claim → Option Proof) : Option Proof := do
  let c ← factClaim P fact
  let p ← k c
  if p.claim == c then some p else none

mutual

/-- Lift a proof about the compiled program to a source proof of its fact's claim:
`π ⇑ π'` with `P ⊢ π' : ⌈fact(π)⌉`. A compiled proof is a rule node
`rule_{i'}((t = t), σ; π̄)` for the row `t` a firing wrote, or for a subterm of a row a
source firing wrote, which that firing's facts cover. `origins` has one entry per rule of
the compiled program, in the order of `Program.rules`; `i'` below is the compiled copy of
source rule `i`, and `m` a maintenance rule. -/
@[blueprint "def:lift"
  (statement := /--
  \begin{mathpar}
  \ir{Source}{r_i=(p_1\land\cdots\land p_k\Rightarrow H)\\\rho_j\Uparrow\pi_j\ (\forall j)\\
    p_j\Uparrow\pi'_j:c_j\ (\forall j)\\
    \lceil t\rceil\in\operatorname{facts}_{\sigma|_{\operatorname{FV}(Q)}}(H)}
    {\kw{rule}_{i'}((t=t),\sigma;\rho_1,\ldots,\rho_m)\Uparrow
      \kw{rule}_i(\lceil t\rceil,\sigma|_{\operatorname{FV}(Q)};\pi'_1,\ldots,\pi'_k)}
  \end{mathpar}
  where the derivations of $p_j\Uparrow\pi'_j$ take their node, edge and comparison proofs
  from $\pi_1,\ldots,\pi_m$ in the order the compiler emits the atoms.
  -/)
  (latexEnv := "paperfragment")]
def liftProof (P : Program) (origins : List Congruence.RuleOrigin) :
    Proof → Option Proof
  | .rule c k σ premises =>
    if c.lhs != c.rhs then none else
    expect P c.lhs fun wanted => do
      let origin ← origins[k]?
      let ps ← liftAll P origins premises
      match origin with
      | .source index => do
        let r ← P.rules[index]?
        let σ' ← sourceSubst r.query.vars σ
        let sourcePremises ← query P r.query ps
        node P (.rule wanted index σ' sourcePremises)
      | .rebuild kind => do
        let p ← rebuild P kind ps
        finish P p wanted
  -- Reconstruction only produces rule nodes.
  | .symm _ | .trans _ _ | .congr _ _ _ => none

def liftAll (P : Program) (origins : List Congruence.RuleOrigin) :
    List Proof → Option (List Proof)
  | [] => some []
  | p :: ps => do
    let q ← liftProof P origins p
    let qs ← liftAll P origins ps
    some (q :: qs)

end

/-- Check the proof against the compiled program, lift it, and check the original source
claim. -/
def lift (P : Program) (pf : Proof) : Option Proof := do
  if !SourceProof.sourceOk P then none else do
    let compiled := Congruence.compile P
    let fact ← Provenance.check compiled.program pf
    let wanted ← factClaim P fact
    let result ← liftProof P compiled.origins pf
    if SourceProof.check P result == some wanted then some result else none

/-- A source proof of every row of the compiled program, read off the log of its
instrumented run and lifted. -/
def sourceProofs (P : Program) (terms : List Term) : Option (List Proof) := do
  let rows ← Provenance.proofs (Congruence.encode P) terms
  rows.mapM fun tp => lift P tp.2

end Egglog.Resugar
