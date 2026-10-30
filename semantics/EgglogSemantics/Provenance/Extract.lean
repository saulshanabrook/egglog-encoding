import EgglogSemantics.Provenance.Encode

/-! Proofs from the firing log. A firing is justified once every premise is established:
a row premise by a proof of its instance, an equality or disequality premise by a proof of
a row carrying the side in question. Passes over the log justify firings until none is
left that can be, and each data row keeps the first proof found for it. -/

namespace Egglog.Provenance

/-- The firings the held terms record: a rule index and its substitution. -/
def firings (P : Program) (terms : List Term) : List (Nat × Env) :=
  terms.filterMap fun t => match t with
    | .app f args => do
        let i ← fireIndex f
        let r ← P.rules[i]?
        if args.length == r.query.vars.length then some (i, r.query.vars.zip args) else none
    | .lit _ => none

/-- Proofs of rows, by row. -/
abbrev Facts := List (Term × Proof)

/-- A proof establishing `t`: a row's proof, or a subterm of one. The proofs at hand come
first, so that a premise is witnessed by a row of the same firing when it can be. -/
def establish (facts : Facts) (near : List Proof) (t : Term) : Option Proof :=
  match near.find? (·.fact == t) with
  | some p => some p
  | none =>
  match near.find? fun p => decide (t ∈ p.fact.subtermList) with
  | some p => some (.subterm t p)
  | none =>
  match facts.find? (·.1 == t) with
  | some fp => some fp.2
  | none => (facts.find? fun fp => decide (t ∈ fp.1.subtermList)).map fun fp => .subterm t fp.2

/-- The proof of a premise: a row premise's instance, the common value of an equality, or
the first side of a disequality. -/
def premiseProof (facts : Facts) (rows : List Proof) (σ : Env) : Pattern → Option Proof
  | .expr e => do establish facts rows (← e.eval σ)
  | .eq a b => do
      let x ← a.eval σ
      let y ← b.eval σ
      if x == y then establish facts rows x else none
  | .ne a b => do
      let x ← a.eval σ
      let y ← b.eval σ
      if x == y then none else establish facts rows x

/-- The rows a firing writes, with their proofs, once its premises are established. -/
def justify (P : Program) (facts : Facts) (i : Nat) (σ : Env) : Option Facts := do
  let r ← P.rules[i]?
  let rows ← (r.query.filterMap fun p => match p with | .expr e => some e | _ => none).mapM
    fun e => do establish facts [] (← e.eval σ)
  let ps ← r.query.mapM (premiseProof facts rows σ)
  some <| r.actions.filterMap fun a => match a with
    | .expr e => (e.eval σ).map fun t => (t, .rule t i σ ps)
    | _ => none

/-- Justify the pending firings in order, repeatedly, until a pass justifies none. -/
def passes (P : Program) : Nat → Facts → List (Nat × Env) → Facts
  | 0, facts, _ => facts
  | n + 1, facts, pending =>
    let (facts', pending', progress) :=
      pending.foldl (init := (facts, ([] : List (Nat × Env)), false)) fun (fs, rest, prog) f =>
        match justify P fs f.1 f.2 with
        | some new => ((new.filter fun tp => !(fs.any (·.1 == tp.1))) ++ fs, rest, true)
        | none => (fs, f :: rest, prog)
    if progress then passes P n facts' pending'.reverse else facts'

/-- The rows of the uninstrumented program among the held terms. -/
def dataRows (P : Program) (terms : List Term) : List Term :=
  let heads := rowHeads P
  terms.filter fun t => match t with
    | .app f _ => heads.contains f
    | .lit _ => false

/-- The held terms without the log. -/
def eraseLog (terms : List Term) : List Term :=
  terms.filter fun t => match t with
    | .app f _ => (fireIndex f).isNone
    | .lit _ => true

/-- Every data row with its checked proof from the log, or `none` where no proof checks. -/
def extractEach (P : Program) (terms : List Term) : List (Term × Option Proof) :=
  let fs := firings P terms
  let facts := passes P (fs.length + 1) [] fs
  (dataRows P terms).map fun t =>
    (t, (facts.find? (·.1 == t)).bind fun fp =>
      if check P fp.2 == some t then some fp.2 else none)

/-- A checked proof of every data row. -/
def extract (P : Program) (terms : List Term) : Option (List (Term × Proof)) := do
  if !programOk P then none else
    (extractEach P terms).mapM fun tp => tp.2.map (tp.1, ·)

end Egglog.Provenance
