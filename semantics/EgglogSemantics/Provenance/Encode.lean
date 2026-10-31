import EgglogSemantics.Provenance.Checker

/-!
# Provenance instrumentation

Every rule gets one more action: a row that records the firing, under the rule's index,
with the values of the rule's query variables. No rule reads these rows, so the
instrumented program builds the same data as the original, round for round, subsumes the
same rows, and settles when it does. Proofs are read off the log afterwards (`Extract`).
-/

namespace Egglog.Provenance

def namePrefix : String := "@prov:"
def firePrefix : String := namePrefix ++ "fire:"
def fireName (i : Nat) : FnName := firePrefix ++ toString i

/-- The rule index a firing-log name carries. -/
def fireIndex (f : FnName) : Option Nat :=
  if firePrefix.isPrefixOf f then (f.drop firePrefix.length).toNat? else none

/-- The names applied at the root of a written row. A query atom whose name is applied
inside a column is a lookup of a value, not a row. -/
def rowHeads (P : Program) : List FnName :=
  (P.rules.flatMap fun r => r.actions.filterMap fun a => match a with
    | .expr (.app f _) | .subsume f _ => some f | _ => none).dedup

/-- The names applied inside a column. -/
def Pattern.innerFns : Pattern → List FnName
  | .expr (.app _ cols) => Expr.fnsList cols
  | .expr _ => []
  | .eq a b | .ne a b => a.fns ++ b.fns

@[inherit_doc Pattern.innerFns]
def valueHeads (P : Program) : List FnName :=
  ((P.rules.flatMap fun r => r.query.flatMap Pattern.innerFns ++
      (r.actions.flatMap fun a => match a with
        | .expr (.app _ cols) | .subsume _ cols => Expr.fnsList cols
        | _ => [])) ++
    P.check.flatMap Pattern.innerFns).dedup

/-- No union, no reserved name, and no name written both as a row and inside a column, so
that rows, values and the log can be told apart. This covers the congruence compiler's
output, whose rows are the union-find edges and whose values are the source terms. -/
def programOk (P : Program) : Bool :=
  unionFree P &&
  (rowHeads P ++ valueHeads P).all (fun f => !namePrefix.isPrefixOf f) &&
  (rowHeads P).all fun f => !(valueHeads P).contains f

/-- The row recording a firing of rule `k`. -/
def fireAction (k : Nat) (r : Rule) : Action :=
  .expr (.app (fireName k) (r.query.vars.map Expr.var))

def encodeRule (k : Nat) (r : Rule) : Rule :=
  { r with actions := r.actions ++ [fireAction k r] }

/-- Instrument a schedule's rules, numbered from `k` in `Program.rules`. -/
def encodeSchedule : Schedule → Nat → Schedule × Nat
  | .run rs, k => (.run (rs.zipIdx.map fun ri => encodeRule (k + ri.2) ri.1), k + rs.length)
  | .saturate S, k =>
      let (S', n) := encodeSchedule S k
      (.saturate S', n)
  | .seq S₁ S₂, k =>
      let (T₁, n) := encodeSchedule S₁ k
      let (T₂, m) := encodeSchedule S₂ n
      (.seq T₁ T₂, m)

/-- Instrument a union-free program: every rule also logs its firings. -/
def encode (P : Program) : Option Program :=
  if programOk P then some { schedule := (encodeSchedule P.schedule 0).1, check := P.check }
  else none

end Egglog.Provenance
