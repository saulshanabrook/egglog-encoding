import EgglogSemantics.Provenance.Checker

/-!
# Provenance instrumentation

Every rule gets one more action: a row that records the firing, under the rule's index,
with the values of the rule's query variables. No rule reads these rows, so the
instrumented program builds the same data as the original, round for round, subsumes the
same rows, and settles when it does. Proofs are read off the log afterwards (`Log`).
-/

namespace Egglog.Provenance

def firePrefix : String := "@fire:"
def fireName (i : Nat) : FnName := firePrefix ++ toString i

/-- The rule index a firing-log name carries. -/
def fireIndex (f : FnName) : Option Nat :=
  if firePrefix.isPrefixOf f then (f.drop firePrefix.length).toNat? else none

/-- The names applied at the root of a written row: the program's rows, as opposed to the
values inside them. -/
def rowHeads (P : Program) : List FnName :=
  (P.rules.flatMap fun r => r.actions.filterMap fun a => match a with
    | .expr (.app f _) | .subsume f _ => some f | _ => none).dedup

/-- No union, so that the checker is sound for the program, and no name that could be
mistaken for the log. This covers the congruence compiler's output. -/
def programOk (P : Program) : Bool :=
  unionFree P && P.names.all fun f => !firePrefix.isPrefixOf f

/-- The row recording a firing of rule `k`. -/
def fireAction (k : Nat) (r : Rule) : Action :=
  .expr (.app (fireName k) (r.query.vars.map Expr.var))

/-- Rule `k` with its firing log action; the `fire` rows of a run are its log `L`. -/
@[blueprint "def:instrument"
  (statement := /--
  \[
  \operatorname{instrument}_i(Q\Rightarrow H)\ \triangleq\ Q\Rightarrow H\cup\{\mathtt{fire}_i(x_1,\ldots,x_n)\}
  \qquad\text{where }\{x_1,\ldots,x_n\}=\operatorname{FV}(Q)
  \]
  -/)
  (latexEnv := "paperfragment")]
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
