import EgglogSemantics.Proofs.Congruence.Correctness
import EgglogSemantics.Tests.Divergence

/-! Non-vacuity checks for the mathematical compiler theorem. These witnesses use
`Database`, `CmdStep`, and `Eval` directly; no interpreter correctness bridge is used. -/

namespace Egglog.Tests.CongruenceCorrectness

open Congruence

def ctorTerm : Term := .app "C" []
def constructorExpr : Expr := .app "C" []
def constructorQuery : Query := [.expr constructorExpr]
def view : Term := .app (viewName "C") [ctorTerm]
def viewQuery : Query := [.expr (.app (viewName "C") [.var (freshVar 0)])]

private def initialRule : Rule := ⟨[], [.expr constructorExpr], "seed"⟩

/-- An empty-query rule builds the term observed by the successful check. -/
def successProgram : Program :=
  [.decl "C" (ctorDecl 0), .rule initialRule, .run "seed", .check constructorQuery]

/-- Declaration alone does not build an instance, so this check fails dynamically. -/
def failureProgram : Program :=
  [.decl "C" (ctorDecl 0), .check constructorQuery]

private theorem safe_name : ¬ "@".isPrefixOf "C" := by
  rw [String.isPrefixOf, String.startsWith_string_iff]
  decide

theorem success_wellFormed : successProgram.WellFormed := by decide
theorem success_noSaturate : successProgram.NoSaturate := by
  simp [Program.NoSaturate, successProgram, Cmd.NoSaturate]
theorem success_fragment : successProgram.Fragment := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, by decide, by decide, by decide⟩
  intro n hn
  change n ∈ ["C", "seed"] at hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact safe_name
  · obtain rfl := List.mem_singleton.mp hn
    rw [String.isPrefixOf, String.startsWith_string_iff]
    decide

theorem failure_wellFormed : failureProgram.WellFormed := by decide
theorem failure_noSaturate : failureProgram.NoSaturate := by
  simp [Program.NoSaturate, failureProgram, Cmd.NoSaturate]
theorem failure_fragment : failureProgram.Fragment := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, by decide, by decide, by decide⟩
  intro n hn
  change n ∈ ["C"] at hn
  obtain rfl := List.mem_singleton.mp hn
  exact safe_name

def sourceDeclared : Database :=
  { Database.empty with sig := Function.update Database.empty.sig "C" (some (ctorDecl 0)) }
private def sourceRegistered : Database :=
  { sourceDeclared with rules := {initialRule} }
def sourceBuilt : Database := sourceRegistered.addTerm ctorTerm

private theorem no_query_of_empty {d : Database} (hd : d.eqs = ∅) {q : Query}
    (hq : q ≠ []) : ¬ QueryHolds d q := by
  rw [queryHolds_iff_validQuerySubst]
  rintro ⟨σ, σs, hσs, _⟩
  cases q with
  | nil => exact hq rfl
  | cons p ps =>
      cases hσs with
      | cons hp _ =>
          cases hp.2 using Matches.storedCases with
          | expr hw _ _ => simp [Database.terms_empty_of_eqs_empty hd] at hw
          | eq hw _ _ _ _ => simp [Database.terms_empty_of_eqs_empty hd] at hw

private theorem empty_normal {d : Database} (hd : d.eqs = ∅) : MergeNormal d := by
  intro row hr
  exact (hd ▸ hr.2).elim

private theorem constructors_normal {d : Database} (hc : d.sig.AllConstructors) :
    MergeNormal d := by
  intro row hr
  obtain ⟨dc, hd, hm, _⟩ := hr.1
  have hh := hc row.name
  rw [Signature.mergeOf, hd, Option.bind_some] at hh
  exact (hm hh).elim

private theorem source_ctors : sourceDeclared.sig.AllConstructors := by
  intro f
  by_cases hf : f = "C"
  · subst f; rfl
  · simp [sourceDeclared, Database.empty, Signature.mergeOf, hf]

private theorem source_check : QueryHolds sourceBuilt constructorQuery := by
  obtain ⟨σ, hσ, _⟩ := Abstract.validQuerySubst_of_flatReads
    (d := sourceBuilt) (ρ := []) (q := constructorQuery)
    (by simp [Env.lookup]) (by
      intro p hp
      obtain rfl := List.mem_singleton.mp hp
      exact .entry ⟨ctorDecl 0, rfl, Or.inl rfl⟩ rfl (Database.mem_addTerm _ _))
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; rfl)
  exact queryHolds_iff_validQuerySubst.mpr ⟨σ, hσ⟩

private theorem source_decl : CmdStep Database.empty (.decl "C" (ctorDecl 0)) sourceDeclared :=
  .of_reach rfl (empty_normal rfl)

private theorem run_initializer {d e : Database} {r : Rule}
    (hempty : d.eqs = ∅) (hrules : d.rules = {r}) (hquery : r.query = [])
    (hfire : evalLocalActions d r.actions [] = some e) : RunRules r.ruleset d = e := by
  have hresults : {out | ∃ s ∈ d.rules, s.ruleset = r.ruleset ∧
      out ∈ RuleResults d s} = {e} := by
    ext out
    constructor
    · rintro ⟨s, hs, _, σ, hσ, he⟩
      have hs : s = r := by simpa [hrules] using hs
      subst s
      have hσ : σ = [] := ValidQuerySubst.nil_iff.mp (hquery ▸ hσ)
      subst σ
      rw [hfire] at he
      exact (Option.some.inj he).symm
    · intro he
      obtain rfl := Set.mem_singleton_iff.mp he
      exact ⟨r, by simp [hrules], rfl, [], by
        simpa only [hquery] using (ValidQuerySubst.nil_iff.mpr rfl : ValidQuerySubst d [] []),
        hfire⟩
  rw [RunRules.eq_sUnion, hresults]
  apply Database.ext
  · exact (evalLocalActions_sig hfire).symm
  · simp [Database.sUnion, hempty]
  · exact (evalLocalActions_env hfire).symm
  · exact (evalLocalActions_rules hfire).symm

private theorem source_rule : CmdStep sourceDeclared (.rule initialRule) sourceRegistered := by
  apply CmdStep.of_reach
  · change sourceRegistered =
      { sourceDeclared with rules := insert initialRule sourceDeclared.rules }
    simp [sourceRegistered, sourceDeclared, Database.empty]
  · exact empty_normal rfl

private theorem source_run : CmdStep sourceRegistered (.run "seed") sourceBuilt :=
  .of_reach (run_initializer (d := sourceRegistered) (e := sourceBuilt)
    (r := initialRule) rfl rfl rfl rfl).symm (constructors_normal source_ctors)

theorem source_success : Eval Database.empty successProgram (.ok sourceBuilt) := by
  exact .cons (.ok source_decl)
    (.cons (.ok source_rule) (.cons (.ok source_run) (.cons (.ok ⟨source_check, rfl⟩) .nil)))

theorem source_failure : Eval Database.empty failureProgram .checkFailed := by
  exact .cons (.ok source_decl)
    (.fail (.checkFailed (no_query_of_empty (d := sourceDeclared) rfl (by decide))))

def targetSetup : Program :=
  [.decl ufName (tableDecl 1), .decl "C" (ctorDecl 0),
   .decl (viewName "C") (tableDecl 0),
   .rule pathCompressRule, .rule (eclassRule "C" 0)]

def targetDeclared : Database :=
  { sig := Function.update
      (Function.update (Function.update Database.empty.sig ufName (some (tableDecl 1)))
        "C" (some (ctorDecl 0))) (viewName "C") (some (tableDecl 0)),
    eqs := ∅, env := [], rules := insert (eclassRule "C" 0) (insert pathCompressRule ∅) }

private theorem target_setup : ProgramStep Database.empty targetSetup targetDeclared := by
  exact .cons (.of_reach rfl (empty_normal rfl))
    (.cons (.of_reach rfl (empty_normal rfl)) (.cons (.of_reach rfl (empty_normal rfl))
      (.cons (.of_reach rfl (empty_normal rfl)) (.cons (.of_reach rfl (empty_normal rfl)) .nil))))

private def targetRegistered : Database :=
  { targetDeclared with rules := insert (encodeRule initialRule) targetDeclared.rules }

private theorem target_register : ProgramStep targetDeclared
    ((encodeCmd 1 (.rule initialRule)).map Command.command) targetRegistered :=
  .cons (.of_reach rfl (empty_normal rfl)) .nil

private theorem success_encoding : encode successProgram = targetSetup ++
    (encodeCmd 1 (.rule initialRule)).map Command.command ++
    (encodeCmd 2 (.run "seed")).map Command.command ++ [.check viewQuery] := by rfl

private theorem failure_encoding : encode failureProgram = targetSetup ++ [.check viewQuery] :=
  by rfl

/-- The compiled initialization round and rebuilding finish before the nonempty check. -/
theorem target_success : ∃ d, Eval Database.empty (encode successProgram) (.ok d) := by
  have hp : ProgramStep Database.empty [.decl "C" (ctorDecl 0), .rule initialRule]
      sourceRegistered := .cons source_decl (.cons source_rule .nil)
  have htp : ProgramStep Database.empty
      ((encodePrelude successProgram ++
        encodeCmds [.decl "C" (ctorDecl 0), .rule initialRule] 0).map Command.command)
      targetRegistered := target_setup.append target_register
  have hboundary := Abstract.boundary_prefix success_fragment
    (show successProgram = [.decl "C" (ctorDecl 0), .rule initialRule] ++
      [.run "seed", .check constructorQuery] from rfl) hp htp
  obtain ⟨d, hd⟩ := hboundary.run_exists success_fragment rfl hp htp source_run
  have hsrc : ProgramStep Database.empty
      [.decl "C" (ctorDecl 0), .rule initialRule, .run "seed"] sourceBuilt :=
    .cons source_decl (.cons source_rule (.cons source_run .nil))
  have htgt := Abstract.compiled_prefix_step htp hd
  have hcheck : QueryHolds d viewQuery :=
    (Abstract.checkAgreement success_fragment
      [.decl "C" (ctorDecl 0), .rule initialRule, .run "seed"] constructorQuery []
      sourceBuilt d rfl hsrc htgt).mp source_check
  refine ⟨d, ?_⟩
  rw [success_encoding]
  exact Eval.append_of_ok ((target_setup.append target_register).append hd)
    (.cons (.ok ⟨hcheck, rfl⟩) .nil)

theorem target_failure : Eval Database.empty (encode failureProgram) .checkFailed := by
  rw [failure_encoding]
  apply Eval.append_of_ok target_setup
  exact .fail (.checkFailed (no_query_of_empty (d := targetDeclared) rfl (by decide)))

/-- The theorem's premises include a constructed value and a successful nonempty check. -/
theorem successful_instance :
    successProgram.WellFormed ∧ successProgram.Fragment ∧ successProgram.NoSaturate ∧
    ∃ source target, Eval Database.empty successProgram source ∧
      Eval Database.empty (encode successProgram) target ∧
      source.succeeded = true ∧ target.succeeded = true := by
  obtain ⟨d, hd⟩ := target_success
  exact ⟨success_wellFormed, success_fragment, success_noSaturate, .ok sourceBuilt, .ok d,
    source_success, hd, rfl, rfl⟩

/-- Both premises are also inhabited for genuine dynamic check failure. -/
theorem failing_instance :
    failureProgram.WellFormed ∧ failureProgram.Fragment ∧ failureProgram.NoSaturate ∧
    ∃ source target, Eval Database.empty failureProgram source ∧
      Eval Database.empty (encode failureProgram) target ∧
      source.succeeded = false ∧ target.succeeded = false := by
  refine ⟨failure_wellFormed, failure_fragment, failure_noSaturate, .checkFailed, .checkFailed,
    source_failure, target_failure, rfl, ?_⟩
  exact (preservesObservations failureProgram failure_wellFormed failure_fragment _ _
    source_failure target_failure).symm

/-- The finite-outcome contract rejects a compiler that simply erases every program. -/
theorem rejects_empty_compiler : ¬ (∀ P : Program, P.WellFormed → P.Fragment →
    P.NoSaturate →
    ∀ source target : Result, Eval Database.empty P source →
      Eval Database.empty ([] : Program) target → source.succeeded = target.succeeded) := by
  intro h
  have heq := h failureProgram failure_wellFormed failure_fragment failure_noSaturate .checkFailed
    (.ok Database.empty) source_failure .nil
  contradiction

-- These obtain target executions from the termination theorem itself.
theorem finite_success : ∃ target, Eval Database.empty (encode successProgram) target ∧
    target.succeeded = true := by
  obtain ⟨target, ht, he⟩ := preservesFiniteObservations successProgram success_wellFormed
    success_fragment success_noSaturate _ source_success
  exact ⟨target, ht, he.symm⟩

theorem finite_failure : ∃ target, Eval Database.empty (encode failureProgram) target ∧
    target.succeeded = false := by
  obtain ⟨target, ht, he⟩ := preservesFiniteObservations failureProgram failure_wellFormed
    failure_fragment failure_noSaturate _ source_failure
  exact ⟨target, ht, he.symm⟩

private def createRule : Rule := ⟨[], [.expr constructorExpr], "R"⟩
private def roundProgram : Program :=
  [.decl "C" (ctorDecl 0), .rule createRule, .run "R", .check constructorQuery]
private def sourceRule : Database :=
  { sourceDeclared with rules := insert createRule sourceDeclared.rules }
private def sourceRan : Database := RunRules "R" sourceRule

private theorem round_wellFormed : roundProgram.WellFormed := by decide
private theorem round_noSaturate : roundProgram.NoSaturate := by
  simp [Program.NoSaturate, roundProgram, Cmd.NoSaturate]
private theorem round_fragment : roundProgram.Fragment := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, by decide, by decide, by decide⟩
  intro n hn
  change n ∈ ["C", "R"] at hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact safe_name
  · obtain rfl := List.mem_singleton.mp hn
    rw [String.isPrefixOf, String.startsWith_string_iff]
    decide

private theorem source_round_success : Eval Database.empty roundProgram (.ok sourceRan) := by
  have hfire : evalLocalActions sourceRule createRule.actions [] =
      some (sourceRule.addTerm ctorTerm) := rfl
  have hcontains : (sourceRule.addTerm ctorTerm).Contained sourceRan := by
    rw [sourceRan, RunRules.eq_sUnion]
    exact Database.Contained.mem_sUnion ⟨createRule, by simp [sourceRule], rfl,
      [], ValidQuerySubst.nil_iff.mpr rfl, hfire⟩
  have hcheck : QueryHolds sourceRan constructorQuery := by
    obtain ⟨σ, hσ, _⟩ := Abstract.validQuerySubst_of_flatReads
      (d := sourceRan) (ρ := []) (q := constructorQuery)
      (by simp [Env.lookup]) (by
        intro p hp
        obtain rfl := List.mem_singleton.mp hp
        exact .entry ⟨ctorDecl 0, rfl, Or.inl rfl⟩ rfl
          (hcontains.terms (Database.mem_addTerm _ _)))
      (by intro p hp; obtain rfl := List.mem_singleton.mp hp; rfl)
    exact queryHolds_iff_validQuerySubst.mpr ⟨σ, hσ⟩
  exact .cons (.ok source_decl)
    (.cons (.ok (.of_reach rfl (empty_normal rfl)))
      (.cons (.ok (.of_reach rfl (constructors_normal source_ctors)))
        (.cons (.ok ⟨hcheck, rfl⟩) .nil)))

-- One source round creates the checked term; compiled rebuilding must terminate too.
theorem finite_rule_round : ∃ target, Eval Database.empty (encode roundProgram) target ∧
    target.succeeded = true := by
  obtain ⟨target, ht, he⟩ := preservesFiniteObservations roundProgram round_wellFormed
    round_fragment round_noSaturate _ source_round_success
  exact ⟨target, ht, he.symm⟩

private def a : Term := .app "A" []
private def b : Term := .app "B" []
private def fa : Term := .app "F" [a]
private def fb : Term := .app "F" [b]
private def queryFB : Query := [.expr (.app "F" [.app "B" []])]

private def congruenceInitializer : Rule :=
  ⟨[], [.union (.app "A" []) (.app "B" []), .expr (.app "F" [.app "A" []])], "seed"⟩

/-- The final check needs congruence: the initialization rule only builds `F(A)`. -/
def congruenceProgram : Program :=
  [.decl "A" (ctorDecl 0), .decl "B" (ctorDecl 0), .decl "F" (ctorDecl 1),
   .rule congruenceInitializer, .run "seed", .check queryFB]

private def declaredA : Database :=
  { Database.empty with sig := Function.update Database.empty.sig "A" (some (ctorDecl 0)) }
private def declaredAB : Database :=
  { declaredA with sig := Function.update declaredA.sig "B" (some (ctorDecl 0)) }
private def declaredABF : Database :=
  { declaredAB with sig := Function.update declaredAB.sig "F" (some (ctorDecl 1)) }
private def registeredABF : Database :=
  { declaredABF with rules := {congruenceInitializer} }
private def unitedAB : Database := registeredABF.addEq a b
private def builtFA : Database := unitedAB.addTerm fa

private theorem congruence_ctors : declaredABF.sig.AllConstructors := by
  intro f
  by_cases hF : f = "F"
  · subst f; rfl
  · by_cases hB : f = "B"
    · subst f; rfl
    · by_cases hA : f = "A"
      · subst f; rfl
      · simp [declaredABF, declaredAB, declaredA, Database.empty, Signature.mergeOf,
          hF, hB, hA]

private theorem congruence_fragment : congruenceProgram.Fragment := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, by decide, by decide, by decide⟩
  intro n hn
  have hs : ∀ n ∈ congruenceProgram.names, ¬ "@".isPrefixOf n := by
    simp only [String.isPrefixOf, String.startsWith_string_iff]
    decide
  exact hs n hn

private theorem congruence_check : QueryHolds builtFA queryFB := by
  have hfa : fa ∈ builtFA.terms := Database.mem_addTerm _ _
  have hab : Cong builtFA a b := Cong.mono (Database.Contained.addTerm _ _) (.direct
    (Set.mem_insert _ _))
  have hread : Cong builtFA fa fb := .congr (Database.toCong hfa) (.cons hab .nil)
  refine queryHolds_iff_validQuerySubst.mpr
    ⟨[], [[]], .cons ⟨?_, Matches.atom rfl (hread.symm.trans hread)⟩ .nil, .single []⟩
  exact ⟨List.Perm.refl [], by simp⟩

private theorem congruence_source : Eval Database.empty congruenceProgram (.ok builtFA) := by
  have hA : CmdStep Database.empty (.decl "A" (ctorDecl 0)) declaredA :=
    .of_reach rfl (empty_normal rfl)
  have hB : CmdStep declaredA (.decl "B" (ctorDecl 0)) declaredAB :=
    .of_reach rfl (empty_normal rfl)
  have hF : CmdStep declaredAB (.decl "F" (ctorDecl 1)) declaredABF :=
    .of_reach rfl (empty_normal rfl)
  have hregister : CmdStep declaredABF (.rule congruenceInitializer) registeredABF := by
    apply CmdStep.of_reach
    · change registeredABF =
        { declaredABF with rules := insert congruenceInitializer declaredABF.rules }
      simp [registeredABF, declaredABF, declaredAB, declaredA, Database.empty]
    · exact empty_normal rfl
  have hrun : CmdStep registeredABF (.run "seed") builtFA :=
    .of_reach (run_initializer (d := registeredABF) (e := builtFA)
      (r := congruenceInitializer) rfl rfl rfl rfl).symm (constructors_normal congruence_ctors)
  exact .cons (.ok hA) (.cons (.ok hB) (.cons (.ok hF)
    (.cons (.ok hregister) (.cons (.ok hrun) (.cons (.ok ⟨congruence_check, rfl⟩) .nil)))))

/-- The witness succeeds without inserting the queried spelling into the source store. -/
theorem congruence_without_stored_spelling :
    fb ∉ builtFA.terms ∧ QueryHolds builtFA queryFB := by
  refine ⟨?_, congruence_check⟩
  have he : declaredABF.terms = ∅ := Database.terms_empty_of_eqs_empty rfl
  simp [builtFA, unitedAB, registeredABF, a, b, fa, fb, he]

theorem finite_congruence_check :
    ∃ target, Eval Database.empty (encode congruenceProgram) target ∧
      target.succeeded = true := by
  obtain ⟨target, ht, he⟩ := preservesFiniteObservations congruenceProgram (by decide)
    congruence_fragment
    (by simp [Program.NoSaturate, congruenceProgram, Cmd.NoSaturate]) _ congruence_source
  exact ⟨target, ht, he.symm⟩

/-- The full contract applies to real successes and dynamic failures. -/
theorem full_success_behavior :
    Behaves Database.empty (encode successProgram) .success ∧
      ¬ Behaves Database.empty (encode successProgram) .diverges :=
  ⟨(preservesBehaviors successProgram success_wellFormed success_fragment
      success_noSaturate .success).mpr ⟨sourceBuilt, source_success⟩,
    not_encode_diverges success_fragment success_noSaturate⟩

theorem full_failure_behavior :
    Behaves Database.empty (encode failureProgram) .checkFailed ∧
      ¬ Behaves Database.empty (encode failureProgram) .diverges :=
  ⟨(preservesBehaviors failureProgram failure_wellFormed failure_fragment
      failure_noSaturate .checkFailed).mpr source_failure,
    not_encode_diverges failure_fragment failure_noSaturate⟩

theorem rejects_empty_behavior_compiler :
    ¬ (∀ P : Program, P.WellFormed → P.Fragment → P.NoSaturate → ∀ b : Behavior,
      Behaves Database.empty [] b ↔ Behaves Database.empty P b) := by
  intro h
  have he := (h failureProgram failure_wellFormed failure_fragment failure_noSaturate
    .checkFailed).mpr source_failure
  cases he

/-- A compiler that introduces a real divergent execution violates the full contract. -/
theorem rejects_diverging_behavior_compiler :
    ∃ Q : Program, ProgramDiverges Database.empty Q ∧
      ¬ (∀ P : Program, P.WellFormed → P.Fragment → P.NoSaturate → ∀ b : Behavior,
        Behaves Database.empty Q b ↔ Behaves Database.empty P b) := by
  obtain ⟨Q, hQ⟩ := Divergence.divergent_from_empty
  refine ⟨Q, hQ, ?_⟩
  intro h
  exact (neither_diverges success_fragment success_noSaturate).1
    ((h successProgram success_wellFormed success_fragment success_noSaturate .diverges).mp hQ)

end Egglog.Tests.CongruenceCorrectness
