import EgglogSemantics.Spec.Syntax
import EgglogSemantics.Spec.Term
import EgglogSemantics.Spec.Database
import EgglogSemantics.Spec.Congruence
import EgglogSemantics.Spec.Eval
import EgglogSemantics.Spec.Match
import EgglogSemantics.Spec.Step
import EgglogSemantics.Spec.Divergence
import EgglogSemantics.Spec.Behavior
import EgglogSemantics.Spec.Order
import EgglogSemantics.Source.Domain
import EgglogSemantics.Source.WellFormed
import EgglogSemantics.Proofs.OrderFinite
import EgglogSemantics.Congruence.Correctness
import EgglogSemantics.Proofs.InterpDeletes
import EgglogSemantics.Proofs.Deletes
import EgglogSemantics.Proofs.Provenance.GeneratedSoundness
import EgglogSemantics.Proofs.Resugar.Soundness
import Mathlib.Util.AssertNoSorry

/-! The modules whose blueprint nodes the paper displays, and the proof closure the paper
relies on. The congruence pass theorem is displayed as a statement
(`Congruence.Correctness`); its proof for the constructor-and-delete encoding is open. -/

-- The term order the compiled rebuilding uses.
assert_no_sorry Egglog.Term.blt_admissible

-- Matching, deletion, rounds, and evaluation agree with their presentations and are
-- deterministic.
assert_no_sorry Egglog.queryHolds_iff_validQuerySubst
assert_no_sorry Egglog.Database.deleteRows_eq
assert_no_sorry Egglog.RunErases.eq_empty
assert_no_sorry Egglog.RunRules.eq_addEqs
assert_no_sorry Egglog.RunRules.eq_sUnion
assert_no_sorry Egglog.RunRules.wf
assert_no_sorry Egglog.Eval.det
assert_no_sorry Egglog.SourceMeaning.completion_closed_of_saturated

-- The reference interpreter refines the specification, up to meaning, for delete-free
-- programs and for union-free programs with deletes (the compiler's output), and decides
-- the final check as the specification does.
assert_no_sorry Egglog.patternHolds_iff
assert_no_sorry Egglog.FDatabase.holds_iff_queryHolds
assert_no_sorry Egglog.exec_programStep
assert_no_sorry Egglog.exec_complete
assert_no_sorry Egglog.observe_eval
assert_no_sorry Egglog.exec_programStep_noUnions
assert_no_sorry Egglog.exec_complete_noUnions
assert_no_sorry Egglog.observe_eval_noUnions
assert_no_sorry Egglog.Congruence.exec_encode_programStep

-- Certificates: checked source proofs infer their claims, and so does everything the
-- firing-log extraction and lifting return.
assert_no_sorry Egglog.SourceProof.check_infers
assert_no_sorry Egglog.Provenance.extract_checked
assert_no_sorry Egglog.Provenance.Generated.check_uf_infers
assert_no_sorry Egglog.Resugar.extractAll_infers
assert_no_sorry Egglog.Resugar.certificates_infers
