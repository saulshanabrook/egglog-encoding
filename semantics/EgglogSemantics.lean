-- Specification
import EgglogSemantics.Spec.Behavior
import EgglogSemantics.Spec.Congruence
import EgglogSemantics.Spec.Database
import EgglogSemantics.Spec.Divergence
import EgglogSemantics.Spec.Eval
import EgglogSemantics.Spec.Match
import EgglogSemantics.Spec.Order
import EgglogSemantics.Spec.Scope
import EgglogSemantics.Spec.Sequential
import EgglogSemantics.Spec.Step
import EgglogSemantics.Spec.Syntax
import EgglogSemantics.Spec.Term

-- Source fragment
import EgglogSemantics.Source.Domain
import EgglogSemantics.Source.Names
import EgglogSemantics.Source.WellFormed

-- Executable interpreter
import EgglogSemantics.Impl.Closure
import EgglogSemantics.Impl.Interp
import EgglogSemantics.Impl.Observe

-- Congruence compiler
import EgglogSemantics.Congruence.Correctness
import EgglogSemantics.Congruence.Encode
import EgglogSemantics.Congruence.Read
import EgglogSemantics.Congruence.Reader
import EgglogSemantics.Congruence.Relational

-- Source proofs
import EgglogSemantics.SourceProof.Checker
import EgglogSemantics.SourceProof.Evaluate
import EgglogSemantics.SourceProof.Format

-- Provenance
import EgglogSemantics.Provenance.Checker
import EgglogSemantics.Provenance.Encode
import EgglogSemantics.Provenance.Extract
import EgglogSemantics.Provenance.Format

-- Lifting
import EgglogSemantics.Resugar.Builder
import EgglogSemantics.Resugar.Claim
import EgglogSemantics.Resugar.Execute
import EgglogSemantics.Resugar.Export
import EgglogSemantics.Resugar.Fixtures
import EgglogSemantics.Resugar.Lift
import EgglogSemantics.Resugar.Query

-- Proofs
import EgglogSemantics.Proofs.ActionMonotone
import EgglogSemantics.Proofs.ActionProgram
import EgglogSemantics.Proofs.Assignments
import EgglogSemantics.Proofs.Behavior
import EgglogSemantics.Proofs.Bindings
import EgglogSemantics.Proofs.Closure
import EgglogSemantics.Proofs.Completion
import EgglogSemantics.Proofs.Congruence
import EgglogSemantics.Proofs.Congruence.Properties
import EgglogSemantics.Proofs.Database
import EgglogSemantics.Proofs.Deletes
import EgglogSemantics.Proofs.Diagonal
import EgglogSemantics.Proofs.DiagonalPreservation
import EgglogSemantics.Proofs.DiagonalRound
import EgglogSemantics.Proofs.Divergence
import EgglogSemantics.Proofs.Entries
import EgglogSemantics.Proofs.EnvTransform
import EgglogSemantics.Proofs.Eval
import EgglogSemantics.Proofs.Execution
import EgglogSemantics.Proofs.Finite
import EgglogSemantics.Proofs.FiniteSaturation
import EgglogSemantics.Proofs.Interp
import EgglogSemantics.Proofs.InterpDeletes
import EgglogSemantics.Proofs.LiveTables
import EgglogSemantics.Proofs.Match
import EgglogSemantics.Proofs.MatchMonotone
import EgglogSemantics.Proofs.MatchValues
import EgglogSemantics.Proofs.MatchingCounterexamples
import EgglogSemantics.Proofs.Merge
import EgglogSemantics.Proofs.NoUnions
import EgglogSemantics.Proofs.Operands
import EgglogSemantics.Proofs.Order
import EgglogSemantics.Proofs.OrderFinite
import EgglogSemantics.Proofs.Presentation
import EgglogSemantics.Proofs.Provenance.Counterexamples
import EgglogSemantics.Proofs.Provenance.Facts
import EgglogSemantics.Proofs.Provenance.GeneratedClaim
import EgglogSemantics.Proofs.Provenance.GeneratedEvaluation
import EgglogSemantics.Proofs.Provenance.GeneratedSoundness
import EgglogSemantics.Proofs.Provenance.Model
import EgglogSemantics.Proofs.Provenance.Soundness
import EgglogSemantics.Proofs.Query
import EgglogSemantics.Proofs.Resugar.Soundness
import EgglogSemantics.Proofs.Result
import EgglogSemantics.Proofs.SameMeaning
import EgglogSemantics.Proofs.Scope
import EgglogSemantics.Proofs.SemanticCong
import EgglogSemantics.Proofs.Setup
import EgglogSemantics.Proofs.Source.Arity
import EgglogSemantics.Proofs.Source.Ctors
import EgglogSemantics.Proofs.Source.Domain
import EgglogSemantics.Proofs.Source.Execution
import EgglogSemantics.Proofs.Source.FreshBindings
import EgglogSemantics.Proofs.Source.FreshEnv
import EgglogSemantics.Proofs.Source.RebuildVars
import EgglogSemantics.Proofs.Source.Termination
import EgglogSemantics.Proofs.SourceMeaning
import EgglogSemantics.Proofs.SourceModel
import EgglogSemantics.Proofs.SourceProof.Actions
import EgglogSemantics.Proofs.SourceProof.Counterexamples
import EgglogSemantics.Proofs.SourceProof.Ledger
import EgglogSemantics.Proofs.SourceProof.Matching
import EgglogSemantics.Proofs.SourceProof.Rules
import EgglogSemantics.Proofs.SourceProof.Soundness
import EgglogSemantics.Proofs.SourceProof.Support
import EgglogSemantics.Proofs.StatePreservation
import EgglogSemantics.Proofs.Step
import EgglogSemantics.Proofs.StoredCong
import EgglogSemantics.Proofs.Syntax
import EgglogSemantics.Proofs.Term
import EgglogSemantics.Proofs.Writes

-- Tests
import EgglogSemantics.Tests.Checks
import EgglogSemantics.Tests.Congruence
import EgglogSemantics.Tests.Egg
import EgglogSemantics.Tests.Examples
import EgglogSemantics.Tests.Parse
import EgglogSemantics.Tests.ProofPass
import EgglogSemantics.Tests.Provenance
import EgglogSemantics.Tests.Render
import EgglogSemantics.Tests.Resugar
import EgglogSemantics.Tests.SemanticCong
import EgglogSemantics.Tests.SourceProof
import EgglogSemantics.Tests.SourceProofCorrectness
import EgglogSemantics.Tests.SubtermExistence

/-! The whole library. The modules under `Proofs/Congruence/` other than `Properties`
concern the previous, merge-function encoding and are not built; `Tests/{CongruenceCorrectness,
LeaderGrowth,LiveCompiler,LiveSemantics}` depend on them. -/
