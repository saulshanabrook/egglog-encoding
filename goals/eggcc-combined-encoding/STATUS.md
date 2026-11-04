# Richer EggCC encoding case

Complete: the accepted positive path is satisfied. A default-off integration uses injectivity and disequality together to check nested EggCC type metadata through the existing ExpectType diagnostic. The old and manual checks reach the same result; no new baseline bug, optimization or speedup is claimed.

Read [report.md](report.md), [reference.md](reference.md), [reproduction.md](reproduction.md) and [completion-audit.md](completion-audit.md). The accepted facts and approved plan are unchanged.

## Outcome and source

- Compiler: `/Users/saul/p/wt/eggcc/combined-encoding`, branch `codex/eggcc-combined-encoding`.
- Encoding dependency: `/Users/saul/p/wt/egglog-encoding/eggcc-combined-encoding`.
- Fresh pre-integration control: `/Users/saul/p/wt/eggcc/combined-encoding-control`.
- Raw evidence: ignored `benchmarks/local/eggcc-combined-encoding/`.
- Final source manifest: `consumer/oracle-final/source.json`, SHA `8165c4521d16ea4f5d1cffe66a08092962b55b8976f37c2b6a2553bfc5352738`.
- Functional checkpoint: `227599b8ac493ecb60b012191d8d56b7ae90e602ad721992f8c00c8ec2a6b985`.
- Final gate summary: `b116e66101b0cd69c25ea53e7725e4b356c3fca3074999ef42c046c1192f1b69`.

18 engine tests, nine focused DAG tests, 54 independent Rust Type comparisons, 50 query observations, ten consumer outcomes, a five-mode native host test, a CLI-parser test and ten primary CLI optimize/emit runs validate the bounded integration. The final oracle delta is test-only; reuse of older host/CLI receipts is bound to identical production code.

Official compiler test/nit gates remain failed on 13 pending snapshots and three strict Clippy sites freshly matched to the control. Candidate/control full DAG suites pass 83/74; formatting passes. Default-Off prologue bytes are identical. All 30,609 protected old files, candidate/control source, encoding source and accepted snapshots are unchanged. No snapshot acceptance or lint allowance was used.

## Closed execution contracts

| Agent | Domain | Final state |
| --- | --- | --- |
| root | Coordination, docs and fact audit | Accepted positive result; final source/artifact/static checks complete |
| combined_consumers | Compiler implementation and functional evidence | Complete; no pending edits/runs |
| study_semantics | Type contract, source and oracle review | Scoped consent; no remaining blocker |
| study_harness | Reconstruction, strict gates, attribution and preservation | 47 terminal receipts; slot released; no active owned processes |
| document_review | Diátaxis and collaborator readability | No blocker; optional representation-name clarification applied |

No required goal work remains. Other candidate directions are future leads, not an exhausted search. Earlier studies and frozen evidence remain separate. No commits, pushes, paper edits, proof support or Lean work were included. Memory-pressure blocking remained disabled as requested; timeout/error reporting was retained.
