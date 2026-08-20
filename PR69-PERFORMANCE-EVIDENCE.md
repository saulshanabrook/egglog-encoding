# PR 69 performance evidence disposition

This note supersedes the interpretation, not the contents, of the sealed
August 19 archive for baseline `fdd4eac12c1` and candidate `1c974cf99a8`.
The raw JSONL, original `provenance.md` and `results.md`, and checksum
manifests remain byte-for-byte unchanged. All archived checksums verify;
the SHA-256 of `archive-files.sha256` is
`ce79dbfe6e36cabd30d58f3b1dc57bc35546e0e13a2f1b1f1ede9e13ee1b3b38`.

The archived `term` ratio `0.887905` and `proofs` ratio `0.859259` are
reproducible calculations from the recorded rows, but they are withdrawn as
overall speedup and follow-up-sizing claims. Both collections contain visible
unmonitored timing transients. No post-hoc subset is substituted for them;
decision-bearing timing requires a new continuously monitored run.

The comparatively stable `off` collection measured `1.003608`, 95% Fieller CI
`[0.993136, 1.014144]`, consistent with no measured off-mode change in that run.
The durable causal claim is structural: generated proof commands no longer
re-enter source parsing, desugaring, typechecking, or `remove_globals`. A
permanent call-counting regression covers the complete `add_term_encoding` plus
`resolve_generated_batch` window; archived phase timings have the expected
direction, but their exact magnitude is not clean sizing evidence.

Churchroad remains a performance risk. Its proofs-mode point estimate was
`1.011920`, CI `[1.000121, 1.023817]`, initially and `1.023252`,
CI `[0.999861, 1.046852]`, on retest. The slowdown direction reproduced and
the point estimate grew; the retest made statistical boundedness inconclusive
rather than showing that the slowdown disappeared.

Four proof workloads retained `CI high < 1` in both collections. Treat these as
workload-level witnesses, not an overall PR speedup percentage. Upstream
winner-recording and duplicate-solving remain tracked solely in issue #76.
