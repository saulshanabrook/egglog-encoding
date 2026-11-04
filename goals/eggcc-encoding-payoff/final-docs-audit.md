# Final documentation and Diátaxis audit

Verdict: **PASS**. No binding documentation, link, evidence-path, terminology,
count, or static reproduction-command finding remains. This audit ran no
build, compiler, native program, timing campaign, or network command and edited
no other file.

## Diátaxis and reader flow

- [`report.md`](report.md) is a connected explanation. It starts from the
  mathematical laws, follows QR7 and Parts32 through scoped EggCC imports and
  exact consumers, connects the resulting code changes to the measurements,
  and finishes with negative probes, validation boundaries, and nonclaims. It
  contains no replay procedure.
- [`reference.md`](reference.md) is a compact factual lookup for terms, rules,
  execution/storage behavior, host obligations, treatments, implemented and
  failed cases, identities, counts, and supported claim boundaries.
- [`reproduce.md`](reproduce.md) owns evidence review, correctness replay,
  performance replay, validation review, and failure interpretation. It keeps
  diagnostic durations and compiler-time measurements separate from accepted
  generated-runtime evidence.
- The Pack32 report cleanly separates portfolio supersession from the later
  fail-closed actual probe. The final validation summary separates passing
  repository/engine/DAG checks from the non-green host snapshot and lint
  commands.

The explanation distinguishes QR7's injectivity-only equality-to-memory path
from Parts32's combined forward/reverse disequality path. It names the exact
added bridge or contextual union that consumes each result and explains what
Manual, primitive-only, knockout, rescue, and neutral controls establish.
Same-mask is explicitly a smaller independent replication rather than a stage
of Parts32.

## Parts32 false-`If` boundary

The recent correction is accurate and consistent across the explanation and
Parts32 authority. The `if-consumer-off` treatment disables the named
non-weakly-linear false-`If` rule, while the interval false-`If` rule remains
enabled and extraction or the backend may also consume the constant. The text
therefore concludes only that the named rule is nonessential and does not name
an unproved alternate consumer. The causal endpoint remains the contextual
`Eq=false` application: `consumer-off` restores U0, whereas `if-consumer-off`
retains optimized code. This agrees with the retained patch, source validation,
and `final-reviewed/inspection.json`.

## Links, paths, statuses, and identities

- Every Markdown link in the six final goal documents, the Pack32 report, and
  the final validation summary resolves. Every local heading anchor resolves.
- All 55 `strongest_evidence_paths` entries in
  [`acceptance.json`](acceptance.json) exist.
- `acceptance.json` names the local [`facts.md`](facts.md), and its
  `facts_source_sha256` matches the current file.
- The acceptance map contains 14 facts: 13 pass, zero pending, zero fail, and
  one not applicable. Those counts and the generated-runtime route agree with
  [`acceptance.md`](acceptance.md) and [`STATUS.md`](STATUS.md).
- No stale open-lead, authentication-failure, running-validation, or
  acceptance-pending language remains in the audited final documents.
  References to 13 pending snapshots describe current retained host failures,
  not task status.
- All 16 SHA-256 values explicitly presented for the QR7, Parts32, same-mask,
  and compiler-diagnostic authorities match the current files.
- The audited text consistently avoids claims of a compiler bug, suite-wide
  speedup, compiler-time speedup, unique logical power, exact LLVM pass order,
  or successful P1/A1 endpoint.

## Counts and terminology

- QR7's 37 compiler cases, 177 native checks, 91/2 versus 55/0 process-entry
  shape, 3,136 confirmation rows, hot ratio and interval, and neutral ratio and
  interval agree with its retained JSON.
- Parts32's 200 native checks, two 1,350-row sessions, 18 passing speed gates,
  six separately reported Encoding/U0 cells, and placebo status agree with its
  inspection and independent verifier.
- Same-mask's 32 cycles and reported ratios agree with its retained summary.
- P1's four corpora total 93 rows, 243 exact native outputs, 156 rejected
  queries, zero accepted or exported witnesses, and one emitted/native hash
  group, matching the new Pack32 report.
- A1's 31 interpreter pairs, 233 native checks, 18 identical positive
  endpoints, zero exports, and terminal one-revision boundary agree with its
  summary.
- The final summary, report, reference, acceptance, and status agree on the
  green repository-root check, green selected-engine check, green 70-test DAG
  suite, non-green host root due to 13 unaccepted dependency-retarget
  snapshots, and non-green host nits due to one inherited U0 Clippy diagnostic.
  None converts those attributed host failures into green checks or a
  merge-readiness claim.

## Reproduction-command audit

The four findings from the first pass are resolved:

1. The Parts32 inspector is copied with `final-reviewed` into a fresh
   `mktemp` root, so its function extracts, diffs, and inspection JSON are
   written only into the copy.
2. The same-mask evidence tree is copied into a fresh `mktemp` root before its
   verifier writes `final-evidence-audit.json`. The guide retains the necessary
   live-source prerequisite and does not call this a cold-checkout replay.
3. U0 archive reconstruction and the Parts32 matrix now use unique `mktemp`
   roots. They cannot reuse the driver's resumptive arm directories or
   overwrite a fixed `/tmp` archive or phase summary.
4. The compiler diagnostic copies `run.py` and its frozen design into a fresh
   root, links the immutable sibling command map, and links the original shared
   measurement-exclusion lock. Because the driver resolves `output_root`
   relative to its copied `__file__`, diagnostic artifacts go to the fresh
   root.

The copied compiler-diagnostic layout was exercised with its `validate`
subcommand. It passed the frozen design, command-map, source, compiler, output,
and schedule checks; resolved the exclusion lock to the retained shared lock;
resolved `results` beneath the temporary copy; reported that the result did not
exist; and reported `compiler_processes_launched: 0`. Static review confirms
that the documented `run --acknowledge-diagnostic-only` command uses that same
validated layout and creates its result beneath the copy.

The remaining replay sections either read retained evidence directly or
explicitly create/copy into fresh output roots before a writer runs. Their
scope statements accurately distinguish immutable-binary replay, optional
already-reconstructed source validation, retained-row verification, fresh
performance collection, and diagnostic compiler timing. No documentation-only
repair requires another build or timing run.
