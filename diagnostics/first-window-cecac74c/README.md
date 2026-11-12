# First collection window: full-query substitution diagnostic

This is the complete, unchanged evidence for the first five-layer campaign,
ending at source `cecac74c2a2a4fcdc9400b3e6fadf560b51aed89` (preserved as
`perf/slotted-full-query-diagnostic`). The timing window closed at
2026-11-12T12:45:29.570252+00:00. All 354 selected observations succeeded;
all samples are retained. No workloads or outliers were removed.

The full-query substitution strategy improved the nested ΣMMM/MMM cases but
regressed encoded multipattern workloads. At layer 10, TTM 2nd took about
5.82 times its parent's runtime (95% interval 5.78–5.86), and the multipattern
suite took about 1.80 times as long (1.78–1.82). This triggered a matcher-aware
revision before publication. These plots describe the original implementation,
not the revised layer 10 or 11.

From main to the original final layer, the nested suite ratio was
1.063 (95% interval 0.940–1.189), inconclusive; encoded multipattern was
1.832 (1.740–1.926), a regression. Nested ΣMMM 1st fell from 167.2 to 142.7ms,
ΣMMM 2nd from 562.6 to 527.2ms, and MMM 1st from 325.2 to 278.4ms.
MMM 2nd changed from 2120.3 to 2095.0ms with an interval crossing 1.
The cumulative results and focus JSON retain exact values and intervals.

`collection-manifest.json` is the original, byte-for-byte source/protocol
binding. `manifest.json` is a derived offline rendering binding pointing at
this frozen grouped export; it explicitly identifies the diagnostic window.
`snapshot.json` records original absolute paths and hashes for frozen inputs.
`artifact-files.json` checksums all publication files in this directory.
`report-grouped.json` is the complete public export. Raw tool-owned JSONL was
never manually read or copied. `artifacts/` holds all five PNG/SVG/PDF bundles,
bound specifications, and selected results. `final-artifact-validation.json`
records the successful selection/hash audit, actual visual inspection of all
five plots near 800px, and embedded PDF fonts.

`validation/` retains the exact original validation metadata and logs with
original absolute-path provenance. It certifies the original source only.
The final revised campaign has separate validation evidence. Protocol,
commands, environment, build markers, and source/binary/input hashes remain
available here; no frozen input was changed when the revision began.
