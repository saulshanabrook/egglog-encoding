# Independent scoped-sort audit — 2026-10-19

No implementation blocker found in the reviewed exact-chain probe. This audit covers the signed-sort law, expression import, scope transport, finite manual closure, generic-engine controls, consumer application, and the external primitive-only null. It does not certify the main matrix or host test suite, which were still running when this audit was requested.

The key (signed min, signed max, Select(a < b, 1, 0)) is injective over all signed i64 pairs. Ties reconstruct correctly; MIN/MAX need no arithmetic assumption. Import requires all three exact fields over the same ordered pair, literal Select arms, three nested true equality guards, the false mixed-Add branch, and the matching Mul3 target. Translation checks contexts and follows exact branch-input projections. Abstracting payload expressions as independent opaque words forgets possible aliases; the universal proof remains valid under their actual substitution. Only the exact target predicate is exported and united with false in its own context.

The generic graph obtains payload equality through the marked OrderKey and its unmarked Triple representation, reverses the Add-result disequality with an equal sibling, and forwards the resulting child disequality through Mul3. Encoding does not call the manual closure. The manual comparator implements the same finite congruence, cancellation, forward, and guarded reverse implications. Cancellation and reverse rescues supply intermediate facts, rather than asserting the final target. These support a bounded generic-engine causal claim; they do not establish unique logical power over the faithful manual comparator.

The earlier primitive-null gap is resolved by the externally executed primitive_null.py pass. Rust PrimitiveOnly carries the unchanged seed graph and performs no dynamic reasoning. The external pass derives primitive columns from constructor schemas, retains the symbolic tag and all seeds, and checks corresponding primitive columns across every same-constructor application pair. Its graph equals Encoding's after removing only scheduling, and equals SeedOnly's. The retained result has 26 syntactic application occurrences, including repeated nullary Scope occurrences, 12 primitive comparisons, zero mismatches, no equality-sort inspection or propagation, and no final primitive witness/export. I independently recomputed the retained JSON in memory with its write intercepted; the result matched exactly. The command receipt records exit 0 without timeout and matches the reviewed script and captured streams.

All 884 retained engine files currently match the sort, affine, and Parts32 trees. The historical Parts32 archive freezes five changed engine files, all matching this candidate. The successful Parts32 make check receipt is reused evidence, not a fresh sort-engine check or a historical full-tree hash freeze.

I changed only this audit artifact. I made no implementation, fixture, binary, or evidence changes and ran no builds or compiler/native tests.

The following SHA-256 identities bind this review. Relative paths are within this sort-integration directory.

| Reviewed artifact | SHA-256 |
|---|---|
| /private/tmp/eggcc-sort-candidate/dag_in_context/src/scoped_reasoning.rs | 03329de55baf7130d1ad05c23974235c79237e7658963161ac6f67a22436a723 |
| /private/tmp/eggcc-sort-candidate/dag_in_context/src/lib.rs | 96fbeb280e76e29505e79c3d96ac8beefcbd70792a6d61b9dc2f6ae497f7c323 |
| fixtures/source.bril | e1848eef382dd1ffd8df8d42283d470121e5fa286d3fb9a0b6324a2edab97f10 |
| bin/eggcc | 56808fe97852950e1080f07c4b3f1284327a9f050ee80e37518648f066bcb26e |
| primitive_null.py | 6f442dc82b6522d1d3aa27a46cc5a4c4a980e33e1478037fcf1ebfd2eac0b399 |
| primitive-null.json | 1f5adb523bf0ff39b9d67dbda4ec03f137d628f9ffc2902b9f2db231629d4014 |
| positive-results.json | 8cfcab1a8c0ea1d42312b18112ac623954c25cf5c8c2de68af5cf5007e181887 |
| source-files.json | b59c6413330dee938a384e0ce1fd2e1e48991119f586026e6b0611eb018dc1ab |
| commands/primitive-null/receipt.json | 61a1db933a7a638ded7a50efbd99a724081422faa3bc384ee4e2ecafe5ca1d75 |

The reused Parts32 make check receipt at ../parts32-integration/commands/engine-make-check-process-access/receipt.json hashes to 99f8ff02e41a46e7cb530c6388fd7b73577580b09c196da9efff23e4f8d04d73. The null's retained seed-program hash is 1602db2375f853aaea44456fdde33a33403379c0fe5c62572d8e434ba6e055ec; Encoding's program including scheduling hashes to dc04128f0ce97e527e303a1a43a85877e30da132d59207ed553847d02a40316d.
