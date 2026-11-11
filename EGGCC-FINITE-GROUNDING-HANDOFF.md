# Eggcc finite and derived grounding handoff

The three-file patch adds typed finite binary64 identity matching and one-level existing-row TupleT observations for erased fields. It preserves original source/rules/schedules/selected-node identities. Derived observers are strict zero-argument functions, populated only by constructor rows matched in rule bodies after all original schedules. Their commands, expected singleton counts and hashes are explicit metadata; no constructor occurs in generated actions.

The f64 mapping records source/native spellings, exact big-endian binary64 bits, sort and class. Opposite signed zeros, nextafter neighbors, nonfinite values and ambiguous primitive classes do not gain an anchor. Other erased constructor shapes, ungrounded children and inconsistent native type/FD evidence retain structural constraints. Existing structural fallback also emits any valid derived observers referenced by its checks.

Validation: 94 focused lightweight tests, Ruff check/format and two-file mypy passed. Offline transformation of retained events (no engine) now maps all three optimization sessions of Max-subarray and Cholesky to existing-row DAG queries, retaining all 3 and 8 root requests respectively. This is representability evidence only. The first pass adds 1/2 derived type tables; later passes add none.

The first test attempt had 13 unrelated failures from the mirror's stale capture adapter; that unmodified dependency was refreshed from current live and is excluded from the patch. Baseline, modified and patch hashes are in the adjacent JSON. No native jobs, live source edits, or prior receipt changes occurred.

Root must run the positive/absent-row/wrong-child/wrong-input gates and primary constructor count comparison, then complete native parents plus every ordinary replay. Proof support for observer functions remains unvalidated. Independent read-only review of the final exact file hashes found no remaining blocker. Reserved observer child/value variable names and collision checks prevent source-global precedence collisions.
