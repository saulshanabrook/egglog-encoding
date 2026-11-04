# Prior results and the stricter boundary

Setup-only synthesis from completed study reports and audits. These notes are constraints for the new search, not new experiments or fresh compiler findings. The fourteen accepted [facts](../facts.md) are authoritative.

| Prior result | What was established | Why it does not close this goal |
| --- | --- | --- |
| [Multiplication overflow](../../eggcc-encoding-impact/report.md) | A valid MAX input miscompiles because two multiplication-sign interval rules ignore wrapping overflow. A newly added injective Boolean observation audit and an equivalent manual audit both catch the conflicting equality. Deleting both rules is a confirmed diagnostic control. | Already demonstrated in the completed study. The failure was first discovered by differential source/optimized execution, and the encoding audit was attached afterward; that chronology cannot be rewritten as encoding-led discovery. |
| [Nested type checker](../../eggcc-combined-encoding/report.md) | A tag distinction propagates through marked pointer/list/tuple metadata into the real ExpectType diagnostic. Contribution controls, native host/CLI coverage and an independent finite Type oracle validate the integration. | The original raw-ID check and manual structural checker already reject the same internal malformed fixture. No new valid-source bug or measured speedup was established. |
| Type-tag consistency repair | A review/test iteration found and fixed a missing corruption guard in the new experimental checker. | Introduced by that integration; it is not a pre-existing baseline compiler bug. |
| Missing Tiger, empty ARGS reparse and raw checker failures | Tooling failures and retries are retained with explicit boundaries. | They are not encoding-caused evidence of the required compiler bug or speedup. |
| Thirteen snapshots and three strict lint sites | [Fresh matched gates](../../eggcc-combined-encoding/findings/gates.md) reproduce the same snapshot bodies and lint diagnostics in the pre-integration control. | These are known current integration limitations. The failed official commands remain failed and are not thirteen new encoding-discovered bugs. |

Neither completed study supplies controlled evidence of a speedup. Previous descriptive timings are not an eligible performance baseline. Existing source/evidence authorities may be reused, but every new acceptance result needs fresh correctness and comparison receipts.

The new goal can use either encoding, preferably both. It does not require a behavior to be impossible to hand-code. It does require the encoding to contribute to a genuine new bug diagnostic or the optimization/analysis whose measured end-to-end benefit is claimed. An independently discovered new fault may still be valuable, but the record must distinguish discovery from later encoding validation.

The latest completed compiler manifest is `benchmarks/local/eggcc-combined-encoding/consumer/oracle-final/source.json`, SHA `8165c4521d16ea4f5d1cffe66a08092962b55b8976f37c2b6a2553bfc5352738`; its production closure is unchanged from the host/CLI checkpoint before the final oracle test-only addition. Both that worktree and its pre-integration control are completed-study assets. New execution must preserve them and select an explicit isolated baseline; the verification owner supplies the reconstruction and upstream-freshness decision.

If a candidate fails, preserve its actual falsifier and change the next hypothesis. If no investigated lead yields the required result, the goal remains unmet. A documented failed search is not a third success option, and a new implementation without demonstrated payoff is not a substitute.
