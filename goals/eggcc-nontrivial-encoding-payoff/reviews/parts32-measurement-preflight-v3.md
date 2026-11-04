# Parts32 measurement preflight audit: import-shadow repair

**Verdict: PASS to issue one fresh exclusive preflight and, if that preflight admits the host, run both frozen sessions.** This is a runner-readiness verdict, not performance evidence. I ran no host inventory, preflight, compiler, native program, warmup, or timing sample. At the end of the audit, `timing-preflight.json`, the entire `timing/` directory, and `independent-verification.json` were absent.

## Preserved failed start

The accepted policy-v2 preflight from the aborted start is preserved as `timing-preflight-aborted-import-shadow-1792438903886522000.json`, SHA-256 `a97bb2c9e42866b2d4af082a3e5084e92700f1ff2309b68f2ee02f560401ef87`, matching the hash recorded when it was renamed. Its canonical process-snapshot digest recomputes to its recorded value, `3f7aa24c92fe0228a6b5a9f31be09e5ff090d2595e4c68425ddc86216effd870`. It binds the unchanged design, preparer, verifier, and original runner hashes listed below and says timing outputs were absent. There is no session directory or sample artifact that could enter the confirmation statistics.

| Binding | SHA-256 |
| --- | --- |
| `prospective-timing-design-frozen.json` | `c646d77e41334fd252a4e951245068f771afbbb41e44cd828e30edd58b0f6367` |
| `prepare-timing.py` | `57c3d7a9195e7d28e9563936effe26585dd1a9953cc59af31922ab7063861577` |
| original `timing.py` | `bf71a082ce5afccc1a61f15f5c9162747808831c264133f62689dc43345ddb3f` |
| repaired `timing.py` | `ba93aedaf6d64115c6beaeb022de5367d6f3469e247444eff3f20679ab47364a` |
| `verify-timing.py` | `2e01190ac2d09f8d9b368d049498e1c30f5c0041ad3f848f05860b6313e77749` |
| `check-process-policy.py` | `251394f693723bfd1aa156883fe3430db1922104219d421b5c4a443ad0789c3a` |
| retained post-incident receipt | `4739f75cb4bc1d713b5ee5930c6cc6bddca320b94af27e7237b0d65a68264754` |

## Frozen cohort

All 23 frozen bindings are exact against current bytes and the retained preflight: source input, compiler, source archive, and four artifacts for each of five arms. The retained preflight's design path and design hash also match the frozen file. The three global hashes are:

| Artifact | SHA-256 |
| --- | --- |
| `final-reviewed/fixtures/source.bril` | `d1fe5b6ace306fff529d1ed7bac03609066624cf750fc0238cb71fcbee583ae0` |
| `bin-reviewed-final/eggcc` | `d712e8347bf6eea231de829174a9436f411a3cedfd210daf8e7c4614c2371d2f` |
| `final-source.tar` | `ba2f65df7091573a594b7c51ec68a8b3665b5c85f279fe4415ca0f6e08565873` |

The five runtime binaries remain `U0` `0225044fd41b38a39e7281908ed6a90da5702da64736d34056c6d72ff0197bbb`, `B1` `bcab16fe955e1ecbb1b62c5e040e662d5b65a266146da36a33d236c6e3c683aa`, `SeedOnly` `0092b47bb94281266da5f7586569c2e396b0b38f3f9d88d401ede6ad4f78ef46`, `Manual` `7cf36403f071dfd4cf734bd7353843042814d016de473766c485e385ea6ffb2c`, and `Encoding` `b4159d556b2f9bcb6407f0e24b7bd79296c9b1554073a173a5b5a2bb5ff372d2`. `U0`/`B1`/`SeedOnly` share emitted, main-assembly, and Bril-main-assembly hashes `efc494a5aeda44028ae09c757f206140673e9b17e0a63ffc18dc5d13a85972fb`, `5acc1b241edcba37b437efef2ef69d8754250d57620ff791dbf107700ab2f2eb`, and `592a2990a2fc56179e571139882dadedc7c3a9f8c6f6e88eb3a771c2313cc771`. `Manual`/`Encoding` share `d33e62b14d01c645ba016ac6b134a29f284be9a1b781abdae2579d60079687b9`, `b1333575136a7098ab66939781f8b2c8141cd254b3ea0b8b41218e6a33e46d19`, and `b7bf23ef4d6418e3694797b1140e5097fec1ea391bffe48b46c06fcfceeed707`.

As an additional continuity check, all 17 entries in `final-source-identities.json` match their current paths, all 13 archived entries match their `final-source.tar` members, and the archive hash matches its manifest.

## Repair scope and semantics

The original runner source can be reconstructed exactly from the repaired file by moving the existing `sys` and `Path` imports back to their prior positions, removing the early directory exclusion, and replacing `ROOT = _IMPORT_ROOT` with the equivalent `ROOT = Path(__file__).resolve().parent`. That reconstruction is 27,755 bytes, matches the cached pre-repair source-size field, and hashes to the original preflight-bound SHA-256 `bf71a082ce5afccc1a61f15f5c9162747808831c264133f62689dc43345ddb3f`.

The resulting bytewise delta is confined to import setup: compute the same resolved evidence directory, remove it from `sys.path`, then import `argparse`; all measurement functions and their bodies are unchanged. The `sys.path` mutation prevents local `inspect.py` from satisfying `argparse`'s standard-library import. It does not alter the frozen workload, arm order, subprocess arguments, timer boundary, estimator, resampling, gates, or persisted sample schema. `ROOT = _IMPORT_ROOT` retains the prior resolved path value. No later dynamic import or child environment derives from `sys.path`, so this runner-only correction does not change measurement semantics.

Running the exact help path from the evidence directory, `python3 -B timing.py --help`, exited 0 with `usage: timing.py [-h] {1,2}` and empty stderr. Before and after that command, every one of the 65 previously unbound derived files had the same SHA-256, size, and nanosecond mtime. All 65 current hashes match the retained post-incident hashes; thus the help path did not execute local `inspect.py`.

## Static and synthetic checks

AST parsing passed for `prepare-timing.py`, `timing.py`, `verify-timing.py`, and `check-process-policy.py`. Both `python3 -B check-process-policy.py` and `python3 -I -B check-process-policy.py` passed all 41 synthetic policy cases with no stderr. The 65 derived-file states and the retained aborted-preflight hash remained unchanged, and no timing evidence appeared.

The preparer computes `timing_sha256`, `verifier_sha256`, and `preparer_sha256` from current file bytes while creating a new preflight exclusively. The producer then requires those current hashes before creating a session, and the independent verifier requires the same producer/verifier bindings. A new preflight therefore refreshes the repaired producer hash to `ba93aedaf6d64115c6beaeb022de5367d6f3469e247444eff3f20679ab47364a` while retaining the unchanged preparer and verifier hashes above; the aborted preflight cannot authorize the repaired runner.

The shared-host limits from the v2 audit remain. Collection should proceed only if the new preflight admits the host, and both frozen sessions plus independent verification remain mandatory.
