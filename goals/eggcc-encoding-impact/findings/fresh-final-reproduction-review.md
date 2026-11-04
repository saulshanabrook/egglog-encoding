# Fresh final representative reproduction

Both authorized fresh compilations pass. Exactly two compiler processes ran, both Injective with the normal three-pass native pipeline; neither timed out. Their direct Popen children were reaped and the reproduction script exited 0. No build, project test, source change, peer-classifier import, or additional compiler workload was performed. This is correctness evidence, excluded from costs and interference-sensitive timing results.

The reference is derived independently: both inputs select `0 < x`; wrapping i64 `1*2 = 2`, so `2 < 0` is false, while `(2^63-1)*2 = -2` modulo `2^64`, so `-2 < 0` is true. The standalone script computes signed wrapping explicitly, checks fixed fixture hashes/ARGS, and compares both original and result interpreter fields with those exact newline-terminated references.

| Fresh case | Frozen compiler SHA-256 | Actual PID / exit | Exact source/result |
| --- | --- | --- | --- |
| Final original, x=1, Injective | `5d980389feec6270146db9a2cfe4e1775974102ab6c50cdf7bad029471907af1` | 19243 / 0 | `false\n` / `false\n` |
| Corrected, MAX, Injective | `f44edb3cb9c4b9660524335a29bea536571fe2ddbd1bcc68ba589decbd9bcc15` | 19247 / 0 | `true\n` / `true\n` |

Each actual command uses `--with-context --run-mode optimize --interp --observations injective`, fresh copied input/run-data/evidence/egraph paths, `RUST_LOG=info`, `RAYON_NUM_THREADS=1`, cwd `/Users/saul/p/wt/eggcc/encoding-impact`, and a 120-second process-group limit. Both stdout files exactly render the expected result plus the CLI's separator newline; captured interpreter fields match the reference exactly. Each run has passes 0/1/2, three nonempty native Tiger graph captures, and three reconstruction schedule completions. Each pass has two supported Boolean observations/six seeds, accepted audit/no conflicts, and the pre-serialization marker. The reached product-comparison observation agrees with the independently computed value and actual `[StateV, 0, x, 2]` region input.

Both fresh persistent children are PID/root/mode bound to their full-stderr locator and normal receipt: `invocation-19243-0` and `invocation-19247-0`. Each complete 19-file tree is independently validated and copied to its own `evidence-archive`; archived/persistent bytes match. Before/after checks bind each endpoint manifest, source manifest/patch, actual compiler, sibling Tiger, original and copied fixture, and this script. All hashes remain unchanged, including a separate read-only receipt/archive check after script completion.

The x=1 fixture SHA is `b8bc31ef18ebefd6f25057439e277569a931b2ec769295cbf590aef14550bf9c`; MAX is `f6624abf3e6018b7e6d2d5e410afff2f95822965515361b644cfc61ba8fd31eb`. Both frozen sibling Tigers have SHA `bd53d3716c6ec4fffbb8aa4a4435476cf5cfa977415fbbcb364d1ecbd8cb3b0a`. Final-original source manifest SHA is `5cddb863fa1a242fd028051400fb9a58c54ff33c876fe74a678e29fee020c6a3`; corrected source manifest SHA is `8748805409bdc89ae7d529521140aacadb85483ffb421b957d82b3a8de0fbc22`. These are separately bound source packages; this reproduction does not claim their test-only source inventory is identical or rerun full source gates.

The [standalone script](/Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/fresh-final-reproduction/reproduce.py) has SHA `559513b996633415431bb865dd3d4767233908b2a4fd41332765a1b7081d8c72`. Exact executed command, from the repository root:

```sh
python3 /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/fresh-final-reproduction/reproduce.py --out /Users/saul/p/egglog-encoding/benchmarks/local/eggcc-encoding-impact/fresh-final-reproduction/run-01
```

The script requires a new output directory. A future rerun must choose another `--out` path; do not overwrite `run-01`.

Raw receipts are under `benchmarks/local/eggcc-encoding-impact/fresh-final-reproduction/run-01/`:

| Retained record | SHA-256 |
| --- | --- |
| `results.json` | `5ea7d3ffcf6150883d9818e884466ae3c69c47aeaa44952543337fca5f6acdb9` |
| `original-one/command.json` | `06aa8766e68230d7a6614c7eedbd9f61f153155fee2323d7dc53eaa35082a6fb` |
| `original-one/command.stderr` | `0bb334b4046d20edc45a8b907f209cfb830904c06add1d72e7548d9583ea2793` |
| `original-one/captured-run-data.json` | `ea9c46f9f07126da5d7c1a23a49adc5e3e7540b1535723ad5ae11dea97d47174` |
| `corrected-max/command.json` | `6f546a07aec7f9da8d338885a35a96a941b36860a026963fca0949e91724d716` |
| `corrected-max/command.stderr` | `b83847877b1c1421444dcdb0067adf05981b2c7c7fd63ea6a0f8dd9608aa220d` |
| `corrected-max/captured-run-data.json` | `0ff17744496f2735dd9e157c4061c8129017e8f6237f75f2463fc305cdffbbbb` |

Each case also retains full stdout, `before.json`, `after.json`, copied input, per-pass evidence, native graphs and independent `review.json` inventories. The two representative checks are reproduced; final whole-dossier/gate/cost admission remains the coordinator's separate review. No further compiler work is running from this reproduction.
