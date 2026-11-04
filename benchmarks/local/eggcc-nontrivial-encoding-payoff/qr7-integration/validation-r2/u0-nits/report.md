# Fresh U0 nits control

This control was extracted from EggCC commit `a0bbec127f83249074a46af3fd6f6126c90fe0fb` into
`/private/tmp/eggcc-qr7-u0-nits-r2`. The retained Git archive has SHA-256
`7a886debd758e78d0e859a05bbac75084e7da9c4f4bd0d73321dcf6f5ad25c2a`. All 771 extracted blobs match their
Git object IDs and recorded SHA-256 values, the archive reproduces byte for byte, and
the before/after manifests are identical. The commands used Rust 1.91.0 with four
Cargo jobs and `EGGLOG_BENCH_MEMORY_GUARD` absent. No tests, benchmarks, or
raytracing were run.

| Command | Exit | Result |
| --- | ---: | --- |
| Root `cargo fmt --check` | 0 | pass |
| DAG `cargo fmt --check` | 0 | pass |
| Root `cargo clippy --tests -- -D warnings` | 101 | one warning promoted to error |
| DAG `cargo clippy --tests -- -D warnings` | 101 | two warnings promoted to errors |

The root `unnecessary_unwrap` diagnostic reproduces byte for byte in U0. The DAG
`unnecessary_unwrap` and `cloned_ref_to_slice_refs` diagnostics also reproduce byte
for byte. Their flagged source files are byte-identical between U0 and the QR7
candidate.

The candidate's two diagnostics in `dag_in_context/src/scoped_qr7.rs` do not
reproduce: that file is absent from U0. U0 also passes DAG formatting, while the
candidate formatting diff is confined to that QR7-only file. Thus the whole set of
candidate warnings does not reproduce in U0; precisely the three diagnostics in
preexisting, byte-identical files do, while the two QR7 diagnostics are
candidate-only.

Exact diagnostic text, per-diagnostic hashes, every flagged-file source hash,
receipt and stream hashes, and the source verification are in
[`comparison.json`](comparison.json). Raw streams and receipts are under
[`commands/`](commands/), and [`source-identity.json`](source-identity.json) records
the archive and toolchain identity.
