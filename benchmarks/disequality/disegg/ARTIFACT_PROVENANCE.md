# Artifact Provenance

This directory reconstructs the `disegg` dependency used by the
*Dis/Equality Graphs* artifact. The archived artifact contains
`../disegg.patch`, but not the patched Git checkout referenced by its absolute
`/disegg` Cargo path.

The reconstruction starts from the published `egg` 0.9.5 crate. The two Rust
source hunks from the artifact's patch apply unchanged. The published crate's
normalized `Cargo.toml` differs textually from the Git manifest targeted by the
patch, so its equivalent `egg` to `disegg` package-name change was applied
manually. The normalized upstream manifest remains in `Cargo.toml.orig`.

Upstream: <https://crates.io/crates/egg/0.9.5>

Artifact: <https://doi.org/10.5281/zenodo.13938878>
