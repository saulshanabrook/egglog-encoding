# Read-only source admission check

This check ran while the execution plan's Plannotator gate remained open. It changes no source checkout or remote ref and is not a compiler, test, or benchmark result.

## Fresh remote identities

The following network reads both exited zero on 2026-10-18:

| Working directory | Command | Remote `refs/heads/main` |
| --- | --- | --- |
| `/Users/saul/p/eggcc` | `git ls-remote origin refs/heads/main` | `a0bbec127f83249074a46af3fd6f6126c90fe0fb` |
| `/Users/saul/p/egglog-encoding` | `git ls-remote origin refs/heads/main` | `03e533714524c1b21be77edff46fb694120b8b81` |

The first sandboxed attempts failed DNS resolution; the authorized network retries succeeded. No fetch or checkout was performed. EggCC matches the setup source. Encoding main has assertion disequality but no `injectivity.rs` or marked-constructor query support.

## Encoding reconstruction boundary

Both remote objects and the retained feature object are present locally. The merge base of encoding main `03e53371` and injectivity feature `392b6d6b48b5bc307a5b9c981c957fc0a09e23e5` is exactly `03e53371`. Thus the feature is an additive descendant of the freshly verified main, not an unrelated historical branch. `Cargo.toml` and `Cargo.lock` are identical between those two commits.

The feature-only history is:

```text
392b6d6b Explain injectivity examples with mathematical implications
e9d91839 Document injectivity encodings and inference boundaries
34064008 Query constructor disequality without storing derived pairs
c5bbd03d Merge remote-tracking branch 'origin/main' into codex/injectivity
7c16a632 Add constructor injectivity encoding
```

The committed delta changes 23 files, with 1,491 insertions and 19 deletions. Runtime changes cover the injectivity command pass, AST/parser flag, fresh macro handling, proof flag rejection, `keep-best` marker preservation, and the on-demand query. `keep_best.rs` is part of the invariant: it must retain declaration-level marked-constructor rows when clearing runtime tables. Do not discard it as unrelated cleanup.

The retained E1 tree `/Users/saul/p/wt/egglog-encoding/eggcc-encoding-payoff` is at the same feature commit and has a further uncommitted n-ary reverse-congruence delta. Its tracked changes are limited to the disequality implementation, its README explanation, the executable explanation fixture, and the integration test; its untracked test directory contains the independent oracle. At this check, `git diff --check -- egglog-experimental` passed.

| E1 file | SHA-256 |
| --- | --- |
| `egglog-experimental/src/disequality.rs` | `8d56d53d87d0c21595b765f3aa6a9f7e3bc4752b4f87dfbcc651c108fe11bb3c` |
| `egglog-experimental/tests/injectivity_disequality.rs` | `3da93594215cf562380d0dd9c2391dcf5e184ff3214e60dac80b8c303816251c` |
| `egglog-experimental/tests/injectivity_disequality/oracle.rs` | `18dbe43bf36f530752bca6fd7fbc66222cd3b12d4a3073fe2cef1177a86674ec` |

After plan approval, create a new isolated encoding worktree at `392b6d6b`, record its ancestor relation to current main, and copy/apply only that E1 delta plus the untracked oracle into it. Rehash the source before tests and record an exact patch. Do not mutate the retained E1 tree, cherry-pick its merge commit blindly, or refer only to a branch name as the experiment identity. If remote main changes before actual admission, repeat the ancestry/API check.

Both main and the feature expose `new_experimental_egraph_with_options(extended_run_schedule, DisequalityEncoding)`; the feature adds injectivity registration and marked-query behavior. Actual dependency resolution, EggCC API compatibility, build success, and test coverage remain unverified in the new study. The prior E1 retarget regression remains excluded and must be checked rather than assumed fixed.

## Goal package consistency

A direct Python check verified the exact text/order of all 18 accepted facts against `facts-result.json`, their IDs and automated-verification flags against `facts.meta.json`, all 18 entries in the plan's verification map, and every relative plan link. The reviewed plan SHA-256 is `996b57417a40695fa1194e2b0e93f9c5502459af9c15c0e234bd3c1f35f9fbd0`.

The review process handle `65626` was polled and remained live without a terminal result. No approval, denial, or dismissal has been inferred from that wait.
