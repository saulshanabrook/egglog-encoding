# SpEQ TPAL and TSVC2 input recovery

Inspected 2026-09-25. The original artifact Dockerfile has now been recovered from
a checksum-complete archive acquisition. Following its compiler dependencies did
not recover the exact TPAL or TSVC2 application sources and setup. The findings
below describe the specific inspected sources, not every historical revision or
file in those repositories. This investigation performed no builds, benchmark
execution, large clones, container execution, or author contact.

## Verified archive and Dockerfile

The retained [full-stream result][stream-result] records process success and binds
the [artifact receipt][archive-receipt] by SHA-256. That receipt records all
6,259,975,347 compressed bytes, all 73,109 member-index entries, and the expected
archive MD5 `813c94e4c12a3466909849f38b6ac1fe` for
[Zenodo record 10963236](https://zenodo.org/records/10963236). Its member-index
SHA-256 is `23acf74505c56b2e08479b8cfb82a52b4670ef5f95bd3fce36192649615ab136`.
The result, referenced receipt, and recovered Dockerfile bytes were read for this
report; the receipt and Dockerfile hashes were checked against the result.

| Retained evidence | SHA-256 |
|---|---|
| Full-stream result | `a25c64176dfc4d60eea473c9f72e9de3a851c9b65a15bd31a7577ae65599802e` |
| Artifact receipt | `275471a781f7781525d9dee31c47fe1465694b4be894967d9c7cba8862c38f5a` |
| Original 1,893-byte Dockerfile | `5cd0486c93f2ec785ea1d551069ab5275273ba4bf27dc7b55c6ac81de0fd68d8` |

The [Dockerfile][dockerfile] clones four compiler repositories, builds their tools,
and copies local LiLAC support files. Its clone commands are on lines 8, 19, 20
and 41. It contains no TPAL/TSVC2 benchmark download or source-copy command. These
clones use branch names and depth one; the Dockerfile does not pin commit hashes.
The resolved and historical commits below are evidence from this inspection, not
an assertion of the exact commits used by the original container build.

## Dependency sources inspected

GitHub source, tree and history HTTP reads used a 2-MiB response cap and 20-second
timeout. The audit inspected the following branches, immutable commits, small
subtrees and setup/history files. No repository was cloned.

| Dockerfile dependency | Source pin inspected | Result |
|---|---|---|
| `jaopaulolc/KernelFaRer`, `kernelfarer` | Historical upstream commit [`48aaf903ab69bb624732a1e817c9543360ba5acb`][kernelfarer-old] (2023-02-17), tree `4fdc9bd5f5f5bb9a214c34c4f65416494c368122` | The named branch now returns 404. A preserved fork supplies this old LLVM-monorepo commit, still accessible upstream. Its inspected benchmark/test trees do not recover either missing application. |
| `ginsbach/llvm`, `linearalgebra` | [`113d41f6e3695045fcc6e93166b3d1f5df1a8074`][lilac-source] (2020-02-12), tree `18e2d08ec99678bd8107618f9a2ff7a9b191906c` | Root/setup, six LiLAC support files, resources, examples/projects and transform directory names yielded no exact missing input or fetch. |
| `ginsbach/clang`, `research` | [`5e3d3c0055dc731abd506e18c320f227168f728b`][clang-source] (2018-09-18), tree `1f75dd696541adbcdf85b6595824f6c5b201f59f` | Root notes and all 14 `INPUTS` entries are compiler inputs, with no recovered TPAL/TSVC2 source/setup. |
| `avery-laird/lleq`, `artifact` | [`00bd6254b3832d94558b7c38a394ea03d01a2763`][lleq-source], tree `3672fc725d1782ce8e3f15ca20fbae231e65ede7` | The REV test subtree, complete 790-entry unittest tree and eight-commit REVTest path history provide the same eight existing examples, without the missing cases. |

KernelFaRer's current `main`, commit
`53a10e6e76b7136a1349245bbcdf8ed7ce5a23b4`, is a 2025 plugin rewrite. Its complete
177-entry tree `a71565889363cf6edfa75aa345b6dcde474429e9` has no TPAL/TSVC names.
The preserved `kernelfarer` branch in `liangminghuang/KernelFaRer` leads to the
2023 commit above; the `shrutimohanty/KernelFaRer` and `sazzy4o/KernelFaRer` forks
preserve `3e42c947d01a31de6aee8f17b309aa0021d1d81a` (2021). In the inspected 2023
source, `llvm/benchmarks` tree `02a9229805e10b89c7fae78ee79c9f507abc76d5` contains
only CMakeLists and DummyYAML. The [GEMMFaRer test tree][kernelfarer-tests]
`7ea90c3cbb39529d19fd45705e8f6fb0fd218a2c` contains 112 GEMM/MM LLVM tests, with no
TPAL/TSVC or fetch scripts. Its generic root README has blob
`1273ba17c2fa0c73d93a66462f7f25111144b540`, SHA-256
`2c590a0a86882c62f01752c5e124ca01a08326bf1386c4df1833598cd4c6dac5`.

The ginsbach LLVM [`artifact.sh`][lilac-script], blob
`41bb5db581c5d5804e8332e2264a2fa836ced1b0`, SHA-256
`2c141e11d0f1d61f5b7554eef06e27819d94a686eee2c77ae6efef2a7b65d787`, fetches
OpenBLAS and the compiler repositories, then expects an already-local SNU_NPB
archive. It does not fetch TPAL or TSVC, and the SpEQ Dockerfile does not invoke
this script. Its path history has three commits, all on 2020-02-12. Targeted
TPAL/TSVC commit-message searches returned no results in either ginsbach
repository; this is limited search evidence, not a full-content history scan.

LLEQ's [REVTest.cpp][rev-tests] has blob
`10f59946758bd88791430323fab21b8cc5cd1e53`, SHA-256
`6dc7b594b2c33917c1332615a476258c2166901c2bb5900ab8f7c455bc05ba33`. It names eight
existing examples below the author's local `/files/revpy/analysis` path. The
historical “added rest of tests” commit
`7ed1228f9a24889ffc0d34d522fdd14eb4960320` has REVTest SHA-256
`e141abf6881ebc1cfbaab2b314ec1923c100baec2de1263bf7dadcfb970766ab` and the same
eight examples. The inspected REV subtree contains only CMakeLists, REVTest.cpp
and polybench_gemm.ll; it supplies no TPAL/TSVC application or reduction setup.

## Exact remaining requirements

The artifact's [table mapping][table-mapping] identifies TPAL as `tpal_spmv` and
TSVC2 as `tsvc`, but comments both out of its selected benchmark list. The named
`benchmarks/{name}.c`, `ll/{name}.ll` and `analysis/{name}.ll` members are absent
from the verified complete archive index, as recorded by the existing
[paper-case reconciliation][reconciliation]. The [active driver][active-driver]
registers GEMM, GEMV and histogram targets, not a TSVC reduction target.

- **TPAL:** recover the exact paper-selected `tpal_spmv` C source and function,
  required headers or extraction changes, compiler options and original setup,
  with provenance connecting those bytes to the paper case. Then retain its
  complete frontend regions and intended sparse-matrix/vector translation.
- **TSVC2:** recover the exact `tsvc` source, selected function/reduction and
  options, together with the original reference definition, argument mapping,
  active rule registration and intended translation check. A same-named upstream
  suite or an arbitrary reduction example does not establish that identity.

Recovering an old compiler commit repairs a possible dependency-acquisition path;
it does not recover those benchmark inputs. These findings authorize no input
substitution or corpus admission. Exact-input recovery would still require the
complete native source parent and ordinary replay validation.

[stream-result]: ../local/reproduction/diagnostics/speq-dockerfile-recovery-0001/full-stream-0001/result.json
[archive-receipt]: ../local/reproduction/diagnostics/speq-dockerfile-recovery-0001/full-stream-0001/archive/artifact-receipt.json
[dockerfile]: ../local/reproduction/diagnostics/speq-dockerfile-recovery-0001/full-stream-0001/archive/artifact/Dockerfile
[kernelfarer-old]: https://github.com/jaopaulolc/KernelFaRer/commit/48aaf903ab69bb624732a1e817c9543360ba5acb
[kernelfarer-tests]: https://api.github.com/repos/jaopaulolc/KernelFaRer/git/trees/7ea90c3cbb39529d19fd45705e8f6fb0fd218a2c
[lilac-source]: https://github.com/ginsbach/llvm/tree/113d41f6e3695045fcc6e93166b3d1f5df1a8074
[lilac-script]: https://github.com/ginsbach/llvm/blob/113d41f6e3695045fcc6e93166b3d1f5df1a8074/artifact.sh
[clang-source]: https://github.com/ginsbach/clang/tree/5e3d3c0055dc731abd506e18c320f227168f728b
[lleq-source]: https://github.com/avery-laird/lleq/tree/00bd6254b3832d94558b7c38a394ea03d01a2763
[rev-tests]: https://github.com/avery-laird/lleq/blob/00bd6254b3832d94558b7c38a394ea03d01a2763/llvm/unittests/Transforms/REV/REVTest.cpp
[table-mapping]: ../local/reproduction/preparation/speq-attempt-0002/sources/artifact/figures/table3/draw_table3.py
[active-driver]: ../local/reproduction/preparation/speq-attempt-0002/sources/artifact/run_benchmark.py
[reconciliation]: ../../scripts/suite_capture_dialegg_speq.py
