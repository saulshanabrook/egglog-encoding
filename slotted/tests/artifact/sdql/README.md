# Slotted E-Graphs paper artifact fixtures

The files here are copied from commit
`83f2e5bee2b3aa45bf97ef1e3a8abe953790c735` of
[`memoryleak47/slotted-egraphs-artifact`](https://github.com/memoryleak47/slotted-egraphs-artifact),
the S4.2 SDQL case study's ten workloads: five kernels (ΣMMM, MTTKRP, MMM, TTM,
BATAX), each in the compiler's two phases.

- `<kernel>_<phase>.sexp` is `sdql/slotted/progs/<kernel>_<phase>.sexp`, the input the
  artifact's slotted runner read.
- `<kernel>_<phase>_esat.sexp` is `sdql/baseline/progs/<kernel>_<phase>_esat.sexp`, the
  program the artifact's egg baseline extracted after its equality-saturation run. The
  artifact's Table 1 runner compares extraction costs rather than asserting this syntax
  as a golden result; the tests here ask for the term itself.
- `mttkrp_2nd_bestcost.txt` is `sdql/baseline/progs/mttkrp_2nd_bestcost.txt`, the cost
  Table 2 judges that workload by, whose `_esat` file is the coarse-grained run's.

The published files have no final newline; the copies follow repository convention and
do. `slotted/checks/check-paper-sdql.py` pins their hashes, and
`slotted/paper_fixtures.py` translates them into the language of
`slotted/languages/sdql.egg` and writes the tests under `slotted/tests/sdql-paper/`.
