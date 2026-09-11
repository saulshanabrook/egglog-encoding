# Slotted E-Graphs paper artifact fixtures

These two files are copied from commit
`83f2e5bee2b3aa45bf97ef1e3a8abe953790c735` of
[`memoryleak47/slotted-egraphs-artifact`](https://github.com/memoryleak47/slotted-egraphs-artifact):

- `batax_2nd.sexp` is `sdql/slotted/progs/batax_2nd.sexp`, the BATAX second-pass input.
- `batax_2nd_esat.sexp` is `sdql/baseline/progs/batax_2nd_esat.sexp`, the
  baseline runner's published extracted optimized program.  The artifact writes this
  file after its equality-saturation run; its Table 1/2 runners compare extraction
  cost rather than asserting this syntax as a golden result.

`slotted/check-paper-sdql.py` pins their hashes and checks the syntax translation
used by `slotted/tests/sdql-paper-batax.egg`.
