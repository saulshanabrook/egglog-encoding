# Pointer Analysis `initdb.bc` Facts

These facts come from the PLDI 2023 artifact for *Better Together: Unifying
Datalog and Equality Saturation*:

- DOI: <https://doi.org/10.5281/zenodo.7709794>
- Archive SHA-256: `2f061f4f59fd3404638db0d9ad9d130e008d4c41fdeb58ade30684d8e424607a`
- Artifact path: `pointer-analysis-benchmark/benchmark-input/postgresql-9.5.2/initdb.bc`

The benchmark program reads 23 of the artifact directory's 25 CSV files. This
repository includes every row from those 23 files, totaling 73,864 rows. The
unused `call_instruction.csv` and `call_instruction_fn_operand.csv` files are
omitted. The CSV contents are otherwise unchanged.
