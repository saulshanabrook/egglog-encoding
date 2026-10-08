# Prepared paper workloads

This directory holds the standalone, content-addressed `.egg` inputs and portable
`manifest.json` consumed by `./bench.py --suite expanded` and `make figures-all`.
Commit both the inputs and manifest after preparation. The manifest records
source revisions, adaptations, aliases, hashes, and unavailable cases.

To create or refresh the corpus from the pinned author sources:

```sh
make reproduce-benchmarks
git status --short benchmarks/corpus
```

Source checkouts and compiler builds stay in ignored `benchmarks/local/`.
The ignored `.local/` directory here holds resumable preparation state and strict
validation outcomes/logs. Those files are optional local evidence; they are not
needed to benchmark the saved inputs and do not belong in Git.

See [workload boundaries and collection](../README.md) for details.
