# Prepared standalone inputs

The manifest and 487 `.egg` files are the published benchmark inputs. Each file
retains complete graph construction, rules, schedule and ordinary output queries.
Identical bytes are stored once; source-case aliases and invocation order remain
in `manifest.json`. Source revisions, adaptations and unavailable cases are kept
even when a prepared file is too fast, too slow or fails a proof treatment.

Readable paths are labels. The manifest's content and fact hashes identify the
workload, so renaming a file does not invalidate compatible measurements or
justify changing their recorded provenance. Once published, a name stays stable
when additional aliases are discovered.

Run these files through the ordinary explicit-file benchmark interface. Collection
does not require an author compiler or source acquisition. The separate
[reproduction package](../reproduction/README.md) contains regeneration and strict
validation commands. Local resume state and diagnostic logs belong in ignored
`.local/`, never in the portable manifest.
