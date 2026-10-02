# Unsupported spellings

Files here are written against constructs the slotted language does not accept, so the
compiler refuses them and `run-slotted-tests.py` skips this directory by name, as it
skips `snapshots/`. They are kept as the originals they are, not as tests.

| file | why it is here | runnable translation |
| --- | --- | --- |
| `bound-aliasing-rel.egg` | uses egglog's `rule` with a relation conclusion; the language has only `rewrite` | `../rudi/bound-aliasing-rel-decoded.egg` |
| `unify-redundant-and-symmetric-appid.egg` | the same, for the shared-body-under-two-binders case | `../rudi/unify-redundant-and-symmetric-appid-decoded.egg` |

Both were written by Rudi Schneider while reporting the matcher bug that
the frame's join fixes. The `-decoded` files spell the same programs as
`(rewrite (Truth) (Rel x w) :when (...))` and carry the checks. If `rule` ever becomes
part of the language, these move back beside them.
