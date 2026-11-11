# Public MISAAL Egglog export preparation

The public reproduction command now prepares `egglog-only-v1` requests and refuses to launch historical native-lowering requests. The [export contract](misaal-egglog-export.md) preserves the original source traversal and Egglog calls, then stops before LLVM legalization or final native outputs. Historical native attempts retain their original receipts and meaning.

Use the existing configured request directory as explicit retained templates:

```sh
uv run --locked python scripts/suite_acquisition.py reproduce --family misaal --stage prepare
uv run --locked python scripts/suite_acquisition.py reproduce --family misaal --stage all
```

`prepare` verifies the retained source, backend, Python, Racket and source-policy dependencies; builds one export frontend and the original per-case generators; then publishes fresh export requests. It does not build or require old selectors, legalizers, wrapper products, old generator binaries or final LLVM files. The Halide frontend build still uses its pinned LLVM development library. No source optimization runs during preparation. The existing stage cache reuses intact prepared artifacts.

The previous `misaal.paths.requests` supplies the initial templates. Prepared settings retain that directory as `misaal.export_templates`, while `paths.requests` points to the new export requests. An explicit `misaal.export_frontend` may point to a verified `frontend.json` from the source preparer to reuse that frontend build. All inventory cases remain represented, and existing exact configuration blockers are preserved. A resource stop prevents later generator builds and settings publication.

`all` replaces old native settings with export preparation before capture. `capture` requires already prepared export settings and requests; an old request cannot reach native execution. Ordinary replay and existing corpus publication still follow complete source export; preparation alone is not reproduction evidence.

This initial route requires retained source/runtime templates. With no configured templates, preparation reports that limitation and does not invoke the old native preparation pipeline. Fully fresh source/runtime acquisition is a separate pending integration; no fresh-install claim is made here.
