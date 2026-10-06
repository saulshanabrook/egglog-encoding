"""Published source identities and the active standalone capture path."""

from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path
from typing import Any

import pytest

from scripts import reproduction_published as published
from scripts import suite_reproduction as reproduction
from scripts.hardboiled_replay import egglog_forms

SOURCE = b"""(datatype E (A) (B) (Identity E))
(ruleset canonicalize)
(ruleset typechecking)
(ruleset amx)
(sort Callback (UnstableFn (E) E))
(relation callback (Callback))
(rule ((= e (A))) ((callback (unstable-fn "Identity"))) :ruleset canonicalize)
(rule ((callback f) (= e (A))) ((union e (unstable-app f e))) :ruleset canonicalize)
(let root (A))
(run-schedule (repeat 20 (saturate (run typechecking)) (run) (run amx)))
(extract root)
"""


@pytest.fixture
def entry() -> dict[str, Any]:
    return {
        "file": "example.egg",
        "size_bytes": len(SOURCE),
        "sha256": hashlib.sha256(SOURCE).hexdigest(),
        "git_blob": hashlib.sha1(b"blob " + str(len(SOURCE)).encode() + b"\0" + SOURCE).hexdigest(),
        "extracts": 1,
    }


def test_capture_preserves_source_and_only_omits_unscheduled_rules(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, entry: dict[str, Any]
) -> None:
    monkeypatch.setattr(published, "published_entries", lambda _: {"case": entry})
    monkeypatch.setattr(reproduction.urllib.request, "urlopen", lambda *a, **kw: io.BytesIO(SOURCE))
    replay, adaptations = reproduction.capture_source_file(
        {"id": "case", "family": "hardboiled", "source": "example.egg"},
        {"repository": published.REPOSITORY, "revision": published.REVISION},
        tmp_path,
    )
    assert (tmp_path / "source.egg").read_bytes() == SOURCE
    assert adaptations == ["omit statically unscheduled higher-order rules"]
    assert [tokens for _, _, tokens in egglog_forms(replay.read_text())] == [
        tokens
        for _, _, tokens in egglog_forms(SOURCE.decode())
        if not {"unstable-app", "unstable-fn"}.intersection(tokens)
    ]
    evidence = json.loads((tmp_path / "source.json").read_text())
    assert evidence["sha256"] == entry["sha256"]
    assert published.REVISION in evidence["url"]


@pytest.mark.parametrize("change", ["bytes", "missing-query", "include"])
def test_changed_source_and_missing_original_queries_are_rejected(entry: dict[str, Any], change: str) -> None:
    data = SOURCE
    if change == "bytes":
        data += b"; changed\n"
        message = "identity changed"
    else:
        data = data.replace(b"(extract root)", b"" if change == "missing-query" else b'(include "other.egg")')
        entry.update(
            sha256=hashlib.sha256(data).hexdigest(),
            size_bytes=len(data),
            git_blob=hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest(),
        )
        message = "original extraction queries" if change == "missing-query" else "self-contained"
    with pytest.raises(ValueError, match=message):
        published.verify_input(entry, data)


def test_selected_published_population_is_pinned() -> None:
    assert len(published.published_entries()) == 42
