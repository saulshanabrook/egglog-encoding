"""Request expansion verifies produced files without running a native compiler."""

import shlex
from pathlib import Path

import pytest

from scripts import reproduction_prepare_misaal_cases as preparation


def test_dependency_closure_handles_escaped_spaces_and_requires_original_source(tmp_path: Path) -> None:
    source = tmp_path / "source file.cpp"
    source.write_bytes(b"source")
    dependency = tmp_path / "generator.d"
    # Clang's dependency format escapes spaces rather than shell-quoting the name.
    dependency.write_text("object.o: " + str(source).replace(" ", "\\ ") + "\n")
    assert preparation.compile_dependencies(dependency, tmp_path, {source}) == {
        str(source): preparation.sha256_file(source)
    }
    dependency.write_text("object.o: " + shlex.quote(str(source)) + "\n")
    with pytest.raises(ValueError, match="omitted"):
        preparation.compile_dependencies(dependency, tmp_path, {tmp_path / "missing.cpp"})
