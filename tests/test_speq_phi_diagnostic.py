"""Static patch/provenance and fixture-oracle tests; native LLVM checks are separate."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

import pytest

from scripts import speq_phi_diagnostic as diagnostic

ORIGINAL_METHOD = """  template <class PHITy>
  BranchInst *getPhiBr(PHITy *Phi, BasicBlock **Then, BasicBlock **Else) {
    if (Phi->getNumIncomingValues() != 2)
      return nullptr;
    auto *BB1 = Phi->getIncomingBlock(0);
    auto *BB2 = Phi->getIncomingBlock(1);
    BasicBlock *CommonDenom = DT.findNearestCommonDominator(BB1, BB2);
    BranchInst *Br = dyn_cast<BranchInst>(CommonDenom->getTerminator());
    if (Br == nullptr)
      return Br;
    bool IsTrueBr = DT.dominates(cast<BasicBlock>(Br->getOperand(2)), BB1);
    IsTrueBr ? (*Then = BB1, *Else = BB2) : (*Then = BB2, *Else = BB1);
    return Br;
  }
"""


@pytest.fixture
def source(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    original = (
        '#include "llvm/Support/Debug.h"\n'
        "unrelated original content\n"
        + ORIGINAL_METHOD
        + diagnostic.END
        + "\n    BranchInst *Br = getPhiBr(Phi, &Then, &Else);\n"
        "    auto *TrueVal = Phi->getIncomingValueForBlock(Then);\n"
        "unrelated trailing content\n"
    )
    cpp = tmp_path / "source/llvm/lib/Analysis/REVPass.cpp"
    header = tmp_path / "source/llvm/include/llvm/Analysis/REVPass.h"
    cpp.parent.mkdir(parents=True)
    header.parent.mkdir(parents=True)
    cpp.write_text(original)
    header.write_text("pinned header fixture")
    memory_header = header.with_name("MemorySSA.h")
    memory_header.write_text("pinned custom memory header fixture")
    monkeypatch.setattr(diagnostic, "MEMORY_SSA_SHA256", hashlib.sha256(memory_header.read_bytes()).hexdigest())
    monkeypatch.setattr(diagnostic, "REV_PASS_SHA256", hashlib.sha256(cpp.read_bytes()).hexdigest())
    monkeypatch.setattr(diagnostic, "REV_PASS_HEADER_SHA256", hashlib.sha256(header.read_bytes()).hexdigest())
    return tmp_path / "source"


def test_only_reviewed_phi_function_error_guard_and_include_change(source: Path) -> None:
    original = (source / "llvm/lib/Analysis/REVPass.cpp").read_text()
    patched = diagnostic.patched_rev(original)
    restored = patched.replace(diagnostic.EDGE_AWARE_PHI, ORIGINAL_METHOD)
    restored = restored.replace('#include "llvm/Support/ErrorHandling.h"\n', "")
    restored = restored.replace(
        '    if (!Br)\n      report_fatal_error("REV: unsupported PHI control-flow polarity");\n', ""
    )
    assert restored == original
    assert patched.index("if (!Br)") < patched.index("Phi->getIncomingValueForBlock(Then)")


def test_materialization_preserves_original_and_binds_exact_tested_function(source: Path, tmp_path: Path) -> None:
    cpp = source / "llvm/lib/Analysis/REVPass.cpp"
    before = cpp.read_bytes()
    output = tmp_path / "diagnostic"
    record = diagnostic.materialize(source, output)
    assert cpp.read_bytes() == before
    assert (output / "original/REVPass.cpp").read_bytes() == before
    assert record["status"] == "diagnostic-materialized-unrun"
    assert record["native_execution"] is record["corpus_admission"] is False
    assert (output / "original-phi-harness.cpp").read_text().count(ORIGINAL_METHOD) == 1
    assert (output / "patched-phi-harness.cpp").read_text().count(diagnostic.EDGE_AWARE_PHI) == 1
    for relative, digest in record["files"].items():
        assert hashlib.sha256((output / relative).read_bytes()).hexdigest() == digest
    assert json.loads((output / "diagnostic.json").read_text()) == record


@pytest.mark.parametrize("changed", ["cpp", "header", "memory-header", "destination"])
def test_changed_source_or_existing_output_reject_before_materialization(
    source: Path, tmp_path: Path, changed: str
) -> None:
    output = tmp_path / "diagnostic"
    if changed == "cpp":
        (source / "llvm/lib/Analysis/REVPass.cpp").write_text("different revision")
    elif changed == "header":
        (source / "llvm/include/llvm/Analysis/REVPass.h").write_text("different header")
    elif changed == "memory-header":
        (source / "llvm/include/llvm/Analysis/MemorySSA.h").write_text("changed custom header")
    else:
        output.mkdir()
    with pytest.raises(ValueError):
        diagnostic.materialize(source, output)
    assert not (output / "diagnostic.json").exists()
    assert not (output / "patched").exists()


def test_fixture_oracle_follows_real_edges_and_scalar_values_independently_of_phi_order() -> None:
    source = (diagnostic.SUPPORT / "speq_phi_fixtures.ll").read_text()
    functions = re.findall(r"define i32 @(\w+)\(.*?\) \{(.*?)\n\}", source, re.S)
    assert len(functions) == 7
    outcomes = {}
    for name, body in functions:
        if name.startswith("unsupported_"):
            assert "switch i1" in body
            continue
        blocks = dict(re.findall(r"^(\w+):\n(.*?)(?=^\w+:|\Z)", body, re.M | re.S))
        incoming = {block: int(value) for value, block in re.findall(r"\[ (\d+), %(\w+) \]", blocks["merge"])}
        values = []
        for condition in (True, False):
            current = "entry"
            memory = None
            for _ in range(4):
                stores = re.findall(r"store i32 (\d+), ptr %p", blocks[current])
                if stores:
                    memory = int(stores[-1])
                conditional = re.search(r"br i1 %cond, label %(\w+), label %(\w+)", blocks[current])
                if conditional:
                    target = conditional.group(1 if condition else 2)
                else:
                    branch = re.search(r"br label %(\w+)", blocks[current])
                    assert branch
                    target = branch.group(1)
                if target == "merge":
                    assert incoming[current] == memory
                    values.append(memory)
                    break
                current = target
            else:
                pytest.fail("fixture did not reach its PHI merge")
        outcomes[name] = values
    assert outcomes == {
        "direct_true": [0, 22],
        "direct_true_reversed": [0, 22],
        "direct_false": [11, 0],
        "direct_false_reversed": [11, 0],
        "diamond": [11, 22],
        "diamond_reversed": [11, 22],
    }


def test_normal_recorder_build_uses_pinned_isolated_repair_and_keeps_original_source(
    source: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from scripts.paper_benchmarks import record_speq

    for name, digest in (
        ("REV_PASS_SHA256", diagnostic.REV_PASS_SHA256),
        ("REV_PASS_HEADER_SHA256", diagnostic.REV_PASS_HEADER_SHA256),
        ("REV_MEMORY_SSA_SHA256", diagnostic.MEMORY_SSA_SHA256),
    ):
        monkeypatch.setattr(record_speq, name, digest)
    original = (source / "llvm/lib/Analysis/REVPass.cpp").read_bytes()
    commands = []

    def metadata(command: tuple) -> str:
        commands.append(command)
        if command[-1] == "--bindir":
            return str(tmp_path / "llvm/bin")
        if command[-1] == "--version":
            return "17.0.6"
        return "-std=c++17"

    def compile_plugin(command: tuple, *, check: bool) -> None:
        assert check
        commands.append(command)
        compile_source = Path(command[3])
        assert compile_source == tmp_path / "phi-repair/patched/llvm/lib/Analysis/REVPass.cpp"
        assert diagnostic.EDGE_AWARE_PHI in compile_source.read_text()
        assert f"-I{tmp_path / 'phi-repair/patched/llvm/include'}" in command
        assert (tmp_path / "phi-repair/patched/llvm/include/llvm/Analysis/MemorySSA.h").is_file()
        Path(command[-1]).write_text("mock plugin; no compiler executed")

    monkeypatch.setattr(record_speq, "command_output", metadata)
    monkeypatch.setattr(record_speq.subprocess, "run", compile_plugin)
    result = record_speq.build_rev_plugin(
        source, tmp_path / "llvm-config", tmp_path / "plugin.so", repair_phi_polarity=True
    )
    assert result == (tmp_path / "llvm/bin/opt", tmp_path / "plugin.so", "17.0.6")
    assert len(commands) == 4
    assert (source / "llvm/lib/Analysis/REVPass.cpp").read_bytes() == original
    assert (tmp_path / "phi-repair/original/REVPass.cpp").read_bytes() == original


def test_normal_recorder_rejects_changed_header_before_compilation(
    source: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from scripts.paper_benchmarks import record_speq

    monkeypatch.setattr(record_speq, "REV_PASS_SHA256", diagnostic.REV_PASS_SHA256)
    monkeypatch.setattr(record_speq, "REV_PASS_HEADER_SHA256", diagnostic.REV_PASS_HEADER_SHA256)
    monkeypatch.setattr(record_speq, "REV_MEMORY_SSA_SHA256", diagnostic.MEMORY_SSA_SHA256)
    (source / "llvm/include/llvm/Analysis/MemorySSA.h").write_text("wrong header")
    monkeypatch.setattr(record_speq, "command_output", lambda _: pytest.fail("must reject before native commands"))
    with pytest.raises(ValueError, match="MemorySSA.h"):
        record_speq.build_rev_plugin(source, tmp_path / "llvm-config", tmp_path / "plugin", repair_phi_polarity=True)
    assert not (tmp_path / "phi-repair").exists()
