#!/usr/bin/env python3
"""Add the Lean-extracted semantics to the paper as a section after disequality.

Reads `paper/semantics.tex`, inlines every `\\inputleannode{...}` from the blueprint
extraction, and writes each named block to `<paper-dir>/generated/<name>.tex`, with
`generated/macros.tex` holding the macros it uses. A display block is a footnote-size
inline display, not a float, so the paper's prose flows around it. Every generated file
says that it is generated and where to edit instead. The section itself,
`<paper-dir>/semantics.tex`, is written once, as the blocks in order with room for prose
between them, and then left alone; `main.tex` gets
`\\input{semantics}` after `\\input{disequality}`, `\\input{generated/macros}` after
`\\input{macros}`, and the packages the displays need, each inserted once.

Usage: paper_sync.py [--paper-dir DIR] [--no-extract] [--build]
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "paper" / "semantics.tex"
LIBRARY_INDEX = ROOT / "semantics" / ".lake" / "build" / "blueprint" / "library" / "EgglogPaper.tex"
DEFAULT_PAPER = ROOT.parent / "extended-egglog-paper"
PACKAGES = ("mathpartir", "stmaryrd", "placeins")
GENERATED_DIR = "generated"
SECTION_FILE = "semantics.tex"
# Programs the congruence pass is run on, rendered in the paper's notation by
# `difftest paper-tex`: (generated file stem, source program).
EXAMPLES = (("congruence_example", ROOT / "paper" / "background.egg"),)
LEAN_BIN = Path(os.environ.get("LEAN_BIN_DIR") or "~/.elan/bin").expanduser()
SECTION_ANCHOR = "\\input{disequality}"
MACROS_ANCHOR = "\\input{macros}"

GENERATED_HEADER = """%% GENERATED FILE. Do not edit.
%% Written by scripts/paper_sync.py in the extended-proofs repository (`make paper-sync`)
%% from paper/semantics.tex there and from the @[blueprint] statements in
%% semantics/EgglogSemantics/{Spec,Source,Congruence}/*.lean. Edit those and rerun.
"""

MACROS = r"""\providecommand{\kw}[1]{\mathsf{#1}}
\providecommand{\eval}[1]{\llbracket #1\rrbracket_{\sigma}}
\providecommand{\ir}[3]{\inferrule[\textsc{#1}]{#2}{#3}}
\providecommand{\syntaxline}[2]{%
  \noindent\makebox[5em][l]{\textsf{#1}}\mbox{$#2$}\par}
% A block of semantics displays, in the size given as the optional argument (footnote size
% by default). It is a one-item trivlist, so the class's own list spacing (\topsep) frames
% it and the size command supplies the display skips; the only other setting is
% mathpartir's line skip between rows of rules.
\makeatletter
\@ifundefined{semanticsblock}{%
  \newenvironment{semanticsblock}[1][\footnotesize]{%
    \begin{trivlist}#1
    \def\MathparLineskip{\lineskiplimit=0.6em\lineskip=0.6em plus 0.2em}%
    \item[]\ignorespaces}{\end{trivlist}}}{}
\makeatother
"""

SECTION_HEADER = """%% The semantics section. This file is yours to edit: write the prose between the blocks.
%% The blocks under generated/ are inline displays, rewritten by scripts/paper_sync.py
%% in the extended-proofs repository; do not edit them by hand.
\\section{Semantics}
\\label{sec:semantics}
"""


def node_paths() -> dict[str, Path]:
    """The blueprint's label-to-artifact map: the library index lists one file per module,
    and each of those names its nodes."""
    if not LIBRARY_INDEX.exists():
        sys.exit(f"paper_sync: {LIBRARY_INDEX} missing; run without --no-extract")
    paths: dict[str, Path] = {}
    semantics = ROOT / "semantics"
    for module in re.findall(r"\\input\{([^}]*)\}", LIBRARY_INDEX.read_text()):
        module_file = semantics / module
        if not module_file.exists():
            continue
        for label, path in re.findall(r"\\newleannode\{([^}]*)\}\{\\input\{([^}]*)\}\}", module_file.read_text()):
            paths[label] = Path(path if path.endswith(".tex") else path + ".tex")
    return paths


def clean_node(text: str) -> str:
    """One extracted node, without the blueprint bookkeeping. The label stays, on the
    node's first line, so the paper can refer to the definition."""
    labels = []
    lines = []
    for line in text.splitlines():
        stripped = line.strip()
        if stripped in ("\\begin{paperfragment}", "\\end{paperfragment}", "\\leanok"):
            continue
        if stripped.startswith(("\\uses{", "\\lean{", "% at ")):
            continue
        if stripped.startswith("\\label{"):
            labels.append(stripped)
            continue
        lines.append(line)
    return "".join(labels) + "\n".join(lines).strip() + "\n"


def strip_command(text: str, name: str) -> str:
    """Remove every `\\name{...}` with balanced braces, including a trailing newline."""
    out = []
    i = 0
    token = "\\" + name + "{"
    while True:
        j = text.find(token, i)
        if j < 0:
            out.append(text[i:])
            break
        out.append(text[i:j])
        depth = 0
        k = j + len(token) - 1
        while k < len(text):
            if text[k] == "{":
                depth += 1
            elif text[k] == "}":
                depth -= 1
                if depth == 0:
                    break
            k += 1
        i = k + 1
        if i < len(text) and text[i] == "\n":
            i += 1
    return "".join(out)


# A display block `\begin{semantics}[size]{name} … \end{semantics}` becomes an inline display
# in that size (footnote size by default); a prose block
# `\begin{semanticstext}{name} … \end{semanticstext}` is inlined as is.
BLOCK = re.compile(
    r"\\begin\{(?P<env>semantics|semanticstext)\}(?P<size>\[[^\]]*\])?\{(?P<name>[^}]*)\}"
    r"(?P<body>.*?)\\end\{(?P=env)\}",
    re.S,
)


def render(text: str, nodes: dict[str, Path]) -> str:
    """A block's content with its nodes inlined."""
    missing = [label for label in re.findall(r"\\inputleannode\{([^}]*)\}", text) if label not in nodes]
    if missing:
        sys.exit(f"paper_sync: no extracted node for {missing}")
    text = re.sub(r"\\inputleannode\{([^}]*)\}", lambda m: clean_node(nodes[m.group(1)].read_text()), text)
    text = re.sub(r"\n{3,}", "\n\n", text).strip()
    return text + "\n"


def blocks(source: str, nodes: dict[str, Path]) -> list[tuple[str, bool, str]]:
    """Each block of the source, as `(name, is_display, content)`, in order."""
    start = source.index("\\begin{document}") + len("\\begin{document}")
    end = source.index("\\end{document}")
    out = []
    for m in BLOCK.finditer(source[start:end]):
        name = m.group("name").replace("-", "_")
        display = m.group("env") == "semantics"
        body = render(m.group("body"), nodes)
        if display:
            body = "\\begin{semanticsblock}" + (m.group("size") or "") + "\n" + body + "\\end{semanticsblock}\n"
        out.append((name, display, body))
    names = [n for n, _, _ in out]
    if len(set(names)) != len(names):
        sys.exit(f"paper_sync: duplicate block names {names}")
    return out


def section_skeleton(entries: list[tuple[str, bool, str]]) -> str:
    """The section, once: every block inlined in order, with room for prose between them."""
    parts = [SECTION_HEADER]
    for name, _, _ in entries:
        parts.append(f"% {name}\n\\input{{{GENERATED_DIR}/{name}}}\n")
    return "\n".join(parts)


def compiled_example(program: Path) -> str:
    """The congruence pass over `program`, in the paper's notation (`difftest paper-tex`)."""
    semantics = ROOT / "semantics"
    env = dict(os.environ, PATH=f"{LEAN_BIN}{os.pathsep}{os.environ.get('PATH', '')}")
    subprocess.run(["lake", "build", "difftest"], cwd=semantics, env=env, check=True, capture_output=True)
    run = subprocess.run(
        [str(semantics / ".lake" / "build" / "bin" / "difftest"), "paper-tex", str(program)],
        cwd=semantics,
        env=env,
        check=True,
        capture_output=True,
        text=True,
    )
    if run.stderr:
        print(run.stderr, end="", file=sys.stderr)
    return run.stdout


def insert_once(main: str, anchor: str, line: str) -> str:
    if line in main:
        return main
    if anchor not in main:
        sys.exit(f"paper_sync: {anchor!r} not found in main.tex")
    return main.replace(anchor, anchor + "\n\n" + line, 1)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--paper-dir", type=Path, default=DEFAULT_PAPER)
    parser.add_argument("--no-extract", action="store_true", help="reuse the last blueprint extraction")
    parser.add_argument("--build", action="store_true", help="run the paper's make afterwards")
    args = parser.parse_args()
    paper = args.paper_dir.resolve()
    main_tex = paper / "main.tex"
    if not main_tex.exists():
        sys.exit(f"paper_sync: {main_tex} missing")
    if not args.no_extract:
        subprocess.run([sys.executable, str(ROOT / "scripts" / "check.py"), "paper-extract"], check=True)
    generated = paper / GENERATED_DIR
    generated.mkdir(exist_ok=True)
    for stale in generated.glob("*.tex"):
        stale.unlink()
    (generated / "macros.tex").write_text(GENERATED_HEADER + MACROS)
    entries = blocks(SOURCE.read_text(), node_paths())
    for name, _, text in entries:
        (generated / f"{name}.tex").write_text(GENERATED_HEADER + text)
    for stem, program in EXAMPLES:
        (generated / f"{stem}.tex").write_text(GENERATED_HEADER + compiled_example(program))
    section = paper / SECTION_FILE
    if not section.exists():
        section.write_text(section_skeleton(entries))
    text = main_tex.read_text()
    for package in PACKAGES:
        if re.search(r"\\usepackage(\[[^\]]*\])?\{" + package + r"\}", text) is None:
            text = insert_once(text, "\\usepackage{xspace}", "\\usepackage{" + package + "}")
    text = insert_once(text, MACROS_ANCHOR, "\\input{" + GENERATED_DIR + "/macros}")
    text = insert_once(text, SECTION_ANCHOR, "\\input{semantics}")
    main_tex.write_text(text)
    print(
        f"paper_sync: wrote {len(entries)} blocks and {len(EXAMPLES)} compiled example(s) under {generated}"
        + ("" if section.exists() else f"; created {section.name}")
    )
    if args.build:
        subprocess.run(["make"], cwd=paper, check=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
