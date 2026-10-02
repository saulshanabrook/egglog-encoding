#!/usr/bin/env python3
"""Run the paper's array and SDQL workloads and compare their final e-graphs.

    python3 slotted/eval.py array --params 0
    python3 slotted/eval.py sdql --kernel mmm --phase 1st
    python3 slotted/eval.py --from /tmp/eval.jsonl --html /tmp/eval.html

Per side, one timed process checks the goal; a separate untimed process collects
counts and the final graph without inserting the target. Encoding/ref-multi
comparisons require equal class/node counts AND a verified isomorphism. Missing
or bounded-out evidence is inconclusive and fails the correctness gate.

ref-multi uses matching snapshot substitution. ref-nested uses the artifact's
syntactic substitution and is diagnostic only. Every selected side must reach
its goal. --no-counts explicitly opts into goal/timing checks alone.

Defaults: release builds, 300 seconds per process, the paper's round budgets.
Records are appended to eval.jsonl; use --jsonl for a separate cache. --from
prints cached observations without collecting; --merged selects the latest
observation per workload/side and invalidates stale comparisons. Both the compact
summary and full report are rendered by eval_report.py. See ENCODING.md for the
counting convention, substitution policies, and limitations of these comparisons.
"""

import argparse
import datetime
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "slotted"))
sys.path.insert(0, str(ROOT / "slotted" / "xdiff"))

import isomorphism as ISO  # noqa: E402
import xarray as XA  # noqa: E402
from eval_report import Comparison, Row, html, load_rows, markdown, report_sections  # noqa: E402

sc = __import__("slotted-egglog")
slotenc = __import__("slotted-encoder")
pf = __import__("paper_fixtures")

BATAX_SUBSET = ROOT / "slotted" / "tests" / "sdql-paper-batax.egg"

SIDES = ("encoding", "ref-multi", "ref-nested")
SCRATCH = ROOT / "target" / "slotted"
#: Where every run is recorded unless `--jsonl` says otherwise: append-only, ignored by git.
REPORT = ROOT / "eval.jsonl"


#: Release builds of both sides: egglog, and the reference through `xmulti` without the
#: crate's `checks` feature, the way the paper's experiments ran it.
EGGLOG = ROOT / "target" / "release" / "egglog"
#: `--group-cap`: how many live slots the oracle enumerates a symmetry group over when it
#: dumps its graph; past it the dump, and so the counts and the comparison, are unavailable.
#: The oracle's own default is 6, which stops at every second-phase SDQL graph; 10 covers
#: all but TTM's, whose 12-slot classes take the oracle minutes to enumerate.
GROUP_CAP = 10
XMULTI = ROOT / "slotted" / "xmulti" / "target" / "release" / "xmulti"
BUILDS = (
    ("cargo", "build", "--release", "--bin", "egglog"),
    ("cargo", "build", "--release", "--no-default-features", "--manifest-path", "slotted/xmulti/Cargo.toml"),
)


def build():
    """Bring both binaries up to date, so a timing is of the code in the checkout.
    cargo's own output stays on stderr."""
    for cmd in BUILDS:
        if subprocess.run(cmd, cwd=ROOT, stdout=sys.stderr).returncode != 0:
            sys.exit(f"eval.py: `{' '.join(cmd)}` failed")


# ------------------------------------------------------------------ the reference
def oracle_env(side):
    """Choose the comparison's policy explicitly, overriding ambient XMULTI_SUBST."""
    return {
        **os.environ,
        "XMULTI_GROUP_SLOT_CAP": str(GROUP_CAP),
        "XMULTI_SUBST": "syntactic" if side == "ref-nested" else "snapshot",
    }


def run_reference(spec, row, timeout, counts):
    """One timed `xmulti` run, whose GOAL line is the criterion; with `counts`, a second,
    untimed run that also dumps the graph, since enumerating the symmetry groups for the
    dump can cost more than the run."""
    env = oracle_env(row.side)
    row.substitution = env["XMULTI_SUBST"]
    t0 = time.perf_counter()
    try:
        r = subprocess.run([str(XMULTI)], input=spec, capture_output=True, text=True, timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        row.goal, row.seconds = "timeout", time.perf_counter() - t0
        if counts:
            row.graph_issue = "reference timed run exceeded timeout"
        return
    row.seconds = time.perf_counter() - t0
    lines = r.stdout.splitlines()
    if r.returncode != 0 and "REFERENCE_LIMIT:" not in r.stderr:
        row.goal = "error: " + ((r.stderr.strip().splitlines() or ["?"])[-1])[:80]
        row.graph_issue = row.goal
        return
    row.goal = next((ln.split()[1] for ln in lines if ln.startswith("GOAL ")), "?")
    row.saturated = next((ln.split()[1] for ln in lines if ln.startswith("SATURATED ")), "?")
    row.checks = next((ln.split("=", 1)[1] for ln in lines if ln.startswith("CONFIG checks=")), None)
    reported_subst = next((ln.split("=", 1)[1] for ln in lines if ln.startswith("CONFIG substitution=")), None)
    if reported_subst != row.substitution:
        row.goal = "error: reference substitution policy missing or unexpected; rebuild xmulti"
        row.graph_issue = row.goal
        return
    if counts:
        try:
            r = subprocess.run(
                [str(XMULTI)], input=spec + "dump\n", capture_output=True, text=True, timeout=timeout, env=env
            )
        except subprocess.TimeoutExpired:
            row.graph_issue = "reference graph dump exceeded timeout"
            return
        if r.returncode != 0:
            row.graph_issue = "reference graph dump failed: " + (r.stderr.strip() or f"exit {r.returncode}")
            return
        try:
            g = ISO.parse_reference(r.stdout)
        except ValueError as exc:
            row.graph_issue = f"reference graph unreadable: {exc}"
            return
        if not g.ids():
            row.graph_issue = "reference graph dump is empty"
            return
        row.classes, row.nodes = g.summary()
        row.graph = g


def ctor_lines(lang):
    """`ctor <tag> <Name>` lines: what the encoding calls each of the oracle's constructors,
    so the oracle's substitution snapshot breaks ties by the same spelling."""
    out = []
    for op in {id(op): op for op in lang.ops.values()}.values():
        if op.ref:
            out.append(f"ctor {op.ref} {op.ctor}")
        else:
            out.append(f"ctor {'symbol' if 'String' in op.sig else 'number'} {op.ctor}")
    return sorted(out)


def rule_lines(lang, rules_path, selected, nested):
    """A rule file's rules as oracle spec lines, flattened or nested."""
    src = sc.Source(rules_path)
    out = []
    for form in sc.parse(rules_path.read_text()):
        if not (isinstance(form, list) and form and form[0] == "rewrite"):
            continue
        r = sc.rewrite_parts(src, form)
        if selected is not None and r["name"] not in selected:
            continue
        lhs = src.term(r["lhs"], ground=False)
        rhs = slotenc.pat_sexpr(lang, slotenc.rhs_of(lang, src.term(r["rhs"], ground=False)))
        if nested:
            out += ["rule", f"nested {slotenc.pat_sexpr(lang, slotenc.rhs_of(lang, lhs))}", f"rhs root {rhs}"]
        else:
            root, atoms = slotenc.flatten(lang, lhs)
            root, atom_text = slotenc.atom_lines(lang, root, atoms)
            out += ["rule", *atom_text, f"rhs {root} {rhs}"]
        for want, slot, pvars in r["conds"]:
            out.append(f"cond {'in' if want else 'notin'} {slot} {' '.join(pvars)}")
    return out


# ------------------------------------------------------------------- the encoding
def run_egglog(program, name, row, timeout, goal_of):
    """Run one egglog program; `goal_of(result)` reads the criterion off it."""
    SCRATCH.mkdir(parents=True, exist_ok=True)
    path = SCRATCH / f"eval-{name}-{os.getpid()}.egg"
    path.write_text(program)
    t0 = time.perf_counter()
    try:
        r = subprocess.run([str(EGGLOG), str(path)], capture_output=True, text=True, cwd=ROOT, timeout=timeout)
    except subprocess.TimeoutExpired:
        row.goal, row.seconds = "timeout", time.perf_counter() - t0
        return
    finally:
        path.unlink(missing_ok=True)
    row.seconds = time.perf_counter() - t0
    row.goal = goal_of(r)


def one_more_round(program):
    """The program's last user-rule schedule, cut to one round.

    A step of the encoding is `(repeat n (seq (run) ...))` around the machinery's
    saturation; the same block with `n` set to 1 is one further step, which is how a
    run is asked whether it had settled. `None` when the program has no such step.
    """
    block, at = None, program.find("(run-schedule")
    while at >= 0:
        depth, end = 0, at
        for end in range(at, len(program)):
            depth += program[end] == "("
            depth -= program[end] == ")"
            if depth == 0:
                break
        if "(repeat " in program[at : end + 1]:
            block = program[at : end + 1]
        at = program.find("(run-schedule", end)
    return re.sub(r"\(repeat \d+ ", "(repeat 1 ", block, count=1) if block else None


def saturation_probe(program):
    """The program with one more round run under `push`/`pop`: the e-graph the run
    serializes is still the run's own, and the two `print-size` listings around the extra
    round say whether it changed anything -- the reference's own notion of having
    saturated, a round that applies nothing new."""
    extra = one_more_round(program)
    if extra is None:
        return program
    return program + "\n".join(["(print-size)", "(push)", extra, "(print-size)", "(pop)", ""])


def saturated(stdout):
    """Whether the two `print-size` listings agree, ignoring the rules' own match stores,
    which `slotted-apply` empties as it acts on them."""
    sizes = [(name, int(n)) for name, n in re.findall(r"\((\S+) (\d+)\)", stdout) if not name.startswith("_matched_")]
    if not sizes or len(sizes) % 2:
        return "?"
    half = len(sizes) // 2
    return "yes" if sizes[:half] == sizes[half:] else "no"


def encoding_counts(program, name, lang, row, timeout):
    """Classes and nodes of the encoding's final graph, read as the isomorphism checker
    reads it, whether one more round would have changed it, and the graph itself for
    `compare`."""
    SCRATCH.mkdir(parents=True, exist_ok=True)
    path = SCRATCH / f"eval-{name}-{os.getpid()}-counts.egg"
    jpath = path.with_suffix(".json")
    path.write_text(saturation_probe(program))
    try:
        r = subprocess.run(
            [str(EGGLOG), "--to-json", *ISO.SERIALIZE_LIMITS, str(path)],
            capture_output=True,
            text=True,
            cwd=ROOT,
            timeout=timeout,
        )
        if r.returncode != 0:
            row.graph_issue = "encoding graph dump failed: " + (r.stderr.strip() or f"exit {r.returncode}")
            return
        if ISO.incomplete_serialization(r.stderr):
            row.graph_issue = "encoding graph serialization was truncated"
            return
        if not jpath.exists():
            row.graph_issue = "encoding graph dump was not written"
            return
        row.saturated = saturated(r.stdout)
        ISO.use_language(lang)
        g, issues = ISO.build_encoding_graph(json.loads(jpath.read_text()))
        if issues:
            row.graph_issue = "encoding graph unreadable: " + "; ".join(map(str, issues))
            return
        # the reference's node forms: a binder's bound slot as a slot literal
        var_class = next((c for c in g.ids() if any(n[0] == "var" for n in g.nodes[c])), None)
        g, unfaithful = ISO.to_reference_shape(g, var_class)
        if unfaithful:
            row.graph_issue = "encoding graph cannot be converted faithfully: " + str(unfaithful)
            return
        row.classes, row.nodes = g.summary()
        row.graph = g
    except subprocess.TimeoutExpired:
        row.graph_issue = "encoding graph dump exceeded timeout"
    except (json.JSONDecodeError, ISO.IsomorphismLimit) as exc:
        row.graph_issue = f"encoding graph unavailable: {exc}"
    finally:
        path.unlink(missing_ok=True)
        jpath.unlink(missing_ok=True)


def compare_counts(enc, ref):
    """A cheap check of the reported sizes, independent of witness search/verification."""
    missing = False
    for name in ("classes", "nodes"):
        a, b = getattr(enc, name), getattr(ref, name)
        if a is None or b is None:
            missing = True
        elif a != b:
            return f"different: {name} {a} vs {b} (encoding vs reference)"
    return "inconclusive: counts unavailable" if missing else "same counts"


def compare(rows):
    """Compare complete graphs, preserving differences and resource limits.

    Only a verified class/slot/group/node witness establishes graph equality.
    Probe partitions and row counts cannot replace that obligation.
    """
    enc = next((r for r in rows if r.side == "encoding"), None)
    if enc is None:
        return
    for ref_row in (r for r in rows if r.side != "encoding"):
        enc.vs_ref[ref_row.side] = Comparison(enc.observation, ref_row.observation, compare_graphs(enc, ref_row))


def compare_graphs(enc, reference):
    counts = compare_counts(enc, reference)
    if counts != "same counts":
        issues = [r.graph_issue for r in (enc, reference) if r.graph_issue]
        return counts + ("; " + "; ".join(issues) if issues else "")
    if enc.graph is None:
        return "inconclusive: no encoding graph"
    if reference.graph is None:
        return "inconclusive: no reference graph"
    cap, ISO.SEARCH_CAP = ISO.SEARCH_CAP, min(ISO.SEARCH_CAP, 5_000)
    try:
        iso, why = ISO.find_isomorphism(reference.graph, enc.graph)
        if iso is not None:
            bad = ISO.verify(reference.graph, enc.graph, *iso)
            return "isomorphic" if bad is None else f"inconclusive: witness rejected ({bad})"
        if why and why.endswith("-- inconclusive"):
            return "inconclusive: " + why.removesuffix(" -- inconclusive")
        return f"different: {why}"
    except (ISO.IsomorphismLimit, RecursionError) as exc:
        return f"inconclusive: {exc}"
    finally:
        ISO.SEARCH_CAP = cap


# ------------------------------------------------------------------ the array study
def array_rows(params, rounds, sides, counts, timeout):
    for n in params:
        case = XA.goal_cases([n], rounds=rounds)[0]
        a, b = case.probes
        head = [f"rounds {rounds}", *ctor_lines(XA.LANG), f"term {XA.sexpr(a)}"]
        goal = [f"goal {XA.sexpr(b)}"]
        group, bare_program = [], None
        for side in sides:
            row = Row("array", case.name, side, rounds)
            if side == "ref-multi":
                lines = [ln for r in case.rules for ln in r.spec_lines()]
                run_reference("\n".join(head + lines + goal) + "\n", row, timeout, counts)
            elif side == "ref-nested":
                lines = rule_lines(XA.LANG, XA.ARRAY_SRC_RULES, None, nested=True)
                run_reference("\n".join(head + lines + goal) + "\n", row, timeout, counts)
            else:
                prog = XA.egg_program(case, mult=1, defer_probes=True)
                probes = len(case.probes)

                def goal_of(r, k=probes):
                    if r.returncode != 0:
                        return "error"
                    return "yes" if XA.parse_same_class(r.stdout, k).startswith("[0,1]") else "no"

                run_egglog(prog, case.name, row, timeout, goal_of)
                if counts:
                    bare = XA.Case(case.name, case.terms, case.rules, [], rounds=rounds)
                    bare_program = XA.egg_program(bare, mult=1).replace("(print-function SameClass 100000)", "")
                    encoding_counts(bare_program, case.name, XA.LANG, row, timeout)
            group.append(row)
        if counts and bare_program is not None:
            compare(group)
        yield from group


# ------------------------------------------------------------------- the SDQL study
def sdql_program(kernel, phase, rules, rounds, with_target):
    """One workload as a slotted source: the full library by include, or BATAX's own 12."""
    if rules == 12:
        # the goal-directed test, its own rules and schedule; only its terms are reused
        forms = sc.parse(BATAX_SUBSET.read_text())
        forms = [["run", str(rounds)] if f[:1] == ["run"] and f[1] != "0" else f for f in forms]
    else:
        forms = pf.test_forms(kernel, phase, rounds)
    if not with_target:
        # the saturated input alone, for counting: no target, no check
        forms = [f for f in forms if f[0] != "check" and f[:2] != ["let", "paper-target"]]
    SCRATCH.mkdir(parents=True, exist_ok=True)
    path = SCRATCH / f"eval-{kernel}_{phase}-{rules}-{'goal' if with_target else 'counts'}-{os.getpid()}.egg"
    path.write_text("\n".join(sc.render(f) for f in forms) + "\n")
    try:
        return sc.compile_source(sc.Source(path))
    finally:
        path.unlink(missing_ok=True)


def sdql_rows(workloads, rules, rounds, sides, counts, timeout):
    lang = pf.reference_language()
    source = sc.Source(pf.RULES)
    for kernel, phase in workloads:
        start, target = pf.workload_text(kernel, phase, source, lang)
        budget = pf.iteration_limit(kernel, phase) if rounds is None else rounds
        selected = None
        if rules == 12:
            subset = sc.Source(BATAX_SUBSET)
            selected = {
                sc.rule_name(subset, form) for form in sc.parse(BATAX_SUBSET.read_text()) if form[:1] == ["rewrite"]
            }
        head = [f"rounds {budget}", *ctor_lines(lang), f"term {start}"]
        goal = [f"goal {target}"]
        name = f"{kernel}_{phase}-{rules}rules"
        group, bare_program = [], None
        for side in sides:
            row = Row("sdql", name, side, budget, rules)
            row.paper = pf.TABLE1[(kernel, phase)]
            if side.startswith("ref-"):
                lines = rule_lines(lang, pf.RULES, selected, nested=(side == "ref-nested"))
                run_reference("\n".join(head + lines + goal) + "\n", row, timeout, counts)
            else:

                def goal_of(r):
                    if r.returncode == 0:
                        return "yes"
                    return "no" if "(check" in r.stderr else "error"

                run_egglog(sdql_program(kernel, phase, rules, budget, True), name, row, timeout, goal_of)
                if counts:
                    bare_program = sdql_program(kernel, phase, rules, budget, False)
                    encoding_counts(bare_program, name, lang, row, timeout)
            group.append(row)
        if counts and bare_program is not None:
            compare(group)
        yield from group


def main():
    global GROUP_CAP
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("study", nargs="?", default="all", choices=("all", "array", "sdql"))
    ap.add_argument("--side", default="all", help="comma-separated subset of encoding,ref-multi,ref-nested")
    ap.add_argument("--params", type=int, nargs="*", default=[0, 1, 2], help="array: extra function parameters")
    ap.add_argument(
        "--rounds", type=int, default=None, help="iterations; default 6 for array, the artifact's limit for sdql"
    )
    ap.add_argument("--kernel", nargs="*", default=list(pf.KERNELS), choices=pf.KERNELS, help="sdql: kernels to run")
    ap.add_argument(
        "--phase", nargs="*", default=list(pf.PHASES), choices=pf.PHASES, help="sdql: compiler phases to run"
    )
    ap.add_argument(
        "--rules",
        type=int,
        default=44,
        choices=(12, 44),
        help="sdql: the full set, or the suite's goal-directed BATAX second-phase subset",
    )
    ap.add_argument(
        "--counts",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="count the final e-graphs' classes and nodes, whether the encoding had settled, and compare"
        " the encoding's graph with each reference side's (isomorphic, different, or inconclusive);"
        " require verified equality to ref-multi when both sides are selected",
    )
    ap.add_argument(
        "--group-cap",
        type=int,
        default=GROUP_CAP,
        help="live slots the oracle enumerates a symmetry group over when dumping; TTM's second phase"
        " needs 12, which takes the oracle minutes (default %(default)s)",
    )
    ap.add_argument("--timeout", type=int, default=300, help="seconds per run; the artifact's own budget")
    ap.add_argument(
        "--jsonl", type=Path, default=REPORT, help=f"record one JSON object per run here (default {REPORT.name})"
    )
    ap.add_argument(
        "--from",
        dest="report",
        type=Path,
        nargs="?",
        const=REPORT,
        help=f"print the table from a record instead of running (default {REPORT.name})",
    )
    ap.add_argument("--html", type=Path, help="also write the table as an HTML page here")
    ap.add_argument("--long", action="store_true", help="one row per run with every field, instead of the timing pivot")
    ap.add_argument(
        "--merged", action="store_true", help="with --from: the latest entry per workload and side across every batch"
    )
    ap.add_argument("--no-build", action="store_true", help="skip `cargo build`; the binaries are known current")
    args = ap.parse_args()

    GROUP_CAP = args.group_cap
    sides = SIDES if args.side == "all" else tuple(s.strip() for s in args.side.split(","))
    bad = [s for s in sides if s not in SIDES]
    if bad:
        ap.error(f"unknown side {bad}; choose from {SIDES}")

    if args.report:
        # reporting alone: the rows come from an earlier run's record
        rows, when = load_rows(args.report, args.merged)
        rows = [r for r in rows if r.side in sides]
        shown = "every batch, latest entries" if args.merged else f"the batch of {when}"
        print(f"{args.report}: {shown}", file=sys.stderr)
        if args.study != "all":
            rows = [r for r in rows if r.study == args.study]
        if args.side == "all":
            sides = tuple(s for s in SIDES if any(r.side == s for r in rows))
    else:
        rows = collect(args, sides, ap)

    sections = report_sections(rows, sides, args.long)
    print(
        "\n\n".join(
            f"## {title}\n\n{markdown(head, table)}" + (f"\n\n{note}" if note else "")
            for title, note, head, table in sections
        )
    )
    if args.html:
        args.html.write_text(html(sections))
        print(f"wrote {args.html}", file=sys.stderr)
    if not args.report:
        # one id per invocation: the clock alone can name two quick runs alike
        batch = f"{datetime.datetime.now().isoformat(timespec='microseconds')}-{os.getpid()}"
        with args.jsonl.open("a") as f:
            for r in rows:
                f.write(
                    json.dumps(
                        r.as_dict(batch, egglog=str(EGGLOG.relative_to(ROOT)), xmulti=str(XMULTI.relative_to(ROOT)))
                    )
                    + "\n"
                )
    return 0 if successful(rows, sides, args.counts) else 1


def successful(rows, sides, counts):
    """Goals must succeed; MultiPattern comparison needs equal counts and a certificate.

    The nested matcher is a diagnostic, not the correctness oracle. Explicit
    `--no-counts` runs check goals alone; missing verdicts or evidence about other
    observations do not satisfy a requested graph comparison.
    """
    if not rows or any(r.goal != "yes" for r in rows):
        return False
    if not counts or not {"encoding", "ref-multi"}.issubset(sides):
        return True
    groups = {}
    for row in rows:
        groups.setdefault(row.workload(), {})[row.side] = row
    return all(
        "encoding" in group
        and "ref-multi" in group
        and compare_counts(group["encoding"], group["ref-multi"]) == "same counts"
        and group["encoding"].verdict(group["ref-multi"]) == "isomorphic"
        for group in groups.values()
    )


def collect(args, sides, ap):
    """Build both sides and run the requested workloads: the rows a report is made of."""
    if not args.no_build:
        build()
    for tool in (EGGLOG, XMULTI):
        if not tool.exists():
            ap.error(f"missing {tool.relative_to(ROOT)}; run without --no-build")
    print(f"egglog {EGGLOG.relative_to(ROOT)}   xmulti {XMULTI.relative_to(ROOT)}", file=sys.stderr)

    rows = []
    if args.study in ("all", "array"):
        rows += list(
            array_rows(args.params, 6 if args.rounds is None else args.rounds, sides, args.counts, args.timeout)
        )
    if args.study in ("all", "sdql"):
        workloads = [w for w in pf.WORKLOADS if w[0] in args.kernel and w[1] in args.phase]
        if args.rules == 12 and workloads != [("batax", "2nd")]:
            ap.error("--rules 12 is the suite's BATAX second-phase subset: use --kernel batax --phase 2nd")
        rows += list(sdql_rows(workloads, args.rules, args.rounds, sides, args.counts, args.timeout))
    return rows


if __name__ == "__main__":
    sys.exit(main())
