"""Observation records, cache loading, and tables for slotted/eval.py.

No processes are launched here. Comparison evidence is tied to both observation
IDs, so merging cache batches cannot turn an unchecked pair into a verified one.
"""

import datetime
import json
import re
import uuid
from dataclasses import asdict, dataclass, replace

import paper_fixtures as pf

REPORT_SCHEMA = 4

SIDES = ("encoding", "encoding-no-aliasing", "ref-multi", "ref-nested-snapshot", "ref-nested")
EXACT_PAIRS = {"encoding": "ref-multi", "encoding-no-aliasing": "ref-nested-snapshot"}


@dataclass(frozen=True)
class Comparison:
    """A verdict about exactly two observations, including inconclusive outcomes."""

    encoding: str
    reference: str
    verdict: str


class Row:
    def __init__(self, study, case, side, rounds, rules=None):
        self.study, self.case, self.side, self.rounds, self.rules = study, case, side, rounds, rules
        self.observation = uuid.uuid4().hex
        self.goal, self.saturated, self.seconds = "?", "?", None
        self.classes, self.nodes = None, None
        self.checks = None  # the oracle's `CONFIG checks=` answer, for reference sides
        self.substitution = None  # the oracle's `CONFIG substitution=` answer
        self.paper = None  # Table 1's slotted row for this workload, when it has one
        #: encoding side: per reference side, how its final graph compares (`compare`)
        self.vs_ref = {}
        self.graph = None  # only used during comparison; not recorded in the cache
        self.graph_issue = None

    def workload(self):
        return self.study, self.case, self.rounds, self.rules

    def verdict(self, reference):
        if reference is None:
            return "inconclusive: reference observation unavailable"
        comparison = self.vs_ref.get(reference.side)
        if comparison is None:
            return "inconclusive: observations have not been compared"
        if (comparison.encoding, comparison.reference) != (self.observation, reference.observation):
            return "inconclusive: selected observations have not been compared"
        return comparison.verdict

    def as_dict(self, batch, *, egglog="target/release/egglog", xmulti="slotted/xmulti/target/release/xmulti"):
        d = dict(vars(self))
        d.pop("graph")
        d["schema"] = REPORT_SCHEMA
        d["vs_ref"] = {side: asdict(comparison) for side, comparison in self.vs_ref.items()}
        d["egglog"] = egglog
        d["xmulti"] = xmulti
        d["date"] = datetime.datetime.now().isoformat(timespec="seconds")
        d["batch"] = batch  # one invocation of this script: what a report shows by default
        return d

    @classmethod
    def from_dict(cls, d):
        """A row back from its `--jsonl` record."""
        if d.get("schema") != REPORT_SCHEMA:
            raise SystemExit("eval.py: report cache schema changed; recompute into a fresh --jsonl path")
        row = cls(d["study"], d["case"], d["side"], d["rounds"], d.get("rules"))
        for field in (
            "observation",
            "goal",
            "saturated",
            "seconds",
            "classes",
            "nodes",
            "checks",
            "substitution",
            "graph_issue",
        ):
            setattr(row, field, d[field])
        row.paper = tuple(d["paper"]) if d.get("paper") is not None else None
        row.vs_ref = {side: Comparison(**comparison) for side, comparison in d["vs_ref"].items()}
        return row


def load_rows(path, merged):
    """The runs a record holds: the latest batch -- one invocation of this script --
    or, `merged`, the latest entry per workload and side across every batch, in the
    order they first appeared. Comparisons belong to their original observations."""
    records = []
    with path.open() as f:
        for line in f:
            if line.strip():
                records.append(json.loads(line))
    if not records:
        return [], None
    if not merged:
        batch = records[-1].get("batch")
        records = [d for d in records if d.get("batch") == batch]
    latest, order = {}, []
    for d in records:
        row = Row.from_dict(d)
        key = (*row.workload(), row.side)
        if key not in latest:
            order.append(key)
        latest[key] = row
    for row in latest.values():
        for side, comparison in row.vs_ref.items():
            reference = latest.get((*row.workload(), side))
            row.vs_ref[side] = replace(comparison, verdict=row.verdict(reference))
    return [latest[key] for key in order], (None if merged else records[-1].get("date"))


# ------------------------------------------------------------------------- output
LONG_HEAD = (
    "study",
    "case",
    "side",
    "rounds",
    "rules",
    "goal",
    "saturated",
    "seconds",
    "classes",
    "nodes",
    "vs reference",
    "graph issue",
    "paper (iters, nodes, classes, sat.)",
)
SUMMARY_NOTE = (
    "Budget is the round limit; elapsed time includes unsuccessful runs. "
    "SDQL uses 44 rules unless noted. — means unavailable. "
    "encoding-no-aliasing restricts matching to the nested matcher's aliasing policy. "
    "ref-nested uses the paper's syntactic substitution; the other systems use snapshot substitution. "
    "Exact comparisons pair encoding with ref-multi, and encoding-no-aliasing with ref-nested-snapshot. "
    "Reference settings and correctness comparisons are in the full report."
)


def paper_cell(r):
    return "" if r.paper is None else f"{r.paper[0]}, {r.paper[1]:,}, {r.paper[2]:,}, {'yes' if r.paper[3] else 'no'}"


def long_cells(r):
    """One row's cells, as text, in `LONG_HEAD` order: the record of one run."""
    side = r.side + reference_label(r)
    counts = ["" if n is None else str(n) for n in (r.classes, r.nodes)]
    return [
        r.study,
        r.case,
        side,
        str(r.rounds),
        str(r.rules or ""),
        r.goal,
        r.saturated,
        seconds_cell(r),
        *counts,
        vs_cell(r),
        r.graph_issue or "",
        paper_cell(r),
    ]


def vs_cell(r):
    return "; ".join(f"{side}: {comparison.verdict}" for side, comparison in r.vs_ref.items())


def seconds_cell(r):
    return "" if r.seconds is None else f"{r.seconds:.3g}"


def graph_cell(r):
    """The final graph's size and saturation status, independent of goal outcome."""
    if r.classes is not None:
        return f"{r.classes}/{r.nodes}" + (f", sat. {r.saturated}" if r.saturated != "?" else "")
    return f"counts unavailable: {r.graph_issue}" if r.graph_issue else ""


def reference_label(*rows):
    labels = []
    for field, label in (("checks", "checks"), ("substitution", "subst")):
        values = {getattr(row, field) for row in rows}
        known = sorted(v for v in values if v is not None)
        if known:
            detail = "/".join(known)
            if None in values:
                detail += "/unknown"
            labels.append(f"{label} {detail}")
    return f" ({', '.join(labels)})" if labels else ""


def pivot(rows, sides):
    """One row per workload, with each side's goal, elapsed time, and graph separate."""
    columns = []
    for side in sides:
        label = reference_label(*(r for r in rows if r.side == side))
        columns.extend((f"{side} goal{label}", f"{side} elapsed (s)", f"{side} graph (classes/nodes, sat.)"))
    # the encoding's graph against each reference side it was compared with
    compared = [(e, s) for e in sides for s in sides if any(r.side == e and s in r.vs_ref for r in rows)]
    head = [
        "study",
        "case",
        "rounds",
        "rules",
        *columns,
        *(f"{e} vs {s}" for e, s in compared),
        "paper (iters, nodes, classes, sat.)",
    ]
    by_case, order = {}, []
    for r in rows:
        key = r.workload()
        if key not in by_case:
            by_case[key] = {"paper": paper_cell(r)}
            order.append(key)
        by_case[key][r.side] = [r.goal, seconds_cell(r), graph_cell(r)]
        for s, comparison in r.vs_ref.items():
            by_case[key][f"{r.side} vs {s}"] = comparison.verdict
    table = []
    for study, case, rounds, rules in order:
        got = by_case[(study, case, rounds, rules)]
        cells = [cell for s in sides for cell in got.get(s, ["", "", ""])]
        cells += [got.get(f"{e} vs {s}", "") for e, s in compared]
        table.append([study, case, str(rounds), str(rules or ""), *cells, got["paper"]])
    return head, table


def workload_label(study, case, rules):
    """Short paper names for known workloads, retaining custom workload identities."""
    if study == "sdql":
        for kernel, phase in pf.WORKLOADS:
            if case == f"{kernel}_{phase}-{rules}rules":
                name = "ΣMMM" if kernel == "mmm_sum" else kernel.upper()
                suffix = f", {rules} rules" if rules != 44 else ""
                return f"{name} ({phase}{suffix})"
    if study == "array" and (match := re.fullmatch(r"goal-2d-4f-N(\d+)", case)):
        return f"Array N={match[1]}"
    suffix = f" ({rules} rules)" if rules is not None else ""
    return f"{study}: {case}{suffix}"


def summary(rows, sides):
    """Table 1's grouped system rows, with independently measured goals and timings."""
    head = ("Workload", "System", "Budget", "Goal", "Elapsed (s)", "Nodes", "Classes", "Sat.")
    groups = {}
    for row in rows:
        groups.setdefault(row.workload(), {})[row.side] = row
    table = []
    for (study, case, rounds, rules), group in groups.items():
        label = workload_label(study, case, rules)
        for i, side in enumerate(sides):
            row = group.get(side)
            cells = [label if i == 0 else "", side, str(rounds)]
            if row is None:
                cells += ["missing", "—", "—", "—", "—"]
            else:
                goal = "error" if row.goal.startswith("error") else row.goal
                cells += [goal, seconds_cell(row) or "—"]
                cells += ["—" if n is None else f"{n:,}" for n in (row.nodes, row.classes)]
                cells += ["—" if row.saturated == "?" else row.saturated]
            table.append(cells)
    return head, table


def report_sections(rows, sides, long=False):
    full = (LONG_HEAD, [long_cells(r) for r in rows]) if long else pivot(rows, sides)
    return [("Summary", SUMMARY_NOTE, *summary(rows, sides)), ("Full report", "", *full)]


def markdown(head, table):
    """A Markdown table with its columns padded, so it also reads aligned in a terminal."""
    table = [list(head)] + table
    widths = [max(len(row[i]) for row in table) for i in range(len(head))]

    def line(cells):
        return "| " + " | ".join(c.ljust(w) for c, w in zip(cells, widths, strict=True)) + " |"

    rule = "|" + "|".join("-" * (w + 2) for w in widths) + "|"
    return "\n".join([line(table[0]), rule] + [line(c) for c in table[1:]])


def html(sections):
    """The summary and full table as a standalone page."""
    import html as h

    contents = []
    for title, note, head, table in sections:
        head_cells = "".join(f"<th>{h.escape(c)}</th>" for c in head)
        body = []
        for cells in table:
            row_class = ' class="group"' if cells[0] else ""
            body.append(f"<tr{row_class}>" + "".join(f"<td>{h.escape(c)}</td>" for c in cells) + "</tr>")
        contents.append(
            f"<section><h2>{h.escape(title)}</h2><div class=scroll>"
            f"<table><thead><tr>{head_cells}</tr></thead><tbody>\n"
            + "\n".join(body)
            + "\n</tbody></table></div>"
            + (f"<p>{h.escape(note)}</p>" if note else "")
            + "</section>"
        )
    return (
        "<!doctype html><meta charset=utf-8><meta name=viewport content='width=device-width, initial-scale=1'>"
        "<title>slotted eval</title>"
        "<style>body{font:14px system-ui,sans-serif;margin:2em}table{border-collapse:collapse}"
        "section{margin-bottom:2.5em}.scroll{overflow-x:auto}p{max-width:85ch;color:#555;line-height:1.5}"
        "th,td{border:1px solid #bbb;padding:4px 10px;text-align:left;white-space:nowrap}"
        "th{background:#eee}tr:nth-child(even){background:#f7f7f7}"
        "section:first-of-type th,section:first-of-type td{border:0;padding:6px 12px}"
        "section:first-of-type tr{background:none}"
        "section:first-of-type th{background:none;border-bottom:2px solid #777}"
        "section:first-of-type tr.group td{border-top:1px solid #ccc}"
        "section:first-of-type td:nth-child(n+3){text-align:right;font-variant-numeric:tabular-nums}"
        "</style>\n" + "\n".join(contents) + "\n"
    )
