"""Validate engine dumps and compare their logical slotted e-graphs.

Both engines export annotated egraph-serialize JSON. Rust validates the documents,
searches for an isomorphism, and independently verifies its witness. Python runs
the processes and passes engine documents unchanged; mutable graph builders are
used only for test fixtures and mutations. Work limits remain inconclusive.

Run: `python3 slotted/xdiff/isomorphism.py [name-prefix|fuzz N [seed]]`
"""

import json
import os
import random
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from slotted import test_program as driver  # noqa: E402

SEARCH_CAP = 200_000
MATCH_VARIANT_CAP = 200_000


# ------------------------------------------------------------------ the graphs
class Graph:
    """Mutable test fixture builder; engine exports use Document instead.

    A node is `(op, elems)`; an elem is `("slot", s)` for a slot the node names
    directly, or `("child", cid, ((child_slot, parent_slot), ...))`.
    """

    def __init__(self):
        self.slots = {}  # cid -> tuple of slot names
        self.group = {}  # cid -> set of permutations, each a frozenset of pairs
        self.nodes = {}  # cid -> list of nodes

    def add_class(self, cid, slots):
        self.slots.setdefault(cid, tuple(slots))
        self.group.setdefault(cid, set())
        self.nodes.setdefault(cid, [])

    def close_groups(self):
        """Add each group's identity; this does not compute closure."""
        for cid, slots in self.slots.items():
            self.group[cid].add(frozenset((s, s) for s in slots))

    def ids(self):
        return sorted(self.slots)

    def summary(self):
        return (len(self.slots), sum(len(v) for v in self.nodes.values()))


class Document:
    """An engine's annotated graph, passed unchanged to the Rust checker."""

    def __init__(self, document):
        self.document = document

    def ids(self):
        return sorted(self.document["slotted"]["classes"])

    def summary(self):
        return len(self.ids()), len(self.document["nodes"])


def parse_reference(out):
    exports = [line.removeprefix("GRAPH ") for line in out.splitlines() if line.startswith("GRAPH ")]
    if len(exports) != 1:
        raise ValueError("expected one complete GRAPH export")
    return Document(json.loads(exports[0]))


def export_command(path, lang):
    """Select reference operator spellings; Rust reads all layouts and table rows."""
    names = []
    for op in lang.ops.values():
        fields = [json.dumps(op.ref or ("=payload" if op.pays else op.ctor))]
        if op.ref_prefix:
            fields.append(json.dumps(op.ref_prefix))
        names.append(f"({op.ctor} {' '.join(fields)})")
    return f"(slotted-export {json.dumps(str(path))} {' '.join(names)})\n"


def validate_document(graph, *, checker=None):
    result = rust_request({"graph": serialized_graph(graph)}, checker=checker)
    if result["status"] != "valid":
        raise ValueError(result["reason"])
    return result["classes"], result["nodes"]


def read_export(doc, *, checker=None):
    """Validate native export and independently check its recorded table sizes."""
    graph = Document(doc)
    counts = validate_document(graph, checker=checker)
    raw = doc["counts"]
    if (raw["classes"], raw["nodes"]) != counts:
        raise ValueError(f"raw class/node counts {raw} disagree with exported graph {counts}")
    return graph


def fixture(graph):
    """Copy a standard document into the mutable builder used by mutation tests.

    Runtime comparisons use the original document. This helper deliberately keeps
    only the single untyped carrier used by these mutation fixtures.
    """
    doc = serialized_graph(graph)
    if (
        doc.get("root_eclasses")
        or any(c.get("type") for c in doc.get("class_data", {}).values())
        or any(n.get("subsumed") for n in doc["nodes"].values())
    ):
        raise ValueError("mutation fixture requires an untyped graph without roots or subsumption")
    out = Graph()
    for cid, data in doc["slotted"]["classes"].items():
        slots = data["slots"]
        out.add_class(cid, slots)
        out.group[cid] = {frozenset(zip(slots, (slots[i] for i in p), strict=True)) for p in data["group"]}
    for nid, node in doc["nodes"].items():
        children = iter(node["children"])
        elems = []
        for arg in doc["slotted"]["nodes"][nid]["arguments"]:
            if arg["kind"] == "slot":
                elems.append(("slot", arg["slot"]))
            else:
                elems.append(("child", doc["nodes"][next(children)]["eclass"], tuple(map(tuple, arg["renaming"]))))
        out.nodes[node["eclass"]].append((node["op"], tuple(elems)))
    return out


def group_sizes(graph):
    return [len(c["group"]) for c in serialized_graph(graph)["slotted"]["classes"].values()]


def serialized_graph(g):
    """Export annotated egraph-serialize JSON, preserving duplicates and empty classes.

    Integer and string slot names remain distinct. Child pointers name an arbitrary
    node of their class; a dangling pointer remains an invalid input.
    """
    if isinstance(g, Document):
        return g.document
    if set(g.slots) != set(g.group) or set(g.slots) != set(g.nodes):
        raise ValueError("class slots, groups, and nodes name different classes")
    ids = {c: json.dumps(c) for c in g.ids()}

    def node_id(c, i):
        return f"{ids[c]}/{i}"

    classes, nodes, annotations = {}, {}, {}
    for c in g.ids():
        slots = g.slots[c]
        positions = {s: i for i, s in enumerate(slots)}
        group = []
        for permutation in g.group[c]:
            p = dict(permutation)
            if len(p) != len(permutation) or set(p) != set(slots) or not set(p.values()) <= set(slots):
                raise ValueError(f"{c}: malformed symmetry permutation")
            group.append([positions[p[s]] for s in slots])
        classes[ids[c]] = {"slots": list(map(json.dumps, slots)), "group": sorted(group)}
        for i, (op, elems) in enumerate(g.nodes[c]):
            children, arguments = [], []
            for elem in elems:
                if elem[0] == "slot":
                    arguments.append({"kind": "slot", "slot": json.dumps(elem[1])})
                elif elem[0] == "child":
                    children.append(node_id(elem[1], 0))
                    arguments.append(
                        {"kind": "child", "renaming": [[json.dumps(a), json.dumps(b)] for a, b in elem[2]]}
                    )
                else:
                    raise ValueError(f"{c}: unknown node argument {elem[0]!r}")
            nodes[node_id(c, i)] = {"op": op, "eclass": ids[c], "children": children}
            annotations[node_id(c, i)] = {"arguments": arguments}
    return {
        "nodes": nodes,
        "class_data": {cid: {} for cid in ids.values()},
        "slotted": {"classes": classes, "nodes": annotations},
    }


def rust_request(request, *, checker=None):
    checker = checker or driver.ROOT / "target/debug/egraph-isomorphism"
    result = subprocess.run([str(checker)], input=json.dumps(request), text=True, capture_output=True)
    try:
        response = json.loads(result.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(f"isomorphism checker failed ({result.returncode}): {result.stderr}") from exc
    codes = {
        "valid": 0,
        "isomorphic": 0,
        "verified": 0,
        "different": 1,
        "invalid": 2,
        "inconclusive": 3,
        "invalid_witness": 4,
    }
    if response.get("status") not in codes or result.returncode != codes[response["status"]]:
        raise RuntimeError(f"unexpected checker response ({result.returncode}): {response}")
    return response


def rust_check(left, right, *, checker=None, **options):
    return rust_request({"left": serialized_graph(left), "right": serialized_graph(right), **options}, checker=checker)


def find_isomorphism(ga, gb, *, search_cap=SEARCH_CAP, checker=None):
    """Return (witness, None), or (None, reason) for a mismatch, invalid input, or limit."""
    try:
        result = rust_check(ga, gb, checker=checker, limits={"search": search_cap, "node_variants": MATCH_VARIANT_CAP})
    except (KeyError, ValueError) as exc:
        return None, f"invalid graph: {exc}"
    match result["status"]:
        case "isomorphic":
            return result["witness"], None
        case "inconclusive":
            return None, result["reason"] + " -- inconclusive"
        case "invalid":
            return None, "invalid graph: " + result["reason"]
        case _:
            return None, result["reason"]


def verify(ga, gb, witness, *, checker=None):
    """Return None for a valid witness, otherwise its rejection reason."""
    try:
        result = rust_check(ga, gb, checker=checker, witness=witness)
    except (KeyError, ValueError) as exc:
        return f"invalid graph: {exc}"
    return None if result["status"] == "verified" else result["reason"]


# ------------------------------------------------------------------- the runners
#: A carrier's machinery seeds `(Var 0)` unconditionally, so that class exists on the
#: encoding side whether or not the case mentions it. Adding the same term to the
#: reference makes the two graphs comparable as wholes, rather than needing classes to
#: be dropped from one side by a rule about which ones "do not count". It is an ordinary
#: term to the reference, so any rule that fires on it fires on the encoding's copy too.
#:
#: `(Null)` is NOT seeded. It is an ordinary constructor of the language under test, and
#: neither side has a class for it unless a term built one.
SEED = "term (var $0)\n"


def reference_graph(case, mult=3, *, timeout=25):
    """The reference's graph after the SAME number of rounds the encoding gets steps.

    NOT SATURATION -- a fixed count, because a generated rule set need not have a fixpoint.
    A reference round applies every rule once and so does one `(run)` of the encoding's
    user rules, so at equal counts the two are answering the same question whether or not
    either has settled. `fuzz1152`, which never settles, is isomorphic at every budget from
    3 to 12 rounds. This used to skip a case the moment the reference reported
    `SATURATED no`, which threw away the only cases that test unbounded growth.

    The count is the ENCODING's, `rounds * mult`, since `_dump` runs
    `schedule(rounds * mult)`. Where the reference saturates the extra rounds change
    nothing, so it is safe for the whole corpus.

    Scale the spec's round budget without changing the terms, rules, or probes.
    """
    spec = case.spec()
    spec, subbed = re.subn(r"^rounds \d+$", f"rounds {case.rounds * mult}", spec, count=1, flags=re.M)
    assert subbed, f"{case.name}: spec has no `rounds` line to scale"
    try:
        r = subprocess.run(
            [str(driver.XMULTI)],
            input=spec + SEED + "dump\n",
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        # The reference running out of time is NOT a finding -- it is a case that cannot
        # be compared, which the encoding side has always reported that way. A rule with
        # unrelated atoms is a cross product, so some of those are simply too much work
        # for the reference; the small ones still finish and still get compared.
        return None, "reference timeout"
    if r.returncode != 0:
        if "REFERENCE_LIMIT:" in r.stderr:
            detail = next(line for line in r.stderr.splitlines() if "REFERENCE_LIMIT:" in line)
            return None, f"reference dump unavailable: {detail.strip()}"
        lines = (r.stderr or "?").strip().splitlines()
        detail = next(
            (line for line in lines if "panicked at" in line or "assertion" in line or "ERROR" in line),
            lines[-1],
        )
        return None, f"reference error: {detail}"
    try:
        graph = parse_reference(r.stdout)
        validate_document(graph)
        return graph, None
    except ValueError as exc:
        # The pinned oracle deliberately declines to enumerate symmetry groups above
        # six live slots.  That is a coverage limit, not evidence of agreement.
        return None, f"reference dump unavailable: {exc}"


def _dump(case, mult, timeout, *, egg_program=None):
    prog = egg_program(case, mult=mult) if egg_program else case.egg_program(mult=mult)
    prog = prog.replace("(print-function SameClass 100000)", "")
    p = driver.ROOT / f"xdiff-tmp-iso-{os.getpid()}-{mult}.egg"
    j = p.with_suffix(".json")
    j.unlink(missing_ok=True)
    p.write_text(prog + "\n" + export_command(j, case.lang))
    try:
        r = subprocess.run(
            [str(driver.EGGLOG), "--slotted-encoded", str(p)],
            capture_output=True,
            text=True,
            cwd=driver.ROOT,
            timeout=timeout,
        )
        if r.returncode != 0:
            return None, ("unreadable", f"encoding export failed: {r.stderr[-600:]}")
        if not j.exists():
            return None, ("unreadable", "encoding produced no exported e-graph")
        return read_export(json.loads(j.read_text())), None
    except subprocess.TimeoutExpired:
        return None, "timeout"
    except ValueError as exc:
        return None, ("unreadable", str(exc))
    finally:
        p.unlink(missing_ok=True)
        j.unlink(missing_ok=True)


def encoding_graph(case, *, egg_program=None):
    """The encoding's final graph, at the strongest fixpoint available to it.

    The harness's schedule saturates the `slotted` invariants between user-rule steps and
    gives the user rules a finite step count, since user rules are not expected to
    terminate. If that does not finish, the state is taken at a fixpoint of the *database*
    instead, established by two different step counts producing the same graph -- the same
    standard the partition comparison uses -- and reported separately.
    """
    g, err = _dump(case, 3, timeout=60, egg_program=egg_program)
    if err != "timeout":
        return g, err, 3
    a, e1 = _dump(case, 6, timeout=180, egg_program=egg_program)
    if e1:
        err = ("limit", "encoding too slow to settle") if e1 == "timeout" else e1
        return None, err, 6
    b, e2 = _dump(case, 12, timeout=180, egg_program=egg_program)
    if e2:
        err = e2 if e2 != "timeout" else ("limit", "encoding too slow to settle")
        return None, err, 12
    witness, why = find_isomorphism(a, b)
    if witness is None:
        if why.endswith(" -- inconclusive"):
            return None, ("limit", why), 12
        if why.startswith("invalid graph:"):
            return None, ("unreadable", why), 12
        return None, "encoding has not settled: doubling the rounds changes the graph", 12
    return a, None, 6


def check(
    case,
    encoding_builder=None,
    reference_builder=None,
    *,
    egg_program=None,
    search_cap=SEARCH_CAP,
):
    # Only a reference that ERRORS is skipped. One that has not settled is compared
    # anyway, at the same fixed number of rounds the encoding gets steps -- see
    # `reference_graph`.
    reference_builder = reference_builder or reference_graph
    enc, err, mult = encoding_builder(case) if encoding_builder else encoding_graph(case, egg_program=egg_program)
    if isinstance(err, tuple):
        return err[0], err[1]
    if err:
        return "FAIL", err
    # The timeout fallback may have selected a larger fixed-round graph.  Build the
    # reference at that exact multiplier; comparing ref@3 to enc@6 is not meaningful.
    ref, err = reference_builder(case, mult)
    if err:
        # A timeout or an oracle serialization ceiling is NOT COMPARABLE. An
        # unexpected oracle panic is a hard unreadable result: silently skipping it
        # could make the suite green by removing precisely the difficult cases.
        unavailable = err == "reference timeout" or err.startswith("reference dump unavailable:")
        return ("limit" if unavailable else "unreadable"), err
    iso, why = find_isomorphism(ref, enc, search_cap=search_cap)
    if iso is None:
        if why and why.endswith("-- inconclusive"):
            return "limit", why
        return "FAIL", f"{why}  [ref {ref.summary()} enc {enc.summary()}]"
    bad = verify(ref, enc, iso)
    if bad:
        return "FAIL", f"witness rejected: {bad}"
    n, m = ref.summary()
    groups = sum(group_sizes(ref))
    return "ok", (n, m, groups)


def selftest():
    """Hand-built graphs, exercising what the mutations may not reach.

    A checker that always answers "isomorphic" would pass every corpus, so direct graph
    answers are pinned here: relabelling, symmetry-equivalent child representatives,
    and redundant-slot alpha-renaming must be *accepted*; missing symmetries, moved
    edges, nonmember permutations, and broken repeated-slot sharing must be *rejected*.
    These use no engine or reference; native export validation has its own Rust tests.
    """

    def build(spec):
        g = Graph()
        for cid, (slots, perms, nodes) in spec.items():
            g.add_class(cid, slots)
            for p in perms:
                g.group[cid].add(frozenset(p))
            g.nodes[cid] = nodes
        g.close_groups()
        return g

    def kn(child, *pairs):
        return ("k", tuple(("child", child, (p,)) for p in pairs))

    swap = [[("a", "b"), ("b", "a")]]
    base = build(
        {"v": (("x",), [], [("var", (("slot", "x"),))]), "K": (("a", "b"), swap, [kn("v", ("x", "a"), ("x", "b"))])}
    )
    cases = [
        # the same graph with every slot renamed
        (
            "relabelled",
            True,
            build(
                {
                    "w": (("q",), [], [("var", (("slot", "q"),))]),
                    "J": (("m", "n"), [[("m", "n"), ("n", "m")]], [kn("w", ("q", "m"), ("q", "n"))]),
                }
            ),
        ),
        # identical nodes, but the class does not prove the swap
        (
            "symmetry dropped",
            False,
            build(
                {
                    "w": (("q",), [], [("var", (("slot", "q"),))]),
                    "J": (("m", "n"), [], [kn("w", ("q", "m"), ("q", "n"))]),
                }
            ),
        ),
        # the swap, but both edges land on one slot
        (
            "edge moved",
            False,
            build(
                {
                    "w": (("q",), [], [("var", (("slot", "q"),))]),
                    "J": (("m", "n"), [[("m", "n"), ("n", "m")]], [kn("w", ("q", "m"), ("q", "m"))]),
                }
            ),
        ),
    ]
    bad = 0
    for name, want, other in cases:
        got, why = find_isomorphism(base, other)
        ok = (got is not None) == want
        if got is not None and verify(base, other, got) is not None:
            ok = False
        bad += not ok
        print(
            f"  {'ok  ' if ok else 'FAIL'} {name:20} "
            f"isomorphic={got is not None}, expected={want}"
            f"{'' if got else '  (' + (why or '') + ')'}"
        )

    def cycle_edge_graph(prefix, second_edge):
        """A C3 child used twice, so one global slot map cannot hide its edge reps."""
        a, b, c = (f"{prefix}a", f"{prefix}b", f"{prefix}c")
        x, y, z = (f"{prefix}x", f"{prefix}y", f"{prefix}z")
        cycle = [(a, b), (b, c), (c, a)]
        cycle2 = [(a, c), (b, a), (c, b)]
        identity_edge = ((a, x), (b, y), (c, z))
        return build(
            {
                f"{prefix}C": (
                    (a, b, c),
                    [cycle, cycle2],
                    [("triple", (("slot", a), ("slot", b), ("slot", c)))],
                ),
                f"{prefix}P": (
                    (x, y, z),
                    [],
                    [
                        (
                            "pair",
                            (
                                ("slot", x),
                                ("slot", y),
                                ("slot", z),
                                ("child", f"{prefix}C", identity_edge),
                                ("child", f"{prefix}C", tuple(second_edge(a, b, c, x, y, z))),
                            ),
                        )
                    ],
                ),
            }
        )

    cycle_source = cycle_edge_graph("s", lambda a, b, c, x, y, z: ((a, x), (b, y), (c, z)))
    matcher_cases = [
        # The second child is stored under a different representative, reached by
        # the child's order-three symmetry.  The first edge prevents one global
        # class-slot bijection from absorbing that local representative choice.
        (
            "child 3-cycle representative",
            True,
            cycle_source,
            cycle_edge_graph("t", lambda a, b, c, x, y, z: ((c, x), (a, y), (b, z))),
        ),
        # A reflection is not in C3, even though it is a permutation of the same
        # three slots and conjugates C3 to itself.
        (
            "nonmember child representative",
            False,
            cycle_source,
            cycle_edge_graph("u", lambda a, b, c, x, y, z: ((a, x), (c, y), (b, z))),
        ),
        # Def. 8 extends the class-slot bijection independently for every e-node.
        # Thus one redundant name shared across two source nodes need not remain a
        # shared name across those two distinct target nodes.
        (
            "node-local redundant alpha",
            True,
            build({"r": ((), [], [("left", (("slot", "x"),)), ("right", (("slot", "x"),))])}),
            build({"q": ((), [], [("left", (("slot", "y"),)), ("right", (("slot", "z"),))])}),
        ),
        # Within one node, however, a bijection must preserve repeated-name
        # equality: alpha-renaming xx to yy is valid, but splitting xx into yz is not.
        (
            "redundant equality alpha",
            True,
            build({"r": ((), [], [("bind", (("slot", "x"), ("slot", "x")))])}),
            build({"q": ((), [], [("bind", (("slot", "y"), ("slot", "y")))])}),
        ),
        (
            "redundant equality split",
            False,
            build({"r": ((), [], [("bind", (("slot", "x"), ("slot", "x")))])}),
            build({"q": ((), [], [("bind", (("slot", "y"), ("slot", "z")))])}),
        ),
    ]
    for name, want, left, right in matcher_cases:
        got, why = find_isomorphism(left, right)
        ok = (got is not None) == want
        if got is not None and verify(left, right, got) is not None:
            ok = False
        bad += not ok
        print(
            f"  {'ok  ' if ok else 'FAIL'} {name:32} "
            f"isomorphic={got is not None}, expected={want}"
            f"{'' if got else '  (' + (why or '') + ')'}"
        )

    seen_multipliers = []

    def fake_encoding(_case):
        return base, None, 6

    def fake_reference(_case, mult):
        seen_multipliers.append(mult)
        return base, None

    verdict, _detail = check(object(), fake_encoding, fake_reference)
    fallback_ok = verdict == "ok" and seen_multipliers == [6]
    bad += not fallback_ok
    print(
        f"  {'ok  ' if fallback_ok else 'FAIL'} fallback round parity "
        f"reference multipliers={seen_multipliers}, expected=[6]"
    )

    verdict, detail = check(object(), fake_encoding, fake_reference, search_cap=0)
    cap_ok = verdict == "limit" and detail.endswith("-- inconclusive")
    bad += not cap_ok
    print(f"  {'ok  ' if cap_ok else 'FAIL'} search-cap verdict verdict={verdict}, expected=limit")

    def fake_broken_reference(_case, _mult):
        return None, "reference error: invariant failure"

    verdict, _detail = check(object(), fake_encoding, fake_broken_reference)
    oracle_error_ok = verdict == "unreadable"
    bad += not oracle_error_ok
    print(f"  {'ok  ' if oracle_error_ok else 'FAIL'} reference error verdict verdict={verdict}, expected=unreadable")

    total = len(cases) + len(matcher_cases) + 3
    print(f"\n{total - bad}/{total} self-tests pass")
    return 1 if bad else 0


def known_groups():
    """Do BOTH readers recover a group whose size is known by hand?

    `checker-mutations.py` damages a graph AFTER it is extracted, so it shows the
    comparison discriminates -- not that either side read the graph right. A blind spot
    shared by the two readers is what it cannot see: if both lost a class's symmetries
    the checker would compare two trivial groups and pass. The corpus does not cover
    this well either. A 300-case fuzz run matches 2298 classes and 2314 group elements,
    and the identity is in every group, so only SIXTEEN non-identity permutations are
    ever compared.

    So: cases whose group is known, asked of each reader separately.
    """
    from slotted.xdiff import xdiff as X

    v0, v1, v2 = ("var", 0), ("var", 1), ("var", 2)

    def g(a, b):
        return ("G", a, b)

    cases = [
        # f($0,$1) = f($1,$0) -- the group is {id, swap}
        (
            "swap",
            2,
            X.Case("swap", [("F", v0, v1), ("F", v1, v0)], [(("F", v0, v1), ("F", v1, v0))], [], None, [], rounds=0),
        ),
        # g(g($0,$1),$2) = g(g($1,$2),$0) -- a 3-cycle generates three elements
        (
            "3-cycle",
            3,
            X.Case(
                "3cycle",
                [g(g(v0, v1), v2), g(g(v1, v2), v0)],
                [(g(g(v0, v1), v2), g(g(v1, v2), v0))],
                [],
                None,
                [],
                rounds=0,
            ),
        ),
    ]
    bad = 0
    for name, want, case in cases:
        ref, err = reference_graph(case)
        if err:
            print(f"  FAIL {name:9} reference: {err}")
            bad += 1
            continue
        enc, err, mult = encoding_graph(case)
        if err:
            print(f"  FAIL {name:9} encoding: {err}")
            bad += 1
            continue
        if mult != 3:
            ref, err = reference_graph(case, mult)
            if err:
                print(f"  FAIL {name:9} reference@{mult}: {err}")
                bad += 1
                continue
        rmax = max(group_sizes(ref), default=0)
        emax = max(group_sizes(enc), default=0)
        ok = rmax == want == emax
        bad += not ok
        print(f"  {'ok  ' if ok else 'FAIL'} {name:9} largest group: reference {rmax}, encoding {emax}, want {want}")
    print(f"\n{len(cases) - bad}/{len(cases)} groups recovered by both readers")
    return 1 if bad else 0


def known_open_bugs():
    """Each reproduction of an open bug must STILL diverge.

    A bug that has been fixed makes its case agree, and that is reported rather than
    passed over: the entry is then stale and should come out, taking the reproduction
    into `curated()` where it will be held green from then on.
    """
    bad = []
    from slotted.xdiff import xdiff as X

    cases = X.known_divergences()
    for why, case in cases:
        verdict, detail = check(case)
        if verdict == "FAIL":
            print(f"  ok    {case.name}\n        {detail}\n        {why}")
        else:
            print(f"  STALE {case.name}: {verdict} -- it agrees now, so the bug is fixed?")
            bad.append(case.name)
    if not cases:
        print("  (none -- no open bug has a reproduction here, which is the good state)")
    print(f"\n{len(cases) - len(bad)}/{len(cases)} known divergences still diverge")
    return 1 if bad else 0


def main():
    from slotted.xdiff import xdiff as X

    args = sys.argv[1:]
    if args and args[0] == "selftest":
        return selftest()
    if args and args[0] == "known-groups":
        return known_groups()
    if args and args[0] == "known":
        return known_open_bugs()
    if args and args[0] == "fuzz":
        n = int(args[1]) if len(args) > 1 else 100
        rng = random.Random(int(args[2]) if len(args) > 2 else 0)
        cases = [X.rand_case(rng, i) for i in range(n)]
    elif args:
        cases = [c for c in X.curated() if c.name.startswith(args[0])]
    else:
        cases = X.curated()

    tally = {"ok": 0, "FAIL": 0, "skip": 0, "limit": 0, "unreadable": 0}
    totals = [0, 0, 0]
    unsaturated = []

    def tracked_encoding(case):
        result = encoding_graph(case)
        if result[1] is None and result[2] != 3:
            unsaturated.append(case.name)
        return result

    for c in cases:
        verdict, detail = check(c, encoding_builder=tracked_encoding)
        tally[verdict] += 1
        if verdict == "ok":
            totals = [a + b for a, b in zip(totals, detail, strict=True)]
        else:
            print(f"  {verdict:5} {c.name:44} {detail}", flush=True)
    # Out of what could be COMPARED, not out of what was generated. A run the reference
    # cannot finish is not a verdict either way, and counting it against the total made
    # one slow case look like a divergence. A rule whose atoms share nothing is a cross
    # product, so some of those are more work than the reference's budget -- the small
    # ones still finish, and those are the ones this number is about.
    #
    # The sizes are still part of the result: a checker that compared nothing would
    # otherwise pass, which is what the floor in `check-slotted.py` is for.
    comparable = tally["ok"] + tally["FAIL"]
    print(
        f"\n{tally['ok']}/{comparable} isomorphic"
        f"   ({tally['FAIL']} differ, {tally['skip']} skipped,"
        f" {tally['limit']} ran out of time, {tally['unreadable']} unreadable,"
        f" of {len(cases)} generated)"
    )
    print(f"matched {totals[0]} e-classes, {totals[1]} e-nodes, {totals[2]} symmetries")
    if unsaturated:
        print(
            f"{len(unsaturated)} compared at a database fixpoint, not a rule "
            f"fixpoint: {', '.join(unsaturated[:6])}"
            f"{' ...' if len(unsaturated) > 6 else ''}"
        )
    return 1 if tally["FAIL"] or tally["unreadable"] else 0


if __name__ == "__main__":
    sys.exit(main())
