#!/usr/bin/env python3
"""Independent arithmetic checks plus source/emitted interpreter validation."""

from pathlib import Path
import importlib.util
import json
import os
import random
import re

BASE = Path(__file__).resolve().parent
ROOT = Path(os.environ.get("SORT_OUTPUT_ROOT", str(BASE)))
spec = importlib.util.spec_from_file_location("capture", BASE / "run.py")
capture = importlib.util.module_from_spec(spec)
spec.loader.exec_module(capture)
capture.ROOT = ROOT
U0 = BASE.parent / "admission/bin/eggcc"
MODULUS = 1 << 64


def wrap(value):
    bits = value % MODULUS
    return bits if bits < (1 << 63) else bits - MODULUS


def oracle(args, *, omit=None, right_tag=None, multiplier=3, mixed_true=False):
    a,b,c,d,z,w=args
    left=(min(a,b),max(a,b),int(a<b))
    tag=int(d<c) if right_tag=='reverse' else (int(c>=d) if right_tag=='arms' else int(c<d))
    right=(min(c,d),max(c,d),tag)
    if omit != "all" and any(x!=y for index,(x,y) in enumerate(zip(left,right)) if index!=omit): return '3\n'
    same=wrap(c+z)==wrap(a+w)
    if same:
        return '5\n' if not mixed_true else ('99\n' if wrap(multiplier*z)==wrap(multiplier*w) else '7\n')
    if mixed_true: return '5\n'
    return '99\n' if wrap(multiplier*z)==wrap(multiplier*w) else '7\n'


def interpreted(label, path, args, expected):
    destination = ROOT / "interpreted" / f"{label}.bril"
    destination.parent.mkdir(parents=True, exist_ok=True)
    text = re.sub(
        r"^# ARGS:.*$",
        "# ARGS: " + " ".join(map(str, args)),
        path.read_text(),
        count=1,
        flags=re.M,
    )
    data_path = destination.with_suffix(".json")
    command_label="interp-" + label.replace("/", "-")
    if (ROOT / "commands" / command_label / "receipt.json").exists():
        assert destination.read_text()==text
        data=json.loads(data_path.read_text())
        assert data["original_interpreted"]==expected and data["result_interpreted"]==expected
        return {"label":label,"args":args,"expected":expected,"actual":expected}
    destination.write_text(text)
    capture.run(
        "interp-" + label.replace("/", "-"),
        [
            U0,
            "--with-context",
            "--run-mode",
            "parse",
            "--interp",
            "--run-data-out",
            data_path,
            destination,
        ],
        30,
    )
    data = json.loads(data_path.read_text())
    assert data["original_interpreted"] == expected, (label, args, data, expected)
    assert data["result_interpreted"] == expected, (label, args, data, expected)
    return {"label": label, "args": args, "expected": expected, "actual": expected}


def semantic_laws():
    exhaustive=[]
    def key(a,b): return (min(a,b),max(a,b),int(a<b))
    def reconstruct(k): return (k[0],k[1]) if k[2] else (k[1],k[0])
    for width in range(2,9):
        values=range(-(1<<(width-1)),1<<(width-1))
        for a in values:
            for b in values: assert reconstruct(key(a,b))==(a,b)
        exhaustive.append({'width':width,'pairs':(1<<width)**2})
    edges=[-(1<<63),-(1<<63)+1,-1,0,1,(1<<63)-2,(1<<63)-1]
    pairs=[(a,b) for a in edges for b in edges]
    rng=random.Random(0x5037)
    pairs.extend((wrap(rng.getrandbits(64)),wrap(rng.getrandbits(64))) for _ in range(4096))
    inv3=pow(3,-1,MODULUS)
    for a,b in pairs:
        assert reconstruct(key(a,b))==(a,b)
        assert wrap(inv3*wrap(3*a))==a
    assert key(1,2)[:2]==key(2,1)[:2] and key(1,2)!=key(2,1)
    assert wrap(2*0)==wrap(2*(-(1<<63)))
    return {'law':'tag 1: (min,max); tag 0: (max,min)', 'reduced_exhaustive':exhaustive, 'full_width_pairs':len(pairs), 'inverse_of_three_mod_2_64':inv3,'no_tag_collision':[[1,2],[2,1]],'even_multiplier_collision':[0,-(1<<63)]}


def main():
    rows = []
    positives = json.loads((BASE / "positive-oracle.json").read_text())
    for row in positives:
        assert oracle(row["args"]) == row["expected_stdout"]
    positive_results = json.loads((ROOT / "positive-results.json").read_text())
    rows.extend(
        interpreted(f"positive/source/{index:02}", BASE / "fixtures/source.bril", row["args"], row["expected_stdout"])
        for index, row in enumerate(positives)
    )
    for result in positive_results:
        if result["mode"]=="source": continue  # byte-identical to the original source checked above
        emitted = ROOT / "matrix/positive" / result["mode"] / "optimized.bril"
        for index, row in enumerate(positives):
            rows.append(
                interpreted(
                    f"positive/{result['mode']}/{index:02}",
                    emitted,
                    row["args"],
                    row["expected_stdout"],
                )
            )

    negative_options = {
        "omitted-tag": {"omit":2},
        "omitted-min": {"omit":0},
        "omitted-max": {"omit":1},
        "reversed-right-tag": {"right_tag":"reverse"},
        "changed-right-tag": {"right_tag":"arms"},
        "even-multiplier": {"multiplier":2},
        "wrong-mixed-branch": {"mixed_true":True},
        "no-key-context": {"omit":"all"},
    }
    negative_results = json.loads((ROOT / "negative-results.json").read_text())
    grouped = {}
    for result in negative_results:
        grouped.setdefault(result["family"], []).append(result)
    for family, results in grouped.items():
        args = results[0]["outputs"][0]["args"]
        expected = oracle(args, **negative_options[family])
        assert expected == "99\n"
        source = BASE / "fixtures" / f"{family}.bril"
        rows.append(interpreted(f"negative/{family}/source", source, args, expected))
        for result in results:
            if result["mode"]=="source": continue  # same original source/header
            assert result["outputs"][0]["expected"] == expected
            emitted = ROOT / "matrix" / family / result["mode"] / "optimized.bril"
            rows.append(
                interpreted(
                    f"negative/{family}/{result['mode']}", emitted, args, expected
                )
            )

    contexts = json.loads((ROOT / "context-negative-results.json").read_text())
    for result in contexts:
        emitted = ROOT / "matrix/no-context-final" / result["mode"] / "optimized.bril"
        for index, positive in enumerate(positives):
            rows.append(
                interpreted(
                    f"context/{result['mode']}/{index:02}",
                    emitted,
                    positive["args"],
                    positive["expected_stdout"],
                )
            )

    invalid_results=json.loads((ROOT / "invalid-fold-results.json").read_text())
    for result in invalid_results:
        args=result["outputs"][0]["args"]
        rows.append(interpreted(f"{result['family']}/source", Path(result["source"]), args, "7\n"))

    output = {
        "status": "passed",
        "semantic_laws": semantic_laws(),
        "interpretations": len(rows),
        "rows": rows,
    }
    (ROOT / "verification.json").write_text(json.dumps(output, indent=2) + "\n")


if __name__ == "__main__":
    main()
