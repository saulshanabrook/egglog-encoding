"""Treatment configuration shared by benchmarking and correctness tests.

Each encoding names its exact reference and its timing baseline. The nested
baseline retains the paper's syntactic substitution; only its snapshot variant
is expected to produce the same e-graph as the compatibility encoding.
"""

from dataclasses import dataclass


@dataclass(frozen=True)
class Treatment:
    label: str
    description: str
    engine: str
    matcher: str
    substitution: str = "snapshot"
    exact_reference: str | None = None
    timing_reference: str | None = None

    @property
    def flags(self):
        if self.engine != "egglog":
            return ()
        return ("--slotted",) + (("--slotted-no-aliasing",) if self.matcher == "nested" else ())


TREATMENTS = {
    "encoding": Treatment(
        "egglog",
        "Egglog's slotted encoding, allowing slot aliasing.",
        "egglog",
        "multi",
        exact_reference="ref-multi",
        timing_reference="ref-multi",
    ),
    "encoding-no-aliasing": Treatment(
        "egglog-no-aliasing",
        "Egglog's compatibility mode, restricting aliasing like the nested matcher.",
        "egglog",
        "nested",
        exact_reference="ref-nested-snapshot",
        timing_reference="ref-nested",
    ),
    "ref-multi": Treatment(
        "ref-multi",
        "Reference multipattern matcher with deterministic snapshot substitution.",
        "reference",
        "multi",
    ),
    "ref-nested-snapshot": Treatment(
        "ref-nested-snapshot",
        "Reference nested matcher with the same snapshot substitution as egglog.",
        "reference",
        "nested",
    ),
    "ref-nested": Treatment(
        "ref-nested",
        "Original paper's nested matcher with syntactic substitution (timing baseline).",
        "reference",
        "nested",
        substitution="syntactic",
    ),
}
SIDES = tuple(TREATMENTS)
EXACT_PAIRS = {name: t.exact_reference for name, t in TREATMENTS.items() if t.exact_reference}
TIMING_PAIRS = {name: t.timing_reference for name, t in TREATMENTS.items() if t.timing_reference}
BENCHMARK_SIDES = tuple(dict.fromkeys(side for pair in TIMING_PAIRS.items() for side in pair))


def description():
    return "Treatments:\n" + "\n".join(f"  {name}: {t.description}" for name, t in TREATMENTS.items())
