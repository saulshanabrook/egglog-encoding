"""Define the narrow adapter registry that supplies paper process lanes."""

from __future__ import annotations

from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from types import MappingProxyType

from .models import Evaluation, Preset, ProcessLane

type LaneFactory = Callable[[Preset, Path], Sequence[ProcessLane]]


@dataclass(frozen=True)
class LaneRegistry:
    """Map each implemented evaluation to its adapter-owned lane factory."""

    factories: Mapping[Evaluation, LaneFactory] = field(default_factory=dict)

    def __post_init__(self) -> None:
        object.__setattr__(self, "factories", MappingProxyType(dict(self.factories)))

    def lanes_for(
        self,
        preset: Preset,
        evaluations: Sequence[Evaluation],
        artifact_root: Path,
    ) -> tuple[ProcessLane, ...]:
        """Resolve every selected adapter before allowing a run to begin."""

        missing = [evaluation for evaluation in evaluations if evaluation not in self.factories]
        if missing:
            raise ValueError("paper evaluation adapters are not implemented for: " + ", ".join(missing))
        lanes: list[ProcessLane] = []
        identities: set[tuple[Evaluation, str]] = set()
        for evaluation in evaluations:
            produced = tuple(self.factories[evaluation](preset, artifact_root))
            if not produced:
                raise ValueError(f"paper evaluation adapter produced no lanes: {evaluation}")
            for lane in produced:
                if lane.evaluation != evaluation:
                    raise ValueError(f"paper adapter {evaluation!r} produced a lane for {lane.evaluation!r}")
                identity = (lane.evaluation, lane.name)
                if identity in identities:
                    raise ValueError(f"duplicate paper process lane: {lane.evaluation}/{lane.name}")
                identities.add(identity)
                lanes.append(lane)
        return tuple(lanes)
