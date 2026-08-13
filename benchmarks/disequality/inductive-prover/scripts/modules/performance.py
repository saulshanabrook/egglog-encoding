################################################################################
# performance.py
# The model of the performances of a solver on a benchmark.
################################################################################

from . import util

class Result(util.JSONSerializable):
    """The result of a benchmark: either Success, Failure, Timeout or a collection of these."""
    def from_json(raw):
        ty = raw["type"]
        if ty == Success.Name:
            return Success.Singleton
        elif ty == Failure.Name:
            return Failure.Singleton
        elif ty == Timeout.Name:
            return Timeout.Singleton    
        elif ty == Collection.Name:
            return Collection(raw["n_successes"], raw["n_failures"], raw["n_timeouts"])
        else:
            raise Exception(f"DeserializationException: could not deserialize result of type {ty}")

    def __init__(self): util.JSONSerializable.__init__(self)
    def is_success(self): return False
    def is_failure(self): return False
    def is_timeout(self): return False
    def is_collection(self): return False
    def as_success(self): return None
    def as_failure(self): return None
    def as_timeout(self): return None
    def as_collection(self): return None


class Success(Result):
    """The result obtained when a solver was able to prove the expected properties."""
    Name = "Success"
    def singleton(): return Success.Singleton
    def __init__(self): Result.__init__(self)
    def __str__(self): return Success.Name
    def is_success(self): return True
    def as_success(self): return self
    def to_json(self): return {"type": str(self)}


class Failure(Result):
    """The result obtained when a solver was unable to prove the expected properties."""
    Name = "Failure"
    def singleton(): return Failure.Singleton
    def __init__(self): Result.__init__(self)
    def __str__(self): return Failure.Name
    def is_failure(self): return True
    def as_failure(self): return self
    def to_json(self): return {"type": str(self)}


class Timeout(Result):
    """The result obtained when a solver got stuck in proving the expected properties."""
    Name = "Timeout"
    def singleton(): return Timeout.Singleton
    def __init__(self): Result.__init__(self)
    def __str__(self): return Timeout.Name
    def is_timeout(self): return True
    def as_timeout(self): return self
    def to_json(self): return {"type": str(self)}


class Collection(Result):
    """A collection of results."""
    Name = "Collection"

    def __init__(self, n_successes, n_failures, n_timeouts):
        Result.__init__(self)
        self.n_successes = n_successes
        self.n_failures = n_failures
        self.n_timeouts = n_timeouts
        self.n_completed = n_successes + n_failures
        self.n_results = self.n_completed + n_timeouts

    def __str__(self): return Collection.Name
    def is_collection(self): return True
    def as_collection(self): return self

    def to_json(self): return {
        "type": str(self),
        "n_successes": self.n_successes,
        "n_failures": self.n_failures,
        "n_timeouts": self.n_timeouts
    }


Success.Singleton = Success()
Failure.Singleton = Failure()
Timeout.Singleton = Timeout()


class Performance(util.JSONSerializable):
    """The performance obtained by a solver on a benchmark."""
    def from_json(raw):
        ty = raw["type"]
        if ty == "Performance":
            return Performance(
                n_egraphs=raw["n_egraphs"],
                n_classes=raw["n_classes"],
                n_enodes=raw["n_enodes"],
                duration_ns=raw["duration_ns"],
                result=Result.from_json(raw["result"])
            )
        else:
            raise Exception(f"DeserializationException: could not deserialize performance of type {ty}")

    def sum(performances):
        """
        Return a new performance representing the sum of the specified performances,
        ignoring timeouts.
        """
        if len(performances) <= 0:
            raise ValueError("Cannot evaluate average of an empty list of performances")
        n_successes, n_failures, n_timeouts = 0, 0, 0
        sum_egraphs, sum_classes, sum_enodes, sum_duration_ns = 0, 0, 0, 0
        for performance in performances:
            if performance.result.as_timeout() is None:
                sum_egraphs = sum_egraphs + performance.n_egraphs
                sum_classes = sum_classes + performance.n_classes
                sum_enodes = sum_enodes + performance.n_enodes
                sum_duration_ns = sum_duration_ns + performance.duration_ns
                if performance.result.as_success() is not None:
                    n_successes = n_successes + 1
                elif performance.result.as_failure() is not None:
                    n_failures = n_failures + 1
                else:
                    collection = performance.result.as_collection()
                    n_successes = n_successes + collection.n_successes
                    n_failures = n_failures + collection.n_failures
                    n_timeouts = n_timeouts + collection.n_timeouts
            else:
                n_timeouts = n_timeouts + 1
        return Performance(
            n_egraphs=sum_egraphs,
            n_classes=sum_classes,
            n_enodes=sum_enodes,
            duration_ns=sum_duration_ns,
            result=Collection(n_successes, n_failures, n_timeouts)
        )

    def __init__(self, n_egraphs, n_classes, n_enodes, duration_ns, result):
        util.JSONSerializable.__init__(self)
        self.n_egraphs = n_egraphs
        self.n_classes = n_classes
        self.n_enodes = n_enodes
        self.duration_ns = duration_ns
        self.result = result

    def enode_per_class(self):
        """Return the average number of e-nodes per e-class."""
        return self.n_enodes / (1 if self.n_classes == 0 else self.n_classes)

    def average(self):
        """
        Return a new performance representing the average of this performance.
        This only makes sense if this performance is a collection of results.
        """
        result = self.result.as_collection()
        if result is None:
            return self
        else:
            return Performance(
                n_egraphs=self.n_egraphs / result.n_completed,
                n_classes=self.n_classes / result.n_completed,
                n_enodes=self.n_enodes / result.n_completed,
                duration_ns=self.duration_ns / result.n_completed,
                result=result,
            )

    def to_json(self):
        return {
            "type": "Performance",
            "n_egraphs": self.n_egraphs,
            "n_classes": self.n_classes,
            "n_enodes": self.n_enodes,
            "duration_ns": self.duration_ns,
            "result": self.result.to_json(),
        }


class Performances(util.JSONSerializable):
    """A map from benchmarks to their performance."""
    def from_json(raw):
        ty = raw["type"]
        if ty == "Performances":
            performances = Performances()
            for (benchmark, performance) in raw["benchmarks"].items():
                performances.update(benchmark, Performance.from_json(performance))
            return performances
        else:
            raise Exception(f"DeserializationException: cannot deserialize performances of type {ty}")

    def __init__(self, performances = None):
        util.JSONSerializable.__init__(self)
        self.entries = performances or {}

    def get(self, benchmark):
        """Return the performance of the specified benchmark."""
        return self.entries[benchmark]

    def update(self, benchmark, performance):
        """Set the performances of the specified benchmark to the specified performance."""
        self.entries[benchmark] = performance
        return self

    def to_json(self):
        return {
            "type": "Performances",
            "benchmarks": {benchmark: performance.to_json() for (benchmark, performance) in self.entries.items()}
        }