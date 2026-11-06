"""Load the pinned data and compute independent decimal answers."""

from __future__ import annotations

import hashlib
from pathlib import Path
from typing import Any

import duckdb

from . import model
from .model import ident

type Results = list[list[tuple[Any, ...]]]


def load_data(directory: Path) -> tuple[duckdb.DuckDBPyConnection, dict[str, Any]]:
    for filename in ("features.conf", "treedecomposition.conf"):
        if (directory / filename).read_bytes() != (model.FIXTURES / filename).read_bytes():
            raise ValueError(f"{filename} differs from the pinned artifact")
    attrs, relations = model.WORKLOAD.attributes, model.WORKLOAD.relations
    types = {name: "DECIMAL(18,6)" if kind == "double" else "BIGINT" for name, kind in attrs}
    db = duckdb.connect()
    db.execute("SET threads=1")
    hashes, sizes = {}, {}
    try:
        for name, columns in relations.items():
            path = directory / f"{name}.tbl"
            hashes[path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
            db.read_csv(str(path), delimiter="|", header=False, columns={c: types[c] for c in columns}).create(name)
            sizes[name] = db.sql(f"SELECT COUNT(*) FROM {ident(name)}").fetchall()[0][0]
    except Exception:
        db.close()
        raise
    return db, {"duckdb": duckdb.__version__, "data_sha256": hashes, "input_rows": sizes, "lmfao_commit": model.COMMIT}


def reference_results(db: duckdb.DuckDBPyConnection) -> Results:
    db.execute(
        "CREATE TEMP TABLE oracle AS SELECT * FROM " + " NATURAL JOIN ".join(map(ident, model.WORKLOAD.relations))
    )
    expected = []
    for query in model.WORKLOAD.queries:
        groups = [ident(g) for g in query.groups]
        weight = " * ".join(f"CAST({ident(f)} AS DECIMAL(38,6))" for f in query.factors) or "1"
        fields = [f"{g} AS g{i}" for i, g in enumerate(groups)] + [f"COALESCE(SUM({weight}), 0) AS value"]
        sql = f"SELECT {', '.join(fields)} FROM oracle" + (" GROUP BY " + ", ".join(groups) if groups else "")
        expected.append(db.execute(sql).fetchall())
    return expected
