"""Package the DuckDB cache schema, parameterized analysis, and presentation layer.

``schema.sql`` defines the trusted JSONL projection, typed scope STRUCT, and
current-scope holder. ``analysis.sql`` owns scope table macros, statistics, and
timing aggregation. ``presentation.sql`` exposes same-named parameterized table
macros and current-scope views for Python rendering and interactive UI queries.
Python loads all three through :mod:`importlib.resources`.
"""
