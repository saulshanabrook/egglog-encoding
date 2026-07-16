"""Package the DuckDB schema, analysis, and output-facing report views.

``schema.sql`` defines the trusted JSONL projection and selected-scope tables,
``analysis.sql`` owns reusable statistics and timing aggregation, and
``presentation.sql`` exposes typed semantic datasets for Python rendering and
interactive UI queries. Python loads all three through :mod:`importlib.resources`.
"""
