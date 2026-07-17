"""Package the persistent DuckDB schema and session-local report relations.

``schema.sql`` defines versioned stored-record types and tables. ``session.sql``
owns temporary selection/scope types and the immutable comparison scope;
``analysis.sql`` owns temporary selection, aggregation, and statistics views;
``presentation.sql`` exposes temporary renderer-facing views. Python loads all
four through :mod:`importlib.resources`.
"""
