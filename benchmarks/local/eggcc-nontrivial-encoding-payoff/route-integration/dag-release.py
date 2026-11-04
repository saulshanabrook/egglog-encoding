#!/usr/bin/env python3
"""Run the unchanged second host Makefile validation step after root Insta failure."""
from pathlib import Path
import importlib.util
BASE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('capture',BASE/'run.py');capture=importlib.util.module_from_spec(spec);spec.loader.exec_module(capture)
capture.run('dag-release-required',['cargo','insta','test','--release','--unreferenced=reject'],1800,cwd=Path('/private/tmp/eggcc-route-candidate/dag_in_context'),check=False)
