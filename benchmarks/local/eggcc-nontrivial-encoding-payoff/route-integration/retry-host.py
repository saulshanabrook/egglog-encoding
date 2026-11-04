#!/usr/bin/env python3
"""One exact host validation retry after retained ENOSPC-contaminated runs."""
from pathlib import Path
import importlib.util
BASE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('capture',BASE/'run.py');capture=importlib.util.module_from_spec(spec);spec.loader.exec_module(capture)
capture.run('host-make-test-disk-retry',['make','test'],1800,check=False)
