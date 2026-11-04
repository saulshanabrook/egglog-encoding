#!/usr/bin/env python3
"""Bounded capture for the isolated actual encoding candidate."""
from pathlib import Path
import importlib.util
import json
import os
import sys

ROOT=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('screen',ROOT.parent/'scoped-screen/run.py')
capture=importlib.util.module_from_spec(spec)
spec.loader.exec_module(capture)
capture.ROOT=ROOT
capture.U0=Path('/private/tmp/eggcc-same-mask-candidate')
capture.ENV.update(EGGCC_ROOT=str(capture.U0),RUSTUP_TOOLCHAIN='1.91.0',
    CARGO_BUILD_JOBS='4',RUST_TEST_THREADS='4',
    CARGO_TARGET_DIR='/private/tmp/encoding-same-mask-candidate/target')

if __name__=='__main__':
    label=sys.argv[1]
    argv=sys.argv[2:]
    capture.run(label,argv,1800 if argv[0]=='cargo' else 180)
