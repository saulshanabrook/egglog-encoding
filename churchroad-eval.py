#!/usr/bin/env python3
"""Measure Churchroad's DSP mapping or bounded module discovery."""

import importlib
import sys

if __name__ == "__main__":
    sys.exit(importlib.import_module("slotted.churchroad.evaluation").main())
