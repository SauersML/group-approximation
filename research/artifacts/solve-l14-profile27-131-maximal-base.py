#!/usr/bin/env python3
"""Install a profile27 boundary-only core into the audited state solver."""

import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def install(compression, tag):
    C = load(f"profile27_{tag}_compression", compression)
    S = load(f"profile27_{tag}_solver", "solve-l14-profile18-i0131-maximal.py")
    S.C = C
    S.NUMBER = {name: index + 1 for index, name in enumerate(C.FREE)}
    S.IDENTITY = tuple((index,) for index in range(1, len(C.FREE) + 1))
    S.combine.cache_clear()
    S.relation_state.cache_clear()
    S.EMPTY = S.P.close_tietze((), S.IDENTITY)
    S.WORDS = {"r2": C.R2, "r4": C.R4, "boundary": C.K}
    return S
