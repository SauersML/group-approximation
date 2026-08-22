#!/usr/bin/env python3
"""Install a profile27 boundary-only state module into the audited solver."""

import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def install(state_file, tag):
    S = load(f"profile27_{tag}_states", state_file)
    W = load(f"profile27_{tag}_boundary_driver",
             "solve-l14-profile18-i0131-boundary.py")
    W.S = S
    W.B.S = S
    W.B.C = S.C
    W.B.ALG = S.ALG
    W.B.Q = len(S.C.FREE) + 1
    W.B.IDENTITY = tuple((index,) for index in range(1, W.B.Q + 1))
    W.B.combine.cache_clear()
    W.B.relation_state.cache_clear()
    W.B.maximal_states_relative.cache_clear()
    W.B.ENCODED_K = tuple((copy, S.encode(coefficient))
                          for copy, coefficient in S.C.K)
    return W
